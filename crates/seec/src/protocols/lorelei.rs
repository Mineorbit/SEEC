use crate::circuit::{ExecutableCircuit, GateIdx};
use crate::common::BitVec;
use std::vec::Vec;
use crate::executor::{Executor, GateOutputs, Input};
use crate::gate::base::BaseGate;
use crate::mul_triple::boolean::MulTriples;
use crate::mul_triple::MTProvider;
use crate::protocols::{
    Ring, FunctionDependentSetup, Gate, Protocol, ScalarDim, SetupStorage, ShareStorage, Share
};
use crate::secret::Secret;
use crate::utils::take_arr;
use crate::{bristol, executor, CircuitBuilder};
use ahash::AHashMap;
use async_trait::async_trait;
use itertools::Itertools;
use rand::{Rng, SeedableRng};
use std::marker::PhantomData;
use rand_chacha::ChaChaRng;
use seec_channel::multi::{MultiReceiver, MultiSender};
use serde::{Deserialize, Serialize};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::convert::Infallible;
use std::error::Error;
use std::fmt::Debug;
use std::ops::Not;
use std::cmp;
use std::cmp::Ordering;


// 2 party OT based setup provider


pub type LoreleiSetupMsg<R> = executor::Message<Lorelei<R>>;

// this maps a gate to a list of its shares of blinding values: the first element of the image is potential gamma shares, i.e. crossterms, the latter output shares
pub type SetupLookup<R> = HashMap<GateIdx,(Vec<R>,R)>;

#[derive(Clone, Debug, Hash,PartialEq,Eq,PartialOrd,Ord)]
pub struct LoreleiSharing<R> {
    pub(crate) lookup: SetupLookup<R>
    // TODO: Maybe give access to rngs here like in aby2.0 implementation
}

impl<R> Default for LoreleiSharing<R> {
    fn default() -> Self {
        Self {
            lookup: HashMap::new()
        }
    }
}


pub struct LoreleiSetupProvider<'a,Mtp,R: Ring> {
    party_id: usize,
    mt_provider: Mtp,
    sender: seec_channel::Sender<LoreleiSetupMsg<R>>,
    receiver: seec_channel::Receiver<LoreleiSetupMsg<R>>,
    sharing: &'a LoreleiSharing<R>
}

#[async_trait]
impl<'a,MtpErr, Mtp, Idx, R: Ring> FunctionDependentSetup<Lorelei<R>, Idx> for LoreleiSetupProvider<'a,Mtp,R>
where
    MtpErr: Error + Send + Sync + Debug + 'static,
    Mtp: MTProvider<Output = MulTriples, Error = MtpErr> + Send,
    Idx: GateIdx,
{
    type Error = Infallible;

    async fn setup(
        &mut self,
        shares: &GateOutputs<ShareStorage<LoreleiShare<R>>>,
        circuit: &ExecutableCircuit<R, LoreleiGate<R>, Idx>,
    ) -> Result<(), Self::Error> {
        // TODO: populate sharing with lambda and gamma values
        Ok(())
    }

    // these values end up being the setup data being passed to the protocol context in older implementations, we move this to the protocol struct instead, to allow for easier access, the outputs of this function will be ignored therefore
    async fn request_setup_output(&mut self, count: usize) -> Result<R, Self::Error> {
        Ok(R::ZERO)
    }
}



impl<'a,Mtp,R: Ring> LoreleiSetupProvider<'a,Mtp,R> {
    pub fn new(
        party_id: usize,
        mt_provider: Mtp,
        sender: seec_channel::Sender<LoreleiSetupMsg<R>>,
        receiver: seec_channel::Receiver<LoreleiSetupMsg<R>>,
        sharing: &'a LoreleiSharing<R> 
    ) -> Self {
        Self {
            party_id,
            mt_provider,
            sender,
            receiver,
            sharing
        }
    }
}

// -----  ring Lorelei protocol = combined arithmetic and blinded protocol


#[derive(Clone, Debug, Default, Hash,PartialEq,PartialOrd,Eq,Ord)]
pub struct Lorelei<R: Ring> {
    sharing: LoreleiSharing<R>
}


#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Msg<R> {
    Delta { delta: Vec<R> },
}



impl<R: Ring> Protocol for Lorelei<R> {
    const SIMD_SUPPORT: bool = false;
    type Plain = R;
    type Share = LoreleiShare<R>;
    type Msg = Msg<R>;
    type SimdMsg = ();
    type Gate = LoreleiGate<R>;
    type Wire = ();
    type ShareStorage = ShareStorage<LoreleiShare<R>>;
    type SetupStorage = SetupStorage;

    fn share_constant(
        &self,
        _party_id: usize,
        output_share: Self::Share,
        val: Self::Plain,
    ) -> Self::Share {
        match output_share {
            LoreleiShare::Arithmetic(arithShare) => {
                arithShare.x = val;
                output_share
            }

            LoreleiShare::Blinded(blindedShare) => {
                let is_active: Ring;
                if  _party_id == 0
                {
                    is_active = R::ONE;
                }else
                {
                    is_active = R::ZERO;
                }
                blindedShare.m =  is_active.wrapping_mul(val);
                blindedShare.l = R::ZERO;
                output_share
            }
        }
    }

    fn evaluate_non_interactive(
        &self,
        party_id: usize,
        gate: &Self::Gate,
        mut inputs: impl Iterator<Item = Self::Share>,
    ) -> Self::Share {
        match gate {
            BlindedGate::Base(base) => base.default_evaluate(party_id, inputs.by_ref()),
            
            BlindedGate::Arith(arith) => 
            {

                // TODO should assert that all input shares are completely blinded or completely arithmetic
                match arith {
                
                    ArithmeticGate::Add {n} => {
                        let arithmeticMode = false;
                        let sumMask = R::ZERO;

                        let sumLambda = R::ZERO;

                        let sumShare = R::ZERO;
                        while let Some(currentInput) = inputs.next()
                        {
                            match currentInput {
                                LoreleiShare::Arithmetic(arithmeticShare) => {
                                    arithmeticMode = true;
                                    sumShare.wrapping_add(&arithmeticShare.x);
                                }
                                LoreleiShare::Blinded(blindedShare) => {
                                    arithmeticMode = false;
                                    sumMask.wrapping_add(&blindedShare.m);
                                    sumLambda.wrapping_add(&blindedShare.l);
                                }
                            }
                        }
                        if arithmeticMode
                        {
                            LoreleiShare::Arithmetic(ArithmeticShare {x: sumShare})
                        } else
                        {
                            LoreleiShare::Blinded(BlindedShare {m: sumMask, l:sumLambda})
                        }

                    }

                    
                    ArithmeticGate::Mul {n} => {
                        let outShareValue = R::ZERO;

                        // TODO: Sum for each posetof gamma values and mask values

                        LoreleiShare::Arithmetic(ArithmeticShare {x: outShareValue})
                    }
                }
            },
            BlindedGate::Conv(conv) => 
            {
                // todo, somehow this does not work, not sure why
                //assert_eq(inputs.len(),1);
                match conv {
                    Blinded2Arithmetic => {
                        let input = inputs.next().unwrap();
                        assert!(matches!(input,LoreleiShare::Blinded(BlindedShare)));
                        match input 
                        {
                            LoreleiShare::Blinded(blindedShare) => 
                            {
                                let outShareValue = blindedShare.l;
                                if party_id == 0
                                {
                                    outShareValue.wrapping_add(&blindedShare.m);
                                }

                                LoreleiShare::Arithmetic(ArithmeticShare {x: outShareValue})
                            }
                        }
                    },
                    Arithmetic2Blinded => {
                        panic!("Called evaluate_non_interactive on Arithmetic to blinded reshare gate")
                    }
                }
            }
        }
    }

    // on conv gate send the necessary randomly offset arithmetic shares of the m value
    fn compute_msg( &self, party_id: usize, interactive_gates: impl Iterator<Item = LoreleiGate<R>>, gate_outputs: impl Iterator<Item = Self::Share>, mut inputs: impl Iterator<Item = Self::Share>, _old_setup_store_var: Self::SetupStorage) -> Self::Msg 
    {        
        let m: Vec<R> = interactive_gates
        .zip(gate_outputs)
        .map(|(gate, output)| {
            assert!(matches!(gate, LoreleiGate::Conv(ConvGate::Arithmetic2Blinded)));
            let inputs = inputs.by_ref().take(gate.input_size());
            gate.compute_delta_share(party_id, inputs, output)
        }).collect();
    Msg::Delta { delta: m }
    }

    // on arith 2 blinded conv gate, add together my arithmetic share of m with other arithmetic share, add together into blinded share
    fn evaluate_interactive(&self, _party_id: usize, interactive_gates: impl Iterator<Item = LoreleiGate<R>>, gate_outputs: impl Iterator<Item = Self::Share>, Msg::Delta { delta: m_arith }: Self::Msg, Msg::Delta { delta: other_m_arith }: Self::Msg, _old_setup_store_var: Self::SetupStorage) -> Self::ShareStorage 
    {
        
        let intermediate = gate_outputs
            .zip(m_arith).zip(other_m_arith)
            .map(|((mut out_share, my_delta), other_delta)| {
                out_share = LoreleiShare::Blinded(BlindedShare{m:(my_delta.wrapping_add(&other_delta)),l:R::ZERO});
                out_share
            }).collect();
    }

    fn setup_gate_outputs<Idx: GateIdx>(&mut self, _party_id: usize, circuit: &ExecutableCircuit<Self::Plain, Self::Gate, Idx>,) -> GateOutputs<Self::ShareStorage> 
    {
        assert!(false);
    }
}


// ---- Sharing structure





// Computation (Online Shares)

#[derive(Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub enum LoreleiShare<R: Ring> {
    Arithmetic(ArithmeticShare<R>),
    Blinded(BlindedShare<R>)
}

impl<R: Ring> Default for LoreleiShare<R> {
    fn default() -> Self {
        LoreleiShare::Blinded(BlindedShare::default()) // Specify the default variant and its values
    }
}

// currently do not support SIMD, so this is place holding
impl<R: Ring> Share for LoreleiShare<R> {
    type Plain = R;
    type SimdShare = ShareStorage<LoreleiShare<R>>;
}


#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct BlindedShare<R: Ring> {
    pub(crate) m: R,
    pub(crate) l: R,
}

#[derive(Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct BlindedShareVec<R: Ring> {
    pub(crate) m: Vec<R>,
    pub(crate) l: Vec<R>,
}


#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct ArithmeticShare<R> {
    pub(crate) x: R
}


// ---- Gate Structure

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug)]
pub enum LoreleiGate<R: Ring> {
    Base(BaseGate<Lorelei<R>>),
    Arith(ArithmeticGate<R>),
    Conv(ConvGate<R>),
}


impl<R: Ring>  Gate<R> for LoreleiGate<R> {
    type DimTy = ScalarDim;

    fn is_interactive(&self) -> bool {
        match &self {
            LoreleiGate::Base(g) => { g.is_interactive()
            }
            LoreleiGate::Arith(g) => { false
            }
            LoreleiGate::Conv(g) => { g.is_interactive()
            }
        }
    }

    fn input_size(&self) -> usize {
        match self {
            ArithmeticGate::Base(base_gate) => base_gate.input_size(),
            ArithmeticGate::Mul { n } => *n as usize,
            ArithmeticGate::Add { n } => *n as usize,
        }
    }

    fn as_base_gate(&self) -> Option<&BaseGate<R>> {
        match self {
            ArithmeticGate::Base(base_gate) => Some(base_gate),
            _ => None,
        }
    }

    fn wrap_base_gate(base_gate: BaseGate<R, Self::DimTy>) -> Self {
        Self::Base(base_gate)
    }
}


impl<R: Ring> From<BaseGate<R>> for LoreleiGate<R> {
    fn from(base_gate: BaseGate<R>) -> Self {
        LoreleiGate::Base(base_gate)
    }
}



#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum ConvGate<R> {
    Base(BaseGate<R>),
    Blinded2Arithmetic,
    Arithmetic2Blinded
}


impl<R: Ring>  Gate<R> for ConvGate<R> {
    type DimTy = ScalarDim;

    fn is_interactive(&self) -> bool {
        match &self {
            ConvGate::Blinded2Arithmetic => { false }
            ConvGate::Arithmetic2Blinded => { true }
        }
    }

    fn input_size(&self) -> usize {
        1
    }

    fn as_base_gate(&self) -> Option<&BaseGate<R>> {
        match self {
            LoreleiGate::Base(base_gate) => Some(base_gate),
            _ => None,
        }
    }

    fn wrap_base_gate(base_gate: BaseGate<R>) -> Self {
        Self::Base(base_gate)
    }
}


#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum ArithmeticGate<R> {
    Base(BaseGate<R>),
    Mul { n: u8 },
    Add { n: u8 },
}

impl<R: Ring>  Gate<R> for ArithmeticGate<R> {
    type DimTy = ScalarDim;

    fn is_interactive(&self) -> bool {
        false
    }

    fn input_size(&self) -> usize {
        match self {
            ArithmeticGate::Base(base_gate) => base_gate.input_size(),
            ArithmeticGate::Mul { n } => *n as usize,
            ArithmeticGate::Add { n } => *n as usize,
        }
    }

    fn as_base_gate(&self) -> Option<&BaseGate<R>> {
        match self {
            ArithmeticGate::Base(base_gate) => Some(base_gate),
            _ => None,
        }
    }

    fn wrap_base_gate(base_gate: BaseGate<R, Self::DimTy>) -> Self {
        Self::Base(base_gate)
    }
}


impl<R> From<BaseGate<R>> for ArithmeticGate<R> {
    fn from(base_gate: BaseGate<R>) -> Self {
        ArithmeticGate::Base(base_gate)
    }
}






// custom gate behavior
impl<R: Ring> LoreleiGate<R> {
    /// output_share contains the previously randomly generated private share needed for the
    /// evaluation
    fn compute_delta_share(
        &self,
        party_id: usize,
        mut inputs: impl Iterator<Item = Share>,
        output_share: Share,
    ) -> bool {
        assert!(matches!(party_id, 0 | 1));
        //assert!(matches!(self, LoreleiGate::Conv( { .. })));
        match self {
            &LoreleiGate::Conv(convGate) => {
                let inputs: Vec<_> = inputs.take(1).collect();
                match inputs[0] {
                    LoreleiShare::Arithmetic(arithShare) => {

                        // <m_x>_i = <x>_i - <lambda_x>_i
                        arithShare.x.wrapping_sub(output_share.l)
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    // this is the lambda functionality
    // it produces only the lambda values across the entire circuit, note that as multiplications do not have blinded output shares they have no lambda/gamma output
    fn setup_output_share(
        &self,
        mut inputs: impl Iterator<Item = Share>,
        mut rng: impl Rng,
    ) -> Share {

        match self {
            LoreleiGate::Base(base_gate) => match base_gate {
                BaseGate::Input(_) => {
                    // TODO this needs to randomly generate the private part of the share
                    //  however, there is a problem. This private part needs to match the private
                    //  part of the input which is supplied to Executor::execute
                    //  one option to ensure this would be to use two PRNGs seeded with the same
                    //  seed for this method and for the Sharing of the input
                    //  Or maybe the setup gate outputs of the input gates can be passed to
                    //  the share() method?
                    LoreleiShare::Blinded( 
                        BlindedShare {
                        m: Default::default(),
                        l: rng.gen()
                        }
                    )
                }
                BaseGate::Output(_)
                | BaseGate::SubCircuitInput(_)
                | BaseGate::SubCircuitOutput(_)
                | BaseGate::ConnectToMain(_)
                | BaseGate::Debug
                | BaseGate::Identity => inputs.next().expect("Empty input"),
                BaseGate::Constant(_) => Share::default(),
                BaseGate::ConnectToMainFromSimd(_) => {
                    unimplemented!("SIMD currently not supported for ABY2")
                }
                },
            LoreleiGate::Arith(arithmetic_gate) => match arithmetic_gate {
                ArithmeticGate::Mul { n } => {
                    // multiplication never has fresh randomness itself
                    Share::Default
                },
                ArithmeticGate::Add { n } => {
                    let mut acc = R::ZERO;
                    
                    while let Some(currentInput) = inputs.next()
                        {
                            match currentInput {
                                LoreleiShare::Blinded(blindedShare) => {
                                    acc.wrapping_add(blindedShare.l);
                                }
                            }
                        }
                        LoreleiShare::Blinded( 
                            BlindedShare {
                            m: Default::default(),
                            l: acc
                        })
                    }
                },
            LoreleiGate::Conv(conversion_gate) => match conversion_gate {
                // here fresh randomness only if it is arithmetic to blinded, else give no randomness
                Arithmetic2Blinded => {
                    LoreleiShare::Blinded( 
                        BlindedShare {
                        m: Default::default(),
                        l: rng.gen()
                    })
                }
            }
        }

    }

}






#[cfg(test)]
mod tests {
    use super::LoreleiGate as LG;
    use super::*;
    use crate::circuit::BaseCircuit;
    use crate::mul_triple::boolean::InsecureMTProvider;
    use bitvec::bitvec;
    use bitvec::order::Lsb0;

    #[tokio::test]
    async fn multi_mult() {

        type RING = u32;
        // Setting up circuit
        let mut circuit = BaseCircuit::<RING, LG>::new();
        let i0 = circuit.add_gate(LG::Base(BaseGate::Input(ScalarDim)));
        let i1 = circuit.add_gate(LG::Base(BaseGate::Input(ScalarDim)));
        let i2 = circuit.add_gate(LG::Base(BaseGate::Input(ScalarDim)));
        let i3 = circuit.add_gate(LG::Base(BaseGate::Input(ScalarDim)));
        let a = circuit.add_wired_gate(LG::Arith(Mult { n: 3 }, &[i0, i1, i2]));
        let reshare = circuit.add_wired_gate(LG::Conv(Arithmetic2Blinded,&[a]));
        let b = circuit.add_wired_gate(LG::Arith(Mult { n: 2 }, &[reshare, i3]));
        let _out = circuit.add_wired_gate(LG::Base(BaseGate::Output(ScalarDim)), &[b]);
        let c = ExecutableCircuit::DynLayers(c.into());


        // Create protocol context
        let (ch0, ch1) = seec_channel::in_memory::new_pair(16);
        let loreleiSharing_0 = LoreleiSharing::default();
        let loreleiSharing_1 = LoreleiSharing::default();
        let protocol_state_0 = Lorelei::new(loreleiSharing_0);
        let protocol_state_1 = Lorelei::new(loreleiSharing_1);
        let setup0: LoreleiSetupProvider<InsecureMTProvider<R>, R> = LoreleiSetupProvider::new(0, InsecureMTProvider::default(), ch0.0, ch0.1,&loreleiSharing_0);
        let setup1: LoreleiSetupProvider<InsecureMTProvider<R>, R> = LoreleiSetupProvider::new(1, InsecureMTProvider::default(), ch1.0, ch1.1,&loreleiSharing_0);
        let (mut ex1, mut ex2) = tokio::try_join!(
            Executor::new_with_state(protocol_state.clone(), &c, 0, setup0),
            Executor::new_with_state(protocol_state, &c, 1, setup1),
        ).unwrap();

        let inp0 = LoreleiSharing::new().share(vec![2,2,2,2]);
        let inp1 = LoreleiSharing::insecure_default().plain_delta_to_share(mask);
        let (mut ch1, mut ch2) = seec_channel::in_memory::new_pair(2);

        let h1 = ex1.execute(Input::Scalar(inp0), &mut ch1.0, &mut ch1.1);
        let h2 = ex2.execute(Input::Scalar(inp1), &mut ch2.0, &mut ch2.1);
        let (res1, res2) = tokio::try_join!(h1, h2).unwrap();
        let res = LoreleiSharing::reconstruct(res1.into_scalar().unwrap(), res2.into_scalar().unwrap());

        assert_eq!(vec![16], res);
        Ok(())
    }
}
