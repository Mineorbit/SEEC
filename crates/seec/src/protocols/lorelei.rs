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


// 3 party Helper based Setup


pub type LoreleiSetupMsg<R> = executor::Message<Lorelei<R>>;



#[derive(Clone, Debug, Hash,PartialEq,Eq,PartialOrd,Ord,Default)]
pub struct LoreleiSharing<R> {
    pub(crate) private_rng: ChaChaRng,
    pub(crate) local_joint_rng: ChaChaRng,
    pub(crate) remote_joint_rng: ChaChaRng,
    pub(crate) circuit_input_owner_map: HashMap<usize, usize>,
    phantom: PhantomData<R>,
}






// this is the party that sends lambda and gamma shares to the two online parties
pub struct AstraSetupHelper<R> {
    sender: MultiSender<AstraSetupMsg<R>>,
    // shared rng seed owned by helper and p0
    priv_seed_p0: [u8; 32],
    // shared rng seed owned by helper and p1
    priv_seed_p1: [u8; 32],
    // shared rng seed owned by helper, p0 and p1
    joint_seed: [u8; 32],
}


impl AstraSetupHelper {

    pub fn new(
        sender: MultiSender<AstraSetupMsg>,
        priv_seed_p0: [u8; 32],
        priv_seed_p1: [u8; 32],
        joint_seed: [u8; 32],
    ) -> Self {
        Self {
            sender,
            priv_seed_p0,
            priv_seed_p1,
            joint_seed,
        }
    }

    pub async fn setup<Idx: GateIdx>(
        self,
        circuit: &ExecutableCircuit<bool, BooleanGate, Idx>,
        input_map: HashMap<usize, InputBy>,
    ) {
        let p0_gate_outputs =
            self.setup_gate_outputs(0, circuit, self.priv_seed_p0, self.joint_seed, &input_map);
        let p1_gate_outputs =
            self.setup_gate_outputs(1, circuit, self.priv_seed_p1, self.joint_seed, &input_map);

        let mut rng_p0 = ChaChaRng::from_seed(self.priv_seed_p0);
        // synchronized with the AstraSetupProvider but different than the stream used for the gate
        // outputs before
        rng_p0.set_stream(1);

        // TODO this could potentially be optimized as it reconstructs all lambda values
        //  but we only need those that are an input to an interactive gate
        let rec_gate_outputs: Vec<_> = p0_gate_outputs
            .into_iter()
            .zip(p1_gate_outputs.into_iter())
            .map(|(p0_out, p1_out)| {
                let p0_storage = p0_out.into_scalar().expect("SIMD unsupported");
                let p1_storage = p1_out.into_scalar().expect("SIMD unsupported");
                // we only need to reconstruct the private parts which were initialized
                p0_storage.private ^ p1_storage.private
            })
            .collect();

        let mut msg = BitVec::with_capacity(circuit.interactive_count());

        for (gate, _gate_id, parents) in circuit.interactive_with_parents_iter() {
            match gate {
                BooleanGate::And { n } => {
                    assert_eq!(2, n, "Astra setup currently supports 2 input ANDs");
                    let inputs: [bool; 2] = take_arr(&mut parents.take(2).map(|scg| {
                        rec_gate_outputs[scg.circuit_id as usize][scg.gate_id.as_usize()]
                    }));
                    let lambda_xy = inputs[0] & inputs[1];
                    let lambda_xy_0: bool = rng_p0.gen();
                    let lambda_xy_1 = lambda_xy ^ lambda_xy_0;
                    msg.push(lambda_xy_1);
                }
                ni => unreachable!("non interactive gate {ni:?}"),
            }
        }
        self.sender
            .send_to([1], AstraSetupMsg(msg))
            .await
            .expect("failed to send setup message")
    }

    fn setup_gate_outputs<Idx: GateIdx>(
        &self,
        party_id: usize,
        circuit: &ExecutableCircuit<bool, BooleanGate, Idx>,
        local_seed: [u8; 32],
        joint_seed: [u8; 32],
        input_map: &HashMap<usize, InputBy>,
    ) -> GateOutputs<ShareVec> {
        // The idea is to reuse the `Lorelei` setup_gate_outputs method with the correct
        // rngs to generate the correct values for the helper

        let input_position_share_type_map = input_map
            .iter()
            .map(|(&pos, by)| {
                let st = match (party_id, by) {
                    (0, InputBy::P0) | (1, InputBy::P1) => ShareType::Local,
                    (0, InputBy::P1) | (1, InputBy::P0) => ShareType::Remote,
                    (id, _) => panic!("Unsupported party id {id}"),
                };
                (pos, st)
            })
            .collect();

        let mut p = Lorelei {
            delta_sharing_state: DeltaSharing::new(
                party_id,
                local_seed,
                joint_seed,
                input_position_share_type_map,
            ),
        };
        p.setup_gate_outputs(party_id, circuit)
    }
}











// This is the setup provider that talks to the Astra Setup Helper

#[derive(Clone, Default)]
pub struct SetupData<R> {
    eval_shares: Vec<EvalShares<R>>,
}

#[derive(Clone)]
pub struct EvalShares<R> {
    shares: Vec<R>,
}


pub struct AstraSetupProvider<R: Ring> {
    party_id: usize,
    receiver: MultiReceiver<AstraSetupMsg<R>>,
    rng: ChaChaRng,
    setup_data: Option<SetupData<R>>,
}

#[async_trait]
impl<MtpErr, Mtp, Idx, R: Ring> FunctionDependentSetup<Lorelei<R>, Idx> for AstraSetupProvider<Mtp,R>
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

        // receive lambda values from AstraSetupHelper party


        Ok(())
    }

    async fn request_setup_output(&mut self, count: usize) -> Result<R, Self::Error> {
        Ok(())
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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Msg<R> {
    Delta { delta: Vec<R> },
}


#[derive(Clone, Debug, Default, Hash,PartialEq,PartialOrd,Eq,Ord)]
pub struct Lorelei<R: Ring> {
    sharing: LoreleiSharing<R>
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

                // TODO: more than two inputs
                        
        assert!(matches!(party_id, 0 | 1));
        assert!(matches!(self, ArithmeticGate::Mul));
        let mut priv_delta = preprocessing_delta
            .eval_shares
            .pop()
            .expect("Missing eval_share");
        match self {
            ArithmeticGate::Mul => {
                let a = inputs.next().expect("Empty input");
                let b = inputs.next().expect("Insufficient input");
                let plain_ab = a.public.wrapping_mul(&b.public);
                let i = if party_id == 1 { R::ONE } else { R::ZERO };
                
                let multiplication_result_arithmetic_share = 
                i.wrapping_mul(&plain_ab)
                    .wrapping_sub(&a.public.wrapping_mul(&b.private))
                    .wrapping_sub(&b.public.wrapping_mul(&a.private))
                    .wrapping_add(&priv_delta.shares.pop().expect("Missing eval share"));

                LoreleiShare::Arithmetic(ArithmeticShare{
                    x: multiplication_result_arithmetic_share
                })
            }
            _ => unreachable!(),
        }


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

        let _g = init_tracing();
        let mut channels = multi::new_local(3);
        let helper_ch = channels.pop().unwrap();
        let p1_ch = channels.pop().unwrap();
        let p0_ch = channels.pop().unwrap();
        let priv_seed_p0: [u8; 32] = thread_rng().gen();
        let priv_seed_p1: [u8; 32] = thread_rng().gen();
        let joint_seed: [u8; 32] = thread_rng().gen();
        let helper = AstraSetupHelper::new(helper_ch.0, priv_seed_p0, priv_seed_p1, joint_seed);
    
        let astra_setup0 = AstraSetupProvider::new(0, p0_ch.1, priv_seed_p0);
        let astra_setup1 = AstraSetupProvider::new(1, p1_ch.1, priv_seed_p1);
        
        // Setting up circuit
        type RING = u32;
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


        // start helper
        let input_map = (0..8)
            .map(|i| (i, InputBy::P0))
            .chain((8..16).map(|i| (i, InputBy::P1)))
            .collect();
        let circ_clone = circ.clone();
        let jh = tokio::spawn(async move { helper.setup(&circ_clone, input_map).await });

        // Create protocol context
        let mut sharing_state1 = LoreleiSharing::new(0, priv_seed_p0, joint_seed, share_map1);
        let mut sharing_state2 = LoreleiSharing::new(1, priv_seed_p1, joint_seed, share_map2);
        let state1 = BooleanAby2::new(sharing_state1.clone());
        let state2 = BooleanAby2::new(sharing_state2.clone());

        let (mut ex1, mut ex2): (Executor<BooleanAby2, u32>, Executor<BooleanAby2, u32>) =
            tokio::try_join!(
                Executor::new_with_state(state1, &circ, 0, astra_setup0),
                Executor::new_with_state(state2, &circ, 1, astra_setup1)
            )
        .unwrap();
        jh.await.expect("error in helper");

        let inp0 = LoreleiSharing::new().share(vec![2,2,2,2]);
        let inp1 = LoreleiSharing::insecure_default().plain_delta_to_share(mask);
        
        let (mut ch1, mut ch2) = seec_channel::in_memory::new_pair(16);

        let (out0, out1) = tokio::try_join!(
            ex1.execute(Input::Scalar(inp0), &mut ch1.0, &mut ch1.1),
            ex2.execute(Input::Scalar(inp1), &mut ch2.0, &mut ch2.1),
        )?;

        let res = LoreleiSharing::reconstruct(out0.into_scalar().unwrap(), out1.into_scalar().unwrap());

        assert_eq!(vec![16], res);
        Ok(())
    }
}
