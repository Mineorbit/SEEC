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



// 2 party OT based setup provider


pub type LoreleiSetupMsg<R> = executor::Message<Lorelei<R>>;

pub struct LoreleiSetupProvider<Mtp,R: Ring> {
    party_id: usize,
    mt_provider: Mtp,
    sender: seec_channel::Sender<LoreleiSetupMsg<R>>,
    receiver: seec_channel::Receiver<LoreleiSetupMsg<R>>,
    setup_data: Option<DeltaShareData<R>>,
}

#[async_trait]
impl<MtpErr, Mtp, Idx, R: Ring> FunctionDependentSetup<Lorelei<R>, Idx> for LoreleiSetupProvider<Mtp,R>
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
        // TODO: redo from aby boolean example but with rolled in structure

        
        //self.setup_data = Some(DeltaShareData::from_raw(eval_shares));
        Ok(())
    }

    async fn request_setup_output(&mut self, count: usize) -> Result<DeltaShareData<R>, Self::Error> {
        Ok(self
            .setup_data
            .as_mut()
            .expect("setup must be called before request_setup_output")
            .split_off_last(count))
    }
}



// -----  ring Lorelei combined arithmetic and blinded protocol


#[derive(Clone, Debug, Default)]
pub struct Lorelei<R: Ring> {
    delta_sharing_state: BlindedSharingContext,
    _p: PhantomData<R>
}

#[derive(Clone, Debug)]
pub struct BlindedSharingContext {
    pub(crate) private_rng: ChaChaRng,
    pub(crate) local_joint_rng: ChaChaRng,
    pub(crate) remote_joint_rng: ChaChaRng,
}

impl Default for BlindedSharingContext {
    fn default() -> Self {
        todo!()
    }
}



impl<R: Ring> Protocol for Lorelei<R> {
    const SIMD_SUPPORT: bool = false;
    type Plain = R;
    type Share = LoreleiShare<R>;
    type Msg = Msg;
    type SimdMsg = ();
    type Gate = LoreleiGate<R>;
    type Wire = ();
    type ShareStorage = ShareStorage<LoreleiShare<R>>;
    type SetupStorage = DeltaShareData<R>;

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
                blindedShare.m = val;
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
                            LoreleiShare::Blinded (BlindedShare {m: sumMask, l:sumLambda})
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
                        let input = inputs.next();
                        assert!(matches!(input,LoreleiShare::Blinded(_)));
                        match input 
                        {
                            LoreleiShare::Blinded(blindedShare) => 
                            {
                                let outShareValue = blindedShare.l;
                                if party_id == 0
                                {
                                    outShareValue.wrapping_add(blindedShare.m);
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
    fn compute_msg( &self, party_id: usize, interactive_gates: impl Iterator<Item = LoreleiGate<R>>, gate_outputs: impl Iterator<Item = Self::Share>, mut inputs: impl Iterator<Item = Self::Share>, preprocessing_data: &mut Self::SetupStorage, ) -> Self::Msg 
    {        
        let m: Vec<R> = interactive_gates
        .zip(gate_outputs)
        .map(|(gate, output)| {
            assert!(matches!(gate, LoreleiGate::Conv(ConvGate::Arithmetic2Blinded)));
            let inputs = inputs.by_ref().take(gate.input_size());
            gate.compute_delta_share(party_id, inputs, preprocessing_data, output)
        }).collect();
    Msg::Delta { m }
    }

    // on arith 2 blinded conv gate, add together my arithmetic share of m with other arithmetic share
    fn evaluate_interactive(&self, _party_id: usize, _interactive_gates: impl Iterator<Item = LoreleiGate<R>>, gate_outputs: impl Iterator<Item = Self::Share>, Msg::Delta { m_arith }: Self::Msg, Msg::Delta { delta: other_m_arith }: Self::Msg, _preprocessing_data: &mut Self::SetupStorage,) -> Self::ShareStorage 
    {
        gate_outputs
            .zip(m_arith).zip(other_m_arith)
            .map(|((mut out_share, my_m_arith), other_m_arith)| {
                out_share.m = my_m_arith.wrapping_add(&other_m_arith);
                out_share
            }).collect()
    }

    fn setup_gate_outputs<Idx: GateIdx>(&mut self, _party_id: usize, circuit: &ExecutableCircuit<Self::Plain, Self::Gate, Idx>,) -> GateOutputs<Self::ShareStorage> 
    {
        assert!(false);
    }
}





#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Msg {
    Delta { delta: Vec<u8> },
}




// ---- Sharing structure


// Setup (Offline Shares)

#[derive(Clone, Default)]
pub struct DeltaShareData<R> {
    eval_shares: Vec<DeltaShares<R>>,
}

#[derive(Clone)]
pub struct DeltaShares<R> {
    shares: Vec<R>,
}


impl<R: Ring> SetupStorage for DeltaShareData<R> {
    fn len(&self) -> usize {
        self.eval_shares.len()
    }

    fn split_off_last(&mut self, count: usize) -> Self {
        Self {
            eval_shares: self.eval_shares.split_off(self.len() - count),
        }
    }
    fn reserve(&mut self, additional: usize) {
        self.eval_shares.reserve(additional);
    }

    fn append(&mut self, mut other: Self) {
        self.eval_shares.append(&mut other.eval_shares);
    }
}


// Computation (Online Shares)

#[derive(Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub enum LoreleiShare<R: Ring> {
    Arithmetic(ArithmeticShare<R>),
    Blinded(BlindedShare<R>)
}

impl<R: Ring> Default for LoreleiShare<R> {
    fn default() -> Self {
        LoreleiShare::Arithmetic(ArithmeticShare::default()) // Specify the default variant and its values
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
        let a = circuit.add_wired_gate(LG::Mult { n: 3 }, &[i0, i1, i2]);
        let reshare = arith2blinded(&mut circuit, a);
        let b = circuit.add_wired_gate(LG::Mult { n: 2 }, &[reshare, i3]);
        let _out = circuit.add_wired_gate(LG::Base(BaseGate::Output(ScalarDim)), &[b]);
        let circuit = ExecutableCircuit::DynLayers(circuit.into());


        // Create protocol context
        let out = execute_circuit::<Lorelei<RING>, DefaultIdx, MixedSharing<_, _, RING>>(
            &circuit,
            (2,2,2,2),
            TestChannel::InMemory,
        )
        .await?;
        let mut exp = BitVec::from_element(8);
        exp.truncate(32);
        let exp = MixedShareStorage::Bool(exp);
        assert_eq!(out, exp);
        Ok(())
    }
}
