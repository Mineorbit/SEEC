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
        shares: &GateOutputs<LoreleiShareVec<R>>,
        circuit: &ExecutableCircuit<R, LoreleiGate<R>, Idx>,
    ) -> Result<(), Self::Error> {
        let circ_builder: CircuitBuilder<R, LoreleiGate<R>, Idx> =
            CircuitBuilder::new();
        let old = circ_builder.install();
        let total_inputs: usize = circuit
            .interactive_iter()
            .map(|(gate, _)| 2_usize.pow(gate.input_size() as u32))
            .sum();

        let mut circ_inputs = BitVec::<usize>::with_capacity(total_inputs);
        // Block is needed as otherwise !Send types are held over .await
        let setup_outputs: Vec<Vec<_>> = {
            let mut input_sw_map: AHashMap<_, Secret<_, Idx>> =
                AHashMap::with_capacity(total_inputs);
            let mut setup_outputs = Vec::with_capacity(circuit.interactive_count());
            let mut setup_sub_circ_cache = AHashMap::with_capacity(total_inputs);
            for (gate, _gate_id, parents) in circuit.interactive_with_parents_iter() {
                let mut gate_input_shares = vec![];
                parents.for_each(|parent| match input_sw_map.entry(parent) {
                    Entry::Vacant(vacant) => {
                        let sh = Secret::<_, Idx>::input(0);
                        gate_input_shares.push(sh.clone());
                        circ_inputs.push(shares.get(parent).get_private());
                        vacant.insert(sh);
                    }
                    Entry::Occupied(occupied) => {
                        gate_input_shares.push(occupied.get().clone());
                    }
                });

                // TODO does this impact correctness??
                gate_input_shares.sort();

                let t = gate.setup_data_circ(gate_input_shares.iter(), &mut setup_sub_circ_cache);
                setup_outputs.push(t);
            }
            setup_outputs
                .into_iter()
                .map(|v| v.into_iter().map(|opt_sh| opt_sh.output()).collect())
                .collect()
        };

        let setup_data_circ: ExecutableCircuit<R, LoreleiGate, Idx> =
            ExecutableCircuit::DynLayers(CircuitBuilder::global_into_circuit());
        old.install();
        let mut executor: Executor<Lorelei, Idx> =
            Executor::new(&setup_data_circ, self.party_id, &mut self.mt_provider)
                .await
                .expect("Executor::new in AbySetupProvider");
        executor
            .execute(
                Input::Scalar(circ_inputs),
                &mut self.sender,
                &mut self.receiver,
            )
            .await
            .unwrap();
        let Input::Scalar(executor_gate_outputs) = executor.gate_outputs().get_sc(0) else {
            panic!("SIMD not supported for ABY2");
        };

        let eval_shares = circuit
            .interactive_iter()
            .zip(setup_outputs)
            .map(|((gate, _gate_id), setup_out)| match gate {
                ArithmeticGate::Mul { n: u8 } => {
                    let shares = setup_out
                        .into_iter()
                        .map(|out_id| executor_gate_outputs.get(out_id.as_usize()))
                        .collect();
                    DeltaShares { shares }
                }
                _ => unreachable!(),
            })
            .collect();
        self.setup_data = Some(DeltaShareData::from_raw(eval_shares));
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


#[derive(Clone, Debug, Default, Hash, Eq, PartialEq)]
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



impl<R: Ring> Protocol for Lorelei<R> {
    const SIMD_SUPPORT: bool = false;
    type Plain = R;
    type Share = LoreleiShare<R>;
    type Msg = Msg;
    type SimdMsg = ();
    type Gate = LoreleiGate<R>;
    type Wire = ();
    type ShareStorage = LoreleiShareVec<R>;
    type SetupStorage = DeltaShareData<R>;

    fn share_constant(
        &self,
        _party_id: usize,
        output_share: Self::Share,
        val: Self::Plain,
    ) -> Self::Share {
        assert!(
            !output_share.l,
            "Private part of constant share must be 0"
        );
        Self::Share {
            m: val,
            l: false,
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
            BlindedGate::Mul { .. } => {
                panic!("Called evaluate_non_interactive on Gate::And<N>")
            }
            BlindedGate::Add => {
                let acc: R = 0;
                for input in inputs
                {
                    acc = acc.wrapping_add(&input.m);
                }
                acc
            }
        }
    }

    // there are no interactive gates so this is never called
    fn compute_msg(
        &self,
        party_id: usize,
        interactive_gates: impl Iterator<Item = LoreleiGate>,
        gate_outputs: impl Iterator<Item = Self::Share>,
        mut inputs: impl Iterator<Item = Self::Share>,
        preprocessing_data: &mut Self::SetupStorage,
    ) -> Self::Msg {
        assert!(false)
    }

    // there are no interactive gates so this is never called
    fn evaluate_interactive(
        &self,
        _party_id: usize,
        _interactive_gates: impl Iterator<Item = LoreleiGate>,
        gate_outputs: impl Iterator<Item = Self::Share>,
        Msg::Delta { delta }: Self::Msg,
        Msg::Delta { delta: other_delta }: Self::Msg,
        _preprocessing_data: &mut Self::SetupStorage,
    ) -> Self::ShareStorage {
        assert!(false)
    }

    fn setup_gate_outputs<Idx: GateIdx>(
        &mut self,
        _party_id: usize,
        circuit: &ExecutableCircuit<Self::Plain, Self::Gate, Idx>,
    ) -> GateOutputs<Self::ShareStorage> {
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


impl<R> SetupStorage for DeltaShareData<R> {
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


#[derive(Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct LoreleiShare<R> {
    pub(crate) b: BlindedShare<R>,
    pub(crate) a: ArithmeticShare<R>
}

impl<R> Share for LoreleiShare<R> {

}


#[derive(Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct LoreleiShareVec<R: Ring> {
    pub(crate) b: Vec<BlindedShare<R>>,
    pub(crate) a: Vec<ArithmeticShare<R>>
}

impl<R: Ring> ShareStorage<Share> for LoreleiShareVec<R> {
    fn len(&self) -> usize {
        cmp::max(self.a.len(),self.b.len())
    }

    fn repeat(val: Share, len: usize) -> Self {
        Self {
            a: BitVec::repeat(val.a, len),
            b: BitVec::repeat(val.b, len),
        }
    }

    fn set(&mut self, idx: usize, val: Share) {
        self.a.set(idx, val.a);
        self.b.set(idx, val.b);
    }

    fn get(&self, idx: usize) -> Share {
        LoreleiShare {
            a: self.a[idx],
            b: self.b[idx],
        }
    }
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



#[derive(Debug)]
pub struct LoreleiSharing<B, A, R> {
    bool: B,
    arith: A,
    ring: PhantomData<R>,
}




// ---- Gate Structure

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum LoreleiGate<R> {
    Base(BaseGate<Lorelei<R>>),
    Arith(ArithmeticGate<R>),
    Conv(ConvGate),
}


impl<R: Ring>  Gate<R> for LoreleiGate<R> {
    type DimTy = ScalarDim;

    fn is_interactive(&self) -> bool {
        match &self {
            LoreleiGate::Base(g) => { g.is_interactive()
            }
            LoreleiGate::Arith(g) => {g.is_interactive()
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


impl<R> From<BaseGate<R>> for LoreleiGate<R> {
    fn from(base_gate: BaseGate<R>) -> Self {
        LoreleiGate::Base(base_gate)
    }
}



// Gate Mode

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Mode<R> {
    Blinded(R),
    Arith(R),
}

#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum ConvGate {
    Blinded2Arithmetic,
    Arithmetic2Blinded
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
        let reshare = arith2blinded(&mut c, a);
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
