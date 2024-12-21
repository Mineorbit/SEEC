use crate::circuit::{ExecutableCircuit, GateIdx};
use crate::common::BitVec;
use crate::executor::{Executor, GateOutputs, Input};
use crate::gate::base::BaseGate;
use crate::mul_triple::boolean::MulTriples;
use crate::mul_triple::MTProvider;
use crate::protocols::{
    Ring, FunctionDependentSetup, Gate, Protocol, ScalarDim, SetupStorage, ShareStorage,
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

// -----  ring ABY2 protocol (will need ring implementation of aby2.rs)

#[derive(Clone, Debug, Default, Hash, Eq, PartialEq)]
pub struct ABY2<R> {

}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Msg {
    Delta { delta: Vec<u8> },
}

/// Contains preprocessing data (`[\delta_ab]_i`) for interactive gates in
/// **reverse** topological order. This is needed to evaluate interactive gates.
#[derive(Clone, Default)]
pub struct DeltaShareData<R> {
    eval_shares: Vec<DeltaShares<R>>,
}

#[derive(Clone)]
pub struct DeltaShares<R> {
    shares: Vec<R>,
}


pub type Aby2SetupMsg = executor::Message<ABY2>;

pub struct Aby2SetupProvider<Mtp,R> {
    party_id: usize,
    mt_provider: Mtp,
    sender: seec_channel::Sender<Aby2SetupMsg>,
    receiver: seec_channel::Receiver<Aby2SetupMsg>,
    setup_data: Option<DeltaShareData<R>>,
}


#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct BlindedShare<R> {
    pub(crate) m: R,
    pub(crate) l: R,
}




#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum BlindedGate<R>{
    Base(BaseGate<R>),
    Mult { n: u8 },
    Add { n: u8 },
}





// -----  ring arithmetic GMW like protocol


#[derive(Clone, Debug, Default, Hash, Eq, PartialEq)]
pub struct Arithmetic<R> {

}

#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct ArithmeticShare<R> {
    pub(crate) x: R
}

// Note: arithmetic has only multiplication by constant
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum ArithmeticGate<R> {
    Base(BaseGate<R>),
    Mult { n: u8 },
    Add { n: u8 },
}



// -----  ring Lorelei combined arithmetic and blinded protocol



#[derive(Clone, Debug, Default, Hash, Eq, PartialEq)]
pub struct Lorelei<R> {
    b: ABY2<R>,
    a: Arithmetic<R>,
}

// Gate Mode
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Mode<R> {
    Blinded(R),
    Arith(R),
}

#[derive(Debug)]
pub struct LoreleiSharing<B, A, R> {
    bool: B,
    arith: A,
    ring: PhantomData<R>,
}




#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct LoreleiShare<R> {
    pub(crate) b: BlindedShare<R>,
    pub(crate) a: ArithmeticShare<R>
}



#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum ConvGate {
    Blinded2Arithmetic,
    Arithmetic2Blinded
}


#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum LoreleiGate<R> {
    Base(BaseGate<Lorelei<R>>),
    Blinded(BlindedGate<R>),
    Arith(ArithmeticGate<R>),
    Conv(ConvGate),
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
