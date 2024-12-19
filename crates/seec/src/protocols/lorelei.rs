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
use rand_chacha::ChaChaRng;
use seec_channel::multi::{MultiReceiver, MultiSender};
use serde::{Deserialize, Serialize};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::convert::Infallible;
use std::error::Error;
use std::fmt::Debug;
use std::ops::Not;

// ring ABY2 protocol (will need ring implementation of aby2.rs)
#[derive(Clone, Debug, Default, Hash, Eq, PartialEq)]
pub struct ABY2<R> {

}

// ring arithmetic GMW like protocol
#[derive(Clone, Debug, Default, Hash, Eq, PartialEq)]
pub struct Arithmetic<R> {

}

// Lorelei Protocol context struct
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


#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct BlindedShare<R> {
    pub(crate) m: R,
    pub(crate) l: R,
}

#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct ArithmeticShare<R> {
    pub(crate) x: R
}



#[derive(Copy, Clone, Hash, PartialOrd, Ord, PartialEq, Eq, Debug, Default)]
pub struct LoreleiShare<R> {
    pub(crate) b: BlindedShare<R>,
    pub(crate) a: ArithmeticShare<R>
}




/// Contains preprocessing data (`[\delta_ab]_i`) for interactive gates in
/// **reverse** topological order. This is needed to evaluate interactive gates.
#[derive(Clone, Default)]
pub struct SetupData {
    eval_shares: Vec<EvalShares>,
}

#[derive(Clone)]
pub struct EvalShares {
    shares: BitVec,
}

// Note: arithmetic has only multiplication by constant
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum ArithmeticGate<R> {
    Base(BaseGate<R>),
    Mult { n: u8 },
    Add { n: u8 },
}

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub enum BlindedGate<R>{
    Base(BaseGate<R>),
    Mult { n: u8 },
    Add { n: u8 },
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





pub type AbySetupMsg = executor::Message<BooleanGmw>;

pub struct AbySetupProvider<Mtp> {
    party_id: usize,
    mt_provider: Mtp,
    sender: seec_channel::Sender<AbySetupMsg>,
    receiver: seec_channel::Receiver<AbySetupMsg>,
    setup_data: Option<SetupData>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AstraSetupMsg(BitVec);

#[derive(Debug, Copy, Clone)]
pub enum InputBy {
    P0,
    P1,
}
pub struct AstraSetupHelper {
    sender: MultiSender<AstraSetupMsg>,
    // shared rng with p0
    priv_seed_p0: [u8; 32],
    // shared rng with p1
    priv_seed_p1: [u8; 32],
    // shared between p0 and p1
    joint_seed: [u8; 32],
}
pub struct AstraSetupProvider {
    // The normal parties have party id 0 and 1. For the helper, there is a dedicated struct
    party_id: usize,
    receiver: MultiReceiver<AstraSetupMsg>,
    rng: ChaChaRng,
    setup_data: Option<SetupData>,
}

impl Gate<R> for ArithmeticGate<R> {
    type DimTy = ScalarDim;

    fn is_interactive(&self) -> bool {
        return false;
    }

    fn input_size(&self) -> usize {
        match self {
            ArithmeticGate::Base(base_gate) => base_gate.input_size(),
            ArithmeticGate::Add => n,
            ArithmeticGate::Mult => 2
        }
    }

    fn as_base_gate(&self) -> Option<&BaseGate<bool>> {
        match self {
            BooleanGate::Base(base_gate) => Some(base_gate),
            _ => None,
        }
    }

    fn wrap_base_gate(base_gate: BaseGate<bool, Self::DimTy>) -> Self {
        Self::Base(base_gate)
    }
}

/*
#[cfg(test)]
mod tests {
    use super::BooleanGate as BG;
    use super::*;
    use crate::circuit::BaseCircuit;
    use crate::mul_triple::boolean::InsecureMTProvider;
    use bitvec::bitvec;
    use bitvec::order::Lsb0;

    #[tokio::test]
    async fn multi_and() {
        let mut c = BaseCircuit::<bool, BG>::new();
        let i0 = c.add_gate(BG::Base(BaseGate::Input(ScalarDim)));
        let i1 = c.add_gate(BG::Base(BaseGate::Input(ScalarDim)));
        let i2 = c.add_gate(BG::Base(BaseGate::Input(ScalarDim)));
        let i3 = c.add_gate(BG::Base(BaseGate::Input(ScalarDim)));
        let a = c.add_wired_gate(BG::And { n: 4 }, &[i0, i1, i2, i3]);
        let _out = c.add_wired_gate(BG::Base(BaseGate::Output(ScalarDim)), &[a]);
        let c = ExecutableCircuit::DynLayers(c.into());

        let (ch0, ch1) = seec_channel::in_memory::new_pair(16);
        let setup0 = AbySetupProvider::new(0, InsecureMTProvider::default(), ch0.0, ch0.1);
        let setup1 = AbySetupProvider::new(1, InsecureMTProvider::default(), ch1.0, ch1.1);
        let p_state = BooleanAby2::new(DeltaSharing::insecure_default());
        let (mut ex1, mut ex2) = tokio::try_join!(
            Executor::new_with_state(p_state.clone(), &c, 0, setup0),
            Executor::new_with_state(p_state, &c, 1, setup1),
        )
        .unwrap();

        let (inp0, mask) = DeltaSharing::insecure_default().share(bitvec!(u8, Lsb0; 1, 1, 1, 1));
        let inp1 = DeltaSharing::insecure_default().plain_delta_to_share(mask);
        let (mut ch1, mut ch2) = seec_channel::in_memory::new_pair(2);

        let h1 = ex1.execute(Input::Scalar(inp0), &mut ch1.0, &mut ch1.1);
        let h2 = ex2.execute(Input::Scalar(inp1), &mut ch2.0, &mut ch2.1);
        let (res1, res2) = tokio::try_join!(h1, h2).unwrap();
        let res =
            DeltaSharing::reconstruct(res1.into_scalar().unwrap(), res2.into_scalar().unwrap());
        assert_eq!(BitVec::<u8>::repeat(true, 1), res);
    }
}
*/
