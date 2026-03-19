use crate::virtual_group_polynomial_mixed::VirtualGroupPolynomialMixed;
use ark_ec::CurveGroup;
use ark_serialize::CanonicalSerialize;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct IOPProof<G: CurveGroup> {
    pub point: Vec<G::ScalarField>,
    pub proofs: Vec<IOPProverMessage<G>>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize)]
pub struct IOPProverMessage<G: CurveGroup> {
    pub(crate) evaluations: Vec<G>,
}

#[derive(Debug)]
pub struct IOPProverState<G: CurveGroup> {
    pub challenges: Vec<G::ScalarField>,
    pub round: usize,
    pub num_vars: usize,
    pub max_degree: usize,
    pub poly: VirtualGroupPolynomialMixed<G>,
}

#[derive(Debug)]
pub struct IOPVerifierState<G: CurveGroup> {
    pub round: usize,
    pub num_vars: usize,
    pub max_degree: usize,
    pub finished: bool,
    pub polynomials_received: Vec<Vec<G>>,
    pub challenges: Vec<G::ScalarField>,
}
