pub mod hypercube;
pub mod mle;
pub mod mleg;
pub mod vec;
pub mod vecg;

use ark_std::log2;

/// Return the number of variables that one need for an MLE to
/// batch the list of MLEs
#[inline]
pub fn get_batched_nv(num_var: usize, polynomials_len: usize) -> usize {
    num_var + log2(polynomials_len) as usize
}