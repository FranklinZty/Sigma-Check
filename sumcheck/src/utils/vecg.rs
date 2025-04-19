/// Some basic utilities
///
/// Stole a bunch of code from Alex in https://github.com/alex-ozdemir/bulletproofs
/// and wrote some lame tests for it
use ark_ec::CurveGroup;
use ark_std::{cfg_iter, ops::Mul};

use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelRefIterator;
use rayon::iter::ParallelIterator;

// Multiply vector by scalar
pub fn group_vec_scalar_mul<G: CurveGroup>(vec: &[G], c: &G::ScalarField) -> Vec<G> {
    let mut result = vec![G::zero(); vec.len()];
    for (i, a) in vec.iter().enumerate() {
        result[i] = a.mul(c);
    }
    result
}

// Add two vectors
pub fn group_vec_add<G: CurveGroup>(vec_a: &[G], vec_b: &[G]) -> Vec<G> {
    assert_eq!(vec_a.len(), vec_b.len());

    let mut result = vec![G::zero(); vec_a.len()];
    for i in 0..vec_a.len() {
        result[i] = vec_a[i] + vec_b[i];
    }
    result
}

pub fn to_G_vec<G: CurveGroup>(z: Vec<usize>, g: &G) -> Vec<G> {
    let mut r: Vec<G> = vec![G::zero(); z.len()];
    for i in 0..z.len() {
        r[i] = g.mul(G::ScalarField::from(z[i] as u64));
    }
    r
}

#[cfg(test)]
mod test {
    use super::*;
    use ark_std::UniformRand;
    use ark_bls12_381::{Fr, G1Projective};

    #[test]
    fn test_group_vec() -> () {
        let mut rng = ark_std::test_rng();
        let g = G1Projective::rand(&mut rng);
        let v = vec![1, 2, 3];

        // test to_G_vec 
        let vecg_1 = to_G_vec(v.clone(), &g);
        let vecg_2: Vec<G1Projective> = v.iter().map(|x| g.mul(Fr::from(*x as u64))).collect();
        assert_eq!(vecg_1, vecg_2);

        // test scalar mul
        let scalar = Fr::from(3);
        let result = group_vec_scalar_mul(&vecg_1, &scalar);
        let target = to_G_vec(vec![3, 6, 9], &g);

        // test add
        let result = group_vec_add(&vecg_1,&vecg_2);
        let target = to_G_vec(vec![2, 4, 6], &g);
    }
}
