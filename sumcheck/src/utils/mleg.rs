/// Some basic MLE utilities
use ark_ec::CurveGroup;
use my_poly::evaluations::multivariate::multilinear::DenseGroupMultilinearExtension;
use ark_std::log2;

use super::vec::Matrix;

pub fn group_vec_to_mle<G: CurveGroup>(n_vars: usize, v: &Vec<G>) -> DenseGroupMultilinearExtension<G> {
    // Pad to 2^n_vars
    let v_padded: Vec<G> = [
        v.clone(),
        std::iter::repeat(G::zero())
            .take((1 << n_vars) - v.len())
            .collect(),
    ]
    .concat();
DenseGroupMultilinearExtension::<G>::from_evaluations_vec(n_vars, v_padded)
}

mod tests {
    use crate::utils::{hypercube::BooleanHypercube, vec::to_F_matrix};
    use my_poly::evaluations::multivariate::multilinear::{GroupMultilinearExtension, DenseGroupMultilinearExtension};
    use my_poly::GroupPolynomial;
    use ark_std::{rand::Rng, UniformRand, ops::Mul, Zero};

    use ark_bls12_381::{Fr, G1Projective};

    #[test]
    fn test_vec_to_mle() {
        let mut rng = ark_std::test_rng();
        let eval = vec![0,1,2,3];
        let g = G1Projective::rand(&mut rng);
        let mle = DenseGroupMultilinearExtension::from_evaluations_vec(
            2, 
            eval.iter()
            .map(|x| g.mul(Fr::from(*x as u64)))
            .collect());

        // check that the mle evaluated over the boolean hypercube equals the vec z_i values
        let bhc = BooleanHypercube::new(mle.num_vars);
        for i in 0..eval.len() {
            let s_i = bhc.at_i(i);
            assert_eq!(mle.evaluate(&s_i), g.mul(Fr::from(eval[i])));
        }
        // for the rest of elements of the boolean hypercube, expect it to evaluate to zero
        for i in (eval.len())..(1 << mle.num_vars) {
            let s_i = bhc.at_i(i);
            assert_eq!(mle.evaluate(&s_i), g.mul(Fr::zero()));
        }
    }
}
