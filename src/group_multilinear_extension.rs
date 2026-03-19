use ark_ec::CurveGroup;

/// Dense multilinear extension whose evaluations are group elements.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DenseGroupMultilinearExtension<G: CurveGroup> {
    pub evaluations: Vec<G>,
    pub num_vars: usize,
}

impl<G: CurveGroup> DenseGroupMultilinearExtension<G> {
    pub fn from_evaluations_vec(num_vars: usize, evaluations: Vec<G>) -> Self {
        let expected_len = 1usize << num_vars;
        assert_eq!(
            evaluations.len(),
            expected_len,
            "evaluation size mismatch: expected {}, got {}",
            expected_len,
            evaluations.len()
        );
        Self {
            evaluations,
            num_vars,
        }
    }

    pub fn from_evaluations_slice(num_vars: usize, evaluations: &[G]) -> Self {
        Self::from_evaluations_vec(num_vars, evaluations.to_vec())
    }

    pub fn evaluate(&self, point: &[G::ScalarField]) -> G {
        assert_eq!(
            self.num_vars,
            point.len(),
            "point length mismatch: expected {}, got {}",
            self.num_vars,
            point.len()
        );

        let mut poly = self.evaluations.clone();
        for i in 1..=point.len() {
            let r = point[i - 1];
            for b in 0..(1 << (self.num_vars - i)) {
                poly[b] = poly[b << 1] + (poly[(b << 1) + 1] - poly[b << 1]).mul(r);
            }
        }
        poly[0]
    }
}

#[cfg(test)]
mod tests {
    use super::DenseGroupMultilinearExtension;
    use ark_bls12_381::{Fr, G1Projective};
    use ark_ec::Group;
    use ark_ff::UniformRand;
    use ark_std::ops::Mul;

    #[test]
    fn evaluate_matches_hypercube_points() {
        let mut rng = ark_std::test_rng();
        let g = G1Projective::rand(&mut rng);
        let evals = vec![
            g.mul(Fr::from(1u64)),
            g.mul(Fr::from(2u64)),
            g.mul(Fr::from(3u64)),
            g.mul(Fr::from(4u64)),
        ];
        let mle = DenseGroupMultilinearExtension::from_evaluations_vec(2, evals.clone());

        assert_eq!(mle.evaluate(&[Fr::from(0u64), Fr::from(0u64)]), evals[0]);
        assert_eq!(mle.evaluate(&[Fr::from(1u64), Fr::from(0u64)]), evals[1]);
        assert_eq!(mle.evaluate(&[Fr::from(0u64), Fr::from(1u64)]), evals[2]);
        assert_eq!(mle.evaluate(&[Fr::from(1u64), Fr::from(1u64)]), evals[3]);
    }

    #[test]
    #[should_panic(expected = "evaluation size mismatch")]
    fn constructor_rejects_invalid_length() {
        let g = G1Projective::generator();
        let _ = DenseGroupMultilinearExtension::from_evaluations_vec(2, vec![g; 3]);
    }
}
