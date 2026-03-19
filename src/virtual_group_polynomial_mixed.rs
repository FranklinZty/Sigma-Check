use crate::errors::ArithErrors;
use crate::group_multilinear_extension::DenseGroupMultilinearExtension;
use ark_ec::CurveGroup;
use ark_ff::One;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use ark_serialize::CanonicalSerialize;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Debug, Default, PartialEq)]
pub struct VirtualGroupPolynomialMixed<G: CurveGroup> {
    pub num_variables: usize,
    pub group_mles: Vec<Arc<DenseGroupMultilinearExtension<G>>>,
    pub scalar_mles: Vec<Arc<DenseMultilinearExtension<G::ScalarField>>>,
    pub products: Vec<(Option<usize>, Vec<usize>, G)>,
    group_ptrs: HashMap<*const DenseGroupMultilinearExtension<G>, usize>,
    scalar_ptrs: HashMap<*const DenseMultilinearExtension<G::ScalarField>, usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize)]
pub struct VGPMAuxInfo<G: CurveGroup> {
    pub max_degree: usize,
    pub num_variables: usize,
    #[doc(hidden)]
    pub phantom: std::marker::PhantomData<G>,
}

impl<G: CurveGroup> VirtualGroupPolynomialMixed<G> {
    pub fn new(num_variables: usize) -> Self {
        Self {
            num_variables,
            group_mles: Vec::new(),
            scalar_mles: Vec::new(),
            products: Vec::new(),
            group_ptrs: HashMap::new(),
            scalar_ptrs: HashMap::new(),
        }
    }

    pub fn add_group_mle(
        &mut self,
        mle: Arc<DenseGroupMultilinearExtension<G>>,
    ) -> Result<usize, ArithErrors> {
        if mle.num_vars != self.num_variables {
            return Err(ArithErrors::InvalidParameters(
                "group mle num_vars mismatch".to_string(),
            ));
        }
        let ptr = Arc::as_ptr(&mle);
        if let Some(&idx) = self.group_ptrs.get(&ptr) {
            return Ok(idx);
        }
        let idx = self.group_mles.len();
        self.group_mles.push(mle);
        self.group_ptrs.insert(ptr, idx);
        Ok(idx)
    }

    pub fn add_scalar_mle(
        &mut self,
        mle: Arc<DenseMultilinearExtension<G::ScalarField>>,
    ) -> Result<usize, ArithErrors> {
        if mle.num_vars != self.num_variables {
            return Err(ArithErrors::InvalidParameters(
                "scalar mle num_vars mismatch".to_string(),
            ));
        }
        let ptr = Arc::as_ptr(&mle);
        if let Some(&idx) = self.scalar_ptrs.get(&ptr) {
            return Ok(idx);
        }
        let idx = self.scalar_mles.len();
        self.scalar_mles.push(mle);
        self.scalar_ptrs.insert(ptr, idx);
        Ok(idx)
    }

    pub fn add_product(
        &mut self,
        group_idx: Option<usize>,
        scalar_idxs: Vec<usize>,
        coeff: G,
    ) -> Result<(), ArithErrors> {
        for &idx in scalar_idxs.iter() {
            if idx >= self.scalar_mles.len() {
                return Err(ArithErrors::InvalidParameters(
                    "scalar mle index out of range".to_string(),
                ));
            }
        }
        if let Some(gi) = group_idx {
            if gi >= self.group_mles.len() {
                return Err(ArithErrors::InvalidParameters(
                    "group mle index out of range".to_string(),
                ));
            }
        }
        self.products.push((group_idx, scalar_idxs, coeff));
        Ok(())
    }

    pub fn mul_by_scalar_mle(
        &mut self,
        mle: Arc<DenseMultilinearExtension<G::ScalarField>>,
    ) -> Result<(), ArithErrors> {
        let idx = self.add_scalar_mle(mle)?;
        for (_, scalars, _) in self.products.iter_mut() {
            scalars.push(idx);
        }
        Ok(())
    }

    pub fn aux_info(&self) -> VGPMAuxInfo<G> {
        let mut max_degree = 0usize;
        for (group_idx, scalars, _) in self.products.iter() {
            let deg = scalars.len() + if group_idx.is_some() { 1 } else { 0 };
            if deg > max_degree {
                max_degree = deg;
            }
        }
        VGPMAuxInfo {
            max_degree,
            num_variables: self.num_variables,
            phantom: std::marker::PhantomData,
        }
    }

    pub fn evaluate(&self, point: &[G::ScalarField]) -> Result<G, ArithErrors> {
        if point.len() != self.num_variables {
            return Err(ArithErrors::InvalidParameters(
                "point length mismatch".to_string(),
            ));
        }

        let scalar_evals: Vec<G::ScalarField> = self
            .scalar_mles
            .iter()
            .map(|mle| mle.evaluate(point).unwrap())
            .collect();
        let group_evals: Vec<G> = self
            .group_mles
            .iter()
            .map(|mle| mle.evaluate(point))
            .collect();

        let mut acc = G::zero();
        for (group_idx, scalars, coeff) in self.products.iter() {
            let mut term = *coeff;
            if let Some(gi) = group_idx {
                term += group_evals[*gi];
            }
            let mut scalar_prod = G::ScalarField::one();
            for &si in scalars.iter() {
                scalar_prod *= scalar_evals[si];
            }
            term = term.mul(scalar_prod);
            acc += term;
        }
        Ok(acc)
    }
}
