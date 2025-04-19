// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

//! This module defines our main mathematical object `VirtualGroupPolynomial`; and
//! various functions associated with it.

use super::errors::ArithErrors;
use ark_ec::CurveGroup;
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use my_poly::evaluations::multivariate::multilinear::{DenseGroupMultilinearExtension, GroupMultilinearExtension};
use ark_serialize::CanonicalSerialize;
use ark_std::{end_timer, start_timer, Zero, One};
use rayon::prelude::*;
use std::{cmp::max, collections::HashMap, marker::PhantomData, ops::Add, sync::Arc};

#[rustfmt::skip]
/// A virtual polynomial is a sum of products of multilinear polynomials;
/// where the multilinear polynomials are stored via their multilinear
/// extensions:  `(coefficient, DenseGroupMultilinearExtension)`
///
/// * Number of products n = `polynomial.products.len()`,
/// * Number of multiplicands of ith product m_i =
///   `polynomial.products[i].1.len()`,
/// * Coefficient of ith product c_i = `polynomial.products[i].0`
///
/// The resulting polynomial is
///
/// $$ \sum_{i=0}^{n} c_i \cdot \prod_{j=0}^{m_i} P_{ij} $$
///
/// Example:
///  f = c0 * f0 * f1 * f2 + c1 * f3 * f4
/// where f0 ... f4 are multilinear polynomials
///
/// - flattened_ml_extensions stores the multilinear extension representation of
///   f0, f1, f2, f3 and f4
/// - products is
///     \[
///         (c0, \[0, 1, 2\]),
///         (c1, \[3, 4\])
///     \]
/// - raw_pointers_lookup_table maps fi to i
///
#[derive(Clone, Debug, Default, PartialEq)]
pub struct VirtualGroupPolynomial<G: CurveGroup> {
    /// Aux information about the multilinear polynomial
    pub aux_info: VGPAuxInfo<G>,
    /// list of reference to products (as usize) of multilinear extension
    pub products: Vec<(G, Vec<usize>)>,
    /// Stores multilinear extensions in which product multiplicand can refer
    /// to.
    pub flattened_ml_extensions: Vec<Arc<DenseMultilinearExtension<G::ScalarField>>>,
    /// Pointers to the above poly extensions
    raw_pointers_lookup_table: HashMap<*const DenseMultilinearExtension<G::ScalarField>, usize>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, CanonicalSerialize)]
/// Auxiliary information about the multilinear polynomial
pub struct VGPAuxInfo<G: CurveGroup> {
    /// max number of multiplicands in each product
    pub max_degree: usize,
    /// number of variables of the polynomial
    pub num_variables: usize,
    /// Associated field
    #[doc(hidden)]
    pub phantom: PhantomData<G>,
}

impl<G: CurveGroup> Add for &VirtualGroupPolynomial<G> {
    type Output = VirtualGroupPolynomial<G>;
    fn add(self, other: &VirtualGroupPolynomial<G>) -> Self::Output {
        let start = start_timer!(|| "virtual poly add");
        let mut res = self.clone();
        for products in other.products.iter() {
            let cur: Vec<Arc<DenseMultilinearExtension<G::ScalarField>>> = products
                .1
                .iter()
                .map(|&x| other.flattened_ml_extensions[x].clone())
                .collect();

            res.add_mle_list(cur, products.0)
                .expect("add product failed");
        }
        end_timer!(start);
        res
    }
}

// TODO: convert this into a trait
impl<G: CurveGroup> VirtualGroupPolynomial<G> {
    /// Creates an empty virtual polynomial with `num_variables`.
    pub fn new(num_variables: usize) -> Self {
        VirtualGroupPolynomial {
            aux_info: VGPAuxInfo {
                max_degree: 0,
                num_variables,
                phantom: PhantomData::default(),
            },
            products: Vec::new(),
            flattened_ml_extensions: Vec::new(),
            raw_pointers_lookup_table: HashMap::new(),
        }
    }

    /// Creates an new virtual polynomial from a MLE and its coefficient.
    pub fn new_from_mle(mle: &Arc<DenseMultilinearExtension<G::ScalarField>>, coefficient: G) -> Self {
        let mle_ptr: *const DenseMultilinearExtension<G::ScalarField> = Arc::as_ptr(mle);
        let mut hm = HashMap::new();
        hm.insert(mle_ptr, 0);

        VirtualGroupPolynomial {
            aux_info: VGPAuxInfo {
                // The max degree is the max degree of any individual variable
                max_degree: 1,
                num_variables: mle.num_vars,
                phantom: PhantomData::default(),
            },
            // here `0` points to the first polynomial of `flattened_ml_extensions`
            products: vec![(coefficient, vec![0])],
            flattened_ml_extensions: vec![mle.clone()],
            raw_pointers_lookup_table: hm,
        }
    }
    /// Add a product of list of multilinear extensions to self
    /// Returns an error if the list is empty, or the MLE has a different
    /// `num_vars` from self.
    ///
    /// The MLEs will be multiplied together, and then multiplied by the group
    /// `coefficient`.
    pub fn add_mle_list(
        &mut self,
        mle_list: impl IntoIterator<Item = Arc<DenseMultilinearExtension<G::ScalarField>>>,
        coefficient: G,
    ) -> Result<(), ArithErrors> {
        let mle_list: Vec<Arc<DenseMultilinearExtension<G::ScalarField>>> = mle_list.into_iter().collect();
        let mut indexed_product = Vec::with_capacity(mle_list.len());

        if mle_list.is_empty() {
            return Err(ArithErrors::InvalidParameters(
                "input mle_list is empty".to_string(),
            ));
        }

        self.aux_info.max_degree = max(self.aux_info.max_degree, mle_list.len());

        for mle in mle_list {
            if mle.num_vars != self.aux_info.num_variables {
                return Err(ArithErrors::InvalidParameters(format!(
                    "product has a multiplicand with wrong number of variables {} vs {}",
                    mle.num_vars, self.aux_info.num_variables
                )));
            }

            let mle_ptr: *const DenseMultilinearExtension<G::ScalarField> = Arc::as_ptr(&mle);
            if let Some(index) = self.raw_pointers_lookup_table.get(&mle_ptr) {
                indexed_product.push(*index)
            } else {
                let curr_index = self.flattened_ml_extensions.len();
                self.flattened_ml_extensions.push(mle.clone());
                self.raw_pointers_lookup_table.insert(mle_ptr, curr_index);
                indexed_product.push(curr_index);
            }
        }
        self.products.push((coefficient, indexed_product));
        Ok(())
    }

    /// Multiple the current VirtualGroupPolynomial by an MLE:
    /// - add the MLE to the MLE list;
    /// - multiple each product by MLE and its coefficient.
    /// Returns an error if the MLE has a different `num_vars` from self.
    pub fn mul_by_mle(
        &mut self,
        mle: Arc<DenseMultilinearExtension<G::ScalarField>>,
        coefficient: G::ScalarField,
    ) -> Result<(), ArithErrors> {
        let start = start_timer!(|| "mul by mle");

        if mle.num_vars != self.aux_info.num_variables {
            return Err(ArithErrors::InvalidParameters(format!(
                "product has a multiplicand with wrong number of variables {} vs {}",
                mle.num_vars, self.aux_info.num_variables
            )));
        }

        let mle_ptr: *const DenseMultilinearExtension<G::ScalarField> = Arc::as_ptr(&mle);

        // check if this mle already exists in the virtual polynomial
        let mle_index = match self.raw_pointers_lookup_table.get(&mle_ptr) {
            Some(&p) => p,
            None => {
                self.raw_pointers_lookup_table
                    .insert(mle_ptr, self.flattened_ml_extensions.len());
                self.flattened_ml_extensions.push(mle);
                self.flattened_ml_extensions.len() - 1
            }
        };

        for (prod_coef, indices) in self.products.iter_mut() {
            // - add the MLE to the MLE list;
            // - multiple each product by MLE and its coefficient.
            indices.push(mle_index);
            *prod_coef *= coefficient;
        }

        // increase the max degree by one as the MLE has degree 1.
        self.aux_info.max_degree += 1;
        end_timer!(start);
        Ok(())
    }

    /// Given virtual polynomial `p(x)` and scalar `s`, compute `s*p(x)`
    pub fn scalar_mul(&mut self, s: &G::ScalarField) {
        for i in 0..self.products.len() {
            self.products[i].0 = self.products[i].0.mul(s);
        }
    }

    /// Evaluate the virtual polynomial at point `point`.
    /// Returns an error is point.len() does not match `num_variables`.
    pub fn evaluate(&self, point: &[G::ScalarField]) -> Result<G, ArithErrors> {
        let start = start_timer!(|| "evaluation");

        if self.aux_info.num_variables != point.len() {
            return Err(ArithErrors::InvalidParameters(format!(
                "wrong number of variables {} vs {}",
                self.aux_info.num_variables,
                point.len()
            )));
        }

        // Evaluate all the MLEs at `point`
        let evals: Vec<G::ScalarField> = self
            .flattened_ml_extensions
            .iter()
            .map(|x| {
                x.evaluate(point).unwrap() // safe unwrap here since we have
                                           // already checked that num_var
                                           // matches
            })
            .collect();

        let res = self
            .products
            .iter()
            .map(|(c, p)| c.mul(p.iter().map(|&i| evals[i]).product::<G::ScalarField>()))
            .sum();

        end_timer!(start);
        Ok(res)
    }

    // Input poly f(x) and a random vector r, output
    //      \hat f(x) = \sum_{x_i \in eval_x} f(x_i) eq(x, r)
    // where
    //      eq(x,y) = \prod_i=1^num_var (x_i * y_i + (1-x_i)*(1-y_i))
    //
    // This function is used in ZeroCheck.
    pub fn build_f_hat(&self, r: &[G::ScalarField]) -> Result<Self, ArithErrors> {
        let start = start_timer!(|| "zero check build hat f");

        if self.aux_info.num_variables != r.len() {
            return Err(ArithErrors::InvalidParameters(format!(
                "r.len() is different from number of variables: {} vs {}",
                r.len(),
                self.aux_info.num_variables
            )));
        }

        let eq_x_r = build_eq_x_r::<G>(r)?;
        let mut res = self.clone();
        res.mul_by_mle(eq_x_r, G::ScalarField::one())?;

        end_timer!(start);
        Ok(res)
    }
}

/// Evaluate eq polynomial.
pub fn eq_eval<G: CurveGroup>(x: &[G::ScalarField], y: &[G::ScalarField]) -> Result<G::ScalarField, ArithErrors> {
    if x.len() != y.len() {
        return Err(ArithErrors::InvalidParameters(
            "x and y have different length".to_string(),
        ));
    }
    let start = start_timer!(|| "eq_eval");
    let mut res = G::ScalarField::one();
    for (&xi, &yi) in x.iter().zip(y.iter()) {
        let xi_yi = xi * yi;
        res *= xi_yi + xi_yi - xi - yi + G::ScalarField::one();
    }
    end_timer!(start);
    Ok(res)
}

/// This function build the eq(x, r) polynomial for any given r.
///
/// Evaluate
///      eq(x,y) = \prod_i=1^num_var (x_i * y_i + (1-x_i)*(1-y_i))
/// over r, which is
///      eq(x,y) = \prod_i=1^num_var (x_i * r_i + (1-x_i)*(1-r_i))
fn build_eq_x_r<G: CurveGroup>(r: &[G::ScalarField]) -> Result<Arc<DenseMultilinearExtension<G::ScalarField>>, ArithErrors> {
    let evals = build_eq_x_r_vec::<G>(r)?;
    let mle = DenseMultilinearExtension::from_evaluations_vec(r.len(), evals);

    Ok(Arc::new(mle))
}
/// This function build the eq(x, r) polynomial for any given r, and output the
/// evaluation of eq(x, r) in its vector form.
///
/// Evaluate
///      eq(x,y) = \prod_i=1^num_var (x_i * y_i + (1-x_i)*(1-y_i))
/// over r, which is
///      eq(x,y) = \prod_i=1^num_var (x_i * r_i + (1-x_i)*(1-r_i))
fn build_eq_x_r_vec<G: CurveGroup>(r: &[G::ScalarField]) -> Result<Vec<G::ScalarField>, ArithErrors> {
    // we build eq(x,r) from its evaluations
    // we want to evaluate eq(x,r) over x \in {0, 1}^num_vars
    // for example, with num_vars = 4, x is a binary vector of 4, then
    //  0 0 0 0 -> (1-r0)   * (1-r1)    * (1-r2)    * (1-r3)
    //  1 0 0 0 -> r0       * (1-r1)    * (1-r2)    * (1-r3)
    //  0 1 0 0 -> (1-r0)   * r1        * (1-r2)    * (1-r3)
    //  1 1 0 0 -> r0       * r1        * (1-r2)    * (1-r3)
    //  ....
    //  1 1 1 1 -> r0       * r1        * r2        * r3
    // we will need 2^num_var evaluations

    let mut eval = Vec::new();
    build_eq_x_r_helper::<G>(r, &mut eval)?;

    Ok(eval)
}

/// A helper function to build eq(x, r) recursively.
/// This function takes `r.len()` steps, and for each step it requires a maximum
/// `r.len()-1` multiplications.
fn build_eq_x_r_helper<G: CurveGroup>(r: &[G::ScalarField], buf: &mut Vec<G::ScalarField>) -> Result<(), ArithErrors> {
    if r.is_empty() {
        return Err(ArithErrors::InvalidParameters("r length is 0".to_string()));
    } else if r.len() == 1 {
        // initializing the buffer with [1-r_0, r_0]
        buf.push(G::ScalarField::one() - r[0]);
        buf.push(r[0]);
    } else {
        build_eq_x_r_helper::<G>(&r[1..], buf)?;

        // suppose at the previous step we received [b_1, ..., b_k]
        // for the current step we will need
        // if x_0 = 0:   (1-r0) * [b_1, ..., b_k]
        // if x_0 = 1:   r0 * [b_1, ..., b_k]
        // let mut res = vec![];
        // for &b_i in buf.iter() {
        //     let tmp = r[0] * b_i;
        //     res.push(b_i - tmp);
        //     res.push(tmp);
        // }
        // *buf = res;

        let mut res = vec![G::ScalarField::zero(); buf.len() << 1];
        res.par_iter_mut().enumerate().for_each(|(i, val)| {
            let bi = buf[i >> 1];
            let tmp = r[0] * bi;
            if i & 1 == 0 {
                *val = bi - tmp;
            } else {
                *val = tmp;
            }
        });
        *buf = res;
    }

    Ok(())
}

/// Decompose an integer into a binary vector in little endian.
pub fn bit_decompose(input: u64, num_var: usize) -> Vec<bool> {
    let mut res = Vec::with_capacity(num_var);
    let mut i = input;
    for _ in 0..num_var {
        res.push(i & 1 == 1);
        i >>= 1;
    }
    res
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::multilinear_polynomial::testing_code::random_mle_list;
    use crate::virtual_polynomial::VirtualPolynomial;
    use ark_bls12_381::{Fr, G1Projective};
    use ark_ff::UniformRand;
    use ark_std::{
        rand::{Rng, RngCore},
        test_rng,
        ops::Mul,
    };

    impl<G: CurveGroup> VirtualGroupPolynomial<G> {
        /// Sample a random virtual polynomial, return the polynomial and its sum.
        fn rand<R: RngCore>(
            nv: usize,
            num_multiplicands_range: (usize, usize),
            num_products: usize,
            rng: &mut R,
        ) -> Result<(Self, G), ArithErrors> {
            let start = start_timer!(|| "sample random virtual polynomial");

            let mut sum = G::zero();
            let mut poly = VirtualGroupPolynomial::<G>::new(nv);
            for _ in 0..num_products {
                let num_multiplicands =
                    rng.gen_range(num_multiplicands_range.0..num_multiplicands_range.1);
                let (product, product_sum) = random_mle_list(nv, num_multiplicands, rng);
                let coefficient = G::rand(rng);
                poly.add_mle_list(product.into_iter(), coefficient)?;
                sum += coefficient.mul(product_sum);
            }

            end_timer!(start);
            Ok((poly, sum))
        }
    }

    #[test]
    fn test_virtual_polynomial_additions() -> Result<(), ArithErrors> {
        let mut rng = test_rng();
        for nv in 2..5 {
            for num_products in 2..5 {
                let base: Vec<Fr> = (0..nv).map(|_| Fr::rand(&mut rng)).collect();

                let (a, _a_sum) =
                    VirtualGroupPolynomial::<G1Projective>::rand(nv, (2, 3), num_products, &mut rng)?;
                let (b, _b_sum) =
                    VirtualGroupPolynomial::<G1Projective>::rand(nv, (2, 3), num_products, &mut rng)?;
                let c = &a + &b;

                assert_eq!(
                    a.evaluate(base.as_ref())? + b.evaluate(base.as_ref())?,
                    c.evaluate(base.as_ref())?
                );
            }
        }

        Ok(())
    }

    #[test]
    fn test_virtual_polynomial_mul_by_mle() -> Result<(), ArithErrors> {
        let mut rng = test_rng();
        for nv in 2..5 {
            for num_products in 2..5 {
                let base: Vec<Fr> = (0..nv).map(|_| Fr::rand(&mut rng)).collect();

                let (a, _a_sum) =
                    VirtualGroupPolynomial::<G1Projective>::rand(nv, (2, 3), num_products, &mut rng)?;
                let (b, _b_sum) = random_mle_list(nv, 1, &mut rng);
                let b_mle = b[0].clone();
                let coeff_f = Fr::rand(&mut rng);
                let b_vp = VirtualPolynomial::<Fr>::new_from_mle(&b_mle, coeff_f);
                let mut c = a.clone();                
                c.mul_by_mle(b_mle, coeff_f)?;

                let a_eval = a.evaluate(base.as_ref()).unwrap();
                let c_eval = c.evaluate(base.as_ref()).unwrap();
                let b_eval = b_vp.evaluate(base.as_ref()).unwrap();
                assert_eq!(
                    a_eval.mul(b_eval),
                    c_eval
                );
            }
        }

        Ok(())
    }

    #[test]
    fn test_eq_xr() {
        let mut rng = test_rng();
        for nv in 4..10 {
            let r: Vec<Fr> = (0..nv).map(|_| Fr::rand(&mut rng)).collect();
            let eq_x_r = build_eq_x_r::<G1Projective>(r.as_ref()).unwrap();
            let eq_x_r2 = build_eq_x_r_for_test::<G1Projective>(r.as_ref());
            assert_eq!(eq_x_r, eq_x_r2);
        }
    }

    /// Naive method to build eq(x, r).
    /// Only used for testing purpose.
    // Evaluate
    //      eq(x,y) = \prod_i=1^num_var (x_i * y_i + (1-x_i)*(1-y_i))
    // over r, which is
    //      eq(x,y) = \prod_i=1^num_var (x_i * r_i + (1-x_i)*(1-r_i))
    fn build_eq_x_r_for_test<G: CurveGroup>(r: &[G::ScalarField]) -> Arc<DenseMultilinearExtension<G::ScalarField>> {
        // we build eq(x,r) from its evaluations
        // we want to evaluate eq(x,r) over x \in {0, 1}^num_vars
        // for example, with num_vars = 4, x is a binary vector of 4, then
        //  0 0 0 0 -> (1-r0)   * (1-r1)    * (1-r2)    * (1-r3)
        //  1 0 0 0 -> r0       * (1-r1)    * (1-r2)    * (1-r3)
        //  0 1 0 0 -> (1-r0)   * r1        * (1-r2)    * (1-r3)
        //  1 1 0 0 -> r0       * r1        * (1-r2)    * (1-r3)
        //  ....
        //  1 1 1 1 -> r0       * r1        * r2        * r3
        // we will need 2^num_var evaluations

        // First, we build array for {1 - r_i}
        let one_minus_r: Vec<G::ScalarField> = r.iter().map(|ri| G::ScalarField::one() - ri).collect();

        let num_var = r.len();
        let mut eval = vec![];

        for i in 0..1 << num_var {
            let mut current_eval = G::ScalarField::one();
            let bit_sequence = bit_decompose(i, num_var);

            for (&bit, (ri, one_minus_ri)) in
                bit_sequence.iter().zip(r.iter().zip(one_minus_r.iter()))
            {
                current_eval *= if bit { *ri } else { *one_minus_ri };
            }
            eval.push(current_eval);
        }

        let mle = DenseMultilinearExtension::from_evaluations_vec(num_var, eval);

        Arc::new(mle)
    }
}