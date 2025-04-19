//! Multilinear polynomial represented in dense evaluation form.

use crate::{
    evaluations::multivariate::multilinear::{swap_bits, GroupMultilinearExtension},
    GroupPolynomial,
};
use ark_ec::CurveGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    Zero,
    fmt,
    fmt::Formatter,
    ops::{Add, AddAssign, Index, Neg, Sub, SubAssign},
    rand::Rng,
    slice::{Iter, IterMut},
    vec::*,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// Stores a multilinear polynomial in dense evaluation form.
#[derive(Clone, PartialEq, Eq, Hash, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct DenseGroupMultilinearExtension<G: CurveGroup> {
    /// The evaluation over {0,1}^`num_vars`
    pub evaluations: Vec<G>,
    /// Number of variables
    pub num_vars: usize,
}

impl<G: CurveGroup> DenseGroupMultilinearExtension<G> {
    /// Construct a new polynomial from a list of evaluations where the index
    /// represents a point in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_slice(num_vars: usize, evaluations: &[G]) -> Self {
        Self::from_evaluations_vec(num_vars, evaluations.to_vec())
    }

    /// Construct a new polynomial from a list of evaluations where the index
    /// represents a point in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`
    pub fn from_evaluations_vec(num_vars: usize, evaluations: Vec<G>) -> Self {
        // assert that the number of variables matches the size of evaluations
        assert_eq!(
            evaluations.len(),
            1 << num_vars,
            "The size of evaluations should be 2^num_vars."
        );

        Self {
            num_vars,
            evaluations,
        }
    }
    /// Relabel the point in place by switching `k` scalars from position `a` to
    /// position `b`, and from position `b` to position `a` in vector.
    ///
    /// This function turns `P(x_1,...,x_a,...,x_{a+k - 1},...,x_b,...,x_{b+k - 1},...,x_n)`
    /// to `P(x_1,...,x_b,...,x_{b+k - 1},...,x_a,...,x_{a+k - 1},...,x_n)`
    pub fn relabel_in_place(&mut self, mut a: usize, mut b: usize, k: usize) {
        // enforce order of a and b
        if a > b {
            ark_std::mem::swap(&mut a, &mut b);
        }
        if a == b || k == 0 {
            return;
        }
        assert!(b + k <= self.num_vars, "invalid relabel argument");
        assert!(a + k <= b, "overlapped swap window is not allowed");
        for i in 0..self.evaluations.len() {
            let j = swap_bits(i, a, b, k);
            if i < j {
                self.evaluations.swap(i, j);
            }
        }
    }

    /// Returns an iterator that iterates over the evaluations over {0,1}^`num_vars`
    pub fn iter(&self) -> Iter<'_, G> {
        self.evaluations.iter()
    }

    /// Returns a mutable iterator that iterates over the evaluations over {0,1}^`num_vars`
    pub fn iter_mut(&mut self) -> IterMut<'_, G> {
        self.evaluations.iter_mut()
    }
}

impl<G: CurveGroup> GroupMultilinearExtension<G> for DenseGroupMultilinearExtension<G> {
    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn rand<R: Rng>(num_vars: usize, rng: &mut R) -> Self {
        Self::from_evaluations_vec(
            num_vars,
            (0..(1 << num_vars)).map(|_| G::rand(rng)).collect(),
        )
    }

    fn relabel(&self, a: usize, b: usize, k: usize) -> Self {
        let mut copied = self.clone();
        copied.relabel_in_place(a, b, k);
        copied
    }

    /// Return the MLE resulting from binding the first variables of self
    /// to the values in `partial_point` (from left to right).
    /// # Example
    /// 
    /// Note: this method can be used in combination with `relabel` or
    /// `relabel_in_place` to bind variables at arbitrary positions.
    ///
    /// ```
    /// use ark_test_curves::bls12_381::{Fr, G1Projective};
    /// # use ark_poly::{GroupMultilinearExtension, DenseGroupMultilinearExtension};
    ///
    /// let mut rng = ark_std::test_rng();
    /// // Randomly sample a generator
    /// let g = G::rand(&mut rng);
    /// // Constructing the two-variate multilinear polynomial x_0 + 2 * x_1 + 3 * x_0 * x_1
    /// // by specifying its evaluations at [00, 10, 01, 11]
    /// let mle = DenseGroupMultilinearExtension::from_evaluations_vec(
    ///     2, vec![0, 1, 2, 6].iter().map(|x| g.mul(Fr::from(*x as u64))).collect()
    /// );
    ///
    /// // Bind the first variable of the MLE to the value 5, resulting in
    /// // the new polynomial 5 + 17 * x_1
    /// let bound = mle.fix_variables(&[Fr::from(5)]);
    /// ```
    /// }
    fn fix_variables(&self, partial_point: &[G::ScalarField]) -> Self {
        assert!(
            partial_point.len() <= self.num_vars,
            "invalid size of partial point"
        );
        let mut poly = self.evaluations.to_vec();
        let nv = self.num_vars;
        let dim = partial_point.len();
        // evaluate single variable of partial point from left to right
        for i in 1..dim + 1 {
            let r = partial_point[i - 1];
            for b in 0..(1 << (nv - i)) {
                let left = poly[b << 1];
                let right = poly[(b << 1) + 1];
                poly[b] = left + (right - left).mul(r);
            }
        }
        Self::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
    }

    fn to_evaluations(&self) -> Vec<G> {
        self.evaluations.to_vec()
    }
}

impl<G: CurveGroup> Index<usize> for DenseGroupMultilinearExtension<G> {
    type Output = G;

    /// Returns the evaluation of the polynomial at a point represented by index.
    ///
    /// Index represents a vector in {0,1}^`num_vars` in little endian form. For
    /// example, `0b1011` represents `P(1,1,0,1)`
    ///
    /// For dense multilinear polynomial, `index` takes constant time.
    fn index(&self, index: usize) -> &Self::Output {
        &self.evaluations[index]
    }
}

impl<G: CurveGroup> Add for DenseGroupMultilinearExtension<G> {
    type Output = DenseGroupMultilinearExtension<G>;

    fn add(self, other: DenseGroupMultilinearExtension<G>) -> Self {
        &self + &other
    }
}

impl<'a, 'b, G: CurveGroup> Add<&'a DenseGroupMultilinearExtension<G>> for &'b DenseGroupMultilinearExtension<G> {
    type Output = DenseGroupMultilinearExtension<G>;

    fn add(self, rhs: &'a DenseGroupMultilinearExtension<G>) -> Self::Output {
        // handle constant zero case
        if rhs.is_zero() {
            return self.clone();
        }
        if self.is_zero() {
            return rhs.clone();
        }
        assert_eq!(self.num_vars, rhs.num_vars);
        let result: Vec<G> = cfg_iter!(self.evaluations)
            .zip(cfg_iter!(rhs.evaluations))
            .map(|(a, b)| *a + *b)
            .collect();

        Self::Output::from_evaluations_vec(self.num_vars, result)
    }
}

impl<G: CurveGroup> AddAssign for DenseGroupMultilinearExtension<G> {
    fn add_assign(&mut self, other: Self) {
        *self = &*self + &other;
    }
}

impl<'a, G: CurveGroup> AddAssign<&'a DenseGroupMultilinearExtension<G>> for DenseGroupMultilinearExtension<G> {
    fn add_assign(&mut self, other: &'a DenseGroupMultilinearExtension<G>) {
        *self = &*self + other;
    }
}

impl<'a, G: CurveGroup> AddAssign<(G::ScalarField, &'a DenseGroupMultilinearExtension<G>)>
    for DenseGroupMultilinearExtension<G>
{
    fn add_assign(&mut self, (f, other): (G::ScalarField, &'a DenseGroupMultilinearExtension<G>)) {
        let other = Self {
            num_vars: other.num_vars,
            evaluations: cfg_iter!(other.evaluations).map(|x| x.mul(f)).collect(),
        };
        *self = &*self + &other;
    }
}

impl<G: CurveGroup> Neg for DenseGroupMultilinearExtension<G> {
    type Output = DenseGroupMultilinearExtension<G>;

    fn neg(self) -> Self::Output {
        Self::Output {
            num_vars: self.num_vars,
            evaluations: cfg_iter!(self.evaluations).map(|x| -*x).collect(),
        }
    }
}

impl<G: CurveGroup> Sub for DenseGroupMultilinearExtension<G> {
    type Output = DenseGroupMultilinearExtension<G>;

    fn sub(self, other: DenseGroupMultilinearExtension<G>) -> Self {
        &self - &other
    }
}

impl<'a, 'b, G: CurveGroup> Sub<&'a DenseGroupMultilinearExtension<G>> for &'b DenseGroupMultilinearExtension<G> {
    type Output = DenseGroupMultilinearExtension<G>;

    fn sub(self, rhs: &'a DenseGroupMultilinearExtension<G>) -> Self::Output {
        self + &rhs.clone().neg()
    }
}

impl<G: CurveGroup> SubAssign for DenseGroupMultilinearExtension<G> {
    fn sub_assign(&mut self, other: Self) {
        *self = &*self - &other;
    }
}

impl<'a, G: CurveGroup> SubAssign<&'a DenseGroupMultilinearExtension<G>> for DenseGroupMultilinearExtension<G> {
    fn sub_assign(&mut self, other: &'a DenseGroupMultilinearExtension<G>) {
        *self = &*self - other;
    }
}

impl<G: CurveGroup> fmt::Debug for DenseGroupMultilinearExtension<G> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "DenseML(nv = {}, evaluations = [", self.num_vars)?;
        for i in 0..ark_std::cmp::min(4, self.evaluations.len()) {
            write!(f, "{:?} ", self.evaluations[i])?;
        }
        if self.evaluations.len() < 4 {
            write!(f, "])")?;
        } else {
            write!(f, "...])")?;
        }
        Ok(())
    }
}

impl<G: CurveGroup> Zero for DenseGroupMultilinearExtension<G> {
    fn zero() -> Self {
        Self {
            num_vars: 0,
            evaluations: vec![G::zero()],
        }
    }

    fn is_zero(&self) -> bool {
        self.num_vars == 0 && self.evaluations[0].is_zero()
    }
}

impl<G: CurveGroup> GroupPolynomial<G> for DenseGroupMultilinearExtension<G> {
    type Point = Vec<G::ScalarField>;

    fn degree(&self) -> usize {
        self.num_vars
    }

    /// Evaluate the dense MLE at the given point
    /// # Example
    /// ```
    /// use ark_test_curves::bls12_381::{Fr, G1Projective};
    /// # use ark_poly::{GroupMultilinearExtension, DenseGroupMultilinearExtension, GroupPolynomial};
    /// # use ark_ff::One;
    ///
    /// let mut rng = ark_std::test_rng();
    /// // Randomly sample a generator
    /// let g = G::rand(&mut rng);
    /// // The two-variate polynomial x_0 + 3 * x_0 * x_1 + 2 evaluates to [2, 3, 2, 6]
    /// // in the two-dimensional hypercube with points [00, 10, 01, 11]
    /// let mle = DenseGroupMultilinearExtension::from_evaluations_vec(
    ///     2, vec![2, 3, 2, 6].iter().map(|x| g.mul(Fr::from(*x as u64))).collect()
    /// );
    ///
    /// // By the uniqueness of MLEs, `mle` is precisely the above polynomial, which
    /// // takes the value 54 at the point (1, 17)
    /// let eval = mle.evaluate(&[Fr::one(), Fr::from(17)].into());
    /// assert_eq!(eval, g.mul(Fr::from(54)));
    /// ```
    fn evaluate(&self, point: &Self::Point) -> G {
        assert!(point.len() == self.num_vars);
        self.fix_variables(&point)[0]
    }
}

#[cfg(test)]
mod tests {
    use crate::evaluations::multivariate::multilinear::{DenseGroupMultilinearExtension, GroupMultilinearExtension, GroupPolynomial};
    use ark_ec::CurveGroup;
    use ark_ff::{Zero, One};
    use ark_std::{ops::Neg, ops::Mul, test_rng, vec::*, UniformRand};
    use ark_test_curves::bls12_381::{Fr, G1Projective};

    /// utility: evaluate multilinear extension (in form of data array) at a random point
    fn evaluate_data_array<G: CurveGroup>(data: &[G1Projective], point: &[Fr]) -> G1Projective {
        if data.len() != (1 << point.len()) {
            panic!("Data size mismatch with number of variables. ")
        }

        let nv = point.len();
        let mut a = data.to_vec();

        for i in 1..nv + 1 {
            let r = point[i - 1];
            for b in 0..(1 << (nv - i)) {
                a[b] = a[b << 1].mul(Fr::one() - r) + a[(b << 1) + 1].mul(r);
            }
        }
        a[0]
    }

    #[test]
    fn group_evaluate_at_a_point() {
        let mut rng = test_rng();
        let poly = DenseGroupMultilinearExtension::<G1Projective>::rand(4, & mut rng);
        let point: Vec<_> = (0..4).map(|_| Fr::rand(&mut rng)).collect();
        assert_eq!(
            evaluate_data_array::<G1Projective>(&poly.evaluations, &point),
            poly.evaluate(&point)
        )
    }

    #[test]
    fn relabel_group_polynomial() {
        let mut rng = test_rng();
        let mut poly = DenseGroupMultilinearExtension::<G1Projective>::rand(10, &mut rng);
        let mut point: Vec<_> = (0..10).map(|_| Fr::rand(&mut rng)).collect();

        let expected = poly.evaluate(&point);

        poly.relabel_in_place(2, 2, 1); // should have no effect
        assert_eq!(expected, poly.evaluate(&point));

        poly.relabel_in_place(3, 4, 1); // should switch 3 and 4
        point.swap(3, 4);
        assert_eq!(expected, poly.evaluate(&point));

        poly.relabel_in_place(7, 5, 1);
        point.swap(7, 5);
        assert_eq!(expected, poly.evaluate(&point));

        poly.relabel_in_place(2, 5, 3);
        point.swap(2, 5);
        point.swap(3, 6);
        point.swap(4, 7);
        assert_eq!(expected, poly.evaluate(&point));

        poly.relabel_in_place(7, 0, 2);
        point.swap(0, 7);
        point.swap(1, 8);
        assert_eq!(expected, poly.evaluate(&point));

        poly.relabel_in_place(0, 9, 1);
        point.swap(0, 9);
        assert_eq!(expected, poly.evaluate(&point));
    }

    #[test]
    fn group_arithmetic() {
        const NV: usize = 4;
        let mut rng = test_rng();
        let point: Vec<_> = (0..NV).map(|_| Fr::rand(&mut rng)).collect();
        let poly1 = DenseGroupMultilinearExtension::<G1Projective>::rand(NV, &mut rng);
        let poly2 = DenseGroupMultilinearExtension::<G1Projective>::rand(NV, &mut rng);
        let v1 = poly1.evaluate(&point);
        let v2 = poly2.evaluate(&point);
        // test add
        assert_eq!((&poly1 + &poly2).evaluate(&point), v1 + v2);
        // test sub
        assert_eq!((&poly1 - &poly2).evaluate(&point), v1 - v2);
        // test negate
        assert_eq!(poly1.clone().neg().evaluate(&point), -v1);
        // test add assign
        {
            let mut poly1 = poly1.clone();
            poly1 += &poly2;
            assert_eq!(poly1.evaluate(&point), v1 + v2)
        }
        // test sub assign
        {
            let mut poly1 = poly1.clone();
            poly1 -= &poly2;
            assert_eq!(poly1.evaluate(&point), v1 - v2)
        }
        // test add assign with scalar
        {
            let mut poly1 = poly1.clone();
            let scalar = Fr::rand(&mut rng);
            poly1 += (scalar, &poly2);
            assert_eq!(poly1.evaluate(&point), v1 + v2.mul(scalar))
        }
        // test additive identity
        {
            assert_eq!(&poly1 + &DenseGroupMultilinearExtension::<G1Projective>::zero(), poly1);
            assert_eq!(&DenseGroupMultilinearExtension::<G1Projective>::zero() + &poly1, poly1);
            {
                let mut poly1_cloned = poly1.clone();
                poly1_cloned += &DenseGroupMultilinearExtension::<G1Projective>::zero();
                assert_eq!(&poly1_cloned, &poly1);
                let mut zero = DenseGroupMultilinearExtension::<G1Projective>::zero();
                let scalar = Fr::rand(&mut rng);
                zero += (scalar, &poly1);
                assert_eq!(zero.evaluate(&point), v1.mul(scalar));
            }
        }
    }
}
