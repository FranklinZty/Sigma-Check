use crate::errors::ArithErrors;
use crate::multilinear_polynomial::{fix_last_variables, fix_variables};
use crate::utils::hypercube::BooleanHypercube;
use crate::utils::mle::vec_to_mle;
use crate::utils::mleg::group_vec_to_mle;
use crate::utils::vec::Matrix;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_poly::DenseMultilinearExtension;
use ark_poly::MultilinearExtension;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct XYMLE<F: PrimeField> {
    pub mle: DenseMultilinearExtension<F>,
    pub logk: usize,
    pub logm: usize,
}

pub fn pow2_dims(k: usize, m: usize) -> Result<(usize, usize, usize, usize), ArithErrors> {
    if k == 0 || m == 0 {
        return Err(ArithErrors::InvalidParameters(
            "k and m must be non-zero".to_string(),
        ));
    }
    let k2 = k.next_power_of_two();
    let m2 = m.next_power_of_two();
    let logk = k2.trailing_zeros() as usize;
    let logm = m2.trailing_zeros() as usize;
    Ok((k2, m2, logk, logm))
}

pub fn pad_matrix_pow2<F: PrimeField>(matrix: &Matrix<F>) -> Result<(Matrix<F>, usize, usize), ArithErrors> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return Err(ArithErrors::InvalidParameters(
            "matrix must be non-empty".to_string(),
        ));
    }
    let rows = matrix.len();
    let cols = matrix[0].len();
    for row in matrix.iter() {
        if row.len() != cols {
            return Err(ArithErrors::InvalidParameters(
                "matrix rows must have equal length".to_string(),
            ));
        }
    }

    let (k2, m2, logk, logm) = pow2_dims(rows, cols)?;
    let mut padded = vec![vec![F::zero(); m2]; k2];
    for (i, row) in matrix.iter().enumerate() {
        for (j, val) in row.iter().enumerate() {
            padded[i][j] = *val;
        }
    }
    Ok((padded, logk, logm))
}

/// Build an MLE for a k x m table using variable order [y..., x...]
pub fn table_to_mle_yx<F: PrimeField>(matrix: &Matrix<F>) -> Result<XYMLE<F>, ArithErrors> {
    let (padded, logk, logm) = pad_matrix_pow2(matrix)?;
    let k2 = padded.len();
    let m2 = padded[0].len();
    let n_vars = logk + logm;

    let mut evals = Vec::with_capacity(k2 * m2);
    for row in padded.iter() {
        evals.extend_from_slice(row);
    }

    let mle = DenseMultilinearExtension::from_evaluations_vec(n_vars, evals);
    Ok(XYMLE { mle, logk, logm })
}

/// Evaluate f~(x,y) with variable order [y..., x...]
pub fn eval_xy<F: PrimeField>(mle: &DenseMultilinearExtension<F>, x_bits: &[F], y_bits: &[F]) -> Result<F, ArithErrors> {
    if mle.num_vars != x_bits.len() + y_bits.len() {
        return Err(ArithErrors::InvalidParameters(
            "point length mismatch".to_string(),
        ));
    }
    let mut point = Vec::with_capacity(y_bits.len() + x_bits.len());
    point.extend_from_slice(y_bits);
    point.extend_from_slice(x_bits);
    mle.evaluate(&point)
        .ok_or_else(|| ArithErrors::InvalidParameters("evaluation failed".to_string()))
}

/// Fix x (last variables) and return a y-dimensional MLE
pub fn fix_x<F: PrimeField>(
    mle: &DenseMultilinearExtension<F>,
    logk: usize,
    x_bits: &[F],
) -> Result<DenseMultilinearExtension<F>, ArithErrors> {
    if x_bits.len() != logk {
        return Err(ArithErrors::InvalidParameters(
            "x_bits length mismatch".to_string(),
        ));
    }
    Ok(fix_last_variables(mle, x_bits))
}

/// Fix y (first variables) and return an x-dimensional MLE
pub fn fix_y<F: PrimeField>(
    mle: &DenseMultilinearExtension<F>,
    logm: usize,
    y_bits: &[F],
) -> Result<DenseMultilinearExtension<F>, ArithErrors> {
    if y_bits.len() != logm {
        return Err(ArithErrors::InvalidParameters(
            "y_bits length mismatch".to_string(),
        ));
    }
    Ok(fix_variables(mle, y_bits))
}

/// Evaluate f~(r_x, y) for all y in {0,1}^logm
pub fn eval_all_y<F: PrimeField>(
    mle: &DenseMultilinearExtension<F>,
    logk: usize,
    logm: usize,
    x_bits: &[F],
) -> Result<Vec<F>, ArithErrors> {
    let mle_y = fix_x(mle, logk, x_bits)?;
    let mut out = Vec::with_capacity(1usize << logm);
    for y in BooleanHypercube::<F>::new(logm) {
        let val = mle_y
            .evaluate(&y)
            .ok_or_else(|| ArithErrors::InvalidParameters("evaluation failed".to_string()))?;
        out.push(val);
    }
    Ok(out)
}

pub fn vec_to_mle_field<F: PrimeField>(logn: usize, v: &[F]) -> DenseMultilinearExtension<F> {
    vec_to_mle(logn, &v.to_vec())
}

pub fn vec_to_mle_group<G: CurveGroup>(logn: usize, v: &[G]) -> crate::group_multilinear_extension::DenseGroupMultilinearExtension<G> {
    group_vec_to_mle(logn, &v.to_vec())
}

pub fn build_eq_mle<F: PrimeField>(r: &[F]) -> Result<Arc<DenseMultilinearExtension<F>>, ArithErrors> {
    if r.is_empty() {
        return Err(ArithErrors::InvalidParameters(
            "r must be non-empty".to_string(),
        ));
    }
    let mut evals = Vec::with_capacity(1usize << r.len());
    for x in BooleanHypercube::<F>::new(r.len()) {
        let w = crate::virtual_polynomial::eq_eval(&x, r)?;
        evals.push(w);
    }
    Ok(Arc::new(DenseMultilinearExtension::from_evaluations_vec(
        r.len(),
        evals,
    )))
}

#[cfg(test)]
fn bits_to_field<F: PrimeField>(index: usize, num_vars: usize) -> Vec<F> {
    let bits = crate::virtual_polynomial::bit_decompose(index as u64, num_vars);
    bits.iter().map(|&b| F::from(b as u64)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{One, Zero};
    use ark_test_curves::secp256k1::Fr;

    #[test]
    fn table_to_mle_yx_eval_matches_entries() {
        let table: Matrix<Fr> = vec![
            vec![Fr::from(1u64), Fr::from(2u64)],
            vec![Fr::from(3u64), Fr::from(4u64)],
        ];
        let xy = table_to_mle_yx(&table).unwrap();

        // x=0,y=0 -> 1
        let x0 = vec![Fr::zero()];
        let y0 = vec![Fr::zero()];
        assert_eq!(eval_xy(&xy.mle, &x0, &y0).unwrap(), Fr::from(1u64));

        // x=0,y=1 -> 2
        let y1 = vec![Fr::one()];
        assert_eq!(eval_xy(&xy.mle, &x0, &y1).unwrap(), Fr::from(2u64));

        // x=1,y=0 -> 3
        let x1 = vec![Fr::one()];
        assert_eq!(eval_xy(&xy.mle, &x1, &y0).unwrap(), Fr::from(3u64));

        // x=1,y=1 -> 4
        assert_eq!(eval_xy(&xy.mle, &x1, &y1).unwrap(), Fr::from(4u64));
    }

    #[test]
    fn fix_x_matches_row() {
        let table: Matrix<Fr> = vec![
            vec![Fr::from(10u64), Fr::from(11u64), Fr::from(12u64), Fr::from(13u64)],
            vec![Fr::from(20u64), Fr::from(21u64), Fr::from(22u64), Fr::from(23u64)],
            vec![Fr::from(30u64), Fr::from(31u64), Fr::from(32u64), Fr::from(33u64)],
            vec![Fr::from(40u64), Fr::from(41u64), Fr::from(42u64), Fr::from(43u64)],
        ];
        let xy = table_to_mle_yx(&table).unwrap();

        for x_idx in 0..4 {
            let x_bits = bits_to_field::<Fr>(x_idx, xy.logk);
            let row_vals = eval_all_y(&xy.mle, xy.logk, xy.logm, &x_bits).unwrap();
            assert_eq!(row_vals, table[x_idx]);
        }
    }

    #[test]
    fn fix_y_matches_column() {
        let table: Matrix<Fr> = vec![
            vec![Fr::from(1u64), Fr::from(2u64), Fr::from(3u64), Fr::from(4u64)],
            vec![Fr::from(5u64), Fr::from(6u64), Fr::from(7u64), Fr::from(8u64)],
            vec![Fr::from(9u64), Fr::from(10u64), Fr::from(11u64), Fr::from(12u64)],
            vec![Fr::from(13u64), Fr::from(14u64), Fr::from(15u64), Fr::from(16u64)],
        ];
        let xy = table_to_mle_yx(&table).unwrap();

        for y_idx in 0..4 {
            let y_bits = bits_to_field::<Fr>(y_idx, xy.logm);
            let mle_x = fix_y(&xy.mle, xy.logm, &y_bits).unwrap();
            let mut col = Vec::with_capacity(4);
            for x_idx in 0..4 {
                let x_bits = bits_to_field::<Fr>(x_idx, xy.logk);
                col.push(mle_x.evaluate(&x_bits).unwrap());
            }
            let expected: Vec<Fr> = table.iter().map(|row| row[y_idx]).collect();
            assert_eq!(col, expected);
        }
    }
}
