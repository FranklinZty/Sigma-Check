pub mod errors;
pub mod multilinear_polynomial;
pub mod multilinear_group_polynomial;
pub mod utils;
pub mod virtual_polynomial;
pub mod virtual_group_polynomial;
pub mod sumcheck;
pub mod sumcheckg;

use subroutines::PolyIOP;
use crate::{
    virtual_group_polynomial::{VirtualGroupPolynomial, VGPAuxInfo},
    virtual_polynomial::{VirtualPolynomial, VPAuxInfo},
    sumcheck::SumCheck,
    sumcheckg::GroupSumCheck,
    multilinear_polynomial::{fix_variables, scalar_mul},
    utils::mle::{matrix_to_mle, vec_to_mle},
    utils::vec::{to_F_matrix, to_F_vec},
    utils::hypercube::BooleanHypercube,
};
use std::sync::Arc;
use ark_poly::DenseMultilinearExtension;
use ark_test_curves::secp256k1::{Fr, G1Projective};
// use ark_bls12_381::{Fr, Fq, G1Projective};
use ark_std::{One, Zero, test_rng, UniformRand, time::Instant};
use std::ops::Add;
use std::marker::PhantomData;
use rand::Rng;

// x, y dimensions M(x,y) - k times m matrix
const num_x:usize = 8;
const num_y:usize = 4;
// degrees for f(x) and g(y)
const deg_x:usize = 2;
const deg_y:usize = deg_x+1;
fn main() {
    let base: usize = 2;
    let row_num = base.pow(u32::try_from(num_x).unwrap());
    let col_num = base.pow(u32::try_from(num_y).unwrap());
    let mut rng = rand::thread_rng();
    let G_raw: Vec<usize> = (0..col_num).map(|_| rng.gen_range(0..99)).collect();
    let M_raw = vec![G_raw.clone(); row_num];
    println!("M_raw: {:?}, G_raw: {:?}", M_raw, G_raw);

    let G = to_F_vec::<Fr>(G_raw);
    let M = to_F_matrix::<Fr>(M_raw);

    sumcheck_on_F(M.clone(), G.clone()); // g_2(x,y)
    sumcheck_on_G(M.clone(), G.clone()); // g_1(x,y)
}

fn sumcheck_on_F(
    M : Vec<Vec<Fr>>,
    G : Vec<Fr>,
) {
    // transform M and G into MLEs
    let M_xy_mle: DenseMultilinearExtension<Fr> = matrix_to_mle(M.clone());
    let G_y_mle: DenseMultilinearExtension<Fr> = vec_to_mle(num_y, &G.clone());
    // further transform G_y_mle into a virtual polynomial
    let mut G_y_virtual =
    VirtualPolynomial::new_from_mle(&Arc::new(G_y_mle.clone()), Fr::one());
    
    let mut M_x_mle: DenseMultilinearExtension<Fr> = vec_to_mle(num_x, &vec![Fr::zero();  M.len()]);
    let bhc = BooleanHypercube::new(num_y);
    for y in bhc.into_iter() {
        M_x_mle += fix_variables(&M_xy_mle, &y);
    }

    let now = Instant::now();
    // ---------------- first round sum-check prover --------------------
    // compute GM(x) = sum_y M(x,y) G(y) on the hypercube
    let mut sum_GM = DenseMultilinearExtension::<Fr> {
        evaluations: vec![Fr::zero(); M_xy_mle.evaluations.len()],
        num_vars: num_x,
    };
    let bhc = BooleanHypercube::new(num_y);
    for y in bhc.into_iter() {
        // In a slightly counter-intuitive fashion fix_variables() fixes the right-most variables of the polynomial. So
        // for a polynomial M(x,y) and a random field element r, if we do fix_variables(M,r) we will get M(x,r).
        let M_j_y = fix_variables(&M_xy_mle, &y);
        let G_y = G_y_virtual.evaluate(&y).unwrap();
        let M_j_z = scalar_mul(&M_j_y, &G_y);
        sum_GM = sum_GM.add(M_j_z);
    }

    // transform GM(x) into a virtual polynomial on x
    let mut GM_x_virtual =
    VirtualPolynomial::new_from_mle(&Arc::new(sum_GM.clone()), Fr::one());
    for _ in 0..deg_x-1 {
        GM_x_virtual.mul_by_mle(Arc::new(M_x_mle.clone()), Fr::one()).unwrap();
    }

    // initialize the transcript
    let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();

    // run the sum-check protocol on x
    let sumcheck_proof_x =
            <PolyIOP<Fr> as SumCheck<Fr>>::prove(&GM_x_virtual, & mut transcript).unwrap();
    let r_x = sumcheck_proof_x.point.clone();
    
    // ---------------- second round sum-check prover--------------------
    // compute GM(y) = M(rx,y) G(y)
    let M_y_mle = fix_variables(&M_xy_mle, &r_x);
    let M_y_virtual =
    VirtualPolynomial::new_from_mle(&Arc::new(M_y_mle.clone()), Fr::one());

    let mut GM_y_virtual= M_y_virtual.clone();
    GM_y_virtual.mul_by_mle(Arc::new(G_y_mle.clone()), Fr::one()).unwrap();

    for _ in 0..deg_x-1 {
        GM_y_virtual.mul_by_mle(Arc::new(M_y_mle.clone()), Fr::one()).unwrap();
    }

    let sumcheck_proof_y =
            <PolyIOP<Fr> as SumCheck<Fr>>::prove(&GM_y_virtual, & mut transcript).unwrap();
    let r_y = sumcheck_proof_y.point.clone();

    // ---------------- sum-check proving ends--------------------
    let elapsed_time = now.elapsed();
        println!("Sumcheck on F Prover time: {:?}", elapsed_time);

    // compute sum_x
    let mut sum_x = Fr::zero();
    let bhc = BooleanHypercube::new(num_x);
    for x in bhc.into_iter() {
        // In a slightly counter-intuitive fashion fix_variables() fixes the right-most variables of the polynomial. So
        // for a polynomial M(x,y) and a random field element r, if we do fix_variables(M,r) we will get M(x,r).
        let GM_j_x = GM_x_virtual.evaluate(&x).unwrap();
        sum_x += GM_j_x;
    }

    // compute sum_y
    let mut sum_y = Fr::zero();
    let bhc = BooleanHypercube::new(num_y);
    for y in bhc.into_iter() {
        // In a slightly counter-intuitive fashion fix_variables() fixes the right-most variables of the polynomial. So
        // for a polynomial M(x,y) and a random field element r, if we do fix_variables(M,r) we will get M(x,r).
        let GM_j_y = GM_y_virtual.evaluate(&y).unwrap();
        sum_y += GM_j_y;
    }

    let now = Instant::now();
    // ---------------- first round sum-check verifier ----------

    let vp_aux_info_x = VPAuxInfo::<Fr> {
        max_degree: deg_x,
        num_variables: num_x,
        phantom: PhantomData::<Fr>,
    };
    
    let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();

    // run the verification
    let sumcheck_subclaim = <PolyIOP<Fr> as SumCheck<Fr>>::verify(
        sum_x,
        &sumcheck_proof_x,
        &vp_aux_info_x,
        & mut transcript,
    )
    .unwrap();

    // ---------------- second round sum-check verifier --------------------
    let vp_aux_info_y = VPAuxInfo::<Fr> {
        max_degree: deg_y,
        num_variables: num_y,
        phantom: PhantomData::<Fr>,
    };

    // run the verification
    let sumcheck_subclaim = <PolyIOP<Fr> as SumCheck<Fr>>::verify(
        sum_y,
        &sumcheck_proof_y,
        &vp_aux_info_y,
        & mut transcript,
    )
    .unwrap();

    // ---------------- sum-check verificaiton ends--------------------
    let elapsed_time = now.elapsed();
        println!("Sumcheck on F Verifier time: {:?}", elapsed_time);
}

fn sumcheck_on_G(
    M : Vec<Vec<Fr>>,
    G : Vec<Fr>,
) {
    let mut rng = test_rng();
    let g = G1Projective::rand(&mut rng);

    let M_xy_mle: DenseMultilinearExtension<Fr> = matrix_to_mle(M.clone());
    let G_y_mle: DenseMultilinearExtension<Fr> = vec_to_mle(num_y, &G);
    let mut G_y_virtual =
    VirtualPolynomial::new_from_mle(&Arc::new(G_y_mle.clone()), Fr::one());

    let mut M_x_mle: DenseMultilinearExtension<Fr> = vec_to_mle(num_x, &vec![Fr::zero();  M.len()]);
    let bhc = BooleanHypercube::new(num_y);
    for y in bhc.into_iter() {
        M_x_mle += fix_variables(&M_xy_mle, &y);
    }

    let now = Instant::now();
    // ---------------- first round sum-check prover --------------------
    let mut sum_Mz = DenseMultilinearExtension::<Fr> {
        evaluations: vec![Fr::zero(); M_xy_mle.evaluations.len()],
        num_vars: num_x,
    };
    let bhc = BooleanHypercube::new(num_y);
    for y in bhc.into_iter() {
        // In a slightly counter-intuitive fashion fix_variables() fixes the right-most variables of the polynomial. So
        // for a polynomial M(x,y) and a random field element r, if we do fix_variables(M,r) we will get M(x,r).
        let M_j_y = fix_variables(&M_xy_mle, &y);
        let G_y = G_y_virtual.evaluate(&y).unwrap();
        let M_j_z = scalar_mul(&M_j_y, &G_y);
        sum_Mz = sum_Mz.add(M_j_z);
    }

    let mut GM_x_virtual =
    VirtualGroupPolynomial::new_from_mle(&Arc::new(sum_Mz.clone()), g);
    for _ in 0..deg_x-1 {
        GM_x_virtual.mul_by_mle(Arc::new(M_x_mle.clone()), Fr::one()).unwrap();
    }

    let mut transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();

    let sumcheck_proof_x =
            <PolyIOP<Fr> as GroupSumCheck<G1Projective>>::prove(&GM_x_virtual, & mut transcript).unwrap();
    let r_x = sumcheck_proof_x.point.clone();
        
    // ---------------- second round sum-check prover--------------------
    // compute GM(y) = M(rx,y) G(y)
    let M_y_mle = fix_variables(&M_xy_mle, &r_x);
    let M_y_virtual =
    VirtualGroupPolynomial::new_from_mle(&Arc::new(M_y_mle.clone()), g);

    let mut GM_y_virtual= M_y_virtual.clone();
    GM_y_virtual.mul_by_mle(Arc::new(G_y_mle.clone()), Fr::one()).unwrap();
    for _ in 0..deg_x-1 {
        GM_y_virtual.mul_by_mle(Arc::new(M_y_mle.clone()), Fr::one()).unwrap();
    }
    let eval = GM_y_virtual.evaluate(&r_x);

    let sumcheck_proof_y =
            <PolyIOP<Fr> as GroupSumCheck<G1Projective>>::prove(&GM_y_virtual, & mut transcript).unwrap();
    let r_y = sumcheck_proof_y.point.clone();

    // ---------------- sum-check proving ends--------------------
    let elapsed_time = now.elapsed();
    println!("Sumcheck on G Prover time: {:?}", elapsed_time);
    
    // compute sum_x
    let mut sum_x = G1Projective::zero();
    let bhc = BooleanHypercube::new(num_x);
    for x in bhc.into_iter() {
        // In a slightly counter-intuitive fashion fix_variables() fixes the right-most variables of the polynomial. So
        // for a polynomial M(x,y) and a random field element r, if we do fix_variables(M,r) we will get M(x,r).
        let GM_j_x = GM_x_virtual.evaluate(&x).unwrap();
        sum_x += GM_j_x;
    }

    // compute sum_y
    let mut sum_y = G1Projective::zero();
    let bhc = BooleanHypercube::new(num_y);
    for y in bhc.into_iter() {
        // In a slightly counter-intuitive fashion fix_variables() fixes the right-most variables of the polynomial. So
        // for a polynomial M(x,y) and a random field element r, if we do fix_variables(M,r) we will get M(x,r).
        let GM_j_y = GM_y_virtual.evaluate(&y).unwrap();
        sum_y += GM_j_y;
    }

    let now = Instant::now();
    // ---------------- first round sum-check verifier --------------------
    let vp_aux_info_x = VGPAuxInfo::<G1Projective> {
        max_degree: deg_x,
        num_variables: num_x,
        phantom: PhantomData::<G1Projective>,
    };
    
    let mut transcript = <PolyIOP<Fr> as GroupSumCheck<G1Projective>>::init_transcript();

    // ---------------- first round sum-check verifier--------------------
    let sumcheck_subclaim = <PolyIOP<Fr> as GroupSumCheck<G1Projective>>::verify(
        sum_x,
        &sumcheck_proof_x,
        &vp_aux_info_x,
        & mut transcript,
    )
    .unwrap();

    // ---------------- second round sum-check verifier --------------------
    let vp_aux_info_y = VGPAuxInfo::<G1Projective> {
        max_degree: deg_y,
        num_variables: num_y,
        phantom: PhantomData::<G1Projective>,
    };

    // run the verification
    let sumcheck_subclaim = <PolyIOP<Fr> as GroupSumCheck<G1Projective>>::verify(
        sum_y,
        &sumcheck_proof_y,
        &vp_aux_info_y,
        & mut transcript,
    )
    .unwrap();

    let eval = GM_y_virtual.evaluate(&r_y);

    // ---------------- sum-check verificaiton ends----------
    let elapsed_time = now.elapsed();
    println!("Sumcheck on G Verifier time: {:?}", elapsed_time);
}
