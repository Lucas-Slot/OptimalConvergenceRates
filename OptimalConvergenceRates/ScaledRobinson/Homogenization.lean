/-
  OptimalConvergenceRates/ScaledRobinson/Homogenization.lean

  Final theorem layer connecting the dehomogenized Robinson polynomial, the homogeneous
  threshold forms `P_{m,lambda}`, and the scaled-ball quadratic module.
-/
import OptimalConvergenceRates.ScaledRobinson.HomogenizationCriticalBinary
import OptimalConvergenceRates.ScaledRobinson.HomogenizationSpectralIteration
import OptimalConvergenceRates.ScaledRobinson.HomogenizationSymmetry

open MvPolynomial Finset


noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- Scaling equivalence between the unit-ball module for `R_eps` and the scaled-ball
module for `R`, with `lambda = eps⁻¹ ^ 2`. -/
theorem scaledRobinson_mem_unitBallQuadraticModule_iff_robinson_mem_ball
    {eps : ℝ} (hEps : 0 < eps) (r : ℕ) :
    scaledRobinson eps ∈ UnitBallQuadraticModule r ↔
      robinson ∈ BallQuadraticModule (eps⁻¹ ^ 2) r := by
  constructor
  · intro hmem
    obtain ⟨σ0, σ1, hσ0, hσ1, hcert⟩ := hmem
    refine ⟨scale2 eps σ0, MvPolynomial.C (eps ^ 2) * scale2 eps σ1,
      hσ0.scale eps, (hσ1.scale eps).const_mul (sq_nonneg eps), ?_⟩
    have hEps_ne : eps ≠ 0 := ne_of_gt hEps
    calc robinson
        = scale2 eps (scaledRobinson eps) := by
            unfold scaledRobinson
            rw [scale2_comp, inv_mul_cancel₀ hEps_ne, scale2_one]
      _ = scale2 eps (σ0 + UnitBallGenerator * σ1) := by rw [hcert]
      _ = scale2 eps σ0 + scale2 eps UnitBallGenerator * scale2 eps σ1 := by
            simp only [map_add, map_mul]
      _ = scale2 eps σ0 + BallGenerator (eps⁻¹ ^ 2) *
            (MvPolynomial.C (eps ^ 2) * scale2 eps σ1) := by
            rw [scale2_unitBallGenerator eps hEps_ne]
            ring
  · intro hmem
    obtain ⟨σ0, σ1, hσ0, hσ1, hcert⟩ := hmem
    refine ⟨scale2 eps⁻¹ σ0, MvPolynomial.C (eps⁻¹ ^ 2) * scale2 eps⁻¹ σ1,
      hσ0.scale eps⁻¹, (hσ1.scale eps⁻¹).const_mul (sq_nonneg eps⁻¹), ?_⟩
    calc scaledRobinson eps
        = scale2 eps⁻¹ robinson := rfl
      _ = scale2 eps⁻¹ (σ0 + BallGenerator (eps⁻¹ ^ 2) * σ1) := by rw [hcert]
      _ = scale2 eps⁻¹ σ0 + scale2 eps⁻¹ (BallGenerator (eps⁻¹ ^ 2)) *
            scale2 eps⁻¹ σ1 := by
            simp only [map_add, map_mul]
      _ = scale2 eps⁻¹ σ0 + UnitBallGenerator *
            (MvPolynomial.C (eps⁻¹ ^ 2) * scale2 eps⁻¹ σ1) := by
            rw [scale2_ballGenerator_invSq eps]
            ring

/-- Homogeneous substitution equivalence used to pass between the scaled-ball module and
SOS-ness of `P_{m,lambda}`. -/
theorem robinson_mem_ballQuadraticModule_iff_Pmlambda_sos
    {m : ℕ} (_hm : 1 ≤ m) {lambda : ℝ} (hLam : 0 < lambda) :
    robinson ∈ BallQuadraticModule lambda (m + 3) ↔ IsSOS (Pmlambda m lambda) := by
  constructor
  · intro hmem
    have hLamNonneg : 0 ≤ lambda := le_of_lt hLam
    have hhom : HomBallCertificate lambda
        (homRobinson * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m)) :=
      robinson_mem_ballQuadraticModule_to_HomBallCertificate (m := m) hmem
    obtain ⟨τ0, τ1, hτ0, hτ1, hτ0inv, hτ1inv, hcert⟩ :=
      HomBallCertificate.exists_zReflect3_invariant_witness hhom
        (zReflect3_homRobinson_mul_even_z_pow m)
    obtain ⟨σ0, hσ0sq, hσ0sos⟩ :=
      IsSOS.exists_source_of_zSquareSubst3_invariant (lambda := lambda) hτ0 hτ0inv
    obtain ⟨σ1, hσ1sq, hσ1sos⟩ :=
      IsSOS.exists_source_of_zSquareSubst3_invariant (lambda := lambda) hτ1 hτ1inv
    have hsourceSq : zSquareSubst3 (homRobinsonSource m) =
        zSquareSubst3 (σ0 + homBallGeneratorSource lambda * σ1) := by
      calc
        zSquareSubst3 (homRobinsonSource m)
            = (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson :=
              zSquareSubst3_homRobinsonSource m
        _ = homRobinson * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) := by ring
        _ = τ0 + HomBallGenerator lambda * τ1 := hcert
        _ = zSquareSubst3 σ0 + zSquareSubst3 (homBallGeneratorSource lambda) *
              zSquareSubst3 σ1 := by
              rw [hσ0sq, hσ1sq, zSquareSubst3_homBallGeneratorSource]
        _ = zSquareSubst3 (σ0 + homBallGeneratorSource lambda * σ1) := by
              simp only [map_add, map_mul]
    have hsource : homRobinsonSource m = σ0 + homBallGeneratorSource lambda * σ1 :=
      zSquareSubst3_injective hsourceSq
    rw [← pmlambdaSourceSubst_homRobinsonSource hLamNonneg m]
    rw [hsource]
    simp only [map_add, map_mul]
    rw [pmlambdaSourceSubst_homBallGeneratorSource hLamNonneg]
    exact IsSOS.add hσ0sos (IsSOS.lambda_z_sq_mul hLamNonneg hσ1sos)
  · intro hSOS
    have hsubst :
        ∃ N : ℕ, ∃ A B : Fin N → MvPolynomial (Fin 3) ℝ,
          Pmlambda m lambda =
            (∑ i : Fin N, (zSquareSubst3 (A i)) ^ 2) +
              ∑ i : Fin N,
                ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 (B i)) ^ 2 ∧
          (∀ i : Fin N, sourceWeightedDegree3 (A i) ≤ m + 3) ∧
          (∀ i : Fin N, sourceWeightedDegree3 (B i) ≤ m + 2) := by
      obtain ⟨N, A, B, hsum, hAinv, hBinv, hAdeg, hBdeg⟩ :=
        IsSOS.exists_Pmlambda_z_reflection_even_odd_witness_degree_bound hSOS
      choose A0 hA0 using fun i => exists_zSquareSubst3_of_zReflect3_eq_self (hAinv i)
      choose B0 hB0 using fun i => exists_X_two_mul_zSquareSubst3_of_zReflect3_eq_neg
        (hBinv i)
      refine ⟨N, A0, B0, ?_, ?_, ?_⟩
      · rw [hsum]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [hA0 i]
        · apply Finset.sum_congr rfl
          intro i _
          rw [hB0 i]
      · intro i
        calc sourceWeightedDegree3 (A0 i)
            ≤ (zSquareSubst3 (A0 i)).totalDegree :=
              sourceWeightedDegree3_le_zSquareSubst3_totalDegree (A0 i)
          _ ≤ m + 3 := by
              rw [← hA0 i]
              exact hAdeg i
      · intro i
        apply sourceWeightedDegree3_le_of_X_two_mul_zSquareSubst3_totalDegree_le (r := m + 2)
        simpa [← hB0 i, show (m + 2) + 1 = m + 3 by omega] using hBdeg i
    have hbounded : DegreeBoundedHomBallCertificate lambda (m + 3)
        ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) :=
      Pmlambda_isSOS_to_DegreeBoundedHomBallCertificate_of_source_weighted_bounds hLam hSOS hsubst
    exact hbounded.robinson_mem_BallQuadraticModule

/-- Explicit critical SOS certificate at `lambda = 4*m*(m+1)`. -/
theorem Pmlambda_critical_isSOS {m : ℕ} (_hm : 1 ≤ m) :
    IsSOS (Pmlambda m (criticalLambda m)) :=
  Pmlambda_critical_isSOS_binary m

/-- Monotonicity in the ball-radius parameter for the homogeneous SOS threshold forms. -/
theorem Pmlambda_isSOS_of_le_critical
    {m : ℕ} (hm : 1 ≤ m) {lambda : ℝ} (hLam : 0 < lambda)
    (hle : lambda ≤ criticalLambda m) :
    IsSOS (Pmlambda m lambda) := by
  have hCritPos : 0 < criticalLambda m := criticalLambda_pos hm
  have hmemCrit : robinson ∈ BallQuadraticModule (criticalLambda m) (m + 3) :=
    (robinson_mem_ballQuadraticModule_iff_Pmlambda_sos hm hCritPos).mpr
      (Pmlambda_critical_isSOS hm)
  have hmem : robinson ∈ BallQuadraticModule lambda (m + 3) :=
    BallQuadraticModule_of_lambda_le hle hmemCrit
  exact (robinson_mem_ballQuadraticModule_iff_Pmlambda_sos hm hLam).mp hmem

/-- Arithmetic endpoint of the spectral-factor necessity argument. -/
theorem lambda_le_critical_of_sqrt_bounds
    {m : ℕ} {lambda D : ℝ} (hm : 1 ≤ m)
    (hlow : Real.sqrt (lambda + 1) - (m : ℝ) ≤ D) (hup : D ≤ (m : ℝ) + 1) :
    lambda ≤ criticalLambda m := by
  have hsqrt_le : Real.sqrt (lambda + 1) ≤ 2 * (m : ℝ) + 1 := by linarith
  have hright_nonneg : 0 ≤ 2 * (m : ℝ) + 1 := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hsq := (Real.sqrt_le_left hright_nonneg).mp hsqrt_le
  unfold criticalLambda
  nlinarith

/-- Final arithmetic step of the necessity proof, stated directly in terms of the
axis and diagonal derivative norms. -/
theorem lambda_le_critical_of_axis_diagonal_derivative_bounds
    {m Naxis Ndiag : ℕ} {lambda : ℝ} (hm : 1 ≤ m)
    {Faxis : Fin Naxis → Polynomial ℝ} {Fdiag : Fin Ndiag → Polynomial ℝ}
    (hDerivEq :
      vecNorm (fun i : Fin Naxis => (Polynomial.derivative (Faxis i)).eval 0) =
        vecNorm (fun i : Fin Ndiag => (Polynomial.derivative (Fdiag i)).eval 0))
    (hAxisLower :
      Real.sqrt (lambda + 1) - (m : ℝ) ≤
        vecNorm (fun i : Fin Naxis => (Polynomial.derivative (Faxis i)).eval 0))
    (hDiagUpper :
      vecNorm (fun i : Fin Ndiag => (Polynomial.derivative (Fdiag i)).eval 0) ≤
        (m : ℝ) + 1) :
    lambda ≤ criticalLambda m := by
  refine lambda_le_critical_of_sqrt_bounds hm hAxisLower ?_
  rwa [hDerivEq]

/-- The threshold is automatic in the small-radius branch of the necessity proof. -/
theorem lambda_le_critical_of_le_two {m : ℕ} {lambda : ℝ}
    (hm : 1 ≤ m) (hLam : lambda ≤ 2) : lambda ≤ criticalLambda m := by
  unfold criticalLambda
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- Necessity of the sharp homogeneous SOS threshold. -/
theorem Pmlambda_lambda_le_critical_of_isSOS
    {m : ℕ} (hm : 1 ≤ m) {lambda : ℝ} (_hLam : 0 < lambda)
    (hSOS : IsSOS (Pmlambda m lambda)) :
    lambda ≤ criticalLambda m := by
  by_cases hSmall : lambda ≤ 2
  · exact lambda_le_critical_of_le_two hm hSmall
  · have hgt2 : 2 < lambda := lt_of_not_ge hSmall
    have hgt1 : 1 < lambda := by linarith
    obtain ⟨N, H, Faxis, Fdiag, _hH, hFaxis, hFdiag, hAxisPt, hDiagPt⟩ :=
      IsSOS.exists_signedSwap_axis_diagonalRestriction_normalized_factorization hgt2 hSOS
    have hAxisNorm :
        ∑ ij : Fin (N * 8),
            (Faxis ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)) ^ 2 =
          (1 + Polynomial.X ^ 2) ^ m *
            (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2) :=
      axisRestriction_stripped_norm_identity_prod hFaxis
    have hDiagNorm :
        ∑ ij : Fin (N * 8),
            (Fdiag ((finProdFinEquiv.symm ij).2) ((finProdFinEquiv.symm ij).1)) ^ 2 =
          (1 + Polynomial.X ^ 2) ^ (m + 1) :=
      diagonalRestriction_stripped_norm_identity_prod hFdiag
    have hAxisLower :
        Real.sqrt (lambda + 1) - (m : ℝ) ≤
          Real.sqrt (prodVecSqNorm (fun ij : Fin N × Fin 8 =>
            (Polynomial.derivative (Faxis ij.2 ij.1)).eval 0)) :=
      axisRestriction_stripped_derivative_norm_ge_prod (by linarith) hAxisNorm
    have hDiagUpper :
        Real.sqrt (prodVecSqNorm (fun ij : Fin N × Fin 8 =>
            (Polynomial.derivative (Fdiag ij.2 ij.1)).eval 0)) ≤
          (m : ℝ) + 1 :=
      diagonalRestriction_stripped_derivative_norm_le_prod hDiagNorm
    have hDerivEq :
        Real.sqrt (prodVecSqNorm (fun ij : Fin N × Fin 8 =>
            (Polynomial.derivative (Faxis ij.2 ij.1)).eval 0)) =
          Real.sqrt (prodVecSqNorm (fun ij : Fin N × Fin 8 =>
            (Polynomial.derivative (Fdiag ij.2 ij.1)).eval 0)) := by
      rw [signedSwapAverageWitness_axis_diagonal_stripped_derivative_prodVecSqNorm_eq
        hAxisPt hDiagPt]
    exact lambda_le_critical_of_sqrt_bounds hm hAxisLower (by rwa [hDerivEq])

/-- Sharp homogeneous SOS threshold. -/
theorem Pmlambda_isSOS_iff_le_critical
    {m : ℕ} (hm : 1 ≤ m) {lambda : ℝ} (hLam : 0 < lambda) :
    IsSOS (Pmlambda m lambda) ↔ lambda ≤ criticalLambda m := by
  constructor
  · exact Pmlambda_lambda_le_critical_of_isSOS hm hLam
  · exact Pmlambda_isSOS_of_le_critical hm hLam

/-- Exact scaled-ball module threshold for the unscaled Robinson polynomial in orders `r >= 4`. -/
theorem robinson_mem_ballQuadraticModule_iff_threshold_of_four_le
    {lambda : ℝ} (hLam : 0 < lambda) {r : ℕ} (hr : 4 ≤ r) :
    robinson ∈ BallQuadraticModule lambda r ↔
      lambda ≤ 4 * ((r : ℝ) - 3) * ((r : ℝ) - 2) := by
  let m : ℕ := r - 3
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hr_eq : m + 3 = r := by dsimp [m]; omega
  have hcrit : criticalLambda m = 4 * ((r : ℝ) - 3) * ((r : ℝ) - 2) := by
    dsimp [m, criticalLambda]
    rw [Nat.cast_sub (by omega : 3 ≤ r)]
    ring
  have hmem : robinson ∈ BallQuadraticModule lambda r ↔ IsSOS (Pmlambda m lambda) := by
    rw [← hr_eq]
    exact robinson_mem_ballQuadraticModule_iff_Pmlambda_sos hm hLam
  rw [hmem]
  rw [Pmlambda_isSOS_iff_le_critical hm hLam]
  rw [hcrit]

/-- The small-scale range in the main theorem is exactly the nontrivial `lambda > 2` range. -/
theorem two_lt_eps_inv_sq_of_lt_inv_sqrt_two
    {eps : ℝ} (hEps : 0 < eps) (hEpsSmall : eps < (Real.sqrt 2)⁻¹) :
    2 < eps⁻¹ ^ 2 := by
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : eps ^ 2 < ((Real.sqrt 2)⁻¹) ^ 2 := by
    rw [sq_lt_sq]
    rw [abs_of_pos hEps, abs_of_pos (inv_pos.mpr hsqrt2_pos)]
    exact hEpsSmall
  have hright : ((Real.sqrt 2)⁻¹) ^ 2 = (2 : ℝ)⁻¹ := by
    rw [show ((Real.sqrt 2)⁻¹) ^ 2 = ((Real.sqrt 2) ^ 2)⁻¹ by ring]
    rw [hsqrt2_sq]
  rw [hright] at hsq
  have heps_sq_pos : 0 < eps ^ 2 := sq_pos_of_ne_zero (ne_of_gt hEps)
  have hinv : 1 / ((2 : ℝ)⁻¹) < 1 / (eps ^ 2) :=
    one_div_lt_one_div_of_lt heps_sq_pos hsq
  have htwo : 1 / ((2 : ℝ)⁻¹) = (2 : ℝ) := by norm_num
  have heps : 1 / (eps ^ 2) = eps⁻¹ ^ 2 := by
    field_simp [ne_of_gt hEps]
  rwa [htwo, heps] at hinv

/-- The concrete small-scale bound used by the public main theorem. -/
theorem inv_hundred_lt_inv_sqrt_two : ((100 : ℝ)⁻¹) < (Real.sqrt 2)⁻¹ := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_lt : Real.sqrt 2 < (100 : ℝ) := by
    have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    nlinarith
  simpa [one_div] using one_div_lt_one_div_of_lt hsqrt2_pos hsqrt2_lt

/-- A convenient form of the small-scale hypothesis used to avoid the order-three branch. -/
theorem two_lt_eps_inv_sq_of_lt_inv_hundred
    {eps : ℝ} (hEps : 0 < eps) (hEpsSmall : eps < (100 : ℝ)⁻¹) :
    2 < eps⁻¹ ^ 2 :=
  two_lt_eps_inv_sq_of_lt_inv_sqrt_two hEps (hEpsSmall.trans inv_hundred_lt_inv_sqrt_two)


/-- Arithmetic form of the target-order threshold for orders `r >= 4`. -/
theorem ballTargetOrder_le_iff
    {lambda : ℝ} (_hLam : 0 < lambda) {r : ℕ} (hr : 4 ≤ r) :
    ballTargetOrder lambda ≤ r ↔
      lambda ≤ 4 * ((r : ℝ) - 3) * ((r : ℝ) - 2) := by
  unfold ballTargetOrder
  by_cases h2 : lambda ≤ 2
  · simp only [h2, ↓reduceIte]
    constructor
    · intro _h
      have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
      have hRhs : (2 : ℝ) ≤ 4 * ((r : ℝ) - 3) * ((r : ℝ) - 2) := by
        nlinarith
      exact h2.trans hRhs
    · intro _h
      omega
  · simp only [h2, ↓reduceIte]
    let A : ℝ := (Real.sqrt (1 + lambda) - 1) / 2
    have h3r : 3 ≤ r := by omega
    have hceil : (3 + Nat.ceil A ≤ r) ↔ Nat.ceil A ≤ r - 3 := by omega
    rw [hceil, Nat.ceil_le]
    have hcast : ((r - 3 : ℕ) : ℝ) = (r : ℝ) - 3 := by
      norm_num [Nat.cast_sub h3r]
    rw [hcast]
    have hRpos : 0 ≤ 2 * ((r : ℝ) - 3) + 1 := by
      have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    unfold A
    constructor
    · intro hA
      have hsqrt_le : Real.sqrt (1 + lambda) ≤ 2 * ((r : ℝ) - 3) + 1 := by
        linarith
      have hsq := (Real.sqrt_le_left hRpos).mp hsqrt_le
      nlinarith
    · intro hlam
      have hsqrt_le : Real.sqrt (1 + lambda) ≤ 2 * ((r : ℝ) - 3) + 1 := by
        rw [Real.sqrt_le_left hRpos]
        nlinarith
      linarith

/-- Ceiling arithmetic used by the dyadic order specializations. -/
theorem ceil_sqrt_one_add_two_mul_sq (n : ℕ) (hn : 1 ≤ n) :
    Nat.ceil ((Real.sqrt (1 + (2 * (n : ℝ)) ^ 2) - 1) / 2) = n := by
  apply le_antisymm
  · rw [Nat.ceil_le]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnonneg : 0 ≤ 2 * (n : ℝ) + 1 := by nlinarith
    have hsqrt : Real.sqrt (1 + (2 * (n : ℝ)) ^ 2) ≤ 2 * (n : ℝ) + 1 := by
      rw [Real.sqrt_le_left hnonneg]
      nlinarith
    linarith
  · have hpred_lt : n - 1 <
        Nat.ceil ((Real.sqrt (1 + (2 * (n : ℝ)) ^ 2) - 1) / 2) := by
      rw [Nat.lt_ceil]
      rw [Nat.cast_sub hn]
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hlt : 2 * (n : ℝ) - 1 < Real.sqrt (1 + (2 * (n : ℝ)) ^ 2) := by
        rw [Real.lt_sqrt (by nlinarith)]
        nlinarith
      linarith
    omega

/-- Dyadic arithmetic specialization of the scaled Robinson order, stated with
`eps = 1 / (2*n)`. -/
theorem scaledRobinsonOrder_inv_two_mul (n : ℕ) (hn : 1 ≤ n) :
    scaledRobinsonOrder ((2 * (n : ℝ))⁻¹) = n + 3 := by
  unfold scaledRobinsonOrder ballTargetOrder
  have hLamEq : (((2 * (n : ℝ))⁻¹)⁻¹) ^ 2 = (2 * (n : ℝ)) ^ 2 := by
    field_simp [show 2 * (n : ℝ) ≠ 0 by positivity]
  rw [hLamEq]
  have hgt2 : ¬ (2 * (n : ℝ)) ^ 2 ≤ 2 := by
    have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  simp [hgt2, ceil_sqrt_one_add_two_mul_sq n hn]
  omega

/-- Dyadic arithmetic specialization using the notation `eps = 2^(1-k)`. -/
theorem scaledRobinsonOrder_two_zpow_one_sub_natCast {k : ℕ} (hk : 2 ≤ k) :
    scaledRobinsonOrder ((2 : ℝ) ^ (1 - (k : ℤ))) = 2 ^ (k - 2) + 3 := by
  have heps : ((2 : ℝ) ^ (1 - (k : ℤ))) = (2 * ((2 ^ (k - 2) : ℕ) : ℝ))⁻¹ := by
    rw [show (1 : ℤ) - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega]
    rw [zpow_neg, zpow_natCast]
    congr 1
    rw [show k - 1 = k - 2 + 1 by omega]
    norm_num [pow_succ]
    ring
  rw [heps]
  exact scaledRobinsonOrder_inv_two_mul (2 ^ (k - 2)) (Nat.one_le_two_pow)

end ScaledRobinson
end OptimalConvergenceRates

end
