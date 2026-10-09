/-
  Coefficient bounds for the dyadic rational-square-root package.
-/
import OptimalConvergenceRates.GeneralArchimedean.RationalSquareRootPackage

noncomputable section

open Finset

namespace OptimalConvergenceRates.GeneralArchimedean
namespace RationalSquareRoot

open UnivariateParity

theorem evenContract_coeff (P : Polynomial ℝ) (k : ℕ) :
    (evenContract P).coeff k = P.coeff (k * 2) := by
  rw [evenContract, Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  exact evenPart_even_coeff P (by omega)

/-- For a coefficientwise nonnegative polynomial, the coefficient norm is
evaluation at one. -/
theorem polynomialCoeffL1Norm_eq_eval_one_of_coeffNonneg
    {P : Polynomial ℝ} (hP : CoeffNonneg P) :
    polynomialCoeffL1Norm P = P.eval 1 := by
  rw [polynomialCoeffL1Norm, Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [abs_of_nonneg (hP k)]
  simp

/-- Selecting the even coefficients cannot increase the coefficient norm of
a coefficientwise nonnegative polynomial. -/
theorem polynomialCoeffL1Norm_evenContract_le_of_coeffNonneg
    {P : Polynomial ℝ} (hP : CoeffNonneg P) :
    polynomialCoeffL1Norm (evenContract P) ≤ polynomialCoeffL1Norm P := by
  let S := Finset.range ((evenContract P).natDegree + 1)
  let f : ℕ → ℕ := fun k => k * 2
  have hf : Function.Injective f := by
    intro a b hab
    simpa [f] using hab
  have hdeg : (evenContract P).natDegree ≤ P.natDegree :=
    evenContract_natDegree_le P
  have hS : S ⊆ Finset.range (P.natDegree + 1) := by
    intro k hk
    simp only [S, Finset.mem_range] at hk ⊢
    exact lt_of_lt_of_le hk (Nat.succ_le_succ hdeg)
  rw [polynomialCoeffL1Norm, polynomialCoeffL1Norm]
  simp_rw [evenContract_coeff, abs_of_nonneg (hP _)]
  calc
    ∑ k ∈ S, P.coeff (f k) ≤
        ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff (f k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro k hk hnot
      exact hP (f k)
    _ = ∑ j ∈ (Finset.range (P.natDegree + 1)).image f, P.coeff j := by
      rw [Finset.sum_image (fun _ _ _ _ hab => hf hab)]
    _ ≤ ∑ j ∈ Finset.range (2 * P.natDegree + 1), P.coeff j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨k, hk, rfl⟩ := hj
        simp only [Finset.mem_range] at hk ⊢
        dsimp [f]
        omega
      · intro j hj hnot
        exact hP j
    _ = ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j := by
      symm
      apply Finset.sum_subset
      · apply Finset.range_mono
        exact Nat.add_le_add_right
          (Nat.le_mul_of_pos_left P.natDegree Nat.zero_lt_two) 1
      · intro j hj hnot
        simp only [Finset.mem_range, not_lt] at hnot
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega

/-- Selecting the odd coefficients and dividing out the variable cannot
increase the coefficient norm of a coefficientwise nonnegative polynomial. -/
theorem polynomialCoeffL1Norm_oddContract_le_of_coeffNonneg
    {P : Polynomial ℝ} (hP : CoeffNonneg P) :
    polynomialCoeffL1Norm (oddContract P) ≤ polynomialCoeffL1Norm P := by
  let S := Finset.range ((oddContract P).natDegree + 1)
  let f : ℕ → ℕ := fun k => k * 2 + 1
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    omega
  have hdeg : (oddContract P).natDegree ≤ P.natDegree :=
    oddContract_natDegree_le P
  have hS : S ⊆ Finset.range (P.natDegree + 1) := by
    intro k hk
    simp only [S, Finset.mem_range] at hk ⊢
    exact lt_of_lt_of_le hk (Nat.succ_le_succ hdeg)
  rw [polynomialCoeffL1Norm, polynomialCoeffL1Norm]
  simp_rw [oddContract_coeff, abs_of_nonneg (hP _)]
  calc
    ∑ k ∈ S, P.coeff (f k) ≤
        ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff (f k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro k hk hnot
      exact hP (f k)
    _ = ∑ j ∈ (Finset.range (P.natDegree + 1)).image f, P.coeff j := by
      rw [Finset.sum_image (fun _ _ _ _ hab => hf hab)]
    _ ≤ ∑ j ∈ Finset.range (2 * P.natDegree + 2), P.coeff j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        rw [Finset.mem_image] at hj
        obtain ⟨k, hk, rfl⟩ := hj
        simp only [Finset.mem_range] at hk ⊢
        dsimp [f]
        omega
      · intro j hj hnot
        exact hP j
    _ = ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j := by
      symm
      apply Finset.sum_subset
      · apply Finset.range_mono
        omega
      · intro j hj hnot
        simp only [Finset.mem_range, not_lt] at hnot
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        omega


theorem gridPoint_mono {δ : ℝ} (hδ : 0 ≤ δ) {j J : ℕ} (hj : j ≤ J) :
    gridPoint δ j ≤ gridPoint δ J := by
  unfold gridPoint
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg δ)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj

/-- A common base controlling every affine factor in the dyadic product and
its residual. -/
def dyadicCoefficientBase (δ : ℝ) (J : ℕ) : ℝ :=
  2 + δ + gridPoint δ J + gridPoint δ J ^ 2

theorem one_le_dyadicCoefficientBase
    {δ : ℝ} (hδ : 0 ≤ δ) (J : ℕ) :
    1 ≤ dyadicCoefficientBase δ J := by
  unfold dyadicCoefficientBase
  have hg := gridPoint_nonneg hδ J
  have hs := sq_nonneg (gridPoint δ J)
  linarith

theorem gridProduct_polynomialCoeffL1Norm_le
    {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ) :
    polynomialCoeffL1Norm (gridProduct δ ell J) ≤
      dyadicCoefficientBase δ J ^ (2 * ell * (J + 1)) := by
  let Q := dyadicCoefficientBase δ J
  have hfactor (j : ℕ) (hj : j ∈ Finset.range (J + 1)) :
      (1 + gridPoint δ j) ^ (2 * ell) ≤ Q ^ (2 * ell) := by
    apply pow_le_pow_left₀
    · exact add_nonneg zero_le_one (gridPoint_nonneg hδ j)
    · dsimp [Q, dyadicCoefficientBase]
      have hgrid := gridPoint_mono hδ
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      have hsq := sq_nonneg (gridPoint δ J)
      linarith
  calc
    polynomialCoeffL1Norm (gridProduct δ ell J) =
        (gridProduct δ ell J).eval 1 :=
      polynomialCoeffL1Norm_eq_eval_one_of_coeffNonneg
        (gridProduct_coeffNonneg hδ ell J)
    _ = ∏ j ∈ Finset.range (J + 1),
        (1 + gridPoint δ j) ^ (2 * ell) := by
      rw [gridProduct_eval]
    _ ≤ ∏ _j ∈ Finset.range (J + 1), Q ^ (2 * ell) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact pow_nonneg (add_nonneg zero_le_one (gridPoint_nonneg hδ j)) _
      · intro j hj
        exact hfactor j hj
    _ = Q ^ (2 * ell * (J + 1)) := by
      simp [pow_mul]

theorem numerator_coeffL1Norm_le
    {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ) :
    embeddedPolynomialCoeffL1Norm (numerator δ ell J) ≤
      dyadicCoefficientBase δ J ^ (2 * ell * (J + 1)) := by
  exact (embeddedPolynomialCoeffL1Norm_le_polynomialCoeffL1Norm _).trans
    ((polynomialCoeffL1Norm_evenContract_le_of_coeffNonneg
      (gridProduct_coeffNonneg hδ ell J)).trans
        (gridProduct_polynomialCoeffL1Norm_le hδ ell J))

theorem denominator_coeffL1Norm_le
    {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ) :
    embeddedPolynomialCoeffL1Norm (denominator δ ell J) ≤
      dyadicCoefficientBase δ J ^ (2 * ell * (J + 1)) := by
  exact (embeddedPolynomialCoeffL1Norm_le_polynomialCoeffL1Norm _).trans
    ((polynomialCoeffL1Norm_oddContract_le_of_coeffNonneg
      (gridProduct_coeffNonneg hδ ell J)).trans
        (gridProduct_polynomialCoeffL1Norm_le hδ ell J))

theorem embeddedPolynomialCoeffL1Norm_prod_le
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (P : ι → Polynomial ℝ) :
    embeddedPolynomialCoeffL1Norm (∏ i ∈ S, P i) ≤
      ∏ i ∈ S, embeddedPolynomialCoeffL1Norm (P i) := by
  simpa [embeddedPolynomialCoeffL1Norm] using
    (coeffL1Norm_prod_le S
      (fun i => (P i).toMvPolynomial (0 : Fin 1)))

/-- One signed residual factor is controlled by the common dyadic base. -/
theorem gridResidualFactor_coeffL1Norm_le
    {δ : ℝ} (hδ : 0 ≤ δ) {j J : ℕ} (hj : j ≤ J) (ell : ℕ) :
    embeddedPolynomialCoeffL1Norm
        ((Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ^ ell) ≤
      dyadicCoefficientBase δ J ^ ell := by
  calc
    embeddedPolynomialCoeffL1Norm
        ((Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ^ ell) ≤
        embeddedPolynomialCoeffL1Norm
          (Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ^ ell :=
      embeddedPolynomialCoeffL1Norm_pow_le _ _
    _ ≤ (((gridPoint δ j) ^ 2) + 1) ^ ell := by
      apply pow_le_pow_left₀ (embeddedPolynomialCoeffL1Norm_nonneg _)
      calc
        embeddedPolynomialCoeffL1Norm
            (Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ≤
            embeddedPolynomialCoeffL1Norm
                (Polynomial.C ((gridPoint δ j) ^ 2)) +
              embeddedPolynomialCoeffL1Norm Polynomial.X :=
          embeddedPolynomialCoeffL1Norm_sub_le _ _
        _ ≤ |(gridPoint δ j) ^ 2| + 1 :=
          add_le_add (embeddedPolynomialCoeffL1Norm_C_le _)
            embeddedPolynomialCoeffL1Norm_X_le
        _ = (gridPoint δ j) ^ 2 + 1 := by
          rw [abs_of_nonneg (sq_nonneg _)]
    _ ≤ dyadicCoefficientBase δ J ^ ell := by
      apply pow_le_pow_left₀ (by positivity)
      unfold dyadicCoefficientBase
      have hgrid := gridPoint_mono hδ hj
      have hsq := pow_le_pow_left₀ (gridPoint_nonneg hδ j) hgrid 2
      have hg := gridPoint_nonneg hδ J
      linarith

theorem gridResidual_coeffL1Norm_le
    {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ) :
    embeddedPolynomialCoeffL1Norm (gridResidual δ ell J) ≤
      dyadicCoefficientBase δ J ^ (ell * (J + 1)) := by
  unfold gridResidual
  calc
    embeddedPolynomialCoeffL1Norm
        (∏ j ∈ Finset.range (J + 1),
          (Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ^ ell) ≤
        ∏ j ∈ Finset.range (J + 1), embeddedPolynomialCoeffL1Norm
          ((Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ^ ell) :=
      embeddedPolynomialCoeffL1Norm_prod_le _ _
    _ ≤ ∏ _j ∈ Finset.range (J + 1),
        dyadicCoefficientBase δ J ^ ell := by
      apply Finset.prod_le_prod
      · intro j hj
        exact embeddedPolynomialCoeffL1Norm_nonneg _
      · intro j hj
        exact gridResidualFactor_coeffL1Norm_le hδ
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) ell
    _ = dyadicCoefficientBase δ J ^ (ell * (J + 1)) := by
      simp [pow_mul]

theorem normalizeShift_coeffL1Norm_le
    {δ c Q : ℝ} {N : ℕ} {P : Polynomial ℝ}
    (hδ : 0 ≤ δ) (hc : 0 < c) (hQ : 1 ≤ Q)
    (haffine : 1 + δ ≤ Q)
    (hPnorm : embeddedPolynomialCoeffL1Norm P ≤ Q ^ N)
    (hPdegree : P.natDegree ≤ N) :
    embeddedPolynomialCoeffL1Norm (normalizeShift δ c P) ≤
      c⁻¹ * Q ^ (2 * N) := by
  have haffineNorm : embeddedPolynomialCoeffL1Norm
      (Polynomial.X + Polynomial.C δ) ≤ Q := by
    have hbase : embeddedPolynomialCoeffL1Norm
        (Polynomial.X + Polynomial.C δ) ≤ 1 + δ := by
      simpa [abs_of_nonneg hδ] using
        embeddedPolynomialCoeffL1Norm_C_mul_X_add_C_le 1 δ
    exact hbase.trans haffine
  have hcomp : embeddedPolynomialCoeffL1Norm
      (P.comp (Polynomial.X + Polynomial.C δ)) ≤ Q ^ (2 * N) := by
    calc
      embeddedPolynomialCoeffL1Norm (P.comp (Polynomial.X + Polynomial.C δ)) ≤
          embeddedPolynomialCoeffL1Norm P * Q ^ P.natDegree := by
        exact embeddedPolynomialCoeffL1Norm_comp_le P _ hQ haffineNorm
      _ ≤ Q ^ N * Q ^ N := by
        exact mul_le_mul hPnorm (pow_le_pow_right₀ hQ hPdegree)
          (pow_nonneg (zero_le_one.trans hQ) _)
          (pow_nonneg (zero_le_one.trans hQ) _)
      _ = Q ^ (2 * N) := by rw [← pow_add]; congr 1; omega
  calc
    embeddedPolynomialCoeffL1Norm (normalizeShift δ c P) ≤
        embeddedPolynomialCoeffL1Norm (Polynomial.C c⁻¹) *
          embeddedPolynomialCoeffL1Norm
            (P.comp (Polynomial.X + Polynomial.C δ)) :=
      embeddedPolynomialCoeffL1Norm_mul_le _ _
    _ ≤ c⁻¹ * Q ^ (2 * N) := by
      apply mul_le_mul (by simpa [abs_of_pos (inv_pos.mpr hc)] using
        embeddedPolynomialCoeffL1Norm_C_le c⁻¹) hcomp
      · exact embeddedPolynomialCoeffL1Norm_nonneg _
      · exact inv_nonneg.mpr hc.le

theorem two_mul_sqrt_mul_denominator_eval
    {δ : ℝ} (hδ : 0 < δ) {ell : ℕ} (hell : 0 < ell) (J : ℕ) :
    2 * Real.sqrt δ * (denominator δ ell J).eval δ =
      (gridProduct δ ell J).eval (Real.sqrt δ) := by
  let t : ℝ := Real.sqrt δ
  have ht_sq : t ^ 2 = δ := Real.sq_sqrt hδ.le
  have hzero : (gridProduct δ ell J).eval (-t) = 0 := by
    rw [gridProduct_eval]
    apply Finset.prod_eq_zero (show 0 ∈ Finset.range (J + 1) by simp)
    simp [gridPoint, t, hell.ne']
  have hplus := eval_evenContract_add_oddContract
    (gridProduct δ ell J) t
  have hminus := eval_evenContract_add_oddContract
    (gridProduct δ ell J) (-t)
  simp only [neg_sq] at hminus
  rw [ht_sq] at hplus hminus
  have hplus' :
      (gridProduct δ ell J).eval t =
        (numerator δ ell J).eval δ +
          t * (denominator δ ell J).eval δ := by
    simpa [numerator, denominator] using hplus
  have hminus' :
      (gridProduct δ ell J).eval (-t) =
        (numerator δ ell J).eval δ -
          t * (denominator δ ell J).eval δ := by
    simpa [numerator, denominator] using hminus
  rw [hzero] at hminus'
  dsimp [t] at hplus' hminus' ⊢
  linarith

theorem gridProduct_eval_sqrt_lower
    {δ : ℝ} (hδ : 0 < δ) (ell J : ℕ) :
    (2 * Real.sqrt δ) ^ (2 * ell * (J + 1)) ≤
      (gridProduct δ ell J).eval (Real.sqrt δ) := by
  let t : ℝ := Real.sqrt δ
  have ht : 0 < t := Real.sqrt_pos.2 hδ
  have hfactor (j : ℕ) (hj : j ∈ Finset.range (J + 1)) :
      (2 * t) ^ (2 * ell) ≤ (t + gridPoint δ j) ^ (2 * ell) := by
    apply pow_le_pow_left₀
    · positivity
    · have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hgrid : t ≤ gridPoint δ j := by
        dsimp [gridPoint]
        exact (le_mul_iff_one_le_left ht).2 hpow
      linarith
  rw [gridProduct_eval]
  calc
    (2 * Real.sqrt δ) ^ (2 * ell * (J + 1)) =
        ∏ _j ∈ Finset.range (J + 1), (2 * t) ^ (2 * ell) := by
      simp [t, pow_mul]
    _ ≤ ∏ j ∈ Finset.range (J + 1),
          (t + gridPoint δ j) ^ (2 * ell) := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        exact hfactor j hj

/-- The value used to normalize the odd contraction is bounded below by an
explicit power of the shift. -/
theorem denominator_eval_self_lower
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ell : ℕ} (hell : 0 < ell) (J : ℕ) :
    δ ^ (2 * ell * (J + 1) + 1) ≤
      (denominator δ ell J).eval δ := by
  let t : ℝ := Real.sqrt δ
  let N : ℕ := 2 * ell * (J + 1)
  have ht : 0 < t := Real.sqrt_pos.2 hδ
  have ht1 : t ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hδ1
  have hN : 1 ≤ N := by
    have htwoell : 0 < 2 * ell :=
      Nat.mul_pos Nat.zero_lt_two hell
    have hprod : 0 < (2 * ell) * (J + 1) :=
      Nat.mul_pos htwoell (Nat.succ_pos J)
    omega
  have ht_sq : t ^ 2 = δ := Real.sq_sqrt hδ.le
  have hdeltaPow : δ ^ (N + 1) ≤ t ^ N := by
    rw [← ht_sq, ← pow_mul]
    exact pow_le_pow_of_le_one ht.le ht1 (by omega)
  have htwoPow : (2 : ℝ) ≤ 2 ^ N := by
    calc
      (2 : ℝ) = 2 ^ 1 := by simp
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hnumeric : (2 * t) * δ ^ (N + 1) ≤ (2 * t) ^ N := by
    calc
      (2 * t) * δ ^ (N + 1) ≤ (2 * t) * t ^ N :=
        mul_le_mul_of_nonneg_left hdeltaPow (by positivity)
      _ ≤ 2 * t ^ N := by
        have h2t : 2 * t ≤ 2 := by linarith
        exact mul_le_mul_of_nonneg_right h2t (pow_nonneg ht.le N)
      _ ≤ 2 ^ N * t ^ N :=
        mul_le_mul_of_nonneg_right htwoPow (pow_nonneg ht.le N)
      _ = (2 * t) ^ N := by rw [mul_pow]
  have hproduct : (2 * t) ^ N ≤ (gridProduct δ ell J).eval t := by
    simpa [t, N] using gridProduct_eval_sqrt_lower hδ ell J
  have hidentity : (2 * t) * (denominator δ ell J).eval δ =
      (gridProduct δ ell J).eval t := by
    simpa [t, mul_assoc] using
      two_mul_sqrt_mul_denominator_eval hδ hell J
  have hmul : (2 * t) * δ ^ (N + 1) ≤
      (2 * t) * (denominator δ ell J).eval δ := by
    rw [hidentity]
    exact hnumeric.trans hproduct
  have hcancel : δ ^ (N + 1) ≤ (denominator δ ell J).eval δ := by
    nlinarith [hmul]
  simpa [N] using hcancel

/-- A raw common norm bound for the three normalized dyadic polynomials. -/
def dyadicRawNorm (δ : ℝ) (ell J : ℕ) : ℝ :=
  (δ ^ (2 * ell * (J + 1) + 1))⁻¹ *
    dyadicCoefficientBase δ J ^ (2 * (2 * ell * (J + 1)))

/-- The resulting common envelope for the packaged numerator, denominator,
and error polynomial. -/
def dyadicPackageCoefficientBound (δ : ℝ) (ell J : ℕ) : ℝ :=
  let Z := dyadicRawNorm δ ell J
  1 + 2 * Z + 2 * Z ^ 2

theorem normalized_components_coeffL1Norm_le
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ell : ℕ} (hell : 0 < ell) (J : ℕ) :
    embeddedPolynomialCoeffL1Norm (normalizedNumerator δ ell J) ≤
        dyadicRawNorm δ ell J ∧
      embeddedPolynomialCoeffL1Norm (normalizedDenominator δ ell J) ≤
        dyadicRawNorm δ ell J ∧
      embeddedPolynomialCoeffL1Norm (normalizedResidual δ ell J) ≤
        dyadicRawNorm δ ell J := by
  let N : ℕ := 2 * ell * (J + 1)
  let Q : ℝ := dyadicCoefficientBase δ J
  let c : ℝ := (denominator δ ell J).eval δ
  have hQ : 1 ≤ Q := one_le_dyadicCoefficientBase hδ.le J
  have haffine : 1 + δ ≤ Q := by
    dsimp [Q, dyadicCoefficientBase]
    have hg := gridPoint_nonneg hδ.le J
    have hs := sq_nonneg (gridPoint δ J)
    linarith
  have hc : 0 < c := denominator_eval_self_pos hδ hell J
  have hcLower : δ ^ (N + 1) ≤ c := by
    simpa [N, c] using denominator_eval_self_lower hδ hδ1 hell J
  have hδpow : 0 < δ ^ (N + 1) := pow_pos hδ _
  have hcinv : c⁻¹ ≤ (δ ^ (N + 1))⁻¹ :=
    (inv_le_inv₀ hc hδpow).2 hcLower
  have hnum : embeddedPolynomialCoeffL1Norm (numerator δ ell J) ≤ Q ^ N := by
    simpa [Q, N] using numerator_coeffL1Norm_le hδ.le ell J
  have hden : embeddedPolynomialCoeffL1Norm (denominator δ ell J) ≤ Q ^ N := by
    simpa [Q, N] using denominator_coeffL1Norm_le hδ.le ell J
  have hres : embeddedPolynomialCoeffL1Norm (gridResidual δ ell J) ≤ Q ^ N := by
    calc
      embeddedPolynomialCoeffL1Norm (gridResidual δ ell J) ≤
          Q ^ (ell * (J + 1)) := by
        simpa [Q] using gridResidual_coeffL1Norm_le hδ.le ell J
      _ ≤ Q ^ N := by
        apply pow_le_pow_right₀ hQ
        exact Nat.mul_le_mul_right (J + 1)
          (Nat.le_mul_of_pos_left ell Nat.zero_lt_two)
  have hnumNorm : embeddedPolynomialCoeffL1Norm
      (normalizedNumerator δ ell J) ≤ c⁻¹ * Q ^ (2 * N) := by
    exact normalizeShift_coeffL1Norm_le hδ.le hc hQ haffine hnum
      (by simpa [N] using numerator_degree_bound δ ell J)
  have hdenNorm : embeddedPolynomialCoeffL1Norm
      (normalizedDenominator δ ell J) ≤ c⁻¹ * Q ^ (2 * N) := by
    exact normalizeShift_coeffL1Norm_le hδ.le hc hQ haffine hden
      (by simpa [N] using denominator_degree_bound δ ell J)
  have hresNorm : embeddedPolynomialCoeffL1Norm
      (normalizedResidual δ ell J) ≤ c⁻¹ * Q ^ (2 * N) := by
    exact normalizeShift_coeffL1Norm_le hδ.le hc hQ haffine hres
      (by
        apply (gridResidual_natDegree_le δ ell J).trans
        exact Nat.mul_le_mul_right (J + 1)
          (Nat.le_mul_of_pos_left ell Nat.zero_lt_two))
  have hraw : c⁻¹ * Q ^ (2 * N) ≤ dyadicRawNorm δ ell J := by
    dsimp [dyadicRawNorm, N, Q]
    exact mul_le_mul_of_nonneg_right hcinv
      (pow_nonneg (zero_le_one.trans hQ) _)
  exact ⟨hnumNorm.trans hraw, hdenNorm.trans hraw, hresNorm.trans hraw⟩

namespace Package

/-- The intrinsic package coefficient envelope is bounded solely by the
dyadic parameters and the shift. -/
theorem coefficientBound_le_dyadicPackageCoefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    pkg.coefficientBound ≤
      dyadicPackageCoefficientBound δ pkg.ell pkg.J := by
  let Z := dyadicRawNorm δ pkg.ell pkg.J
  obtain ⟨hP, hV, hR⟩ :=
    normalized_components_coeffL1Norm_le hδ hδ1 pkg.ell_pos pkg.J
  have hZ : 0 ≤ Z := by
    dsimp [Z, dyadicRawNorm]
    exact mul_nonneg
      (inv_nonneg.mpr (pow_nonneg hδ.le _))
      (pow_nonneg (zero_le_one.trans
        (one_le_dyadicCoefficientBase hδ.le pkg.J)) _)
  have hE : embeddedPolynomialCoeffL1Norm pkg.E ≤ 2 * Z ^ 2 := by
    calc
      embeddedPolynomialCoeffL1Norm pkg.E =
          embeddedPolynomialCoeffL1Norm
            (Polynomial.C δ * pkg.V ^ 2 +
              normalizedResidual δ pkg.ell pkg.J ^ 2) := rfl
      _ ≤ embeddedPolynomialCoeffL1Norm (Polynomial.C δ * pkg.V ^ 2) +
          embeddedPolynomialCoeffL1Norm
            (normalizedResidual δ pkg.ell pkg.J ^ 2) :=
        embeddedPolynomialCoeffL1Norm_add_le _ _
      _ ≤ (δ * Z ^ 2) + Z ^ 2 := by
        apply add_le_add
        · calc
            embeddedPolynomialCoeffL1Norm (Polynomial.C δ * pkg.V ^ 2) ≤
                embeddedPolynomialCoeffL1Norm (Polynomial.C δ) *
                  embeddedPolynomialCoeffL1Norm (pkg.V ^ 2) :=
              embeddedPolynomialCoeffL1Norm_mul_le _ _
            _ ≤ δ * Z ^ 2 := by
              apply mul_le_mul
              · simpa [abs_of_pos hδ] using
                  embeddedPolynomialCoeffL1Norm_C_le δ
              · exact (embeddedPolynomialCoeffL1Norm_pow_le pkg.V 2).trans
                  (pow_le_pow_left₀
                    (embeddedPolynomialCoeffL1Norm_nonneg pkg.V) hV 2)
              · exact embeddedPolynomialCoeffL1Norm_nonneg _
              · exact hδ.le
        · exact (embeddedPolynomialCoeffL1Norm_pow_le _ 2).trans
            (pow_le_pow_left₀
              (embeddedPolynomialCoeffL1Norm_nonneg
                (normalizedResidual δ pkg.ell pkg.J)) hR 2)
      _ ≤ 2 * Z ^ 2 := by
        have hZsq := sq_nonneg Z
        nlinarith
  unfold coefficientBound
  dsimp [dyadicPackageCoefficientBound]
  change 1 + embeddedPolynomialCoeffL1Norm pkg.P +
      embeddedPolynomialCoeffL1Norm pkg.V + embeddedPolynomialCoeffL1Norm pkg.E ≤
    1 + 2 * Z + 2 * Z ^ 2
  linarith

end Package
end RationalSquareRoot
end OptimalConvergenceRates.GeneralArchimedean

end
