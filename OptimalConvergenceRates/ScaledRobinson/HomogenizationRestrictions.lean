/-
  OptimalConvergenceRates/ScaledRobinson/HomogenizationRestrictions.lean

  Axis and diagonal restrictions for the scaled Robinson homogenization.
-/
import OptimalConvergenceRates.ScaledRobinson.HomogenizationSpectral

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- Evaluation formula for the scaled Robinson polynomial. -/
theorem scaledRobinson_eval (eps : ℝ) (x : Fin 2 → ℝ) :
    MvPolynomial.eval x (scaledRobinson eps) =
      MvPolynomial.eval (fun i => eps⁻¹ * x i) robinson := by
  have h : (MvPolynomial.aeval x).comp (scale2 eps⁻¹) =
      (MvPolynomial.aeval (fun i => eps⁻¹ * x i) :
        MvPolynomial (Fin 2) ℝ →ₐ[ℝ] ℝ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [scale2, MvPolynomial.aeval_X, map_mul]
  have hrob := AlgHom.congr_fun h robinson
  simpa [scaledRobinson, MvPolynomial.aeval_eq_eval] using hrob

/-- Evaluation formula for the dehomogenized Robinson polynomial. -/
theorem robinson_eval (x : Fin 2 → ℝ) :
    MvPolynomial.eval x robinson =
      x 0 ^ 6 + x 1 ^ 6 + 1 -
        (x 0 ^ 4 * x 1 ^ 2 + x 0 ^ 4 + x 0 ^ 2 * x 1 ^ 4 + x 1 ^ 4 +
          x 0 ^ 2 + x 1 ^ 2) + 3 * x 0 ^ 2 * x 1 ^ 2 := by
  simp [robinson, map_add, map_sub, map_mul, map_pow]

/-- Evaluation formula for the homogeneous threshold form. -/
theorem Pmlambda_eval (m : ℕ) (lambda : ℝ) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (Pmlambda m lambda) =
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ^ m *
        Phi (lambda * x 0 ^ 2) (lambda * x 1 ^ 2)
          (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  unfold Pmlambda sphereSq Phi
  simp only [map_mul, map_pow, map_add, map_sub, eval_C, eval_X]
  norm_num

/-- Axis restriction map `(x,y,z) = (t,0,1)`. -/
def axisRestrict3To1 : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval ![(Polynomial.X : Polynomial ℝ), 0, 1]

/-- Diagonal restriction map `(x,y,z) = (t/sqrt 2,t/sqrt 2,1)`. -/
def diagonalRestrict3To1 : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.C (Real.sqrt 2)⁻¹ * Polynomial.X,
    Polynomial.C (Real.sqrt 2)⁻¹ * Polynomial.X, 1]

/-- The positive axis root of the axis restriction when `lambda > 1`. -/
def axisRoot (lambda : ℝ) : ℝ :=
  (Real.sqrt (lambda - 1))⁻¹

/-- The positive diagonal root of the diagonal restriction when `lambda > 2`. -/
def diagonalRoot (lambda : ℝ) : ℝ :=
  Real.sqrt (2 / (lambda - 2))

/-- Square of the positive axis root. -/
theorem axisRoot_sq {lambda : ℝ} (hLam : 1 < lambda) :
    axisRoot lambda ^ 2 = (lambda - 1)⁻¹ := by
  unfold axisRoot
  rw [inv_pow]
  congr 1
  rw [Real.sq_sqrt]
  linarith

/-- Square of the positive diagonal root. -/
theorem diagonalRoot_sq {lambda : ℝ} (hLam : 2 < lambda) :
    diagonalRoot lambda ^ 2 = 2 / (lambda - 2) := by
  unfold diagonalRoot
  rw [Real.sq_sqrt]
  have hden_pos : 0 < lambda - 2 := by linarith
  positivity

/-- The axis root cancels the axis linear factor. -/
theorem axisRoot_linear_eq_zero {lambda : ℝ} (hLam : 1 < lambda) :
    (lambda - 1) * axisRoot lambda ^ 2 - 1 = 0 := by
  unfold axisRoot
  have hpos : 0 < lambda - 1 := by linarith
  have hsqrt_sq : (Real.sqrt (lambda - 1)) ^ 2 = lambda - 1 := by
    rw [Real.sq_sqrt]
    linarith
  have hsqrt_ne : Real.sqrt (lambda - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  field_simp [hsqrt_ne]
  rw [hsqrt_sq]
  ring

/-- The diagonal root cancels the diagonal linear factor. -/
theorem diagonalRoot_linear_eq_zero {lambda : ℝ} (hLam : 2 < lambda) :
    ((lambda - 2) / 2) * diagonalRoot lambda ^ 2 - 1 = 0 := by
  unfold diagonalRoot
  have hden_pos : 0 < lambda - 2 := by linarith
  have hden_ne : lambda - 2 ≠ 0 := ne_of_gt hden_pos
  have hrad_nonneg : 0 ≤ 2 / (lambda - 2) := by positivity
  have hsqrt_sq : (Real.sqrt (2 / (lambda - 2))) ^ 2 = 2 / (lambda - 2) := by
    rw [Real.sq_sqrt hrad_nonneg]
  rw [hsqrt_sq]
  field_simp [hden_ne]
  ring

/-- The axis even root factor in normalized form. -/
theorem axisRoot_quadratic_factor_eq {lambda : ℝ} (hLam : 1 < lambda) :
    Polynomial.C (lambda - 1) * (Polynomial.X ^ 2 - Polynomial.C (axisRoot lambda ^ 2)) =
      Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1 := by
  apply Polynomial.funext
  intro x
  simp
  have hroot := axisRoot_linear_eq_zero hLam
  nlinarith

/-- The diagonal even root factor in normalized form. -/
theorem diagonalRoot_quadratic_factor_eq {lambda : ℝ} (hLam : 2 < lambda) :
    Polynomial.C ((lambda - 2) / 2) *
        (Polynomial.X ^ 2 - Polynomial.C (diagonalRoot lambda ^ 2)) =
      Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1 := by
  apply Polynomial.funext
  intro x
  simp
  have hroot := diagonalRoot_linear_eq_zero hLam
  nlinarith

/-- Axis restriction of `P_{m,lambda}`. -/
theorem Pmlambda_axis_eval (m : ℕ) (lambda t : ℝ) :
    MvPolynomial.eval ![t, 0, 1] (Pmlambda m lambda) =
      ((lambda - 1) * t ^ 2 - 1) ^ 2 * (1 + t ^ 2) ^ m *
        (1 + (lambda + 1) * t ^ 2) := by
  rw [Pmlambda_eval]
  unfold Phi
  simp
  ring

/-- Diagonal restriction of `P_{m,lambda}` with `x = y = t / sqrt 2`. -/
theorem Pmlambda_diagonal_eval (m : ℕ) (lambda t : ℝ) :
    MvPolynomial.eval ![t / Real.sqrt 2, t / Real.sqrt 2, 1] (Pmlambda m lambda) =
      (((lambda - 2) / 2) * t ^ 2 - 1) ^ 2 * (1 + t ^ 2) ^ (m + 1) := by
  rw [Pmlambda_eval]
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  unfold Phi
  simp [hsqrt2_sq, div_pow]
  field_simp [show (Real.sqrt 2) ^ 2 ≠ 0 by rw [hsqrt2_sq]; norm_num]
  ring

/-- Evaluation compatibility for the axis restriction map. -/
theorem axisRestrict3To1_eval (p : MvPolynomial (Fin 3) ℝ) (t : ℝ) :
    Polynomial.eval t (axisRestrict3To1 p) = MvPolynomial.eval ![t, 0, 1] p := by
  have h : (Polynomial.aeval t).comp axisRestrict3To1 =
      (MvPolynomial.aeval ![t, 0, 1] : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] ℝ) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [axisRestrict3To1]
  exact AlgHom.congr_fun h p

/-- Evaluation compatibility for the diagonal restriction map. -/
theorem diagonalRestrict3To1_eval (p : MvPolynomial (Fin 3) ℝ) (t : ℝ) :
    Polynomial.eval t (diagonalRestrict3To1 p) =
      MvPolynomial.eval ![t / Real.sqrt 2, t / Real.sqrt 2, 1] p := by
  have h : (Polynomial.aeval t).comp diagonalRestrict3To1 =
      (MvPolynomial.aeval ![t / Real.sqrt 2, t / Real.sqrt 2, 1] :
        MvPolynomial (Fin 3) ℝ →ₐ[ℝ] ℝ) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [diagonalRestrict3To1, div_eq_mul_inv]
      ring
    · simp [diagonalRestrict3To1, div_eq_mul_inv]
      ring
    · simp [diagonalRestrict3To1]
  exact AlgHom.congr_fun h p

/-- Polynomial identity for the axis restriction of `P_{m,lambda}`. -/
theorem axisRestrict3To1_Pmlambda (m : ℕ) (lambda : ℝ) :
    axisRestrict3To1 (Pmlambda m lambda) =
      ((Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) ^ 2 *
        (1 + Polynomial.X ^ 2) ^ m *
          (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)) := by
  apply Polynomial.funext
  intro t
  rw [axisRestrict3To1_eval, Pmlambda_axis_eval]
  simp

/-- Polynomial identity for the diagonal restriction of `P_{m,lambda}`. -/
theorem diagonalRestrict3To1_Pmlambda (m : ℕ) (lambda : ℝ) :
    diagonalRestrict3To1 (Pmlambda m lambda) =
      ((Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) ^ 2 *
        ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)) := by
  apply Polynomial.funext
  intro t
  rw [diagonalRestrict3To1_eval, Pmlambda_diagonal_eval]
  simp

/-- Restricting a ternary SOS form to the affine axis gives a univariate SOS. -/
theorem IsSOS.toIsSOSUni_axisRestrict3To1 {p : MvPolynomial (Fin 3) ℝ} (hp : IsSOS p) :
    IsSOSUni (axisRestrict3To1 p) := by
  obtain ⟨N, Q, hQ⟩ := hp
  exact ⟨N, fun i => axisRestrict3To1 (Q i), by
    rw [hQ]
    simp only [map_sum, map_pow]⟩

/-- Restricting a ternary SOS form to the affine diagonal gives a univariate SOS. -/
theorem IsSOS.toIsSOSUni_diagonalRestrict3To1 {p : MvPolynomial (Fin 3) ℝ} (hp : IsSOS p) :
    IsSOSUni (diagonalRestrict3To1 p) := by
  obtain ⟨N, Q, hQ⟩ := hp
  exact ⟨N, fun i => diagonalRestrict3To1 (Q i), by
    rw [hQ]
    simp only [map_sum, map_pow]⟩

/-- Evaluating a concrete univariate SOS decomposition at a zero forces each summand to vanish. -/
theorem IsSOSUni.eval_zero_of_witness
    {N : ℕ} {p : Polynomial ℝ} {Q : Fin N → Polynomial ℝ}
    (hQ : p = ∑ i : Fin N, (Q i) ^ 2) {t : ℝ} (ht : p.eval t = 0) :
    ∀ i : Fin N, (Q i).eval t = 0 := by
  have hsum : (∑ i : Fin N, (Q i).eval t ^ 2) = 0 := by
    rw [hQ] at ht
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_pow] using ht
  exact (sum_sq_eq_zero_iff (fun i : Fin N => (Q i).eval t)).mp hsum

/-- A univariate SOS is pointwise nonnegative. -/
theorem IsSOSUni.eval_nonneg {p : Polynomial ℝ} (hp : IsSOSUni p) (t : ℝ) :
    0 ≤ p.eval t := by
  obtain ⟨N, Q, hQ⟩ := hp
  rw [hQ]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow]
  exact Finset.sum_nonneg fun i _hi => sq_nonneg ((Q i).eval t)

/-- A real root gives the corresponding linear factor. -/
theorem Polynomial.X_sub_C_dvd_of_eval_eq_zero (p : Polynomial ℝ) {t : ℝ}
    (ht : p.eval t = 0) : Polynomial.X - Polynomial.C t ∣ p := by
  rw [Polynomial.dvd_iff_isRoot]
  exact ht

/-- Every square root in a univariate SOS decomposition has each root of the SOS polynomial. -/
theorem IsSOSUni.each_witness_eval_zero_at_root
    {N : ℕ} {p : Polynomial ℝ} {Q : Fin N → Polynomial ℝ}
    (hQ : p = ∑ i : Fin N, (Q i) ^ 2) {t : ℝ} (ht : p.eval t = 0) (i : Fin N) :
    (Q i).eval t = 0 :=
  IsSOSUni.eval_zero_of_witness hQ ht i

/-- The two distinct real linear factors at `t` and `-t` are coprime. -/
theorem Polynomial.isCoprime_X_sub_C_pos_neg {t : ℝ} (ht : t ≠ 0) :
    IsCoprime (Polynomial.X - Polynomial.C t) (Polynomial.X - Polynomial.C (-t)) := by
  refine ⟨Polynomial.C (-(2 * t)⁻¹), Polynomial.C ((2 * t)⁻¹), ?_⟩
  apply Polynomial.funext
  intro x
  simp
  field_simp [ht]
  ring

/-- Cancellation by a nonzero polynomial on the left. -/
theorem Polynomial.mul_left_cancel_of_ne_zero {a b c : Polynomial ℝ} (ha : a ≠ 0)
    (h : a * b = a * c) : b = c := by
  have hzero : a * (b - c) = 0 := by
    rw [mul_sub, h]
    ring
  have hor := mul_eq_zero.mp hzero
  cases hor with
  | inl hz => exact False.elim (ha hz)
  | inr hz => exact sub_eq_zero.mp hz

/-- Squared norm of a sum of two finite real vectors. -/
theorem vecSqNorm_add {N : ℕ} (u v : Fin N → ℝ) :
    vecSqNorm (fun i => u i + v i) = vecSqNorm u + 2 * vecDot u v + vecSqNorm v := by
  unfold vecSqNorm vecDot
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [show (∑ x : Fin N, 2 * u x * v x) = 2 * (∑ x : Fin N, u x * v x) by
    rw [Finset.mul_sum]
    congr 1
    ext x
    ring]

/-- Squared norm after dividing a vector sum by `sqrt 2`. -/
theorem vecSqNorm_add_div_sqrt_two {N : ℕ} (u v : Fin N → ℝ) :
    vecSqNorm (fun i => (u i + v i) / Real.sqrt 2) =
      (vecSqNorm (fun i => u i + v i)) / 2 := by
  unfold vecSqNorm
  rw [Finset.sum_div]
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  apply Finset.sum_congr rfl
  intro i _
  field_simp [show Real.sqrt 2 ≠ 0 by positivity]
  rw [hsqrt2_sq]

/-- If two vectors are orthogonal and have equal norm, their normalized sum has the same
norm. -/
theorem vecNorm_add_div_sqrt_two_eq_of_orthogonal_of_norm_eq {N : ℕ}
    {u v : Fin N → ℝ} (hdot : vecDot u v = 0) (hnorm : vecNorm u = vecNorm v) :
    vecNorm (fun i => (u i + v i) / Real.sqrt 2) = vecNorm u := by
  have hsq : vecNorm (fun i => (u i + v i) / Real.sqrt 2) ^ 2 = vecNorm u ^ 2 := by
    rw [vecNorm_sq, vecSqNorm_add_div_sqrt_two, vecSqNorm_add, hdot]
    have hv_sq : vecSqNorm v = vecSqNorm u := by
      rw [← vecNorm_sq v, ← vecNorm_sq u, ← hnorm]
    rw [hv_sq, ← vecNorm_sq u]
    ring
  nlinarith [vecNorm_nonneg (fun i => (u i + v i) / Real.sqrt 2), vecNorm_nonneg u]

/-- Negating every coordinate preserves the finite Euclidean norm. -/
theorem vecNorm_neg {N : ℕ} (v : Fin N → ℝ) : vecNorm (fun i => -v i) = vecNorm v := by
  unfold vecNorm vecSqNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Signed form of the normalized-sum norm identity used by the symmetrized derivative
comparison. -/
theorem vecNorm_neg_add_div_sqrt_two_eq_neg_left_of_orthogonal_of_norm_eq {N : ℕ}
    {u v : Fin N → ℝ} (hdot : vecDot u v = 0) (hnorm : vecNorm u = vecNorm v) :
    vecNorm (fun i => -((u i + v i) / Real.sqrt 2)) = vecNorm (fun i => -u i) := by
  rw [vecNorm_neg, vecNorm_neg]
  exact vecNorm_add_div_sqrt_two_eq_of_orthogonal_of_norm_eq hdot hnorm

/-- The normalized quadratic factor has value `-1` at zero and zero derivative there,
so stripping it changes first derivatives at zero by a sign. -/
theorem normalizedQuadraticFactor_mul_derivative_eval_zero (a : ℝ) (F : Polynomial ℝ) :
    (Polynomial.derivative ((Polynomial.C a * Polynomial.X ^ 2 - 1) * F)).eval 0 =
      - (Polynomial.derivative F).eval 0 := by
  rw [Polynomial.derivative_mul]
  have heval : ((Polynomial.C a * Polynomial.X ^ 2 - 1 : Polynomial ℝ).eval 0) = -1 := by
    simp
  simp [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow, heval]

/-- Evaluation of an explicit univariate SOS decomposition is the squared norm of the
evaluated square-root vector. -/
theorem sosUni_eval_eq_vecSqNorm
    {N : ℕ} {p : Polynomial ℝ} {P : Fin N → Polynomial ℝ}
    (hp : p = ∑ i : Fin N, (P i) ^ 2) (t : ℝ) :
    p.eval t = vecSqNorm (fun i => (P i).eval t) := by
  rw [hp]
  unfold vecSqNorm
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow]

/-- Multiplying a divisor by a nonzero real scalar preserves divisibility over `ℝ`. -/
theorem Polynomial.C_mul_dvd_of_dvd {p q : Polynomial ℝ} {a : ℝ} (ha : a ≠ 0)
    (h : p ∣ q) : Polynomial.C a * p ∣ q := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨Polynomial.C a⁻¹ * s, ?_⟩
  calc
    p * s = 1 * (p * s) := by simp
    _ = (Polynomial.C a * Polynomial.C a⁻¹) * (p * s) := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ ha]
      simp
    _ = Polynomial.C a * p * (Polynomial.C a⁻¹ * s) := by ring

/-- Divisibility by the two opposite linear factors gives divisibility by the corresponding
quadratic factor. -/
theorem Polynomial.X_sq_sub_C_sq_dvd_of_pos_neg_linear_dvd
    {q : Polynomial ℝ} {t : ℝ} (ht : t ≠ 0)
    (hpos : Polynomial.X - Polynomial.C t ∣ q)
    (hneg : Polynomial.X - Polynomial.C (-t) ∣ q) :
    Polynomial.X ^ 2 - Polynomial.C (t ^ 2) ∣ q := by
  have hprod : (Polynomial.X - Polynomial.C t) * (Polynomial.X - Polynomial.C (-t)) ∣ q :=
    (Polynomial.isCoprime_X_sub_C_pos_neg ht).mul_dvd hpos hneg
  rwa [show (Polynomial.X - Polynomial.C t) * (Polynomial.X - Polynomial.C (-t)) =
      Polynomial.X ^ 2 - Polynomial.C (t ^ 2) by
        apply Polynomial.funext
        intro x
        simp
        ring] at hprod

/-- Every square root in a univariate SOS decomposition is divisible by the linear root factor. -/
theorem IsSOSUni.each_witness_linear_dvd_at_root
    {N : ℕ} {p : Polynomial ℝ} {Q : Fin N → Polynomial ℝ}
    (hQ : p = ∑ i : Fin N, (Q i) ^ 2) {t : ℝ} (ht : p.eval t = 0) (i : Fin N) :
    Polynomial.X - Polynomial.C t ∣ Q i :=
  Polynomial.X_sub_C_dvd_of_eval_eq_zero (Q i)
    (IsSOSUni.each_witness_eval_zero_at_root hQ ht i)

/-- The axis restriction of an SOS `P_{m,lambda}` is the corresponding univariate SOS. -/
theorem IsSOS.axisRestrict3To1_Pmlambda {m : ℕ} {lambda : ℝ}
    (hSOS : IsSOS (Pmlambda m lambda)) :
    IsSOSUni (((Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) ^ 2 *
      (1 + Polynomial.X ^ 2) ^ m *
        (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2))) := by
  rw [← _root_.OptimalConvergenceRates.ScaledRobinson.axisRestrict3To1_Pmlambda m lambda]
  exact IsSOS.toIsSOSUni_axisRestrict3To1 hSOS

/-- The diagonal restriction of an SOS `P_{m,lambda}` is the corresponding univariate SOS. -/
theorem IsSOS.diagonalRestrict3To1_Pmlambda {m : ℕ} {lambda : ℝ}
    (hSOS : IsSOS (Pmlambda m lambda)) :
    IsSOSUni (((Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) ^ 2 *
      ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1))) := by
  rw [← _root_.OptimalConvergenceRates.ScaledRobinson.diagonalRestrict3To1_Pmlambda m lambda]
  exact IsSOS.toIsSOSUni_diagonalRestrict3To1 hSOS

/-- The axis restriction of `P_{m,lambda}` vanishes at the positive axis root. -/
theorem axisRestrict3To1_Pmlambda_eval_axisRoot_eq_zero
    (m : ℕ) {lambda : ℝ} (hLam : 1 < lambda) :
    (axisRestrict3To1 (Pmlambda m lambda)).eval (axisRoot lambda) = 0 := by
  rw [axisRestrict3To1_Pmlambda]
  simp [axisRoot_linear_eq_zero hLam]

/-- The axis restriction of `P_{m,lambda}` vanishes at the negative axis root. -/
theorem axisRestrict3To1_Pmlambda_eval_neg_axisRoot_eq_zero
    (m : ℕ) {lambda : ℝ} (hLam : 1 < lambda) :
    (axisRestrict3To1 (Pmlambda m lambda)).eval (-axisRoot lambda) = 0 := by
  rw [axisRestrict3To1_Pmlambda]
  have hroot := axisRoot_linear_eq_zero (lambda := lambda) hLam
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, neg_sq] using
    show (((lambda - 1) * axisRoot lambda ^ 2 - 1) ^ 2 *
      (1 + axisRoot lambda ^ 2) ^ m * (1 + (lambda + 1) * axisRoot lambda ^ 2)) = 0 by
      simp [hroot]

/-- The diagonal restriction of `P_{m,lambda}` vanishes at the positive diagonal root. -/
theorem diagonalRestrict3To1_Pmlambda_eval_diagonalRoot_eq_zero
    (m : ℕ) {lambda : ℝ} (hLam : 2 < lambda) :
    (diagonalRestrict3To1 (Pmlambda m lambda)).eval (diagonalRoot lambda) = 0 := by
  rw [diagonalRestrict3To1_Pmlambda]
  simp [diagonalRoot_linear_eq_zero hLam]

/-- The diagonal restriction of `P_{m,lambda}` vanishes at the negative diagonal root. -/
theorem diagonalRestrict3To1_Pmlambda_eval_neg_diagonalRoot_eq_zero
    (m : ℕ) {lambda : ℝ} (hLam : 2 < lambda) :
    (diagonalRestrict3To1 (Pmlambda m lambda)).eval (-diagonalRoot lambda) = 0 := by
  rw [diagonalRestrict3To1_Pmlambda]
  have hroot := diagonalRoot_linear_eq_zero (lambda := lambda) hLam
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, neg_sq] using
    show ((((lambda - 2) / 2) * diagonalRoot lambda ^ 2 - 1) ^ 2 *
      (1 + diagonalRoot lambda ^ 2) ^ (m + 1)) = 0 by
      simp [hroot]

/-- Axis-restricted square roots of an SOS `P_{m,lambda}` vanish at the positive axis root. -/
theorem IsSOS.exists_axisRestriction_witness_linear_dvd
    {m : ℕ} {lambda : ℝ} (hLam : 1 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ Q : Fin N → Polynomial ℝ,
      axisRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 ∧
        ∀ i : Fin N, Polynomial.X - Polynomial.C (axisRoot lambda) ∣ Q i := by
  obtain ⟨N, H, hH⟩ := hSOS
  let Q : Fin N → Polynomial ℝ := fun i => axisRestrict3To1 (H i)
  have hQ : axisRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 := by
    rw [hH]
    simp only [map_sum, map_pow]
    simp [Q]
  refine ⟨N, Q, hQ, ?_⟩
  intro i
  exact IsSOSUni.each_witness_linear_dvd_at_root hQ
    (axisRestrict3To1_Pmlambda_eval_axisRoot_eq_zero m hLam) i

/-- Diagonal-restricted square roots of an SOS `P_{m,lambda}` vanish at the positive
    diagonal root. -/
theorem IsSOS.exists_diagonalRestriction_witness_linear_dvd
    {m : ℕ} {lambda : ℝ} (hLam : 2 < lambda)
    (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ Q : Fin N → Polynomial ℝ,
      diagonalRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 ∧
        ∀ i : Fin N, Polynomial.X - Polynomial.C (diagonalRoot lambda) ∣ Q i := by
  obtain ⟨N, H, hH⟩ := hSOS
  let Q : Fin N → Polynomial ℝ := fun i => diagonalRestrict3To1 (H i)
  have hQ : diagonalRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 := by
    rw [hH]
    simp only [map_sum, map_pow]
    simp [Q]
  refine ⟨N, Q, hQ, ?_⟩
  intro i
  exact IsSOSUni.each_witness_linear_dvd_at_root hQ
    (diagonalRestrict3To1_Pmlambda_eval_diagonalRoot_eq_zero m hLam) i

/-- Axis-restricted square roots of an SOS `P_{m,lambda}` vanish at the negative axis root. -/
theorem IsSOS.exists_axisRestriction_witness_neg_linear_dvd
    {m : ℕ} {lambda : ℝ} (hLam : 1 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ Q : Fin N → Polynomial ℝ,
      axisRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 ∧
        ∀ i : Fin N, Polynomial.X - Polynomial.C (-axisRoot lambda) ∣ Q i := by
  obtain ⟨N, H, hH⟩ := hSOS
  let Q : Fin N → Polynomial ℝ := fun i => axisRestrict3To1 (H i)
  have hQ : axisRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 := by
    rw [hH]
    simp only [map_sum, map_pow]
    simp [Q]
  refine ⟨N, Q, hQ, ?_⟩
  intro i
  exact IsSOSUni.each_witness_linear_dvd_at_root hQ
    (axisRestrict3To1_Pmlambda_eval_neg_axisRoot_eq_zero m hLam) i

/-- Diagonal-restricted square roots of an SOS `P_{m,lambda}` vanish at the negative
    diagonal root. -/
theorem IsSOS.exists_diagonalRestriction_witness_neg_linear_dvd
    {m : ℕ} {lambda : ℝ} (hLam : 2 < lambda)
    (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ Q : Fin N → Polynomial ℝ,
      diagonalRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 ∧
        ∀ i : Fin N, Polynomial.X - Polynomial.C (-diagonalRoot lambda) ∣ Q i := by
  obtain ⟨N, H, hH⟩ := hSOS
  let Q : Fin N → Polynomial ℝ := fun i => diagonalRestrict3To1 (H i)
  have hQ : diagonalRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 := by
    rw [hH]
    simp only [map_sum, map_pow]
    simp [Q]
  refine ⟨N, Q, hQ, ?_⟩
  intro i
  exact IsSOSUni.each_witness_linear_dvd_at_root hQ
    (diagonalRestrict3To1_Pmlambda_eval_neg_diagonalRoot_eq_zero m hLam) i

/-- Axis-restricted square roots of an SOS `P_{m,lambda}` have the full even
quadratic root factor. -/
theorem IsSOS.exists_axisRestriction_witness_quadratic_dvd
    {m : ℕ} {lambda : ℝ} (hLam : 1 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ Q : Fin N → Polynomial ℝ,
      axisRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 ∧
        ∀ i : Fin N, Polynomial.X ^ 2 - Polynomial.C (axisRoot lambda ^ 2) ∣ Q i := by
  obtain ⟨N, H, hH⟩ := hSOS
  let Q : Fin N → Polynomial ℝ := fun i => axisRestrict3To1 (H i)
  have hQ : axisRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 := by
    rw [hH]
    simp only [map_sum, map_pow]
    simp [Q]
  refine ⟨N, Q, hQ, ?_⟩
  intro i
  apply Polynomial.X_sq_sub_C_sq_dvd_of_pos_neg_linear_dvd
  · unfold axisRoot
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by linarith)))
  · exact IsSOSUni.each_witness_linear_dvd_at_root hQ
      (axisRestrict3To1_Pmlambda_eval_axisRoot_eq_zero m hLam) i
  · exact IsSOSUni.each_witness_linear_dvd_at_root hQ
      (axisRestrict3To1_Pmlambda_eval_neg_axisRoot_eq_zero m hLam) i

/-- Diagonal-restricted square roots of an SOS `P_{m,lambda}` have the full even
quadratic root factor. -/
theorem IsSOS.exists_diagonalRestriction_witness_quadratic_dvd
    {m : ℕ} {lambda : ℝ} (hLam : 2 < lambda)
    (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ Q : Fin N → Polynomial ℝ,
      diagonalRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 ∧
        ∀ i : Fin N, Polynomial.X ^ 2 - Polynomial.C (diagonalRoot lambda ^ 2) ∣ Q i := by
  obtain ⟨N, H, hH⟩ := hSOS
  let Q : Fin N → Polynomial ℝ := fun i => diagonalRestrict3To1 (H i)
  have hQ : diagonalRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 := by
    rw [hH]
    simp only [map_sum, map_pow]
    simp [Q]
  refine ⟨N, Q, hQ, ?_⟩
  intro i
  apply Polynomial.X_sq_sub_C_sq_dvd_of_pos_neg_linear_dvd
  · unfold diagonalRoot
    have hden_pos : 0 < lambda - 2 := by linarith
    have hrad_pos : 0 < 2 / (lambda - 2) := by positivity
    exact ne_of_gt (Real.sqrt_pos.2 hrad_pos)
  · exact IsSOSUni.each_witness_linear_dvd_at_root hQ
      (diagonalRestrict3To1_Pmlambda_eval_diagonalRoot_eq_zero m hLam) i
  · exact IsSOSUni.each_witness_linear_dvd_at_root hQ
      (diagonalRestrict3To1_Pmlambda_eval_neg_diagonalRoot_eq_zero m hLam) i

/-- Axis-restricted square roots of an SOS `P_{m,lambda}` have the normalized
axis root factor. -/
theorem IsSOS.exists_axisRestriction_witness_normalized_quadratic_dvd
    {m : ℕ} {lambda : ℝ} (hLam : 1 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ Q : Fin N → Polynomial ℝ,
      axisRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 ∧
        ∀ i : Fin N, Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1 ∣ Q i := by
  obtain ⟨N, Q, hQ, hdiv⟩ :=
    IsSOS.exists_axisRestriction_witness_quadratic_dvd hLam hSOS
  refine ⟨N, Q, hQ, ?_⟩
  intro i
  have hscaled := Polynomial.C_mul_dvd_of_dvd (by linarith : lambda - 1 ≠ 0) (hdiv i)
  rwa [axisRoot_quadratic_factor_eq hLam] at hscaled

/-- Diagonal-restricted square roots of an SOS `P_{m,lambda}` have the normalized
diagonal root factor. -/
theorem IsSOS.exists_diagonalRestriction_witness_normalized_quadratic_dvd
    {m : ℕ} {lambda : ℝ} (hLam : 2 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ Q : Fin N → Polynomial ℝ,
      diagonalRestrict3To1 (Pmlambda m lambda) = ∑ i : Fin N, (Q i) ^ 2 ∧
        ∀ i : Fin N, Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1 ∣ Q i := by
  obtain ⟨N, Q, hQ, hdiv⟩ :=
    IsSOS.exists_diagonalRestriction_witness_quadratic_dvd hLam hSOS
  refine ⟨N, Q, hQ, ?_⟩
  intro i
  have hcoef_ne : (lambda - 2) / 2 ≠ 0 := by
    have hden : (2 : ℝ) ≠ 0 := by norm_num
    exact div_ne_zero (by linarith) hden
  have hscaled := Polynomial.C_mul_dvd_of_dvd hcoef_ne (hdiv i)
  rwa [diagonalRoot_quadratic_factor_eq hLam] at hscaled

/-- A single SOS witness for `P_{m,lambda}` gives simultaneous axis and diagonal
restricted witnesses, before stripping. Keeping the common index set is needed for
the later symmetry comparison of first derivatives. -/
theorem IsSOS.exists_axis_diagonalRestriction_common_witness
    {m : ℕ} {lambda : ℝ} (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ H : Fin N → MvPolynomial (Fin 3) ℝ,
      Pmlambda m lambda = ∑ i : Fin N, (H i) ^ 2 ∧
      axisRestrict3To1 (Pmlambda m lambda) =
        ∑ i : Fin N, (axisRestrict3To1 (H i)) ^ 2 ∧
      diagonalRestrict3To1 (Pmlambda m lambda) =
        ∑ i : Fin N, (diagonalRestrict3To1 (H i)) ^ 2 := by
  obtain ⟨N, H, hH⟩ := hSOS
  refine ⟨N, H, hH, ?_, ?_⟩
  · rw [hH]
    simp only [map_sum, map_pow]
  · rw [hH]
    simp only [map_sum, map_pow]

/-- A common SOS witness for `P_{m,lambda}` can be stripped on both the axis and
diagonal restrictions, with the same finite index set. -/
theorem IsSOS.exists_axis_diagonalRestriction_common_normalized_factorization
    {m : ℕ} {lambda : ℝ} (hLam : 2 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ Faxis Fdiag : Fin N → Polynomial ℝ,
      axisRestrict3To1 (Pmlambda m lambda) =
        ∑ i : Fin N,
          ((Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) * Faxis i) ^ 2 ∧
      diagonalRestrict3To1 (Pmlambda m lambda) =
        ∑ i : Fin N,
          ((Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) * Fdiag i) ^ 2 := by
  have hgt1 : 1 < lambda := by linarith
  obtain ⟨N, H, _hH, hAxis, hDiag⟩ :=
    IsSOS.exists_axis_diagonalRestriction_common_witness hSOS
  have hAxisDiv : ∀ i : Fin N,
      Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1 ∣ axisRestrict3To1 (H i) := by
    intro i
    have hquad : Polynomial.X ^ 2 - Polynomial.C (axisRoot lambda ^ 2) ∣
        axisRestrict3To1 (H i) := by
      apply Polynomial.X_sq_sub_C_sq_dvd_of_pos_neg_linear_dvd
      · unfold axisRoot
        exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by linarith)))
      · exact IsSOSUni.each_witness_linear_dvd_at_root hAxis
          (axisRestrict3To1_Pmlambda_eval_axisRoot_eq_zero m hgt1) i
      · exact IsSOSUni.each_witness_linear_dvd_at_root hAxis
          (axisRestrict3To1_Pmlambda_eval_neg_axisRoot_eq_zero m hgt1) i
    have hscaled := Polynomial.C_mul_dvd_of_dvd (by linarith : lambda - 1 ≠ 0) hquad
    rwa [axisRoot_quadratic_factor_eq hgt1] at hscaled
  have hDiagDiv : ∀ i : Fin N,
      Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1 ∣ diagonalRestrict3To1 (H i) := by
    intro i
    have hquad : Polynomial.X ^ 2 - Polynomial.C (diagonalRoot lambda ^ 2) ∣
        diagonalRestrict3To1 (H i) := by
      apply Polynomial.X_sq_sub_C_sq_dvd_of_pos_neg_linear_dvd
      · unfold diagonalRoot
        have hden_pos : 0 < lambda - 2 := by linarith
        have hrad_pos : 0 < 2 / (lambda - 2) := by positivity
        exact ne_of_gt (Real.sqrt_pos.2 hrad_pos)
      · exact IsSOSUni.each_witness_linear_dvd_at_root hDiag
          (diagonalRestrict3To1_Pmlambda_eval_diagonalRoot_eq_zero m hLam) i
      · exact IsSOSUni.each_witness_linear_dvd_at_root hDiag
          (diagonalRestrict3To1_Pmlambda_eval_neg_diagonalRoot_eq_zero m hLam) i
    have hcoef_ne : (lambda - 2) / 2 ≠ 0 := by
      exact div_ne_zero (by linarith) (by norm_num)
    have hscaled := Polynomial.C_mul_dvd_of_dvd hcoef_ne hquad
    rwa [diagonalRoot_quadratic_factor_eq hLam] at hscaled
  let Faxis : Fin N → Polynomial ℝ := fun i => (hAxisDiv i).choose
  let Fdiag : Fin N → Polynomial ℝ := fun i => (hDiagDiv i).choose
  refine ⟨N, Faxis, Fdiag, ?_, ?_⟩
  · rw [hAxis]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [(hAxisDiv i).choose_spec]
  · rw [hDiag]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [(hDiagDiv i).choose_spec]

/-- Axis restriction of an SOS `P_{m,lambda}` after stripping the normalized
axis quadratic root factor from each square root. -/
theorem IsSOS.exists_axisRestriction_witness_normalized_quadratic_factorization
    {m : ℕ} {lambda : ℝ} (hLam : 1 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ F : Fin N → Polynomial ℝ,
      axisRestrict3To1 (Pmlambda m lambda) =
        ∑ i : Fin N,
          ((Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) * F i) ^ 2 := by
  obtain ⟨N, Q, hQ, hdiv⟩ :=
    IsSOS.exists_axisRestriction_witness_normalized_quadratic_dvd hLam hSOS
  let F : Fin N → Polynomial ℝ := fun i => (hdiv i).choose
  refine ⟨N, F, ?_⟩
  rw [hQ]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [(hdiv i).choose_spec]

/-- Diagonal restriction of an SOS `P_{m,lambda}` after stripping the normalized
diagonal quadratic root factor from each square root. -/
theorem IsSOS.exists_diagonalRestriction_witness_normalized_quadratic_factorization
    {m : ℕ} {lambda : ℝ} (hLam : 2 < lambda)
    (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ F : Fin N → Polynomial ℝ,
      diagonalRestrict3To1 (Pmlambda m lambda) =
        ∑ i : Fin N,
          ((Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) * F i) ^ 2 := by
  obtain ⟨N, Q, hQ, hdiv⟩ :=
    IsSOS.exists_diagonalRestriction_witness_normalized_quadratic_dvd hLam hSOS
  let F : Fin N → Polynomial ℝ := fun i => (hdiv i).choose
  refine ⟨N, F, ?_⟩
  rw [hQ]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [(hdiv i).choose_spec]

/-- Axis restriction of an SOS `P_{m,lambda}` after stripping the even quadratic
root factor from each square root. -/
theorem IsSOS.exists_axisRestriction_witness_quadratic_factorization
    {m : ℕ} {lambda : ℝ} (hLam : 1 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ F : Fin N → Polynomial ℝ,
      axisRestrict3To1 (Pmlambda m lambda) =
        ∑ i : Fin N,
          ((Polynomial.X ^ 2 - Polynomial.C (axisRoot lambda ^ 2)) * F i) ^ 2 := by
  obtain ⟨N, Q, hQ, hdiv⟩ :=
    IsSOS.exists_axisRestriction_witness_quadratic_dvd hLam hSOS
  let F : Fin N → Polynomial ℝ := fun i => (hdiv i).choose
  refine ⟨N, F, ?_⟩
  rw [hQ]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [(hdiv i).choose_spec]

/-- Diagonal restriction of an SOS `P_{m,lambda}` after stripping the even quadratic
root factor from each square root. -/
theorem IsSOS.exists_diagonalRestriction_witness_quadratic_factorization
    {m : ℕ} {lambda : ℝ} (hLam : 2 < lambda)
    (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ F : Fin N → Polynomial ℝ,
      diagonalRestrict3To1 (Pmlambda m lambda) =
        ∑ i : Fin N,
          ((Polynomial.X ^ 2 - Polynomial.C (diagonalRoot lambda ^ 2)) * F i) ^ 2 := by
  obtain ⟨N, Q, hQ, hdiv⟩ :=
    IsSOS.exists_diagonalRestriction_witness_quadratic_dvd hLam hSOS
  let F : Fin N → Polynomial ℝ := fun i => (hdiv i).choose
  refine ⟨N, F, ?_⟩
  rw [hQ]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [(hdiv i).choose_spec]

/-- Evaluating a scalar linear combination of polynomial-vector coordinates is the dot
product of the coefficient vector with the evaluated polynomial vector. -/
theorem polynomial_weighted_sum_eval {N : ℕ} (F : Fin N → Polynomial ℝ)
    (a : Fin N → ℝ) (t : ℝ) :
    (∑ i : Fin N, Polynomial.C (a i) * F i).eval t =
      vecDot a (fun i : Fin N => (F i).eval t) := by
  unfold vecDot
  simp_rw [← Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- A scalar linear combination of polynomial-vector coordinates preserves a uniform
univariate degree bound. -/
theorem polynomial_weighted_sum_natDegree_le {N k : ℕ}
    (F : Fin N → Polynomial ℝ) (a : Fin N → ℝ)
    (hdeg : ∀ i : Fin N, (F i).natDegree ≤ k) :
    (∑ i : Fin N, Polynomial.C (a i) * F i).natDegree ≤ k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  calc
    (Polynomial.C (a i) * F i).natDegree ≤
        (Polynomial.C (a i)).natDegree + (F i).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + k := by
      rw [Polynomial.natDegree_C]
      exact Nat.add_le_add_left (hdeg i) 0
    _ = k := by omega

/-- Derivative at zero of a scalar linear combination of polynomial-vector coordinates. -/
theorem polynomial_weighted_sum_derivative_eval_zero {N : ℕ}
    (F : Fin N → Polynomial ℝ) (a : Fin N → ℝ) :
    (Polynomial.derivative (∑ i : Fin N, Polynomial.C (a i) * F i)).eval 0 =
      vecDot a (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) := by
  unfold vecDot
  rw [Polynomial.derivative_sum]
  simp_rw [← Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Polynomial.derivative_mul]

/-- If the derivative vector is nonzero, projecting onto its unit direction realizes its
norm as the derivative of a scalar linear combination. -/
theorem exists_scalar_projection_derivative_eq_vecNorm {N : ℕ}
    (F : Fin N → Polynomial ℝ)
    (hD : vecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≠ 0) :
    ∃ a : Fin N → ℝ,
      (Polynomial.derivative (∑ i : Fin N, Polynomial.C (a i) * F i)).eval 0 =
        vecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ∧
      ∀ t : ℝ, |(∑ i : Fin N, Polynomial.C (a i) * F i).eval t| ≤
        vecNorm (fun i : Fin N => (F i).eval t) := by
  let D : Fin N → ℝ := fun i => (Polynomial.derivative (F i)).eval 0
  let a : Fin N → ℝ := fun i => D i / vecNorm D
  refine ⟨a, ?_, ?_⟩
  · dsimp [a, D]
    rw [polynomial_weighted_sum_derivative_eval_zero]
    exact vecDot_unit_self hD
  · intro t
    rw [polynomial_weighted_sum_eval]
    exact abs_vecDot_unit_le (v := D) hD (fun i : Fin N => (F i).eval t)

/-- First derivative at zero is the linear coefficient. -/
theorem polynomial_derivative_eval_zero_eq_coeff_one (P : Polynomial ℝ) :
    (Polynomial.derivative P).eval 0 = P.coeff 1 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [Polynomial.coeff_derivative]
  norm_num

/-- Second derivative at zero is twice the quadratic coefficient. -/
theorem polynomial_second_derivative_eval_zero_eq_two_coeff_two (P : Polynomial ℝ) :
    (Polynomial.derivative (Polynomial.derivative P)).eval 0 = 2 * P.coeff 2 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [show Polynomial.derivative (Polynomial.derivative P) =
      (Polynomial.derivative^[2]) P by rfl]
  rw [Polynomial.coeff_iterate_derivative]
  norm_num

/-- Derivative at zero of a finite sum of univariate squares is twice the dot product
of value and derivative vectors. -/
theorem sum_sq_derivative_eval_zero {N : ℕ} (F : Fin N → Polynomial ℝ) :
    (Polynomial.derivative (∑ i : Fin N, (F i) ^ 2)).eval 0 =
      2 * vecDot (fun i : Fin N => (F i).eval 0)
        (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) := by
  rw [Polynomial.derivative_sum]
  simp only [Polynomial.derivative_pow, Nat.reduceSub, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]
  unfold vecDot
  rw [Finset.mul_sum]
  congr 1
  ext i
  ring_nf

/-- Second derivative at zero of a finite sum of univariate squares. -/
theorem sum_sq_second_derivative_eval_zero {N : ℕ} (F : Fin N → Polynomial ℝ) :
    (Polynomial.derivative (Polynomial.derivative (∑ i : Fin N, (F i) ^ 2))).eval 0 =
      2 * vecSqNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) +
        2 * vecDot (fun i : Fin N => (F i).eval 0)
          (fun i : Fin N =>
            (Polynomial.derivative (Polynomial.derivative (F i))).eval 0) := by
  rw [Polynomial.derivative_sum, Polynomial.derivative_sum]
  simp only [Polynomial.derivative_pow, Nat.reduceSub, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.derivative_mul, Polynomial.eval_add]
  unfold vecSqNorm vecDot
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [Polynomial.derivative_C]
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring_nf

/-- Second-jet identity for an axis stripped square-root vector. -/
theorem axisRestriction_stripped_second_jet_identity
    {m N : ℕ} {lambda : ℝ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)) :
    2 * vecSqNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) +
        2 * vecDot (fun i : Fin N => (F i).eval 0)
          (fun i : Fin N =>
            (Polynomial.derivative (Polynomial.derivative (F i))).eval 0) =
      2 * ((m : ℝ) + (lambda + 1)) := by
  have hder := congrArg
    (fun p : Polynomial ℝ => (Polynomial.derivative (Polynomial.derivative p)).eval 0) hNorm
  change (Polynomial.derivative
      (Polynomial.derivative (∑ i : Fin N, (F i) ^ 2))).eval 0 =
    (Polynomial.derivative (Polynomial.derivative
      ((1 + Polynomial.X ^ 2) ^ m *
        (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)))).eval 0 at hder
  rw [sum_sq_second_derivative_eval_zero] at hder
  have hrhs :
      (Polynomial.derivative (Polynomial.derivative
        ((1 + Polynomial.X ^ 2) ^ m *
          (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)))).eval 0 =
        2 * ((m : ℝ) + (lambda + 1)) := by
    simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
    ring
  rwa [hrhs] at hder

/-- Second-jet identity for a diagonal stripped square-root vector. -/
theorem diagonalRestriction_stripped_second_jet_identity
    {m N : ℕ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)) :
    2 * vecSqNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) +
        2 * vecDot (fun i : Fin N => (F i).eval 0)
          (fun i : Fin N =>
            (Polynomial.derivative (Polynomial.derivative (F i))).eval 0) =
      2 * ((m : ℝ) + 1) := by
  have hder := congrArg
    (fun p : Polynomial ℝ => (Polynomial.derivative (Polynomial.derivative p)).eval 0) hNorm
  change (Polynomial.derivative
      (Polynomial.derivative (∑ i : Fin N, (F i) ^ 2))).eval 0 =
    (Polynomial.derivative
      (Polynomial.derivative (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)))).eval 0 at hder
  rw [sum_sq_second_derivative_eval_zero] at hder
  have hrhs :
      (Polynomial.derivative
        (Polynomial.derivative (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)))).eval 0 =
        2 * ((m : ℝ) + 1) := by
    simp [Polynomial.derivative_pow]
    ring
  rwa [hrhs] at hder

/-- The axis stripped vector has squared norm one at zero. -/
theorem axisRestriction_stripped_vecSqNorm_zero
    {m N : ℕ} {lambda : ℝ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)) :
    vecSqNorm (fun i : Fin N => (F i).eval 0) = 1 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval 0) hNorm
  unfold vecSqNorm
  simpa [Polynomial.eval_finsetSum, Polynomial.eval_pow] using h

/-- The diagonal stripped vector has squared norm one at zero. -/
theorem diagonalRestriction_stripped_vecSqNorm_zero
    {m N : ℕ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 = ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)) :
    vecSqNorm (fun i : Fin N => (F i).eval 0) = 1 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval 0) hNorm
  unfold vecSqNorm
  simpa [Polynomial.eval_finsetSum, Polynomial.eval_pow] using h

/-- A vector with squared norm one has norm one. -/
theorem vecNorm_eq_one_of_vecSqNorm_eq_one {N : ℕ} {v : Fin N → ℝ}
    (h : vecSqNorm v = 1) :
    vecNorm v = 1 := by
  unfold vecNorm
  rw [h, Real.sqrt_one]

/-- The axis stripped value vector has norm one at zero. -/
theorem axisRestriction_stripped_vecNorm_zero
    {m N : ℕ} {lambda : ℝ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)) :
    vecNorm (fun i : Fin N => (F i).eval 0) = 1 :=
  vecNorm_eq_one_of_vecSqNorm_eq_one (axisRestriction_stripped_vecSqNorm_zero hNorm)

/-- The diagonal stripped value vector has norm one at zero. -/
theorem diagonalRestriction_stripped_vecNorm_zero
    {m N : ℕ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)) :
    vecNorm (fun i : Fin N => (F i).eval 0) = 1 :=
  vecNorm_eq_one_of_vecSqNorm_eq_one (diagonalRestriction_stripped_vecSqNorm_zero hNorm)

/-- The axis stripped value vector is orthogonal to its derivative vector at zero. -/
theorem axisRestriction_stripped_vecDot_derivative_zero
    {m N : ℕ} {lambda : ℝ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)) :
    vecDot (fun i : Fin N => (F i).eval 0)
      (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) = 0 := by
  have hder := congrArg (fun p : Polynomial ℝ => (Polynomial.derivative p).eval 0) hNorm
  change (Polynomial.derivative (∑ i : Fin N, (F i) ^ 2)).eval 0 =
    (Polynomial.derivative ((1 + Polynomial.X ^ 2) ^ m *
      (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2))).eval 0 at hder
  rw [sum_sq_derivative_eval_zero] at hder
  have hrhs : (Polynomial.derivative ((1 + Polynomial.X ^ 2) ^ m *
      (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2))).eval 0 = 0 := by
    simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
  rw [hrhs] at hder
  linarith

/-- The diagonal stripped value vector is orthogonal to its derivative vector at zero. -/
theorem diagonalRestriction_stripped_vecDot_derivative_zero
    {m N : ℕ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 = ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)) :
    vecDot (fun i : Fin N => (F i).eval 0)
      (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) = 0 := by
  have hder := congrArg (fun p : Polynomial ℝ => (Polynomial.derivative p).eval 0) hNorm
  change (Polynomial.derivative (∑ i : Fin N, (F i) ^ 2)).eval 0 =
    (Polynomial.derivative
      (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1))).eval 0 at hder
  rw [sum_sq_derivative_eval_zero] at hder
  have hrhs :
      (Polynomial.derivative
        (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1))).eval 0 = 0 := by
    simp [Polynomial.derivative_pow]
  rw [hrhs] at hder
  linarith

/-- Stripping a normalized quadratic factor preserves the first-derivative vector norm at
zero, up to the harmless global sign. -/
theorem normalizedQuadraticFactor_derivative_vecNorm_eq
    {N : ℕ} (a : ℝ) (F : Fin N → Polynomial ℝ) :
    vecNorm (fun i : Fin N =>
      (Polynomial.derivative ((Polynomial.C a * Polynomial.X ^ 2 - 1) * F i)).eval 0) =
    vecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) := by
  rw [show (fun i : Fin N =>
      (Polynomial.derivative ((Polynomial.C a * Polynomial.X ^ 2 - 1) * F i)).eval 0) =
      fun i : Fin N => - (Polynomial.derivative (F i)).eval 0 by
        funext i
        exact normalizedQuadraticFactor_mul_derivative_eval_zero a (F i)]
  exact vecNorm_neg _

/-- After stripping the normalized axis quadratic factor, the remaining axis
square-root vector has the expected norm polynomial. -/
theorem axisRestriction_stripped_norm_identity
    {m N : ℕ} {lambda : ℝ} {F : Fin N → Polynomial ℝ}
    (hF : axisRestrict3To1 (Pmlambda m lambda) =
      ∑ i : Fin N,
        ((Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1) * F i) ^ 2) :
    ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2) := by
  let A : Polynomial ℝ := Polynomial.C (lambda - 1) * Polynomial.X ^ 2 - 1
  let T : Polynomial ℝ := (1 + Polynomial.X ^ 2) ^ m *
    (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)
  have hA_ne : A ^ 2 ≠ 0 := by
    have hA : A ≠ 0 := by
      intro hzero
      have heval := congrArg (fun p : Polynomial ℝ => p.eval 0) hzero
      norm_num [A] at heval
    exact pow_ne_zero 2 hA
  have hsum : ∑ i : Fin N, (A * F i) ^ 2 = A ^ 2 * ∑ i : Fin N, (F i) ^ 2 := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
  have haxis : axisRestrict3To1 (Pmlambda m lambda) = A ^ 2 * T := by
    rw [axisRestrict3To1_Pmlambda]
    simp [A, T]
    ring
  have hmain : A ^ 2 * (∑ i : Fin N, (F i) ^ 2) = A ^ 2 * T := by
    rw [← hsum, ← haxis]
    exact hF.symm
  exact Polynomial.mul_left_cancel_of_ne_zero hA_ne hmain

/-- After stripping the normalized diagonal quadratic factor, the remaining diagonal
square-root vector has the expected norm polynomial. -/
theorem diagonalRestriction_stripped_norm_identity
    {m N : ℕ} {lambda : ℝ} {F : Fin N → Polynomial ℝ}
    (hF : diagonalRestrict3To1 (Pmlambda m lambda) =
      ∑ i : Fin N,
        ((Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1) * F i) ^ 2) :
    ∑ i : Fin N, (F i) ^ 2 = (1 + Polynomial.X ^ 2) ^ (m + 1) := by
  let A : Polynomial ℝ := Polynomial.C ((lambda - 2) / 2) * Polynomial.X ^ 2 - 1
  let T : Polynomial ℝ := (1 + Polynomial.X ^ 2) ^ (m + 1)
  have hA_ne : A ^ 2 ≠ 0 := by
    have hA : A ≠ 0 := by
      intro hzero
      have heval := congrArg (fun p : Polynomial ℝ => p.eval 0) hzero
      norm_num [A] at heval
    exact pow_ne_zero 2 hA
  have hsum : ∑ i : Fin N, (A * F i) ^ 2 = A ^ 2 * ∑ i : Fin N, (F i) ^ 2 := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
  have hdiag : diagonalRestrict3To1 (Pmlambda m lambda) = A ^ 2 * T := by
    simpa [A, T] using diagonalRestrict3To1_Pmlambda m lambda
  have hmain : A ^ 2 * (∑ i : Fin N, (F i) ^ 2) = A ^ 2 * T := by
    rw [← hsum, ← hdiag]
    exact hF.symm
  exact Polynomial.mul_left_cancel_of_ne_zero hA_ne hmain

/-- Pointwise squared-norm identity for an axis stripped square-root vector. -/
theorem axisRestriction_stripped_vecSqNorm_eval
    {m N : ℕ} {lambda : ℝ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2))
    (t : ℝ) :
    vecSqNorm (fun i : Fin N => (F i).eval t) =
      (1 + t ^ 2) ^ m * (1 + (lambda + 1) * t ^ 2) := by
  have h := sosUni_eval_eq_vecSqNorm hNorm.symm t
  simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X, Polynomial.eval_C] using h.symm

/-- Pointwise squared-norm identity for a diagonal stripped square-root vector. -/
theorem diagonalRestriction_stripped_vecSqNorm_eval
    {m N : ℕ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 = (1 + Polynomial.X ^ 2) ^ (m + 1))
    (t : ℝ) :
    vecSqNorm (fun i : Fin N => (F i).eval t) = (1 + t ^ 2) ^ (m + 1) := by
  have h := sosUni_eval_eq_vecSqNorm hNorm.symm t
  simpa [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
    using h.symm

/-- Axis stripped norm identities contain the spectral factor at
`sqrt (lambda + 1)`, hence the complexified value vectors at the two imaginary
roots are Hermitian-orthogonal. -/
theorem axisRestriction_stripped_complexHermitian_orthogonal
    {m N : ℕ} {lambda : ℝ} {F : Fin N → Polynomial ℝ}
    (hLam : 0 < lambda + 1)
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)) :
    complexVecHermitianEval
        (fun i : Fin N =>
          (complexifyPoly (F i)).eval (-Complex.I / (Real.sqrt (lambda + 1) : ℂ)))
        (fun i : Fin N =>
          (complexifyPoly (F i)).eval (Complex.I / (Real.sqrt (lambda + 1) : ℂ))) = 0 := by
  have hsqrt_sq : Real.sqrt (lambda + 1) ^ 2 = lambda + 1 :=
    Real.sq_sqrt (le_of_lt hLam)
  have hsqrt_ne : Real.sqrt (lambda + 1) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hLam)
  have hNorm' : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.C (Real.sqrt (lambda + 1) ^ 2) * Polynomial.X ^ 2) *
        ((1 + Polynomial.X ^ 2) ^ m) := by
    rw [hNorm, hsqrt_sq]
    ring
  exact complexHermitian_orthogonal_of_real_spectral_factor
    (F := F) (a := Real.sqrt (lambda + 1)) hsqrt_ne hNorm'

/-- Diagonal stripped norm identities contain the spectral factor `1 + t^2`, hence
the complexified value vectors at `±i` are Hermitian-orthogonal. -/
theorem diagonalRestriction_stripped_complexHermitian_orthogonal
    {m N : ℕ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 = ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)) :
    complexVecHermitianEval
        (fun i : Fin N => (complexifyPoly (F i)).eval (-Complex.I / (1 : ℂ)))
        (fun i : Fin N => (complexifyPoly (F i)).eval (Complex.I / (1 : ℂ))) = 0 := by
  have hone_ne : (1 : ℝ) ≠ 0 := by norm_num
  have hNorm' : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.C ((1 : ℝ) ^ 2) * Polynomial.X ^ 2) *
        ((1 + Polynomial.X ^ 2) ^ m) := by
    rw [hNorm]
    simp
    ring
  exact complexHermitian_orthogonal_of_real_spectral_factor
    (F := F) (a := (1 : ℝ)) hone_ne hNorm'

end ScaledRobinson
end OptimalConvergenceRates

end
