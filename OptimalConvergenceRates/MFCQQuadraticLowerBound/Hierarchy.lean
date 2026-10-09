/-
  Consequences of the certificate obstruction for the hierarchy error and
  the full quadratic module.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.LowerBound

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

/-- The elementary order-one certificate from the note:
`t + 1 = ((t+1)^2 + u^2 + v^2 + ball) / 2`. -/
theorem objective_add_one_mem :
    objective + C 1 ∈ GenQuadraticModule generators 2 := by
  let sigmaZero : MvPolynomial (Fin 3) ℝ :=
    C (1 / 2) * (t + C 1) ^ 2 +
      C (1 / 2) * u ^ 2 + C (1 / 2) * v ^ 2
  have hsos : IsSOS sigmaZero := by
    dsimp [sigmaZero]
    exact IsSOS_add
      (IsSOS_add
        (IsSOS_nonneg_scale (IsSOS_sq (t + C 1)) (1 / 2) (by norm_num))
        (IsSOS_nonneg_scale (IsSOS_sq u) (1 / 2) (by norm_num)))
      (IsSOS_nonneg_scale (IsSOS_sq v) (1 / 2) (by norm_num))
  have hlinear : (t + C 1).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) (by simp))
  have hsquare : ((t + C 1) ^ 2).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_pow _ _).trans (by omega)
  have hscaledSquare : (C (1 / 2) * (t + C 1) ^ 2).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hsquare)
  have hscaledU : (C (1 / 2) * u ^ 2).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_mul _ _).trans
      (by simp [u, MvPolynomial.totalDegree_X_pow])
  have hscaledV : (C (1 / 2) * v ^ 2).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_mul _ _).trans
      (by simp [v, MvPolynomial.totalDegree_X_pow])
  have hsigmaDegree : sigmaZero.totalDegree ≤ 2 := by
    dsimp [sigmaZero]
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le
        ((MvPolynomial.totalDegree_add _ _).trans
          (max_le hscaledSquare hscaledU))
        hscaledV)
  have hfree := genQuadraticModule_sos generators hsos hsigmaDegree
  have hballDegree : (generators 4).totalDegree ≤ 2 := by
    change ball.totalDegree ≤ 2
    unfold ball
    repeat first
      | apply le_trans (MvPolynomial.totalDegree_sub _ _)
      | apply max_le
    all_goals simp [u, v, t, MvPolynomial.totalDegree_X_pow]
  have hball : C (1 / 2) * generators 4 ∈ GenQuadraticModule generators 2 :=
    GenQuadraticModule_nonneg_scale (1 / 2) (by norm_num)
      (GenQuadraticModule_mono hballDegree
        (genQuadraticModule_generator generators 4))
  have hsum := GenQuadraticModule_add hfree hball
  convert hsum using 1
  change objective + C 1 = sigmaZero + C (1 / 2) * ball
  dsimp [sigmaZero, objective, ball, u, v, t]
  ring_nf
  change 1 + X 2 = X 2 * C (1 / 2) * C 2 + C (1 / 2) * C 2
  rw [mul_assoc, ← map_mul]
  norm_num
  ring

/-- Every paper-order `r ≥ 1` level admits at least one nonnegative
perturbation of the objective. -/
theorem hierarchyError_set_nonempty (r : ℕ) (hr : 1 ≤ r) :
    {ε : ℝ | 0 ≤ ε ∧
      objective + C ε ∈ GenQuadraticModule generators (2 * r)}.Nonempty := by
  refine ⟨1, by norm_num, ?_⟩
  exact GenQuadraticModule_mono (by omega) objective_add_one_mem

/-- The hierarchy error inherits the certificate-level quadratic lower
bound. -/
theorem hierarchy_error_lower_bound_proof (r : ℕ) (hr : 1 ≤ r) :
    (1 : ℝ) / (2 ^ 14 * (r : ℝ) ^ 2) ≤ hierarchyError r := by
  unfold hierarchyError
  apply le_csInf (hierarchyError_set_nonempty r hr)
  intro epsilon hepsilon
  exact (certificate_lower_bound_proof r hr epsilon hepsilon.2).le

/-- The exact objective is excluded from the untruncated quadratic module. -/
theorem objective_not_in_quadraticModule_proof :
    ¬ GeneralArchimedean.QuadraticModuleMem generators objective := by
  rintro ⟨degree, hdegree⟩
  let r := max 1 degree
  have hr : 1 ≤ r := Nat.le_max_left _ _
  have hcertificate : objective + C (0 : ℝ) ∈
      GenQuadraticModule generators (2 * r) := by
    simpa using GenQuadraticModule_mono
      (show degree ≤ 2 * r by omega) hdegree
  have hpositive := certificate_lower_bound_proof r hr 0 hcertificate
  have hrReal : (0 : ℝ) < r := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have : (0 : ℝ) < 1 / (2 ^ 14 * (r : ℝ) ^ 2) := by positivity
  linarith

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
