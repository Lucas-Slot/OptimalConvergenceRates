/-
# Headline conclusions for the MFCQ quadratic example

This file is deliberately only the readable public statement layer.  All
proofs and certificate calculations live in the supporting files.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.MainResultsProofs

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

/-- The module is Archimedean and `t` has the origin as its unique feasible
global minimizer, with minimum value zero. -/
theorem archimedean_and_unique_minimum :
    GeneralArchimedean.IsArchimedean generators ∧
      origin ∈ feasibleSet ∧
      eval origin objective = 0 ∧
      ∀ z ∈ feasibleSet, 0 ≤ eval z objective ∧
        (eval z objective = 0 → z = origin) :=
  archimedean_and_unique_minimum_proof

/-- MFCQ holds everywhere, although CQC/LICQ fails at the unique minimizer
and holds at every other feasible point. -/
theorem qualification_properties :
    (∀ z ∈ feasibleSet, MFCQAt generators z) ∧
      ¬ CQCAt generators origin ∧
      ∀ z ∈ feasibleSet, z ≠ origin → CQCAt generators z :=
  qualification_properties_proof

/-- The example has a global linear Euclidean feasibility error bound. -/
theorem global_linear_error_bound (z : Fin 3 → ℝ) :
    euclideanDistanceToSet z feasibleSet ≤ 3 * violation z :=
  global_linear_error_bound_proof z

/-- The linear exponent is sharp: at `(0,0,-h)`, both distance to the
feasible set and constraint violation are exactly `h`. -/
theorem linear_error_exponent_witness
    (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    violation (negativeAxisPoint h) = h ∧
      euclideanDistanceToSet (negativeAxisPoint h) feasibleSet = h :=
  linear_error_exponent_witness_proof h h0 h1

/-- **Headline SOS obstruction.**  With the paper's convention that order
`r` means complete certificate degree at most `2r`, every certificate for
`t + ε` forces the sharp quadratic-scale lower bound shown below. -/
theorem certificate_lower_bound
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ)
    (hcertificate : objective + C ε ∈
      GenQuadraticModule generators (2 * r)) :
    (1 : ℝ) / (2 ^ 14 * (r : ℝ) ^ 2) < ε :=
  certificate_lower_bound_proof r hr ε hcertificate

/-- Inverse form of the quadratic obstruction: a certificate for `t + ε`
must have order larger than a fixed multiple of `ε⁻¹ᐟ²`. -/
theorem certificate_order_lower_bound
    (r : ℕ) (hr : 1 ≤ r) (ε : ℝ) (hε : 0 < ε)
    (hcertificate : objective + C ε ∈
      GenQuadraticModule generators (2 * r)) :
    (1 : ℝ) / (128 * Real.sqrt ε) < (r : ℝ) :=
  certificate_order_lower_bound_proof r hr ε hε hcertificate

/-- Consequently the hierarchy error is bounded below by `2⁻¹⁴ r⁻²`. -/
theorem hierarchy_error_lower_bound (r : ℕ) (hr : 1 ≤ r) :
    (1 : ℝ) / (2 ^ 14 * (r : ℝ) ^ 2) ≤ hierarchyError r :=
  hierarchy_error_lower_bound_proof r hr

/-- In particular the exact objective does not belong to the untruncated
quadratic module. -/
theorem objective_not_in_quadraticModule :
    ¬ GeneralArchimedean.QuadraticModuleMem generators objective :=
  objective_not_in_quadraticModule_proof

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
