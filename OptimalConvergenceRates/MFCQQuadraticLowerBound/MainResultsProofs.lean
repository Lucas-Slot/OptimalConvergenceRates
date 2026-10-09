/-
  Assembly of the proved ingredients used by the statement-only public
  interface in `MainResults.lean`.
-/
import OptimalConvergenceRates.MFCQQuadraticLowerBound.OffOriginCQC
import OptimalConvergenceRates.MFCQQuadraticLowerBound.ErrorBound
import OptimalConvergenceRates.MFCQQuadraticLowerBound.LocalExponent
import OptimalConvergenceRates.MFCQQuadraticLowerBound.Hierarchy

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.MFCQQuadraticLowerBound

/-- The three constraint-qualification conclusions, assembled from their
separate geometric proofs. -/
theorem qualification_properties_proof :
    (∀ z ∈ feasibleSet, MFCQAt generators z) ∧
      ¬ CQCAt generators origin ∧
      ∀ z ∈ feasibleSet, z ≠ origin → CQCAt generators z := by
  exact ⟨mfcq_everywhere, cqc_fails_at_origin,
    fun _ hz hne ↦ cqc_off_origin hz hne⟩

/-- Algebraic inversion of the quadratic certificate obstruction. -/
theorem certificate_order_lower_bound_proof
    (r : ℕ) (hr : 1 ≤ r) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hcertificate : objective + C epsilon ∈
      GenQuadraticModule generators (2 * r)) :
    (1 : ℝ) / (128 * Real.sqrt epsilon) < (r : ℝ) := by
  have hlower := certificate_lower_bound_proof r hr epsilon hcertificate
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hsqrt : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon
  have hdenom : 0 < (2 : ℝ) ^ 14 * (r : ℝ) ^ 2 := by positivity
  have hscaled : (1 : ℝ) < epsilon * ((2 : ℝ) ^ 14 * (r : ℝ) ^ 2) :=
    (div_lt_iff₀ hdenom).mp hlower
  have hsqrtSq : (Real.sqrt epsilon) ^ 2 = epsilon :=
    Real.sq_sqrt hepsilon.le
  have hproduct : (1 : ℝ) < 128 * Real.sqrt epsilon * (r : ℝ) := by
    have hnonneg : 0 ≤ 128 * Real.sqrt epsilon * (r : ℝ) := by positivity
    nlinarith
  apply (div_lt_iff₀ (mul_pos (by norm_num) hsqrt)).2
  nlinarith

end OptimalConvergenceRates.MFCQQuadraticLowerBound

end
