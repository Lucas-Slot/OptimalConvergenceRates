/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/Motzkin/CertificateExtraction.lean

  Degree-controlled SOS witnesses for ternary box-preordering certificates.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.Defs
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

/-- A ternary box generator product is nonzero, as witnessed at the origin. -/
lemma boxSemialgebraicGeneratorProd_ne_zero_n3 (J : Finset (Fin 3)) :
    (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 3) ℝ) ≠ 0 := by
  intro hzero
  have heval :
      eval 0 (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 3) ℝ) = 0 := by
    rw [hzero, map_zero]
  have hone :
      eval 0 (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 3) ℝ) = 1 := by
    unfold BoxSemialgebraicGeneratorProd
    rw [map_prod]
    apply Finset.prod_eq_one
    intro i _hi
    rw [BoxSemialgebraicGenerator_eval]
    simp
  linarith

/-- Extract degree-controlled square roots from all multipliers in a ternary
box-preordering certificate. -/
theorem boxPreorderingSOSWitnessDegreeBound_n3
    {r : ℕ} {sigma : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ}
    (hsos : ∀ J, IsSOS (sigma J))
    (hdeg : ∀ J, (sigma J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) :
    ∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 3) ℝ),
      sigma J = ∑ i : Fin N, (Q i) ^ 2 ∧ ∀ i, (Q i).totalDegree ≤ r := by
  intro J
  by_cases hsigma : sigma J = 0
  · refine ⟨0, Fin.elim0, ?_, ?_⟩
    · simp [hsigma]
    · intro i
      exact Fin.elim0 i
  · obtain ⟨N, Q, hQ⟩ := hsos J
    refine ⟨N, Q, hQ, ?_⟩
    have hmul := MvPolynomial.totalDegree_mul_of_isDomain hsigma
      (boxSemialgebraicGeneratorProd_ne_zero_n3 J)
    have hsigmaDeg : (sigma J).totalDegree ≤ r := by
      have hweighted := hdeg J
      omega
    have hsigmaDegTwo : (sigma J).totalDegree ≤ 2 * r := by omega
    exact sos_summand_totalDegree_le_of_sum_sq_totalDegree hQ hsigmaDegTwo

/-- Expand a ternary box-preordering certificate into degree-controlled SOS vectors. -/
theorem boxPreorderingCertificateSOSVectors_n3
    {p : MvPolynomial (Fin 3) ℝ} {r : ℕ} (hcert : p ∈ BoxPreordering 3 r) :
    ∃ (sigma : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 3) ℝ),
        sigma J = ∑ i : Fin N, (Q i) ^ 2 ∧ ∀ i, (Q i).totalDegree ≤ r) ∧
      (∀ J, (sigma J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      p = ∑ J ∈ Finset.univ.powerset,
        sigma J * BoxSemialgebraicGeneratorProd J := by
  obtain ⟨sigma, hsos, hdeg, hsum⟩ := hcert
  exact ⟨sigma, boxPreorderingSOSWitnessDegreeBound_n3 hsos hdeg, hdeg, hsum⟩

end Motzkin

end OptimalConvergenceRates

end
