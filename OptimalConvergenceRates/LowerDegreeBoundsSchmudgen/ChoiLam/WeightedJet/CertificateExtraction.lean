/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/WeightedJet/CertificateExtraction.lean

  Extraction of degree-bounded SOS-vector witnesses from Choi-Lam box-preordering certificates.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.SOSJets
import OptimalConvergenceRates.BasicNotions.SOS
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-- A Schmuedgen generator product is nonzero because it evaluates to `1` at the origin. -/
lemma BoxSemialgebraicGeneratorProd_ne_zero_n4 (J : Finset (Fin 4)) :
    (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ) ≠ 0 := by
  intro hzero
  have heval :
      MvPolynomial.eval 0 (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ) = 0 := by
    rw [hzero, map_zero]
  have hone :
      MvPolynomial.eval 0 (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ) = 1 := by
    unfold BoxSemialgebraicGeneratorProd
    rw [map_prod]
    apply Finset.prod_eq_one
    intro i _hi
    rw [BoxSemialgebraicGenerator_eval]
    simp
  linarith

/-- Degree control for SOS witnesses extracted from a bounded preordering certificate.

The no-cancellation theorem `sos_summand_totalDegree_le_of_sum_sq_totalDegree`
controls the square roots. Multiplication by a nonzero generator product cannot lower
total degree over `ℝ`. -/
theorem box_preordering_sos_witness_degree_bound
    {r : ℕ} {σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ}
    (hsos : ∀ J, IsSOS (σ J))
    (hdeg : ∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) :
    ∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 4) ℝ),
      σ J = sosVectorSq4 Q ∧ ∀ i, (Q i).totalDegree ≤ r := by
  intro J
  by_cases hσzero : σ J = 0
  · refine ⟨0, (fun i : Fin 0 => Fin.elim0 i), ?_, ?_⟩
    · simp [hσzero, sosVectorSq4]
    · intro i
      exact Fin.elim0 i
  · obtain ⟨N, Q, hQ⟩ := hsos J
    refine ⟨N, Q, hQ, ?_⟩
    have hg : (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ) ≠ 0 :=
      BoxSemialgebraicGeneratorProd_ne_zero_n4 J
    have hmul := MvPolynomial.totalDegree_mul_of_isDomain hσzero hg
    have hσdeg : (σ J).totalDegree ≤ r := by
      have hj := hdeg J
      omega
    have hσdeg2 : (σ J).totalDegree ≤ 2 * r := by
      omega
    intro i
    exact sos_summand_totalDegree_le_of_sum_sq_totalDegree (by simpa [sosVectorSq4] using hQ)
      hσdeg2 i

/-- Certificate-level extraction of SOS vectors with both local control and degree control.

This combines the local estimates from `SOSJets.lean` with the separate SOS witness
degree bridge above. -/
theorem box_preordering_certificate_sos_vectors_local_control_with_degree
    {epsilon : ℝ} {r : ℕ} (heps : 0 ≤ epsilon)
    (hcert : choiLamQuartic + MvPolynomial.C epsilon ∈ BoxPreordering 4 r) :
    ∃ (σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ),
      (∀ J, ∃ (N : ℕ) (Q : Fin N → MvPolynomial (Fin 4) ℝ),
        σ J = sosVectorSq4 Q ∧
        (∀ i, (Q i).totalDegree ≤ r) ∧
        (∀ x, boxSmall x →
          interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i)) ≤
            schmInteriorLocalControlConst * (Real.sqrt epsilon + localSqNorm x)) ∧
        (∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
          interiorVecNorm
              (fun i : Fin N =>
                MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i)) ≤
            schmInteriorLocalControlConst * Real.sqrt epsilon)) ∧
      (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
      choiLamQuartic + MvPolynomial.C epsilon =
        ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J := by
  obtain ⟨σ, hsos, hdeg, hsum⟩ := hcert
  refine ⟨σ, ?_, hdeg, hsum⟩
  have hQdeg := box_preordering_sos_witness_degree_bound hsos hdeg
  intro J
  obtain ⟨N, Q, hQ, hQdegJ⟩ := hQdeg J
  refine ⟨N, Q, hQ, hQdegJ, ?_, ?_⟩
  · intro x hx
    exact box_preordering_sos_vector_local_control_by_norm heps hsos hsum J Q hQ x hx
  · intro zi t ht
    exact box_preordering_sos_vector_zero_line_control heps hsos hsum J Q hQ zi t ht

end OptimalConvergenceRates
