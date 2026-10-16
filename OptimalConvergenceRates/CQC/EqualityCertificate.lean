import OptimalConvergenceRates.CQC.EqualityEmbedding
import OptimalConvergenceRates.CQC.ModulePullback

/-!
# Positivity and equality-remainder certificates

The determinant for the selected squared-slack family remains positive on the
original feasible set. The linear equality-slack penalty descends to a fixed
sum of equality representatives; its negative is already in the original
quadratic module because every representative has an opposite generator.
-/

noncomputable section

open MvPolynomial Finset Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

open GeneralArchimedean

variable {n m : ℕ}

/-- The determinant multiplier of the selected family is strictly positive on
the feasible set under equality-aware CQC. -/
theorem selectedDeterminantMultiplier_posOn
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcqc : CQCWithEqualities g) :
    ∀ x ∈ KrivineStengle.basicClosedSet g,
      0 < MvPolynomial.eval x
        (determinantMultiplier (selectedGenerator g)) := by
  intro x hx
  let z := equalitySlackLift g x
  have hz : z ∈ equalitySlackZeroSet g :=
    equalitySlackLift_mem_equalitySlackZeroSet hx
  have hcore : z ∈ slackZeroSet (selectedGenerator g) :=
    mem_selected_slackZeroSet_of_mem_equalitySlackZeroSet hz
  rw [eval_determinantMultiplier]
  have heq :
      cqcGramAt (selectedGenerator g) x =
        slackGramAt (selectedGenerator g) z := by
    simpa [z] using cqcGramAt_eq_slackGramAt hcore
  rw [heq]
  have hinj := slackJacobianAt_vecMul_injective
    (selectedSlackGradients_linearIndependent hcqc hz)
  have hpos : (slackGramAt (selectedGenerator g) z).PosDef := by
    simpa [slackGramAt] using
      Matrix.PosDef.mul_conjTranspose_self
        (slackJacobianAt (selectedGenerator g) z) hinj
  exact hpos.det_pos


@[simp]
theorem eval_equalityRepresentativeSum_eq_zero
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {x : Fin n → ℝ} (hx : x ∈ KrivineStengle.basicClosedSet g) :
    MvPolynomial.eval x (equalityRepresentativeSum g) = 0 := by
  classical
  simp only [equalityRepresentativeSum, MvPolynomial.eval_sum]
  apply Finset.sum_eq_zero
  intro e _
  have henc := selectedEqualityIndex_encodes g e
  change HasOppositeConstraint g
    (selectedRawIndex g (selectedEqualityIndex g e)) at henc
  simpa [selectedGenerator] using
    (eval_eq_zero_of_hasOppositeConstraint hx henc)

/-- The negative constant multiple of an equality representative is certified
by the opposite raw generator. -/
theorem neg_C_mul_selectedEquality_quadraticModuleMem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {M : ℝ} (hM : 0 ≤ M)
    (e : Fin (selectedEqualityCount g)) :
    QuadraticModuleMem g
      (-(C M * selectedGenerator g (selectedEqualityIndex g e))) := by
  have henc := selectedEqualityIndex_encodes g e
  change HasOppositeConstraint g
    (selectedRawIndex g (selectedEqualityIndex g e)) at henc
  obtain ⟨j, _hne, hj⟩ := henc
  refine ⟨(C M * g j).totalDegree, ?_⟩
  have hcert := genQuadraticModule_sos_mul_generator
    g j (C M) (IsSOS_C_nonneg M hM)
  convert hcert using 1
  simp only [selectedGenerator]
  rw [hj]
  ring

/-- At some fixed order, the original quadratic module contains the negative
of the full descended equality remainder. -/
theorem exists_order_neg_equalityRepresentativeSum
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ s, -(C M * equalityRepresentativeSum g) ∈
      GenQuadraticModule g s := by
  have hterm :
      ∀ e : Fin (selectedEqualityCount g),
        QuadraticModuleMem g
          (-(C M * selectedGenerator g (selectedEqualityIndex g e))) :=
    neg_C_mul_selectedEquality_quadraticModuleMem hM
  obtain ⟨s, hs⟩ := exists_common_quadraticModule_order hterm
  refine ⟨s, ?_⟩
  have hsum := genQuadraticModule_sum Finset.univ
    (fun e : Fin (selectedEqualityCount g) ↦
      -(C M * selectedGenerator g (selectedEqualityIndex g e)))
    (fun e _ ↦ hs e)
  convert hsum using 1
  simp [equalityRepresentativeSum, Finset.mul_sum]

end CQCInternal
end OptimalConvergenceRates

end
