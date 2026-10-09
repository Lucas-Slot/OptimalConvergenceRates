/- Positive coefficient distance from the Motzkin sextic to cubic SOS forms. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.CubicNormalForm

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

private def motzkinSosDistanceSet : Set ℝ :=
  {d | ∃ S : MvPolynomial (Fin 3) ℝ,
    Nonempty (DegreeBoundedSOS S 3) ∧ d = coeffL1Distance motzkinSextic S}

private theorem motzkinSosDistanceSet_nonempty : motzkinSosDistanceSet.Nonempty := by
  refine ⟨coeffL1Distance motzkinSextic 0, 0, ?_, rfl⟩
  exact ⟨zeroDegreeBoundedSOS 3 3⟩

private theorem motzkinSosDistanceSet_bddBelow : BddBelow motzkinSosDistanceSet := by
  refine ⟨0, ?_⟩
  rintro d ⟨S, _hS, rfl⟩
  exact coeffL1Distance_nonneg motzkinSextic S

theorem motzkinSosDistance_nonneg : 0 ≤ motzkinSosDistance := by
  unfold motzkinSosDistance
  exact le_csInf motzkinSosDistanceSet_nonempty (by
    rintro d ⟨S, _hS, rfl⟩
    exact coeffL1Distance_nonneg motzkinSextic S)

theorem motzkinSosDistance_pos : 0 < motzkinSosDistance := by
  by_contra hnot
  have hzero : motzkinSosDistance = 0 :=
    le_antisymm (le_of_not_gt hnot) motzkinSosDistance_nonneg
  have hclosed : Nonempty (DegreeBoundedSOS motzkinSextic 3) := by
    apply degreeBoundedSOSCone_closed_coeffL1 motzkinSextic_totalDegree_le_six
    simpa [motzkinSosDistance, motzkinSosDistanceSet] using hzero
  exact motzkinSextic_not_sos hclosed.some.toIsSOS

theorem motzkinSosDistance_le {S : MvPolynomial (Fin 3) ℝ}
    (hS : Nonempty (DegreeBoundedSOS S 3)) :
    motzkinSosDistance ≤ coeffL1Distance motzkinSextic S := by
  unfold motzkinSosDistance
  exact csInf_le motzkinSosDistanceSet_bddBelow ⟨S, hS, rfl⟩

end Motzkin

end OptimalConvergenceRates

end
