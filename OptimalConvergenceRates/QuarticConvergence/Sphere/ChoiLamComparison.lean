/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/ChoiLamComparison.lean

  Compatibility of constant sphere perturbations with the existing Choi-Lam API.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.QuarticRate
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.SphereBallTransfers.MainResults

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- The Choi-Lam perturbation by `epsilon * sphereRho^2` differs from the constant
perturbation by a multiple of the unit-sphere relation. -/
theorem sphereChoiLamPerturbed_eq_const_add_relation (epsilon : ℝ) :
    sphereChoiLamPerturbed epsilon =
      choiLamSphereQuartic + MvPolynomial.C epsilon +
        sphereRelation 5 * (MvPolynomial.C epsilon * (sphereRho + 1)) := by
  unfold sphereChoiLamPerturbed
  rw [← sphereRhoRelation_eq_sphereRelation]
  unfold sphereRhoRelation
  ring

/-- Constant perturbations use exactly the same sphere SOS predicate as the existing
Choi-Lam results. -/
theorem sphereSOSMod_const_choiLam_iff (r : ℕ) (epsilon : ℝ) :
    SphereSOSMod (choiLamSphereQuartic + MvPolynomial.C epsilon) r ↔
      ChoiLamHasSphereCert r epsilon := by
  rw [ChoiLamHasSphereCert, sphereChoiLamPerturbed_eq_const_add_relation]
  exact (sphereSOSMod_add_relation_mul_iff
    (choiLamSphereQuartic + MvPolynomial.C epsilon)
    (MvPolynomial.C epsilon * (sphereRho + 1))).symm

/-- Embed a normalized Choi-Lam zero direction into the five-dimensional sphere by
setting the final coordinate to zero. -/
def choiLamSphereZeroDirection (i : Fin 4) : Fin 5 → ℝ :=
  Fin.lastCases 0 (choiLamZeroDirection i)

@[simp] theorem choiLamSphereZeroDirection_castSucc (i j : Fin 4) :
    choiLamSphereZeroDirection i j.castSucc = choiLamZeroDirection i j := by
  simp [choiLamSphereZeroDirection]

@[simp] theorem choiLamSphereZeroDirection_last (i : Fin 4) :
    choiLamSphereZeroDirection i (Fin.last 4) = 0 := by
  change Fin.lastCases (0 : ℝ) (choiLamZeroDirection i) (Fin.last 4) = (0 : ℝ)
  exact Fin.lastCases_last

/-- The embedded Choi-Lam zero directions lie on the unit sphere. -/
theorem choiLamSphereZeroDirection_mem (i : Fin 4) :
    choiLamSphereZeroDirection i ∈ sphereSet 5 := by
  unfold sphereSet sphereQuadratic
  simp only [Set.mem_setOf_eq, map_sum, map_pow, eval_X]
  rw [Fin.sum_univ_castSucc]
  rw [choiLamSphereZeroDirection_last,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
  change interiorVecSqNorm (choiLamZeroDirection i) = 1
  exact choiLamZeroDirection_sqNorm i

/-- The lifted Choi-Lam quartic vanishes at each embedded zero direction. -/
theorem choiLamSphereQuartic_zero_on_direction (i : Fin 4) :
    MvPolynomial.eval (choiLamSphereZeroDirection i) choiLamSphereQuartic = 0 := by
  unfold choiLamSphereQuartic
  rw [MvPolynomial.eval_rename]
  have hcomp :
      choiLamSphereZeroDirection i ∘ xIndexInSphere =
        choiLamZeroDirection i := by
    funext j
    exact choiLamSphereZeroDirection_castSucc i j
  rw [hcomp]
  exact choiLamQuartic_zero_on_direction i

/-- The lifted Choi-Lam quartic is nonnegative on the five-dimensional unit sphere. -/
theorem choiLamSphereQuartic_nonnegative :
    SphereNonnegative choiLamSphereQuartic := by
  intro x hx
  unfold choiLamSphereQuartic
  rw [MvPolynomial.eval_rename]
  exact choiLamQuartic_nonneg_global _

/-- The true sphere minimum of the lifted Choi-Lam quartic is exactly zero. -/
@[simp] theorem spherePolyMin_choiLamSphereQuartic :
    spherePolyMin choiLamSphereQuartic = 0 := by
  have hnonneg : 0 ≤ spherePolyMin choiLamSphereQuartic :=
    (sphereNonnegative_iff_min_nonnegative (by omega) _).mp
      choiLamSphereQuartic_nonnegative
  have hle := spherePolyMin_le_eval choiLamSphereQuartic
    (choiLamSphereZeroDirection 0) (choiLamSphereZeroDirection_mem 0)
  rw [choiLamSphereQuartic_zero_on_direction] at hle
  exact le_antisymm hle hnonneg

/-- Any proof of the uniform quartic certificate theorem specializes directly to the
lifted Choi-Lam quartic, with no translation between certificate notions. -/
theorem quarticSphereCertificateOfNonnegStatement_choiLam
    (hmain : QuarticSphereCertificateOfNonnegStatement 5) :
    ∃ (A : ℝ) (c : ℕ),
      0 < A ∧ 0 < c ∧
      ∀ r : ℕ, c * 4 ≤ r →
        SphereSOSMod
          (choiLamSphereQuartic +
            MvPolynomial.C
              (A * sphereC6Norm choiLamSphereQuartic / (r : ℝ) ^ 4))
          r := by
  obtain ⟨A, c, hA, hc, hcert⟩ := hmain
  refine ⟨A, c, hA, hc, ?_⟩
  intro r hr
  apply hcert choiLamSphereQuartic 4 r
  · unfold choiLamSphereQuartic
    exact (MvPolynomial.totalDegree_rename_le xIndexInSphere choiLamQuartic).trans
      choiLamQuartic_totalDegree_le_four
  · exact choiLamSphereQuartic_nonnegative
  · simpa using hr

/-- The existing Choi-Lam upper bound, restated directly for the constant perturbation
used by the quartic convergence theorem. -/
theorem sphereSOSMod_const_choiLam_upperBound_rootDegree
    (epsilon : ℝ) (heps : 0 < epsilon) (heps4 : epsilon ≤ 4) :
    ∃ k : ℕ,
      (k : ℝ) ≤ 32 * epsilon ^ (-(1 : ℝ) / 4) ∧
        SphereSOSMod (choiLamSphereQuartic + MvPolynomial.C epsilon) k := by
  obtain ⟨k, hk, hcert⟩ :=
    sphereChoiLamPerturbed_upperBound_rootDegree epsilon heps heps4
  exact ⟨k, hk, (sphereSOSMod_const_choiLam_iff k epsilon).mpr hcert⟩

/-- The existing Choi-Lam lower bound, restated directly for the constant perturbation
and the common root-degree convention. -/
theorem sphereSOSMod_const_choiLam_lowerBound_rootDegree
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0 / 16)
    (hcert : SphereSOSMod
      (choiLamSphereQuartic + MvPolynomial.C epsilon) k) :
    (schmInteriorLowerBoundConst4 / 2) *
        (16 * epsilon) ^ (-(1 : ℝ) / 4) ≤ (k : ℝ) :=
  sphereChoiLamPerturbed_lowerBound_rootDegree
    hk heps heps0 ((sphereSOSMod_const_choiLam_iff k epsilon).mp hcert)

end QuarticConvergence
end OptimalConvergenceRates

end
