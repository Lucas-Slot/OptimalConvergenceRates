/-
  Scaling adapter for the sphere-to-cube descent used by Putinar repair.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SchmudgenDescent
import OptimalConvergenceRates.BaldiSlot2024.ScaledSchmudgen

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


variable {n r k : ℕ} {p : MvPolynomial (Fin n) ℝ}

/-- Scaling a canonical box-preordering certificate back by `c⁻¹` gives a
certificate using the generators `c² - X_i²`, without increasing canonical
total certificate degree. -/
theorem polyScale_inv_mem_ScaledBoxPreordering
    (c : ℝ) (hc : c ≠ 0) (hp : p ∈ BoxPreordering n r) :
    polyScale c⁻¹ p ∈ ScaledBoxPreordering c n r := by
  obtain ⟨τ, hτsos, hτdegree, hτsum⟩ := hp
  let σ : Finset (Fin n) → MvPolynomial (Fin n) ℝ := fun J ↦
    MvPolynomial.C (c⁻¹ ^ (2 * J.card)) * polyScale c⁻¹ (τ J)
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro J
    dsimp only [σ]
    apply IsSOS_nonneg_scale (polyScale_IsSOS c⁻¹ (hτsos J))
    exact (even_two_mul J.card).pow_nonneg (c⁻¹)
  · intro J
    have hterm :
        σ J * ScaledBoxGeneratorProd c J =
          polyScale c⁻¹ (τ J * BoxSemialgebraicGeneratorProd J) := by
      rw [map_mul, polyScale_inv_generatorProd c hc J]
      dsimp only [σ]
      ring
    rw [hterm]
    exact (polyScale_totalDegree_le c⁻¹ _).trans (hτdegree J)
  · rw [hτsum, map_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [map_mul, polyScale_inv_generatorProd c hc J]
    dsimp only [σ]
    ring

/-- A sphere certificate for the lift of the dilated polynomial descends to
the preordering of the enlarged-cube generators `c² - X_i²`.

The order remains `2*k`, matching the repository's total-degree convention.
-/
theorem sphereSOSMod_cubeSphereLift_polyScale_to_ScaledBoxPreordering
    (hn : 0 < n) (c : ℝ) (hc : c ≠ 0)
    (hcert : SphereSOSMod (cubeSphereLift n (polyScale c p)) k) :
    p ∈ ScaledBoxPreordering c n (2 * k) := by
  have hcanonical : polyScale c p ∈ BoxPreordering n (2 * k) :=
    sphereSOSMod_cubeSphereLift_to_boxPreordering hn hcert
  have hscaled := polyScale_inv_mem_ScaledBoxPreordering c hc hcanonical
  rw [polyScale_inv c hc p] at hscaled
  exact hscaled

end QuarticConvergence
end OptimalConvergenceRates

end
