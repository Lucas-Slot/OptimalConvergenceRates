/-
  A small enlargement of the cube for the Putinar repair.

  This file deliberately reuses the Baldi--Slot extended cube and Markov
  perturbation theorem.  The output is pointwise, so no second sup-norm
  convention is introduced.
-/
import OptimalConvergenceRates.BaldiSlot2024.UpperBound

open MvPolynomial Finset Real

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-- The coordinate enlargement used by the Putinar repair. -/
def putinarEnlargementEpsilon (D : ℕ) : ℝ :=
  1 / (6 * constCChebyshev * (D : ℝ) ^ 2)

/-- The radius of the enlarged cube. -/
def putinarEnlargementRadius (D : ℕ) : ℝ :=
  1 + putinarEnlargementEpsilon D

/-- The corresponding shift of the canonical generator:
`b² - X_i² = (1 - X_i²) + eta`. -/
def putinarEnlargementShift (D : ℕ) : ℝ :=
  putinarEnlargementRadius D ^ 2 - 1

theorem putinarEnlargementEpsilon_pos {D : ℕ} (hD : 1 ≤ D) :
    0 < putinarEnlargementEpsilon D := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  unfold putinarEnlargementEpsilon
  exact one_div_pos.mpr
    (mul_pos (mul_pos (by norm_num) constCChebyshev_pos)
      (pow_pos hDreal 2))

theorem putinarEnlargementEpsilon_le_inv_sq {D : ℕ} (hD : 1 ≤ D) :
    putinarEnlargementEpsilon D ≤ 1 / (D : ℝ) ^ 2 := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  unfold putinarEnlargementEpsilon
  apply div_le_div_of_nonneg_left (by norm_num) (pow_pos hDreal 2)
  have hc : (1 : ℝ) ≤ constCChebyshev := one_le_constCChebyshev
  nlinarith

theorem putinarEnlargementRadius_pos {D : ℕ} (hD : 1 ≤ D) :
    0 < putinarEnlargementRadius D := by
  unfold putinarEnlargementRadius
  linarith [putinarEnlargementEpsilon_pos hD]

theorem putinarEnlargementShift_nonneg {D : ℕ} (hD : 1 ≤ D) :
    0 ≤ putinarEnlargementShift D := by
  have heps := putinarEnlargementEpsilon_pos hD
  unfold putinarEnlargementShift putinarEnlargementRadius
  nlinarith [sq_nonneg (putinarEnlargementEpsilon D)]

/-- The generator shift is bounded below by a dimension-free multiple of
`D⁻²`.  A later choice `k = O_n(D)` therefore meets the shifted-product
hypothesis. -/
theorem putinarEnlargementShift_ge {D : ℕ} (hD : 1 ≤ D) :
    1 / (3 * constCChebyshev * (D : ℝ) ^ 2) ≤
      putinarEnlargementShift D := by
  have heps := putinarEnlargementEpsilon_pos hD
  have hDreal : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hc : 0 < constCChebyshev := constCChebyshev_pos
  have htwo :
      2 * putinarEnlargementEpsilon D =
        1 / (3 * constCChebyshev * (D : ℝ) ^ 2) := by
    unfold putinarEnlargementEpsilon
    field_simp
    ring
  rw [← htwo]
  unfold putinarEnlargementShift putinarEnlargementRadius
  nlinarith [sq_nonneg (putinarEnlargementEpsilon D)]

/-- The existing Markov perturbation estimate gives a `4/3` growth bound
on the enlarged cube. -/
theorem abs_eval_le_four_thirds_on_putinarEnlargement
    (u : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (hD : 1 ≤ D) (huDegree : u.totalDegree ≤ D)
    (z : Fin n → ℝ)
    (hz : z ∈ ExtendedHypercube (putinarEnlargementEpsilon D) n) :
    |MvPolynomial.eval z u| ≤ (4 / 3 : ℝ) * polySupNorm u := by
  have heps : 0 < putinarEnlargementEpsilon D :=
    putinarEnlargementEpsilon_pos hD
  have hperturb := markov_perturbation_bound u D huDegree z
    (putinarEnlargementEpsilon D) heps
    (putinarEnlargementEpsilon_le_inv_sq hD) hz
  have hclamp :
      |MvPolynomial.eval (clampVec z) u| ≤ polySupNorm u :=
    polySupNorm_eval_le u (polySupNorm u) le_rfl _
      (clampVec_mem_Hypercube z)
  have hcoefficient :
      2 * constCChebyshev * (D : ℝ) ^ 2 *
          putinarEnlargementEpsilon D = 1 / 3 := by
    have hDreal : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have hc : 0 < constCChebyshev := constCChebyshev_pos
    unfold putinarEnlargementEpsilon
    field_simp
    ring
  have htriangle :
      |MvPolynomial.eval z u| ≤
        |MvPolynomial.eval (clampVec z) u| +
          |MvPolynomial.eval z u - MvPolynomial.eval (clampVec z) u| := by
    calc
      |MvPolynomial.eval z u| =
          |MvPolynomial.eval (clampVec z) u +
            (MvPolynomial.eval z u - MvPolynomial.eval (clampVec z) u)| := by
              ring_nf
      _ ≤ |MvPolynomial.eval (clampVec z) u| +
          |MvPolynomial.eval z u - MvPolynomial.eval (clampVec z) u| :=
        abs_add_le _ _
  calc
    |MvPolynomial.eval z u| ≤
        |MvPolynomial.eval (clampVec z) u| +
          |MvPolynomial.eval z u - MvPolynomial.eval (clampVec z) u| :=
      htriangle
    _ ≤ polySupNorm u +
          (2 * constCChebyshev * (D : ℝ) ^ 2 *
            putinarEnlargementEpsilon D) * polySupNorm u := by
      gcongr
    _ = (4 / 3 : ℝ) * polySupNorm u := by rw [hcoefficient]; ring

/-- Scaled points from the ordinary cube lie in the enlarged cube. -/
theorem putinarEnlargement_smul_mem
    {D : ℕ} (hD : 1 ≤ D) (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    (fun i ↦ putinarEnlargementRadius D * x i) ∈
      ExtendedHypercube (putinarEnlargementEpsilon D) n := by
  apply ScaledHypercube_subset_ExtendedHypercube
      (putinarEnlargementRadius D) (putinarEnlargementEpsilon D)
      (putinarEnlargementRadius_pos hD).le
  · rfl
  rw [ScaledHypercube_mem_abs _ (putinarEnlargementRadius_pos hD).le]
  intro i
  have hi := (Hypercube_mem_iff x).mp hx i
  rw [abs_mul, abs_of_pos (putinarEnlargementRadius_pos hD)]
  exact mul_le_of_le_one_right (putinarEnlargementRadius_pos hD).le
    (abs_le.mpr ⟨hi.1, hi.2⟩)

/-- The scaled polynomial inherits the enlarged-cube growth bound on the
ordinary cube. -/
theorem abs_eval_polyScale_putinarEnlargement_le
    (u : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (hD : 1 ≤ D) (huDegree : u.totalDegree ≤ D)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    |MvPolynomial.eval x (polyScale (putinarEnlargementRadius D) u)| ≤
      (4 / 3 : ℝ) * polySupNorm u := by
  rw [polyScale_eval]
  exact abs_eval_le_four_thirds_on_putinarEnlargement u D hD huDegree _
    (putinarEnlargement_smul_mem hD x hx)

/-- After adding `2 * ‖u‖∞`, the repair polynomial is uniformly bounded
away from zero and from above on the scaled cube. -/
theorem polyScale_add_two_supNorm_bounds
    (u : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (hD : 1 ≤ D) (huDegree : u.totalDegree ≤ D)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    (2 / 3 : ℝ) * polySupNorm u ≤
        MvPolynomial.eval x
          (polyScale (putinarEnlargementRadius D)
            (u + MvPolynomial.C (2 * polySupNorm u))) ∧
      MvPolynomial.eval x
          (polyScale (putinarEnlargementRadius D)
            (u + MvPolynomial.C (2 * polySupNorm u))) ≤
        (10 / 3 : ℝ) * polySupNorm u := by
  have habs := abs_eval_polyScale_putinarEnlargement_le u D hD huDegree x hx
  have hnorm : 0 ≤ polySupNorm u := polySupNorm_nonneg u
  simp only [map_add, polyScale_eval, MvPolynomial.eval_C]
  rw [polyScale_eval] at habs
  have hbounds := abs_le.mp habs
  constructor <;> linarith

end QuarticConvergence
end OptimalConvergenceRates

end
