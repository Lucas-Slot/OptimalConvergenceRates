/-
  Bounds and degree bookkeeping for the enlarged polynomial used by the
  degree-linear Putinar repair.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarEnlargement
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SphereLiftSection

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

variable {n : ℕ}

/-- The enlargement estimate with a supplied cube bound.  This is the form
used in the final approximation assembly, where the residual already comes
with a concrete uniform error bound. -/
theorem polyScale_add_two_bound_bounds
    (u : MvPolynomial (Fin n) ℝ) (D : ℕ) (L : ℝ)
    (hD : 1 ≤ D) (huDegree : u.totalDegree ≤ D)
    (huBound : polySupNorm u ≤ L)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    (2 / 3 : ℝ) * L ≤
        MvPolynomial.eval x
          (polyScale (putinarEnlargementRadius D)
            (u + MvPolynomial.C (2 * L))) ∧
      MvPolynomial.eval x
          (polyScale (putinarEnlargementRadius D)
            (u + MvPolynomial.C (2 * L))) ≤
        (10 / 3 : ℝ) * L := by
  have habs := abs_eval_polyScale_putinarEnlargement_le
    u D hD huDegree x hx
  have hnorm : 0 ≤ polySupNorm u := polySupNorm_nonneg u
  have hL : 0 ≤ L := hnorm.trans huBound
  have habsL :
      |MvPolynomial.eval x
        (polyScale (putinarEnlargementRadius D) u)| ≤
          (4 / 3 : ℝ) * L := by
    exact habs.trans (mul_le_mul_of_nonneg_left huBound (by norm_num))
  simp only [map_add, polyScale_eval, MvPolynomial.eval_C]
  rw [polyScale_eval] at habsL
  have hbounds := abs_le.mp habsL
  constructor <;> linarith

/-- The enlarged-and-scaled polynomial has the same two-sided bounds after
the polynomial lift to the sphere. -/
theorem cubeSphereLift_polyScale_add_two_bound_bounds
    {n : ℕ} (hn : 0 < n)
    (u : MvPolynomial (Fin n) ℝ) (D : ℕ) (L : ℝ)
    (hD : 1 ≤ D) (huDegree : u.totalDegree ≤ D)
    (huBound : polySupNorm u ≤ L)
    (z : Fin (2 * n + 1) → ℝ) (hz : z ∈ sphereSet (2 * n + 1)) :
    (2 / 3 : ℝ) * L ≤
        MvPolynomial.eval z
          (cubeSphereLift n
            (polyScale (putinarEnlargementRadius D)
              (u + MvPolynomial.C (2 * L)))) ∧
      MvPolynomial.eval z
          (cubeSphereLift n
            (polyScale (putinarEnlargementRadius D)
              (u + MvPolynomial.C (2 * L)))) ≤
        (10 / 3 : ℝ) * L := by
  rw [eval_cubeSphereLift_eq_map]
  exact polyScale_add_two_bound_bounds u D L hD huDegree huBound
    (cubeSphereMap n z) (cubeSphereMap_mem_hypercube hn z hz)

/-- Convenient weaker constants matching the bounded-positivity sphere
adapter. -/
theorem cubeSphereLift_polyScale_add_two_bound_conditioned
    {n : ℕ} (hn : 0 < n)
    (u : MvPolynomial (Fin n) ℝ) (D : ℕ) (L : ℝ)
    (hD : 1 ≤ D) (huDegree : u.totalDegree ≤ D)
    (huBound : polySupNorm u ≤ L)
    (z : Fin (2 * n + 1) → ℝ) (hz : z ∈ sphereSet (2 * n + 1)) :
    L / 2 ≤
        MvPolynomial.eval z
          (cubeSphereLift n
            (polyScale (putinarEnlargementRadius D)
              (u + MvPolynomial.C (2 * L)))) ∧
      MvPolynomial.eval z
          (cubeSphereLift n
            (polyScale (putinarEnlargementRadius D)
              (u + MvPolynomial.C (2 * L)))) ≤
        7 * L / 2 := by
  have hbounds := cubeSphereLift_polyScale_add_two_bound_bounds
    hn u D L hD huDegree huBound z hz
  have hL : 0 ≤ L := (polySupNorm_nonneg u).trans huBound
  constructor <;> nlinarith

/-- The enlarged lifted polynomial still has degree linear in the input
degree, with the lift's existing dimension factor. -/
theorem cubeSphereLift_polyScale_add_two_bound_totalDegree_le
    (u : MvPolynomial (Fin n) ℝ) (D : ℕ) (L : ℝ)
    (huDegree : u.totalDegree ≤ D) :
    (cubeSphereLift n
      (polyScale (putinarEnlargementRadius D)
        (u + MvPolynomial.C (2 * L)))).totalDegree ≤
      (2 * n + 1) * D := by
  apply (cubeSphereLift_totalDegree_le n _).trans
  apply Nat.mul_le_mul_left
  apply (polyScale_totalDegree_le _ _).trans
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le huDegree
  calc
    (MvPolynomial.C (2 * L) : MvPolynomial (Fin n) ℝ).totalDegree = 0 :=
      MvPolynomial.totalDegree_C _
    _ ≤ D := Nat.zero_le D

end QuarticConvergence
end OptimalConvergenceRates

end
