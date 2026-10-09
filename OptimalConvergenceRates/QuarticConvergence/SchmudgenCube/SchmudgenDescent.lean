/-
  Descent of sphere SOS certificates through the cube sphere lift to the
  canonical box preordering.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ConeWitnesses
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SquareAverage
import OptimalConvergenceRates.QuarticConvergence.Sphere.SphereIdeal

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


variable {n k : ℕ} {p : MvPolynomial (Fin n) ℝ}

/-- Summing the parity preorderings of several roots can be regrouped by the
box-generator set. -/
theorem sum_circleParityPreorderingPolynomial {N : ℕ}
    (P : Fin N → MvPolynomial (CubeCircleVar n) ℝ) :
    ∑ j : Fin N, circleParityPreorderingPolynomial (P j) =
      ∑ J ∈ Finset.univ.powerset,
        (∑ j : Fin N, (circleParityComponent (P j) J) ^ 2) *
          BoxSemialgebraicGeneratorProd J := by
  classical
  calc
    ∑ j : Fin N, circleParityPreorderingPolynomial (P j) =
        ∑ j : Fin N, ∑ J ∈ Finset.univ.powerset,
          (circleParityComponent (P j) J) ^ 2 *
            BoxSemialgebraicGeneratorProd J := by
      rfl
    _ = ∑ J ∈ Finset.univ.powerset, ∑ j : Fin N,
          (circleParityComponent (P j) J) ^ 2 *
            BoxSemialgebraicGeneratorProd J := by
      rw [Finset.sum_comm]
    _ = ∑ J ∈ Finset.univ.powerset,
        (∑ j : Fin N, (circleParityComponent (P j) J) ^ 2) *
          BoxSemialgebraicGeneratorProd J := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [Finset.sum_mul]

/-- A sphere SOS certificate for the polynomial cube lift descends to a
Schmüdgen certificate. The output order is `2*k` because the sphere convention
bounds root degree by `k`, whereas the repository's box convention bounds the
total degree of each complete weighted square term. -/
theorem sphereSOSMod_cubeSphereLift_to_boxPreordering
    (hn : 0 < n)
    (hcert : SphereSOSMod (cubeSphereLift n p) k) :
    p ∈ BoxPreordering n (2 * k) := by
  classical
  obtain ⟨N, q, relationMultiplier, hdecomp, hdegree⟩ := hcert
  let P : Fin N → MvPolynomial (CubeCircleVar n) ℝ :=
    fun j ↦ productCircleSubstitution n (q j)
  let root : Finset (Fin n) → Fin N → MvPolynomial (Fin n) ℝ :=
    fun J j ↦ circleParityComponent (P j) J
  have hrootDegree (J : Finset (Fin n)) (j : Fin N) :
      root J j = 0 ∨ (root J j).totalDegree + J.card ≤ k := by
    rcases circleParityComponent_eq_zero_or_totalDegree_add_card_le (P j) J with
      hzero | hweighted
    · exact Or.inl hzero
    · exact Or.inr <| hweighted.trans <|
        (productCircleSubstitution_totalDegree_le n (q j)).trans (hdegree j)
  have hpointwise :
      p = ∑ j : Fin N, circleParityPreorderingPolynomial (P j) := by
    apply sub_eq_zero.mp
    apply mvPolynomial_eq_zero_of_eval_eq_zero_on_openCube 1 zero_lt_one
    intro x hx
    have hxclosed : ∀ i, |x i| ≤ 1 := fun i ↦ (hx i).le
    have hscaled :
        (2 : ℝ) ^ n * MvPolynomial.eval x p =
          (2 : ℝ) ^ n *
            MvPolynomial.eval x
              (∑ j : Fin N, circleParityPreorderingPolynomial (P j)) := by
      calc
        (2 : ℝ) ^ n * MvPolynomial.eval x p =
            ∑ eps : Fin n → Bool, MvPolynomial.eval x p := by
          simp
        _ = ∑ eps : Fin n → Bool, ∑ j : Fin N,
              (MvPolynomial.eval (signedCirclePoint x eps) (P j)) ^ 2 := by
          apply Fintype.sum_congr
          intro eps
          have hz := signedCirclePoint_mem_productCircle x eps hxclosed
          calc
            MvPolynomial.eval x p =
                MvPolynomial.eval (signedCirclePoint x eps)
                  (productCircleSubstitution n (cubeSphereLift n p)) :=
              (eval_productCircleSubstitution_cubeSphereLift hn hz p).symm
            _ = MvPolynomial.eval (signedCirclePoint x eps)
                  (productCircleSubstitution n
                    ((∑ j : Fin N, (q j) ^ 2) +
                      sphereRelation (2 * n + 1) * relationMultiplier)) := by
              rw [hdecomp]
            _ = ∑ j : Fin N,
                (MvPolynomial.eval (signedCirclePoint x eps) (P j)) ^ 2 := by
              simp only [map_add, map_sum, map_pow, map_mul,
                eval_productCircleSubstitution_sphereRelation hn hz,
                zero_mul, add_zero, P]
        _ = ∑ j : Fin N, ∑ eps : Fin n → Bool,
              (MvPolynomial.eval (signedCirclePoint x eps) (P j)) ^ 2 := by
          rw [Finset.sum_comm]
        _ = ∑ j : Fin N, (2 : ℝ) ^ n *
              MvPolynomial.eval x (circleParityPreorderingPolynomial (P j)) := by
          apply Fintype.sum_congr
          intro j
          exact sum_signedCircle_eval_sq (P j) x hxclosed
        _ = (2 : ℝ) ^ n *
            MvPolynomial.eval x
              (∑ j : Fin N, circleParityPreorderingPolynomial (P j)) := by
          rw [map_sum, Finset.mul_sum]
    have hpowpos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
    simp only [map_sub]
    nlinarith
  refine boxPreordering_of_weightedRoots (p := p) (k := k)
    (fun _J ↦ N) root ?_ hrootDegree
  exact hpointwise.trans (sum_circleParityPreorderingPolynomial P)

end QuarticConvergence
end OptimalConvergenceRates

end
