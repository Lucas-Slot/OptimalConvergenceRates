/-
  Set-level geometry of the polynomial sphere-to-cube lift.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SphereLift

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


/-- The scalar AM--GM inequality used by every coordinate of the lift. -/
theorem cubeSphere_scalar_amgm (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht0 : 0 ≤ t) (htn : t ≤ n) :
    t * (((2 * n + 1 : ℝ) - t) / (2 * n)) ^ (2 * n) ≤ 1 := by
  let d : ℝ := 2 * n + 1
  let a : ℝ := (d - t) / (2 * n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < d := by dsimp [d]; positivity
  have hnum : 0 ≤ d - t := by
    dsimp [d]
    nlinarith
  have ha : 0 ≤ a := div_nonneg hnum (by positivity)
  have hw1 : 0 ≤ (1 / d : ℝ) := by positivity
  have hw2 : 0 ≤ ((2 * n : ℝ) / d) := by positivity
  have hwsum : (1 / d : ℝ) + (2 * n : ℝ) / d = 1 := by
    dsimp [d]
    field_simp
    ring
  have harith : (1 / d : ℝ) * t + ((2 * n : ℝ) / d) * a = 1 := by
    dsimp [a, d]
    field_simp
    ring
  have hamgm : t ^ (1 / d : ℝ) * a ^ ((2 * n : ℝ) / d) ≤ 1 := by
    calc
      t ^ (1 / d : ℝ) * a ^ ((2 * n : ℝ) / d) ≤
          (1 / d : ℝ) * t + ((2 * n : ℝ) / d) * a :=
        Real.geom_mean_le_arith_mean2_weighted hw1 hw2 ht0 ha hwsum
      _ = 1 := harith
  have hbase : 0 ≤ t ^ (1 / d : ℝ) * a ^ ((2 * n : ℝ) / d) :=
    mul_nonneg (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg ha _)
  have hpow := Real.rpow_le_one hbase hamgm (show 0 ≤ d by positivity)
  have hrewrite :
      (t ^ (1 / d : ℝ) * a ^ ((2 * n : ℝ) / d)) ^ d =
        t * a ^ (2 * n) := by
    rw [Real.mul_rpow (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg ha _)]
    rw [← Real.rpow_mul ht0, ← Real.rpow_mul ha]
    rw [show (1 / d : ℝ) * d = 1 by field_simp]
    rw [show ((2 * n : ℝ) / d) * d = (2 * n : ℝ) by field_simp]
    rw [Real.rpow_one]
    have hcast : (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) := by norm_num
    rw [hcast, Real.rpow_natCast]
  rw [hrewrite] at hpow
  change t * a ^ (2 * n) ≤ 1
  exact hpow

theorem cubeSphereFirst_ne_second (n : ℕ) (i : Fin n) :
    cubeSphereFirst n i ≠ cubeSphereSecond n i := by
  intro h
  apply (cubeSphereEquiv n).injective at h
  simp at h

@[simp] theorem eval_cubeSphereBlockMass (n : ℕ) (i : Fin n)
    (z : Fin (2 * n + 1) → ℝ) :
    MvPolynomial.eval z (cubeSphereBlockMass n i) =
      n * (z (cubeSphereFirst n i) ^ 2 + z (cubeSphereSecond n i) ^ 2) := by
  simp [cubeSphereBlockMass]

@[simp] theorem eval_cubeSphereCoordinate (n : ℕ) (i : Fin n)
    (z : Fin (2 * n + 1) → ℝ) :
    MvPolynomial.eval z (cubeSphereCoordinate n i) =
      Real.sqrt n * z (cubeSphereFirst n i) *
        (((2 * n + 1 : ℝ) -
          n * (z (cubeSphereFirst n i) ^ 2 + z (cubeSphereSecond n i) ^ 2)) /
            (2 * n)) ^ n := by
  simp [cubeSphereCoordinate, div_eq_mul_inv]

theorem cubeSphere_block_sq_le_one {n : ℕ} (i : Fin n)
    (z : Fin (2 * n + 1) → ℝ) (hz : z ∈ sphereSet (2 * n + 1)) :
    z (cubeSphereFirst n i) ^ 2 + z (cubeSphereSecond n i) ^ 2 ≤ 1 := by
  have hsphere : ∑ j : Fin (2 * n + 1), z j ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic] using hz
  let f := cubeSphereFirst n i
  let s := cubeSphereSecond n i
  have hne : f ≠ s := cubeSphereFirst_ne_second n i
  calc
    z (cubeSphereFirst n i) ^ 2 + z (cubeSphereSecond n i) ^ 2 =
        ∑ j ∈ ({f, s} : Finset (Fin (2 * n + 1))), z j ^ 2 := by
      simp [f, s, hne]
    _ ≤ ∑ j : Fin (2 * n + 1), z j ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simp
      · intro j _ _
        positivity
    _ = 1 := hsphere

/-- The polynomial coordinate map from the sphere. -/
def cubeSphereMap (n : ℕ) (z : Fin (2 * n + 1) → ℝ) : Fin n → ℝ :=
  fun i ↦ MvPolynomial.eval z (cubeSphereCoordinate n i)

/-- Each coordinate of the polynomial map has absolute value at most one on
the unit sphere. -/
theorem abs_cubeSphereMap_le_one {n : ℕ} (hn : 0 < n)
    (z : Fin (2 * n + 1) → ℝ) (hz : z ∈ sphereSet (2 * n + 1)) (i : Fin n) :
    |cubeSphereMap n z i| ≤ 1 := by
  let u := z (cubeSphereFirst n i)
  let v := z (cubeSphereSecond n i)
  let t : ℝ := n * (u ^ 2 + v ^ 2)
  let a : ℝ := ((2 * n + 1 : ℝ) - t) / (2 * n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hblock : u ^ 2 + v ^ 2 ≤ 1 := by
    simpa [u, v] using cubeSphere_block_sq_le_one i z hz
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htn : t ≤ n := by dsimp [t]; nlinarith
  have hscalar : t * a ^ (2 * n) ≤ 1 := by
    simpa [t, a] using cubeSphere_scalar_amgm n hn t ht0 htn
  have ha : 0 ≤ a := by
    dsimp [a]
    have ht : t ≤ (2 * n + 1 : ℝ) := by nlinarith
    exact div_nonneg (sub_nonneg.mpr ht) (by positivity)
  have hu : n * u ^ 2 ≤ t := by
    dsimp [t]
    nlinarith [sq_nonneg v]
  have hpow : 0 ≤ a ^ (2 * n) := by positivity
  have hsquare : (cubeSphereMap n z i) ^ 2 ≤ 1 := by
    calc
      (cubeSphereMap n z i) ^ 2 = n * u ^ 2 * a ^ (2 * n) := by
        rw [cubeSphereMap, eval_cubeSphereCoordinate]
        change (Real.sqrt n * u * a ^ n) ^ 2 = n * u ^ 2 * a ^ (2 * n)
        calc
          (Real.sqrt n * u * a ^ n) ^ 2 =
              (Real.sqrt n) ^ 2 * u ^ 2 * (a ^ n) ^ 2 := by ring
          _ = n * u ^ 2 * a ^ (2 * n) := by
            rw [Real.sq_sqrt hnR.le]
            rw [← pow_mul, Nat.mul_comm n 2]
      _ ≤ t * a ^ (2 * n) := mul_le_mul_of_nonneg_right hu hpow
      _ ≤ 1 := hscalar
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (cubeSphereMap n z i)]

/-- The polynomial map used by the lift sends the unit sphere into the
repository's standard hypercube. -/
theorem cubeSphereMap_mem_hypercube {n : ℕ} (hn : 0 < n)
    (z : Fin (2 * n + 1) → ℝ) (hz : z ∈ sphereSet (2 * n + 1)) :
    cubeSphereMap n z ∈ Hypercube n := by
  rw [Hypercube_mem_iff]
  intro i
  exact abs_le.mp (abs_cubeSphereMap_le_one hn z hz i)

end QuarticConvergence
end OptimalConvergenceRates

end
