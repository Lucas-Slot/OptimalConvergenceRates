/-
  Explicit section of the polynomial sphere-to-cube map.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.SphereLiftProperties

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


/-- The section in the named coordinate model. -/
def cubeSphereSectionNamed (n : ℕ) (x : Fin n → ℝ) : CubeSphereVar n → ℝ
  | none => 0
  | some (i, false) => x i / Real.sqrt n
  | some (i, true) => Real.sqrt (1 - x i ^ 2) / Real.sqrt n

/-- A cube point embedded in the product-of-circles locus on the sphere. -/
def cubeSphereSection (n : ℕ) (x : Fin n → ℝ) : Fin (2 * n + 1) → ℝ :=
  fun j ↦ cubeSphereSectionNamed n x ((cubeSphereEquiv n).symm j)

@[simp] theorem cubeSphereSection_first (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    cubeSphereSection n x (cubeSphereFirst n i) = x i / Real.sqrt n := by
  simp [cubeSphereSection, cubeSphereSectionNamed, cubeSphereFirst]

@[simp] theorem cubeSphereSection_second (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    cubeSphereSection n x (cubeSphereSecond n i) =
      Real.sqrt (1 - x i ^ 2) / Real.sqrt n := by
  simp [cubeSphereSection, cubeSphereSectionNamed, cubeSphereSecond]

theorem cubeSphereSection_pair_sq {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) (i : Fin n) :
    (x i / Real.sqrt n) ^ 2 +
        (Real.sqrt (1 - x i ^ 2) / Real.sqrt n) ^ 2 = 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hxi := (Hypercube_mem_iff x).mp hx i
  have hsq : x i ^ 2 ≤ 1 := by nlinarith [hxi.1, hxi.2]
  have hrad : 0 ≤ 1 - x i ^ 2 := sub_nonneg.mpr hsq
  rw [div_pow, div_pow, Real.sq_sqrt hrad, Real.sq_sqrt hnR.le]
  field_simp
  ring

/-- The explicit section lies on the unit sphere. -/
theorem cubeSphereSection_mem_sphere {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    cubeSphereSection n x ∈ sphereSet (2 * n + 1) := by
  have hpair' (i : Fin n) :
      (Real.sqrt (1 - x i ^ 2) / Real.sqrt n) ^ 2 +
          (x i / Real.sqrt n) ^ 2 = 1 / (n : ℝ) := by
    rw [add_comm]
    exact cubeSphereSection_pair_sq hn x hx i
  change MvPolynomial.eval (cubeSphereSection n x) (sphereQuadratic (2 * n + 1)) = 1
  simp only [sphereQuadratic, map_sum, map_pow, eval_X]
  rw [← (cubeSphereEquiv n).sum_comp (fun j ↦ cubeSphereSection n x j ^ 2)]
  simp only [cubeSphereSection, Equiv.symm_apply_apply]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp [cubeSphereSectionNamed, hpair', hn.ne']

/-- The explicit section is a right inverse of the polynomial map. -/
theorem cubeSphereMap_section {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    cubeSphereMap n (cubeSphereSection n x) = x := by
  funext i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  have hpair := cubeSphereSection_pair_sq hn x hx i
  have hmass :
      (n : ℝ) * ((x i / Real.sqrt n) ^ 2 +
        (Real.sqrt (1 - x i ^ 2) / Real.sqrt n) ^ 2) = 1 := by
    rw [hpair]
    field_simp
  rw [cubeSphereMap, eval_cubeSphereCoordinate, cubeSphereSection_first,
    cubeSphereSection_second, hmass]
  have hratio : ((2 * n + 1 : ℝ) - 1) / (2 * n) = 1 := by
    field_simp
    ring
  rw [hratio, one_pow]
  field_simp

/-- The polynomial sphere-to-cube map is onto the hypercube. -/
theorem cubeSphereMap_surjective_on_hypercube {n : ℕ} (hn : 0 < n) :
    ∀ x ∈ Hypercube n, ∃ z ∈ sphereSet (2 * n + 1), cubeSphereMap n z = x := by
  intro x hx
  exact ⟨cubeSphereSection n x, cubeSphereSection_mem_sphere hn x hx,
    cubeSphereMap_section hn x hx⟩

/-- The lift preserves the restriction sup norm exactly. -/
theorem sphereSupNorm_cubeSphereLift {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm (cubeSphereLift n p) = polySupNorm p := by
  apply le_antisymm (sphereSupNorm_cubeSphereLift_le hn p)
  apply polySupNorm_le_of_bound
  intro x hx
  have hz := cubeSphereSection_mem_sphere hn x hx
  have heval := eval_cubeSphereLift_eq_map n (cubeSphereSection n x) p
  rw [cubeSphereMap_section hn x hx] at heval
  rw [← heval]
  exact sphereSupNorm_eval_le (cubeSphereLift n p) (cubeSphereSection n x) hz

/-- The lift preserves the minimum exactly. -/
theorem spherePolyMin_cubeSphereLift {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    spherePolyMin (cubeSphereLift n p) = polyMin p := by
  apply le_antisymm
  · obtain ⟨x, hx, hmin⟩ := polyMin_mem p
    calc
      spherePolyMin (cubeSphereLift n p) ≤
          MvPolynomial.eval (cubeSphereSection n x) (cubeSphereLift n p) :=
        spherePolyMin_le_eval _ _ (cubeSphereSection_mem_sphere hn x hx)
      _ = MvPolynomial.eval x p := by
        rw [eval_cubeSphereLift_eq_map, cubeSphereMap_section hn x hx]
      _ = polyMin p := hmin
  · exact polyMin_le_spherePolyMin_cubeSphereLift hn p

end QuarticConvergence
end OptimalConvergenceRates

end
