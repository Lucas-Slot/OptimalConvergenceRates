/-
  Coordinate-plane rotations as products of two axial reflections.

  This supplies an exact one-parameter flow for differentiating the finite
  rotation equivariance of the normalized Boolean filter.  The orientation
  agrees with `coordinateRotationVector i j x = x_i e_j - x_j e_i`.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.FilterRotationEquivariance
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.FilteredRootHessian

open MvPolynomial Finset Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- The `i`-th coordinate unit vector, regarded as a sphere point. -/
def coordinateAxis {n : ℕ} (i : Fin n) : sphereSet n :=
  ⟨Pi.single i 1, by
    simp [sphereSet, sphereQuadratic, Pi.single_apply]⟩

@[simp] theorem coordinateAxis_apply {n : ℕ} (i q : Fin n) :
    (coordinateAxis i).1 q = if q = i then 1 else 0 := by
  simp only [coordinateAxis, Pi.single_apply]

/-- The unit axis making angle `t / 2` with the `i`-axis in the oriented
`(i,j)` coordinate plane. -/
def coordinateHalfAngleAxis {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (t : ℝ) : sphereSet n :=
  ⟨fun q ↦ if q = i then Real.cos (t / 2)
      else if q = j then Real.sin (t / 2) else 0, by
    simp only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X,
      Set.mem_ofPred_eq]
    calc
      (∑ q : Fin n,
          (if q = i then Real.cos (t / 2)
            else if q = j then Real.sin (t / 2) else 0) ^ 2) =
          ∑ q : Fin n,
            ((if q = i then Real.cos (t / 2) ^ 2 else 0) +
              if q = j then Real.sin (t / 2) ^ 2 else 0) := by
        apply Finset.sum_congr rfl
        intro q _hq
        by_cases hqi : q = i
        · subst q
          simp [hij]
        · by_cases hqj : q = j <;> simp [hqi, hqj, hij.symm]
      _ = Real.cos (t / 2) ^ 2 + Real.sin (t / 2) ^ 2 := by
        rw [Finset.sum_add_distrib]
        simp
      _ = 1 := Real.cos_sq_add_sin_sq (t / 2)⟩

@[simp] theorem coordinateHalfAngleAxis_apply {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) (q : Fin n) :
    (coordinateHalfAngleAxis i j hij t).1 q =
      if q = i then Real.cos (t / 2)
      else if q = j then Real.sin (t / 2) else 0 := rfl

/-- The oriented rotation through angle `t` in the `(i,j)` plane, represented
as the product of the half-angle axial reflection and the `i`-axis
reflection. -/
def coordinateRotationFlow {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (t : ℝ) (x : sphereSet n) : sphereSet n :=
  sphereTwoReflectionRotation
    (coordinateHalfAngleAxis i j hij t) (coordinateAxis i) x

theorem coordinateRotationFlow_eq_sphereTwoReflectionRotation {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) (x : sphereSet n) :
    coordinateRotationFlow i j hij t x =
      sphereTwoReflectionRotation
        (coordinateHalfAngleAxis i j hij t) (coordinateAxis i) x := rfl

/-- Coordinate formula for the rotation flow. -/
@[simp] theorem coordinateRotationFlow_apply {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) (x : sphereSet n)
    (q : Fin n) :
    (coordinateRotationFlow i j hij t x).1 q =
      if q = i then Real.cos t * x.1 i - Real.sin t * x.1 j
      else if q = j then Real.sin t * x.1 i + Real.cos t * x.1 j
      else x.1 q := by
  classical
  let c : ℝ := Real.cos (t / 2)
  let s : ℝ := Real.sin (t / 2)
  have hfirst (r : Fin n) :
      (sphereAxialReflection (coordinateAxis i) x).1 r =
        if r = i then x.1 i else -x.1 r := by
    change sphereAxialReflectionRaw (coordinateAxis i).1 x.1 r = _
    unfold sphereAxialReflectionRaw
    have hdot : (∑ a, x.1 a * (coordinateAxis i).1 a) = x.1 i := by
      simp [coordinateAxis, Pi.single_apply]
    rw [hdot]
    by_cases hri : r = i
    · subst r
      simp [coordinateAxis]
      ring
    · simp [coordinateAxis, hri]
  have hdot :
      (∑ r, (sphereAxialReflection (coordinateAxis i) x).1 r *
        (coordinateHalfAngleAxis i j hij t).1 r) =
        x.1 i * c - x.1 j * s := by
    simp_rw [hfirst, coordinateHalfAngleAxis_apply]
    calc
      (∑ r : Fin n,
          (if r = i then x.1 i else -x.1 r) *
            (if r = i then Real.cos (t / 2)
              else if r = j then Real.sin (t / 2) else 0)) =
          (∑ r : Fin n, if r = i then x.1 i * Real.cos (t / 2) else 0) +
            ∑ r : Fin n, if r = j then -x.1 j * Real.sin (t / 2) else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _hr
        by_cases hri : r = i
        · subst r
          simp [hij]
        · by_cases hrj : r = j
          · subst r
            simp [hij.symm]
          · simp [hri, hrj]
      _ = x.1 i * c - x.1 j * s := by
        simp [c, s]
        ring
  change 2 * (∑ r,
      (sphereAxialReflection (coordinateAxis i) x).1 r *
        (coordinateHalfAngleAxis i j hij t).1 r) *
      (coordinateHalfAngleAxis i j hij t).1 q -
        (sphereAxialReflection (coordinateAxis i) x).1 q = _
  rw [hdot, hfirst, coordinateHalfAngleAxis_apply]
  dsimp only [c, s]
  have ht : t = 2 * (t / 2) := by ring
  have hcos : Real.cos t = Real.cos (t / 2) ^ 2 - Real.sin (t / 2) ^ 2 := by
    calc
      Real.cos t = Real.cos (2 * (t / 2)) := congrArg Real.cos ht
      _ = _ := Real.cos_two_mul' (t / 2)
  have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    calc
      Real.sin t = Real.sin (2 * (t / 2)) := congrArg Real.sin ht
      _ = _ := Real.sin_two_mul (t / 2)
  by_cases hqi : q = i
  · subst q
    simp only [ite_eq_left]
    rw [hcos, hsin]
    have hunit := Real.sin_sq_add_cos_sq (t / 2)
    linear_combination (x.1 i) * hunit
  · by_cases hqj : q = j
    · subst q
      simp only [ite_eq_right hij.symm, ite_eq_left]
      rw [hcos, hsin]
      have hunit := Real.sin_sq_add_cos_sq (t / 2)
      linear_combination -(x.1 j) * hunit
    · simp [hqi, hqj]

@[simp] theorem coordinateRotationFlow_zero {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : sphereSet n) :
    coordinateRotationFlow i j hij 0 x = x := by
  apply Subtype.ext
  funext q
  have hji : j ≠ i := hij.symm
  by_cases hqi : q = i
  · simp [coordinateRotationFlow_apply, hqi]
  · by_cases hqj : q = j <;> simp [coordinateRotationFlow_apply, hqi, hqj, hji]

/-- The coordinate rotation is an additive one-parameter flow. -/
theorem coordinateRotationFlow_add {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (s t : ℝ) (x : sphereSet n) :
    coordinateRotationFlow i j hij (s + t) x =
      coordinateRotationFlow i j hij s
        (coordinateRotationFlow i j hij t x) := by
  apply Subtype.ext
  funext q
  have hji : j ≠ i := hij.symm
  by_cases hqi : q = i
  · subst q
    simp [coordinateRotationFlow_apply, hji, Real.sin_add, Real.cos_add]
    ring
  · by_cases hqj : q = j
    · subst q
      simp [coordinateRotationFlow_apply, hji, Real.sin_add, Real.cos_add]
      ring
    · simp [coordinateRotationFlow_apply, hqi, hqj]

theorem coordinateRotationFlow_neg {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) (x : sphereSet n) :
    coordinateRotationFlow i j hij (-t)
        (coordinateRotationFlow i j hij t x) = x := by
  rw [← coordinateRotationFlow_add]
  simp

/-- The velocity at zero is the coordinate-rotation vector field used by
`rotationHessianValue`. -/
theorem hasDerivAt_coordinateRotationFlow_zero {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : sphereSet n) :
    HasDerivAt (fun t ↦ (coordinateRotationFlow i j hij t x).1)
      (coordinateRotationVector i j x.1) 0 := by
  rw [hasDerivAt_pi]
  intro q
  by_cases hqi : q = i
  · subst q
    simp only [coordinateRotationFlow_apply, ite_eq_left]
    convert ((Real.hasDerivAt_cos 0).mul_const (x.1 i)).sub
      ((Real.hasDerivAt_sin 0).mul_const (x.1 j)) using 1
    all_goals simp [coordinateRotationVector, hij]
  · by_cases hqj : q = j
    · subst q
      simp only [coordinateRotationFlow_apply, ite_eq_right hij.symm, ite_eq_left]
      convert ((Real.hasDerivAt_sin 0).mul_const (x.1 i)).add
        ((Real.hasDerivAt_cos 0).mul_const (x.1 j)) using 1
      all_goals simp [coordinateRotationVector, hij]
    · simp only [coordinateRotationFlow_apply, ite_eq_right hqi, ite_eq_right hqj]
      convert hasDerivAt_const (x := (0 : ℝ)) (x.1 q) using 1
      simp [coordinateRotationVector, hqi, hqj]

/-- The velocity formula at an arbitrary time. -/
theorem hasDerivAt_coordinateRotationFlow {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : sphereSet n) (t₀ : ℝ) :
    HasDerivAt (fun t ↦ (coordinateRotationFlow i j hij t x).1)
      (coordinateRotationVector i j
        (coordinateRotationFlow i j hij t₀ x).1) t₀ := by
  rw [hasDerivAt_pi]
  intro q
  by_cases hqi : q = i
  · subst q
    simp only [coordinateRotationFlow_apply, ite_eq_left]
    convert ((Real.hasDerivAt_cos t₀).mul_const (x.1 i)).sub
      ((Real.hasDerivAt_sin t₀).mul_const (x.1 j)) using 1
    all_goals
      simp [coordinateRotationVector, hij, hij.symm]
      ring
  · by_cases hqj : q = j
    · subst q
      simp only [coordinateRotationFlow_apply, ite_eq_right hij.symm, ite_eq_left]
      convert ((Real.hasDerivAt_sin t₀).mul_const (x.1 i)).add
        ((Real.hasDerivAt_cos t₀).mul_const (x.1 j)) using 1
      all_goals
        simp [coordinateRotationVector, hij.symm]
        ring
    · simp only [coordinateRotationFlow_apply, ite_eq_right hqi, ite_eq_right hqj]
      convert hasDerivAt_const (x := t₀) (x.1 q) using 1
      simp [coordinateRotationVector, hqi, hqj]

end QuarticConvergence
end OptimalConvergenceRates

end
