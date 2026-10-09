/-
  Restriction of the controlled filtered sphere roots to the product of circles.

  This module deliberately keeps the polynomial family supplied by
  `FiniteFilteredRootScaleData`: restriction is only the linear
  `productCircleSubstitution`, so the degree and approximation estimates refer
  to the same roots.  The last part records exact angular differentiation
  identities; it does not postulate a derivative bound.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.ControlledRoots
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ProductCircle
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FiniteErrorAssembly

open MvPolynomial Finset Set
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- The standard cosine/sine parametrization of the product of unit circles. -/
def cosineSineCirclePoint {n : ℕ} (theta : Fin n → ℝ) : CubeCircleVar n → ℝ
  | (i, false) => Real.cos (theta i)
  | (i, true) => Real.sin (theta i)

@[simp] theorem cosineSineCirclePoint_first {n : ℕ} (theta : Fin n → ℝ)
    (i : Fin n) :
    cosineSineCirclePoint theta (i, false) = Real.cos (theta i) := rfl

@[simp] theorem cosineSineCirclePoint_second {n : ℕ} (theta : Fin n → ℝ)
    (i : Fin n) :
    cosineSineCirclePoint theta (i, true) = Real.sin (theta i) := rfl

/-- Every cosine/sine point lies on the product of circles. -/
theorem cosineSineCirclePoint_mem {n : ℕ} (theta : Fin n → ℝ) :
    cosineSineCirclePoint theta ∈ ProductCircle n := by
  intro i
  exact Real.cos_sq_add_sin_sq (theta i)

/-- Restrict one polynomial root in scale-resolved sphere data to paired
circle variables. -/
def FiniteFilteredRootScaleData.productCirclePolynomial
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteFilteredRootScaleData (2 * n + 1) C k F)
    (i : Fin data.N) : MvPolynomial (CubeCircleVar n) ℝ :=
  productCircleSubstitution n (data.polynomial i)

/-- Evaluation of a restricted filtered root is evaluation of the original
root polynomial at the scaled sphere point. -/
@[simp] theorem FiniteFilteredRootScaleData.eval_productCirclePolynomial
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteFilteredRootScaleData (2 * n + 1) C k F)
    (i : Fin data.N) (z : CubeCircleVar n → ℝ) :
    MvPolynomial.eval z
        (FiniteFilteredRootScaleData.productCirclePolynomial data i) =
      MvPolynomial.eval (productCircleSpherePoint n z) (data.polynomial i) := by
  exact eval_productCircleSubstitution n z (data.polynomial i)

/-- Product-circle restriction preserves the established linear root-degree
bound. -/
theorem FiniteFilteredRootScaleData.productCirclePolynomial_totalDegree_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteFilteredRootScaleData (2 * n + 1) C k F)
    (i : Fin data.N) :
    (FiniteFilteredRootScaleData.productCirclePolynomial data i).totalDegree ≤
      (2 * (2 * n + 1 + 3)) * k := by
  exact (productCircleSubstitution_totalDegree_le n (data.polynomial i)).trans
    (data.polynomial_totalDegree_le i)

/-- On angular points, a restricted root is literally the corresponding
sphere polynomial evaluated on the scaled cosine/sine inclusion. -/
@[simp] theorem FiniteFilteredRootScaleData.eval_productCirclePolynomial_angle
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteFilteredRootScaleData (2 * n + 1) C k F)
    (i : Fin data.N) (theta : Fin n → ℝ) :
    MvPolynomial.eval (cosineSineCirclePoint theta)
        (FiniteFilteredRootScaleData.productCirclePolynomial data i) =
      MvPolynomial.eval
        (productCircleSpherePoint n (cosineSineCirclePoint theta))
        (data.polynomial i) := by
  exact FiniteFilteredRootScaleData.eval_productCirclePolynomial
    data i (cosineSineCirclePoint theta)

/-- The filtered-root family for a lifted cube polynomial gives the expected
quartic pointwise square approximation on the whole product of circles.

The proof uses the three error fields already stored in
`FiniteFilteredRootScaleData`; no new approximation family is selected. -/
theorem FiniteFilteredRootScaleData.productCircle_square_approximation
    {n : ℕ} (hn : 0 < n) {C : ℝ} {k : ℕ}
    {h : MvPolynomial (Fin n) ℝ}
    (data : FiniteFilteredRootScaleData (2 * n + 1) C k (cubeSphereLift n h))
    {z : CubeCircleVar n → ℝ} (hz : z ∈ ProductCircle n) :
    |MvPolynomial.eval (fun i ↦ z (i, false)) h -
        ∑ i, (MvPolynomial.eval z
          (FiniteFilteredRootScaleData.productCirclePolynomial data i)) ^ 2| ≤
      C / (k : ℝ) ^ 4 := by
  let x := productCircleSpherePoint n z
  have hx : x ∈ sphereSet (2 * n + 1) := productCircleSpherePoint_mem_sphere hn hz
  let E : ℝ := C / (4 * (k : ℝ) ^ 4)
  have hnorm :
      sphereSupNorm
          (cubeSphereLift n h - ∑ i, (data.polynomial i) ^ 2) ≤
        2 * E + E + E :=
    finite_filtered_square_approximation_bound (by omega : 0 < 2 * n + 1)
      (cubeSphereLift n h) data.root data.polynomial E E E
      data.cross_error_le data.square_error_le data.remainder
  have hpoint :
      |MvPolynomial.eval x
          (cubeSphereLift n h - ∑ i, (data.polynomial i) ^ 2)| ≤
        sphereSupNorm (cubeSphereLift n h - ∑ i, (data.polynomial i) ^ 2) :=
    sphereSupNorm_eval_le _ x hx
  calc
    |MvPolynomial.eval (fun i ↦ z (i, false)) h -
        ∑ i, (MvPolynomial.eval z
          (FiniteFilteredRootScaleData.productCirclePolynomial data i)) ^ 2| =
        |MvPolynomial.eval x
          (cubeSphereLift n h - ∑ i, (data.polynomial i) ^ 2)| := by
      rw [map_sub, map_sum]
      simp only [map_pow]
      rw [eval_cubeSphereLift_eq_map]
      have hmap : cubeSphereMap n x = fun i ↦ z (i, false) := by
        funext i
        rw [cubeSphereMap, ← eval_productCircleSubstitution]
        exact eval_productCircleSubstitution_cubeSphereCoordinate hn hz i
      rw [hmap]
      congr 2
      apply Finset.sum_congr rfl
      intro i _hi
      rw [FiniteFilteredRootScaleData.eval_productCirclePolynomial]
    _ ≤ sphereSupNorm
          (cubeSphereLift n h - ∑ i, (data.polynomial i) ^ 2) := hpoint
    _ ≤ 2 * E + E + E := hnorm
    _ = C / (k : ℝ) ^ 4 := by
      dsimp [E]
      ring

/-- The angular form of the preceding product-circle estimate. -/
theorem FiniteFilteredRootScaleData.cosineSine_square_approximation
    {n : ℕ} (hn : 0 < n) {C : ℝ} {k : ℕ}
    {h : MvPolynomial (Fin n) ℝ}
    (data : FiniteFilteredRootScaleData (2 * n + 1) C k (cubeSphereLift n h))
    (theta : Fin n → ℝ) :
    |MvPolynomial.eval (fun i ↦ Real.cos (theta i)) h -
        ∑ i, (MvPolynomial.eval (cosineSineCirclePoint theta)
          (FiniteFilteredRootScaleData.productCirclePolynomial data i)) ^ 2| ≤
      C / (k : ℝ) ^ 4 := by
  simpa using FiniteFilteredRootScaleData.productCircle_square_approximation
    hn data (cosineSineCirclePoint_mem theta)

/-- The same restricted polynomial family, exposed directly from the public
controlled-root package. -/
def FiniteControlledRootData.productCirclePolynomial
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteControlledRootData (2 * n + 1) C k F)
    (i : Fin data.atoms.N) : MvPolynomial (CubeCircleVar n) ℝ :=
  productCircleSubstitution n (data.filter.polynomial i)

/-- Evaluation of a restricted controlled root uses exactly its stored Boolean-filter
polynomial at the scaled sphere point. -/
@[simp] theorem FiniteControlledRootData.eval_productCirclePolynomial
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteControlledRootData (2 * n + 1) C k F)
    (i : Fin data.atoms.N) (z : CubeCircleVar n → ℝ) :
    MvPolynomial.eval z (data.productCirclePolynomial i) =
      MvPolynomial.eval (productCircleSpherePoint n z)
        (data.filter.polynomial i) := by
  exact eval_productCircleSubstitution n z (data.filter.polynomial i)

/-- Controlled data inherit the same root-degree estimate without changing
their roots or Boolean filters. -/
theorem FiniteControlledRootData.productCirclePolynomial_totalDegree_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteControlledRootData (2 * n + 1) C k F)
    (i : Fin data.atoms.N) :
    (data.productCirclePolynomial i).totalDegree ≤
      (2 * (2 * n + 1 + 3)) * k := by
  exact (productCircleSubstitution_totalDegree_le n (data.filter.polynomial i)).trans
    (data.toFilteredRootScaleData.polynomial_totalDegree_le i)

/-- Controlled roots give the product-circle square approximation through
their canonical scale-data compatibility map. -/
theorem FiniteControlledRootData.productCircle_square_approximation
    {n : ℕ} (hn : 0 < n) {C : ℝ} {k : ℕ}
    {h : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData
      (2 * n + 1) C k (cubeSphereLift n h))
    {z : CubeCircleVar n → ℝ} (hz : z ∈ ProductCircle n) :
    |MvPolynomial.eval (fun i ↦ z (i, false)) h -
        ∑ i, (MvPolynomial.eval z (data.productCirclePolynomial i)) ^ 2| ≤
      C / (k : ℝ) ^ 4 := by
  simpa [FiniteControlledRootData.productCirclePolynomial,
    FiniteFilteredRootScaleData.productCirclePolynomial] using
    FiniteFilteredRootScaleData.productCircle_square_approximation
      hn data.toFilteredRootScaleData hz

/-- The infinitesimal rotation in the `i`-th paired circle variables. -/
def circleRotationDeriv {n : ℕ} (i : Fin n)
    (p : MvPolynomial (CubeCircleVar n) ℝ) :
    MvPolynomial (CubeCircleVar n) ℝ :=
  X (i, false) * pderiv (i, true) p -
    X (i, true) * pderiv (i, false) p

@[simp] theorem circleRotationDeriv_zero {n : ℕ} (i : Fin n) :
    circleRotationDeriv i (0 : MvPolynomial (CubeCircleVar n) ℝ) = 0 := by
  simp [circleRotationDeriv]

@[simp] theorem circleRotationDeriv_add {n : ℕ} (i : Fin n)
    (p q : MvPolynomial (CubeCircleVar n) ℝ) :
    circleRotationDeriv i (p + q) =
      circleRotationDeriv i p + circleRotationDeriv i q := by
  simp only [circleRotationDeriv, map_add]
  ring

theorem circleRotationDeriv_mul {n : ℕ} (i : Fin n)
    (p q : MvPolynomial (CubeCircleVar n) ℝ) :
    circleRotationDeriv i (p * q) =
      circleRotationDeriv i p * q + p * circleRotationDeriv i q := by
  simp only [circleRotationDeriv, pderiv_mul]
  ring

/-- The product-circle substitution intertwines an ambient block rotation with
the corresponding paired-variable circle rotation. -/
theorem circleRotationDeriv_productCircleSubstitution_X
    {n : ℕ} (i : Fin n) (j : Fin (2 * n + 1)) :
    circleRotationDeriv i (productCircleSubstitution n (X j)) =
      productCircleSubstitution n
        (rotationDeriv (cubeSphereFirst n i) (cubeSphereSecond n i) (X j)) := by
  rcases h : (cubeSphereEquiv n).symm j with _ | ⟨l, b⟩
  · have hj : j = cubeSphereEquiv n none :=
      (Equiv.symm_apply_eq (cubeSphereEquiv n)).mp h
    subst j
    simp [productCircleSubstitution, circleRotationDeriv, rotationDeriv,
      cubeSphereFirst, cubeSphereSecond, h]
  · have hj : j = cubeSphereEquiv n (some (l, b)) :=
      (Equiv.symm_apply_eq (cubeSphereEquiv n)).mp h
    subst j
    cases b <;> by_cases hli : l = i
    · subst l
      simp [productCircleSubstitution, circleRotationDeriv, rotationDeriv,
        cubeSphereFirst, cubeSphereSecond, h]
      ring
    · simp [productCircleSubstitution, circleRotationDeriv, rotationDeriv,
        cubeSphereFirst, cubeSphereSecond, h, hli]
    · subst l
      simp [productCircleSubstitution, circleRotationDeriv, rotationDeriv,
        cubeSphereFirst, cubeSphereSecond, h]
      ring
    · simp [productCircleSubstitution, circleRotationDeriv, rotationDeriv,
        cubeSphereFirst, cubeSphereSecond, h, hli]

/-- Exact algebraic commutation of product-circle restriction with a block
rotation derivative. -/
theorem circleRotationDeriv_productCircleSubstitution
    {n : ℕ} (i : Fin n) (p : MvPolynomial (Fin (2 * n + 1)) ℝ) :
    circleRotationDeriv i (productCircleSubstitution n p) =
      productCircleSubstitution n
        (rotationDeriv (cubeSphereFirst n i) (cubeSphereSecond n i) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp [productCircleSubstitution, circleRotationDeriv, rotationDeriv]
  | add p q hp hq =>
      simp [map_add, circleRotationDeriv_add, rotationDeriv_add, hp, hq]
  | mul_X p j hp =>
      have hrotmul :
          rotationDeriv (cubeSphereFirst n i) (cubeSphereSecond n i) (p * X j) =
            rotationDeriv (cubeSphereFirst n i) (cubeSphereSecond n i) p * X j +
              p * rotationDeriv
                (cubeSphereFirst n i) (cubeSphereSecond n i) (X j) := by
        simp only [rotationDeriv, pderiv_mul]
        ring
      rw [map_mul, circleRotationDeriv_mul, hp,
        circleRotationDeriv_productCircleSubstitution_X]
      rw [hrotmul, map_add, map_mul, map_mul]

/-- Two angular algebraic derivatives commute with restriction as the same
ordered pair of ambient block rotations. -/
theorem circleRotationDeriv_two_productCircleSubstitution
    {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin (2 * n + 1)) ℝ) :
    circleRotationDeriv i
        (circleRotationDeriv j (productCircleSubstitution n p)) =
      productCircleSubstitution n
        (rotationDeriv (cubeSphereFirst n i) (cubeSphereSecond n i)
          (rotationDeriv (cubeSphereFirst n j) (cubeSphereSecond n j) p)) := by
  rw [circleRotationDeriv_productCircleSubstitution,
    circleRotationDeriv_productCircleSubstitution]

/-- Replacing one angle by a scalar parameter. -/
def replaceAngle {n : ℕ} (theta : Fin n → ℝ) (i : Fin n) (t : ℝ) : Fin n → ℝ :=
  fun j ↦ if j = i then t else theta j

@[simp] theorem replaceAngle_self {n : ℕ} (theta : Fin n → ℝ) (i : Fin n) :
    replaceAngle theta i (theta i) = theta := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [replaceAngle]
  · simp [replaceAngle, hji]

/-- Exact first angular chain rule for a paired-variable polynomial. -/
theorem hasDerivAt_eval_cosineSineCirclePoint_replaceAngle
    {n : ℕ} (p : MvPolynomial (CubeCircleVar n) ℝ)
    (theta : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t ↦ MvPolynomial.eval
        (cosineSineCirclePoint (replaceAngle theta i t)) p)
      (MvPolynomial.eval (cosineSineCirclePoint theta)
        (circleRotationDeriv i p))
      (theta i) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simpa [circleRotationDeriv] using
        (hasDerivAt_const (x := theta i) c)
  | add p q hp hq =>
      simpa [circleRotationDeriv_add] using hp.add hq
  | mul_X p ib hp =>
      obtain ⟨j, b⟩ := ib
      have hcoordinate : HasDerivAt
          (fun t ↦ cosineSineCirclePoint (replaceAngle theta i t) (j, b))
          (MvPolynomial.eval (cosineSineCirclePoint theta)
            (circleRotationDeriv i (X (j, b))))
          (theta i) := by
        cases b <;> by_cases hji : j = i
        · subst j
          simpa [cosineSineCirclePoint, replaceAngle, circleRotationDeriv] using
            Real.hasDerivAt_cos (theta i)
        · simpa [cosineSineCirclePoint, replaceAngle, circleRotationDeriv, hji] using
            (hasDerivAt_const (x := theta i) (Real.cos (theta j)))
        · subst j
          simpa [cosineSineCirclePoint, replaceAngle, circleRotationDeriv] using
            Real.hasDerivAt_sin (theta i)
        · simpa [cosineSineCirclePoint, replaceAngle, circleRotationDeriv, hji] using
            (hasDerivAt_const (x := theta i) (Real.sin (theta j)))
      simpa [circleRotationDeriv_mul] using hp.mul hcoordinate

/-- Restricting an ambient polynomial and differentiating in one angle gives
exactly its ambient block-rotation derivative at the scaled sphere point. -/
theorem hasDerivAt_eval_productCircleSubstitution_replaceAngle
    {n : ℕ} (p : MvPolynomial (Fin (2 * n + 1)) ℝ)
    (theta : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t ↦ MvPolynomial.eval
        (cosineSineCirclePoint (replaceAngle theta i t))
        (productCircleSubstitution n p))
      (MvPolynomial.eval
        (productCircleSpherePoint n (cosineSineCirclePoint theta))
        (rotationDeriv (cubeSphereFirst n i) (cubeSphereSecond n i) p))
      (theta i) := by
  have h := hasDerivAt_eval_cosineSineCirclePoint_replaceAngle
    (productCircleSubstitution n p) theta i
  convert h using 1
  rw [circleRotationDeriv_productCircleSubstitution,
    eval_productCircleSubstitution]

/-- The ordered mixed angular derivative is the restriction of the ordered
pair of ambient block rotations.  This is an identity, not a bound. -/
theorem deriv_eval_productCircleSubstitution_rotationDeriv_replaceAngle
    {n : ℕ} (p : MvPolynomial (Fin (2 * n + 1)) ℝ)
    (theta : Fin n → ℝ) (i j : Fin n) :
    deriv (fun t ↦ MvPolynomial.eval
      (cosineSineCirclePoint (replaceAngle theta i t))
      (productCircleSubstitution n
        (rotationDeriv (cubeSphereFirst n j) (cubeSphereSecond n j) p)))
      (theta i) =
        MvPolynomial.eval
          (productCircleSpherePoint n (cosineSineCirclePoint theta))
          (rotationDeriv (cubeSphereFirst n i) (cubeSphereSecond n i)
            (rotationDeriv (cubeSphereFirst n j) (cubeSphereSecond n j) p)) :=
  (hasDerivAt_eval_productCircleSubstitution_replaceAngle
    (rotationDeriv (cubeSphereFirst n j) (cubeSphereSecond n j) p) theta i).deriv

/-- For each controlled root, the angular derivative is the ambient sphere
block-rotation derivative of that very same Boolean-filter polynomial. -/
theorem FiniteControlledRootData.hasDerivAt_productCirclePolynomial_replaceAngle
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteControlledRootData (2 * n + 1) C k F)
    (nu : Fin data.atoms.N) (theta : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t ↦ MvPolynomial.eval
        (cosineSineCirclePoint (replaceAngle theta i t))
        (data.productCirclePolynomial nu))
      (MvPolynomial.eval
        (productCircleSpherePoint n (cosineSineCirclePoint theta))
        (rotationDeriv (cubeSphereFirst n i) (cubeSphereSecond n i)
          (data.filter.polynomial nu)))
      (theta i) := by
  simpa [FiniteControlledRootData.productCirclePolynomial] using
    hasDerivAt_eval_productCircleSubstitution_replaceAngle
      (data.filter.polynomial nu) theta i

/-- The mixed angular derivative identity for each controlled root.  No
cardinality-dependent or pointwise derivative bound is introduced here. -/
theorem FiniteControlledRootData.deriv_circleRotationDeriv_productCirclePolynomial
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteControlledRootData (2 * n + 1) C k F)
    (nu : Fin data.atoms.N) (theta : Fin n → ℝ) (i j : Fin n) :
    deriv (fun t ↦ MvPolynomial.eval
      (cosineSineCirclePoint (replaceAngle theta i t))
      (circleRotationDeriv j (data.productCirclePolynomial nu))) (theta i) =
        MvPolynomial.eval
          (productCircleSpherePoint n (cosineSineCirclePoint theta))
          (rotationDeriv (cubeSphereFirst n i) (cubeSphereSecond n i)
            (rotationDeriv (cubeSphereFirst n j) (cubeSphereSecond n j)
              (data.filter.polynomial nu))) := by
  rw [FiniteControlledRootData.productCirclePolynomial,
    circleRotationDeriv_productCircleSubstitution]
  exact (hasDerivAt_eval_productCircleSubstitution_replaceAngle
    (rotationDeriv (cubeSphereFirst n j) (cubeSphereSecond n j)
      (data.filter.polynomial nu)) theta i).deriv

/-- Algebraic value of the first angular derivative. -/
theorem deriv_eval_cosineSineCirclePoint_replaceAngle
    {n : ℕ} (p : MvPolynomial (CubeCircleVar n) ℝ)
    (theta : Fin n → ℝ) (i : Fin n) :
    deriv (fun t ↦ MvPolynomial.eval
      (cosineSineCirclePoint (replaceAngle theta i t)) p) (theta i) =
      MvPolynomial.eval (cosineSineCirclePoint theta) (circleRotationDeriv i p) :=
  (hasDerivAt_eval_cosineSineCirclePoint_replaceAngle p theta i).deriv

/-- Reapplying the exact chain rule gives the algebraic mixed angular
derivative, with no analytic estimate asserted. -/
theorem deriv_eval_circleRotationDeriv_replaceAngle
    {n : ℕ} (p : MvPolynomial (CubeCircleVar n) ℝ)
    (theta : Fin n → ℝ) (i j : Fin n) :
    deriv (fun t ↦ MvPolynomial.eval
      (cosineSineCirclePoint (replaceAngle theta i t))
      (circleRotationDeriv j p)) (theta i) =
      MvPolynomial.eval (cosineSineCirclePoint theta)
        (circleRotationDeriv i (circleRotationDeriv j p)) :=
  deriv_eval_cosineSineCirclePoint_replaceAngle (circleRotationDeriv j p) theta i

end QuarticConvergence
end OptimalConvergenceRates

end
