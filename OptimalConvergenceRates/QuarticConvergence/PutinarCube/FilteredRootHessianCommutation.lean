/-
  Exact infinitesimal rotation commutation for the normalized Boolean filter.

  The proof differentiates the already established finite rotation
  equivariance.  Differentiation under the normalized kernel integral is
  justified by compactness of the sphere and the continuous first derivative
  of the source function.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.FilteredRootHessian
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.CoordinateRotationFlow

open MvPolynomial Finset Set Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- First derivative along the coordinate-rotation vector field. -/
def coordinateRotationValue {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i j : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (coordinateRotationVector i j x)

/-- A continuously differentiable function has a continuous coordinate
rotation derivative. -/
theorem continuous_coordinateRotationValue {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (i j : Fin n) :
    Continuous (coordinateRotationValue f i j) := by
  unfold coordinateRotationValue
  exact (hf.continuous_fderiv (by norm_num)).clm_apply
    (by
      simpa only [← coordinateRotationCLM_apply] using
        (coordinateRotationCLM i j).continuous)

/-- At a fixed angle, the coordinate rotation is continuous in its sphere
argument. -/
theorem continuous_coordinateRotationFlow_right {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    Continuous (coordinateRotationFlow i j hij t) := by
  rw [continuous_induced_rng]
  change Continuous (fun x ↦ (coordinateRotationFlow i j hij t x).1)
  convert (sphereForwardRotationCLM
      (coordinateHalfAngleAxis i j hij t) (coordinateAxis i)).continuous.comp
        continuous_subtype_val using 1
  funext x
  exact sphereTwoReflectionRotation_coe
    (coordinateHalfAngleAxis i j hij t) (coordinateAxis i) x

/-- Chain rule along the coordinate-rotation flow. -/
theorem hasDerivAt_comp_coordinateRotationFlow {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i j : Fin n) (hij : i ≠ j) (x : sphereSet n) (t : ℝ) :
    HasDerivAt (fun s ↦ f (coordinateRotationFlow i j hij s x).1)
      (coordinateRotationValue f i j
        (coordinateRotationFlow i j hij t x).1) t := by
  unfold coordinateRotationValue
  simpa only [Function.comp_apply] using
    ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_coordinateRotationFlow i j hij x t))

/-- Differentiation under one fixed normalized-kernel row along a coordinate
rotation.  Compactness supplies a uniform integrable majorant. -/
theorem hasDerivAt_integralSection_sourceRotation {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base x : sphereSet n)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i j : Fin n) (hij : i ≠ j) :
    HasDerivAt
      (fun t ↦ ∫ y : sphereSet n,
        normalizedZonalKernelSection p k base x y *
          f (coordinateRotationFlow i j hij t y).1
        ∂normalizedSphereMeasure n)
      (∫ y : sphereSet n,
        normalizedZonalKernelSection p k base x y *
          coordinateRotationValue f i j y.1
        ∂normalizedSphereMeasure n) 0 := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n (by omega)
  let row : sphereSet n → ℝ := fun y ↦
    normalizedZonalKernelSection p k base x y
  let v : sphereSet n → ℝ := fun y ↦ coordinateRotationValue f i j y.1
  have hrow : Continuous row :=
    continuous_normalizedZonalKernelSection_right p k base x
  have hv : Continuous v :=
    (continuous_coordinateRotationValue hf i j).comp continuous_subtype_val
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let F : ℝ → sphereSet n → ℝ := fun t y ↦
    row y * f (coordinateRotationFlow i j hij t y).1
  let F' : ℝ → sphereSet n → ℝ := fun t y ↦
    row y * v (coordinateRotationFlow i j hij t y)
  let bound : sphereSet n → ℝ := fun y ↦ ‖row y‖ * M
  have hFcont (t : ℝ) : Continuous (F t) := by
    exact hrow.mul (hf.continuous.comp
      (continuous_subtype_val.comp
        (continuous_coordinateRotationFlow_right i j hij t)))
  have hF'cont (t : ℝ) : Continuous (F' t) := by
    exact hrow.mul (hv.comp (continuous_coordinateRotationFlow_right i j hij t))
  have hboundcont : Continuous bound := hrow.norm.mul continuous_const
  have continuous_integrable {g : sphereSet n → ℝ} (hg : Continuous g) :
      Integrable g (normalizedSphereMeasure n) :=
    hg.integrable_of_hasCompactSupport
      ((isCompact_univ : IsCompact (Set.univ : Set (sphereSet n))).of_isClosed_subset
        (isClosed_tsupport g) (Set.subset_univ _))
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := normalizedSphereMeasure n) (F := F) (F' := F') (bound := bound)
    (s := Set.univ) (x₀ := (0 : ℝ)) univ_mem
    (Filter.Eventually.of_forall fun t ↦ (hFcont t).aestronglyMeasurable)
    (continuous_integrable (hFcont 0))
    ((hF'cont 0).aestronglyMeasurable)
    (by
      filter_upwards [] with y
      intro t _ht
      dsimp only [F', bound]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (hM (coordinateRotationFlow i j hij t y) (Set.mem_univ _))
        (norm_nonneg _))
    (continuous_integrable hboundcont)
    (by
      filter_upwards [] with y
      intro t _ht
      dsimp only [F, F']
      exact (hasDerivAt_comp_coordinateRotationFlow hf i j hij y t).const_mul
        (row y))
  simpa only [F, F', v, coordinateRotationFlow_zero] using hdiff.2

/-- The normalized zonal operator commutes infinitesimally with a coordinate
rotation of a continuously differentiable source. -/
theorem hasDerivAt_normalizedFunctionZonalKernelValue_rotation {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i j : Fin n) (hij : i ≠ j) (x : sphereSet n) :
    HasDerivAt
      (fun t ↦ normalizedFunctionZonalKernelValue p k base
        (fun y ↦ f y.1) (coordinateRotationFlow i j hij t x).1)
      (normalizedFunctionZonalKernelValue p k base
        (fun y ↦ coordinateRotationValue f i j y.1) x.1) 0 := by
  have hint := hasDerivAt_integralSection_sourceRotation
    hn p k base x hf i j hij
  rw [← normalizedFunctionZonalKernelValue_eq_integral_section
    p k base x (fun y ↦ coordinateRotationValue f i j y.1)] at hint
  apply hint.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t ↦ by
    change normalizedFunctionZonalKernelValue p k base (fun y ↦ f y.1)
      (coordinateRotationFlow i j hij t x).1 =
        ∫ y : sphereSet n, normalizedZonalKernelSection p k base x y *
          f (coordinateRotationFlow i j hij t y).1 ∂normalizedSphereMeasure n
    rw [coordinateRotationFlow_eq_sphereTwoReflectionRotation,
      normalizedFunctionZonalKernelValue_sphereTwoReflectionRotation]
    exact normalizedFunctionZonalKernelValue_eq_integral_section p k base x
      (fun y ↦ f (coordinateRotationFlow i j hij t y).1)

/-- Evaluation of an ambient polynomial along the coordinate-rotation flow
has derivative given by the algebraic rotation derivation. -/
theorem hasDerivAt_eval_coordinateRotationFlow {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (i j : Fin n) (hij : i ≠ j)
    (x : sphereSet n) :
    HasDerivAt
      (fun t ↦ MvPolynomial.eval
        (coordinateRotationFlow i j hij t x).1 P)
      (MvPolynomial.eval x.1 (rotationDeriv i j P)) 0 := by
  have hchain := (hasFDerivAt_mvPolynomial_eval P
      (coordinateRotationFlow i j hij 0 x).1).comp_hasDerivAt 0
    (hasDerivAt_coordinateRotationFlow_zero i j hij x)
  convert hchain using 1
  rw [mvPolynomialEvalFDeriv_eq_directionalDeriv]
  simpa only [coordinateRotationFlow_zero] using
    (directionalDeriv_coordinateRotation P x.1 i j).symm

/-- Pointwise polynomial form of exact first-order normalized-filter
commutation on the sphere. -/
theorem eval_rotationDeriv_normalizedFunctionZonalKernelPolynomial {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i j : Fin n) (hij : i ≠ j) (x : sphereSet n) :
    MvPolynomial.eval x.1 (rotationDeriv i j
      (normalizedFunctionZonalKernelPolynomial p k base (fun y ↦ f y.1))) =
      normalizedFunctionZonalKernelValue p k base
        (fun y ↦ coordinateRotationValue f i j y.1) x.1 := by
  let q := normalizedFunctionZonalKernelPolynomial p k base (fun y ↦ f y.1)
  have hv : Continuous (fun y : sphereSet n ↦ f y.1) :=
    hf.continuous.comp continuous_subtype_val
  have hcoeff : ZonalKernelCoeffIntegrable p k (fun y : sphereSet n ↦ f y.1) :=
    zonalKernelCoeffIntegrable_of_continuous (by omega) p k _ hv
      (zonalKernelCoeffContinuous p k)
  have hpoly := hasDerivAt_eval_coordinateRotationFlow q i j hij x
  have hvalue := hasDerivAt_normalizedFunctionZonalKernelValue_rotation
    hn p k base hf i j hij x
  have hpoly' := hvalue.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ by
      exact eval_normalizedFunctionZonalKernelPolynomial p k base
        (fun y ↦ f y.1) hcoeff
        (coordinateRotationFlow i j hij t x).1)
  exact hpoly.unique hpoly'

/-- Coordinate rotation of polynomial evaluation agrees with the algebraic
rotation derivation. -/
theorem coordinateRotationValue_mvPolynomial_eval {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (i j : Fin n) (x : Fin n → ℝ) :
    coordinateRotationValue (fun y ↦ MvPolynomial.eval y P) i j x =
      MvPolynomial.eval x (rotationDeriv i j P) := by
  unfold coordinateRotationValue
  rw [(hasFDerivAt_mvPolynomial_eval P x).fderiv,
    mvPolynomialEvalFDeriv_eq_directionalDeriv]
  exact directionalDeriv_coordinateRotation P x i j

/-- The pointwise Boolean filter commutes infinitesimally with coordinate
rotation. -/
theorem hasDerivAt_booleanFilteredFunctionValue_rotation {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i j : Fin n) (hij : i ≠ j) (x : sphereSet n) :
    HasDerivAt
      (fun t ↦ booleanFilteredFunctionValue p k base (fun y ↦ f y.1)
        (coordinateRotationFlow i j hij t x).1)
      (booleanFilteredFunctionValue p k base
        (fun y ↦ coordinateRotationValue f i j y.1) x.1) 0 := by
  let q := normalizedFunctionZonalKernelPolynomial p k base (fun y ↦ f y.1)
  let rot : sphereSet n → ℝ := fun y ↦ coordinateRotationValue f i j y.1
  have hv : Continuous (fun y : sphereSet n ↦ f y.1) :=
    hf.continuous.comp continuous_subtype_val
  have hcoeff : ZonalKernelCoeffIntegrable p k (fun y : sphereSet n ↦ f y.1) :=
    zonalKernelCoeffIntegrable_of_continuous (by omega) p k _ hv
      (zonalKernelCoeffContinuous p k)
  have hfirst := hasDerivAt_normalizedFunctionZonalKernelValue_rotation
    hn p k base hf i j hij x
  have hq : ContDiff ℝ 1 (fun z ↦ MvPolynomial.eval z q) :=
    mvPolynomial_eval_contDiff q 1
  have hsecond := hasDerivAt_normalizedFunctionZonalKernelValue_rotation
    hn p k base hq i j hij x
  have hsource :
      (fun y : sphereSet n ↦ coordinateRotationValue
        (fun z ↦ MvPolynomial.eval z q) i j y.1) =
      (fun y : sphereSet n ↦ normalizedFunctionZonalKernelValue p k base rot y.1) := by
    funext y
    rw [coordinateRotationValue_mvPolynomial_eval]
    exact eval_rotationDeriv_normalizedFunctionZonalKernelPolynomial
      hn p k base hf i j hij y
  rw [hsource] at hsecond
  have hsecond' : HasDerivAt
      (fun t ↦ normalizedFunctionZonalKernelValue p k base
        (fun y ↦ normalizedFunctionZonalKernelValue p k base
          (fun z ↦ f z.1) y.1)
        (coordinateRotationFlow i j hij t x).1)
      (normalizedFunctionZonalKernelValue p k base
        (fun y ↦ normalizedFunctionZonalKernelValue p k base rot y.1) x.1) 0 := by
    apply hsecond.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun t ↦ by
      apply congrArg (fun w ↦ normalizedFunctionZonalKernelValue p k base w
        (coordinateRotationFlow i j hij t x).1)
      funext y
      exact (eval_normalizedFunctionZonalKernelPolynomial p k base
        (fun z ↦ f z.1) hcoeff y.1).symm
  simpa only [booleanFilteredFunctionValue, rot] using
    (hfirst.add hfirst).sub hsecond'

/-- Exact Boolean-filter/rotation commutation in the stored polynomial
representation, evaluated at a sphere point. -/
theorem eval_rotationDeriv_booleanFilteredFunctionPolynomial {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    (i j : Fin n) (hij : i ≠ j) (x : sphereSet n) :
    MvPolynomial.eval x.1 (rotationDeriv i j
      (booleanFilteredFunctionPolynomial p k base (fun y ↦ f y.1))) =
      booleanFilteredFunctionValue p k base
        (fun y ↦ coordinateRotationValue f i j y.1) x.1 := by
  let q := normalizedFunctionZonalKernelPolynomial p k base (fun y ↦ f y.1)
  let B := booleanFilteredFunctionPolynomial p k base (fun y ↦ f y.1)
  have hv : Continuous (fun y : sphereSet n ↦ f y.1) :=
    hf.continuous.comp continuous_subtype_val
  have hcoeff : ZonalKernelCoeffIntegrable p k (fun y : sphereSet n ↦ f y.1) :=
    zonalKernelCoeffIntegrable_of_continuous (by omega) p k _ hv
      (zonalKernelCoeffContinuous p k)
  have hqcont : Continuous (fun y : sphereSet n ↦ MvPolynomial.eval y.1 q) :=
    (mvPolynomial_eval_contDiff q 0).continuous.comp continuous_subtype_val
  have hqcoeff : ZonalKernelCoeffIntegrable p k
      (fun y : sphereSet n ↦ MvPolynomial.eval y.1 q) :=
    zonalKernelCoeffIntegrable_of_continuous (by omega) p k _ hqcont
      (zonalKernelCoeffContinuous p k)
  have hpoly := hasDerivAt_eval_coordinateRotationFlow B i j hij x
  have hvalue := hasDerivAt_booleanFilteredFunctionValue_rotation
    hn p k base hf i j hij x
  have hpoly' := hvalue.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ by
      exact eval_booleanFilteredFunctionPolynomial p k base
        (fun y ↦ f y.1) hcoeff hqcoeff
        (coordinateRotationFlow i j hij t x).1)
  exact hpoly.unique hpoly'

/-- Polynomial tangential derivatives agree at the sphere whenever the two
polynomials agree on the sphere. -/
theorem eval_rotationDeriv_eq_of_eq_on_sphere {n : ℕ}
    (P Q : MvPolynomial (Fin n) ℝ)
    (hPQ : ∀ z : sphereSet n,
      MvPolynomial.eval z.1 P = MvPolynomial.eval z.1 Q)
    (i j : Fin n) (hij : i ≠ j) (x : sphereSet n) :
    MvPolynomial.eval x.1 (rotationDeriv i j P) =
      MvPolynomial.eval x.1 (rotationDeriv i j Q) := by
  have hP := hasDerivAt_eval_coordinateRotationFlow P i j hij x
  have hQ := hasDerivAt_eval_coordinateRotationFlow Q i j hij x
  have hP' := hQ.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦
      hPQ (coordinateRotationFlow i j hij t x))
  exact hP.unique hP'

/-- Automatic evaluation theorem for a Boolean polynomial whose source is
continuously differentiable. -/
theorem eval_booleanFilteredFunctionPolynomial_of_contDiff {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) (x : Fin n → ℝ) :
    MvPolynomial.eval x
        (booleanFilteredFunctionPolynomial p k base (fun y ↦ f y.1)) =
      booleanFilteredFunctionValue p k base (fun y ↦ f y.1) x := by
  let q := normalizedFunctionZonalKernelPolynomial p k base (fun y ↦ f y.1)
  have hv : Continuous (fun y : sphereSet n ↦ f y.1) :=
    hf.continuous.comp continuous_subtype_val
  have hcoeff : ZonalKernelCoeffIntegrable p k (fun y : sphereSet n ↦ f y.1) :=
    zonalKernelCoeffIntegrable_of_continuous (by omega) p k _ hv
      (zonalKernelCoeffContinuous p k)
  have hqcont : Continuous (fun y : sphereSet n ↦ MvPolynomial.eval y.1 q) :=
    (mvPolynomial_eval_contDiff q 0).continuous.comp continuous_subtype_val
  have hqcoeff : ZonalKernelCoeffIntegrable p k
      (fun y : sphereSet n ↦ MvPolynomial.eval y.1 q) :=
    zonalKernelCoeffIntegrable_of_continuous (by omega) p k _ hqcont
      (zonalKernelCoeffContinuous p k)
  exact eval_booleanFilteredFunctionPolynomial p k base
    (fun y ↦ f y.1) hcoeff hqcoeff x

/-- The first coordinate-rotation derivative of a C2 function is C1. -/
theorem contDiff_coordinateRotationValue {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (a b : Fin n) :
    ContDiff ℝ 1 (coordinateRotationValue f a b) := by
  unfold coordinateRotationValue
  have hv : ContDiff ℝ 1 (fun y ↦ coordinateRotationVector a b y) := by
    simpa only [← coordinateRotationCLM_apply] using
      (coordinateRotationCLM a b).contDiff
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply hv

/-- Iterating `coordinateRotationValue` gives the genuine rotation Hessian,
including the derivative of the inner rotation vector field. -/
theorem coordinateRotationValue_coordinateRotationValue {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (i j a b : Fin n) (x : Fin n → ℝ) :
    coordinateRotationValue (coordinateRotationValue f a b) i j x =
      rotationHessianValue f i j a b x := by
  exact fderiv_coordinateRotationValue_eq_rotationHessianValue
    hf i j a b x

/-- Exact mixed-rotation/Boolean-filter commutation on the sphere. -/
theorem eval_two_rotationDeriv_booleanFilteredFunctionPolynomial {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (i j a b : Fin n) (hij : i ≠ j) (hab : a ≠ b)
    (x : sphereSet n) :
    MvPolynomial.eval x.1
        (rotationDeriv i j (rotationDeriv a b
          (booleanFilteredFunctionPolynomial p k base (fun y ↦ f y.1)))) =
      booleanFilteredFunctionValue p k base
        (fun y ↦ rotationHessianValue f i j a b y.1) x.1 := by
  let g : (Fin n → ℝ) → ℝ := coordinateRotationValue f a b
  let Bf := booleanFilteredFunctionPolynomial p k base (fun y ↦ f y.1)
  let Bg := booleanFilteredFunctionPolynomial p k base (fun y ↦ g y.1)
  have hg : ContDiff ℝ 1 g := contDiff_coordinateRotationValue hf a b
  have hsphere : ∀ z : sphereSet n,
      MvPolynomial.eval z.1 (rotationDeriv a b Bf) =
        MvPolynomial.eval z.1 Bg := by
    intro z
    calc
      MvPolynomial.eval z.1 (rotationDeriv a b Bf) =
          booleanFilteredFunctionValue p k base
            (fun y ↦ coordinateRotationValue f a b y.1) z.1 :=
        eval_rotationDeriv_booleanFilteredFunctionPolynomial
          hn p k base (hf.of_le (by norm_num)) a b hab z
      _ = booleanFilteredFunctionValue p k base (fun y ↦ g y.1) z.1 := rfl
      _ = MvPolynomial.eval z.1 Bg :=
        (eval_booleanFilteredFunctionPolynomial_of_contDiff
          hn p k base hg z.1).symm
  calc
    MvPolynomial.eval x.1 (rotationDeriv i j (rotationDeriv a b Bf)) =
        MvPolynomial.eval x.1 (rotationDeriv i j Bg) :=
      eval_rotationDeriv_eq_of_eq_on_sphere
        (rotationDeriv a b Bf) Bg hsphere i j hij x
    _ = booleanFilteredFunctionValue p k base
        (fun y ↦ coordinateRotationValue g i j y.1) x.1 :=
      eval_rotationDeriv_booleanFilteredFunctionPolynomial
        hn p k base hg i j hij x
    _ = booleanFilteredFunctionValue p k base
        (fun y ↦ rotationHessianValue f i j a b y.1) x.1 := by
      apply congrArg (fun w ↦ booleanFilteredFunctionValue p k base w x.1)
      funext y
      exact coordinateRotationValue_coordinateRotationValue hf i j a b y.1

/-- For every stored controlled root, the two rotations of its filtered
polynomial are exactly the Boolean filter of the original root Hessian. -/
theorem FiniteControlledRootData.eval_two_rotationDeriv_filterPolynomial
    {n : ℕ} (hn : 2 ≤ n) {C : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F)
    (nu : Fin data.atoms.N) (i j a b : Fin n)
    (hij : i ≠ j) (hab : a ≠ b) (x : sphereSet n) :
    MvPolynomial.eval x.1
        (rotationDeriv i j (rotationDeriv a b
          (data.filter.polynomial nu))) =
      booleanFilteredFunctionValue (n + 3) k data.atoms.base
        (fun y ↦ rotationHessianValue
          (data.atoms.root nu) i j a b y.1) x.1 := by
  rw [data.filter.polynomial_eq_booleanFilter nu]
  exact eval_two_rotationDeriv_booleanFilteredFunctionPolynomial
    hn (n + 3) k data.atoms.base
      ((data.regular.root_contDiff nu).of_le (by norm_num))
      i j a b hij hab x

/-- Root-count-free square estimate for the actual twice-rotated filtered
polynomials stored in controlled data. -/
theorem FiniteControlledRootData.sum_eval_two_rotationDeriv_filterPolynomial_sq_le
    {n : ℕ} (hn : 2 ≤ n) {C : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F)
    (i j a b : Fin n) (hij : i ≠ j) (hab : a ≠ b)
    (x : sphereSet n) :
    ∑ nu, (MvPolynomial.eval x.1
      (rotationDeriv i j (rotationDeriv a b
        (data.filter.polynomial nu)))) ^ 2 ≤ 144 * C := by
  calc
    ∑ nu, (MvPolynomial.eval x.1
        (rotationDeriv i j (rotationDeriv a b
          (data.filter.polynomial nu)))) ^ 2 =
        ∑ nu, (booleanFilteredFunctionValue (n + 3) k data.atoms.base
          (fun y ↦ rotationHessianValue
            (data.atoms.root nu) i j a b y.1) x.1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro nu _hnu
      rw [data.eval_two_rotationDeriv_filterPolynomial
        hn nu i j a b hij hab x]
    _ ≤ 144 * C :=
      data.booleanFilteredRotationHessian_squareFunction_le hn i j a b x

/-- The preceding square estimate transported to the product of circles. -/
theorem FiniteControlledRootData.sum_eval_two_circleRotationDeriv_sq_le
    {n : ℕ} (hn : 0 < n) {C : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteControlledRootData (2 * n + 1) C k F)
    (i j : Fin n) {z : CubeCircleVar n → ℝ} (hz : z ∈ ProductCircle n) :
    ∑ nu, (MvPolynomial.eval z
      (circleRotationDeriv i (circleRotationDeriv j
        (data.productCirclePolynomial nu)))) ^ 2 ≤ 144 * C := by
  let x : sphereSet (2 * n + 1) :=
    ⟨productCircleSpherePoint n z, productCircleSpherePoint_mem_sphere hn hz⟩
  have hambient := data.sum_eval_two_rotationDeriv_filterPolynomial_sq_le
    (by omega : 2 ≤ 2 * n + 1)
    (cubeSphereFirst n i) (cubeSphereSecond n i)
    (cubeSphereFirst n j) (cubeSphereSecond n j)
    (cubeSphereFirst_ne_second n i) (cubeSphereFirst_ne_second n j) x
  simpa only [FiniteControlledRootData.productCirclePolynomial,
    circleRotationDeriv_two_productCircleSubstitution,
    eval_productCircleSubstitution] using hambient

/-- Angular form of the root-count-free twice-rotated circle estimate. -/
theorem FiniteControlledRootData.sum_eval_two_circleRotationDeriv_angle_sq_le
    {n : ℕ} (hn : 0 < n) {C : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteControlledRootData (2 * n + 1) C k F)
    (i j : Fin n) (theta : Fin n → ℝ) :
    ∑ nu, (MvPolynomial.eval (cosineSineCirclePoint theta)
      (circleRotationDeriv i (circleRotationDeriv j
        (data.productCirclePolynomial nu)))) ^ 2 ≤ 144 * C :=
  data.sum_eval_two_circleRotationDeriv_sq_le hn i j
    (cosineSineCirclePoint_mem theta)

end QuarticConvergence
end OptimalConvergenceRates

end
