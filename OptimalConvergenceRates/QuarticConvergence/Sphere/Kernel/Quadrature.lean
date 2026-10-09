/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/Quadrature.lean

  Exact positive quadratures for bounded-degree polynomial functions on the sphere.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Measure
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.FiniteNormalization
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open Set MeasureTheory MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- A positive finite quadrature on the algebraic sphere, exact for every
ambient polynomial of total degree at most `L`.  Its nodes live in the same
`sphereSet` used by the shared spherical-SOS definition. -/
structure SpherePolynomialQuadrature (n L N : ℕ) where
  weight : Fin N → ℝ
  node : Fin N → sphereSet n
  weight_nonneg : ∀ i, 0 ≤ weight i
  exact : ∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ L →
    ∑ i, weight i * MvPolynomial.eval (node i).1 q =
      ∫ x : sphereSet n, MvPolynomial.eval x.1 q ∂normalizedSphereMeasure n

namespace SpherePolynomialQuadrature

/-- The raw coordinate vectors of the quadrature nodes, in the format used by
the finite zonal-kernel operator. -/
def coordinates {n L N : ℕ} (Q : SpherePolynomialQuadrature n L N) :
    Fin N → Fin n → ℝ := fun i ↦ (Q.node i).1

theorem coordinates_mem_sphereSet {n L N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (i : Fin N) :
    Q.coordinates i ∈ sphereSet n :=
  (Q.node i).2

/-- Exactness is monotone in the requested polynomial degree. -/
def lowerDegree {n L M N : ℕ} (Q : SpherePolynomialQuadrature n L N)
    (hML : M ≤ L) : SpherePolynomialQuadrature n M N where
  weight := Q.weight
  node := Q.node
  weight_nonneg := Q.weight_nonneg
  exact q hq := Q.exact q (hq.trans hML)

@[simp] theorem lowerDegree_weight {n L M N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (hML : M ≤ L) :
    (Q.lowerDegree hML).weight = Q.weight := rfl

@[simp] theorem lowerDegree_node {n L M N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (hML : M ≤ L) :
    (Q.lowerDegree hML).node = Q.node := rfl

/-- Since constants are among the exact moments, a positive-dimensional sphere
quadrature has total weight one. -/
theorem sum_weight_eq_one {n L N : ℕ} (hn : 0 < n)
    (Q : SpherePolynomialQuadrature n L N) :
    ∑ i, Q.weight i = 1 := by
  have h := Q.exact (1 : MvPolynomial (Fin n) ℝ) (by simp)
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  simpa using h

/-- The continuous mass of a zonal kernel section.  Rotation invariance will
later show that this is independent of the base point. -/
def continuousZonalKernelMass {n : ℕ} (p k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∫ y : sphereSet n,
    MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
      ∂normalizedSphereMeasure n

/-- Every continuous zonal-kernel section is continuous on the algebraic
sphere. -/
theorem continuous_sphereDirichletZonalKernel_section {n : ℕ} (p k : ℕ)
    (x : Fin n → ℝ) :
    Continuous (fun y : sphereSet n ↦
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)) := by
  exact (MvPolynomial.continuous_eval
    (sphereDirichletZonalKernel p k x)).comp continuous_subtype_val

/-- Every zonal-kernel section is integrable against normalized sphere
measure in positive dimension. -/
theorem integrable_sphereDirichletZonalKernel_section {n : ℕ} (hn : 0 < n)
    (p k : ℕ) (x : Fin n → ℝ) :
    Integrable (fun y : sphereSet n ↦
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x))
      (normalizedSphereMeasure n) :=
  integrable_eval_normalizedSphereMeasure hn
    (sphereDirichletZonalKernel p k x)

/-- The unnormalized continuous zonal kernel has strictly positive mass at
every sphere point. This isolates positivity of the normalization constant
from the still-separate rotation-invariance proof that the mass is constant. -/
theorem continuousZonalKernelMass_pos {n : ℕ} (hn : 0 < n)
    (p k : ℕ) (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    0 < continuousZonalKernelMass p k x := by
  letI : Measure.IsOpenPosMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isOpenPosMeasure n
  apply integral_pos_of_integrable_nonneg_nonzero (x := ⟨x, hx⟩)
    (continuous_sphereDirichletZonalKernel_section p k x)
    (integrable_sphereDirichletZonalKernel_section hn p k x)
  · intro y
    exact eval_sphereDirichletZonalKernel_nonneg p k y.1 x
  · rw [eval_sphereDirichletZonalKernel]
    have hdot : ∑ i, x i * x i = 1 := by
      simpa [sphereSet, sphereQuadratic, pow_two] using hx
    rw [hdot, sphereDirichletPolynomial_eval_one]
    positivity

/-- Products of a bounded-degree sphere polynomial with a zonal-kernel section
are integrable against normalized sphere measure. -/
theorem integrable_mul_sphereDirichletZonalKernel_section {n D : ℕ} (hn : 0 < n)
    (p k : ℕ) (v : spherePolynomialSpace n D) (x : Fin n → ℝ) :
    Integrable (fun y : sphereSet n ↦ v.1 y *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x))
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact v.1.continuous.mul
      (continuous_sphereDirichletZonalKernel_section p k x)
  · exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
      (subset_univ _)

/-- A normalized continuous kernel's pointwise error is the normalized
integral of increments from the base point. This is the continuous analogue
of `eval_finiteZonalKernelImage_sub`. -/
theorem continuousZonalKernelIntegral_sub {n D : ℕ} (hn : 0 < n)
    (p k : ℕ) (Z : ℝ) (v : spherePolynomialSpace n D)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n)
    (hmass : continuousZonalKernelMass p k x = Z) :
    (∫ y : sphereSet n, v.1 y *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n) / Z - v.1 ⟨x, hx⟩ =
      (∫ y : sphereSet n, (v.1 y - v.1 ⟨x, hx⟩) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n) / Z := by
  have hZpos : 0 < Z :=
    (continuousZonalKernelMass_pos hn p k x hx).trans_eq hmass
  have hkernel := integrable_sphereDirichletZonalKernel_section hn p k x
  have hmul := integrable_mul_sphereDirichletZonalKernel_section hn p k v x
  have hint : (fun y : sphereSet n ↦ (v.1 y - v.1 ⟨x, hx⟩) *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)) =
      (fun y ↦ v.1 y * MvPolynomial.eval y.1
        (sphereDirichletZonalKernel p k x) -
        v.1 ⟨x, hx⟩ * MvPolynomial.eval y.1
          (sphereDirichletZonalKernel p k x)) := by
    funext y
    ring
  rw [hint, integral_sub hmul (hkernel.const_mul (v.1 ⟨x, hx⟩))]
  rw [integral_const_mul, show (∫ y : sphereSet n,
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
        ∂normalizedSphereMeasure n) = Z from hmass]
  field_simp [hZpos.ne']

/-- Exactness through degree `2*(p*k)` converts the continuous zonal-kernel
mass into the corresponding finite weighted mass. -/
theorem sum_kernel_eq_continuousZonalKernelMass {n L N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (p k : ℕ)
    (hdeg : 2 * (p * k) ≤ L) (x : Fin n → ℝ) :
    ∑ i, Q.weight i *
        ((sphereDirichletPolynomial k).eval
          (∑ j, Q.coordinates i j * x j)) ^ (2 * p) =
      continuousZonalKernelMass p k x := by
  have h := Q.exact (sphereDirichletZonalKernel p k x)
    ((sphereDirichletZonalKernel_totalDegree_le p k x).trans hdeg)
  simpa only [coordinates, continuousZonalKernelMass,
    eval_sphereDirichletZonalKernel_comm,
    eval_sphereDirichletZonalKernel] using h

/-- A quadrature exact through degree `D + 2*(p*k)` also integrates the
product of a degree-`D` sphere polynomial with every zonal kernel section.
This is the precise finite-moment identity behind the sampled kernel operator. -/
theorem sum_value_mul_kernel_eq_integral {n D L N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (p k : ℕ)
    (hdeg : D + 2 * (p * k) ≤ L) (v : spherePolynomialSpace n D)
    (x : Fin n → ℝ) :
    ∑ i, Q.weight i * v.1 (Q.node i) *
        ((sphereDirichletPolynomial k).eval
          (∑ j, Q.coordinates i j * x j)) ^ (2 * p) =
      ∫ y : sphereSet n, v.1 y *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n := by
  obtain ⟨q, hqdeg, hqv⟩ :=
    (mem_spherePolynomialSpace_iff v.1).1 v.2
  have hprod :
      (q * sphereDirichletZonalKernel p k x).totalDegree ≤ L := by
    calc
      (q * sphereDirichletZonalKernel p k x).totalDegree ≤
          q.totalDegree +
            (sphereDirichletZonalKernel p k x).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ D + 2 * (p * k) :=
        Nat.add_le_add hqdeg
          (sphereDirichletZonalKernel_totalDegree_le p k x)
      _ ≤ L := hdeg
  have hexact := Q.exact (q * sphereDirichletZonalKernel p k x) hprod
  calc
    (∑ i, Q.weight i * v.1 (Q.node i) *
        ((sphereDirichletPolynomial k).eval
          (∑ j, Q.coordinates i j * x j)) ^ (2 * p)) =
        ∑ i, Q.weight i *
          MvPolynomial.eval (Q.node i).1
            (q * sphereDirichletZonalKernel p k x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, eval_sphereDirichletZonalKernel_comm,
        eval_sphereDirichletZonalKernel]
      have hi := DFunLike.congr_fun hqv (Q.node i)
      simp only [sphereRestrictionLinear_apply] at hi
      rw [hi]
      simp [coordinates, mul_assoc]
    _ = ∫ y : sphereSet n,
        MvPolynomial.eval y.1
          (q * sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n := hexact
    _ = ∫ y : sphereSet n, v.1 y *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      filter_upwards with y
      rw [map_mul]
      exact congrArg
        (fun z ↦ z *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x))
        (DFunLike.congr_fun hqv y)

/-- After dividing the weights by `Z`, evaluation of the sampled polynomial
operator is exactly the normalized continuous kernel integral. -/
theorem eval_finiteZonalKernelOperator_div_eq_integral {n D L N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (p k : ℕ)
    (hdeg : D + 2 * (p * k) ≤ L) (Z : ℝ)
    (v : spherePolynomialSpace n D) (x : Fin n → ℝ) :
    MvPolynomial.eval x
        (finiteZonalKernelOperator p k (fun i ↦ Q.weight i / Z)
          Q.coordinates (fun i ↦ v.1 (Q.node i))) =
      (∫ y : sphereSet n, v.1 y *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n) / Z := by
  rw [eval_finiteZonalKernelOperator]
  calc
    (∑ i, (Q.weight i / Z * v.1 (Q.node i)) *
        ((sphereDirichletPolynomial k).eval
          (∑ j, Q.coordinates i j * x j)) ^ (2 * p)) =
      (∑ i, Q.weight i * v.1 (Q.node i) *
        ((sphereDirichletPolynomial k).eval
          (∑ j, Q.coordinates i j * x j)) ^ (2 * p)) / Z := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = (∫ y : sphereSet n, v.1 y *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n) / Z := by
      rw [Q.sum_value_mul_kernel_eq_integral p k hdeg v x]
/-- A continuously normalized zonal kernel remains normalized after any exact
positive quadrature of sufficient degree. -/
theorem finiteZonalKernelNormalized_of_exact {n L N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (p k : ℕ)
    (hdeg : 2 * (p * k) ≤ L)
    (hmass : ∀ x ∈ sphereSet n, continuousZonalKernelMass p k x = 1) :
    FiniteZonalKernelNormalized p k Q.weight Q.coordinates := by
  intro x hx
  rw [Q.sum_kernel_eq_continuousZonalKernelMass p k hdeg x, hmass x hx]

/-- If the continuous mass is a positive constant `Z`, division of every
quadrature weight by `Z` gives the normalized finite kernel used by repair. -/
theorem finiteZonalKernelNormalized_of_exact_div {n L N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (p k : ℕ)
    (hdeg : 2 * (p * k) ≤ L) (Z : ℝ) (hZ : Z ≠ 0)
    (hmass : ∀ x ∈ sphereSet n, continuousZonalKernelMass p k x = Z) :
    FiniteZonalKernelNormalized p k (fun i ↦ Q.weight i / Z)
      Q.coordinates := by
  intro x hx
  rw [show (∑ i, Q.weight i / Z *
      ((sphereDirichletPolynomial k).eval
        (∑ j, Q.coordinates i j * x j)) ^ (2 * p)) =
      (∑ i, Q.weight i *
        ((sphereDirichletPolynomial k).eval
          (∑ j, Q.coordinates i j * x j)) ^ (2 * p)) / Z by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring]
  rw [Q.sum_kernel_eq_continuousZonalKernelMass p k hdeg x, hmass x hx]
  exact div_self hZ

/-- Positive continuous mass preserves nonnegativity of the rescaled
quadrature weights. -/
theorem div_weight_nonneg {n L N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) {Z : ℝ} (hZ : 0 < Z) :
    ∀ i, 0 ≤ Q.weight i / Z :=
  fun i ↦ div_nonneg (Q.weight_nonneg i) hZ.le

/-- Exact quadrature and constant positive mass give all finite normalization
data after rescaling by the mass. -/
theorem exact_div_kernel_data {n L N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (p k : ℕ)
    (hdeg : 2 * (p * k) ≤ L) (Z : ℝ) (hZ : 0 < Z)
    (hmass : ∀ x ∈ sphereSet n, continuousZonalKernelMass p k x = Z) :
    (∀ i, 0 ≤ Q.weight i / Z) ∧
      FiniteZonalKernelNormalized p k (fun i ↦ Q.weight i / Z)
        Q.coordinates :=
  ⟨Q.div_weight_nonneg hZ,
    Q.finiteZonalKernelNormalized_of_exact_div p k hdeg Z hZ.ne' hmass⟩

/-- Thus exact quadrature supplies the normalization and nonnegative weights
needed by the finite positive-kernel machinery. -/
theorem exact_kernel_data {n L N : ℕ}
    (Q : SpherePolynomialQuadrature n L N) (p k : ℕ)
    (hdeg : 2 * (p * k) ≤ L)
    (hmass : ∀ x ∈ sphereSet n, continuousZonalKernelMass p k x = 1) :
    (∀ i, 0 ≤ Q.weight i) ∧
      FiniteZonalKernelNormalized p k Q.weight Q.coordinates :=
  ⟨Q.weight_nonneg, Q.finiteZonalKernelNormalized_of_exact p k hdeg hmass⟩

/-- Evaluation at a sphere point as a linear functional on ambient
polynomials of total degree at most `L`. -/
def momentEvaluation {n L : ℕ} (x : sphereSet n) :
    Module.Dual ℝ (MvPolynomial.restrictTotalDegree (Fin n) ℝ L) where
  toFun q := MvPolynomial.eval x.1 q.1
  map_add' q r := by simp
  map_smul' a q := by simp

/-- Integration against normalized surface measure as a linear moment
functional on the bounded-degree polynomial space. -/
noncomputable def momentFunctional {n L : ℕ} (hn : 0 < n) :
    Module.Dual ℝ (MvPolynomial.restrictTotalDegree (Fin n) ℝ L) where
  toFun q :=
    ∫ x : sphereSet n, MvPolynomial.eval x.1 q.1
      ∂normalizedSphereMeasure n
  map_add' q r := by
    change (∫ x : sphereSet n,
      MvPolynomial.eval x.1 (q.1 + r.1) ∂normalizedSphereMeasure n) =
        (∫ x : sphereSet n,
          MvPolynomial.eval x.1 q.1 ∂normalizedSphereMeasure n) +
        ∫ x : sphereSet n,
          MvPolynomial.eval x.1 r.1 ∂normalizedSphereMeasure n
    simpa only [map_add] using
      integral_add
        (integrable_eval_normalizedSphereMeasure hn q.1)
        (integrable_eval_normalizedSphereMeasure hn r.1)
  map_smul' a q := by
    change (∫ x : sphereSet n,
      MvPolynomial.eval x.1 (a • q.1) ∂normalizedSphereMeasure n) =
        a * ∫ x : sphereSet n,
          MvPolynomial.eval x.1 q.1 ∂normalizedSphereMeasure n
    simpa only [MvPolynomial.smul_eval, smul_eq_mul] using
      integral_const_mul (μ := normalizedSphereMeasure n) a
        (fun x : sphereSet n ↦ MvPolynomial.eval x.1 q.1)

/-- Coordinates of a point-evaluation functional in the dual basis induced by
the standard finite basis of bounded-degree polynomials. This realizes the
moment problem in an ordinary finite Euclidean coordinate space. -/
noncomputable def momentCoordinateEvaluation {n L : ℕ} (x : sphereSet n) :
    Fin (Module.finrank ℝ
      (MvPolynomial.restrictTotalDegree (Fin n) ℝ L)) → ℝ :=
  (Module.finBasis ℝ
    (MvPolynomial.restrictTotalDegree (Fin n) ℝ L)).dualBasis.equivFun
      (momentEvaluation (L := L) x)

/-- Coordinates of the normalized integral functional in the same dual basis. -/
noncomputable def momentCoordinateFunctional {n L : ℕ} (hn : 0 < n) :
    Fin (Module.finrank ℝ
      (MvPolynomial.restrictTotalDegree (Fin n) ℝ L)) → ℝ :=
  (Module.finBasis ℝ
    (MvPolynomial.restrictTotalDegree (Fin n) ℝ L)).dualBasis.equivFun
      (momentFunctional (L := L) hn)

@[simp] theorem momentCoordinateEvaluation_apply {n L : ℕ}
    (x : sphereSet n)
    (i : Fin (Module.finrank ℝ
      (MvPolynomial.restrictTotalDegree (Fin n) ℝ L))) :
    momentCoordinateEvaluation (L := L) x i =
      MvPolynomial.eval x.1
        ((Module.finBasis ℝ
          (MvPolynomial.restrictTotalDegree (Fin n) ℝ L)) i).1 := by
  simp [momentCoordinateEvaluation, momentEvaluation]

@[simp] theorem momentCoordinateFunctional_apply {n L : ℕ} (hn : 0 < n)
    (i : Fin (Module.finrank ℝ
      (MvPolynomial.restrictTotalDegree (Fin n) ℝ L))) :
    momentCoordinateFunctional (L := L) hn i =
      ∫ x : sphereSet n,
        MvPolynomial.eval x.1
          ((Module.finBasis ℝ
            (MvPolynomial.restrictTotalDegree (Fin n) ℝ L)) i).1
        ∂normalizedSphereMeasure n := by
  simp [momentCoordinateFunctional, momentFunctional]

/-- The finite moment-coordinate map varies continuously with the sphere point. -/
theorem continuous_momentCoordinateEvaluation {n L : ℕ} :
    Continuous (momentCoordinateEvaluation (n := n) (L := L)) := by
  apply continuous_pi
  intro i
  simpa only [momentCoordinateEvaluation_apply] using
    (MvPolynomial.continuous_eval
      ((Module.finBasis ℝ
        (MvPolynomial.restrictTotalDegree (Fin n) ℝ L)) i).1).comp
      continuous_subtype_val

/-- The finite moment-coordinate map is Bochner integrable for normalized
surface measure. -/
theorem integrable_momentCoordinateEvaluation {n L : ℕ} (hn : 0 < n) :
    Integrable (momentCoordinateEvaluation (n := n) (L := L))
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  exact continuous_momentCoordinateEvaluation.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

/-- Integrating the coordinate-valued evaluation map gives exactly the
coordinate vector of the normalized moment functional. -/
theorem integral_momentCoordinateEvaluation {n L : ℕ} (hn : 0 < n) :
    (∫ x : sphereSet n, momentCoordinateEvaluation (L := L) x
      ∂normalizedSphereMeasure n) =
      momentCoordinateFunctional (L := L) hn := by
  ext i
  rw [MeasureTheory.eval_integral]
  · simpa only [momentCoordinateEvaluation_apply] using
      (momentCoordinateFunctional_apply hn i).symm
  · intro j
    simpa only [momentCoordinateEvaluation_apply] using
      integrable_eval_normalizedSphereMeasure hn
        ((Module.finBasis ℝ
          (MvPolynomial.restrictTotalDegree (Fin n) ℝ L)) j).1

/-- The range of the moment-coordinate map is compact. -/
theorem isCompact_range_momentCoordinateEvaluation {n L : ℕ} :
    IsCompact (Set.range (momentCoordinateEvaluation (n := n) (L := L))) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  exact isCompact_range continuous_momentCoordinateEvaluation

/-- In a finite-dimensional real coordinate space, the convex hull of a
compact set is compact. The proof parametrizes every point of the hull by
`m + 1` simplex weights and nodes. Carathéodory bounds the support size, and
zero weights pad a smaller support to exactly `m + 1` slots. -/
theorem isCompact_convexHull_fin_pi (m : ℕ) {s : Set (Fin m → ℝ)}
    (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let I := Fin (m + 1)
  let P := (stdSimplex ℝ I) × (I → s)
  let barycenter : P → (Fin m → ℝ) := fun p ↦
    ∑ i, p.1.1 i • (p.2 i).1
  have hbarycenter : Continuous barycenter := by
    dsimp [barycenter, P]
    apply continuous_finset_sum _
    intro i _
    exact ((continuous_apply i).comp
        (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp
        ((continuous_apply i).comp continuous_snd))
  have hrange : Set.range barycenter = convexHull ℝ s := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, rfl⟩
      exact mem_convexHull_of_exists_fintype (fun i ↦ p.1.1 i)
        (fun i ↦ (p.2 i).1) p.1.2.1 p.1.2.2
        (fun i ↦ (p.2 i).2) rfl
    · intro x hx
      let t := Caratheodory.minCardFinsetOfMemConvexHull hx
      have ht_sub : (t : Set (Fin m → ℝ)) ⊆ s :=
        Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
      have ht_mem : x ∈ convexHull ℝ (t : Set (Fin m → ℝ)) :=
        Caratheodory.mem_minCardFinsetOfMemConvexHull hx
      have ht_aff : AffineIndependent ℝ ((↑) : t → (Fin m → ℝ)) :=
        Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
      obtain ⟨w, hw_nonneg, hw_sum, hw_center⟩ := Finset.mem_convexHull'.mp ht_mem
      have hcard : Fintype.card t ≤ m + 1 := by
        calc
          Fintype.card t ≤
              Module.finrank ℝ
                (vectorSpan ℝ (Set.range ((↑) : t → (Fin m → ℝ)))) + 1 :=
            ht_aff.card_le_finrank_succ
          _ ≤ Module.finrank ℝ (Fin m → ℝ) + 1 :=
            Nat.add_le_add_right (Submodule.finrank_le _) 1
          _ = m + 1 := by rw [Module.finrank_fin_fun]
      have hcard' : Fintype.card t ≤ Fintype.card I := by
        simpa [I] using hcard
      obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard'
      let z0 : s := ⟨hsne.some, hsne.some_mem⟩
      let W : I → ℝ := Function.extend e (fun i : t ↦ w i.1) (fun _ ↦ 0)
      let Z : I → s := Function.extend e
        (fun i : t ↦ ⟨i.1, ht_sub i.2⟩) (fun _ ↦ z0)
      have hW_nonneg : ∀ i, 0 ≤ W i := by
        intro i
        by_cases hi : ∃ j, e j = i
        · obtain ⟨j, rfl⟩ := hi
          simp [W, e.injective.extend_apply, hw_nonneg j.1 j.2]
        · simp [W, Function.extend_apply' _ _ _ hi]
      have hW_sum : ∑ i, W i = 1 := by
        calc
          ∑ i, W i = ∑ j : t, w j.1 := by
            symm
            apply Fintype.sum_of_injective e e.injective
              (fun j : t ↦ w j.1) W
            · intro i hi
              simp [W, Function.extend_apply' _ _ _ hi]
            · intro j
              simp [W, e.injective.extend_apply]
          _ = 1 := (Finset.sum_finset_coe w t).trans hw_sum
      have hcenter : ∑ i, W i • (Z i).1 = x := by
        calc
          ∑ i, W i • (Z i).1 = ∑ j : t, w j.1 • j.1 := by
            symm
            apply Fintype.sum_of_injective e e.injective
              (fun j : t ↦ w j.1 • j.1) (fun i ↦ W i • (Z i).1)
            · intro i hi
              simp [W, Function.extend_apply' _ _ _ hi]
            · intro j
              simp [W, Z, e.injective.extend_apply]
          _ = x := (Finset.sum_finset_coe (fun y ↦ w y • y) t).trans hw_center
      let a : stdSimplex ℝ I := ⟨W, hW_nonneg, hW_sum⟩
      refine ⟨(a, Z), ?_⟩
      exact hcenter
  rw [← hrange]
  exact isCompact_range hbarycenter

/-- Consequently, the convex hull of the moment-coordinate range is totally
bounded. Closedness is the only remaining ingredient needed for compactness. -/
theorem totallyBounded_convexHull_range_momentCoordinateEvaluation
    {n L : ℕ} :
    TotallyBounded (convexHull ℝ
      (Set.range (momentCoordinateEvaluation (n := n) (L := L)))) :=
  totallyBounded_convexHull _
    isCompact_range_momentCoordinateEvaluation.totallyBounded

/-- The remaining finite-dimensional topological input: the convex hull of the
compact moment-coordinate range is closed. -/
theorem isClosed_convexHull_range_momentCoordinateEvaluation_succ
    (n L : ℕ) :
    IsClosed (convexHull ℝ
      (Set.range (momentCoordinateEvaluation (n := n) (L := L + 1)))) :=
  (isCompact_convexHull_fin_pi _
    isCompact_range_momentCoordinateEvaluation).isClosed

/-- The normalized coordinate moment is in the algebraic convex hull of point
coordinates. The proof is the standard integral-in-a-closed-convex-set
argument; all analytic hypotheses are discharged by compactness. -/
theorem momentCoordinateFunctional_mem_convexHull_succ
    (n L : ℕ) (hn : 0 < n) :
    momentCoordinateFunctional (L := L + 1) hn ∈
      convexHull ℝ
        (Set.range (momentCoordinateEvaluation (n := n) (L := L + 1))) := by
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  rw [← integral_momentCoordinateEvaluation hn]
  exact (convex_convexHull ℝ _).integral_mem
    (isClosed_convexHull_range_momentCoordinateEvaluation_succ n L)
    (Filter.Eventually.of_forall fun x ↦
      subset_convexHull ℝ _ (Set.mem_range_self x))
    (integrable_momentCoordinateEvaluation hn)

/-- Exactness for every degree-`L` polynomial is equivalent to one barycenter
identity in the finite-dimensional dual polynomial space. -/
theorem exact_iff_moment_identity {n L N : ℕ} (hn : 0 < n)
    (Q : SpherePolynomialQuadrature n L N) :
    (∀ q : MvPolynomial (Fin n) ℝ, q.totalDegree ≤ L →
      ∑ i, Q.weight i * MvPolynomial.eval (Q.node i).1 q =
        ∫ x : sphereSet n, MvPolynomial.eval x.1 q
          ∂normalizedSphereMeasure n) ↔
      ∑ i, Q.weight i • momentEvaluation (L := L) (Q.node i) =
        momentFunctional (L := L) hn := by
  constructor
  · intro h
    ext q
    simpa [momentEvaluation, momentFunctional] using h q.1
      ((MvPolynomial.mem_restrictTotalDegree (Fin n) L q.1).mp q.2)
  · intro h q hq
    have hq' := DFunLike.congr_fun h
      (⟨q, (MvPolynomial.mem_restrictTotalDegree (Fin n) L q).mpr hq⟩ :
        MvPolynomial.restrictTotalDegree (Fin n) ℝ L)
    simpa [momentEvaluation, momentFunctional] using hq'

/-- Build an exact quadrature directly from a positive finite barycenter
identity in the dual bounded-degree polynomial space. -/
noncomputable def ofMomentIdentity {n L N : ℕ} (hn : 0 < n)
    (w : Fin N → ℝ) (y : Fin N → sphereSet n)
    (hw : ∀ i, 0 ≤ w i)
    (hmoment :
      ∑ i, w i • momentEvaluation (L := L) (y i) =
        momentFunctional (L := L) hn) :
    SpherePolynomialQuadrature n L N where
  weight := w
  node := y
  weight_nonneg := hw
  exact q hq := by
    have hq' := DFunLike.congr_fun hmoment
      (⟨q, (MvPolynomial.mem_restrictTotalDegree (Fin n) L q).mpr hq⟩ :
        MvPolynomial.restrictTotalDegree (Fin n) ℝ L)
    simpa [momentEvaluation, momentFunctional] using hq'

/-- One node with weight one is an exact positive quadrature for constants. -/
theorem exists_exact_zero (n : ℕ) (hn : 0 < n) :
    Nonempty (SpherePolynomialQuadrature n 0 1) := by
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  obtain ⟨x, hx⟩ := sphereSet_nonempty hn
  refine ⟨
    { weight := fun _ ↦ 1
      node := fun _ ↦ ⟨x, hx⟩
      weight_nonneg := by intro i; positivity
      exact := ?_ }⟩
  intro q hq
  have hqzero : q.totalDegree = 0 := Nat.eq_zero_of_le_zero hq
  have hqconst := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).1 hqzero
  rw [hqconst]
  simp

/-- Transport coordinate-space convex-hull membership back through the dual
basis equivalence. This is purely finite-dimensional linear algebra. -/
theorem momentFunctional_mem_convexHull_succ (n L : ℕ) (hn : 0 < n) :
    momentFunctional (L := L + 1) hn ∈
      convexHull ℝ (Set.range (momentEvaluation (n := n) (L := L + 1))) := by
  obtain ⟨ι, instι, w, z, hw, hsum, hz, hmoment⟩ :=
    mem_convexHull_iff_exists_fintype.mp
      (momentCoordinateFunctional_mem_convexHull_succ n L hn)
  letI : Fintype ι := instι
  choose y hy using hz
  refine mem_convexHull_of_exists_fintype w
    (fun i ↦ momentEvaluation (L := L + 1) (y i)) hw hsum
    (fun i ↦ Set.mem_range_self (y i)) ?_
  let b := Module.finBasis ℝ
    (MvPolynomial.restrictTotalDegree (Fin n) ℝ (L + 1))
  apply b.dualBasis.equivFun.injective
  calc
    b.dualBasis.equivFun
        (∑ i, w i • momentEvaluation (L := L + 1) (y i)) =
      ∑ i, w i • momentCoordinateEvaluation (L := L + 1) (y i) := by
        simp [b, momentCoordinateEvaluation]
    _ = ∑ i, w i • z i := by simp_rw [hy]
    _ = momentCoordinateFunctional (L := L + 1) hn := hmoment
    _ = b.dualBasis.equivFun (momentFunctional (L := L + 1) hn) := by
      rfl

/-- The positive-degree Tchakaloff/Carathéodory discretization step, obtained
from the finite barycentric representation supplied by convex-hull membership. -/
theorem exists_exact_succ (n L : ℕ) (hn : 0 < n) :
    ∃ N : ℕ, Nonempty (SpherePolynomialQuadrature n (L + 1) N) := by
  obtain ⟨ι, instι, w, z, hw, _hsum, hz, hmoment⟩ :=
    mem_convexHull_iff_exists_fintype.mp
      (momentFunctional_mem_convexHull_succ n L hn)
  letI : Fintype ι := instι
  choose y hy using hz
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let w' : Fin (Fintype.card ι) → ℝ := fun j ↦ w (e.symm j)
  let y' : Fin (Fintype.card ι) → sphereSet n := fun j ↦ y (e.symm j)
  have hw' : ∀ j, 0 ≤ w' j := fun j ↦ hw (e.symm j)
  have hmoment' :
      ∑ j, w' j • momentEvaluation (L := L + 1) (y' j) =
        momentFunctional (L := L + 1) hn := by
    calc
      _ = ∑ i : ι, w i • momentEvaluation (L := L + 1) (y i) := by
        simpa [w', y', e] using
          (e.symm.sum_comp
            (fun i : ι ↦ w i • momentEvaluation (L := L + 1) (y i)))
      _ = ∑ i : ι, w i • z i := by simp_rw [hy]
      _ = momentFunctional (L := L + 1) hn := hmoment
  exact ⟨Fintype.card ι, ⟨ofMomentIdentity hn w' y' hw' hmoment'⟩⟩

/-- Exact positive quadratures exist in every degree; degree zero is the
explicit one-node construction, and positive degrees use the finite-dimensional
Carathéodory compact-convex-hull argument above. -/
theorem exists_exact (n L : ℕ) (hn : 0 < n) :
    ∃ N : ℕ, Nonempty (SpherePolynomialQuadrature n L N) := by
  cases L with
  | zero => exact ⟨1, exists_exact_zero n hn⟩
  | succ L => simpa [Nat.succ_eq_add_one] using exists_exact_succ n L hn

end SpherePolynomialQuadrature

end QuarticConvergence
end OptimalConvergenceRates

end
