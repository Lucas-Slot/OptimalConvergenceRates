/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/FiniteAtomFilter.lean

  Scale-resolved finite retained roots and their Boolean-filter estimates.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.AtomSummation
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FinitePacking
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Localization
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Repair
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.ContinuousRootFilter
import Mathlib.RingTheory.MvPowerSeries.PiTopology

open MvPolynomial Finset Set
open scoped BigOperators MvPowerSeries.WithPiTopology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers
open SpherePolynomialQuadrature

/-- Concrete finite-resolution output required from the atom decomposition and
Boolean filter. The three pointwise estimates are exactly the cross, square-error,
and discarded-remainder terms in the final summation. -/
def HasFiniteFilteredRootApproximation (n : ℕ) (C : ℝ) (b k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ,
    SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k →
      ∃ (N : ℕ) (a : Fin N → ((Fin n → ℝ) → ℝ))
          (p : Fin N → MvPolynomial (Fin n) ℝ),
        (∀ i, (p i).totalDegree ≤ b * k) ∧
        (∀ x ∈ sphereSet n,
          ∑ i, |a i x * (MvPolynomial.eval x (p i) - a i x)| ≤
            C / (4 * (k : ℝ) ^ 4)) ∧
        (∀ x ∈ sphereSet n,
          ∑ i, (MvPolynomial.eval x (p i) - a i x) ^ 2 ≤
            C / (4 * (k : ℝ) ^ 4)) ∧
        (∀ x ∈ sphereSet n,
          |MvPolynomial.eval x F - ∑ i, (a i x) ^ 2| ≤
            C / (4 * (k : ℝ) ^ 4))

/-- Scale-resolved retained-root data used by the quartic approximation. Besides the final
remainder estimate, this records the geometric information that is lost in the
coarser `HasFiniteFilteredRootApproximation` interface:

* every retained root has a positive radius between `1 / k` and `1` and is
  supported in its own chordal cap;
* only `overlapBound` roots are active at any sphere point;
* active cross-error summands have a uniform pointwise bound;
* squared errors are controlled separately on finitely many dyadic scales.

The last two aggregate budgets are deliberately fields: the analytic construction
is free to choose its intermediate constants, while the summation lemmas below
verify that they fit the public `C / (4 k⁴)` budget. -/
structure FiniteFilteredRootScaleData (n : ℕ) (C : ℝ) (k : ℕ)
    (F : MvPolynomial (Fin n) ℝ) where
  N : ℕ
  J : ℕ
  root : Fin N → ((Fin n → ℝ) → ℝ)
  polynomial : Fin N → MvPolynomial (Fin n) ℝ
  base : sphereSet n
  center : Fin N → sphereSet n
  radius : Fin N → ℝ
  scale : Fin N → Fin J
  overlapBound : ℕ
  crossAtomBound : ℝ
  squareScaleBound : ℝ
  squareMajorant : Fin N → ((Fin n → ℝ) → ℝ)
  root_coeff_integrable : ∀ i,
    ZonalKernelCoeffIntegrable (n + 3) k (fun y ↦ root i y.1)
  first_filter_coeff_integrable : ∀ i,
    ZonalKernelCoeffIntegrable (n + 3) k (fun y ↦
      MvPolynomial.eval y.1
        (normalizedFunctionZonalKernelPolynomial (n + 3) k base (fun z ↦ root i z.1)))
  polynomial_eq_booleanFilter : ∀ i,
    polynomial i = booleanFilteredFunctionPolynomial (n + 3) k base
      (fun y ↦ root i y.1)
  radius_pos : ∀ i, 0 < radius i
  radius_lower : ∀ i, 1 / (k : ℝ) ≤ radius i
  radius_upper : ∀ i, radius i ≤ 1
  supported : ∀ i x (hx : x ∈ sphereSet n), root i x ≠ 0 →
    (⟨x, hx⟩ : sphereSet n) ∈ sphereChordalCap (center i) (radius i)
  cap_overlap_card : ∀ x (_hx : x ∈ sphereSet n),
    (Finset.univ.filter fun i =>
      sphereChordalSq x (center i).1 ≤ (radius i) ^ 2).card ≤
        overlapBound
  crossAtomBound_nonneg : 0 ≤ crossAtomBound
  active_cross : ∀ x ∈ sphereSet n, ∀ i, root i x ≠ 0 →
    |root i x * (MvPolynomial.eval x (polynomial i) - root i x)| ≤
      crossAtomBound
  cross_budget : (overlapBound : ℝ) * crossAtomBound ≤
    C / (4 * (k : ℝ) ^ 4)
  squareScaleBound_nonneg : 0 ≤ squareScaleBound
  square_error_le_majorant : ∀ x ∈ sphereSet n, ∀ i,
    (MvPolynomial.eval x (polynomial i) - root i x) ^ 2 ≤ squareMajorant i x
  scale_packing : ∀ x ∈ sphereSet n, ∀ j : Fin J,
    ∑ i ∈ Finset.univ.filter (fun i => scale i = j), squareMajorant i x ≤
      squareScaleBound * (1 / 16 : ℝ) ^ (j : ℕ)
  square_budget : (16 / 15 : ℝ) * squareScaleBound ≤
    C / (4 * (k : ℝ) ^ 4)
  remainder : ∀ x ∈ sphereSet n,
    |MvPolynomial.eval x F - ∑ i, (root i x) ^ 2| ≤
      C / (4 * (k : ℝ) ^ 4)

/-- The public scale data derives active-root overlap from support containment
and the stronger supporting-cap overlap invariant. -/
theorem FiniteFilteredRootScaleData.active_card
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteFilteredRootScaleData n C k F) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) :
    (Finset.univ.filter fun i => data.root i x ≠ 0).card ≤ data.overlapBound := by
  refine (Finset.card_le_card ?_).trans (data.cap_overlap_card x hx)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hsupported := data.supported i x hx hi
  simpa [sphereChordalCap] using hsupported

/-- Uniform existence of scale-resolved data for every normalized nonnegative
sphere polynomial. -/
def HasFiniteFilteredRootScaleData (n : ℕ) (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ,
    SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k → Nonempty (FiniteFilteredRootScaleData n C k F)


/-- The retained-atom part of `FiniteFilteredRootScaleData`, before any
Boolean-filter estimates are used.  This is the finite-resolution export of
the smooth atom decomposition. -/
structure FiniteRetainedRootData (n : ℕ) (C : ℝ) (k : ℕ)
    (F : MvPolynomial (Fin n) ℝ) where
  N : ℕ
  J : ℕ
  root : Fin N → ((Fin n → ℝ) → ℝ)
  base : sphereSet n
  center : Fin N → sphereSet n
  radius : Fin N → ℝ
  scale : Fin N → Fin J
  overlapBound : ℕ
  radius_pos : ∀ i, 0 < radius i
  radius_lower : ∀ i, 1 / (k : ℝ) ≤ radius i
  radius_upper : ∀ i, radius i ≤ 1
  supported : ∀ i x (hx : x ∈ sphereSet n), root i x ≠ 0 →
    (⟨x, hx⟩ : sphereSet n) ∈ sphereChordalCap (center i) (radius i)
  cap_overlap_card : ∀ x (_hx : x ∈ sphereSet n),
    (Finset.univ.filter fun i =>
      sphereChordalSq x (center i).1 ≤ (radius i) ^ 2).card ≤
        overlapBound
  remainder : ∀ x ∈ sphereSet n,
    |MvPolynomial.eval x F - ∑ i, (root i x) ^ 2| ≤
      C / (4 * (k : ℝ) ^ 4)

/-- Forget the Boolean-filter estimates while retaining the finite atom
decomposition, its scale labels, and its discarded-tail estimate. -/
def FiniteFilteredRootScaleData.toRetainedRootData
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteFilteredRootScaleData n C k F) :
    FiniteRetainedRootData n C k F where
  N := data.N
  J := data.J
  root := data.root
  base := data.base
  center := data.center
  radius := data.radius
  scale := data.scale
  overlapBound := data.overlapBound
  radius_pos := data.radius_pos
  radius_lower := data.radius_lower
  radius_upper := data.radius_upper
  supported := data.supported
  cap_overlap_card := data.cap_overlap_card
  remainder := data.remainder

/-- Support containment turns overlap of the supporting caps into overlap of
the roots that are actually nonzero at a sphere point. -/
theorem FiniteRetainedRootData.active_card_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) :
    (Finset.univ.filter fun i => atoms.root i x ≠ 0).card ≤ atoms.overlapBound := by
  refine (Finset.card_le_card ?_).trans (atoms.cap_overlap_card x hx)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hsupported := atoms.supported i x hx hi
  simpa [sphereChordalCap] using hsupported

/-- The Boolean-filter half of the finite-resolution construction, stated
relative to already constructed retained atoms. -/
structure FiniteBooleanFilterData
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) where
  polynomial : Fin atoms.N → MvPolynomial (Fin n) ℝ
  crossAtomBound : ℝ
  squareScaleBound : ℝ
  squareMajorant : Fin atoms.N → ((Fin n → ℝ) → ℝ)
  root_coeff_integrable : ∀ i,
    ZonalKernelCoeffIntegrable (n + 3) k (fun y ↦ atoms.root i y.1)
  first_filter_coeff_integrable : ∀ i,
    ZonalKernelCoeffIntegrable (n + 3) k (fun y ↦
      MvPolynomial.eval y.1
        (normalizedFunctionZonalKernelPolynomial (n + 3) k atoms.base
          (fun z ↦ atoms.root i z.1)))
  polynomial_eq_booleanFilter : ∀ i,
    polynomial i = booleanFilteredFunctionPolynomial (n + 3) k atoms.base
      (fun y ↦ atoms.root i y.1)
  crossAtomBound_nonneg : 0 ≤ crossAtomBound
  active_cross : ∀ x ∈ sphereSet n, ∀ i, atoms.root i x ≠ 0 →
    |atoms.root i x * (MvPolynomial.eval x (polynomial i) - atoms.root i x)| ≤
      crossAtomBound
  cross_budget : (atoms.overlapBound : ℝ) * crossAtomBound ≤
    C / (4 * (k : ℝ) ^ 4)
  squareScaleBound_nonneg : 0 ≤ squareScaleBound
  square_error_le_majorant : ∀ x ∈ sphereSet n, ∀ i,
    (MvPolynomial.eval x (polynomial i) - atoms.root i x) ^ 2 ≤ squareMajorant i x
  scale_packing : ∀ x ∈ sphereSet n, ∀ j : Fin atoms.J,
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j), squareMajorant i x ≤
      squareScaleBound * (1 / 16 : ℝ) ^ (j : ℕ)
  square_budget : (16 / 15 : ℝ) * squareScaleBound ≤
    C / (4 * (k : ℝ) ^ 4)

/-- Project the filter estimates from combined scale data. -/
def FiniteFilteredRootScaleData.toBooleanFilterData
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteFilteredRootScaleData n C k F) :
    FiniteBooleanFilterData data.toRetainedRootData where
  polynomial := data.polynomial
  crossAtomBound := data.crossAtomBound
  squareScaleBound := data.squareScaleBound
  squareMajorant := data.squareMajorant
  root_coeff_integrable := data.root_coeff_integrable
  first_filter_coeff_integrable := data.first_filter_coeff_integrable
  polynomial_eq_booleanFilter := data.polynomial_eq_booleanFilter
  crossAtomBound_nonneg := data.crossAtomBound_nonneg
  active_cross := data.active_cross
  cross_budget := data.cross_budget
  squareScaleBound_nonneg := data.squareScaleBound_nonneg
  square_error_le_majorant := data.square_error_le_majorant
  scale_packing := data.scale_packing
  square_budget := data.square_budget

/-- Recombine retained atoms with their Boolean-filter estimates.  Downstream
code therefore continues to consume the original combined API. -/
def FiniteRetainedRootData.withBooleanFilterData
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F)
    (filter : FiniteBooleanFilterData atoms) :
    FiniteFilteredRootScaleData n C k F where
  N := atoms.N
  J := atoms.J
  root := atoms.root
  polynomial := filter.polynomial
  base := atoms.base
  center := atoms.center
  radius := atoms.radius
  scale := atoms.scale
  overlapBound := atoms.overlapBound
  crossAtomBound := filter.crossAtomBound
  squareScaleBound := filter.squareScaleBound
  squareMajorant := filter.squareMajorant
  root_coeff_integrable := filter.root_coeff_integrable
  first_filter_coeff_integrable := filter.first_filter_coeff_integrable
  polynomial_eq_booleanFilter := filter.polynomial_eq_booleanFilter
  radius_pos := atoms.radius_pos
  radius_lower := atoms.radius_lower
  radius_upper := atoms.radius_upper
  supported := atoms.supported
  crossAtomBound_nonneg := filter.crossAtomBound_nonneg
  cap_overlap_card := atoms.cap_overlap_card
  active_cross := filter.active_cross
  cross_budget := filter.cross_budget
  squareScaleBound_nonneg := filter.squareScaleBound_nonneg
  square_error_le_majorant := filter.square_error_le_majorant
  scale_packing := filter.scale_packing
  square_budget := filter.square_budget
  remainder := atoms.remainder

@[simp] theorem FiniteRetainedRootData.withBooleanFilterData_toRetainedRootData
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F)
    (filter : FiniteBooleanFilterData atoms) :
    (atoms.withBooleanFilterData filter).toRetainedRootData = atoms := by
  cases atoms
  rfl

/-- Continuity of each bounded-degree coefficient of the zonal kernel as its
center varies.  This is a finite algebraic property of the explicit kernel. -/
def ZonalKernelCoeffContinuous {n : ℕ} (p k : ℕ) : Prop :=
  ∀ α : ExpLE n (2 * (p * k)),
    Continuous (fun y : sphereSet n ↦
      MvPolynomial.coeff α.1 (sphereDirichletZonalKernel p k y.1))

/-- Kernel coefficient continuity follows from the coefficientwise topology
on multivariate power series and the explicit polynomial kernel formula. -/
theorem zonalKernelCoeffContinuous {n : ℕ} (p k : ℕ) :
    ZonalKernelCoeffContinuous (n := n) p k := by
  intro α
  let φ : MvPolynomial (Fin n) ℝ →+* MvPowerSeries (Fin n) ℝ :=
    MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := ℝ)
  change Continuous (fun y : sphereSet n ↦
    MvPowerSeries.coeff α.1 (φ (sphereDirichletZonalKernel p k y.1)))
  unfold sphereDirichletZonalKernel sphereDirichletZonalRoot sphereDotPolynomial
  simp_rw [Polynomial.eval₂_eq_sum_range]
  simp_rw [map_pow, map_sum, map_mul]
  simp_rw [map_pow, map_sum, map_mul]
  have hφ (q : MvPolynomial (Fin n) ℝ) :
      φ q = (q : MvPowerSeries (Fin n) ℝ) := rfl
  simp_rw [hφ, MvPolynomial.coe_C, MvPolynomial.coe_X]
  apply (MvPowerSeries.WithPiTopology.continuous_coeff ℝ α.1).comp
  have hcoordinate (j : Fin n) : Continuous (fun y : sphereSet n ↦
      MvPowerSeries.C (σ := Fin n) (R := ℝ) (y.1 j)) :=
    MvPowerSeries.WithPiTopology.continuous_C.comp
      ((continuous_apply j).comp continuous_subtype_val)
  have hdot : Continuous (fun y : sphereSet n ↦
      ∑ j, MvPowerSeries.C (R := ℝ) (y.1 j) * MvPowerSeries.X j) := by
    exact continuous_finset_sum _ fun j _ ↦ (hcoordinate j).mul continuous_const
  have hsum : Continuous (fun y : sphereSet n ↦
      ∑ i ∈ Finset.range ((sphereDirichletPolynomial k).natDegree + 1),
        MvPowerSeries.C (R := ℝ) ((sphereDirichletPolynomial k).coeff i) *
          (∑ j, MvPowerSeries.C (R := ℝ) (y.1 j) *
            MvPowerSeries.X j) ^ i) := by
    exact continuous_finset_sum _ fun i _ ↦ continuous_const.mul (hdot.pow i)
  exact (hsum.pow p).pow 2

/-- Continuous sphere functions satisfy the coefficientwise integrability
needed by `functionZonalKernelPolynomial`, provided the explicit kernel
coefficient sections are continuous. -/
theorem zonalKernelCoeffIntegrable_of_continuous
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (v : sphereSet n → ℝ)
    (hv : Continuous v) (hcoeff : ZonalKernelCoeffContinuous (n := n) p k) :
    ZonalKernelCoeffIntegrable p k v := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  intro α
  apply Continuous.integrable_of_hasCompactSupport
  · exact hv.mul (hcoeff α)
  · exact (isCompact_univ : IsCompact (Set.univ : Set (sphereSet n))).of_isClosed_subset
      (isClosed_tsupport _) (Set.subset_univ _)

/-- The stored polynomial is the actual Booleanization of the normalized
coefficient-integrated zonal operator. -/
theorem FiniteFilteredRootScaleData.eval_polynomial_eq_booleanFilter
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteFilteredRootScaleData n C k F) (i : Fin data.N)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x (data.polynomial i) =
      booleanFilteredFunctionValue (n + 3) k data.base (fun y ↦ data.root i y.1) x := by
  rw [data.polynomial_eq_booleanFilter i]
  exact eval_booleanFilteredFunctionPolynomial (n + 3) k data.base
    (fun y ↦ data.root i y.1) (data.root_coeff_integrable i)
    (data.first_filter_coeff_integrable i) x

/-- Booleanization does not double the kernel range: every filtered root has
the exact degree multiplier `2 * (n + 3)`. -/
theorem FiniteFilteredRootScaleData.polynomial_totalDegree_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteFilteredRootScaleData n C k F) (i : Fin data.N) :
    (data.polynomial i).totalDegree ≤ (2 * (n + 3)) * k := by
  rw [data.polynomial_eq_booleanFilter i]
  simpa only [Nat.mul_assoc] using
    booleanFilteredFunctionPolynomial_totalDegree_le (n + 3) k data.base
      (fun y ↦ data.root i y.1)

/-- Active-overlap converts the per-root cross estimate in scale data into the
full cross-error estimate needed by finite-square assembly. -/
theorem FiniteFilteredRootScaleData.cross_error_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteFilteredRootScaleData n C k F) :
    ∀ x ∈ sphereSet n,
      ∑ i,
          |data.root i x *
            (MvPolynomial.eval x (data.polynomial i) - data.root i x)| ≤
        C / (4 * (k : ℝ) ^ 4) := by
  intro x hx
  exact (sum_abs_mul_le_of_active_card
    (fun i => data.root i x)
    (fun i => MvPolynomial.eval x (data.polynomial i) - data.root i x)
    data.overlapBound data.crossAtomBound data.crossAtomBound_nonneg
    (data.active_card x hx) (data.active_cross x hx)).trans data.cross_budget

/-- Dyadic packing converts the per-scale squared-error estimates in scale data
into the full squared-error estimate needed by finite-square assembly. -/
theorem FiniteFilteredRootScaleData.square_error_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteFilteredRootScaleData n C k F) :
    ∀ x ∈ sphereSet n,
      ∑ i, (MvPolynomial.eval x (data.polynomial i) - data.root i x) ^ 2 ≤
        C / (4 * (k : ℝ) ^ 4) := by
  intro x hx
  exact (sum_sq_le_of_dyadic_fibers data.scale
    (fun i => MvPolynomial.eval x (data.polynomial i) - data.root i x)
    data.squareScaleBound data.squareScaleBound_nonneg (fun j =>
      (Finset.sum_le_sum fun i _ => data.square_error_le_majorant x hx i).trans
        (data.scale_packing x hx j))).trans data.square_budget

/-- Forgetting centers, radii, overlap, and dyadic scale labels turns the
scale-resolved data into the coarse three-error interface. -/
theorem finiteFilteredRootApproximation_of_scaleData
    {n : ℕ} {C : ℝ} {k₀ : ℕ}
    (hdata : HasFiniteFilteredRootScaleData n C k₀) :
    HasFiniteFilteredRootApproximation n C (2 * (n + 3)) k₀ := by
  intro F hF hnorm k hk
  let data := Classical.choice (hdata F hF hnorm k hk)
  refine ⟨data.N, data.root, data.polynomial, data.polynomial_totalDegree_le,
    ?_, ?_, data.remainder⟩
  · exact data.cross_error_le
  · exact data.square_error_le


/-- Scaled ambient C4 control for the compact radial extensions of retained
roots.  The inequality is the division-free form of
`‖D^j aᵢ‖ ≤ A * ρᵢ^(2-j)`. -/
structure FiniteRetainedRootRegularity
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) where
  jetBound : ℝ
  jetBound_nonneg : 0 ≤ jetBound
  root_contDiff : ∀ i, ContDiff ℝ 4 (atoms.root i)
  scaled_jet : ∀ i j, j ≤ 4 → ∀ x,
    ‖iteratedFDeriv ℝ j (atoms.root i) x‖ * atoms.radius i ^ j ≤
      jetBound * atoms.radius i ^ 2

/-- The scale label records the dyadic interval containing each retained
radius, starting at the resolution `1 / k`. -/
structure FiniteRetainedRootDyadic
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) : Type where
  scale_lower : ∀ i,
    (2 : ℝ) ^ (atoms.scale i : ℕ) / (k : ℝ) ≤ atoms.radius i
  scale_upper : ∀ i,
    atoms.radius i <
      (2 : ℝ) ^ ((atoms.scale i : ℕ) + 1) / (k : ℝ)


/-- A regular retained root has all coefficient integrals required by the
zonal operator once kernel coefficient continuity is available. -/
theorem FiniteRetainedRootRegularity.root_coeff_integrable
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n)
    (hcoeff : ZonalKernelCoeffContinuous (n := n) (n + 3) k) (i : Fin atoms.N) :
    ZonalKernelCoeffIntegrable (n + 3) k (fun y ↦ atoms.root i y.1) := by
  apply zonalKernelCoeffIntegrable_of_continuous hn
  · exact (regular.root_contDiff i).continuous.comp continuous_subtype_val
  · exact hcoeff

/-- Polynomial evaluation supplies the coefficient integrals needed for the
second application of the Boolean filter. -/
theorem zonalKernelCoeffIntegrable_eval
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (q : MvPolynomial (Fin n) ℝ)
    (hcoeff : ZonalKernelCoeffContinuous (n := n) p k) :
    ZonalKernelCoeffIntegrable p k (fun y ↦ MvPolynomial.eval y.1 q) := by
  apply zonalKernelCoeffIntegrable_of_continuous hn
  · exact (MvPolynomial.continuous_eval q).comp continuous_subtype_val
  · exact hcoeff

/-- The raw Dirichlet-square kernel has a single pointwise envelope combining
its peak bound with its reciprocal-distance tail bound.  This is the scalar
localization estimate needed before dividing by the kernel mass. -/
theorem eval_sphereDirichletZonalKernel_mul_localizationFactor_le
    {n : ℕ} (p k : ℕ) (hk : 1 ≤ k) (x y : sphereSet n) :
    MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) *
        (1 + (k : ℝ) * sphereAngularDistance y x) ^ (2 * p) ≤
      (8 * (k : ℝ)) ^ (2 * p) := by
  let θ := sphereAngularDistance y x
  have hkreal : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : 0 ≤ (k : ℝ) := hkreal.trans' zero_le_one
  have hθ0 : 0 ≤ θ := sphereAngularDistance_nonneg y x
  have hkernel : 0 ≤
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) :=
    eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1
  by_cases hnear : (k : ℝ) * θ ≤ 1
  · have hfactor : 1 + (k : ℝ) * θ ≤ 2 := by linarith
    have hpeak := eval_sphereDirichletZonalKernel_le_peak p k y.2 x.2
    have hpeak' :
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) ≤
          (3 * (k : ℝ)) ^ (2 * p) := by
      exact hpeak.trans (pow_le_pow_left₀ (by positivity) (by nlinarith) _)
    calc
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) *
          (1 + (k : ℝ) * θ) ^ (2 * p) ≤
          (3 * (k : ℝ)) ^ (2 * p) * 2 ^ (2 * p) :=
        mul_le_mul hpeak' (pow_le_pow_left₀ (by positivity) hfactor _)
          (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)
      _ = (6 * (k : ℝ)) ^ (2 * p) := by rw [← mul_pow]; congr 1; ring
      _ ≤ (8 * (k : ℝ)) ^ (2 * p) :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) _
  · have hfar : 1 < (k : ℝ) * θ := lt_of_not_ge hnear
    have hθpos : 0 < θ := by
      by_contra h
      have : θ = 0 := le_antisymm (le_of_not_gt h) hθ0
      norm_num [this] at hfar
    have hfactor : 1 + (k : ℝ) * θ ≤ 2 * ((k : ℝ) * θ) := by linarith
    have htail := eval_sphereDirichletZonalKernel_le_pi_div_angularDistance_pow
      p k x y hθpos
    calc
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) *
          (1 + (k : ℝ) * θ) ^ (2 * p) ≤
          (Real.pi / θ) ^ (2 * p) * (2 * ((k : ℝ) * θ)) ^ (2 * p) :=
        mul_le_mul htail (pow_le_pow_left₀ (by positivity) hfactor _)
          (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)
      _ = (2 * Real.pi * (k : ℝ)) ^ (2 * p) := by
        rw [← mul_pow]
        congr 1
        field_simp [hθpos.ne']
      _ ≤ (8 * (k : ℝ)) ^ (2 * p) := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_le_four]) hk0

/-- The square root of the algebraic chordal square is exactly the ambient
Euclidean metric distance after applying the repository's sphere equivalence. -/
theorem sqrt_sphereChordalSq_eq_dist_sphereSetEuclideanCoordinates
    {n : ℕ} (x y : sphereSet n) :
    Real.sqrt (sphereChordalSq x.1 y.1) =
      dist (sphereSetEuclideanCoordinates x)
        (sphereSetEuclideanCoordinates y) := by
  have hsq := sphereChordalSq_euclideanSphereCoordinates_eq_dist_sq
    (sphereSetEuclideanCoordinates x) (sphereSetEuclideanCoordinates y)
  change sphereChordalSq x.1 y.1 =
      dist (sphereSetEuclideanCoordinates x)
        (sphereSetEuclideanCoordinates y) ^ 2 at hsq
  rw [hsq, Real.sqrt_sq (dist_nonneg)]

/-- Chordal distance therefore satisfies the triangle inequality directly,
without requiring a separate geodesic-metric API. -/
theorem sqrt_sphereChordalSq_triangle {n : ℕ} (x y z : sphereSet n) :
    Real.sqrt (sphereChordalSq x.1 z.1) ≤
      Real.sqrt (sphereChordalSq x.1 y.1) +
        Real.sqrt (sphereChordalSq y.1 z.1) := by
  rw [sqrt_sphereChordalSq_eq_dist_sphereSetEuclideanCoordinates,
    sqrt_sphereChordalSq_eq_dist_sphereSetEuclideanCoordinates,
    sqrt_sphereChordalSq_eq_dist_sphereSetEuclideanCoordinates]
  exact dist_triangle _ _ _

/-- The normalized positive kernel section, with normalization fixed at the
same base point used by the continuous zonal operator. -/
noncomputable def normalizedZonalKernelSection {n : ℕ}
    (p k : ℕ) (base x y : sphereSet n) : ℝ :=
  MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) /
    continuousZonalKernelMass p k base.1

theorem normalizedZonalKernelSection_nonneg {n : ℕ} (hn : 0 < n)
    (p k : ℕ) (base x y : sphereSet n) :
    0 ≤ normalizedZonalKernelSection p k base x y := by
  exact div_nonneg
    (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)
    (continuousZonalKernelMass_pos hn p k base.1 base.2).le

theorem normalizedZonalKernelSection_comm {n : ℕ}
    (p k : ℕ) (base x y : sphereSet n) :
    normalizedZonalKernelSection p k base x y =
      normalizedZonalKernelSection p k base y x := by
  unfold normalizedZonalKernelSection
  rw [eval_sphereDirichletZonalKernel_comm]

/-- Every row of the normalized kernel integrates to one; center-independence
of the raw mass is the only invariance input. -/
theorem integral_normalizedZonalKernelSection_eq_one {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base x : sphereSet n) :
    ∫ y : sphereSet n, normalizedZonalKernelSection p k base x y
        ∂normalizedSphereMeasure n = 1 := by
  unfold normalizedZonalKernelSection
  rw [MeasureTheory.integral_div]
  change continuousZonalKernelMass p k x.1 /
      continuousZonalKernelMass p k base.1 = 1
  rw [continuousZonalKernelMass_eq_on_sphere hn p k x base]
  exact div_self (continuousZonalKernelMass_pos (by omega) p k base.1 base.2).ne'

/-- The previously defined continuous operator is integration against the
normalized kernel section. -/
theorem normalizedFunctionZonalKernelValue_eq_integral_section {n : ℕ}
    (p k : ℕ) (base x : sphereSet n) (v : sphereSet n → ℝ) :
    normalizedFunctionZonalKernelValue p k base v x.1 =
      ∫ y : sphereSet n, normalizedZonalKernelSection p k base x y * v y
        ∂normalizedSphereMeasure n := by
  unfold normalizedFunctionZonalKernelValue normalizedZonalKernelSection
  rw [← MeasureTheory.integral_div]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [eval_sphereDirichletZonalKernel_comm]
  ring

/-- Continuity in the integration variable of a normalized kernel row. -/
theorem continuous_normalizedZonalKernelSection_right {n : ℕ}
    (p k : ℕ) (base x : sphereSet n) :
    Continuous (fun y : sphereSet n ↦ normalizedZonalKernelSection p k base x y) := by
  unfold normalizedZonalKernelSection
  exact (continuous_sphereDirichletZonalKernel_section p k x.1).div_const _

/-- Symmetry also gives continuity in the center variable. -/
theorem continuous_normalizedZonalKernelSection_left {n : ℕ}
    (p k : ℕ) (base y : sphereSet n) :
    Continuous (fun x : sphereSet n ↦ normalizedZonalKernelSection p k base x y) := by
  have h := continuous_normalizedZonalKernelSection_right p k base y
  convert h using 1
  funext x
  exact normalizedZonalKernelSection_comm p k base x y

theorem integrable_normalizedZonalKernelSection_right {n : ℕ} (hn : 0 < n)
    (p k : ℕ) (base x : sphereSet n) :
    MeasureTheory.Integrable
      (fun y : sphereSet n ↦ normalizedZonalKernelSection p k base x y)
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact continuous_normalizedZonalKernelSection_right p k base x
  · exact (isCompact_univ : IsCompact (Set.univ : Set (sphereSet n))).of_isClosed_subset
      (isClosed_tsupport _) (Set.subset_univ _)

theorem integrable_normalizedZonalKernelSection_left {n : ℕ} (hn : 0 < n)
    (p k : ℕ) (base y : sphereSet n) :
    MeasureTheory.Integrable
      (fun x : sphereSet n ↦ normalizedZonalKernelSection p k base x y)
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact continuous_normalizedZonalKernelSection_left p k base y
  · exact (isCompact_univ : IsCompact (Set.univ : Set (sphereSet n))).of_isClosed_subset
      (isClosed_tsupport _) (Set.subset_univ _)

/-- Symmetry turns row normalization into column normalization. -/
theorem integral_normalizedZonalKernelSection_left_eq_one {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base y : sphereSet n) :
    ∫ x : sphereSet n, normalizedZonalKernelSection p k base x y
        ∂normalizedSphereMeasure n = 1 := by
  calc
    (∫ x : sphereSet n, normalizedZonalKernelSection p k base x y
        ∂normalizedSphereMeasure n) =
        ∫ x : sphereSet n, normalizedZonalKernelSection p k base y x
          ∂normalizedSphereMeasure n := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact normalizedZonalKernelSection_comm p k base x y
    _ = 1 := integral_normalizedZonalKernelSection_eq_one hn p k base y

/-- Two normalized kernel sections have an integrable product on the compact sphere. -/
theorem integrable_normalizedZonalKernelSection_mul {n : ℕ} (hn : 0 < n)
    (p k : ℕ) (base x y : sphereSet n) :
    MeasureTheory.Integrable (fun z : sphereSet n ↦
      normalizedZonalKernelSection p k base x z *
        normalizedZonalKernelSection p k base z y)
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_normalizedZonalKernelSection_right p k base x).mul
      (continuous_normalizedZonalKernelSection_left p k base y)
  · exact (isCompact_univ : IsCompact (Set.univ : Set (sphereSet n))).of_isClosed_subset
      (isClosed_tsupport _) (Set.subset_univ _)

/-- Kernel of the second iterate of the normalized zonal operator. -/
noncomputable def normalizedZonalKernelConvolution {n : ℕ}
    (p k : ℕ) (base x y : sphereSet n) : ℝ :=
  ∫ z : sphereSet n,
    normalizedZonalKernelSection p k base x z *
      normalizedZonalKernelSection p k base z y
    ∂normalizedSphereMeasure n

theorem normalizedZonalKernelConvolution_nonneg {n : ℕ} (hn : 0 < n)
    (p k : ℕ) (base x y : sphereSet n) :
    0 ≤ normalizedZonalKernelConvolution p k base x y := by
  unfold normalizedZonalKernelConvolution
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards with z
  exact mul_nonneg
    (normalizedZonalKernelSection_nonneg hn p k base x z)
    (normalizedZonalKernelSection_nonneg hn p k base z y)

/-- A localized Markov kernel has a localized convolution, with half-distance loss. -/
theorem normalizedZonalKernelConvolution_le_halfChordalDecay {n : ℕ}
    (hn : 2 ≤ n) (p k q : ℕ) (base x y : sphereSet n)
    (A : ℝ) (hA : 0 ≤ A)
    (hlocal : ∀ u v : sphereSet n, normalizedZonalKernelSection p k base u v ≤
      A * (1 + (k : ℝ) * Real.sqrt (sphereChordalSq u.1 v.1))⁻¹ ^ q) :
    normalizedZonalKernelConvolution p k base x y ≤
      2 * A * (1 + (k : ℝ) * (Real.sqrt (sphereChordalSq x.1 y.1) / 2))⁻¹ ^ q := by
  let d : ℝ := Real.sqrt (sphereChordalSq x.1 y.1)
  let w : ℝ := (1 + (k : ℝ) * (d / 2))⁻¹ ^ q
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hw0 : 0 ≤ w := pow_nonneg (inv_nonneg.mpr (by dsimp [d]; positivity)) q
  have hdecay (u v : sphereSet n)
      (huv : d / 2 ≤ Real.sqrt (sphereChordalSq u.1 v.1)) :
      normalizedZonalKernelSection p k base u v ≤ A * w := by
    have hbase : 1 + (k : ℝ) * (d / 2) ≤
        1 + (k : ℝ) * Real.sqrt (sphereChordalSq u.1 v.1) := by gcongr
    have hinv : (1 + (k : ℝ) * Real.sqrt (sphereChordalSq u.1 v.1))⁻¹ ≤
        (1 + (k : ℝ) * (d / 2))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hbase
    exact (hlocal u v).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) hinv q) hA)
  have hmajor : MeasureTheory.Integrable (fun z : sphereSet n ↦
      (A * w) * (normalizedZonalKernelSection p k base z y +
        normalizedZonalKernelSection p k base x z))
      (normalizedSphereMeasure n) :=
    ((integrable_normalizedZonalKernelSection_left (by omega) p k base y).add
      (integrable_normalizedZonalKernelSection_right (by omega) p k base x)).const_mul
        (A * w)
  have hpoint (z : sphereSet n) :
      normalizedZonalKernelSection p k base x z *
          normalizedZonalKernelSection p k base z y ≤
        (A * w) * (normalizedZonalKernelSection p k base z y +
          normalizedZonalKernelSection p k base x z) := by
    have htriangle := sqrt_sphereChordalSq_triangle x z y
    by_cases hxz : d / 2 ≤ Real.sqrt (sphereChordalSq x.1 z.1)
    · have hxzBound := hdecay x z hxz
      calc
        normalizedZonalKernelSection p k base x z *
            normalizedZonalKernelSection p k base z y ≤
          (A * w) * normalizedZonalKernelSection p k base z y :=
            mul_le_mul_of_nonneg_right hxzBound
              (normalizedZonalKernelSection_nonneg (by omega) p k base z y)
        _ ≤ (A * w) * (normalizedZonalKernelSection p k base z y +
            normalizedZonalKernelSection p k base x z) :=
          mul_le_mul_of_nonneg_left
            (le_add_of_nonneg_right
              (normalizedZonalKernelSection_nonneg (by omega) p k base x z))
            (mul_nonneg hA hw0)
    · have hzy : d / 2 ≤ Real.sqrt (sphereChordalSq z.1 y.1) := by
        dsimp [d] at hxz ⊢
        linarith
      have hzyBound := hdecay z y hzy
      calc
        normalizedZonalKernelSection p k base x z *
            normalizedZonalKernelSection p k base z y ≤
          normalizedZonalKernelSection p k base x z * (A * w) :=
            mul_le_mul_of_nonneg_left hzyBound
              (normalizedZonalKernelSection_nonneg (by omega) p k base x z)
        _ ≤ (A * w) * (normalizedZonalKernelSection p k base z y +
            normalizedZonalKernelSection p k base x z) := by
          have := normalizedZonalKernelSection_nonneg (by omega) p k base z y
          nlinarith
  calc
    normalizedZonalKernelConvolution p k base x y ≤
        ∫ z : sphereSet n, (A * w) *
          (normalizedZonalKernelSection p k base z y +
            normalizedZonalKernelSection p k base x z)
          ∂normalizedSphereMeasure n :=
      MeasureTheory.integral_mono (integrable_normalizedZonalKernelSection_mul
        (by omega) p k base x y) hmajor hpoint
    _ = 2 * A * w := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add
          (integrable_normalizedZonalKernelSection_left (by omega) p k base y)
          (integrable_normalizedZonalKernelSection_right (by omega) p k base x),
        integral_normalizedZonalKernelSection_left_eq_one hn,
        integral_normalizedZonalKernelSection_eq_one hn]
      ring

/-- Signed kernel of the Booleanized operator `2K - K²`. -/
noncomputable def booleanZonalKernelSection {n : ℕ}
    (p k : ℕ) (base x y : sphereSet n) : ℝ :=
  2 * normalizedZonalKernelSection p k base x y -
    normalizedZonalKernelConvolution p k base x y

/-- For the fixed kernel power used here, the normalized positive kernel
has the required dimension-scale decay, uniformly in all three sphere points. -/
theorem exists_fixedPower_normalizedZonalKernelSection_localization
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ base x y : sphereSet n,
        normalizedZonalKernelSection (n + 3) k base x y ≤
          A * (k : ℝ) ^ (n - 1) *
            (1 + (k : ℝ) * sphereAngularDistance y x)⁻¹ ^ (2 * (n + 3)) := by
  obtain ⟨x₀, hx₀⟩ := sphereSet_nonempty (by omega : 0 < n)
  let base₀ : sphereSet n := ⟨x₀, hx₀⟩
  obtain ⟨c, B, hc, _hB, hraw⟩ :=
    continuousZonalKernel_fixedPower_rawMomentBounds_at hn base₀
  let A : ℝ := (8 : ℝ) ^ (2 * (n + 3)) / c
  refine ⟨A, div_nonneg (pow_nonneg (by norm_num) _) hc.le, ?_⟩
  intro k hk base x y
  let t : ℝ := 1 + (k : ℝ) * sphereAngularDistance y x
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have htpos : 0 < t := by
    dsimp [t]
    linarith [mul_nonneg hkpos.le
      (sphereAngularDistance_nonneg y x)]
  have hmassLower :
      c * (k : ℝ) ^ (n + 7) ≤
        continuousZonalKernelMass (n + 3) k base.1 := by
    have hbase := (hraw k hk).1
    have heq := continuousZonalKernelMass_eq_on_sphere
      (by omega) (sphereKernelPower n) k base base₀
    rw [sphereKernelPower] at heq
    exact hbase.trans_eq heq.symm
  have hmassPos : 0 < continuousZonalKernelMass (n + 3) k base.1 :=
    continuousZonalKernelMass_pos (by omega) _ _ base.1 base.2
  have henvelope :=
    eval_sphereDirichletZonalKernel_mul_localizationFactor_le
      (n + 3) k hk x y
  change MvPolynomial.eval y.1 (sphereDirichletZonalKernel (n + 3) k x.1) /
      continuousZonalKernelMass (n + 3) k base.1 ≤ _
  apply (div_le_iff₀ hmassPos).2
  calc
    MvPolynomial.eval y.1 (sphereDirichletZonalKernel (n + 3) k x.1) ≤
        (8 * (k : ℝ)) ^ (2 * (n + 3)) / t ^ (2 * (n + 3)) := by
      apply (le_div_iff₀ (pow_pos htpos _)).2
      simpa only [t] using henvelope
    _ = (A * (k : ℝ) ^ (n - 1) * t⁻¹ ^ (2 * (n + 3))) *
          (c * (k : ℝ) ^ (n + 7)) := by
      dsimp [A]
      rw [mul_pow, show 2 * (n + 3) = (n - 1) + (n + 7) by omega, pow_add]
      rw [inv_pow]
      field_simp [hc.ne', hkpos.ne', htpos.ne']
      ring
    _ ≤ (A * (k : ℝ) ^ (n - 1) * t⁻¹ ^ (2 * (n + 3))) *
          continuousZonalKernelMass (n + 3) k base.1 := by
      exact mul_le_mul_of_nonneg_left hmassLower
        (mul_nonneg (mul_nonneg
          (div_nonneg (pow_nonneg (by norm_num) _) hc.le)
          (pow_nonneg hkpos.le _)) (pow_nonneg (inv_nonneg.mpr htpos.le) _))

/-- The angular localization theorem immediately yields the weaker chordal
form used by retained-root supports and dyadic packing. -/
theorem exists_fixedPower_normalizedZonalKernelSection_chordalLocalization
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ base x y : sphereSet n,
        normalizedZonalKernelSection (n + 3) k base x y ≤
          A * (k : ℝ) ^ (n - 1) *
            (1 + (k : ℝ) * Real.sqrt (sphereChordalSq y.1 x.1))⁻¹ ^
              (2 * (n + 3)) := by
  obtain ⟨A, hA, hangular⟩ :=
    exists_fixedPower_normalizedZonalKernelSection_localization hn
  refine ⟨A, hA, ?_⟩
  intro k hk base x y
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hdist : Real.sqrt (sphereChordalSq y.1 x.1) ≤
      sphereAngularDistance y x := by
    rw [Real.sqrt_le_iff]
    exact ⟨sphereAngularDistance_nonneg y x,
      sphereChordalSq_le_sphereAngularDistance_sq y x⟩
  have hbase :
      1 + (k : ℝ) * Real.sqrt (sphereChordalSq y.1 x.1) ≤
        1 + (k : ℝ) * sphereAngularDistance y x := by
    gcongr
  have hang0 : 0 ≤ 1 + (k : ℝ) * sphereAngularDistance y x := by
    linarith [mul_nonneg hk0 (sphereAngularDistance_nonneg y x)]
  have hinv :
      (1 + (k : ℝ) * sphereAngularDistance y x)⁻¹ ≤
        (1 + (k : ℝ) * Real.sqrt (sphereChordalSq y.1 x.1))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hbase
  calc
    normalizedZonalKernelSection (n + 3) k base x y ≤
        A * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * sphereAngularDistance y x)⁻¹ ^ (2 * (n + 3)) :=
      hangular k hk base x y
    _ ≤ A * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq y.1 x.1))⁻¹ ^
            (2 * (n + 3)) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr hang0) hinv _)
        (mul_nonneg hA (pow_nonneg hk0 _))

theorem sphereChordalSq_comm {n : ℕ} (x y : Fin n → ℝ) :
    sphereChordalSq x y = sphereChordalSq y x := by
  unfold sphereChordalSq
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Replacing half the chordal distance by the full distance costs at most `2^q`. -/
theorem half_chordalDecay_le (k q : ℕ) {d : ℝ} (hd : 0 ≤ d) :
    (1 + (k : ℝ) * (d / 2))⁻¹ ^ q ≤
      (2 : ℝ) ^ q * (1 + (k : ℝ) * d)⁻¹ ^ q := by
  let a : ℝ := 1 + (k : ℝ) * (d / 2)
  let b : ℝ := 1 + (k : ℝ) * d
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : b / 2 ≤ a := by
    dsimp [a, b]
    nlinarith [mul_nonneg (Nat.cast_nonneg k) hd]
  have hinv : a⁻¹ ≤ 2 * b⁻¹ := by
    have h := one_div_le_one_div_of_le (by positivity : 0 < b / 2) hab
    calc
      a⁻¹ = 1 / a := by simp only [one_div]
      _ ≤ 1 / (b / 2) := h
      _ = 2 * b⁻¹ := by field_simp [hb.ne']
  calc
    a⁻¹ ^ q ≤ (2 * b⁻¹) ^ q :=
      pow_le_pow_left₀ (inv_nonneg.mpr ha.le) hinv q
    _ = 2 ^ q * b⁻¹ ^ q := mul_pow 2 b⁻¹ q


/-- Once `t = kρ ≥ 1` and the normalized distance `u = d/ρ ≥ 2`, the
fixed kernel power pays for the complete quartic scale loss. -/
theorem scaled_halfDistance_decay_le (m : ℕ) {t u : ℝ}
    (ht : 1 ≤ t) (hu : 2 ≤ u) :
    t ^ m * (1 + t * (u / 2))⁻¹ ^ (2 * m) ≤
      (1 + u)⁻¹ ^ m := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have htu : 0 ≤ t * u := mul_nonneg ht0 hu0
  have hcore : t * (1 + u) ≤ (1 + t * (u / 2)) ^ 2 := by
    have ht_le : t ≤ t * u / 2 := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hu)]
    have hone : 0 ≤ 1 + t * (u / 2) := by positivity
    nlinarith [sq_nonneg (1 + t * (u / 2) - 3 / 2)]
  have hleftPos : 0 < t * (1 + u) := mul_pos (lt_of_lt_of_le zero_lt_one ht) (by linarith)
  have hinv : (1 + t * (u / 2))⁻¹ ^ 2 ≤ (t * (1 + u))⁻¹ := by
    rw [inv_pow]
    simpa only [one_div] using one_div_le_one_div_of_le hleftPos hcore
  have hinvPow : ((1 + t * (u / 2))⁻¹ ^ 2) ^ m ≤
      ((t * (1 + u))⁻¹) ^ m :=
    pow_le_pow_left₀ (pow_nonneg (inv_nonneg.mpr (by positivity)) 2) hinv m
  calc
    t ^ m * (1 + t * (u / 2))⁻¹ ^ (2 * m) =
        t ^ m * ((1 + t * (u / 2))⁻¹ ^ 2) ^ m := by rw [pow_mul]
    _ ≤ t ^ m * ((t * (1 + u))⁻¹) ^ m :=
      mul_le_mul_of_nonneg_left hinvPow (pow_nonneg ht0 m)
    _ = (1 + u)⁻¹ ^ m := by
      rw [← mul_pow]
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
      have hu1pos : 0 < 1 + u := by linarith
      field_simp [htpos.ne', hu1pos.ne']

/-- In the retained-root variables, the fixed kernel exponent becomes exactly
the quartic scale factor and chordal decay weight. -/
theorem kernelRadius_halfDistance_decay_le {n k : ℕ} (hn : 3 ≤ n)
    (hk : 1 ≤ k) {radius d : ℝ} (hradius : 0 < radius)
    (hradiusLower : 1 / (k : ℝ) ≤ radius) (hfar : 2 * radius ≤ d) :
    (k : ℝ) ^ (n - 1) * radius ^ (n + 1) *
        (1 + (k : ℝ) * (d / 2))⁻¹ ^ (2 * (n + 3)) ≤
      1 / ((k : ℝ) ^ 4 * radius ^ 2) *
        (1 + d / radius)⁻¹ ^ (n + 3) := by
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have ht : 1 ≤ (k : ℝ) * radius := by
    calc
      1 = (k : ℝ) * (1 / (k : ℝ)) := by field_simp [hkpos.ne']
      _ ≤ (k : ℝ) * radius :=
        mul_le_mul_of_nonneg_left hradiusLower hkpos.le
  have hu : 2 ≤ d / radius := (le_div_iff₀ hradius).2 hfar
  have hscaled := scaled_halfDistance_decay_le (n + 3)
    (t := (k : ℝ) * radius) (u := d / radius) ht hu
  have hbase :
      1 + ((k : ℝ) * radius) * ((d / radius) / 2) =
        1 + (k : ℝ) * (d / 2) := by
    field_simp [hradius.ne']
  rw [hbase] at hscaled
  have hscale :
      (k : ℝ) ^ (n - 1) * radius ^ (n + 1) =
        1 / ((k : ℝ) ^ 4 * radius ^ 2) *
          (((k : ℝ) * radius) ^ (n + 3)) := by
    rw [mul_pow, show n + 3 = (n - 1) + 4 by omega,
      show n + 1 = (n - 1) + 2 by omega, pow_add]
    field_simp [hkpos.ne', hradius.ne']
    ring
  rw [hscale]
  calc
    (1 / ((k : ℝ) ^ 4 * radius ^ 2) *
        ((k : ℝ) * radius) ^ (n + 3)) *
        (1 + (k : ℝ) * (d / 2))⁻¹ ^ (2 * (n + 3)) =
      1 / ((k : ℝ) ^ 4 * radius ^ 2) *
        (((k : ℝ) * radius) ^ (n + 3) *
          (1 + (k : ℝ) * (d / 2))⁻¹ ^ (2 * (n + 3))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscaled (by positivity)

/-- The fixed-power normalized kernel convolution has the same chordal decay
as one kernel row, after enlarging the dimension-only constant. -/
theorem exists_fixedPower_normalizedZonalKernelConvolution_chordalLocalization
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k → ∀ base x y : sphereSet n,
      normalizedZonalKernelConvolution (n + 3) k base x y ≤
        B * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^
            (2 * (n + 3)) := by
  obtain ⟨A, hA, hkernel⟩ :=
    exists_fixedPower_normalizedZonalKernelSection_chordalLocalization hn
  let q := 2 * (n + 3)
  let B : ℝ := 2 * A * (2 : ℝ) ^ q
  refine ⟨B, by positivity, ?_⟩
  intro k hk base x y
  let M : ℝ := A * (k : ℝ) ^ (n - 1)
  have hM : 0 ≤ M := mul_nonneg hA (pow_nonneg (Nat.cast_nonneg k) _)
  have hlocal : ∀ u v : sphereSet n,
      normalizedZonalKernelSection (n + 3) k base u v ≤
        M * (1 + (k : ℝ) * Real.sqrt (sphereChordalSq u.1 v.1))⁻¹ ^ q := by
    intro u v
    simpa only [M, q, sphereChordalSq_comm] using hkernel k hk base u v
  have hconv := normalizedZonalKernelConvolution_le_halfChordalDecay
    (by omega) (n + 3) k q base x y M hM hlocal
  have hhalf := half_chordalDecay_le k q
    (Real.sqrt_nonneg (sphereChordalSq x.1 y.1))
  calc
    normalizedZonalKernelConvolution (n + 3) k base x y ≤
        2 * M *
          (1 + (k : ℝ) * (Real.sqrt (sphereChordalSq x.1 y.1) / 2))⁻¹ ^ q :=
      hconv
    _ ≤ 2 * M * ((2 : ℝ) ^ q *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^ q) :=
      mul_le_mul_of_nonneg_left hhalf (mul_nonneg (by norm_num) hM)
    _ = B * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^
            (2 * (n + 3)) := by
      dsimp [B, M, q]
      ring


/-- The signed kernel of the Booleanized operator retains fixed-power
chordal localization.  This is the kernel estimate used for tail control. -/
theorem exists_fixedPower_booleanZonalKernelSection_chordalLocalization
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k : ℕ, 1 ≤ k → ∀ base x y : sphereSet n,
      |booleanZonalKernelSection (n + 3) k base x y| ≤
        D * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^
            (2 * (n + 3)) := by
  obtain ⟨A, hA, hsection⟩ :=
    exists_fixedPower_normalizedZonalKernelSection_chordalLocalization hn
  obtain ⟨B, hB, hconvolution⟩ :=
    exists_fixedPower_normalizedZonalKernelConvolution_chordalLocalization hn
  refine ⟨2 * A + B, by positivity, ?_⟩
  intro k hk base x y
  let w : ℝ :=
    (k : ℝ) ^ (n - 1) *
      (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^
        (2 * (n + 3))
  have hsection' : normalizedZonalKernelSection (n + 3) k base x y ≤ A * w := by
    simpa only [w, sphereChordalSq_comm, mul_assoc] using hsection k hk base x y
  have hconvolution' :
      normalizedZonalKernelConvolution (n + 3) k base x y ≤ B * w := by
    simpa only [w, mul_assoc] using hconvolution k hk base x y
  have hs0 := normalizedZonalKernelSection_nonneg (by omega) (n + 3) k base x y
  have hc0 := normalizedZonalKernelConvolution_nonneg (by omega) (n + 3) k base x y
  unfold booleanZonalKernelSection
  calc
    |2 * normalizedZonalKernelSection (n + 3) k base x y -
        normalizedZonalKernelConvolution (n + 3) k base x y| ≤
      |2 * normalizedZonalKernelSection (n + 3) k base x y| +
        |normalizedZonalKernelConvolution (n + 3) k base x y| := abs_sub _ _
    _ = 2 * normalizedZonalKernelSection (n + 3) k base x y +
        normalizedZonalKernelConvolution (n + 3) k base x y := by
      rw [abs_of_nonneg hc0, abs_of_nonneg (mul_nonneg (by norm_num) hs0)]
    _ ≤ 2 * (A * w) + B * w :=
      add_le_add (mul_le_mul_of_nonneg_left hsection' (by norm_num)) hconvolution'
    _ = (2 * A + B) * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^
            (2 * (n + 3)) := by
      dsimp [w]
      ring

/-- The second normalized zonal iterate is integration against the
convolution kernel.  Compactness supplies the Fubini integrability. -/
theorem normalizedFunctionZonalKernelValue_iterate_eq_integral_convolution
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base x : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) :
    normalizedFunctionZonalKernelValue p k base
        (fun z ↦ normalizedFunctionZonalKernelValue p k base v z.1) x.1 =
      ∫ y : sphereSet n,
        normalizedZonalKernelConvolution p k base x y * v y
        ∂normalizedSphereMeasure n := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  have hjoint : Continuous (fun zy : sphereSet n × sphereSet n ↦
      normalizedZonalKernelSection p k base zy.1 zy.2) := by
    have hdot : Continuous (fun zy : sphereSet n × sphereSet n ↦
        ∑ i, zy.1.1 i * zy.2.1 i) := by
      apply continuous_finset_sum
      intro i _
      exact (((continuous_apply i).comp continuous_subtype_val).comp
        continuous_fst).mul (((continuous_apply i).comp
          continuous_subtype_val).comp continuous_snd)
    have hpoly : Continuous (fun t : ℝ ↦
        (sphereDirichletPolynomial k).eval t) := by
      simpa only [Polynomial.eval₂_id] using
        (Polynomial.continuous_eval₂ (sphereDirichletPolynomial k) (RingHom.id ℝ))
    have hnum : Continuous (fun zy : sphereSet n × sphereSet n ↦
        MvPolynomial.eval zy.2.1 (sphereDirichletZonalKernel p k zy.1.1)) := by
      convert (hpoly.comp hdot).pow (2 * p) using 1
      funext zy
      rw [eval_sphereDirichletZonalKernel]
      rfl
    unfold normalizedZonalKernelSection
    exact hnum.div_const _
  have hprod : MeasureTheory.Integrable
      (Function.uncurry (fun z y : sphereSet n ↦
        normalizedZonalKernelSection p k base x z *
          normalizedZonalKernelSection p k base z y * v y))
      ((normalizedSphereMeasure n).prod (normalizedSphereMeasure n)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (((continuous_normalizedZonalKernelSection_right p k base x).comp
          continuous_fst).mul hjoint).mul (hv.comp continuous_snd)
    · exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
        (Set.subset_univ _)
  calc
    normalizedFunctionZonalKernelValue p k base
        (fun z ↦ normalizedFunctionZonalKernelValue p k base v z.1) x.1 =
      ∫ z : sphereSet n, normalizedZonalKernelSection p k base x z *
        (∫ y : sphereSet n,
          normalizedZonalKernelSection p k base z y * v y
          ∂normalizedSphereMeasure n) ∂normalizedSphereMeasure n := by
      rw [normalizedFunctionZonalKernelValue_eq_integral_section]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [normalizedFunctionZonalKernelValue_eq_integral_section]
    _ = ∫ z : sphereSet n, ∫ y : sphereSet n,
        normalizedZonalKernelSection p k base x z *
          normalizedZonalKernelSection p k base z y * v y
          ∂normalizedSphereMeasure n ∂normalizedSphereMeasure n := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring
    _ = ∫ y : sphereSet n, ∫ z : sphereSet n,
        normalizedZonalKernelSection p k base x z *
          normalizedZonalKernelSection p k base z y * v y
          ∂normalizedSphereMeasure n ∂normalizedSphereMeasure n :=
      MeasureTheory.integral_integral_swap hprod
    _ = ∫ y : sphereSet n,
        normalizedZonalKernelConvolution p k base x y * v y
        ∂normalizedSphereMeasure n := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [MeasureTheory.integral_mul_const]
      rfl

/-- A point in a supporting cap stays at least half the center distance from
a point whose center distance is at least twice the cap radius. -/
theorem half_centerChordalDistance_le_of_mem_cap {n : ℕ}
    (center x y : sphereSet n) {radius : ℝ} (hradius : 0 ≤ radius)
    (hfar : 2 * radius ≤ Real.sqrt (sphereChordalSq x.1 center.1))
    (hy : y ∈ sphereChordalCap center radius) :
    Real.sqrt (sphereChordalSq x.1 center.1) / 2 ≤
      Real.sqrt (sphereChordalSq x.1 y.1) := by
  have hy' : sphereChordalSq y.1 center.1 ≤ radius ^ 2 := by
    simpa only [sphereChordalCap, Set.mem_setOf_eq] using hy
  have hyroot : Real.sqrt (sphereChordalSq y.1 center.1) ≤ radius := by
    rw [Real.sqrt_le_iff]
    exact ⟨hradius, hy'⟩
  have htriangle := sqrt_sphereChordalSq_triangle x y center
  linarith
/-- Error of the canonical Boolean-filter polynomial on one retained root. -/
def FiniteRetainedRootData.booleanFilterError
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) (i : Fin atoms.N)
    (x : Fin n → ℝ) : ℝ :=
  MvPolynomial.eval x
      (booleanFilteredFunctionPolynomial (n + 3) k atoms.base
        (fun y ↦ atoms.root i y.1)) - atoms.root i x

/-- Signed pointwise error of one application of the normalized zonal
operator.  Keeping this as a named quantity exposes the iterated error that
Booleanization cancels. -/
noncomputable def normalizedZonalFilterError {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (x : sphereSet n) : ℝ :=
  normalizedFunctionZonalKernelValue p k base v x.1 - v x

/-- A continuous sphere function times a zonal-kernel section is integrable.
This is the continuous-root counterpart of the bounded-degree polynomial
integrability lemma used by the repair argument. -/
theorem integrable_continuous_mul_sphereDirichletZonalKernel_section
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (v : sphereSet n → ℝ)
    (hv : Continuous v) (x : Fin n → ℝ) :
    MeasureTheory.Integrable (fun y : sphereSet n ↦ v y *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x))
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact hv.mul (continuous_sphereDirichletZonalKernel_section p k x)
  · exact (isCompact_univ : IsCompact (Set.univ : Set (sphereSet n))).of_isClosed_subset
      (isClosed_tsupport _) (Set.subset_univ _)

/-- Reflection pairing cancels the first-order kernel increment for every
continuous sphere function, not only for bounded-degree polynomials. -/
theorem two_mul_integral_continuous_kernel_increment_eq_symmetricIncrement
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (v : sphereSet n → ℝ)
    (hv : Continuous v) (x : sphereSet n) :
    2 * (∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) =
      ∫ y : sphereSet n,
        (v y + v (sphereAxialReflection x y) - 2 * v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
  let f : sphereSet n → ℝ := fun y ↦
    (v y - v x) *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
  have hf : MeasureTheory.Integrable f (normalizedSphereMeasure n) := by
    apply integrable_continuous_mul_sphereDirichletZonalKernel_section
      hn p k (fun y ↦ v y - v x)
    · exact hv.sub continuous_const
  have hfcomp : MeasureTheory.Integrable
      (fun y ↦ f (sphereAxialReflection x y)) (normalizedSphereMeasure n) := by
    change MeasureTheory.Integrable (f ∘ sphereAxialReflection x)
      (normalizedSphereMeasure n)
    exact ((sphereAxialReflection_measurePreserving x).integrable_comp_emb
      (sphereAxialReflection_measurableEmbedding x)).2 hf
  calc
    2 * (∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) =
        2 * ∫ y : sphereSet n, f y ∂normalizedSphereMeasure n := by rfl
    _ = (∫ y : sphereSet n, f y ∂normalizedSphereMeasure n) +
        ∫ y : sphereSet n, f (sphereAxialReflection x y)
          ∂normalizedSphereMeasure n := by
      rw [integral_comp_sphereAxialReflection]
      ring
    _ = ∫ y : sphereSet n, (f y + f (sphereAxialReflection x y))
          ∂normalizedSphereMeasure n :=
      (MeasureTheory.integral_add hf hfcomp).symm
    _ = ∫ y : sphereSet n,
        (v y + v (sphereAxialReflection x y) - 2 * v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      dsimp [f]
      rw [← sphereAxialReflection_coe x y]
      rw [eval_sphereDirichletZonalKernel_sphereAxialReflection]
      ring

/-- A symmetric second-difference estimate for a continuous sphere function
gives the same integrated second-moment remainder bound used for polynomials. -/
theorem abs_integral_continuous_kernel_increment_le_of_symmetricIncrement
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (A : ℝ)
    (v : sphereSet n → ℝ) (hv : Continuous v) (x : sphereSet n)
    (hsymmetric : ∀ y : sphereSet n,
      |v y + v (sphereAxialReflection x y) - 2 * v x| ≤
        (2 * A) * sphereChordalSq y.1 x.1) :
    |∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n| ≤
      A * continuousZonalKernelSecondMoment p k x.1 := by
  have hmajor : MeasureTheory.Integrable (fun y : sphereSet n ↦
      (2 * A) * (sphereChordalSq y.1 x.1 *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)))
      (normalizedSphereMeasure n) :=
    (integrable_sphereChordalSq_mul_sphereDirichletZonalKernel_section
      hn p k x.1).const_mul (2 * A)
  have hsymIntegral :
      |∫ y : sphereSet n,
        (v y + v (sphereAxialReflection x y) - 2 * v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| ≤
        2 * (A * continuousZonalKernelSecondMoment p k x.1) := by
    calc
      |∫ y : sphereSet n,
        (v y + v (sphereAxialReflection x y) - 2 * v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| ≤
          ∫ y : sphereSet n, (2 * A) *
            (sphereChordalSq y.1 x.1 *
              MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1))
              ∂normalizedSphereMeasure n := by
        change ‖∫ y : sphereSet n,
          (v y + v (sphereAxialReflection x y) - 2 * v x) *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n‖ ≤ _
        apply MeasureTheory.norm_integral_le_of_norm_le hmajor
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg
            (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)]
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hsymmetric y)
            (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)
      _ = 2 * (A * continuousZonalKernelSecondMoment p k x.1) := by
        rw [MeasureTheory.integral_const_mul]
        unfold continuousZonalKernelSecondMoment
        ring
  have hpair :=
    two_mul_integral_continuous_kernel_increment_eq_symmetricIncrement
      hn p k v hv x
  have habs :
      2 * |∫ y : sphereSet n, (v y - v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| =
        |∫ y : sphereSet n,
          (v y + v (sphereAxialReflection x y) - 2 * v x) *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n| := by
    calc
      2 * |∫ y : sphereSet n, (v y - v x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| =
          |2 * (∫ y : sphereSet n, (v y - v x) *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n)| := by
        rw [abs_mul]
        norm_num
      _ = |∫ y : sphereSet n,
          (v y + v (sphereAxialReflection x y) - 2 * v x) *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n| :=
        congrArg abs hpair
  linarith

/-- The normalized filter error of a continuous sphere function is the
normalized integral of its increments from the evaluation point. -/
theorem normalizedZonalFilterError_eq_integral_increment
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) (x : sphereSet n)
    (hmass : continuousZonalKernelMass p k x.1 =
      continuousZonalKernelMass p k base.1) :
    normalizedZonalFilterError p k base v x =
      (∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) /
        continuousZonalKernelMass p k base.1 := by
  have hZpos : 0 < continuousZonalKernelMass p k base.1 :=
    continuousZonalKernelMass_pos hn p k base.1 base.2
  have hkernel :=
    integrable_sphereDirichletZonalKernel_section hn p k x.1
  have hmul :=
    integrable_continuous_mul_sphereDirichletZonalKernel_section
      hn p k v hv x.1
  have hint : (fun y : sphereSet n ↦ (v y - v x) *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)) =
      (fun y ↦ v y * MvPolynomial.eval y.1
        (sphereDirichletZonalKernel p k x.1) -
        v x * MvPolynomial.eval y.1
          (sphereDirichletZonalKernel p k x.1)) := by
    funext y
    ring
  have horient :
      (∫ y : sphereSet n, v y *
          MvPolynomial.eval x.1 (sphereDirichletZonalKernel p k y.1)
            ∂normalizedSphereMeasure n) =
        ∫ y : sphereSet n, v y *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [eval_sphereDirichletZonalKernel_comm]
  unfold normalizedZonalFilterError normalizedFunctionZonalKernelValue
  rw [horient, hint, MeasureTheory.integral_sub hmul (hkernel.const_mul (v x))]
  rw [MeasureTheory.integral_const_mul,
    show (∫ y : sphereSet n,
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
        ∂normalizedSphereMeasure n) =
      continuousZonalKernelMass p k base.1 from hmass]
  field_simp [hZpos.ne']

/-- A symmetric second-difference bound and normalized second-moment bound
give a pointwise second-order estimate for the continuous zonal filter. -/
theorem abs_normalizedZonalFilterError_le_of_symmetricIncrement
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) (x : sphereSet n)
    (A B : ℝ) (hA : 0 ≤ A)
    (hmass : continuousZonalKernelMass p k x.1 =
      continuousZonalKernelMass p k base.1)
    (hsymmetric : ∀ y : sphereSet n,
      |v y + v (sphereAxialReflection x y) - 2 * v x| ≤
        (2 * A) * sphereChordalSq y.1 x.1)
    (hmoment : continuousZonalKernelSecondMoment p k x.1 /
      continuousZonalKernelMass p k base.1 ≤ B) :
    |normalizedZonalFilterError p k base v x| ≤ A * B := by
  have hZpos : 0 < continuousZonalKernelMass p k base.1 :=
    continuousZonalKernelMass_pos hn p k base.1 base.2
  rw [normalizedZonalFilterError_eq_integral_increment
    hn p k base v hv x hmass]
  rw [abs_div, abs_of_pos hZpos]
  have hinter :=
    abs_integral_continuous_kernel_increment_le_of_symmetricIncrement
      hn p k A v hv x hsymmetric
  calc
    |∫ y : sphereSet n, (v y - v x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n| /
        continuousZonalKernelMass p k base.1 ≤
      (A * continuousZonalKernelSecondMoment p k x.1) /
        continuousZonalKernelMass p k base.1 :=
      div_le_div_of_nonneg_right hinter hZpos.le
    _ = A * (continuousZonalKernelSecondMoment p k x.1 /
        continuousZonalKernelMass p k base.1) := by ring
    _ ≤ A * B := mul_le_mul_of_nonneg_left hmoment hA

/-- The normalized zonal operator sends continuous sphere functions to
continuous functions, via its already-constructed polynomial representative. -/
theorem continuous_normalizedFunctionZonalKernelValue_of_continuous
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) :
    Continuous (fun x : sphereSet n ↦
      normalizedFunctionZonalKernelValue p k base v x.1) := by
  have hcoeff : ZonalKernelCoeffIntegrable p k v :=
    zonalKernelCoeffIntegrable_of_continuous hn p k v hv
      (zonalKernelCoeffContinuous p k)
  have hpoly : Continuous (fun x : sphereSet n ↦
      MvPolynomial.eval x.1
        (normalizedFunctionZonalKernelPolynomial p k base v)) :=
    (MvPolynomial.continuous_eval
      (normalizedFunctionZonalKernelPolynomial p k base v)).comp
        continuous_subtype_val
  convert hpoly using 1
  funext x
  exact (eval_normalizedFunctionZonalKernelPolynomial
    p k base v hcoeff x.1).symm

/-- For a fixed left endpoint, the normalized convolution kernel is
continuous in its right endpoint. -/
theorem continuous_normalizedZonalKernelConvolution_right
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base x : sphereSet n) :
    Continuous (fun y : sphereSet n ↦
      normalizedZonalKernelConvolution p k base x y) := by
  have hsection := continuous_normalizedZonalKernelSection_right p k base x
  have hoperator := continuous_normalizedFunctionZonalKernelValue_of_continuous
    hn p k base (fun z ↦ normalizedZonalKernelSection p k base x z) hsection
  convert hoperator using 1
  funext y
  rw [normalizedFunctionZonalKernelValue_eq_integral_section]
  unfold normalizedZonalKernelConvolution
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [normalizedZonalKernelSection_comm p k base y z]
  ring

/-- The Booleanized operator is integration against its signed kernel. -/
theorem booleanFilteredFunctionValue_eq_integral_booleanZonalKernelSection
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base x : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) :
    booleanFilteredFunctionValue p k base v x.1 =
      ∫ y : sphereSet n, booleanZonalKernelSection p k base x y * v y
        ∂normalizedSphereMeasure n := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  have hscont : Continuous (fun y : sphereSet n ↦
      normalizedZonalKernelSection p k base x y * v y) :=
    (continuous_normalizedZonalKernelSection_right p k base x).mul hv
  have hccont : Continuous (fun y : sphereSet n ↦
      normalizedZonalKernelConvolution p k base x y * v y) :=
    (continuous_normalizedZonalKernelConvolution_right hn p k base x).mul hv
  have hsint : MeasureTheory.Integrable (fun y : sphereSet n ↦
      normalizedZonalKernelSection p k base x y * v y)
      (normalizedSphereMeasure n) := by
    apply Continuous.integrable_of_hasCompactSupport hscont
    exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
      (Set.subset_univ _)
  have hcint : MeasureTheory.Integrable (fun y : sphereSet n ↦
      normalizedZonalKernelConvolution p k base x y * v y)
      (normalizedSphereMeasure n) := by
    apply Continuous.integrable_of_hasCompactSupport hccont
    exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
      (Set.subset_univ _)
  unfold booleanFilteredFunctionValue
  rw [normalizedFunctionZonalKernelValue_iterate_eq_integral_convolution
    hn p k base x v hv]
  rw [normalizedFunctionZonalKernelValue_eq_integral_section]
  unfold booleanZonalKernelSection
  rw [show (fun y : sphereSet n ↦
      (2 * normalizedZonalKernelSection p k base x y -
        normalizedZonalKernelConvolution p k base x y) * v y) =
      (fun y ↦ normalizedZonalKernelSection p k base x y * v y +
        normalizedZonalKernelSection p k base x y * v y -
        normalizedZonalKernelConvolution p k base x y * v y) by
      funext y
      ring]
  symm
  calc
    (∫ y : sphereSet n,
      normalizedZonalKernelSection p k base x y * v y +
        normalizedZonalKernelSection p k base x y * v y -
        normalizedZonalKernelConvolution p k base x y * v y
        ∂normalizedSphereMeasure n) =
      (∫ y : sphereSet n,
        normalizedZonalKernelSection p k base x y * v y +
          normalizedZonalKernelSection p k base x y * v y
          ∂normalizedSphereMeasure n) -
        ∫ y : sphereSet n, normalizedZonalKernelConvolution p k base x y * v y
          ∂normalizedSphereMeasure n := MeasureTheory.integral_sub (hsint.add hsint) hcint
    _ = _ := by rw [MeasureTheory.integral_add hsint hsint]

/-- The normalized continuous zonal operator preserves subtraction on
continuous sphere functions. -/
theorem normalizedFunctionZonalKernelValue_sub
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (u v : sphereSet n → ℝ) (hu : Continuous u) (hv : Continuous v)
    (x : Fin n → ℝ) :
    normalizedFunctionZonalKernelValue p k base (fun y ↦ u y - v y) x =
      normalizedFunctionZonalKernelValue p k base u x -
        normalizedFunctionZonalKernelValue p k base v x := by
  have huI := integrable_continuous_mul_sphereDirichletZonalKernel_section
    hn p k u hu x
  have hvI := integrable_continuous_mul_sphereDirichletZonalKernel_section
    hn p k v hv x
  have huI' : MeasureTheory.Integrable (fun y : sphereSet n ↦ u y *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1))
      (normalizedSphereMeasure n) := by
    convert huI using 1
    funext y
    rw [eval_sphereDirichletZonalKernel_comm]
  have hvI' : MeasureTheory.Integrable (fun y : sphereSet n ↦ v y *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1))
      (normalizedSphereMeasure n) := by
    convert hvI using 1
    funext y
    rw [eval_sphereDirichletZonalKernel_comm]
  unfold normalizedFunctionZonalKernelValue
  rw [show (fun y : sphereSet n ↦ (u y - v y) *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1)) =
      (fun y ↦ u y * MvPolynomial.eval x
        (sphereDirichletZonalKernel p k y.1) -
        v y * MvPolynomial.eval x
          (sphereDirichletZonalKernel p k y.1)) by
      funext y
      ring]
  rw [MeasureTheory.integral_sub huI' hvI']
  ring

/-- The normalized continuous zonal operator preserves addition on continuous
sphere functions. -/
theorem normalizedFunctionZonalKernelValue_add
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (u v : sphereSet n → ℝ) (hu : Continuous u) (hv : Continuous v)
    (x : Fin n → ℝ) :
    normalizedFunctionZonalKernelValue p k base (fun y ↦ u y + v y) x =
      normalizedFunctionZonalKernelValue p k base u x +
        normalizedFunctionZonalKernelValue p k base v x := by
  have huI := integrable_continuous_mul_sphereDirichletZonalKernel_section
    hn p k u hu x
  have hvI := integrable_continuous_mul_sphereDirichletZonalKernel_section
    hn p k v hv x
  have huI' : MeasureTheory.Integrable (fun y : sphereSet n ↦ u y *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1))
      (normalizedSphereMeasure n) := by
    convert huI using 1
    funext y
    rw [eval_sphereDirichletZonalKernel_comm]
  have hvI' : MeasureTheory.Integrable (fun y : sphereSet n ↦ v y *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1))
      (normalizedSphereMeasure n) := by
    convert hvI using 1
    funext y
    rw [eval_sphereDirichletZonalKernel_comm]
  unfold normalizedFunctionZonalKernelValue
  rw [show (fun y : sphereSet n ↦ (u y + v y) *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1)) =
      (fun y ↦ u y * MvPolynomial.eval x
        (sphereDirichletZonalKernel p k y.1) +
        v y * MvPolynomial.eval x
          (sphereDirichletZonalKernel p k y.1)) by
      funext y
      ring]
  rw [MeasureTheory.integral_add huI' hvI']
  ring

/-- Center-independent normalization makes the continuous zonal operator
reproduce every constant exactly. -/
theorem normalizedFunctionZonalKernelValue_const
    {n : ℕ} (hn : 2 ≤ n) (p k : ℕ) (base x : sphereSet n) (c : ℝ) :
    normalizedFunctionZonalKernelValue p k base (fun _ ↦ c) x.1 = c := by
  have hmass := continuousZonalKernelMass_eq_on_sphere hn p k x base
  have hZpos := continuousZonalKernelMass_pos (by omega) p k base.1 base.2
  have horient :
      (∫ y : sphereSet n, c *
          MvPolynomial.eval x.1 (sphereDirichletZonalKernel p k y.1)
            ∂normalizedSphereMeasure n) =
        ∫ y : sphereSet n, c *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [eval_sphereDirichletZonalKernel_comm]
  unfold normalizedFunctionZonalKernelValue
  rw [horient, MeasureTheory.integral_const_mul]
  change c * continuousZonalKernelMass p k x.1 /
      continuousZonalKernelMass p k base.1 = c
  rw [hmass]
  field_simp [hZpos.ne']

/-- The signed Boolean kernel has total mass one. -/
theorem integral_booleanZonalKernelSection_eq_one {n : ℕ}
    (hn : 2 ≤ n) (p k : ℕ) (base x : sphereSet n) :
    ∫ y : sphereSet n, booleanZonalKernelSection p k base x y
        ∂normalizedSphereMeasure n = 1 := by
  have hrepr :=
    booleanFilteredFunctionValue_eq_integral_booleanZonalKernelSection
      (by omega) p k base x (fun _ ↦ (1 : ℝ)) continuous_const
  have hvalue :
      booleanFilteredFunctionValue p k base (fun _ ↦ (1 : ℝ)) x.1 = 1 := by
    unfold booleanFilteredFunctionValue
    simp_rw [normalizedFunctionZonalKernelValue_const hn]
    ring
  rw [hvalue] at hrepr
  simpa only [mul_one] using hrepr.symm

/-- Consequently, the signed one-step filter error vanishes on constants. -/
theorem normalizedZonalFilterError_const
    {n : ℕ} (hn : 2 ≤ n) (p k : ℕ) (base x : sphereSet n) (c : ℝ) :
    normalizedZonalFilterError p k base (fun _ ↦ c) x = 0 := by
  unfold normalizedZonalFilterError
  rw [normalizedFunctionZonalKernelValue_const hn]
  ring

/-- The signed normalized filter error preserves addition. -/
theorem normalizedZonalFilterError_add
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (u v : sphereSet n → ℝ) (hu : Continuous u) (hv : Continuous v)
    (x : sphereSet n) :
    normalizedZonalFilterError p k base (fun y ↦ u y + v y) x =
      normalizedZonalFilterError p k base u x +
        normalizedZonalFilterError p k base v x := by
  unfold normalizedZonalFilterError
  rw [normalizedFunctionZonalKernelValue_add hn p k base u v hu hv x.1]
  ring

/-- The signed normalized filter error preserves subtraction. -/
theorem normalizedZonalFilterError_sub
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (u v : sphereSet n → ℝ) (hu : Continuous u) (hv : Continuous v)
    (x : sphereSet n) :
    normalizedZonalFilterError p k base (fun y ↦ u y - v y) x =
      normalizedZonalFilterError p k base u x -
        normalizedZonalFilterError p k base v x := by
  unfold normalizedZonalFilterError
  rw [normalizedFunctionZonalKernelValue_sub hn p k base u v hu hv x.1]
  ring

/-- Symmetric second difference about an axial-reflection center. -/
def sphereSymmetricIncrement {n : ℕ} (v : sphereSet n → ℝ)
    (x y : sphereSet n) : ℝ :=
  v y + v (sphereAxialReflection x y) - 2 * v x

/-- Symmetric increments preserve continuity in their evaluation variable. -/
theorem continuous_sphereSymmetricIncrement
    {n : ℕ} (v : sphereSet n → ℝ) (hv : Continuous v)
    (x : sphereSet n) :
    Continuous (sphereSymmetricIncrement v x) := by
  unfold sphereSymmetricIncrement
  exact (hv.add (hv.comp (continuous_sphereAxialReflection x))).sub
    continuous_const

/-- The normalized continuous zonal operator is equivariant under every axial
reflection.  The fixed normalization base is valid because its mass is
center-independent. -/
theorem normalizedFunctionZonalKernelValue_sphereAxialReflection
    {n : ℕ} (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (a x : sphereSet n) :
    normalizedFunctionZonalKernelValue p k base v
        (sphereAxialReflection a x).1 =
      normalizedFunctionZonalKernelValue p k base
        (fun y ↦ v (sphereAxialReflection a y)) x.1 := by
  unfold normalizedFunctionZonalKernelValue
  congr 1
  calc
    (∫ y : sphereSet n, v y *
        MvPolynomial.eval (sphereAxialReflection a x).1
          (sphereDirichletZonalKernel p k y.1)
          ∂normalizedSphereMeasure n) =
      ∫ y : sphereSet n, v (sphereAxialReflection a y) *
        MvPolynomial.eval (sphereAxialReflection a x).1
          (sphereDirichletZonalKernel p k (sphereAxialReflection a y).1)
          ∂normalizedSphereMeasure n :=
      (integral_comp_sphereAxialReflection a _).symm
    _ = ∫ y : sphereSet n, v (sphereAxialReflection a y) *
        MvPolynomial.eval x.1 (sphereDirichletZonalKernel p k y.1)
          ∂normalizedSphereMeasure n := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [eval_sphereDirichletZonalKernel_map_sphereAxialReflection]

/-- The signed normalized filter error inherits axial-reflection equivariance. -/
theorem normalizedZonalFilterError_sphereAxialReflection
    {n : ℕ} (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (a x : sphereSet n) :
    normalizedZonalFilterError p k base v (sphereAxialReflection a x) =
      normalizedZonalFilterError p k base
        (fun y ↦ v (sphereAxialReflection a y)) x := by
  unfold normalizedZonalFilterError
  rw [normalizedFunctionZonalKernelValue_sphereAxialReflection]

/-- Reflection equivariance and constant reproduction commute the one-step
filter error with symmetric increments.  The right side is a point-to-point
increment because the symmetric increment itself vanishes at its center. -/
theorem sphereSymmetricIncrement_normalizedZonalFilterError
    {n : ℕ} (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) (x y : sphereSet n) :
    sphereSymmetricIncrement (normalizedZonalFilterError p k base v) x y =
      normalizedZonalFilterError p k base
          (sphereSymmetricIncrement v x) y -
        normalizedZonalFilterError p k base
          (sphereSymmetricIncrement v x) x := by
  have hvR : Continuous (fun z : sphereSet n ↦
      v (sphereAxialReflection x z)) :=
    hv.comp (continuous_sphereAxialReflection x)
  have hsum : Continuous (fun z : sphereSet n ↦
      v z + v (sphereAxialReflection x z)) := hv.add hvR
  have hconst : Continuous (fun _ : sphereSet n ↦ 2 * v x) :=
    continuous_const
  have herror (z : sphereSet n) :
      normalizedZonalFilterError p k base
          (sphereSymmetricIncrement v x) z =
        normalizedZonalFilterError p k base v z +
          normalizedZonalFilterError p k base
            (fun q ↦ v (sphereAxialReflection x q)) z := by
    unfold sphereSymmetricIncrement
    rw [normalizedZonalFilterError_sub (by omega) p k base
      (fun q ↦ v q + v (sphereAxialReflection x q))
      (fun _ ↦ 2 * v x) hsum hconst z]
    rw [normalizedZonalFilterError_add (by omega) p k base v
      (fun q ↦ v (sphereAxialReflection x q)) hv hvR z]
    rw [normalizedZonalFilterError_const hn]
    ring
  rw [herror y, herror x]
  rw [← normalizedZonalFilterError_sphereAxialReflection p k base v x y]
  rw [← normalizedZonalFilterError_sphereAxialReflection p k base v x x]
  simp [sphereSymmetricIncrement]
  ring

/-- The signed one-step filter error of a continuous input is continuous. -/
theorem continuous_normalizedZonalFilterError
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) :
    Continuous (normalizedZonalFilterError p k base v) :=
  (continuous_normalizedFunctionZonalKernelValue_of_continuous
    hn p k base v hv).sub hv

/-- On continuous functions the Boolean error is exactly the negative of the
one-step zonal-filter error applied to the first one-step error. -/
theorem booleanFilteredFunctionValue_sub_eq_neg_iteratedFilterError
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) (x : sphereSet n) :
    booleanFilteredFunctionValue p k base v x.1 - v x =
      -normalizedZonalFilterError p k base
        (normalizedZonalFilterError p k base v) x := by
  unfold booleanFilteredFunctionValue normalizedZonalFilterError
  rw [normalizedFunctionZonalKernelValue_sub hn p k base
    (fun y ↦ normalizedFunctionZonalKernelValue p k base v y.1) v
    (continuous_normalizedFunctionZonalKernelValue_of_continuous
      hn p k base v hv) hv x.1]
  ring

/-- The repository's proved fixed-power second-moment bound gives a uniform
second-order estimate for every continuous sphere function satisfying a
symmetric increment estimate. -/
theorem exists_fixedPower_continuous_filterError_bound
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ (base : sphereSet n) (v : sphereSet n → ℝ), Continuous v →
      ∀ (x : sphereSet n) (A : ℝ), 0 ≤ A →
      (∀ y : sphereSet n,
        |v y + v (sphereAxialReflection x y) - 2 * v x| ≤
          (2 * A) * sphereChordalSq y.1 x.1) →
      |normalizedZonalFilterError (n + 3) k base v x| ≤
        A * (C / (k : ℝ) ^ 2) := by
  obtain ⟨C, hC, hmoment⟩ :=
    continuousZonalKernel_fixedPower_secondMoment hn
  refine ⟨C, hC, ?_⟩
  intro k hk base v hv x A hA hsymmetric
  have hmass := continuousZonalKernelMass_eq_on_sphere
    (by omega) (sphereKernelPower n) k x base
  have hmass' : continuousZonalKernelMass (n + 3) k x.1 =
      continuousZonalKernelMass (n + 3) k base.1 := by
    simpa [sphereKernelPower] using hmass
  apply abs_normalizedZonalFilterError_le_of_symmetricIncrement
    (by omega) (n + 3) k base v hv x A (C / (k : ℝ) ^ 2) hA
  · exact hmass'
  · exact hsymmetric
  · rw [← hmass']
    simpa [sphereKernelPower] using hmoment k hk x

/-- Applying the proved second-moment estimate to the first filter error gives
the quartic Boolean rate from a second-difference bound for that error. -/
theorem exists_fixedPower_booleanFilterError_bound
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      ∀ (base : sphereSet n) (v : sphereSet n → ℝ), Continuous v →
      ∀ (x : sphereSet n) (A : ℝ), 0 ≤ A →
      (∀ y : sphereSet n,
        |normalizedZonalFilterError (n + 3) k base v y +
            normalizedZonalFilterError (n + 3) k base v
              (sphereAxialReflection x y) -
            2 * normalizedZonalFilterError (n + 3) k base v x| ≤
          (2 * (A / (k : ℝ) ^ 2)) * sphereChordalSq y.1 x.1) →
      |booleanFilteredFunctionValue (n + 3) k base v x.1 - v x| ≤
        A * C / (k : ℝ) ^ 4 := by
  obtain ⟨C, hC, hsecond⟩ :=
    exists_fixedPower_continuous_filterError_bound hn
  refine ⟨C, hC, ?_⟩
  intro k hk base v hv x A hA hsymmetric
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hiterated := hsecond k hk base
    (normalizedZonalFilterError (n + 3) k base v)
    (continuous_normalizedZonalFilterError (by omega) (n + 3) k base v hv)
    x (A / (k : ℝ) ^ 2)
    (div_nonneg hA (sq_nonneg (k : ℝ))) hsymmetric
  rw [booleanFilteredFunctionValue_sub_eq_neg_iteratedFilterError
    (by omega) (n + 3) k base v hv x, abs_neg]
  calc
    |normalizedZonalFilterError (n + 3) k base
        (normalizedZonalFilterError (n + 3) k base v) x| ≤
      (A / (k : ℝ) ^ 2) * (C / (k : ℝ) ^ 2) := hiterated
    _ = A * C / (k : ℝ) ^ 4 := by
      field_simp [hkpos.ne']

/-- The abstract quartic reduction specializes to retained roots with exactly
the target `k⁻⁴ ρ⁻²` global scaling. -/
theorem exists_retainedRoot_global_booleanFilterError_bound
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
        (atoms : FiniteRetainedRootData n C k F)
        (regular : FiniteRetainedRootRegularity atoms), 1 ≤ k →
      ∀ (i : Fin atoms.N) (x : sphereSet n),
      (∀ y : sphereSet n,
        |normalizedZonalFilterError (n + 3) k atoms.base
              (fun z ↦ atoms.root i z.1) y +
            normalizedZonalFilterError (n + 3) k atoms.base
              (fun z ↦ atoms.root i z.1) (sphereAxialReflection x y) -
            2 * normalizedZonalFilterError (n + 3) k atoms.base
              (fun z ↦ atoms.root i z.1) x| ≤
          (2 * ((regular.jetBound / atoms.radius i ^ 2) /
            (k : ℝ) ^ 2)) * sphereChordalSq y.1 x.1) →
      |atoms.booleanFilterError i x.1| ≤
        (regular.jetBound * B) /
          ((k : ℝ) ^ 4 * atoms.radius i ^ 2) := by
  obtain ⟨B, hB, hquartic⟩ :=
    exists_fixedPower_booleanFilterError_bound hn
  refine ⟨B, hB, ?_⟩
  intro C k F atoms regular hk i x hsymmetric
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hrpos := atoms.radius_pos i
  have hv : Continuous (fun y : sphereSet n ↦ atoms.root i y.1) :=
    (regular.root_contDiff i).continuous.comp continuous_subtype_val
  have hquarticRoot := hquartic k hk atoms.base
    (fun y : sphereSet n ↦ atoms.root i y.1) hv x
    (regular.jetBound / atoms.radius i ^ 2)
    (div_nonneg regular.jetBound_nonneg (sq_nonneg (atoms.radius i)))
    hsymmetric
  unfold FiniteRetainedRootData.booleanFilterError
  rw [eval_booleanFilteredFunctionPolynomial (n + 3) k atoms.base
    (fun y ↦ atoms.root i y.1)
    (regular.root_coeff_integrable (by omega)
      (zonalKernelCoeffContinuous (n + 3) k) i)
    (zonalKernelCoeffIntegrable_eval (by omega) (n + 3) k
      (normalizedFunctionZonalKernelPolynomial (n + 3) k atoms.base
        (fun y ↦ atoms.root i y.1)) (zonalKernelCoeffContinuous _ _)) x.1]
  calc
    |booleanFilteredFunctionValue (n + 3) k atoms.base
        (fun y ↦ atoms.root i y.1) x.1 - atoms.root i x.1| ≤
      (regular.jetBound / atoms.radius i ^ 2) * B /
        (k : ℝ) ^ 4 := hquarticRoot
    _ = (regular.jetBound * B) /
        ((k : ℝ) ^ 4 * atoms.radius i ^ 2) := by
      field_simp [hkpos.ne', hrpos.ne']

/-- The Boolean filter error is the difference between the first filter error
of `v` and the first filter error of `K v`. -/
theorem booleanFilteredFunctionValue_sub_eq_filterError_sub {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (x : sphereSet n) :
    booleanFilteredFunctionValue p k base v x.1 - v x =
      normalizedZonalFilterError p k base v x -
        normalizedZonalFilterError p k base
          (fun y ↦ normalizedFunctionZonalKernelValue p k base v y.1) x := by
  unfold booleanFilteredFunctionValue normalizedZonalFilterError
  ring

/-- Triangle-inequality form of the iterated filter-error identity. -/
theorem abs_booleanFilteredFunctionValue_sub_le_filterErrors {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (x : sphereSet n) :
    |booleanFilteredFunctionValue p k base v x.1 - v x| ≤
      |normalizedZonalFilterError p k base v x| +
        |normalizedZonalFilterError p k base
          (fun y ↦ normalizedFunctionZonalKernelValue p k base v y.1) x| := by
  rw [booleanFilteredFunctionValue_sub_eq_filterError_sub]
  calc
    |normalizedZonalFilterError p k base v x -
        normalizedZonalFilterError p k base
          (fun y ↦ normalizedFunctionZonalKernelValue p k base v y.1) x| =
        |normalizedZonalFilterError p k base v x +
          -normalizedZonalFilterError p k base
            (fun y ↦ normalizedFunctionZonalKernelValue p k base v y.1) x| := by
              congr 1
    _ ≤ _ := by
      simpa using (abs_add_le
        (normalizedZonalFilterError p k base v x)
        (-normalizedZonalFilterError p k base
          (fun y ↦ normalizedFunctionZonalKernelValue p k base v y.1) x))

/-- The retained-root error is exactly the pointwise Booleanization of the
normalized continuous zonal-kernel operator. -/
theorem FiniteRetainedRootData.booleanFilterError_eq_value
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n)
    (i : Fin atoms.N) (x : Fin n → ℝ) :
    atoms.booleanFilterError i x =
      booleanFilteredFunctionValue (n + 3) k atoms.base
        (fun y ↦ atoms.root i y.1) x - atoms.root i x := by
  unfold FiniteRetainedRootData.booleanFilterError
  rw [eval_booleanFilteredFunctionPolynomial (n + 3) k atoms.base
    (fun y ↦ atoms.root i y.1)
    (regular.root_coeff_integrable hn (zonalKernelCoeffContinuous (n + 3) k) i)
    (zonalKernelCoeffIntegrable_eval hn (n + 3) k
      (normalizedFunctionZonalKernelPolynomial (n + 3) k atoms.base
        (fun y ↦ atoms.root i y.1)) (zonalKernelCoeffContinuous _ _)) x]

/-- Outside its supporting cap, a retained root vanishes, so its Boolean
filter error is exactly the signed-kernel tail integral. -/
theorem FiniteRetainedRootData.booleanFilterError_eq_integral_of_not_mem_cap
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n)
    (i : Fin atoms.N) (x : sphereSet n)
    (hx : x ∉ sphereChordalCap (atoms.center i) (atoms.radius i)) :
    atoms.booleanFilterError i x.1 =
      ∫ y : sphereSet n,
        booleanZonalKernelSection (n + 3) k atoms.base x y * atoms.root i y.1
          ∂normalizedSphereMeasure n := by
  have hzero : atoms.root i x.1 = 0 := by
    by_contra hne
    exact hx (atoms.supported i x.1 x.2 hne)
  rw [atoms.booleanFilterError_eq_value regular hn i x.1]
  rw [booleanFilteredFunctionValue_eq_integral_booleanZonalKernelSection
    hn (n + 3) k atoms.base x (fun y ↦ atoms.root i y.1)
    ((regular.root_contDiff i).continuous.comp continuous_subtype_val)]
  rw [hzero, sub_zero]

/-- The absolute off-support error is bounded by the integral of the absolute
signed kernel against the root amplitude. -/
theorem FiniteRetainedRootData.abs_booleanFilterError_le_integral_abs_of_not_mem_cap
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n)
    (i : Fin atoms.N) (x : sphereSet n)
    (hx : x ∉ sphereChordalCap (atoms.center i) (atoms.radius i)) :
    |atoms.booleanFilterError i x.1| ≤
      ∫ y : sphereSet n,
        |booleanZonalKernelSection (n + 3) k atoms.base x y| *
          |atoms.root i y.1| ∂normalizedSphereMeasure n := by
  rw [atoms.booleanFilterError_eq_integral_of_not_mem_cap regular hn i x hx]
  change ‖∫ y : sphereSet n,
      booleanZonalKernelSection (n + 3) k atoms.base x y * atoms.root i y.1
      ∂normalizedSphereMeasure n‖ ≤ _
  calc
    _ ≤ ∫ y : sphereSet n,
        ‖booleanZonalKernelSection (n + 3) k atoms.base x y * atoms.root i y.1‖
        ∂normalizedSphereMeasure n := MeasureTheory.norm_integral_le_integral_norm _
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_mul]

/-- On a root's support, far-field center separation makes the signed-kernel
integrand uniformly small. -/
theorem FiniteRetainedRootData.booleanKernel_mul_root_le_far
    {n : ℕ} {C : ℝ} {k q : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (i : Fin atoms.N)
    (x : sphereSet n) (D : ℝ) (hD : 0 ≤ D)
    (hkernel : ∀ y : sphereSet n,
      |booleanZonalKernelSection (n + 3) k atoms.base x y| ≤
        D * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^ q)
    (hfar : 2 * atoms.radius i ≤
      Real.sqrt (sphereChordalSq x.1 (atoms.center i).1))
    (y : sphereSet n) :
    |booleanZonalKernelSection (n + 3) k atoms.base x y| *
        |atoms.root i y.1| ≤
      (D * (k : ℝ) ^ (n - 1) *
        (1 + (k : ℝ) *
          (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^ q) *
        (regular.jetBound * atoms.radius i ^ 2) := by
  by_cases hyroot : atoms.root i y.1 = 0
  · rw [hyroot, abs_zero, mul_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hD (pow_nonneg (Nat.cast_nonneg k) _))
        (pow_nonneg (inv_nonneg.mpr (by positivity)) _))
      (mul_nonneg regular.jetBound_nonneg (sq_nonneg _))
  · have hymem := atoms.supported i y.1 y.2 hyroot
    have hhalf := half_centerChordalDistance_le_of_mem_cap
      (atoms.center i) x y (atoms.radius_pos i).le hfar hymem
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hbase :
        1 + (k : ℝ) *
            (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2) ≤
          1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1) := by
      gcongr
    have hinv :
        (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ≤
          (1 + (k : ℝ) *
            (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hbase
    have hkernel' :
        |booleanZonalKernelSection (n + 3) k atoms.base x y| ≤
          D * (k : ℝ) ^ (n - 1) *
            (1 + (k : ℝ) *
              (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^ q :=
      (hkernel y).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) hinv q)
        (mul_nonneg hD (pow_nonneg hk0 _)))
    have hroot : |atoms.root i y.1| ≤ regular.jetBound * atoms.radius i ^ 2 := by
      simpa using regular.scaled_jet i 0 (by omega) y.1
    exact mul_le_mul hkernel' hroot (abs_nonneg _)
      (mul_nonneg (mul_nonneg hD (pow_nonneg hk0 _))
        (pow_nonneg (inv_nonneg.mpr (by positivity)) _))

/-- Integrating the pointwise far-field estimate gives an off-support error
bound with the same half-center-distance decay. -/
theorem FiniteRetainedRootData.abs_booleanFilterError_le_far
    {n : ℕ} {C : ℝ} {k q : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n)
    (i : Fin atoms.N) (x : sphereSet n) (D : ℝ) (hD : 0 ≤ D)
    (hkernel : ∀ y : sphereSet n,
      |booleanZonalKernelSection (n + 3) k atoms.base x y| ≤
        D * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^ q)
    (hfar : 2 * atoms.radius i ≤
      Real.sqrt (sphereChordalSq x.1 (atoms.center i).1)) :
    |atoms.booleanFilterError i x.1| ≤
      (D * (k : ℝ) ^ (n - 1) *
        (1 + (k : ℝ) *
          (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^ q) *
        (regular.jetBound * atoms.radius i ^ 2) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  let M : ℝ :=
    (D * (k : ℝ) ^ (n - 1) *
      (1 + (k : ℝ) *
        (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^ q) *
      (regular.jetBound * atoms.radius i ^ 2)
  have hx : x ∉ sphereChordalCap (atoms.center i) (atoms.radius i) := by
    intro hxmem
    have hxmem' : sphereChordalSq x.1 (atoms.center i).1 ≤ atoms.radius i ^ 2 := by
      simpa only [sphereChordalCap, Set.mem_setOf_eq] using hxmem
    have hxroot : Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) ≤
        atoms.radius i := by
      rw [Real.sqrt_le_iff]
      exact ⟨(atoms.radius_pos i).le, hxmem'⟩
    linarith [atoms.radius_pos i]
  have hbcont : Continuous (fun y : sphereSet n ↦
      booleanZonalKernelSection (n + 3) k atoms.base x y) := by
    unfold booleanZonalKernelSection
    exact (continuous_const.mul
      (continuous_normalizedZonalKernelSection_right (n + 3) k atoms.base x)).sub
      (continuous_normalizedZonalKernelConvolution_right hn (n + 3) k atoms.base x)
  have hrcont : Continuous (fun y : sphereSet n ↦ atoms.root i y.1) :=
    (regular.root_contDiff i).continuous.comp continuous_subtype_val
  have hinter : MeasureTheory.Integrable (fun y : sphereSet n ↦
      |booleanZonalKernelSection (n + 3) k atoms.base x y| *
        |atoms.root i y.1|) (normalizedSphereMeasure n) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_abs.comp hbcont).mul (continuous_abs.comp hrcont)
    · exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
        (Set.subset_univ _)
  calc
    |atoms.booleanFilterError i x.1| ≤
        ∫ y : sphereSet n,
          |booleanZonalKernelSection (n + 3) k atoms.base x y| *
            |atoms.root i y.1| ∂normalizedSphereMeasure n :=
      atoms.abs_booleanFilterError_le_integral_abs_of_not_mem_cap regular hn i x hx
    _ ≤ ∫ _y : sphereSet n, M ∂normalizedSphereMeasure n :=
      MeasureTheory.integral_mono hinter (MeasureTheory.integrable_const M)
        (atoms.booleanKernel_mul_root_le_far regular i x D hD hkernel hfar)
    _ = M := by simp

/-- Restricting the far-field integral to the actual supporting cap recovers
the cap-measure factor needed for scale-sharp localization. -/
theorem FiniteRetainedRootData.abs_booleanFilterError_le_far_mul_capMeasure
    {n : ℕ} {C : ℝ} {k q : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n)
    (i : Fin atoms.N) (x : sphereSet n) (D : ℝ) (hD : 0 ≤ D)
    (hkernel : ∀ y : sphereSet n,
      |booleanZonalKernelSection (n + 3) k atoms.base x y| ≤
        D * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^ q)
    (hx : x ∉ sphereChordalCap (atoms.center i) (atoms.radius i))
    (hfar : 2 * atoms.radius i ≤
      Real.sqrt (sphereChordalSq x.1 (atoms.center i).1)) :
    |atoms.booleanFilterError i x.1| ≤
      ((D * (k : ℝ) ^ (n - 1) *
        (1 + (k : ℝ) *
          (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^ q) *
        (regular.jetBound * atoms.radius i ^ 2)) *
        (normalizedSphereMeasure n).real
          (sphereChordalCap (atoms.center i) (atoms.radius i)) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  let M : ℝ :=
    (D * (k : ℝ) ^ (n - 1) *
      (1 + (k : ℝ) *
        (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^ q) *
      (regular.jetBound * atoms.radius i ^ 2)
  let s : Set (sphereSet n) := sphereChordalCap (atoms.center i) (atoms.radius i)
  have hs : MeasurableSet s := measurableSet_sphereChordalCap _ _
  have hbcont : Continuous (fun y : sphereSet n ↦
      booleanZonalKernelSection (n + 3) k atoms.base x y) := by
    unfold booleanZonalKernelSection
    exact (continuous_const.mul
      (continuous_normalizedZonalKernelSection_right (n + 3) k atoms.base x)).sub
      (continuous_normalizedZonalKernelConvolution_right hn (n + 3) k atoms.base x)
  have hrcont : Continuous (fun y : sphereSet n ↦ atoms.root i y.1) :=
    (regular.root_contDiff i).continuous.comp continuous_subtype_val
  have hinter : MeasureTheory.Integrable (fun y : sphereSet n ↦
      |booleanZonalKernelSection (n + 3) k atoms.base x y| *
        |atoms.root i y.1|) (normalizedSphereMeasure n) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_abs.comp hbcont).mul (continuous_abs.comp hrcont)
    · exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
        (Set.subset_univ _)
  have hmajor : MeasureTheory.Integrable (s.indicator (fun _ ↦ M))
      (normalizedSphereMeasure n) :=
    (MeasureTheory.integrable_const M).indicator hs
  have hpoint (y : sphereSet n) :
      |booleanZonalKernelSection (n + 3) k atoms.base x y| *
          |atoms.root i y.1| ≤ s.indicator (fun _ ↦ M) y := by
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
      exact atoms.booleanKernel_mul_root_le_far regular i x D hD hkernel hfar y
    · have hyzero : atoms.root i y.1 = 0 := by
        by_contra hyne
        exact hy (atoms.supported i y.1 y.2 hyne)
      rw [Set.indicator_of_notMem hy, hyzero, abs_zero, mul_zero]
  calc
    |atoms.booleanFilterError i x.1| ≤
        ∫ y : sphereSet n,
          |booleanZonalKernelSection (n + 3) k atoms.base x y| *
            |atoms.root i y.1| ∂normalizedSphereMeasure n :=
      atoms.abs_booleanFilterError_le_integral_abs_of_not_mem_cap regular hn i x hx
    _ ≤ ∫ y : sphereSet n, s.indicator (fun _ ↦ M) y
          ∂normalizedSphereMeasure n :=
      MeasureTheory.integral_mono hinter hmajor hpoint
    _ = M * (normalizedSphereMeasure n).real s := by
      rw [MeasureTheory.integral_indicator_const M hs, smul_eq_mul, mul_comm]

/-- The proved sharp cap estimate admits one upper constant uniform over all
centers, by rotational invariance of normalized sphere measure. -/
theorem exists_uniform_chordalCap_power_upper {n : ℕ} (hn : 3 ≤ n) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (center : sphereSet n) (radius : ℝ),
      0 ≤ radius → radius ≤ 1 →
      (normalizedSphereMeasure n).real (sphereChordalCap center radius) ≤
        V * radius ^ (n - 1) := by
  let ref := sphereReferencePoint n (dimension_pos_of_three_le hn)
  obtain ⟨_c, V, _hc, hV, href⟩ :=
    normalizedSphereMeasure_chordalCap_small_power_bounds_at hn ref
  refine ⟨V, hV, ?_⟩
  intro center radius hr0 hr1
  rw [normalizedSphereMeasureReal_sphereChordalCap_eq_on_sphere
    (by omega) radius center ref]
  exact (href radius hr0 hr1).2

/-- Substituting a sharp cap-volume upper bound into the support-restricted
far-field estimate supplies the codimension-one radius power. -/
theorem FiniteRetainedRootData.abs_booleanFilterError_le_far_mul_radiusPower
    {n : ℕ} {C : ℝ} {k q : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n)
    (i : Fin atoms.N) (x : sphereSet n) (D : ℝ) (hD : 0 ≤ D)
    (hkernel : ∀ y : sphereSet n,
      |booleanZonalKernelSection (n + 3) k atoms.base x y| ≤
        D * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) * Real.sqrt (sphereChordalSq x.1 y.1))⁻¹ ^ q)
    (hx : x ∉ sphereChordalCap (atoms.center i) (atoms.radius i))
    (hfar : 2 * atoms.radius i ≤
      Real.sqrt (sphereChordalSq x.1 (atoms.center i).1))
    (V : ℝ)
    (hcap : (normalizedSphereMeasure n).real
      (sphereChordalCap (atoms.center i) (atoms.radius i)) ≤
        V * atoms.radius i ^ (n - 1)) :
    |atoms.booleanFilterError i x.1| ≤
      ((D * (k : ℝ) ^ (n - 1) *
        (1 + (k : ℝ) *
          (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^ q) *
        (regular.jetBound * atoms.radius i ^ 2)) *
        (V * atoms.radius i ^ (n - 1)) := by
  have hraw := atoms.abs_booleanFilterError_le_far_mul_capMeasure
    regular hn i x D hD hkernel hx hfar
  have hfactor : 0 ≤
      (D * (k : ℝ) ^ (n - 1) *
        (1 + (k : ℝ) *
          (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^ q) *
        (regular.jetBound * atoms.radius i ^ 2) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hD (pow_nonneg (Nat.cast_nonneg k) _))
        (pow_nonneg (inv_nonneg.mpr (by positivity)) _))
      (mul_nonneg regular.jetBound_nonneg (sq_nonneg _))
  exact hraw.trans (mul_le_mul_of_nonneg_left hcap hfactor)

/-- For a regular retained root, its canonical polynomial error is exactly the
difference of two successive normalized zonal-filter errors. -/
theorem FiniteRetainedRootData.booleanFilterError_eq_filterError_sub
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n)
    (i : Fin atoms.N) (x : sphereSet n) :
    atoms.booleanFilterError i x.1 =
      normalizedZonalFilterError (n + 3) k atoms.base
        (fun y ↦ atoms.root i y.1) x -
      normalizedZonalFilterError (n + 3) k atoms.base
        (fun y ↦ normalizedFunctionZonalKernelValue (n + 3) k atoms.base
          (fun z ↦ atoms.root i z.1) y.1) x := by
  rw [atoms.booleanFilterError_eq_value regular hn i x.1]
  exact booleanFilteredFunctionValue_sub_eq_filterError_sub
    (n + 3) k atoms.base (fun y ↦ atoms.root i y.1) x

/-- Absolute retained-root error is controlled by the two successive
normalized zonal-filter errors. -/
theorem FiniteRetainedRootData.abs_booleanFilterError_le_filterErrors
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n)
    (i : Fin atoms.N) (x : sphereSet n) :
    |atoms.booleanFilterError i x.1| ≤
      |normalizedZonalFilterError (n + 3) k atoms.base
        (fun y ↦ atoms.root i y.1) x| +
      |normalizedZonalFilterError (n + 3) k atoms.base
        (fun y ↦ normalizedFunctionZonalKernelValue (n + 3) k atoms.base
          (fun z ↦ atoms.root i z.1) y.1) x| := by
  rw [atoms.booleanFilterError_eq_value regular hn i x.1]
  exact abs_booleanFilteredFunctionValue_sub_le_filterErrors
    (n + 3) k atoms.base (fun y ↦ atoms.root i y.1) x

/-- The zeroth scaled-jet estimate is the retained-root amplitude bound. -/
theorem FiniteRetainedRootRegularity.root_abs_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (i : Fin atoms.N)
    (x : Fin n → ℝ) :
    |atoms.root i x| ≤ regular.jetBound * atoms.radius i ^ 2 := by
  simpa using regular.scaled_jet i 0 (by omega) x

/-- The root amplitude and global filter error cancel the atom scale in the
cross term. -/
theorem abs_mul_le_of_scaled_amplitude_error
    {a e A E ρ κ : ℝ} (hA : 0 ≤ A)
    (hρ : 0 < ρ) (hκ : 0 < κ)
    (ha : |a| ≤ A * ρ ^ 2) (he : |e| ≤ E / (κ ^ 4 * ρ ^ 2)) :
    |a * e| ≤ A * E / κ ^ 4 := by
  rw [abs_mul]
  calc
    |a| * |e| ≤ (A * ρ ^ 2) * (E / (κ ^ 4 * ρ ^ 2)) :=
      mul_le_mul ha he (abs_nonneg _) (mul_nonneg hA (sq_nonneg ρ))
    _ = A * E / κ ^ 4 := by field_simp [hρ.ne', hκ.ne']

/-- A dyadic lower bound on an atom radius gives the reciprocal fourth-power
factor used in the squared-error summation. -/
theorem inv_eighth_radius_four_le_dyadic
    {κ ρ : ℝ} {j : ℕ} (hκ : 0 < κ)
    (hdyadic : (2 : ℝ) ^ j / κ ≤ ρ) :
    1 / (κ ^ 8 * ρ ^ 4) ≤ 1 / κ ^ 4 * (1 / 16 : ℝ) ^ j := by
  have hbase : 0 ≤ (2 : ℝ) ^ j / κ := by positivity
  have hpow : ((2 : ℝ) ^ j / κ) ^ 4 ≤ ρ ^ 4 :=
    pow_le_pow_left₀ hbase hdyadic 4
  have hden : κ ^ 4 * ((2 : ℝ) ^ j) ^ 4 ≤ κ ^ 8 * ρ ^ 4 := by
    calc
      κ ^ 4 * ((2 : ℝ) ^ j) ^ 4 =
          ((2 : ℝ) ^ j / κ) ^ 4 * κ ^ 8 := by
            field_simp [hκ.ne']
      _ ≤ ρ ^ 4 * κ ^ 8 := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = κ ^ 8 * ρ ^ 4 := by ring
  calc
    1 / (κ ^ 8 * ρ ^ 4) ≤ 1 / (κ ^ 4 * ((2 : ℝ) ^ j) ^ 4) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = 1 / κ ^ 4 * (1 / 16 : ℝ) ^ j := by
      field_simp [hκ.ne']
      have h16 : (16 : ℝ) ^ j = 2 ^ (j * 4) := by
        calc
          (16 : ℝ) ^ j = ((2 : ℝ) ^ 4) ^ j := by norm_num
          _ = 2 ^ (4 * j) := by rw [pow_mul]
          _ = 2 ^ (j * 4) := by rw [Nat.mul_comm]
      rw [div_pow, one_pow, h16, pow_mul]
      field_simp

/-- Squaring a localized atom error and using its dyadic radius lower bound
produces the `16⁻ʲ` estimate used by the finite packing argument. -/
theorem sq_le_dyadic_of_localized_error
    {e E κ ρ w : ℝ} {j : ℕ} (hκ : 0 < κ) (hρ : 0 < ρ)
    (hdyadic : (2 : ℝ) ^ j / κ ≤ ρ)
    (herror : |e| ≤ E / (κ ^ 4 * ρ ^ 2) * w) :
    e ^ 2 ≤ E ^ 2 / κ ^ 4 * (1 / 16 : ℝ) ^ j * w ^ 2 := by
  have hsquare : |e| ^ 2 ≤ (E / (κ ^ 4 * ρ ^ 2) * w) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg e) herror 2
  have hscale := inv_eighth_radius_four_le_dyadic hκ hdyadic
  calc
    e ^ 2 = |e| ^ 2 := by rw [sq_abs]
    _ ≤ (E / (κ ^ 4 * ρ ^ 2) * w) ^ 2 := hsquare
    _ = (E ^ 2 * w ^ 2) * (1 / (κ ^ 8 * ρ ^ 4)) := by
      field_simp [hκ.ne', hρ.ne']
    _ ≤ (E ^ 2 * w ^ 2) * (1 / κ ^ 4 * (1 / 16 : ℝ) ^ j) :=
      mul_le_mul_of_nonneg_left hscale (mul_nonneg (sq_nonneg E) (sq_nonneg w))
    _ = E ^ 2 / κ ^ 4 * (1 / 16 : ℝ) ^ j * w ^ 2 := by ring

/-- Analytic estimates before the cross term is assembled.  Only the global
`k⁻⁴ ρ⁻²` filter error and the squared-error packing remain as inputs. -/
structure FiniteBooleanFilterAnalyticBounds
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F)
    (regular : FiniteRetainedRootRegularity atoms) where
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  global_error : ∀ x ∈ sphereSet n, ∀ i,
    |atoms.booleanFilterError i x| ≤
      errorConstant / ((k : ℝ) ^ 4 * atoms.radius i ^ 2)
  cross_constant_budget :
    (atoms.overlapBound : ℝ) * (regular.jetBound * errorConstant) ≤ C / 4
  squareScaleBound : ℝ
  squareMajorant : Fin atoms.N → ((Fin n → ℝ) → ℝ)
  squareScaleBound_nonneg : 0 ≤ squareScaleBound
  square_error_le_majorant : ∀ x ∈ sphereSet n, ∀ i,
    (atoms.booleanFilterError i x) ^ 2 ≤ squareMajorant i x

  scale_packing : ∀ x ∈ sphereSet n, ∀ j : Fin atoms.J,
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j), squareMajorant i x ≤
      squareScaleBound * (1 / 16 : ℝ) ^ (j : ℕ)
  square_budget : (16 / 15 : ℝ) * squareScaleBound ≤
    C / (4 * (k : ℝ) ^ 4)

/-- The inverse-power decay weight, using the chordal distance
already developed for the spherical kernel. -/
def sphereChordalDecayWeight {n : ℕ} (L : ℕ) (center : sphereSet n)
    (radius : ℝ) (x : Fin n → ℝ) : ℝ :=
  (1 + Real.sqrt (sphereChordalSq x center.1) / radius)⁻¹ ^ L

/-- Within twice the supporting radius, the chosen decay weight loses at
most the fixed factor 3 ^ L. -/
theorem one_le_pow_mul_sphereChordalDecayWeight_of_near
    {n L : ℕ} (center x : sphereSet n) {radius : ℝ} (hradius : 0 < radius)
    (hnear : Real.sqrt (sphereChordalSq x.1 center.1) ≤ 2 * radius) :
    1 ≤ (3 : ℝ) ^ L * sphereChordalDecayWeight L center radius x.1 := by
  have hratio :
      Real.sqrt (sphereChordalSq x.1 center.1) / radius ≤ 2 :=
    (div_le_iff₀ hradius).2 hnear
  have hbasepos :
      0 < 1 + Real.sqrt (sphereChordalSq x.1 center.1) / radius := by
    positivity
  have hbasele :
      1 + Real.sqrt (sphereChordalSq x.1 center.1) / radius ≤ 3 := by
    linarith
  have hinv :
      1 ≤ 3 * (1 + Real.sqrt (sphereChordalSq x.1 center.1) / radius)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hbasepos).2 (by simpa using hbasele)
  unfold sphereChordalDecayWeight
  calc
    1 = (1 : ℝ) ^ L := (one_pow L).symm
    _ ≤ (3 * (1 + Real.sqrt (sphereChordalSq x.1 center.1) / radius)⁻¹) ^ L :=
      pow_le_pow_left₀ zero_le_one hinv L
    _ = 3 ^ L * (1 + Real.sqrt (sphereChordalSq x.1 center.1) / radius)⁻¹ ^ L :=
      mul_pow 3 _ L

/-- A global retained-root error estimate becomes localized in the near field,
with only the fixed 3 ^ L loss. -/
theorem FiniteRetainedRootData.abs_booleanFilterError_le_localized_of_near
    {n : ℕ} {C E : ℝ} {k L : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) (hE : 0 ≤ E)
    (i : Fin atoms.N) (x : sphereSet n)
    (hglobal : |atoms.booleanFilterError i x.1| ≤
      E / ((k : ℝ) ^ 4 * atoms.radius i ^ 2))
    (hnear : Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) ≤
      2 * atoms.radius i) :
    |atoms.booleanFilterError i x.1| ≤
      ((3 : ℝ) ^ L * E) / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
        sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x.1 := by
  have hone := one_le_pow_mul_sphereChordalDecayWeight_of_near
    (L := L) (atoms.center i) x (atoms.radius_pos i) hnear
  have hfactor : 0 ≤ E / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) :=
    div_nonneg hE (mul_nonneg (pow_nonneg (Nat.cast_nonneg k) _) (sq_nonneg _))
  calc
    |atoms.booleanFilterError i x.1| ≤
        E / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) := hglobal
    _ = E / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) * 1 := by ring
    _ ≤ E / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
        ((3 : ℝ) ^ L * sphereChordalDecayWeight L
          (atoms.center i) (atoms.radius i) x.1) :=
      mul_le_mul_of_nonneg_left hone hfactor
    _ = ((3 : ℝ) ^ L * E) / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
        sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x.1 := by ring

/-- Twice-radius separation automatically places a point outside the closed
supporting cap. -/
theorem not_mem_sphereChordalCap_of_two_mul_radius_le_sqrt
    {n : ℕ} (center x : sphereSet n) {radius : ℝ} (hradius : 0 < radius)
    (hfar : 2 * radius ≤ Real.sqrt (sphereChordalSq x.1 center.1)) :
    x ∉ sphereChordalCap center radius := by
  intro hx
  have hsq : sphereChordalSq x.1 center.1 ≤ radius ^ 2 := by
    simpa only [sphereChordalCap, Set.mem_setOf_eq] using hx
  have hsqrt : Real.sqrt (sphereChordalSq x.1 center.1) ≤ radius := by
    rw [Real.sqrt_le_iff]
    exact ⟨hradius.le, hsq⟩
  linarith

/-- Away from twice the supporting radius, kernel localization and cap volume
give the exact quartic retained-root error bound. -/
theorem exists_retainedRoot_far_booleanFilterError_localization
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
        (atoms : FiniteRetainedRootData n C k F)
        (regular : FiniteRetainedRootRegularity atoms), 1 ≤ k →
      ∀ (i : Fin atoms.N) (x : sphereSet n),
        x ∉ sphereChordalCap (atoms.center i) (atoms.radius i) →
        2 * atoms.radius i ≤
          Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) →
        |atoms.booleanFilterError i x.1| ≤
          (regular.jetBound * E) /
              ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
            sphereChordalDecayWeight (n + 3)
              (atoms.center i) (atoms.radius i) x.1 := by
  obtain ⟨D, hD, hkernel⟩ :=
    exists_fixedPower_booleanZonalKernelSection_chordalLocalization hn
  obtain ⟨V, hV, hcap⟩ := exists_uniform_chordalCap_power_upper hn
  refine ⟨D * V, mul_nonneg hD hV, ?_⟩
  intro C k F atoms regular hk i x hx hfar
  have hraw := atoms.abs_booleanFilterError_le_far_mul_radiusPower
    regular (by omega) i x D hD (hkernel k hk atoms.base x) hx hfar V
    (hcap (atoms.center i) (atoms.radius i) (atoms.radius_pos i).le
      (atoms.radius_upper i))
  have hscale := kernelRadius_halfDistance_decay_le hn hk
    (atoms.radius_pos i) (atoms.radius_lower i) hfar
  unfold sphereChordalDecayWeight
  calc
    |atoms.booleanFilterError i x.1| ≤
        ((D * (k : ℝ) ^ (n - 1) *
          (1 + (k : ℝ) *
            (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^
              (2 * (n + 3))) *
          (regular.jetBound * atoms.radius i ^ 2)) *
          (V * atoms.radius i ^ (n - 1)) := hraw
    _ = (regular.jetBound * (D * V)) *
        ((k : ℝ) ^ (n - 1) * atoms.radius i ^ (n + 1) *
          (1 + (k : ℝ) *
            (Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) / 2))⁻¹ ^
              (2 * (n + 3))) := by
      rw [show n + 1 = 2 + (n - 1) by omega, pow_add]
      ring
    _ ≤ (regular.jetBound * (D * V)) *
        (1 / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
          (1 + Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) /
            atoms.radius i)⁻¹ ^ (n + 3)) :=
      mul_le_mul_of_nonneg_left hscale
        (mul_nonneg regular.jetBound_nonneg (mul_nonneg hD hV))
    _ = (regular.jetBound * (D * V)) /
          ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
        (1 + Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) /
          atoms.radius i)⁻¹ ^ (n + 3) := by ring

/-- Combining a uniform global quartic bound with the proved kernel tail gives
the localized error estimate at every sphere point. -/
theorem exists_retainedRoot_localized_booleanFilterError_of_global
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ {B C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ},
        0 ≤ B →
        ∀ (atoms : FiniteRetainedRootData n C k F)
          (regular : FiniteRetainedRootRegularity atoms), 1 ≤ k →
        (∀ (i : Fin atoms.N) (x : sphereSet n),
          |atoms.booleanFilterError i x.1| ≤
            (regular.jetBound * B) / ((k : ℝ) ^ 4 * atoms.radius i ^ 2)) →
        ∀ (i : Fin atoms.N) (x : sphereSet n),
          |atoms.booleanFilterError i x.1| ≤
            (regular.jetBound * ((3 : ℝ) ^ (n + 3) * B + E)) /
                ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
              sphereChordalDecayWeight (n + 3)
                (atoms.center i) (atoms.radius i) x.1 := by
  obtain ⟨E, hE, hfar⟩ :=
    exists_retainedRoot_far_booleanFilterError_localization hn
  refine ⟨E, hE, ?_⟩
  intro B C k F hB atoms regular hk hglobal i x
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hden : 0 ≤ (k : ℝ) ^ 4 * atoms.radius i ^ 2 :=
    mul_nonneg (pow_nonneg hkpos.le _) (sq_nonneg _)
  have hw : 0 ≤ sphereChordalDecayWeight (n + 3)
      (atoms.center i) (atoms.radius i) x.1 := by
    unfold sphereChordalDecayWeight
    apply pow_nonneg
    apply inv_nonneg.mpr
    have hratio : 0 ≤ Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) /
        atoms.radius i := div_nonneg (Real.sqrt_nonneg _) (atoms.radius_pos i).le
    linarith
  by_cases hnear :
      Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) ≤ 2 * atoms.radius i
  · have hlocal := atoms.abs_booleanFilterError_le_localized_of_near
      (L := n + 3) (mul_nonneg regular.jetBound_nonneg hB) i x (hglobal i x) hnear
    have hcoeff :
        (3 : ℝ) ^ (n + 3) * (regular.jetBound * B) ≤
          regular.jetBound * ((3 : ℝ) ^ (n + 3) * B + E) := by
      nlinarith [mul_nonneg regular.jetBound_nonneg hE]
    exact hlocal.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hcoeff hden) hw)
  · have hfarDist :
        2 * atoms.radius i ≤
          Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) :=
      le_of_not_ge hnear
    have hout := not_mem_sphereChordalCap_of_two_mul_radius_le_sqrt
      (atoms.center i) x (atoms.radius_pos i) hfarDist
    have hlocal := hfar atoms regular hk i x hout hfarDist
    have hcoeff :
        regular.jetBound * E ≤
          regular.jetBound * ((3 : ℝ) ^ (n + 3) * B + E) := by
      nlinarith [mul_nonneg regular.jetBound_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (n + 3)) hB)]
    exact hlocal.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hcoeff hden) hw)

/-- The derivative-commutation estimate used to apply the abstract quartic
Boolean-filter theorem to every retained root. -/
def FiniteRetainedRootFilterErrorSecondDifference
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F)
    (regular : FiniteRetainedRootRegularity atoms) : Prop :=
  ∀ (i : Fin atoms.N) (x y : sphereSet n),
    |normalizedZonalFilterError (n + 3) k atoms.base
          (fun z ↦ atoms.root i z.1) y +
        normalizedZonalFilterError (n + 3) k atoms.base
          (fun z ↦ atoms.root i z.1) (sphereAxialReflection x y) -
        2 * normalizedZonalFilterError (n + 3) k atoms.base
          (fun z ↦ atoms.root i z.1) x| ≤
      (2 * ((regular.jetBound / atoms.radius i ^ 2) / (k : ℝ) ^ 2)) *
        sphereChordalSq y.1 x.1

/-- An equivalent derivative-commutation estimate obtained from reflection
equivariance: apply the one-step filter error to the root's
symmetric increment and control its oscillation from the increment center. -/
def FiniteRetainedRootFilterIncrementOscillation
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F)
    (regular : FiniteRetainedRootRegularity atoms) : Prop :=
  ∀ (i : Fin atoms.N) (x y : sphereSet n),
    |normalizedZonalFilterError (n + 3) k atoms.base
          (sphereSymmetricIncrement (fun z ↦ atoms.root i z.1) x) y -
        normalizedZonalFilterError (n + 3) k atoms.base
          (sphereSymmetricIncrement (fun z ↦ atoms.root i z.1) x) x| ≤
      (2 * ((regular.jetBound / atoms.radius i ^ 2) / (k : ℝ) ^ 2)) *
        sphereChordalSq y.1 x.1

/-- Reflection equivariance converts filtered-increment oscillation into the
second-difference estimate required by the quartic Boolean-filter argument. -/
theorem FiniteRetainedRootFilterIncrementOscillation.toSecondDifference
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    {regular : FiniteRetainedRootRegularity atoms}
    (hn : 2 ≤ n)
    (h : FiniteRetainedRootFilterIncrementOscillation atoms regular) :
    FiniteRetainedRootFilterErrorSecondDifference atoms regular := by
  intro i x y
  change |sphereSymmetricIncrement
      (normalizedZonalFilterError (n + 3) k atoms.base
        (fun z ↦ atoms.root i z.1)) x y| ≤
    (2 * ((regular.jetBound / atoms.radius i ^ 2) / (k : ℝ) ^ 2)) * sphereChordalSq y.1 x.1
  rw [sphereSymmetricIncrement_normalizedZonalFilterError hn
    (n + 3) k atoms.base (fun z ↦ atoms.root i z.1)
    ((regular.root_contDiff i).continuous.comp continuous_subtype_val) x y]
  exact h i x y
/-- The second-difference estimate implies the complete
localized Boolean-filter estimate, uniformly in all retained-root data. -/
theorem exists_retainedRoot_localized_booleanFilterError_bound
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
        (atoms : FiniteRetainedRootData n C k F)
        (regular : FiniteRetainedRootRegularity atoms), 1 ≤ k →
        FiniteRetainedRootFilterErrorSecondDifference atoms regular →
      ∀ (i : Fin atoms.N) (x : sphereSet n),
        |atoms.booleanFilterError i x.1| ≤
          (regular.jetBound * E) / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
            sphereChordalDecayWeight (n + 3)
              (atoms.center i) (atoms.radius i) x.1 := by
  obtain ⟨B, hB, hglobal⟩ :=
    exists_retainedRoot_global_booleanFilterError_bound hn
  obtain ⟨T, hT, hlocal⟩ :=
    exists_retainedRoot_localized_booleanFilterError_of_global hn
  let E : ℝ := (3 : ℝ) ^ (n + 3) * B + T
  have hE : 0 ≤ E := add_nonneg
    (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (n + 3)) hB) hT
  refine ⟨E, hE, ?_⟩
  intro C k F atoms regular hk hsecond
  apply hlocal hB atoms regular hk
  intro i x
  exact hglobal atoms regular hk i x (hsecond i x)

/-- The geodesic decay weight used in the angular localization estimate. -/
def sphereAngularDecayWeight {n : ℕ} (L : ℕ) (center x : sphereSet n)
    (radius : ℝ) : ℝ :=
  (1 + sphereAngularDistance x center / radius)⁻¹ ^ L

/-- Chordal distance is bounded by angular distance on the unit sphere. -/
theorem sqrt_sphereChordalSq_le_sphereAngularDistance {n : ℕ}
    (x center : sphereSet n) :
    Real.sqrt (sphereChordalSq x.1 center.1) ≤ sphereAngularDistance x center := by
  rw [Real.sqrt_le_iff]
  exact ⟨sphereAngularDistance_nonneg x center,
    sphereChordalSq_le_sphereAngularDistance_sq x center⟩

/-- Replacing angular distance by chordal distance enlarges the decay weight,
which is the direction needed to transfer the angular localized bound. -/
theorem sphereAngularDecayWeight_le_chordal {n : ℕ} (L : ℕ)
    (center x : sphereSet n) {radius : ℝ} (hradius : 0 < radius) :
    sphereAngularDecayWeight L center x radius ≤
      sphereChordalDecayWeight L center radius x.1 := by
  have hbase :
      1 + Real.sqrt (sphereChordalSq x.1 center.1) / radius ≤
        1 + sphereAngularDistance x center / radius := by
    gcongr
    exact sqrt_sphereChordalSq_le_sphereAngularDistance x center
  have hinv :
      (1 + sphereAngularDistance x center / radius)⁻¹ ≤
        (1 + Real.sqrt (sphereChordalSq x.1 center.1) / radius)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (by positivity) hbase
  have hangularBase : 0 ≤ 1 + sphereAngularDistance x center / radius := by
    linarith [div_nonneg (sphereAngularDistance_nonneg x center) hradius.le]
  unfold sphereAngularDecayWeight sphereChordalDecayWeight
  exact pow_le_pow_left₀ (inv_nonneg.mpr hangularBase) hinv L

theorem sphereChordalDecayWeight_nonneg {n : ℕ} (L : ℕ) (center : sphereSet n)
    {radius : ℝ} (hradius : 0 < radius) (x : Fin n → ℝ) :
    0 ≤ sphereChordalDecayWeight L center radius x := by
  unfold sphereChordalDecayWeight
  positivity

/-- Chordal decay weights are at most one for positive radii. -/
theorem sphereChordalDecayWeight_le_one {n : ℕ} (L : ℕ) (center : sphereSet n)
    {radius : ℝ} (hradius : 0 < radius) (x : Fin n → ℝ) :
    sphereChordalDecayWeight L center radius x ≤ 1 := by
  unfold sphereChordalDecayWeight
  have hbase : 1 ≤ 1 + Real.sqrt (sphereChordalSq x center.1) / radius := by
    linarith [div_nonneg (Real.sqrt_nonneg (sphereChordalSq x center.1))
      (le_of_lt hradius)]
  have hinv : (1 + Real.sqrt (sphereChordalSq x center.1) / radius)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hbase
  calc
    (1 + Real.sqrt (sphereChordalSq x center.1) / radius)⁻¹ ^ L ≤ 1 ^ L :=
      pow_le_pow_left₀ (by positivity) hinv L
    _ = 1 := one_pow L

/-- A center at least m supporting radii away contributes at most the
corresponding inverse-power annular weight. -/
theorem sphereChordalDecayWeight_le_of_mul_radius_le_sqrt
    {n L : ℕ} (center : sphereSet n) {radius m : ℝ} (hradius : 0 < radius)
    (hm : 0 ≤ m) (x : Fin n → ℝ)
    (hfar : m * radius ≤ Real.sqrt (sphereChordalSq x center.1)) :
    sphereChordalDecayWeight L center radius x ≤ (1 + m)⁻¹ ^ L := by
  have hratio :
      m ≤ Real.sqrt (sphereChordalSq x center.1) / radius := by
    exact (le_div_iff₀ hradius).2 hfar
  have hbase :
      1 + m ≤ 1 + Real.sqrt (sphereChordalSq x center.1) / radius := by
    linarith
  have hsmallPos : 0 < 1 + m := by linarith
  have hlargeNonneg :
      0 ≤ 1 + Real.sqrt (sphereChordalSq x center.1) / radius := by
    positivity
  have hinv :
      (1 + Real.sqrt (sphereChordalSq x center.1) / radius)⁻¹ ≤
        (1 + m)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hsmallPos hbase
  unfold sphereChordalDecayWeight
  exact pow_le_pow_left₀ (inv_nonneg.mpr hlargeNonneg) hinv L

/-- Summing an annular decay estimate costs only the number of centers in
that annular subfamily. -/
theorem FiniteRetainedRootData.sum_decayWeight_le_card_mul_of_far
    {n : ℕ} {C : ℝ} {k L : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F)
    (s : Finset (Fin atoms.N)) (x : Fin n → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hfar : ∀ i ∈ s,
      m * atoms.radius i ≤ Real.sqrt (sphereChordalSq x (atoms.center i).1)) :
    ∑ i ∈ s, sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x ≤
      (s.card : ℝ) * (1 + m)⁻¹ ^ L := by
  calc
    ∑ i ∈ s, sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x ≤
        ∑ _i ∈ s, (1 + m)⁻¹ ^ L := by
      apply Finset.sum_le_sum
      intro i hi
      exact sphereChordalDecayWeight_le_of_mul_radius_le_sqrt
        (atoms.center i) (atoms.radius_pos i) hm x (hfar i hi)
    _ = (s.card : ℝ) * (1 + m)⁻¹ ^ L := by simp

/-- A dyadic shell distance and its cardinality budget imply the desired
geometric weighted bound for that shell. -/
theorem FiniteRetainedRootData.sum_decayWeight_le_half_pow_of_shell
    {n : ℕ} {C A : ℝ} {k L q : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F)
    (s : Finset (Fin atoms.N)) (x : Fin n → ℝ)
    (hfar : ∀ i ∈ s, (2 : ℝ) ^ q * atoms.radius i ≤
      Real.sqrt (sphereChordalSq x (atoms.center i).1))
    (hcard : (s.card : ℝ) * (1 + (2 : ℝ) ^ q)⁻¹ ^ L ≤
      A * (1 / 2 : ℝ) ^ q) :
    ∑ i ∈ s, sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x ≤
      A * (1 / 2 : ℝ) ^ q := by
  exact (atoms.sum_decayWeight_le_card_mul_of_far s x
    (pow_nonneg (by norm_num) q) hfar).trans hcard

/-- Being outside a positive-radius chordal cap is equivalent to lying
strictly beyond one supporting radius. -/
theorem radius_lt_sqrt_sphereChordalSq_of_not_le_sq
    {n : ℕ} (center : sphereSet n) {radius : ℝ} (hradius : 0 < radius)
    (x : Fin n → ℝ)
    (houtside : ¬ sphereChordalSq x center.1 ≤ radius ^ 2) :
    radius < Real.sqrt (sphereChordalSq x center.1) := by
  have hsq : radius ^ 2 < sphereChordalSq x center.1 :=
    lt_of_not_ge houtside
  calc
    radius = Real.sqrt (radius ^ 2) := (Real.sqrt_sq hradius.le).symm
    _ < Real.sqrt (sphereChordalSq x center.1) :=
      Real.sqrt_lt_sqrt (sq_nonneg radius) hsq

/-- Consequently every off-cap decay weight starts below 2⁻ᴸ. -/
theorem sphereChordalDecayWeight_le_inv_two_pow_of_not_le_sq
    {n L : ℕ} (center : sphereSet n) {radius : ℝ} (hradius : 0 < radius)
    (x : Fin n → ℝ) (houtside : ¬ sphereChordalSq x center.1 ≤ radius ^ 2) :
    sphereChordalDecayWeight L center radius x ≤ (2 : ℝ)⁻¹ ^ L := by
  simpa only [one_mul, one_add_one_eq_two] using
    sphereChordalDecayWeight_le_of_mul_radius_le_sqrt center hradius
      (m := (1 : ℝ)) zero_le_one x
      (by simpa using
        (radius_lt_sqrt_sphereChordalSq_of_not_le_sq center hradius x houtside).le)

/-- At one dyadic scale, decay weights from caps containing the evaluation
point cost at most the retained-root overlap bound. -/
theorem FiniteRetainedRootData.sum_scale_decayWeight_near_le_overlapBound
    {n : ℕ} {C : ℝ} {k L : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) (j : Fin atoms.J) :
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j ∧
        sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2),
      sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x ≤
        (atoms.overlapBound : ℝ) := by
  have hcard :
      (Finset.univ.filter (fun i => atoms.scale i = j ∧
        sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).card ≤
      (Finset.univ.filter (fun i =>
        sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).card := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.2
  calc
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j ∧
        sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2),
        sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x ≤
        ∑ _i ∈ Finset.univ.filter (fun i => atoms.scale i = j ∧
          sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2), (1 : ℝ) := by
      gcongr with i hi
      exact sphereChordalDecayWeight_le_one L (atoms.center i) (atoms.radius_pos i) x
    _ = ((Finset.univ.filter (fun i => atoms.scale i = j ∧
        sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).card : ℝ) := by simp
    _ ≤ ((Finset.univ.filter (fun i =>
        sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (atoms.overlapBound : ℝ) := by
      exact_mod_cast atoms.cap_overlap_card x hx

/-- Once the off-cap tail is bounded, the full fixed-scale decay sum is
bounded by that tail plus the overlap contribution. -/
theorem FiniteRetainedRootData.sum_scale_decayWeight_le_overlap_add_of_far
    {n : ℕ} {C P : ℝ} {k L : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) (j : Fin atoms.J)
    (hfar : ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j ∧
        ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2),
      sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x ≤ P) :
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j),
      sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x ≤
        (atoms.overlapBound : ℝ) + P := by
  let s : Finset (Fin atoms.N) :=
    Finset.univ.filter (fun i => atoms.scale i = j)
  let p : Fin atoms.N → Prop := fun i =>
    sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2
  have hsplit := Finset.sum_filter_add_sum_filter_not s p
    (fun i => sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x)
  calc
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j),
        sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x =
        ∑ i ∈ s.filter p,
            sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x +
          ∑ i ∈ s.filter (fun i => ¬ p i),
            sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x := hsplit.symm
    _ ≤ (atoms.overlapBound : ℝ) + P := by
      apply add_le_add
      · simpa only [s, p, Finset.filter_filter] using
          atoms.sum_scale_decayWeight_near_le_overlapBound x hx j
      · simpa [s, p, Finset.filter_filter] using hfar

/-- Geometric control on each annular shell gives a uniform bound for the
whole off-cap tail at one retained-root scale. -/
theorem FiniteRetainedRootData.sum_scale_far_decayWeight_le_two_mul_of_shell_bounds
    {n : ℕ} {C A : ℝ} {k L R : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) (x : Fin n → ℝ)
    (j : Fin atoms.J) (shell : Fin atoms.N → Fin R) (hA : 0 ≤ A)
    (hshell : ∀ q : Fin R,
      ∑ i ∈ (Finset.univ.filter (fun i => atoms.scale i = j ∧
          ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
            (fun i => shell i = q),
        sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x ≤
          A * (1 / 2 : ℝ) ^ (q : ℕ)) :
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j ∧
        ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2),
      sphereChordalDecayWeight L (atoms.center i) (atoms.radius i) x ≤
        2 * A := by
  exact sum_finset_le_two_mul_of_dyadic_fibers
    (Finset.univ.filter (fun i => atoms.scale i = j ∧
      ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2))
    shell (fun i => sphereChordalDecayWeight L
      (atoms.center i) (atoms.radius i) x) A hA hshell

/-- Squaring a decay weight doubles its exponent. -/
theorem sphereChordalDecayWeight_two_mul {n : ℕ} (L : ℕ)
    (center : sphereSet n) (radius : ℝ) (x : Fin n → ℝ) :
    sphereChordalDecayWeight (2 * L) center radius x =
      sphereChordalDecayWeight L center radius x ^ 2 := by
  unfold sphereChordalDecayWeight
  rw [Nat.mul_comm 2 L, pow_mul]

/-- Exact pointwise localization and packing hypotheses for the Boolean-filter estimate.
The dyadic squared estimate is derived from localization and the radius scale. -/
structure FiniteBooleanFilterManuscriptBounds
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F)
    (regular : FiniteRetainedRootRegularity atoms) where
  decayExponent : ℕ
  decay_exponent_large : n < 2 * decayExponent
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  localized_error : ∀ x ∈ sphereSet n, ∀ i,
    |atoms.booleanFilterError i x| ≤
      errorConstant / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
        sphereChordalDecayWeight decayExponent (atoms.center i) (atoms.radius i) x
  cross_constant_budget :
    (atoms.overlapBound : ℝ) * (regular.jetBound * errorConstant) ≤ C / 4
  packingConstant : ℝ
  packingConstant_nonneg : 0 ≤ packingConstant
  scale_decay_packing : ∀ x ∈ sphereSet n, ∀ j : Fin atoms.J,
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j),
      sphereChordalDecayWeight (2 * decayExponent)
        (atoms.center i) (atoms.radius i) x ≤ packingConstant
  square_constant_budget :
    (16 / 15 : ℝ) * (errorConstant ^ 2 * packingConstant) ≤ C / 4

/-- The second-difference, packing, and constant budgets assemble directly
into the Boolean-filter bounds. -/
theorem exists_finiteBooleanFilterManuscriptBounds_of_secondDifference
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
        (atoms : FiniteRetainedRootData n C k F)
        (regular : FiniteRetainedRootRegularity atoms), 1 ≤ k →
        FiniteRetainedRootFilterErrorSecondDifference atoms regular →
      ∀ (packingConstant : ℝ), 0 ≤ packingConstant →
        (∀ x ∈ sphereSet n, ∀ j : Fin atoms.J,
          ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j),
            sphereChordalDecayWeight (2 * (n + 3))
              (atoms.center i) (atoms.radius i) x ≤ packingConstant) →
        (atoms.overlapBound : ℝ) *
            (regular.jetBound * (regular.jetBound * E)) ≤ C / 4 →
        (16 / 15 : ℝ) *
            ((regular.jetBound * E) ^ 2 * packingConstant) ≤ C / 4 →
        Nonempty (FiniteBooleanFilterManuscriptBounds atoms regular) := by
  obtain ⟨E, hE, hlocalized⟩ :=
    exists_retainedRoot_localized_booleanFilterError_bound hn
  refine ⟨E, hE, ?_⟩
  intro C k F atoms regular hk hsecond packingConstant hpackingConstant
    hpacking hcross hsquare
  refine ⟨{
    decayExponent := n + 3
    decay_exponent_large := by omega
    errorConstant := regular.jetBound * E
    errorConstant_nonneg := mul_nonneg regular.jetBound_nonneg hE
    localized_error := ?_
    cross_constant_budget := hcross
    packingConstant := packingConstant
    packingConstant_nonneg := hpackingConstant
    scale_decay_packing := hpacking
    square_constant_budget := hsquare }⟩
  intro x hx i
  exact hlocalized atoms regular hk hsecond i ⟨x, hx⟩

/-- The atom-side analytic data used to build the Boolean-filter bounds.
Its constant `E` is dimension-dependent and supplied by the preceding
existence theorem. -/
structure FiniteRetainedRootManuscriptInput
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) (E : ℝ) where
  regular : FiniteRetainedRootRegularity atoms
  dyadic : FiniteRetainedRootDyadic atoms
  filterIncrementOscillation :
    FiniteRetainedRootFilterIncrementOscillation atoms regular
  farShellCount : ℕ
  farShell : sphereSet n → Fin atoms.N → Fin farShellCount
  farShellConstant : ℝ
  farShellConstant_nonneg : 0 ≤ farShellConstant
  scale_far_shell_distance : ∀ x (hx : x ∈ sphereSet n),
      ∀ (j : Fin atoms.J) (q : Fin farShellCount) i,
    i ∈ (Finset.univ.filter (fun i => atoms.scale i = j ∧
        ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
          (fun i => farShell ⟨x, hx⟩ i = q) →
      (2 : ℝ) ^ (q : ℕ) * atoms.radius i ≤
        Real.sqrt (sphereChordalSq x (atoms.center i).1)
  scale_far_shell_card_budget : ∀ x (hx : x ∈ sphereSet n),
      ∀ (j : Fin atoms.J) (q : Fin farShellCount),
    (((Finset.univ.filter (fun i => atoms.scale i = j ∧
        ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
          (fun i => farShell ⟨x, hx⟩ i = q)).card : ℝ) *
        (1 + (2 : ℝ) ^ (q : ℕ))⁻¹ ^ (2 * (n + 3)) ≤
      farShellConstant * (1 / 2 : ℝ) ^ (q : ℕ)
  cross_constant_budget :
    (atoms.overlapBound : ℝ) *
      (regular.jetBound * (regular.jetBound * E)) ≤ C / 4
  square_constant_budget :
    (16 / 15 : ℝ) * ((regular.jetBound * E) ^ 2 *
      ((atoms.overlapBound : ℝ) + 2 * farShellConstant)) ≤ C / 4

/-- Uniform existence of the atom-side analytic payload before it is
converted to Boolean-filter bounds. -/
def HasFiniteRetainedRootManuscriptInput
    (n : ℕ) (E C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k → Nonempty (Σ atoms : FiniteRetainedRootData n C k F,
      FiniteRetainedRootManuscriptInput atoms E)

/-- Package the angular localization estimate into the
chordal interface used by the finite packing and summation layers. -/
def FiniteBooleanFilterManuscriptBounds.ofAngularLocalization
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    {regular : FiniteRetainedRootRegularity atoms}
    (decayExponent : ℕ) (hdecay : n < 2 * decayExponent)
    (errorConstant : ℝ) (herrorConstant : 0 ≤ errorConstant)
    (angular_error : ∀ x (hx : x ∈ sphereSet n), ∀ i,
      |atoms.booleanFilterError i x| ≤
        errorConstant / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
          sphereAngularDecayWeight decayExponent (atoms.center i) ⟨x, hx⟩
            (atoms.radius i))
    (cross_budget :
      (atoms.overlapBound : ℝ) * (regular.jetBound * errorConstant) ≤ C / 4)
    (packingConstant : ℝ) (hpackingConstant : 0 ≤ packingConstant)
    (packing : ∀ x ∈ sphereSet n, ∀ j : Fin atoms.J,
      ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j),
        sphereChordalDecayWeight (2 * decayExponent)
          (atoms.center i) (atoms.radius i) x ≤ packingConstant)
    (square_budget :
      (16 / 15 : ℝ) * (errorConstant ^ 2 * packingConstant) ≤ C / 4) :
    FiniteBooleanFilterManuscriptBounds atoms regular := by
  refine {
    decayExponent := decayExponent
    decay_exponent_large := hdecay
    errorConstant := errorConstant
    errorConstant_nonneg := herrorConstant
    localized_error := ?_
    cross_constant_budget := cross_budget
    packingConstant := packingConstant
    packingConstant_nonneg := hpackingConstant
    scale_decay_packing := packing
    square_constant_budget := square_budget }
  intro x hx i
  calc
    |atoms.booleanFilterError i x| ≤
        errorConstant / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
          sphereAngularDecayWeight decayExponent (atoms.center i) ⟨x, hx⟩
            (atoms.radius i) := angular_error x hx i
    _ ≤ errorConstant / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
          sphereChordalDecayWeight decayExponent (atoms.center i) (atoms.radius i) x :=
      mul_le_mul_of_nonneg_left
        (sphereAngularDecayWeight_le_chordal _ _ _ (atoms.radius_pos i))
        (div_nonneg herrorConstant (by positivity))

/-- Localized filter estimates in the form produced directly by the kernel
argument.  Fixed-scale packing is stated only for the decay weights; the
`16⁻ʲ` square budget is assembled below. -/
structure FiniteBooleanFilterLocalizedBounds
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F)
    (regular : FiniteRetainedRootRegularity atoms) where
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  global_error : ∀ x ∈ sphereSet n, ∀ i,
    |atoms.booleanFilterError i x| ≤
      errorConstant / ((k : ℝ) ^ 4 * atoms.radius i ^ 2)
  cross_constant_budget :
    (atoms.overlapBound : ℝ) * (regular.jetBound * errorConstant) ≤ C / 4
  squareAtomConstant : ℝ
  squareAtomConstant_nonneg : 0 ≤ squareAtomConstant
  weight : Fin atoms.N → ((Fin n → ℝ) → ℝ)
  weight_nonneg : ∀ i x, 0 ≤ weight i x
  square_error_le_weight : ∀ x ∈ sphereSet n, ∀ i,
    (atoms.booleanFilterError i x) ^ 2 ≤
      squareAtomConstant / (k : ℝ) ^ 4 *
        (1 / 16 : ℝ) ^ (atoms.scale i : ℕ) * weight i x
  packingConstant : ℝ
  packingConstant_nonneg : 0 ≤ packingConstant
  scale_weight_packing : ∀ x ∈ sphereSet n, ∀ j : Fin atoms.J,
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j), weight i x ≤
      packingConstant
  square_constant_budget :
    (16 / 15 : ℝ) * (squareAtomConstant * packingConstant) ≤ C / 4

/-- Specialize the summation interface to the chosen chordal decay weight. -/
def FiniteBooleanFilterManuscriptBounds.toLocalizedBounds
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    {regular : FiniteRetainedRootRegularity atoms}
    (manuscript : FiniteBooleanFilterManuscriptBounds atoms regular)
    (dyadic : FiniteRetainedRootDyadic atoms) (hk : 1 ≤ k) :
    FiniteBooleanFilterLocalizedBounds atoms regular := by
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  refine {
  errorConstant := manuscript.errorConstant
  errorConstant_nonneg := manuscript.errorConstant_nonneg
  global_error := by
    intro x hx i
    calc
      |atoms.booleanFilterError i x| ≤
          manuscript.errorConstant / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) *
            sphereChordalDecayWeight manuscript.decayExponent
              (atoms.center i) (atoms.radius i) x := manuscript.localized_error x hx i
      _ ≤ manuscript.errorConstant / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left
          (sphereChordalDecayWeight_le_one _ _ (atoms.radius_pos i) x)
          (div_nonneg manuscript.errorConstant_nonneg (by positivity))
      _ = manuscript.errorConstant / ((k : ℝ) ^ 4 * atoms.radius i ^ 2) := mul_one _
  cross_constant_budget := manuscript.cross_constant_budget
  squareAtomConstant := manuscript.errorConstant ^ 2
  squareAtomConstant_nonneg := sq_nonneg manuscript.errorConstant
  weight := fun i x ↦ sphereChordalDecayWeight (2 * manuscript.decayExponent)
    (atoms.center i) (atoms.radius i) x
  weight_nonneg := fun i x ↦
    sphereChordalDecayWeight_nonneg _ _ (atoms.radius_pos i) x
  square_error_le_weight := ?_
  packingConstant := manuscript.packingConstant
  packingConstant_nonneg := manuscript.packingConstant_nonneg
  scale_weight_packing := manuscript.scale_decay_packing
  square_constant_budget := manuscript.square_constant_budget }
  intro x hx i
  rw [sphereChordalDecayWeight_two_mul]
  exact sq_le_dyadic_of_localized_error hkpos (atoms.radius_pos i)
    (dyadic.scale_lower i) (manuscript.localized_error x hx i)

/-- Fixed-scale weight packing implies the geometric squared-error majorant. -/
def FiniteBooleanFilterLocalizedBounds.toAnalyticBounds
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    {regular : FiniteRetainedRootRegularity atoms}
    (localized : FiniteBooleanFilterLocalizedBounds atoms regular) (hk : 1 ≤ k) :
    FiniteBooleanFilterAnalyticBounds atoms regular := by
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  refine {
    errorConstant := localized.errorConstant
    errorConstant_nonneg := localized.errorConstant_nonneg
    global_error := localized.global_error
    cross_constant_budget := localized.cross_constant_budget
    squareScaleBound :=
      localized.squareAtomConstant * localized.packingConstant / (k : ℝ) ^ 4
    squareMajorant := fun i x ↦
      localized.squareAtomConstant / (k : ℝ) ^ 4 *
        (1 / 16 : ℝ) ^ (atoms.scale i : ℕ) * localized.weight i x
    squareScaleBound_nonneg := div_nonneg
      (mul_nonneg localized.squareAtomConstant_nonneg localized.packingConstant_nonneg)
      (by positivity)
    square_error_le_majorant := localized.square_error_le_weight
    scale_packing := ?_
    square_budget := ?_ }
  · intro x hx j
    calc
      ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j),
          localized.squareAtomConstant / (k : ℝ) ^ 4 *
            (1 / 16 : ℝ) ^ (atoms.scale i : ℕ) * localized.weight i x =
          (localized.squareAtomConstant / (k : ℝ) ^ 4 *
            (1 / 16 : ℝ) ^ (j : ℕ)) *
            ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j), localized.weight i x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ ≤ (localized.squareAtomConstant / (k : ℝ) ^ 4 *
            (1 / 16 : ℝ) ^ (j : ℕ)) * localized.packingConstant :=
        mul_le_mul_of_nonneg_left (localized.scale_weight_packing x hx j)
          (mul_nonneg (div_nonneg localized.squareAtomConstant_nonneg (by positivity))
            (by positivity))
      _ = (localized.squareAtomConstant * localized.packingConstant / (k : ℝ) ^ 4) *
          (1 / 16 : ℝ) ^ (j : ℕ) := by ring
  · calc
      (16 / 15 : ℝ) * (localized.squareAtomConstant * localized.packingConstant /
          (k : ℝ) ^ 4) =
          ((16 / 15 : ℝ) * (localized.squareAtomConstant * localized.packingConstant)) /
            (k : ℝ) ^ 4 := by ring
      _ ≤ (C / 4) / (k : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right localized.square_constant_budget (by positivity)
      _ = C / (4 * (k : ℝ) ^ 4) := by field_simp [hkpos.ne']

/-- The genuinely analytic Boolean-filter payload.  Its polynomial is fixed
to the canonical filter; continuity and both coefficient-integrability
obligations are supplied automatically by the preceding lemmas. -/
structure FiniteBooleanFilterBounds
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteRetainedRootData n C k F) where
  crossAtomBound : ℝ
  squareScaleBound : ℝ
  squareMajorant : Fin atoms.N → ((Fin n → ℝ) → ℝ)
  crossAtomBound_nonneg : 0 ≤ crossAtomBound
  active_cross : ∀ x ∈ sphereSet n, ∀ i, atoms.root i x ≠ 0 →
    |atoms.root i x *
      (MvPolynomial.eval x
        (booleanFilteredFunctionPolynomial (n + 3) k atoms.base
          (fun y ↦ atoms.root i y.1)) - atoms.root i x)| ≤ crossAtomBound
  cross_budget : (atoms.overlapBound : ℝ) * crossAtomBound ≤
    C / (4 * (k : ℝ) ^ 4)
  squareScaleBound_nonneg : 0 ≤ squareScaleBound
  square_error_le_majorant : ∀ x ∈ sphereSet n, ∀ i,
    (MvPolynomial.eval x
      (booleanFilteredFunctionPolynomial (n + 3) k atoms.base
        (fun y ↦ atoms.root i y.1)) - atoms.root i x) ^ 2 ≤ squareMajorant i x
  scale_packing : ∀ x ∈ sphereSet n, ∀ j : Fin atoms.J,
    ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j), squareMajorant i x ≤
      squareScaleBound * (1 / 16 : ℝ) ^ (j : ℕ)
  square_budget : (16 / 15 : ℝ) * squareScaleBound ≤
    C / (4 * (k : ℝ) ^ 4)

/-- Assemble active cross control from the global atom error and scaled root
amplitude. -/
def FiniteBooleanFilterAnalyticBounds.toBooleanFilterBounds
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    {regular : FiniteRetainedRootRegularity atoms}
    (analytic : FiniteBooleanFilterAnalyticBounds atoms regular) (hk : 1 ≤ k) :
    FiniteBooleanFilterBounds atoms := by
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  refine {
    crossAtomBound := regular.jetBound * analytic.errorConstant / (k : ℝ) ^ 4
    squareScaleBound := analytic.squareScaleBound
    squareMajorant := analytic.squareMajorant
    crossAtomBound_nonneg := div_nonneg
      (mul_nonneg regular.jetBound_nonneg analytic.errorConstant_nonneg) (by positivity)
    active_cross := ?_
    cross_budget := ?_
    squareScaleBound_nonneg := analytic.squareScaleBound_nonneg
    square_error_le_majorant := analytic.square_error_le_majorant
    scale_packing := analytic.scale_packing
    square_budget := analytic.square_budget }
  · intro x hx i _hi
    exact abs_mul_le_of_scaled_amplitude_error regular.jetBound_nonneg
      (atoms.radius_pos i) hkpos (regular.root_abs_le i x) (analytic.global_error x hx i)
  · calc
      (atoms.overlapBound : ℝ) *
          (regular.jetBound * analytic.errorConstant / (k : ℝ) ^ 4) =
          ((atoms.overlapBound : ℝ) *
            (regular.jetBound * analytic.errorConstant)) / (k : ℝ) ^ 4 := by ring
      _ ≤ (C / 4) / (k : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right analytic.cross_constant_budget (by positivity)
      _ = C / (4 * (k : ℝ) ^ 4) := by field_simp [hkpos.ne']

/-- Add the canonical Boolean-filter polynomial and discharge its elementary
integrability obligations. -/
def FiniteBooleanFilterBounds.toBooleanFilterData
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (bounds : FiniteBooleanFilterBounds atoms)
    (regular : FiniteRetainedRootRegularity atoms) (hn : 0 < n) :
    FiniteBooleanFilterData atoms where
  polynomial := fun i ↦ booleanFilteredFunctionPolynomial (n + 3) k atoms.base
    (fun y ↦ atoms.root i y.1)
  crossAtomBound := bounds.crossAtomBound
  squareScaleBound := bounds.squareScaleBound
  squareMajorant := bounds.squareMajorant
  root_coeff_integrable := fun i ↦
    regular.root_coeff_integrable hn (zonalKernelCoeffContinuous (n + 3) k) i
  first_filter_coeff_integrable := fun i ↦
    zonalKernelCoeffIntegrable_eval hn (n + 3) k
      (normalizedFunctionZonalKernelPolynomial (n + 3) k atoms.base
        (fun y ↦ atoms.root i y.1)) (zonalKernelCoeffContinuous _ _)
  polynomial_eq_booleanFilter := fun _ ↦ rfl
  crossAtomBound_nonneg := bounds.crossAtomBound_nonneg
  active_cross := bounds.active_cross
  cross_budget := bounds.cross_budget
  squareScaleBound_nonneg := bounds.squareScaleBound_nonneg
  square_error_le_majorant := bounds.square_error_le_majorant
  scale_packing := bounds.scale_packing
  square_budget := bounds.square_budget

/-- Uniform existence of regular retained roots and their reduced filter bounds. -/
def HasFiniteRetainedRootRegularBooleanBounds (n : ℕ) (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k → Nonempty (Σ atoms : FiniteRetainedRootData n C k F,
      FiniteRetainedRootRegularity atoms × FiniteBooleanFilterBounds atoms)

/-- The reduced construction with the dyadic radius invariant exposed. -/
def HasFiniteRetainedRootDyadicBooleanBounds (n : ℕ) (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k → Nonempty (Σ atoms : FiniteRetainedRootData n C k F,
      FiniteRetainedRootRegularity atoms ×
        (FiniteRetainedRootDyadic atoms × FiniteBooleanFilterBounds atoms))

/-- Dyadic retained roots satisfying the pointwise chordal decay
and fixed-scale packing estimates. -/
def HasFiniteRetainedRootDyadicManuscriptBounds
    (n : ℕ) (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k → Nonempty (Σ atoms : FiniteRetainedRootData n C k F,
      Σ regular : FiniteRetainedRootRegularity atoms,
        FiniteRetainedRootDyadic atoms ×
          FiniteBooleanFilterManuscriptBounds atoms regular)

/-- Uniform atom-side input yields dyadic pointwise-decay and packing bounds
with the same retained-root and spherical SOS interfaces. -/
theorem exists_hasFiniteRetainedRootDyadicManuscriptBounds_of_input
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ {C : ℝ} {k₀ : ℕ}, 1 ≤ k₀ →
        HasFiniteRetainedRootManuscriptInput n E C k₀ →
        HasFiniteRetainedRootDyadicManuscriptBounds n C k₀ := by
  obtain ⟨E, hE, hmake⟩ :=
    exists_finiteBooleanFilterManuscriptBounds_of_secondDifference hn
  refine ⟨E, hE, ?_⟩
  intro C k₀ hk₀ hinput F hF hnorm k hk
  let stage := Classical.choice (hinput F hF hnorm k hk)
  let atoms := stage.1
  let input := stage.2
  let packingConstant : ℝ :=
    (atoms.overlapBound : ℝ) + 2 * input.farShellConstant
  have hpackingConstant : 0 ≤ packingConstant :=
    add_nonneg (Nat.cast_nonneg atoms.overlapBound)
      (mul_nonneg (by norm_num) input.farShellConstant_nonneg)
  have hpacking : ∀ x ∈ sphereSet n, ∀ j : Fin atoms.J,
      ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j),
        sphereChordalDecayWeight (2 * (n + 3))
          (atoms.center i) (atoms.radius i) x ≤ packingConstant := by
    intro x hx j
    apply atoms.sum_scale_decayWeight_le_overlap_add_of_far x hx j
    exact atoms.sum_scale_far_decayWeight_le_two_mul_of_shell_bounds x j
      (input.farShell ⟨x, hx⟩) input.farShellConstant_nonneg
      (by
        intro q
        exact atoms.sum_decayWeight_le_half_pow_of_shell
          ((Finset.univ.filter (fun i => atoms.scale i = j ∧
            ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
              (fun i => input.farShell ⟨x, hx⟩ i = q)) x
          (input.scale_far_shell_distance x hx j q)
          (input.scale_far_shell_card_budget x hx j q))
  have hsquare : (16 / 15 : ℝ) *
      ((input.regular.jetBound * E) ^ 2 * packingConstant) ≤ C / 4 := by
    simpa [packingConstant] using input.square_constant_budget
  have hbounds := hmake atoms input.regular (hk₀.trans hk)
    (input.filterIncrementOscillation.toSecondDifference (by omega)) packingConstant
    hpackingConstant hpacking input.cross_constant_budget hsquare
  let bounds := Classical.choice hbounds
  exact ⟨⟨atoms, input.regular, input.dyadic, bounds⟩⟩

/-- Core retained-root construction: produce retained roots
with regularity, dyadic scales, filtered-increment oscillation, dyadic-shell
separation and cardinality budgets, and both constant budgets. -/
theorem finiteRetainedRootManuscriptInput {n : ℕ} (hn : 3 ≤ n) :
    ∀ E : ℝ, 0 ≤ E →
      ∃ (C : ℝ) (k₀ : ℕ), 0 < C ∧ 1 ≤ k₀ ∧
        HasFiniteRetainedRootManuscriptInput n E C k₀ := by
  have hjets : HasUniformNonnegativeJetBounds n := uniformNonnegativeJetBounds n
  have hcover : HasUniformScaleCover n := uniformScaleCover_of_jetBounds hjets
  have hsplit : HasUniformLocalSplit n := uniformLocalSplit n
  have heuclidean : HasUniformEuclideanAtomDecomposition n :=
    uniformEuclideanAtoms_of_cover_split (by omega) hjets hcover hsplit
  have hsphere : HasUniformSphereAtomDecomposition n :=
    uniformSphereAtoms_of_euclidean hn heuclidean
  intro E hE
  obtain ⟨C, k₀, hC, hk₀, hpackage⟩ :=
    finiteSphereAtomPackage_of_sphereAtoms hn hsphere E hE
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro F hF hnorm k hk
  let package := Classical.choice (hpackage F hF hnorm k hk)
  let atoms : FiniteRetainedRootData n C k F := {
    N := package.N
    J := package.J
    root := package.root
    base := package.base
    center := package.center
    radius := package.radius
    scale := package.scale
    overlapBound := package.overlapBound
    radius_pos := package.radius_pos
    radius_lower := package.radius_lower
    radius_upper := package.radius_upper
    supported := package.supported
    cap_overlap_card := package.cap_overlap_card
    remainder := package.remainder }
  let regular : FiniteRetainedRootRegularity atoms := {
    jetBound := package.jetBound
    jetBound_nonneg := package.jetBound_nonneg
    root_contDiff := package.root_contDiff
    scaled_jet := package.scaled_jet }
  let dyadic : FiniteRetainedRootDyadic atoms := {
    scale_lower := package.scale_lower
    scale_upper := package.scale_upper }
  refine ⟨⟨atoms, {
    regular := regular
    dyadic := dyadic
    filterIncrementOscillation := ?_
    farShellCount := package.farShellCount
    farShell := package.farShell
    farShellConstant := package.farShellConstant
    farShellConstant_nonneg := package.farShellConstant_nonneg
    scale_far_shell_distance := ?_
    scale_far_shell_card_budget := ?_
    cross_constant_budget := ?_
    square_constant_budget := ?_ }⟩⟩
  · intro i x y
    simpa [atoms, regular, normalizedZonalFilterError, sphereSymmetricIncrement,
      packingNormalizedZonalFilterError, packingSphereSymmetricIncrement] using
        package.filter_increment_oscillation i x y
  · simpa [atoms] using package.scale_far_shell_distance
  · simpa [atoms] using package.scale_far_shell_card_budget
  · simpa [atoms, regular] using package.cross_constant_budget
  · simpa [atoms, regular] using package.square_constant_budget

/-- Construct the retained roots and prove the
localized Boolean-filter and packing estimates. -/
theorem finiteRetainedRootDyadicManuscriptBounds {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (k₀ : ℕ), 0 < C ∧ 1 ≤ k₀ ∧
      HasFiniteRetainedRootDyadicManuscriptBounds n C k₀ := by
  obtain ⟨E, hE, hreduce⟩ :=
    exists_hasFiniteRetainedRootDyadicManuscriptBounds_of_input hn
  obtain ⟨C, k₀, hC, hk₀, hinput⟩ :=
    finiteRetainedRootManuscriptInput hn E hE
  exact ⟨C, k₀, hC, hk₀, hreduce hk₀ hinput⟩

/-- Dyadic regular roots with a localized weight whose fixed-scale sums are bounded. -/
def HasFiniteRetainedRootDyadicLocalizedBounds (n : ℕ) (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k → Nonempty (Σ atoms : FiniteRetainedRootData n C k F,
      Σ regular : FiniteRetainedRootRegularity atoms,
        FiniteRetainedRootDyadic atoms ×
          FiniteBooleanFilterLocalizedBounds atoms regular)

/-- Construct the retained roots and localized weights. -/
theorem finiteRetainedRootDyadicLocalizedBounds {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (k₀ : ℕ), 0 < C ∧ 1 ≤ k₀ ∧
      HasFiniteRetainedRootDyadicLocalizedBounds n C k₀ := by
  obtain ⟨C, k₀, hC, hk₀, hmanuscript⟩ :=
    finiteRetainedRootDyadicManuscriptBounds hn
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro F hF hnorm k hk
  let stages := Classical.choice (hmanuscript F hF hnorm k hk)
  exact ⟨⟨stages.1, stages.2.1, stages.2.2.1,
    stages.2.2.2.toLocalizedBounds stages.2.2.1 (hk₀.trans hk)⟩⟩

/-- Dyadic regular roots with the pre-cross-term analytic filter estimates. -/
def HasFiniteRetainedRootDyadicAnalyticBounds (n : ℕ) (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k → Nonempty (Σ atoms : FiniteRetainedRootData n C k F,
      Σ regular : FiniteRetainedRootRegularity atoms,
        FiniteRetainedRootDyadic atoms ×
          FiniteBooleanFilterAnalyticBounds atoms regular)

/-- Assembly after cross-term cancellation has been extracted. -/
theorem finiteRetainedRootDyadicAnalyticBounds {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (k₀ : ℕ), 0 < C ∧ 1 ≤ k₀ ∧
      HasFiniteRetainedRootDyadicAnalyticBounds n C k₀ := by
  obtain ⟨C, k₀, hC, hk₀, hlocalized⟩ := finiteRetainedRootDyadicLocalizedBounds hn
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro F hF hnorm k hk
  let stages := Classical.choice (hlocalized F hF hnorm k hk)
  exact ⟨⟨stages.1, stages.2.1, stages.2.2.1,
    stages.2.2.2.toAnalyticBounds (hk₀.trans hk)⟩⟩

/-- Atom-decomposition and localized-filter theorem with the
dyadic radius bookkeeping made explicit. -/
theorem finiteRetainedRootDyadicBooleanBounds {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (k₀ : ℕ), 0 < C ∧ 1 ≤ k₀ ∧
      HasFiniteRetainedRootDyadicBooleanBounds n C k₀ := by
  obtain ⟨C, k₀, hC, hk₀, hanalytic⟩ := finiteRetainedRootDyadicAnalyticBounds hn
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro F hF hnorm k hk
  let stages := Classical.choice (hanalytic F hF hnorm k hk)
  exact ⟨⟨stages.1, stages.2.1,
    stages.2.2.1, stages.2.2.2.toBooleanFilterBounds (hk₀.trans hk)⟩⟩

/-- Atom-decomposition and localized-filter theorem. -/
theorem finiteRetainedRootRegularBooleanBounds {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (k₀ : ℕ), 0 < C ∧ 1 ≤ k₀ ∧
      HasFiniteRetainedRootRegularBooleanBounds n C k₀ := by
  obtain ⟨C, k₀, hC, hk₀, hdyadic⟩ := finiteRetainedRootDyadicBooleanBounds hn
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro F hF hnorm k hk
  let stages := Classical.choice (hdyadic F hF hnorm k hk)
  exact ⟨⟨stages.1, stages.2.1, stages.2.2.2⟩⟩
/-- Uniform regular retained roots together with the Boolean-filter estimates
that their scaled jets imply. -/
def HasFiniteRetainedRootRegularBooleanData
    (n : ℕ) (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ,
    SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k →
      Nonempty (Σ atoms : FiniteRetainedRootData n C k F,
        FiniteRetainedRootRegularity atoms × FiniteBooleanFilterData atoms)

/-- The analytic construction with the scaled C4 estimates needed
by the Boolean filter made explicit. -/
theorem finiteRetainedRootRegularBooleanData {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (k₀ : ℕ), 0 < C ∧ 1 ≤ k₀ ∧
      HasFiniteRetainedRootRegularBooleanData n C k₀ := by
  obtain ⟨C, k₀, hC, hk₀, hbounds⟩ := finiteRetainedRootRegularBooleanBounds hn
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro F hF hnorm k hk
  let stages := Classical.choice (hbounds F hF hnorm k hk)
  have hnpos : 0 < n := by omega
  exact ⟨⟨stages.1, stages.2.1,
    stages.2.2.toBooleanFilterData stages.2.1 hnpos⟩⟩
/-- Uniform existence of the two separate analytic stages: retained atoms,
followed by Boolean-filter estimates for precisely those atoms. -/
def HasFiniteRetainedRootBooleanData (n : ℕ) (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ,
    SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k →
      Nonempty (Σ atoms : FiniteRetainedRootData n C k F,
        FiniteBooleanFilterData atoms)

/-- Analytic core: construct finite retained smooth roots
and prove the localized Boolean-filter bounds at every sufficiently fine
resolution. -/
theorem finiteRetainedRootBooleanData {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (k₀ : ℕ),
      0 < C ∧ 1 ≤ k₀ ∧ HasFiniteRetainedRootBooleanData n C k₀ := by
  obtain ⟨C, k₀, hC, hk₀, hregular⟩ := finiteRetainedRootRegularBooleanData hn
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro F hF hnorm k hk
  let stages := Classical.choice (hregular F hF hnorm k hk)
  exact ⟨⟨stages.1, stages.2.2⟩⟩
/-- The retained-root input, stated at the actual scale-resolved
level: construct cap-supported retained roots and establish the localized
per-root and per-dyadic-scale Boolean-filter bounds. -/
theorem finiteFilteredRootScaleData {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (k₀ : ℕ),
      0 < C ∧ 1 ≤ k₀ ∧ HasFiniteFilteredRootScaleData n C k₀ := by
  obtain ⟨C, k₀, hC, hk₀, hstages⟩ := finiteRetainedRootBooleanData hn
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro F hF hnorm k hk
  let stages := Classical.choice (hstages F hF hnorm k hk)
  exact ⟨stages.1.withBooleanFilterData stages.2⟩

end QuarticConvergence
end OptimalConvergenceRates

end
