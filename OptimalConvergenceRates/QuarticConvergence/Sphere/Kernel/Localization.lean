/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/Localization.lean

  Reduction of continuous zonal-kernel approximation to a chordal second moment.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Quadrature

open Set MeasureTheory MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers
open SpherePolynomialQuadrature

/-- Squared ambient chordal distance. On the unit sphere this is
`2 * (1 - ⟨y, x⟩)`, the weight used in the localization estimate. -/
def sphereChordalSq {n : ℕ} (y x : Fin n → ℝ) : ℝ :=
  ∑ i, (y i - x i) ^ 2

/-- On the unit sphere, squared chordal distance is twice one minus the
ambient dot product. -/
theorem sphereChordalSq_eq_two_mul_one_sub_dot {n : ℕ}
    {y x : Fin n → ℝ} (hy : y ∈ sphereSet n) (hx : x ∈ sphereSet n) :
    sphereChordalSq y x = 2 * (1 - ∑ i, y i * x i) := by
  have hy' : ∑ i, y i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using hy
  have hx' : ∑ i, x i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using hx
  calc
    sphereChordalSq y x =
        (∑ i, y i ^ 2) - 2 * (∑ i, y i * x i) +
          ∑ i, x i ^ 2 := by
      unfold sphereChordalSq
      simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [Finset.mul_sum]
      ring_nf
    _ = 2 * (1 - ∑ i, y i * x i) := by rw [hy', hx']; ring

theorem sphereChordalSq_nonneg {n : ℕ} (y x : Fin n → ℝ) :
    0 ≤ sphereChordalSq y x := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The squared chordal distance between two unit-sphere points is at most four. -/
theorem sphereChordalSq_le_four {n : ℕ} {y x : Fin n → ℝ}
    (hy : y ∈ sphereSet n) (hx : x ∈ sphereSet n) :
    sphereChordalSq y x ≤ 4 := by
  have hy' : ∑ i, y i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using hy
  have hx' : ∑ i, x i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using hx
  calc
    sphereChordalSq y x ≤ ∑ i, (2 * y i ^ 2 + 2 * x i ^ 2) := by
      unfold sphereChordalSq
      apply Finset.sum_le_sum
      intro i _
      nlinarith [sq_nonneg (y i + x i)]
    _ = 4 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hy', hx']
      norm_num

/-- The dot product of two algebraic unit-sphere points lies in `[-1, 1]`.
This formulation avoids introducing a second Euclidean-coordinate wrapper. -/
theorem sphereDot_mem_Icc {n : ℕ} {y x : Fin n → ℝ}
    (hy : y ∈ sphereSet n) (hx : x ∈ sphereSet n) :
    (∑ i, y i * x i) ∈ Set.Icc (-1 : ℝ) 1 := by
  have heq := sphereChordalSq_eq_two_mul_one_sub_dot hy hx
  have hnonneg := sphereChordalSq_nonneg y x
  have hfour := sphereChordalSq_le_four hy hx
  constructor <;> nlinarith

/-- Angular distance on the algebraic sphere, expressed through the ambient dot product. -/
noncomputable def sphereAngularDistance {n : ℕ} (y x : sphereSet n) : ℝ :=
  Real.arccos (∑ i, y.1 i * x.1 i)

theorem sphereAngularDistance_nonneg {n : ℕ} (y x : sphereSet n) :
    0 ≤ sphereAngularDistance y x := by
  exact Real.arccos_nonneg _

theorem sphereAngularDistance_le_pi {n : ℕ} (y x : sphereSet n) :
    sphereAngularDistance y x ≤ Real.pi := by
  exact Real.arccos_le_pi _

/-- Squared angular distance is globally bounded by `π²`. -/
theorem sphereAngularDistance_sq_le_pi_sq {n : ℕ} (y x : sphereSet n) :
    sphereAngularDistance y x ^ 2 ≤ Real.pi ^ 2 := by
  exact (sq_le_sq₀ (sphereAngularDistance_nonneg y x) Real.pi_pos.le).2
    (sphereAngularDistance_le_pi y x)

/-- Taking cosine recovers the dot product of two sphere points. -/
theorem cos_sphereAngularDistance {n : ℕ} (y x : sphereSet n) :
    Real.cos (sphereAngularDistance y x) = ∑ i, y.1 i * x.1 i := by
  exact Real.cos_arccos (sphereDot_mem_Icc y.2 x.2).1
    (sphereDot_mem_Icc y.2 x.2).2

/-- Angular distance is continuous in the first sphere variable. -/
theorem continuous_sphereAngularDistance_right {n : ℕ} (x : sphereSet n) :
    Continuous (fun y : sphereSet n ↦ sphereAngularDistance y x) := by
  apply Real.continuous_arccos.comp
  apply continuous_finsetSum
  intro i hi
  exact ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

/-- A closed angular cap about `x`. -/
noncomputable def sphereAngularCap {n : ℕ} (x : sphereSet n) (r : ℝ) :
    Set (sphereSet n) :=
  {y | sphereAngularDistance y x ≤ r}

/-- The open angular cap about `x`. -/
noncomputable def sphereAngularOpenCap {n : ℕ}
    (x : sphereSet n) (r : ℝ) : Set (sphereSet n) :=
  {y | sphereAngularDistance y x < r}

/-- Open angular caps are open in the sphere topology. -/
theorem isOpen_sphereAngularOpenCap {n : ℕ}
    (x : sphereSet n) (r : ℝ) :
    IsOpen (sphereAngularOpenCap x r) := by
  exact isOpen_lt (continuous_sphereAngularDistance_right x) continuous_const

/-- A positive-radius angular open cap contains its center. -/
theorem self_mem_sphereAngularOpenCap {n : ℕ}
    (x : sphereSet n) {r : ℝ} (hr : 0 < r) :
    x ∈ sphereAngularOpenCap x r := by
  have hdot : ∑ i, x.1 i * x.1 i = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2
  change Real.arccos (∑ i, x.1 i * x.1 i) < r
  rw [hdot, Real.arccos_one]
  exact hr

/-- The angular open cap is contained in the corresponding closed cap. -/
theorem sphereAngularOpenCap_subset_cap {n : ℕ}
    (x : sphereSet n) (r : ℝ) :
    sphereAngularOpenCap x r ⊆ sphereAngularCap x r := by
  intro y hy
  change sphereAngularDistance y x < r at hy
  change sphereAngularDistance y x ≤ r
  exact hy.le

/-- Every positive-radius closed angular cap has positive normalized measure. -/
theorem normalizedSphereMeasure_sphereAngularCap_pos {n : ℕ}
    (x : sphereSet n) {r : ℝ} (hr : 0 < r) :
    0 < normalizedSphereMeasure n (sphereAngularCap x r) := by
  letI : Measure.IsOpenPosMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isOpenPosMeasure n
  have hpos :
      0 < normalizedSphereMeasure n (sphereAngularOpenCap x r) :=
    (isOpen_sphereAngularOpenCap x r).measure_pos _
      ⟨x, self_mem_sphereAngularOpenCap x hr⟩
  exact hpos.trans_le
    (measure_mono (sphereAngularOpenCap_subset_cap x r))

theorem isClosed_sphereAngularCap {n : ℕ} (x : sphereSet n) (r : ℝ) :
    IsClosed (sphereAngularCap x r) := by
  exact isClosed_le (continuous_sphereAngularDistance_right x) continuous_const

theorem measurableSet_sphereAngularCap {n : ℕ} (x : sphereSet n) (r : ℝ) :
    MeasurableSet (sphereAngularCap x r) :=
  (isClosed_sphereAngularCap x r).measurableSet

/-- Every nonnegative-radius angular cap contains its center. -/
theorem self_mem_sphereAngularCap {n : ℕ} (x : sphereSet n)
    {r : ℝ} (hr : 0 ≤ r) : x ∈ sphereAngularCap x r := by
  have hdot : ∑ i, x.1 i * x.1 i = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2
  change Real.arccos (∑ i, x.1 i * x.1 i) ≤ r
  rw [hdot, Real.arccos_one]
  exact hr

/-- Angular caps are monotone in their radius. -/
theorem sphereAngularCap_mono {n : ℕ} (x : sphereSet n)
    {r s : ℝ} (hrs : r ≤ s) :
    sphereAngularCap x r ⊆ sphereAngularCap x s := by
  intro y hy
  exact hy.trans hrs

/-- An angular cap of radius at least pi is the whole sphere. -/
theorem sphereAngularCap_eq_univ_of_pi_le {n : ℕ}
    (x : sphereSet n) {r : ℝ} (hr : Real.pi ≤ r) :
    sphereAngularCap x r = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  exact (sphereAngularDistance_le_pi y x).trans hr

/-- The half-open angular shell between radii `r` and `s`. -/
noncomputable def sphereAngularAnnulus {n : ℕ}
    (x : sphereSet n) (r s : ℝ) : Set (sphereSet n) :=
  sphereAngularCap x s \ sphereAngularCap x r

/-- Angular annuli are measurable for the dyadic moment decomposition. -/
theorem measurableSet_sphereAngularAnnulus {n : ℕ}
    (x : sphereSet n) (r s : ℝ) :
    MeasurableSet (sphereAngularAnnulus x r s) := by
  exact (measurableSet_sphereAngularCap x s).diff
    (measurableSet_sphereAngularCap x r)

/-- An inner angular cap and its half-open annulus are disjoint. -/
theorem disjoint_sphereAngularCap_sphereAngularAnnulus {n : ℕ}
    (x : sphereSet n) (r s : ℝ) :
    Disjoint (sphereAngularCap x r) (sphereAngularAnnulus x r s) := by
  exact Set.disjoint_sdiff_right

/-- A larger angular cap is the union of an inner cap and the intervening
half-open angular annulus. -/
theorem sphereAngularCap_union_sphereAngularAnnulus {n : ℕ}
    (x : sphereSet n) {r s : ℝ} (hrs : r ≤ s) :
    sphereAngularCap x r ∪ sphereAngularAnnulus x r s =
      sphereAngularCap x s := by
  ext y
  constructor
  · intro hy
    rcases hy with hy | hy
    · exact sphereAngularCap_mono x hrs hy
    · exact hy.1
  · intro hy
    by_cases hyr : y ∈ sphereAngularCap x r
    · exact Or.inl hyr
    · exact Or.inr ⟨hy, hyr⟩

/-- The annulus is always contained in its outer angular cap. -/
theorem sphereAngularAnnulus_subset_outerCap {n : ℕ}
    (x : sphereSet n) (r s : ℝ) :
    sphereAngularAnnulus x r s ⊆ sphereAngularCap x s := by
  intro y hy
  exact hy.1
/-- Squared chordal distance is at most squared angular distance. -/
theorem sphereChordalSq_le_sphereAngularDistance_sq {n : ℕ}
    (y x : sphereSet n) :
    sphereChordalSq y.1 x.1 ≤ sphereAngularDistance y x ^ 2 := by
  rw [sphereChordalSq_eq_two_mul_one_sub_dot y.2 x.2]
  rw [← cos_sphereAngularDistance]
  have hcos := Real.one_sub_sq_div_two_le_cos
    (x := sphereAngularDistance y x)
  nlinarith

/-- A positive zonal-kernel section is bounded by the even power of the
Dirichlet peak everywhere on the sphere. -/
theorem eval_sphereDirichletZonalKernel_le_peak {n : ℕ}
    (p k : ℕ) {y x : Fin n → ℝ}
    (hy : y ∈ sphereSet n) (hx : x ∈ sphereSet n) :
    MvPolynomial.eval y (sphereDirichletZonalKernel p k x) ≤
      (2 * (k : ℝ) + 1) ^ (2 * p) := by
  rw [eval_sphereDirichletZonalKernel]
  let t := ∑ i, x i * y i
  have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
    have h := sphereDot_mem_Icc hy hx
    simpa only [t, mul_comm] using h
  have hbound := abs_sphereDirichletPolynomial_eval_le k ht
  have heven := sphereDirichletPolynomial_evenPow_nonneg p k t
  change ((sphereDirichletPolynomial k).eval t) ^ (2 * p) ≤ _
  rw [← abs_of_nonneg heven, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hbound (2 * p)

/-- Away from its center, a positive zonal-kernel section has the sharp
reciprocal-angular-distance decay inherited from the scalar Dirichlet kernel. -/
theorem eval_sphereDirichletZonalKernel_le_pi_div_angularDistance_pow
    {n : ℕ} (p k : ℕ) (x y : sphereSet n)
    (hangle : 0 < sphereAngularDistance y x) :
    MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) ≤
      (Real.pi / sphereAngularDistance y x) ^ (2 * p) := by
  rw [eval_sphereDirichletZonalKernel]
  have hdot :
      (∑ i, x.1 i * y.1 i) =
        Real.cos (sphereAngularDistance y x) := by
    rw [cos_sphereAngularDistance]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdot]
  have hbound :=
    abs_sphereDirichletPolynomial_eval_cos_le_pi_div
      k hangle (sphereAngularDistance_le_pi y x)
  have heven :=
    sphereDirichletPolynomial_evenPow_nonneg p k
      (Real.cos (sphereAngularDistance y x))
  rw [← abs_of_nonneg heven, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hbound (2 * p)

/-- On an angular annulus outside radius `r > 0`, reciprocal decay may be
bounded uniformly by its value at the inner radius. -/
theorem eval_sphereDirichletZonalKernel_le_pi_div_radius_pow_of_mem_angularAnnulus
    {n : ℕ} (p k : ℕ) (x y : sphereSet n) {r s : ℝ}
    (hr : 0 < r) (hy : y ∈ sphereAngularAnnulus x r s) :
    MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) ≤
      (Real.pi / r) ^ (2 * p) := by
  rcases hy with ⟨hys, hyr⟩
  change ¬sphereAngularDistance y x ≤ r at hyr
  have hrangle : r ≤ sphereAngularDistance y x :=
    (lt_of_not_ge hyr).le
  have hangle : 0 < sphereAngularDistance y x :=
    hr.trans_le hrangle
  calc
    MvPolynomial.eval y.1
        (sphereDirichletZonalKernel p k x.1) ≤
      (Real.pi / sphereAngularDistance y x) ^ (2 * p) :=
        eval_sphereDirichletZonalKernel_le_pi_div_angularDistance_pow
          p k x y hangle
    _ ≤ (Real.pi / r) ^ (2 * p) := by
      exact pow_le_pow_left₀
        (div_nonneg Real.pi_pos.le hangle.le)
        (div_le_div_of_nonneg_left Real.pi_pos.le hr hrangle)
        (2 * p)

/-- On the angular cap of radius `1/k`, the positive zonal kernel is at least
`k^(2p)`. This is the pointwise half of the raw mass lower bound. -/
theorem natCast_pow_le_eval_sphereDirichletZonalKernel_of_mem_angularCap
    {n : ℕ} (p k : ℕ) (hk : 1 ≤ k) (x y : sphereSet n)
    (hy : y ∈ sphereAngularCap x (1 / (k : ℝ))) :
    (k : ℝ) ^ (2 * p) ≤
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) := by
  change sphereAngularDistance y x ≤ 1 / (k : ℝ) at hy
  have htheta : |sphereAngularDistance y x| ≤ 1 / (k : ℝ) := by
    rw [abs_of_nonneg (sphereAngularDistance_nonneg y x)]
    exact hy
  have hdirichlet :
      (k : ℝ) ≤ (sphereDirichletPolynomial k).eval
        (Real.cos (sphereAngularDistance y x)) :=
    natCast_le_sphereDirichletPolynomial_eval_cos k hk htheta
  rw [eval_sphereDirichletZonalKernel]
  have hdot :
      (∑ i, x.1 i * y.1 i) = Real.cos (sphereAngularDistance y x) := by
    rw [cos_sphereAngularDistance]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hdot]
  exact pow_le_pow_left₀ (Nat.cast_nonneg k) hdirichlet (2 * p)

/-- Restricting the positive kernel integral to its `1/k` angular cap turns
the pointwise near-peak estimate into a mass lower bound. -/
theorem angularCap_mass_lower_bound {n : ℕ} (hn : 0 < n)
    (p k : ℕ) (hk : 1 ≤ k) (x : sphereSet n) :
    (k : ℝ) ^ (2 * p) *
        (normalizedSphereMeasure n).real
          (sphereAngularCap x (1 / (k : ℝ))) ≤
      continuousZonalKernelMass p k x.1 := by
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  let cap := sphereAngularCap x (1 / (k : ℝ))
  let f := fun y : sphereSet n ↦
    MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
  have hcap : MeasurableSet cap := measurableSet_sphereAngularCap _ _
  have hfint : Integrable f (normalizedSphereMeasure n) :=
    integrable_sphereDirichletZonalKernel_section hn p k x.1
  have hcint : IntegrableOn (fun _y : sphereSet n ↦ (k : ℝ) ^ (2 * p)) cap
      (normalizedSphereMeasure n) :=
    (MeasureTheory.integrable_const _).integrableOn
  have hlower :
      ∫ _y : sphereSet n in cap, (k : ℝ) ^ (2 * p)
          ∂normalizedSphereMeasure n ≤
        ∫ y : sphereSet n in cap, f y ∂normalizedSphereMeasure n := by
    apply setIntegral_mono_on hcint hfint.integrableOn hcap
    intro y hy
    exact natCast_pow_le_eval_sphereDirichletZonalKernel_of_mem_angularCap
      p k hk x y hy
  have hrestrict :
      ∫ y : sphereSet n in cap, f y ∂normalizedSphereMeasure n ≤
        ∫ y : sphereSet n, f y ∂normalizedSphereMeasure n := by
    apply setIntegral_le_integral hfint
    exact ae_of_all _ fun y ↦ eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1
  calc
    (k : ℝ) ^ (2 * p) * (normalizedSphereMeasure n).real cap =
        ∫ _y : sphereSet n in cap, (k : ℝ) ^ (2 * p)
          ∂normalizedSphereMeasure n := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    _ ≤ ∫ y : sphereSet n in cap, f y ∂normalizedSphereMeasure n := hlower
    _ ≤ ∫ y : sphereSet n, f y ∂normalizedSphereMeasure n := hrestrict
    _ = continuousZonalKernelMass p k x.1 := rfl

/-- Integrating the pointwise peak estimate gives a coarse global upper bound
for the unnormalized kernel mass. -/
theorem continuousZonalKernelMass_le_peak {n : ℕ} (hn : 0 < n)
    (p k : ℕ) {x : Fin n → ℝ} (hx : x ∈ sphereSet n) :
    continuousZonalKernelMass p k x ≤
      (2 * (k : ℝ) + 1) ^ (2 * p) := by
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  calc
    continuousZonalKernelMass p k x =
        ∫ y : sphereSet n,
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
            ∂normalizedSphereMeasure n := rfl
    _ ≤ ∫ _y : sphereSet n, (2 * (k : ℝ) + 1) ^ (2 * p)
        ∂normalizedSphereMeasure n := by
      apply integral_mono
        (integrable_sphereDirichletZonalKernel_section hn p k x)
        (MeasureTheory.integrable_const _)
      intro y
      exact eval_sphereDirichletZonalKernel_le_peak p k y.2 hx
    _ = (2 * (k : ℝ) + 1) ^ (2 * p) := by simp

/-- Chordal square as a function of the integration variable is continuous
on the algebraic sphere. -/
theorem continuous_sphereChordalSq_right {n : ℕ} (x : Fin n → ℝ) :
    Continuous (fun y : sphereSet n ↦ sphereChordalSq y.1 x) := by
  unfold sphereChordalSq
  apply continuous_finsetSum
  intro i _
  exact (((continuous_apply i).comp continuous_subtype_val).sub
    continuous_const).pow 2

/-- In Euclidean-sphere coordinates, chordal square is squared metric distance. -/
theorem sphereChordalSq_euclideanSphereCoordinates_eq_dist_sq {n : ℕ}
    (y x : euclideanUnitSphere n) :
    sphereChordalSq (euclideanSphereCoordinates y)
        (euclideanSphereCoordinates x) = dist y x ^ 2 := by
  rw [Subtype.dist_eq, dist_eq_norm]
  have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n ↦ ℝ) (y.1 - x.1)
  rw [hsq]
  simp [sphereChordalSq, euclideanSphereCoordinates, Real.norm_eq_abs, sq_abs]

/-- A closed chordal cap of radius `r` around an algebraic sphere point. -/
def sphereChordalCap {n : ℕ} (x : sphereSet n) (r : ℝ) : Set (sphereSet n) :=
  {y | sphereChordalSq y.1 x.1 ≤ r ^ 2}

/-- The open chordal cap of radius `r` around an algebraic sphere point. -/
def sphereChordalOpenCap {n : ℕ} (x : sphereSet n) (r : ℝ) : Set (sphereSet n) :=
  {y | sphereChordalSq y.1 x.1 < r ^ 2}

/-- Open chordal caps are open in the sphere topology. -/
theorem isOpen_sphereChordalOpenCap {n : ℕ} (x : sphereSet n) (r : ℝ) :
    IsOpen (sphereChordalOpenCap x r) := by
  exact isOpen_lt (continuous_sphereChordalSq_right x.1) continuous_const

/-- A chordal open cap of nonzero radius contains its center. -/
theorem self_mem_sphereChordalOpenCap {n : ℕ} (x : sphereSet n)
    {r : ℝ} (hr : r ≠ 0) : x ∈ sphereChordalOpenCap x r := by
  simp [sphereChordalOpenCap, sphereChordalSq, sq_pos_of_ne_zero hr]

/-- The open cap is contained in the corresponding closed cap. -/
theorem sphereChordalOpenCap_subset_cap {n : ℕ} (x : sphereSet n) (r : ℝ) :
    sphereChordalOpenCap x r ⊆ sphereChordalCap x r := by
  intro y hy
  change sphereChordalSq y.1 x.1 < r ^ 2 at hy
  change sphereChordalSq y.1 x.1 ≤ r ^ 2
  exact hy.le

/-- Every nonzero-radius closed chordal cap has positive normalized surface measure. -/
theorem normalizedSphereMeasure_sphereChordalCap_pos {n : ℕ}
    (x : sphereSet n) {r : ℝ} (hr : r ≠ 0) :
    0 < normalizedSphereMeasure n (sphereChordalCap x r) := by
  letI : Measure.IsOpenPosMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isOpenPosMeasure n
  have hopen := isOpen_sphereChordalOpenCap x r
  have hpos : 0 < normalizedSphereMeasure n (sphereChordalOpenCap x r) :=
    hopen.measure_pos _ ⟨x, self_mem_sphereChordalOpenCap x hr⟩
  exact hpos.trans_le (measure_mono (sphereChordalOpenCap_subset_cap x r))

/-- Chordal caps are closed in the sphere topology. -/
theorem isClosed_sphereChordalCap {n : ℕ} (x : sphereSet n) (r : ℝ) :
    IsClosed (sphereChordalCap x r) := by
  exact isClosed_le (continuous_sphereChordalSq_right x.1) continuous_const

/-- In particular, chordal caps are measurable for normalized surface measure. -/
theorem measurableSet_sphereChordalCap {n : ℕ} (x : sphereSet n) (r : ℝ) :
    MeasurableSet (sphereChordalCap x r) :=
  (isClosed_sphereChordalCap x r).measurableSet

/-- Transporting a nonnegative-radius chordal cap back through the coordinate
homeomorphism gives the ordinary closed metric ball on the Euclidean sphere. -/
theorem preimage_sphereChordalCap_eq_closedBall {n : ℕ}
    (base : sphereSet n) {r : ℝ} (hr : 0 ≤ r) :
    (euclideanSphereHomeomorphSphereSet n) ⁻¹' sphereChordalCap base r =
      Metric.closedBall ((euclideanSphereHomeomorphSphereSet n).symm base) r := by
  ext y
  simp only [Set.mem_preimage, sphereChordalCap, Set.mem_ofPred_eq,
    Metric.mem_closedBall]
  rw [← sq_le_sq₀ dist_nonneg hr]
  rw [← sphereChordalSq_euclideanSphereCoordinates_eq_dist_sq]
  rfl

/-- Chordal-cap mass for the repository sphere is exactly closed-ball mass
for normalized Haar measure on mathlib's Euclidean sphere. -/
theorem normalizedSphereMeasure_sphereChordalCap_eq_closedBall {n : ℕ}
    (base : sphereSet n) {r : ℝ} (hr : 0 ≤ r) :
    normalizedSphereMeasure n (sphereChordalCap base r) =
      normalizedEuclideanSphereMeasure n
        (Metric.closedBall ((euclideanSphereHomeomorphSphereSet n).symm base) r) := by
  rw [normalizedSphereMeasure]
  rw [Measure.map_apply
    (euclideanSphereHomeomorphSphereSet n).measurable
    (measurableSet_sphereChordalCap base r)]
  rw [preimage_sphereChordalCap_eq_closedBall base hr]
/-- Every chordal cap contains its center. -/
theorem self_mem_sphereChordalCap {n : ℕ} (x : sphereSet n) (r : ℝ) :
    x ∈ sphereChordalCap x r := by
  simp [sphereChordalCap, sphereChordalSq, sq_nonneg r]

/-- Chordal distance is exactly twice the sine of half the angular distance. -/
theorem sphereChordalSq_eq_four_mul_sin_half_sq {n : ℕ}
    (y x : sphereSet n) :
    sphereChordalSq y.1 x.1 =
      4 * Real.sin (sphereAngularDistance y x / 2) ^ 2 := by
  rw [sphereChordalSq_eq_two_mul_one_sub_dot y.2 x.2]
  rw [← cos_sphereAngularDistance]
  have htrig := Real.sin_sq_eq_half_sub (sphereAngularDistance y x / 2)
  rw [show 2 * (sphereAngularDistance y x / 2) =
    sphereAngularDistance y x by ring] at htrig
  nlinarith

/-- An angular cap is contained in the chordal cap with the same radius. -/
theorem sphereAngularCap_subset_sphereChordalCap {n : ℕ}
    (x : sphereSet n) {r : ℝ} (hr : 0 ≤ r) :
    sphereAngularCap x r ⊆ sphereChordalCap x r := by
  intro y hy
  change sphereAngularDistance y x ≤ r at hy
  change sphereChordalSq y.1 x.1 ≤ r ^ 2
  calc
    sphereChordalSq y.1 x.1 ≤ sphereAngularDistance y x ^ 2 :=
      sphereChordalSq_le_sphereAngularDistance_sq y x
    _ ≤ r ^ 2 :=
      (sq_le_sq₀ (sphereAngularDistance_nonneg y x) hr).2 hy

/-- Jordan's sine inequality gives the converse cap inclusion after scaling
the chordal radius by `2 / π`. -/
theorem sphereChordalCap_two_div_pi_mul_subset_sphereAngularCap {n : ℕ}
    (x : sphereSet n) {r : ℝ} (hr : 0 ≤ r) :
    sphereChordalCap x (2 / Real.pi * r) ⊆ sphereAngularCap x r := by
  intro y hy
  let θ := sphereAngularDistance y x
  have hθ0 : 0 ≤ θ := sphereAngularDistance_nonneg y x
  have hθpi : θ ≤ Real.pi := sphereAngularDistance_le_pi y x
  have hhalf0 : 0 ≤ θ / 2 := by positivity
  have hhalfpi : θ / 2 ≤ Real.pi / 2 := by linarith
  have hsin0 : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hhalf0 (hhalfpi.trans (by linarith [Real.pi_pos]))
  have hjordan :
      2 / Real.pi * (θ / 2) ≤ Real.sin (θ / 2) :=
    Real.mul_le_sin hhalf0 hhalfpi
  have hlinear :
      2 / Real.pi * θ ≤ 2 * Real.sin (θ / 2) := by
    calc
      2 / Real.pi * θ = 2 * (2 / Real.pi * (θ / 2)) := by ring
      _ ≤ 2 * Real.sin (θ / 2) := by nlinarith
  have hscaled0 : 0 ≤ 2 / Real.pi * θ := by positivity
  have hsinScaled0 : 0 ≤ 2 * Real.sin (θ / 2) := by positivity
  have hlower :
      (2 / Real.pi * θ) ^ 2 ≤ sphereChordalSq y.1 x.1 := by
    calc
      (2 / Real.pi * θ) ^ 2 ≤
          (2 * Real.sin (θ / 2)) ^ 2 :=
        (sq_le_sq₀ hscaled0 hsinScaled0).2 hlinear
      _ = sphereChordalSq y.1 x.1 := by
        rw [sphereChordalSq_eq_four_mul_sin_half_sq]
        ring
  have hupper :
      sphereChordalSq y.1 x.1 ≤ (2 / Real.pi * r) ^ 2 := hy
  have hrscaled0 : 0 ≤ 2 / Real.pi * r := by positivity
  have hscaled :
      2 / Real.pi * θ ≤ 2 / Real.pi * r :=
    (sq_le_sq₀ hscaled0 hrscaled0).1 (hlower.trans hupper)
  change θ ≤ r
  have hfactor : 0 < 2 / Real.pi := by positivity
  exact (mul_le_mul_iff_right₀ hfactor).mp hscaled

/-- Chordal caps are monotone in their nonnegative radius. -/
theorem sphereChordalCap_mono {n : ℕ} (x : sphereSet n)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    sphereChordalCap x r ⊆ sphereChordalCap x s := by
  intro y hy
  change sphereChordalSq y.1 x.1 ≤ r ^ 2 at hy
  change sphereChordalSq y.1 x.1 ≤ s ^ 2
  exact hy.trans (by nlinarith)

/-- The half-open chordal shell between radii `r` and `s`. -/
def sphereChordalAnnulus {n : ℕ} (x : sphereSet n) (r s : ℝ) :
    Set (sphereSet n) :=
  sphereChordalCap x s \ sphereChordalCap x r

/-- Chordal annuli are measurable, so they can be used directly in the finite
dyadic decomposition of the kernel moments. -/
theorem measurableSet_sphereChordalAnnulus {n : ℕ}
    (x : sphereSet n) (r s : ℝ) :
    MeasurableSet (sphereChordalAnnulus x r s) := by
  exact (measurableSet_sphereChordalCap x s).diff
    (measurableSet_sphereChordalCap x r)

/-- The chordal-square-weighted zonal kernel is integrable on the sphere. -/
theorem integrable_sphereChordalSq_mul_sphereDirichletZonalKernel_section
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : Fin n → ℝ) :
    Integrable (fun y : sphereSet n ↦ sphereChordalSq y.1 x *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x))
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_sphereChordalSq_right x).mul
      (continuous_sphereDirichletZonalKernel_section p k x)
  · exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
      (subset_univ _)

/-- The unnormalized chordal second moment of a continuous zonal-kernel
section. -/
def continuousZonalKernelSecondMoment {n : ℕ} (p k : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  ∫ y : sphereSet n, sphereChordalSq y.1 x *
    MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
      ∂normalizedSphereMeasure n

theorem continuousZonalKernelSecondMoment_nonneg {n : ℕ} (p k : ℕ)
    (x : Fin n → ℝ) : 0 ≤ continuousZonalKernelSecondMoment p k x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (sphereChordalSq_nonneg y.1 x)
    (eval_sphereDirichletZonalKernel_nonneg p k y.1 x)

/-- The angular-square-weighted zonal kernel is integrable on the sphere. -/
theorem integrable_sphereAngularDistance_sq_mul_zonalKernel
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : sphereSet n) :
    Integrable (fun y : sphereSet n ↦ sphereAngularDistance y x ^ 2 *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1))
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_sphereAngularDistance_right x).pow 2 |>.mul
      (continuous_sphereDirichletZonalKernel_section p k x.1)
  · exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
      (subset_univ _)

/-- Splitting a larger angular cap into an inner cap and a half-open annulus
splits the angular second-moment integral additively. -/
theorem setIntegral_angularSecondMoment_cap_eq_add_annulus
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : sphereSet n)
    {r s : ℝ} (hrs : r ≤ s) :
    (∫ y : sphereSet n in sphereAngularCap x s,
        sphereAngularDistance y x ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1)
        ∂normalizedSphereMeasure n) =
      (∫ y : sphereSet n in sphereAngularCap x r,
          sphereAngularDistance y x ^ 2 *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) +
        ∫ y : sphereSet n in sphereAngularAnnulus x r s,
          sphereAngularDistance y x ^ 2 *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n := by
  rw [← sphereAngularCap_union_sphereAngularAnnulus x hrs]
  exact setIntegral_union
    (disjoint_sphereAngularCap_sphereAngularAnnulus x r s)
    (measurableSet_sphereAngularAnnulus x r s)
    (integrable_sphereAngularDistance_sq_mul_zonalKernel hn p k x).integrableOn
    (integrable_sphereAngularDistance_sq_mul_zonalKernel hn p k x).integrableOn

/-- Iterating the cap/annulus split gives an exact finite dyadic
decomposition of the angular second-moment integral. -/
theorem setIntegral_angularSecondMoment_dyadicCap_eq
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : sphereSet n)
    {r : ℝ} (hr : 0 ≤ r) (J : ℕ) :
    (∫ y : sphereSet n in sphereAngularCap x ((2 : ℝ) ^ J * r),
        sphereAngularDistance y x ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1)
        ∂normalizedSphereMeasure n) =
      (∫ y : sphereSet n in sphereAngularCap x r,
          sphereAngularDistance y x ^ 2 *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) +
        ∑ j ∈ Finset.range J,
          ∫ y : sphereSet n in
              sphereAngularAnnulus x
                ((2 : ℝ) ^ j * r) ((2 : ℝ) ^ (j + 1) * r),
            sphereAngularDistance y x ^ 2 *
              MvPolynomial.eval y.1
                (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
  induction J with
  | zero =>
      simp
  | succ J ih =>
      have hrs :
          (2 : ℝ) ^ J * r ≤ (2 : ℝ) ^ (J + 1) * r := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) J]
      rw [setIntegral_angularSecondMoment_cap_eq_add_annulus
        hn p k x hrs]
      rw [ih]
      rw [Finset.sum_range_succ]
      ring

/-- The unnormalized angular second moment of a zonal-kernel section. -/
noncomputable def continuousZonalKernelAngularSecondMoment {n : ℕ}
    (p k : ℕ) (x : sphereSet n) : ℝ :=
  ∫ y : sphereSet n, sphereAngularDistance y x ^ 2 *
    MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
      ∂normalizedSphereMeasure n

/-- The angular second moment is nonnegative. -/
theorem continuousZonalKernelAngularSecondMoment_nonneg {n : ℕ}
    (p k : ℕ) (x : sphereSet n) :
    0 ≤ continuousZonalKernelAngularSecondMoment p k x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (sq_nonneg _)
    (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)

/-- The angular second moment is at most `π²` times the kernel mass. -/
theorem continuousZonalKernelAngularSecondMoment_le_pi_sq_mul_mass
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : sphereSet n) :
    continuousZonalKernelAngularSecondMoment p k x ≤
      Real.pi ^ 2 * continuousZonalKernelMass p k x.1 := by
  calc
    continuousZonalKernelAngularSecondMoment p k x ≤
        ∫ y : sphereSet n, Real.pi ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n := by
      apply integral_mono
        (integrable_sphereAngularDistance_sq_mul_zonalKernel hn p k x)
        ((integrable_sphereDirichletZonalKernel_section
          hn p k x.1).const_mul (Real.pi ^ 2))
      intro y
      apply mul_le_mul_of_nonneg_right
      · exact sphereAngularDistance_sq_le_pi_sq y x
      · exact eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1
    _ = Real.pi ^ 2 * continuousZonalKernelMass p k x.1 := by
      rw [integral_const_mul]
      rfl

/-- One angular annulus contributes at most its outer-radius square times the
inner-radius kernel bound times the measure of the outer cap. -/
theorem setIntegral_angularSecondMoment_le_of_angularAnnulus
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : sphereSet n)
    {r s : ℝ} (hr : 0 < r) :
    (∫ y : sphereSet n in sphereAngularAnnulus x r s,
        sphereAngularDistance y x ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1)
        ∂normalizedSphereMeasure n) ≤
      (s ^ 2 * (Real.pi / r) ^ (2 * p)) *
        (normalizedSphereMeasure n).real (sphereAngularCap x s) := by
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  let bound := s ^ 2 * (Real.pi / r) ^ (2 * p)
  have hmeas : MeasurableSet (sphereAngularAnnulus x r s) :=
    measurableSet_sphereAngularAnnulus x r s
  have hfint := integrable_sphereAngularDistance_sq_mul_zonalKernel
    hn p k x
  have hboundInt :
      IntegrableOn (fun _y : sphereSet n ↦ bound)
        (sphereAngularAnnulus x r s) (normalizedSphereMeasure n) :=
    (MeasureTheory.integrable_const _).integrableOn
  have hpoint :
      (∫ y : sphereSet n in sphereAngularAnnulus x r s,
          sphereAngularDistance y x ^ 2 *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) ≤
        ∫ _y : sphereSet n in sphereAngularAnnulus x r s, bound
          ∂normalizedSphereMeasure n := by
    apply setIntegral_mono_on hfint.integrableOn hboundInt hmeas
    intro y hy
    have houter : sphereAngularDistance y x ≤ s := hy.1
    have hs : 0 ≤ s :=
      (sphereAngularDistance_nonneg y x).trans houter
    have hangleSq :
        sphereAngularDistance y x ^ 2 ≤ s ^ 2 :=
      (sq_le_sq₀ (sphereAngularDistance_nonneg y x) hs).2 houter
    have hkernel :=
      eval_sphereDirichletZonalKernel_le_pi_div_radius_pow_of_mem_angularAnnulus
        p k x y hr hy
    calc
      sphereAngularDistance y x ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1) ≤
        s ^ 2 * MvPolynomial.eval y.1
          (sphereDirichletZonalKernel p k x.1) :=
            mul_le_mul_of_nonneg_right hangleSq
              (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)
      _ ≤ s ^ 2 * (Real.pi / r) ^ (2 * p) :=
        mul_le_mul_of_nonneg_left hkernel (sq_nonneg s)
  have hsubset :
      sphereAngularAnnulus x r s ⊆ sphereAngularCap x s := by
    intro y hy
    exact hy.1
  have hboundNonneg : 0 ≤ bound := by
    exact mul_nonneg (sq_nonneg s)
      (pow_nonneg (div_nonneg Real.pi_pos.le hr.le) _)
  calc
    (∫ y : sphereSet n in sphereAngularAnnulus x r s,
        sphereAngularDistance y x ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1)
        ∂normalizedSphereMeasure n) ≤
      ∫ _y : sphereSet n in sphereAngularAnnulus x r s, bound
        ∂normalizedSphereMeasure n := hpoint
    _ = bound *
        (normalizedSphereMeasure n).real
          (sphereAngularAnnulus x r s) := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    _ ≤ bound *
        (normalizedSphereMeasure n).real
          (sphereAngularCap x s) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hboundNonneg
    _ = (s ^ 2 * (Real.pi / r) ^ (2 * p)) *
        (normalizedSphereMeasure n).real
          (sphereAngularCap x s) := rfl

/-- The angular second-moment contribution of an inner cap is bounded by
its radius square times the global kernel peak times its measure. -/
theorem setIntegral_angularSecondMoment_le_of_angularCap
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : sphereSet n)
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ y : sphereSet n in sphereAngularCap x s,
        sphereAngularDistance y x ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1)
        ∂normalizedSphereMeasure n) ≤
      (s ^ 2 * (2 * (k : ℝ) + 1) ^ (2 * p)) *
        (normalizedSphereMeasure n).real (sphereAngularCap x s) := by
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  let bound := s ^ 2 * (2 * (k : ℝ) + 1) ^ (2 * p)
  have hmeas : MeasurableSet (sphereAngularCap x s) :=
    measurableSet_sphereAngularCap x s
  have hfint := integrable_sphereAngularDistance_sq_mul_zonalKernel
    hn p k x
  have hboundInt :
      IntegrableOn (fun _y : sphereSet n ↦ bound)
        (sphereAngularCap x s) (normalizedSphereMeasure n) :=
    (MeasureTheory.integrable_const _).integrableOn
  have hpoint :
      (∫ y : sphereSet n in sphereAngularCap x s,
          sphereAngularDistance y x ^ 2 *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) ≤
        ∫ _y : sphereSet n in sphereAngularCap x s, bound
          ∂normalizedSphereMeasure n := by
    apply setIntegral_mono_on hfint.integrableOn hboundInt hmeas
    intro y hy
    have hangleSq :
        sphereAngularDistance y x ^ 2 ≤ s ^ 2 :=
      (sq_le_sq₀ (sphereAngularDistance_nonneg y x) hs).2 hy
    calc
      sphereAngularDistance y x ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1) ≤
        s ^ 2 * MvPolynomial.eval y.1
          (sphereDirichletZonalKernel p k x.1) :=
            mul_le_mul_of_nonneg_right hangleSq
              (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)
      _ ≤ s ^ 2 * (2 * (k : ℝ) + 1) ^ (2 * p) :=
        mul_le_mul_of_nonneg_left
          (eval_sphereDirichletZonalKernel_le_peak p k y.2 x.2)
          (sq_nonneg s)
  calc
    (∫ y : sphereSet n in sphereAngularCap x s,
        sphereAngularDistance y x ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1)
        ∂normalizedSphereMeasure n) ≤
      ∫ _y : sphereSet n in sphereAngularCap x s, bound
        ∂normalizedSphereMeasure n := hpoint
    _ = bound *
        (normalizedSphereMeasure n).real
          (sphereAngularCap x s) := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    _ = (s ^ 2 * (2 * (k : ℝ) + 1) ^ (2 * p)) *
        (normalizedSphereMeasure n).real
          (sphereAngularCap x s) := rfl

/-- The chordal second moment is dominated by the angular second moment. -/
theorem continuousZonalKernelSecondMoment_le_angularSecondMoment
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : sphereSet n) :
    continuousZonalKernelSecondMoment p k x.1 ≤
      continuousZonalKernelAngularSecondMoment p k x := by
  apply integral_mono
    (integrable_sphereChordalSq_mul_sphereDirichletZonalKernel_section
      hn p k x.1)
    (integrable_sphereAngularDistance_sq_mul_zonalKernel hn p k x)
  intro y
  exact mul_le_mul_of_nonneg_right
    (sphereChordalSq_le_sphereAngularDistance_sq y x)
    (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)

/-- The chordal second moment is bounded by four times the kernel mass. -/
theorem continuousZonalKernelSecondMoment_le_four_mul_mass
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) :
    continuousZonalKernelSecondMoment p k x ≤
      4 * continuousZonalKernelMass p k x := by
  calc
    continuousZonalKernelSecondMoment p k x ≤
        ∫ y : sphereSet n, 4 *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
            ∂normalizedSphereMeasure n := by
      apply integral_mono
        (integrable_sphereChordalSq_mul_sphereDirichletZonalKernel_section
          hn p k x)
        ((integrable_sphereDirichletZonalKernel_section hn p k x).const_mul 4)
      intro y
      exact mul_le_mul_of_nonneg_right (sphereChordalSq_le_four y.2 hx)
        (eval_sphereDirichletZonalKernel_nonneg p k y.1 x)
    _ = 4 * continuousZonalKernelMass p k x := by
      rw [integral_const_mul]
      rfl

/-- Independently of bandwidth, every normalized kernel has chordal second
moment at most four. The sharper estimate below improves this to `C / k²`. -/
theorem continuousZonalKernelSecondMoment_div_mass_le_four
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) :
    continuousZonalKernelSecondMoment p k x /
      continuousZonalKernelMass p k x ≤ 4 := by
  apply (div_le_iff₀ (continuousZonalKernelMass_pos hn p k x hx)).2
  exact continuousZonalKernelSecondMoment_le_four_mul_mass hn p k x hx

/-- A pointwise increment estimate and a normalized chordal second-moment
estimate imply a pointwise approximation estimate for the normalized
continuous kernel operator. -/
theorem abs_continuousZonalKernelIntegral_sub_le_of_chordalSq
    {n D : ℕ} (hn : 0 < n) (p k : ℕ) (Z A B : ℝ)
    (hA : 0 ≤ A) (v : spherePolynomialSpace n D)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n)
    (hmass : continuousZonalKernelMass p k x = Z)
    (hinc : ∀ y : sphereSet n,
      |v.1 y - v.1 ⟨x, hx⟩| ≤ A * sphereChordalSq y.1 x)
    (hmoment : continuousZonalKernelSecondMoment p k x / Z ≤ B) :
    |(∫ y : sphereSet n, v.1 y *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n) / Z - v.1 ⟨x, hx⟩| ≤ A * B := by
  have hZpos : 0 < Z :=
    (continuousZonalKernelMass_pos hn p k x hx).trans_eq hmass
  have hmajor : Integrable (fun y : sphereSet n ↦
      A * (sphereChordalSq y.1 x *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)))
      (normalizedSphereMeasure n) :=
    (integrable_sphereChordalSq_mul_sphereDirichletZonalKernel_section
      hn p k x).const_mul A
  have hintegral :
      |∫ y : sphereSet n, (v.1 y - v.1 ⟨x, hx⟩) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
            ∂normalizedSphereMeasure n| ≤
        A * continuousZonalKernelSecondMoment p k x := by
    calc
      |∫ y : sphereSet n, (v.1 y - v.1 ⟨x, hx⟩) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
            ∂normalizedSphereMeasure n| ≤
          ∫ y : sphereSet n, A * (sphereChordalSq y.1 x *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x))
              ∂normalizedSphereMeasure n := by
        change ‖∫ y : sphereSet n, (v.1 y - v.1 ⟨x, hx⟩) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
            ∂normalizedSphereMeasure n‖ ≤ _
        apply norm_integral_le_of_norm_le hmajor
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul]
        rw [abs_of_nonneg (eval_sphereDirichletZonalKernel_nonneg p k y.1 x)]
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hinc y)
            (eval_sphereDirichletZonalKernel_nonneg p k y.1 x)
      _ = A * continuousZonalKernelSecondMoment p k x := by
        rw [integral_const_mul]
        rfl
  rw [continuousZonalKernelIntegral_sub hn p k Z v x hx hmass]
  rw [abs_div, abs_of_pos hZpos]
  calc
    |∫ y : sphereSet n, (v.1 y - v.1 ⟨x, hx⟩) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n| / Z ≤
        (A * continuousZonalKernelSecondMoment p k x) / Z :=
      div_le_div_of_nonneg_right hintegral hZpos.le
    _ = A * (continuousZonalKernelSecondMoment p k x / Z) := by ring
    _ ≤ A * B := mul_le_mul_of_nonneg_left hmoment hA

/-- Uniform increment and second-moment estimates give the sup-norm estimate
needed by the continuous kernel candidate. -/
theorem norm_sub_sphereRestrictionLinear_le_of_chordalSq
    {n D : ℕ} (hn : 0 < n) (p k : ℕ) (Z A B : ℝ)
    (hA : 0 ≤ A)
    (T : spherePolynomialSpace n D →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (hmass : ∀ x ∈ sphereSet n, continuousZonalKernelMass p k x = Z)
    (heval : ∀ (v : spherePolynomialSpace n D) (x : Fin n → ℝ),
      x ∈ sphereSet n →
        MvPolynomial.eval x (T v) =
          (∫ y : sphereSet n, v.1 y *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
              ∂normalizedSphereMeasure n) / Z)
    (hinc : ∀ (v : spherePolynomialSpace n D) (x : Fin n → ℝ)
      (hx : x ∈ sphereSet n) (y : sphereSet n),
        |v.1 y - v.1 ⟨x, hx⟩| ≤
          (A * ‖v‖) * sphereChordalSq y.1 x)
    (hmoment : ∀ x ∈ sphereSet n,
      continuousZonalKernelSecondMoment p k x / Z ≤ B)
    (v : spherePolynomialSpace n D) :
    ‖v.1 - sphereRestrictionLinear n (T v)‖ ≤ (A * B) * ‖v‖ := by
  obtain ⟨x₀, hx₀⟩ := sphereSet_nonempty hn
  have hZpos : 0 < Z :=
    (continuousZonalKernelMass_pos hn p k x₀ hx₀).trans_eq (hmass x₀ hx₀)
  have hB : 0 ≤ B :=
    (div_nonneg (continuousZonalKernelSecondMoment_nonneg p k x₀) hZpos.le).trans
      (hmoment x₀ hx₀)
  rw [ContinuousMap.norm_le _
    (mul_nonneg (mul_nonneg hA hB) (norm_nonneg v))]
  intro x
  rw [show (v.1 - sphereRestrictionLinear n (T v)) x =
      v.1 x - MvPolynomial.eval x.1 (T v) by rfl]
  rw [Real.norm_eq_abs, abs_sub_comm, heval v x.1 x.2]
  have hpoint := abs_continuousZonalKernelIntegral_sub_le_of_chordalSq
    hn p k Z (A * ‖v‖) B (mul_nonneg hA (norm_nonneg v)) v x.1 x.2
      (hmass x.1 x.2) (hinc v x.1 x.2) (hmoment x.1 x.2)
  calc
    |(∫ y : sphereSet n, v.1 y *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) / Z - v.1 x| ≤
        (A * ‖v‖) * B := hpoint
    _ = (A * B) * ‖v‖ := by ring

/-- A cancellation-aware integrated second-order remainder estimate and a
normalized second-moment estimate imply the sup-norm bound used by the
axial-reflection pairing argument. -/
theorem norm_sub_sphereRestrictionLinear_le_of_integralRemainder
    {n D : ℕ} (hn : 0 < n) (p k : ℕ) (Z A B : ℝ)
    (hA : 0 ≤ A)
    (T : spherePolynomialSpace n D →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (hmass : ∀ x ∈ sphereSet n, continuousZonalKernelMass p k x = Z)
    (heval : ∀ (v : spherePolynomialSpace n D) (x : Fin n → ℝ),
      x ∈ sphereSet n →
        MvPolynomial.eval x (T v) =
          (∫ y : sphereSet n, v.1 y *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
              ∂normalizedSphereMeasure n) / Z)
    (hremainder : ∀ (v : spherePolynomialSpace n D) (x : Fin n → ℝ)
      (hx : x ∈ sphereSet n),
        |∫ y : sphereSet n, (v.1 y - v.1 ⟨x, hx⟩) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
            ∂normalizedSphereMeasure n| ≤
          (A * ‖v‖) * continuousZonalKernelSecondMoment p k x)
    (hmoment : ∀ x ∈ sphereSet n,
      continuousZonalKernelSecondMoment p k x / Z ≤ B)
    (v : spherePolynomialSpace n D) :
    ‖v.1 - sphereRestrictionLinear n (T v)‖ ≤ (A * B) * ‖v‖ := by
  obtain ⟨x₀, hx₀⟩ := sphereSet_nonempty hn
  have hZpos : 0 < Z :=
    (continuousZonalKernelMass_pos hn p k x₀ hx₀).trans_eq (hmass x₀ hx₀)
  have hB : 0 ≤ B :=
    (div_nonneg (continuousZonalKernelSecondMoment_nonneg p k x₀) hZpos.le).trans
      (hmoment x₀ hx₀)
  rw [ContinuousMap.norm_le _
    (mul_nonneg (mul_nonneg hA hB) (norm_nonneg v))]
  intro x
  rw [show (v.1 - sphereRestrictionLinear n (T v)) x =
      v.1 x - MvPolynomial.eval x.1 (T v) by rfl]
  rw [Real.norm_eq_abs, abs_sub_comm, heval v x.1 x.2]
  rw [continuousZonalKernelIntegral_sub hn p k Z v x.1 x.2
    (hmass x.1 x.2)]
  rw [abs_div, abs_of_pos hZpos]
  calc
    |∫ y : sphereSet n, (v.1 y - v.1 x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n| / Z ≤
        ((A * ‖v‖) * continuousZonalKernelSecondMoment p k x.1) / Z :=
      div_le_div_of_nonneg_right (hremainder v x.1 x.2) hZpos.le
    _ = (A * ‖v‖) *
        (continuousZonalKernelSecondMoment p k x.1 / Z) := by ring
    _ ≤ (A * ‖v‖) * B :=
      mul_le_mul_of_nonneg_left (hmoment x.1 x.2)
        (mul_nonneg hA (norm_nonneg v))
    _ = (A * B) * ‖v‖ := by ring

end QuarticConvergence
end OptimalConvergenceRates
