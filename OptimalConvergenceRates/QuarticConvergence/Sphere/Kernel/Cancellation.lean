/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/Cancellation.lean

  Axial-reflection cancellation for the continuous zonal-kernel operator.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Localization
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Reflection

open Set MeasureTheory MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers
open SpherePolynomialQuadrature

/-- Axial reflection about x preserves squared chordal distance from x. -/
@[simp] theorem sphereChordalSq_sphereAxialReflection {n : ℕ}
    (x y : sphereSet n) :
    sphereChordalSq (sphereAxialReflection x y).1 x.1 =
      sphereChordalSq y.1 x.1 := by
  rw [sphereChordalSq_eq_two_mul_one_sub_dot
      (sphereAxialReflection x y).2 x.2,
    sphereChordalSq_eq_two_mul_one_sub_dot y.2 x.2]
  change 2 * (1 - ∑ i, sphereAxialReflectionRaw x.1 y.1 i * x.1 i) =
    2 * (1 - ∑ i, y.1 i * x.1 i)
  rw [sum_sphereAxialReflectionRaw_mul_axis x.2 y.1]
/-- Applying one axial reflection to both points preserves squared chordal
distance. -/
theorem sphereChordalSq_map_sphereAxialReflection {n : ℕ}
    (a x y : sphereSet n) :
    sphereChordalSq (sphereAxialReflection a y).1
        (sphereAxialReflection a x).1 =
      sphereChordalSq y.1 x.1 := by
  rw [sphereChordalSq_eq_two_mul_one_sub_dot
      (sphereAxialReflection a y).2 (sphereAxialReflection a x).2,
    sphereChordalSq_eq_two_mul_one_sub_dot y.2 x.2]
  change 2 * (1 - ∑ i, sphereAxialReflectionRaw a.1 y.1 i *
      sphereAxialReflectionRaw a.1 x.1 i) =
    2 * (1 - ∑ i, y.1 i * x.1 i)
  rw [sum_sphereAxialReflectionRaw_mul_sphereAxialReflectionRaw a.2 y.1 x.1]

/-- Pulling back a chordal cap centered at the reflected point gives the
original chordal cap. -/
theorem preimage_sphereChordalCap_sphereAxialReflection {n : ℕ}
    (a x : sphereSet n) (r : ℝ) :
    sphereAxialReflection a ⁻¹'
        sphereChordalCap (sphereAxialReflection a x) r =
      sphereChordalCap x r := by
  ext y
  change sphereChordalSq (sphereAxialReflection a y).1
      (sphereAxialReflection a x).1 ≤ r ^ 2 ↔
    sphereChordalSq y.1 x.1 ≤ r ^ 2
  rw [sphereChordalSq_map_sphereAxialReflection]

/-- Reflection invariance makes chordal-cap measure covariant in its center. -/
theorem normalizedSphereMeasure_sphereChordalCap_sphereAxialReflection
    {n : ℕ} (a x : sphereSet n) (r : ℝ) :
    normalizedSphereMeasure n
        (sphereChordalCap (sphereAxialReflection a x) r) =
      normalizedSphereMeasure n (sphereChordalCap x r) := by
  let μ := normalizedSphereMeasure n
  have hpres := sphereAxialReflection_measurePreserving a
  have hmeas : MeasurableSet
      (sphereChordalCap (sphereAxialReflection a x) r) :=
    measurableSet_sphereChordalCap _ _
  calc
    μ (sphereChordalCap (sphereAxialReflection a x) r) =
        μ (sphereAxialReflection a ⁻¹'
          sphereChordalCap (sphereAxialReflection a x) r) :=
      (Measure.measure_preimage_of_map_eq_self hpres.map_eq
        hmeas.nullMeasurableSet).symm
    _ = μ (sphereChordalCap x r) := by
      rw [preimage_sphereChordalCap_sphereAxialReflection]

/-- In dimension at least two, chordal caps of a fixed radius have the same
normalized measure at every center. -/
theorem normalizedSphereMeasure_sphereChordalCap_eq_on_sphere
    {n : ℕ} (hn : 2 ≤ n) (r : ℝ) (x z : sphereSet n) :
    normalizedSphereMeasure n (sphereChordalCap x r) =
      normalizedSphereMeasure n (sphereChordalCap z r) := by
  obtain ⟨a, ha⟩ := exists_sphereAxialReflection_eq hn x z
  have h :=
    normalizedSphereMeasure_sphereChordalCap_sphereAxialReflection a x r
  rw [ha] at h
  exact h.symm

/-- The real-valued chordal-cap measure is likewise independent of its
center. -/
theorem normalizedSphereMeasureReal_sphereChordalCap_eq_on_sphere
    {n : ℕ} (hn : 2 ≤ n) (r : ℝ) (x z : sphereSet n) :
    (normalizedSphereMeasure n).real (sphereChordalCap x r) =
      (normalizedSphereMeasure n).real (sphereChordalCap z r) := by
  exact congrArg ENNReal.toReal
    (normalizedSphereMeasure_sphereChordalCap_eq_on_sphere hn r x z)

/-- Applying one axial reflection to both points preserves angular distance. -/
@[simp] theorem sphereAngularDistance_map_sphereAxialReflection {n : ℕ}
    (a x y : sphereSet n) :
    sphereAngularDistance (sphereAxialReflection a y)
        (sphereAxialReflection a x) = sphereAngularDistance y x := by
  unfold sphereAngularDistance
  congr 1
  exact sum_sphereAxialReflectionRaw_mul_sphereAxialReflectionRaw
    a.2 y.1 x.1

/-- Pulling back a cap centered at the reflected point gives the original cap. -/
theorem preimage_sphereAngularCap_sphereAxialReflection {n : ℕ}
    (a x : sphereSet n) (r : ℝ) :
    sphereAxialReflection a ⁻¹'
        sphereAngularCap (sphereAxialReflection a x) r =
      sphereAngularCap x r := by
  ext y
  change sphereAngularDistance (sphereAxialReflection a y)
      (sphereAxialReflection a x) ≤ r ↔ sphereAngularDistance y x ≤ r
  rw [sphereAngularDistance_map_sphereAxialReflection]

/-- Reflection invariance makes angular-cap measure covariant in its center. -/
theorem normalizedSphereMeasure_sphereAngularCap_sphereAxialReflection
    {n : ℕ} (a x : sphereSet n) (r : ℝ) :
    normalizedSphereMeasure n
        (sphereAngularCap (sphereAxialReflection a x) r) =
      normalizedSphereMeasure n (sphereAngularCap x r) := by
  let μ := normalizedSphereMeasure n
  have hpres := sphereAxialReflection_measurePreserving a
  have hmeas : MeasurableSet
      (sphereAngularCap (sphereAxialReflection a x) r) :=
    measurableSet_sphereAngularCap _ _
  calc
    μ (sphereAngularCap (sphereAxialReflection a x) r) =
        μ (sphereAxialReflection a ⁻¹'
          sphereAngularCap (sphereAxialReflection a x) r) :=
      (Measure.measure_preimage_of_map_eq_self hpres.map_eq
        hmeas.nullMeasurableSet).symm
    _ = μ (sphereAngularCap x r) := by
      rw [preimage_sphereAngularCap_sphereAxialReflection]

/-- In dimension at least two, angular caps of a fixed radius have the same
normalized measure at every center. -/
theorem normalizedSphereMeasure_sphereAngularCap_eq_on_sphere
    {n : ℕ} (hn : 2 ≤ n) (r : ℝ) (x z : sphereSet n) :
    normalizedSphereMeasure n (sphereAngularCap x r) =
      normalizedSphereMeasure n (sphereAngularCap z r) := by
  obtain ⟨a, ha⟩ := exists_sphereAxialReflection_eq hn x z
  have h :=
    normalizedSphereMeasure_sphereAngularCap_sphereAxialReflection a x r
  rw [ha] at h
  exact h.symm

/-- The real-valued cap measure is likewise independent of its center. -/
theorem normalizedSphereMeasureReal_sphereAngularCap_eq_on_sphere
    {n : ℕ} (hn : 2 ≤ n) (r : ℝ) (x z : sphereSet n) :
    (normalizedSphereMeasure n).real (sphereAngularCap x r) =
      (normalizedSphereMeasure n).real (sphereAngularCap z r) := by
  exact congrArg ENNReal.toReal
    (normalizedSphereMeasure_sphereAngularCap_eq_on_sphere hn r x z)

/-- Integrals against normalized sphere measure are invariant under axial
reflection. -/
theorem integral_comp_sphereAxialReflection {n : ℕ} (x : sphereSet n)
    (f : sphereSet n → ℝ) :
    (∫ y, f (sphereAxialReflection x y) ∂normalizedSphereMeasure n) =
      ∫ y, f y ∂normalizedSphereMeasure n :=
  (sphereAxialReflection_measurePreserving x).integral_comp
    (sphereAxialReflection_measurableEmbedding x) f

/-- The continuous zonal-kernel mass is unchanged when its center is axially
reflected. -/
theorem continuousZonalKernelMass_sphereAxialReflection
    {n : ℕ} (p k : ℕ) (a x : sphereSet n) :
    continuousZonalKernelMass p k (sphereAxialReflection a x).1 =
      continuousZonalKernelMass p k x.1 := by
  unfold continuousZonalKernelMass
  calc
    (∫ y : sphereSet n,
      MvPolynomial.eval y.1
        (sphereDirichletZonalKernel p k (sphereAxialReflection a x).1)
        ∂normalizedSphereMeasure n) =
      ∫ y : sphereSet n,
        MvPolynomial.eval (sphereAxialReflection a y).1
          (sphereDirichletZonalKernel p k (sphereAxialReflection a x).1)
          ∂normalizedSphereMeasure n :=
        (integral_comp_sphereAxialReflection a
          (fun y ↦ MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k (sphereAxialReflection a x).1))).symm
    _ = ∫ y : sphereSet n,
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      filter_upwards with y
      exact eval_sphereDirichletZonalKernel_map_sphereAxialReflection p k a x y

/-- The unnormalized angular second moment is unchanged when its center is
axially reflected. -/
theorem continuousZonalKernelAngularSecondMoment_sphereAxialReflection
    {n : ℕ} (p k : ℕ) (a x : sphereSet n) :
    continuousZonalKernelAngularSecondMoment p k (sphereAxialReflection a x) =
      continuousZonalKernelAngularSecondMoment p k x := by
  unfold continuousZonalKernelAngularSecondMoment
  calc
    (∫ y : sphereSet n,
      sphereAngularDistance y (sphereAxialReflection a x) ^ 2 *
        MvPolynomial.eval y.1
          (sphereDirichletZonalKernel p k (sphereAxialReflection a x).1)
        ∂normalizedSphereMeasure n) =
      ∫ y : sphereSet n,
        sphereAngularDistance (sphereAxialReflection a y)
            (sphereAxialReflection a x) ^ 2 *
          MvPolynomial.eval (sphereAxialReflection a y).1
            (sphereDirichletZonalKernel p k (sphereAxialReflection a x).1)
          ∂normalizedSphereMeasure n :=
        (integral_comp_sphereAxialReflection a
          (fun y ↦ sphereAngularDistance y (sphereAxialReflection a x) ^ 2 *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k
                (sphereAxialReflection a x).1))).symm
    _ = ∫ y : sphereSet n, sphereAngularDistance y x ^ 2 *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      filter_upwards with y
      rw [sphereAngularDistance_map_sphereAxialReflection,
        eval_sphereDirichletZonalKernel_map_sphereAxialReflection]

/-- The unnormalized chordal second moment is unchanged when its center is
axially reflected. -/
theorem continuousZonalKernelSecondMoment_sphereAxialReflection
    {n : ℕ} (p k : ℕ) (a x : sphereSet n) :
    continuousZonalKernelSecondMoment p k (sphereAxialReflection a x).1 =
      continuousZonalKernelSecondMoment p k x.1 := by
  unfold continuousZonalKernelSecondMoment
  calc
    (∫ y : sphereSet n,
      sphereChordalSq y.1 (sphereAxialReflection a x).1 *
        MvPolynomial.eval y.1
          (sphereDirichletZonalKernel p k (sphereAxialReflection a x).1)
        ∂normalizedSphereMeasure n) =
      ∫ y : sphereSet n,
        sphereChordalSq (sphereAxialReflection a y).1
            (sphereAxialReflection a x).1 *
          MvPolynomial.eval (sphereAxialReflection a y).1
            (sphereDirichletZonalKernel p k (sphereAxialReflection a x).1)
          ∂normalizedSphereMeasure n :=
        (integral_comp_sphereAxialReflection a
          (fun y ↦ sphereChordalSq y.1 (sphereAxialReflection a x).1 *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k
                (sphereAxialReflection a x).1))).symm
    _ = ∫ y : sphereSet n,
        sphereChordalSq y.1 x.1 *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      filter_upwards with y
      rw [sphereChordalSq_map_sphereAxialReflection,
        eval_sphereDirichletZonalKernel_map_sphereAxialReflection]

/-- The normalized chordal second moment is invariant under axial reflection. -/
theorem continuousZonalKernelSecondMoment_div_mass_sphereAxialReflection
    {n : ℕ} (p k : ℕ) (a x : sphereSet n) :
    continuousZonalKernelSecondMoment p k (sphereAxialReflection a x).1 /
        continuousZonalKernelMass p k (sphereAxialReflection a x).1 =
      continuousZonalKernelSecondMoment p k x.1 /
        continuousZonalKernelMass p k x.1 := by
  rw [continuousZonalKernelSecondMoment_sphereAxialReflection,
    continuousZonalKernelMass_sphereAxialReflection]
/-- Pairing each integration point with its axial reflection cancels the
first-order part of the kernel increment exactly. -/
theorem two_mul_integral_kernel_increment_eq_integral_symmetricIncrement
    {n D : ℕ} (hn : 0 < n) (p k : ℕ)
    (v : spherePolynomialSpace n D) (x : sphereSet n) :
    2 * (∫ y : sphereSet n, (v.1 y - v.1 x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) =
      ∫ y : sphereSet n,
        (v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
  let f : sphereSet n → ℝ := fun y ↦
    (v.1 y - v.1 x) *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
  have hf : Integrable f (normalizedSphereMeasure n) := by
    have hmul :=
      integrable_mul_sphereDirichletZonalKernel_section hn p k v x.1
    have hconst :=
      (integrable_sphereDirichletZonalKernel_section hn p k x.1).const_mul
        (v.1 x)
    convert hmul.sub hconst using 1
    funext y
    dsimp [f]
    ring
  have hfcomp : Integrable (fun y ↦ f (sphereAxialReflection x y))
      (normalizedSphereMeasure n) := by
    change Integrable (f ∘ sphereAxialReflection x)
      (normalizedSphereMeasure n)
    exact ((sphereAxialReflection_measurePreserving x).integrable_comp_emb
      (sphereAxialReflection_measurableEmbedding x)).2 hf
  calc
    2 * (∫ y : sphereSet n, (v.1 y - v.1 x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n) =
        2 * ∫ y : sphereSet n, f y ∂normalizedSphereMeasure n := by rfl
    _ = (∫ y : sphereSet n, f y ∂normalizedSphereMeasure n) +
        ∫ y : sphereSet n, f (sphereAxialReflection x y)
          ∂normalizedSphereMeasure n := by
      rw [integral_comp_sphereAxialReflection]
      ring
    _ = ∫ y : sphereSet n,
        (f y + f (sphereAxialReflection x y))
          ∂normalizedSphereMeasure n :=
      (integral_add hf hfcomp).symm
    _ = ∫ y : sphereSet n,
        (v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp [f]
      rw [← sphereAxialReflection_coe x y]
      rw [eval_sphereDirichletZonalKernel_sphereAxialReflection]
      ring

/-- A symmetric second-difference estimate implies the integrated remainder
bound required by the near-identity argument. The factor two in the hypothesis
is canceled by averaging the two reflected copies of the integral. -/
theorem abs_integral_kernel_increment_le_of_symmetricIncrement
    {n D : ℕ} (hn : 0 < n) (p k : ℕ) (A : ℝ)
    (v : spherePolynomialSpace n D) (x : sphereSet n)
    (hsymmetric : ∀ y : sphereSet n,
      |v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x| ≤
        (2 * (A * ‖v‖)) * sphereChordalSq y.1 x.1) :
    |∫ y : sphereSet n, (v.1 y - v.1 x) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
          ∂normalizedSphereMeasure n| ≤
      (A * ‖v‖) * continuousZonalKernelSecondMoment p k x.1 := by
  have hmajor : Integrable (fun y : sphereSet n ↦
      (2 * (A * ‖v‖)) *
        (sphereChordalSq y.1 x.1 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel p k x.1)))
      (normalizedSphereMeasure n) :=
    (integrable_sphereChordalSq_mul_sphereDirichletZonalKernel_section
      hn p k x.1).const_mul (2 * (A * ‖v‖))
  have hsymIntegral :
      |∫ y : sphereSet n,
        (v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| ≤
        2 * ((A * ‖v‖) *
          continuousZonalKernelSecondMoment p k x.1) := by
    calc
      |∫ y : sphereSet n,
        (v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| ≤
          ∫ y : sphereSet n,
            (2 * (A * ‖v‖)) *
              (sphereChordalSq y.1 x.1 *
                MvPolynomial.eval y.1
                  (sphereDirichletZonalKernel p k x.1))
              ∂normalizedSphereMeasure n := by
        change ‖∫ y : sphereSet n,
          (v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x) *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n‖ ≤ _
        apply norm_integral_le_of_norm_le hmajor
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg
            (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)]
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right (hsymmetric y)
            (eval_sphereDirichletZonalKernel_nonneg p k y.1 x.1)
      _ = 2 * ((A * ‖v‖) *
          continuousZonalKernelSecondMoment p k x.1) := by
        rw [integral_const_mul]
        unfold continuousZonalKernelSecondMoment
        ring
  have hpair :=
    two_mul_integral_kernel_increment_eq_integral_symmetricIncrement
      hn p k v x
  have habs :
      2 * |∫ y : sphereSet n, (v.1 y - v.1 x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| =
        |∫ y : sphereSet n,
          (v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x) *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n| := by
    calc
      2 * |∫ y : sphereSet n, (v.1 y - v.1 x) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n| =
          |2 * (∫ y : sphereSet n, (v.1 y - v.1 x) *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n)| := by
        rw [abs_mul]
        norm_num
      _ = |∫ y : sphereSet n,
          (v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x) *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel p k x.1)
              ∂normalizedSphereMeasure n| :=
        congrArg abs hpair
  linarith

end QuarticConvergence
end OptimalConvergenceRates

