/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/Reflection.lean

  The axial reflection used to cancel first-order kernel error.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Measure
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.PolynomialRange
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

open Set MeasureTheory MvPolynomial Finset

open scoped Pointwise
noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- Reflection through the line spanned by a unit vector `x`. -/
def sphereAxialReflectionRaw {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ 2 * (∑ j, y j * x j) * x i - y i

/-- Axial reflection preserves the dot product with its unit axis. -/
theorem sum_sphereAxialReflectionRaw_mul_axis {n : ℕ}
    {x : Fin n → ℝ} (hx : x ∈ sphereSet n) (y : Fin n → ℝ) :
    ∑ i, sphereAxialReflectionRaw x y i * x i = ∑ i, y i * x i := by
  have hx' : ∑ i, x i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using hx
  let a := ∑ j, y j * x j
  calc
    (∑ i, sphereAxialReflectionRaw x y i * x i) =
        ∑ i, ((2 * a) * (x i * x i) - y i * x i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold sphereAxialReflectionRaw a
      ring
    _ = (2 * a) * (∑ i, x i * x i) - ∑ i, y i * x i := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = ∑ i, y i * x i := by
      rw [show (∑ i, x i * x i) = 1 by simpa [pow_two] using hx']
      unfold a
      ring

/-- Axial reflection preserves the algebraic unit sphere. -/
theorem sphereAxialReflectionRaw_mem_sphereSet {n : ℕ}
    {x y : Fin n → ℝ} (hx : x ∈ sphereSet n) (hy : y ∈ sphereSet n) :
    sphereAxialReflectionRaw x y ∈ sphereSet n := by
  have hx' : ∑ i, x i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using hx
  have hy' : ∑ i, y i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using hy
  have hxy : ∑ i, x i * y i = ∑ i, y i * x i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X, mem_ofPred_eq]
  let a := ∑ j, y j * x j
  calc
    (∑ i, sphereAxialReflectionRaw x y i ^ 2) =
        ∑ i, ((4 * a ^ 2) * x i ^ 2 -
          (4 * a) * (y i * x i) + y i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold sphereAxialReflectionRaw a
      ring
    _ = (4 * a ^ 2) * (∑ i, x i ^ 2) -
        (4 * a) * (∑ i, y i * x i) + ∑ i, y i ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = 1 := by
      rw [hx', hy']
      unfold a
      ring

/-- Axial reflection through a unit axis preserves ambient dot products. -/
theorem sum_sphereAxialReflectionRaw_mul_sphereAxialReflectionRaw
    {n : ℕ} {a : Fin n → ℝ} (ha : a ∈ sphereSet n)
    (y z : Fin n → ℝ) :
    ∑ i, sphereAxialReflectionRaw a y i * sphereAxialReflectionRaw a z i =
      ∑ i, y i * z i := by
  have ha' : ∑ i, a i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using ha
  let u := ∑ j, y j * a j
  let v := ∑ j, z j * a j
  have haz : ∑ i, a i * z i = v := by
    unfold v
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    (∑ i, sphereAxialReflectionRaw a y i * sphereAxialReflectionRaw a z i) =
        ∑ i, ((4 * u * v) * a i ^ 2 - (2 * u) * (a i * z i) -
          (2 * v) * (y i * a i) + y i * z i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold sphereAxialReflectionRaw u v
      ring
    _ = (4 * u * v) * (∑ i, a i ^ 2) -
          (2 * u) * (∑ i, a i * z i) -
          (2 * v) * (∑ i, y i * a i) + ∑ i, y i * z i := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = ∑ i, y i * z i := by
      rw [ha', haz]
      unfold u v
      ring
/-- The axial reflection as a self-map of the exact sphere subtype used by
the spherical-SOS hierarchy. -/
def sphereAxialReflection {n : ℕ} (x : sphereSet n) : sphereSet n → sphereSet n :=
  fun y ↦ ⟨sphereAxialReflectionRaw x.1 y.1,
    sphereAxialReflectionRaw_mem_sphereSet x.2 y.2⟩

@[simp] theorem sphereAxialReflection_coe {n : ℕ} (x y : sphereSet n) :
    (sphereAxialReflection x y).1 = sphereAxialReflectionRaw x.1 y.1 := rfl

/-- Reflecting twice through the same axis is the identity. -/
theorem sphereAxialReflection_involutive {n : ℕ} (x : sphereSet n) :
    Function.Involutive (sphereAxialReflection x) := by
  intro y
  apply Subtype.ext
  ext i
  change 2 * (∑ j, sphereAxialReflectionRaw x.1 y.1 j * x.1 j) * x.1 i -
      sphereAxialReflectionRaw x.1 y.1 i = y.1 i
  rw [sum_sphereAxialReflectionRaw_mul_axis x.2 y.1]
  unfold sphereAxialReflectionRaw
  ring

/-- The axial reflection is a continuous self-map of the algebraic sphere. -/
theorem continuous_sphereAxialReflection {n : ℕ} (x : sphereSet n) :
    Continuous (sphereAxialReflection x) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun y : sphereSet n ↦
    2 * (∑ j, y.1 j * x.1 j) * x.1 i - y.1 i)
  have hdot : Continuous (fun y : sphereSet n ↦ ∑ j, y.1 j * x.1 j) := by
    apply continuous_finsetSum
    intro j _
    exact ((continuous_apply j).comp continuous_subtype_val).mul continuous_const
  exact ((continuous_const.mul hdot).mul continuous_const).sub
    ((continuous_apply i).comp continuous_subtype_val)

/-- An involution is bijective. -/
theorem sphereAxialReflection_bijective {n : ℕ} (x : sphereSet n) :
    Function.Bijective (sphereAxialReflection x) :=
  (sphereAxialReflection_involutive x).bijective

/-- The axial reflection packaged as a homeomorphism. -/
noncomputable def sphereAxialReflectionHomeomorph {n : ℕ} (x : sphereSet n) :
    sphereSet n ≃ₜ sphereSet n where
  toEquiv :=
    { toFun := sphereAxialReflection x
      invFun := sphereAxialReflection x
      left_inv := sphereAxialReflection_involutive x
      right_inv := sphereAxialReflection_involutive x }
  continuous_toFun := continuous_sphereAxialReflection x
  continuous_invFun := continuous_sphereAxialReflection x

theorem sphereAxialReflection_measurableEmbedding {n : ℕ} (x : sphereSet n) :
    MeasurableEmbedding (sphereAxialReflection x) :=
  (sphereAxialReflectionHomeomorph x).measurableEmbedding

/-- The ambient Euclidean linear isometry inducing axial reflection. -/
noncomputable def sphereAxialReflectionLinearIsometry {n : ℕ}
    (x : sphereSet n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ℝ ∙ (sphereSetEuclideanCoordinates x).1).reflection

/-- The ambient linear isometry has the same coordinate formula as the
repository's axial reflection. -/
theorem sphereAxialReflectionLinearIsometry_apply {n : ℕ}
    (x : sphereSet n) (y : EuclideanSpace ℝ (Fin n)) :
    sphereAxialReflectionLinearIsometry x y =
      (EuclideanSpace.equiv (Fin n) ℝ).symm
        (sphereAxialReflectionRaw x.1
          ((EuclideanSpace.equiv (Fin n) ℝ) y)) := by
  apply (EuclideanSpace.equiv (Fin n) ℝ).injective
  ext i
  rw [sphereAxialReflectionLinearIsometry,
    Submodule.reflection_singleton_apply]
  have hxnorm : ‖(sphereSetEuclideanCoordinates x).1‖ = 1 := by
    simp
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hxnorm,
    RCLike.ofReal_real_eq_id, id_eq, one_pow, div_one, PiLp.continuousLinearEquiv_apply,
    PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, mul_comm, nsmul_eq_mul, Nat.cast_ofNat,
    sphereAxialReflectionRaw, sub_left_inj]
  change 2 * (x.1 i * ∑ j, y j * x.1 j) =
    x.1 i * (2 * ∑ j, x.1 j * y j)
  have hsum : (∑ j, y j * x.1 j) = ∑ j, x.1 j * y j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

/-- The ambient linear isometry restricts to a self-map of the Euclidean unit sphere. -/
noncomputable def euclideanSphereAxialReflection {n : ℕ}
    (x : sphereSet n) : euclideanUnitSphere n → euclideanUnitSphere n :=
  euclideanUnitSphereMap (sphereAxialReflectionLinearIsometry x)

/-- The induced Euclidean-sphere reflection is involutive. -/
theorem euclideanSphereAxialReflection_involutive {n : ℕ}
    (x : sphereSet n) :
    Function.Involutive (euclideanSphereAxialReflection x) := by
  intro y
  apply Subtype.ext
  change sphereAxialReflectionLinearIsometry x
      (sphereAxialReflectionLinearIsometry x y.1) = y.1
  exact (ℝ ∙ (sphereSetEuclideanCoordinates x).1).reflection_reflection y.1

/-- The induced Euclidean-sphere reflection as a homeomorphism. -/
noncomputable def euclideanSphereAxialReflectionHomeomorph {n : ℕ}
    (x : sphereSet n) : euclideanUnitSphere n ≃ₜ euclideanUnitSphere n :=
  euclideanUnitSphereMapHomeomorph (sphereAxialReflectionLinearIsometry x)

/-- Coordinate transport intertwines the Euclidean and algebraic reflections. -/
theorem euclideanSphereAxialReflection_commutes {n : ℕ}
    (x : sphereSet n) (y : euclideanUnitSphere n) :
    euclideanSphereHomeomorphSphereSet n
        (euclideanSphereAxialReflection x y) =
      sphereAxialReflection x (euclideanSphereHomeomorphSphereSet n y) := by
  apply Subtype.ext
  ext i
  change (sphereAxialReflectionLinearIsometry x y.1) i =
    sphereAxialReflectionRaw x.1 (euclideanSphereCoordinates y) i
  rw [sphereAxialReflectionLinearIsometry_apply]
  rfl

/-- Ambient volume invariance and radial-cone equivariance imply invariance of
`Measure.toSphere` under the induced Euclidean reflection. -/
theorem euclideanSphereAxialReflection_measurePreserving_toSphere {n : ℕ}
    (x : sphereSet n) :
    MeasurePreserving (euclideanSphereAxialReflection x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  exact euclideanUnitSphereMap_measurePreserving_toSphere
    (sphereAxialReflectionLinearIsometry x)

/-- Normalization of Haar surface measure preserves reflection invariance. -/
theorem euclideanSphereAxialReflection_measurePreserving {n : ℕ}
    (x : sphereSet n) :
    MeasurePreserving (euclideanSphereAxialReflection x)
      (normalizedEuclideanSphereMeasure n)
      (normalizedEuclideanSphereMeasure n) := by
  exact euclideanUnitSphereMap_measurePreserving
    (sphereAxialReflectionLinearIsometry x)

/-- Normalized Haar surface measure is invariant under axial reflection.

The proof uses ambient linear-isometry invariance of volume, radial cones, and
transport through `euclideanSphereHomeomorphSphereSet`. -/
theorem sphereAxialReflection_measurePreserving {n : ℕ} (x : sphereSet n) :
    MeasurePreserving (sphereAxialReflection x)
      (normalizedSphereMeasure n) (normalizedSphereMeasure n) := by
  have h :=
    sphereSetLinearIsometry_measurePreserving
      (sphereAxialReflectionLinearIsometry x)
  have hmaps :
      (sphereSetLinearIsometryHomeomorph
          (sphereAxialReflectionLinearIsometry x) :
        sphereSet n → sphereSet n) = sphereAxialReflection x := by
    funext y
    change (euclideanSphereHomeomorphSphereSet n)
        (euclideanUnitSphereMap (sphereAxialReflectionLinearIsometry x)
          ((euclideanSphereHomeomorphSphereSet n).symm y)) =
      sphereAxialReflection x y
    exact euclideanSphereAxialReflection_commutes x
      ((euclideanSphereHomeomorphSphereSet n).symm y)
  rw [hmaps] at h
  exact h
/-- A unit axis perpendicular to a given sphere point exists in dimension at
least two. This is the only geometric input needed for the antipodal case. -/
theorem exists_sphereAxis_dot_eq_zero {n : ℕ} (hn : 2 ≤ n)
    (x : sphereSet n) :
    ∃ a : sphereSet n, ∑ i, x.1 i * a.1 i = 0 := by
  classical
  have hxnorm : ∑ i, x.1 i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2
  obtain ⟨i, hi⟩ : ∃ i, x.1 i ≠ 0 := by
    by_contra h
    push Not at h
    have hsum : ∑ i, x.1 i ^ 2 = 0 := by simp [h]
    linarith
  have hcard : 1 < Fintype.card (Fin n) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  let b : Fin n → ℝ := fun k ↦
    if k = i then x.1 j else if k = j then -x.1 i else 0
  have hbjne : b j ≠ 0 := by
    simp only [b, ite_eq_right hji, ite_eq_left, neg_ne_zero]
    exact hi
  have hdotb : ∑ k, x.1 k * b k = 0 := by
    have hbexpand (k : Fin n) :
        x.1 k * b k =
          (if k = i then x.1 k * x.1 j else 0) +
            (if k = j then -(x.1 k * x.1 i) else 0) := by
      by_cases hki : k = i
      · simp [b, hki, Ne.symm hji]
      · by_cases hkj : k = j
        · simp [b, hkj, hji]
        · simp [b, hki, hkj]
    rw [show (∑ k, x.1 k * b k) =
        ∑ k, ((if k = i then x.1 k * x.1 j else 0) +
          (if k = j then -(x.1 k * x.1 i) else 0)) by
      apply Finset.sum_congr rfl
      intro k _
      exact hbexpand k]
    rw [Finset.sum_add_distrib, Fintype.sum_ite_eq',
      Fintype.sum_ite_eq']
    ring
  let q : ℝ := ∑ k, b k ^ 2
  have hqpos : 0 < q := by
    have hterm : 0 < b j ^ 2 := sq_pos_of_ne_zero hbjne
    have hle : b j ^ 2 ≤ ∑ k, b k ^ 2 :=
      Finset.single_le_sum (fun k _ ↦ sq_nonneg (b k)) (Finset.mem_univ j)
    exact lt_of_lt_of_le hterm hle
  let a0 : Fin n → ℝ := fun k ↦ b k / Real.sqrt q
  have ha0 : a0 ∈ sphereSet n := by
    simp only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X, mem_ofPred_eq]
    calc
      (∑ k, a0 k ^ 2) = (∑ k, b k ^ 2) / (Real.sqrt q) ^ 2 := by
        simp_rw [a0, div_pow, Finset.sum_div]
      _ = 1 := by
        rw [show (∑ k, b k ^ 2) = q by rfl, Real.sq_sqrt hqpos.le,
          div_self hqpos.ne']
  refine ⟨⟨a0, ha0⟩, ?_⟩
  change (∑ k, x.1 k * (b k / Real.sqrt q)) = 0
  rw [show (∑ k, x.1 k * (b k / Real.sqrt q)) =
    (∑ k, x.1 k * b k) / Real.sqrt q by
      simp_rw [mul_div, Finset.sum_div]]
  rw [hdotb, zero_div]

/-- If two unit vectors are not antipodal, reflection through their normalized
sum sends the first to the second. -/
theorem exists_sphereAxialReflection_eq_of_add_ne_zero {n : ℕ}
    (x z : sphereSet n) (hadd : x.1 + z.1 ≠ 0) :
    ∃ a : sphereSet n, sphereAxialReflection a x = z := by
  let s : Fin n → ℝ := fun i ↦ x.1 i + z.1 i
  let q : ℝ := ∑ i, s i ^ 2
  have hs : s ≠ 0 := by
    intro hs0
    apply hadd
    ext i
    have hi := congrFun hs0 i
    simpa [s] using hi
  obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
    by_contra h
    push Not at h
    exact hs (funext h)
  have hqpos : 0 < q := by
    have hterm : 0 < s i ^ 2 := sq_pos_of_ne_zero hi
    have hle : s i ^ 2 ≤ ∑ j, s j ^ 2 :=
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (s j)) (Finset.mem_univ i)
    exact lt_of_lt_of_le hterm hle
  have hxnorm : ∑ i, x.1 i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2
  have hznorm : ∑ i, z.1 i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using z.2
  let d : ℝ := ∑ i, x.1 i * z.1 i
  have hq : q = 2 * (1 + d) := by
    calc
      q = ∑ i, (x.1 i ^ 2 + 2 * (x.1 i * z.1 i) + z.1 i ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        unfold s
        ring
      _ = (∑ i, x.1 i ^ 2) + 2 * (∑ i, x.1 i * z.1 i) +
          ∑ i, z.1 i ^ 2 := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 2 * (1 + d) := by
        rw [hxnorm, hznorm]
        unfold d
        ring
  have hdotnum : ∑ i, x.1 i * s i = 1 + d := by
    calc
      (∑ i, x.1 i * s i) =
          (∑ i, x.1 i ^ 2) + ∑ i, x.1 i * z.1 i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        unfold s
        ring
      _ = 1 + d := by rw [hxnorm]
  let a0 : Fin n → ℝ := fun i ↦ s i / Real.sqrt q
  have hsqrt_ne : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hqpos)
  have hsqrt_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hqpos.le
  have ha0 : a0 ∈ sphereSet n := by
    simp only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X, mem_ofPred_eq]
    calc
      (∑ i, a0 i ^ 2) = (∑ i, s i ^ 2) / (Real.sqrt q) ^ 2 := by
        simp_rw [a0, div_pow, Finset.sum_div]
      _ = 1 := by
        rw [show (∑ i, s i ^ 2) = q by rfl, hsqrt_sq, div_self hqpos.ne']
  let a : sphereSet n := ⟨a0, ha0⟩
  have hdot : ∑ i, x.1 i * a.1 i = (1 + d) / Real.sqrt q := by
    change (∑ i, x.1 i * (s i / Real.sqrt q)) = _
    rw [show (∑ i, x.1 i * (s i / Real.sqrt q)) =
      (∑ i, x.1 i * s i) / Real.sqrt q by
        simp_rw [mul_div, Finset.sum_div]]
    rw [hdotnum]
  refine ⟨a, ?_⟩
  apply Subtype.ext
  ext j
  change 2 * (∑ i, x.1 i * a.1 i) * a.1 j - x.1 j = z.1 j
  rw [hdot]
  change 2 * ((1 + d) / Real.sqrt q) *
      (s j / Real.sqrt q) - x.1 j = z.1 j
  field_simp
  rw [show s j = x.1 j + z.1 j by rfl]
  rw [hsqrt_sq, hq]
  ring
/-- In dimension at least two, one axial reflection sends any unit vector to
any other. The non-antipodal axis is the normalized sum; in the antipodal case
one chooses a unit vector perpendicular to the source. -/
theorem exists_sphereAxialReflection_eq {n : ℕ} (hn : 2 ≤ n)
    (x z : sphereSet n) :
    ∃ a : sphereSet n, sphereAxialReflection a x = z := by
  by_cases hadd : x.1 + z.1 = 0
  · obtain ⟨a, ha⟩ := exists_sphereAxis_dot_eq_zero hn x
    refine ⟨a, ?_⟩
    apply Subtype.ext
    ext i
    have hzi := congrFun hadd i
    change 2 * (∑ j, x.1 j * a.1 j) * a.1 i - x.1 i = z.1 i
    rw [ha]
    ring_nf
    change x.1 i + z.1 i = 0 at hzi
    linarith
  · exact exists_sphereAxialReflection_eq_of_add_ne_zero x z hadd
/-- Axial reflection leaves every zonal kernel section based at its axis
unchanged. -/
theorem eval_sphereDirichletZonalKernel_sphereAxialReflection {n : ℕ}
    (p k : ℕ) (x y : sphereSet n) :
    MvPolynomial.eval (sphereAxialReflection x y).1
        (sphereDirichletZonalKernel p k x.1) =
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) := by
  rw [eval_sphereDirichletZonalKernel, eval_sphereDirichletZonalKernel]
  congr 2
  calc
    (∑ i, (x.1 i * (sphereAxialReflection x y).1 i)) =
        ∑ i, (sphereAxialReflectionRaw x.1 y.1 i * x.1 i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [sphereAxialReflection_coe]
      ring
    _ = ∑ i, y.1 i * x.1 i :=
      sum_sphereAxialReflectionRaw_mul_axis x.2 y.1
    _ = ∑ i, x.1 i * y.1 i := by
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Applying the same axial reflection to the kernel center and evaluation
point leaves a zonal kernel unchanged. -/
theorem eval_sphereDirichletZonalKernel_map_sphereAxialReflection
    {n : ℕ} (p k : ℕ) (a x y : sphereSet n) :
    MvPolynomial.eval (sphereAxialReflection a y).1
        (sphereDirichletZonalKernel p k (sphereAxialReflection a x).1) =
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1) := by
  rw [eval_sphereDirichletZonalKernel, eval_sphereDirichletZonalKernel]
  congr 2
  change (∑ i, sphereAxialReflectionRaw a.1 x.1 i *
      sphereAxialReflectionRaw a.1 y.1 i) = ∑ i, x.1 i * y.1 i
  exact sum_sphereAxialReflectionRaw_mul_sphereAxialReflectionRaw a.2 x.1 y.1
end QuarticConvergence
end OptimalConvergenceRates
