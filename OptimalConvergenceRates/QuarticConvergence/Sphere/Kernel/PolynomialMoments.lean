/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/PolynomialMoments.lean

  Polynomial-moment replacement for Funk--Hecke filtration preservation.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Quadrature
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Reflection
open Set MeasureTheory MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-- If every coefficient of two polynomials with multivariate-polynomial
coefficients has total degree bounded by its index, the same holds for their
product. -/
theorem totalDegree_coeff_mul_le_index {n : ℕ}
    (P Q : Polynomial (MvPolynomial (Fin n) ℝ))
    (hP : ∀ d, (P.coeff d).totalDegree ≤ d)
    (hQ : ∀ d, (Q.coeff d).totalDegree ≤ d) (d : ℕ) :
    ((P * Q).coeff d).totalDegree ≤ d := by
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij hij
  calc
    (P.coeff ij.1 * Q.coeff ij.2).totalDegree ≤
        (P.coeff ij.1).totalDegree + (Q.coeff ij.2).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ ij.1 + ij.2 := Nat.add_le_add (hP ij.1) (hQ ij.2)
    _ = d := Finset.mem_antidiagonal.mp hij

/-- Coefficientwise degree bounded by the coefficient index is stable under
taking powers. -/
theorem totalDegree_coeff_pow_le_index {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ))
    (hP : ∀ d, (P.coeff d).totalDegree ≤ d) :
    ∀ q d, ((P ^ q).coeff d).totalDegree ≤ d := by
  intro q
  induction q with
  | zero =>
      intro d
      cases d <;> simp [Polynomial.coeff_one]
  | succ q ih =>
      intro d
      rw [pow_succ]
      exact totalDegree_coeff_mul_le_index (P ^ q) P ih hP d
namespace QuarticConvergence

open SphereBallTransfers
/-- The moment of a power of a linear form against normalized sphere
measure. This is the basic scalar moment used to prove filtration preservation. -/
noncomputable def sphereLinearFormMoment {n : ℕ}
    (m : ℕ) (z : Fin n → ℝ) : ℝ :=
  ∫ y : sphereSet n, (∑ i, z i * y.1 i) ^ m ∂normalizedSphereMeasure n

/-- The coordinate action induced by a Euclidean linear isometry. -/
noncomputable def sphereLinearIsometryCoordinates {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (z : Fin n → ℝ) : Fin n → ℝ :=
  (EuclideanSpace.equiv (Fin n) ℝ)
    (L ((EuclideanSpace.equiv (Fin n) ℝ).symm z))

@[simp] theorem sphereSetLinearIsometryHomeomorph_coe {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (y : sphereSet n) :
    (sphereSetLinearIsometryHomeomorph L y).1 =
      sphereLinearIsometryCoordinates L y.1 := by
  rfl

/-- The coordinate action of a Euclidean linear isometry preserves the
standard dot product. -/
theorem sphereLinearIsometryCoordinates_dot {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (z y : Fin n → ℝ) :
    (∑ i, sphereLinearIsometryCoordinates L z i *
      sphereLinearIsometryCoordinates L y i) = ∑ i, z i * y i := by
  have h := L.inner_map_map
    ((EuclideanSpace.equiv (Fin n) ℝ).symm z)
    ((EuclideanSpace.equiv (Fin n) ℝ).symm y)
  rw [PiLp.inner_apply, PiLp.inner_apply] at h
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial] at h
  change (∑ i, (L ((EuclideanSpace.equiv (Fin n) ℝ).symm z)).ofLp i *
    (L ((EuclideanSpace.equiv (Fin n) ℝ).symm y)).ofLp i) =
      ∑ i, ((EuclideanSpace.equiv (Fin n) ℝ).symm z).ofLp i *
        ((EuclideanSpace.equiv (Fin n) ℝ).symm y).ofLp i
  simpa only [mul_comm] using h

/-- Linear-form moments depend only on the orthogonal orbit of their
coefficient vector. -/
theorem sphereLinearFormMoment_linearIsometry {n m : ℕ}
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (z : Fin n → ℝ) :
    sphereLinearFormMoment m (sphereLinearIsometryCoordinates L z) =
      sphereLinearFormMoment m z := by
  let R : sphereSet n ≃ₜ sphereSet n :=
    sphereSetLinearIsometryHomeomorph L
  let f : sphereSet n → ℝ := fun y ↦
    (∑ i, sphereLinearIsometryCoordinates L z i * y.1 i) ^ m
  have hchange :
      (∫ y : sphereSet n, f (R y) ∂normalizedSphereMeasure n) =
        ∫ y : sphereSet n, f y ∂normalizedSphereMeasure n := by
    exact (sphereSetLinearIsometry_measurePreserving L).integral_comp
      R.measurableEmbedding f
  unfold sphereLinearFormMoment
  change (∫ y : sphereSet n, f y ∂normalizedSphereMeasure n) =
    ∫ y : sphereSet n, (∑ i, z i * y.1 i) ^ m
      ∂normalizedSphereMeasure n
  rw [← hchange]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only [f, R]
  rw [sphereSetLinearIsometryHomeomorph_coe,
    sphereLinearIsometryCoordinates_dot]
/-- In dimension at least two, all unit coefficient vectors have the same
linear-form moments. This is the unit-radius part of the radial-moment
argument. -/
theorem sphereLinearFormMoment_eq_on_sphere {n m : ℕ} (hn : 2 ≤ n)
    (x z : sphereSet n) :
    sphereLinearFormMoment m z.1 = sphereLinearFormMoment m x.1 := by
  obtain ⟨a, ha⟩ := exists_sphereAxialReflection_eq hn x z
  let L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    sphereAxialReflectionLinearIsometry a
  have hcoord :
      sphereLinearIsometryCoordinates L x.1 = z.1 := by
    rw [← ha]
    ext i
    change (L ((EuclideanSpace.equiv (Fin n) ℝ).symm x.1)) i =
      (sphereAxialReflection a x).1 i
    rw [sphereAxialReflectionLinearIsometry_apply]
    rfl
  rw [← hcoord]
  exact sphereLinearFormMoment_linearIsometry L x.1
/-- Powers of linear forms are integrable against normalized sphere measure
in positive ambient dimension. -/
theorem integrable_sphereLinearForm_pow {n : ℕ} (hn : 0 < n)
    (m : ℕ) (z : Fin n → ℝ) :
    Integrable (fun y : sphereSet n ↦ (∑ i, z i * y.1 i) ^ m)
      (normalizedSphereMeasure n) := by
  have h := integrable_eval_normalizedSphereMeasure hn
    ((sphereDotPolynomial z) ^ m)
  simpa only [map_pow, eval_sphereDotPolynomial] using h

/-- Linear-form moments are homogeneous in their coefficient vector. -/
theorem sphereLinearFormMoment_smul {n m : ℕ}
    (a : ℝ) (z : Fin n → ℝ) :
    sphereLinearFormMoment m (a • z) =
      a ^ m * sphereLinearFormMoment m z := by
  unfold sphereLinearFormMoment
  calc
    (∫ y : sphereSet n, (∑ i, (a • z) i * y.1 i) ^ m
        ∂normalizedSphereMeasure n) =
        ∫ y : sphereSet n, a ^ m * (∑ i, z i * y.1 i) ^ m
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      have hsum : (∑ i, (a • z) i * y.1 i) =
          a * ∑ i, z i * y.1 i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [mul_assoc]
      change (∑ i, (a • z) i * y.1 i) ^ m =
        a ^ m * (∑ i, z i * y.1 i) ^ m
      rw [hsum, mul_pow]
    _ = a ^ m * ∫ y : sphereSet n, (∑ i, z i * y.1 i) ^ m
          ∂normalizedSphereMeasure n := by
      exact integral_const_mul (a ^ m)
        (fun y : sphereSet n ↦ (∑ i, z i * y.1 i) ^ m)
/-- The radial-moment formula on a ray: scaling a unit coefficient vector
only contributes the corresponding scalar power. -/
theorem sphereLinearFormMoment_smul_sphere {n m : ℕ} (hn : 2 ≤ n)
    (a : ℝ) (x z : sphereSet n) :
    sphereLinearFormMoment m (a • z.1) =
      a ^ m * sphereLinearFormMoment m x.1 := by
  rw [sphereLinearFormMoment_smul]
  rw [sphereLinearFormMoment_eq_on_sphere hn x z]
/-- Squared Euclidean norm in the repository's algebraic coordinates. -/
def sphereCoefficientNormSq {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  ∑ i, z i ^ 2

theorem sphereCoefficientNormSq_pos {n : ℕ} {z : Fin n → ℝ} (hz : z ≠ 0) :
    0 < sphereCoefficientNormSq z := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  have hterm : 0 < z i ^ 2 := sq_pos_of_ne_zero hi
  have hle : z i ^ 2 ≤ ∑ j, z j ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le hterm hle

/-- Normalize a nonzero coefficient vector using its coordinate sum of
squares. -/
noncomputable def normalizedSphereCoefficient {n : ℕ}
    (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ z i / Real.sqrt (sphereCoefficientNormSq z)

/-- A nonzero normalized coefficient vector belongs to the exact algebraic
sphere used by the SOS hierarchy. -/
theorem normalizedSphereCoefficient_mem {n : ℕ} {z : Fin n → ℝ}
    (hz : z ≠ 0) :
    normalizedSphereCoefficient z ∈ sphereSet n := by
  have hqpos : 0 < sphereCoefficientNormSq z :=
    sphereCoefficientNormSq_pos hz
  simp only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X,
    Set.mem_ofPred_eq]
  calc
    (∑ i, normalizedSphereCoefficient z i ^ 2) =
        (∑ i, z i ^ 2) / (Real.sqrt (sphereCoefficientNormSq z)) ^ 2 := by
      simp_rw [normalizedSphereCoefficient, div_pow, Finset.sum_div]
    _ = 1 := by
      rw [show (∑ i, z i ^ 2) = sphereCoefficientNormSq z by rfl,
        Real.sq_sqrt hqpos.le, div_self hqpos.ne']

/-- Reconstruct a nonzero coefficient vector from its normalized sphere
point and radial scalar. -/
theorem sqrt_sphereCoefficientNormSq_smul_normalized {n : ℕ}
    {z : Fin n → ℝ} (hz : z ≠ 0) :
    Real.sqrt (sphereCoefficientNormSq z) • normalizedSphereCoefficient z = z := by
  have hsqrt : Real.sqrt (sphereCoefficientNormSq z) ≠ 0 :=
    (Real.sqrt_pos.2 (sphereCoefficientNormSq_pos hz)).ne'
  ext i
  change Real.sqrt (sphereCoefficientNormSq z) *
    (z i / Real.sqrt (sphereCoefficientNormSq z)) = z i
  field_simp

/-- Even linear-form moments are radial homogeneous polynomials. The
constant is the moment at any chosen unit coefficient vector. -/
theorem sphereLinearFormMoment_even_radial {n q : ℕ} (hn : 2 ≤ n)
    (base : sphereSet n) (z : Fin n → ℝ) :
    sphereLinearFormMoment (2 * q) z =
      sphereLinearFormMoment (2 * q) base.1 *
        sphereCoefficientNormSq z ^ q := by
  by_cases hz : z = 0
  · subst z
    have hzero : (0 : Fin n → ℝ) = (0 : ℝ) • base.1 := by
      simp
    rw [hzero, sphereLinearFormMoment_smul_sphere hn 0 base base]
    by_cases hq : q = 0
    · subst q
      simp [sphereCoefficientNormSq]
    · simp [sphereCoefficientNormSq, hq]
  · let u : sphereSet n :=
      ⟨normalizedSphereCoefficient z, normalizedSphereCoefficient_mem hz⟩
    calc
      sphereLinearFormMoment (2 * q) z =
          sphereLinearFormMoment (2 * q)
            (Real.sqrt (sphereCoefficientNormSq z) • u.1) := by
        change sphereLinearFormMoment (2 * q) z =
          sphereLinearFormMoment (2 * q)
            (Real.sqrt (sphereCoefficientNormSq z) • normalizedSphereCoefficient z)
        rw [sqrt_sphereCoefficientNormSq_smul_normalized hz]
      _ = Real.sqrt (sphereCoefficientNormSq z) ^ (2 * q) *
          sphereLinearFormMoment (2 * q) base.1 :=
        sphereLinearFormMoment_smul_sphere hn _ base u
      _ = sphereLinearFormMoment (2 * q) base.1 *
          sphereCoefficientNormSq z ^ q := by
        rw [pow_mul, Real.sq_sqrt (sphereCoefficientNormSq_pos hz).le]
        ring

/-- The squared norm of x + t z as an explicit quadratic polynomial in t. -/
noncomputable def sphereCoefficientNormSqLinePolynomial {n : ℕ}
    (x z : Fin n → ℝ) : Polynomial ℝ :=
  Polynomial.C (sphereCoefficientNormSq x) +
    Polynomial.C (2 * ∑ i, x i * z i) * Polynomial.X +
    Polynomial.C (sphereCoefficientNormSq z) * Polynomial.X ^ 2

@[simp] theorem sphereCoefficientNormSqLinePolynomial_eval {n : ℕ}
    (x z : Fin n → ℝ) (t : ℝ) :
    (sphereCoefficientNormSqLinePolynomial x z).eval t =
      sphereCoefficientNormSq (x + t • z) := by
  simp only [sphereCoefficientNormSqLinePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  unfold sphereCoefficientNormSq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  symm
  calc
    (∑ i, (x i + t * z i) ^ 2) =
        ∑ i, (x i ^ 2 + 2 * t * (x i * z i) + t ^ 2 * z i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i, x i ^ 2) + 2 * (∑ i, x i * z i) * t +
        (∑ i, z i ^ 2) * t ^ 2 := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- The squared norm of `x + t z`, after using the sphere relation
`∑ i, x i ^ 2 = 1`, as a polynomial in `t` whose coefficients are
multivariate polynomials in `x`. -/
noncomputable def sphereCoefficientNormSqLinePolynomialOnSphere {n : ℕ}
    (z : Fin n → ℝ) : Polynomial (MvPolynomial (Fin n) ℝ) :=
  Polynomial.C 1 +
    Polynomial.C (2 • sphereDotPolynomial z) * Polynomial.X +
    Polynomial.C (MvPolynomial.C (sphereCoefficientNormSq z)) *
      Polynomial.X ^ 2

/-- In the sphere-reduced squared-norm line polynomial, the coefficient of
`t^d` has ambient total degree at most `d`. -/
theorem sphereCoefficientNormSqLinePolynomialOnSphere_coeff_totalDegree_le
    {n : ℕ} (z : Fin n → ℝ) (d : ℕ) :
    ((sphereCoefficientNormSqLinePolynomialOnSphere z).coeff d).totalDegree ≤ d := by
  rcases d with _ | d
  · simp [sphereCoefficientNormSqLinePolynomialOnSphere, Polynomial.coeff_one]
  rcases d with _ | d
  · rw [show (sphereCoefficientNormSqLinePolynomialOnSphere z).coeff 1 =
        2 • sphereDotPolynomial z by
      simp [sphereCoefficientNormSqLinePolynomialOnSphere, Polynomial.coeff_one]]
    exact (MvPolynomial.totalDegree_smul_le 2 (sphereDotPolynomial z)).trans
      (sphereDotPolynomial_totalDegree_le_one z)
  rcases d with _ | d
  · simp [sphereCoefficientNormSqLinePolynomialOnSphere, Polynomial.coeff_one]
  · simp [sphereCoefficientNormSqLinePolynomialOnSphere, Polynomial.coeff_one]

/-- The coefficient of the q-th power of the sphere-reduced radial line
polynomial, viewed as a multivariate polynomial in the sphere point. -/
noncomputable def sphereRadialMomentCoefficientPolynomial {n : ℕ}
    (q d : ℕ) (z : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ((sphereCoefficientNormSqLinePolynomialOnSphere z) ^ q).coeff d

/-- The radial coefficient polynomial has the sharp ambient degree bound
needed by filtration preservation. -/
theorem sphereRadialMomentCoefficientPolynomial_totalDegree_le {n : ℕ}
    (q d : ℕ) (z : Fin n → ℝ) :
    (sphereRadialMomentCoefficientPolynomial q d z).totalDegree ≤ d := by
  exact totalDegree_coeff_pow_le_index
    (sphereCoefficientNormSqLinePolynomialOnSphere z)
    (sphereCoefficientNormSqLinePolynomialOnSphere_coeff_totalDegree_le z) q d

/-- Membership in the repository's algebraic sphere is exactly the statement
that the coordinate squared norm is one. -/
theorem sphereCoefficientNormSq_eq_one_of_mem {n : ℕ}
    {x : Fin n → ℝ} (hx : x ∈ sphereSet n) :
    sphereCoefficientNormSq x = 1 := by
  simpa only [sphereCoefficientNormSq, sphereSet, sphereQuadratic,
    map_sum, map_pow, eval_X, Set.mem_ofPred_eq] using hx

/-- Evaluating the sphere-reduced line polynomial at a sphere point recovers
the actual squared-norm line polynomial. -/
theorem map_sphereCoefficientNormSqLinePolynomialOnSphere {n : ℕ}
    (x z : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    Polynomial.map (MvPolynomial.eval x)
        (sphereCoefficientNormSqLinePolynomialOnSphere z) =
      sphereCoefficientNormSqLinePolynomial x z := by
  have hxnorm : sphereCoefficientNormSq x = 1 :=
    sphereCoefficientNormSq_eq_one_of_mem hx
  have hdot : (∑ i, z i * x i) = ∑ i, x i * z i := by
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  simp [sphereCoefficientNormSqLinePolynomialOnSphere,
    sphereCoefficientNormSqLinePolynomial, hxnorm, hdot]

/-- On the sphere, evaluation of the radial coefficient polynomial is the
corresponding coefficient of the real radial line polynomial. -/
theorem eval_sphereRadialMomentCoefficientPolynomial {n q d : ℕ}
    (x z : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    MvPolynomial.eval x (sphereRadialMomentCoefficientPolynomial q d z) =
      (sphereCoefficientNormSqLinePolynomial x z ^ q).coeff d := by
  rw [sphereRadialMomentCoefficientPolynomial]
  rw [← Polynomial.coeff_map]
  rw [Polynomial.map_pow,
    map_sphereCoefficientNormSqLinePolynomialOnSphere x z hx]

/-- A mixed moment of two powers of linear forms. -/
noncomputable def mixedSphereLinearFormMoment {n : ℕ}
    (a b : ℕ) (x z : Fin n → ℝ) : ℝ :=
  ∫ y : sphereSet n,
    (∑ i, x i * y.1 i) ^ a * (∑ i, z i * y.1 i) ^ b
      ∂normalizedSphereMeasure n

/-- Mixed linear-form moments are integrable in positive dimension. -/
theorem integrable_mixedSphereLinearFormMoment {n : ℕ} (hn : 0 < n)
    (a b : ℕ) (x z : Fin n → ℝ) :
    Integrable (fun y : sphereSet n ↦
      (∑ i, x i * y.1 i) ^ a * (∑ i, z i * y.1 i) ^ b)
      (normalizedSphereMeasure n) := by
  have h := integrable_eval_normalizedSphereMeasure hn
    ((sphereDotPolynomial x) ^ a * (sphereDotPolynomial z) ^ b)
  simpa only [map_mul, map_pow, eval_sphereDotPolynomial] using h

/-- The auxiliary polynomial whose coefficients are the mixed moments in the
binomial expansion along a line. -/
noncomputable def sphereMomentLinePolynomial {n : ℕ}
    (m : ℕ) (x z : Fin n → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    Polynomial.C ((Nat.choose m j : ℝ) *
      mixedSphereLinearFormMoment (m - j) j x z) * Polynomial.X ^ j

/-- Coefficient extraction from the auxiliary moment polynomial. -/
theorem sphereMomentLinePolynomial_coeff {n m j : ℕ}
    (x z : Fin n → ℝ) (hj : j ≤ m) :
    (sphereMomentLinePolynomial m x z).coeff j =
      (Nat.choose m j : ℝ) *
        mixedSphereLinearFormMoment (m - j) j x z := by
  classical
  rw [sphereMomentLinePolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j, Polynomial.coeff_C_mul_X_pow,
    ite_eq_left rfl]
  · intro b hb hbj
    rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right hbj.symm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))).elim

/-- Evaluating the auxiliary polynomial gives the linear-form moment along
the affine line through its coefficient vectors. -/
theorem sphereMomentLinePolynomial_eval {n m : ℕ} (hn : 0 < n)
    (x z : Fin n → ℝ) (t : ℝ) :
    (sphereMomentLinePolynomial m x z).eval t =
      sphereLinearFormMoment m (x + t • z) := by
  rw [sphereMomentLinePolynomial]
  unfold sphereLinearFormMoment
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  calc
    (∑ j ∈ Finset.range (m + 1),
        ((Nat.choose m j : ℝ) * mixedSphereLinearFormMoment (m - j) j x z) *
          t ^ j) =
        ∑ j ∈ Finset.range (m + 1),
          ∫ y : sphereSet n,
            ((Nat.choose m j : ℝ) * t ^ j) *
              ((∑ i, x i * y.1 i) ^ (m - j) *
                (∑ i, z i * y.1 i) ^ j)
              ∂normalizedSphereMeasure n := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [mixedSphereLinearFormMoment, integral_const_mul]
      ring
    _ = ∫ y : sphereSet n,
        ∑ j ∈ Finset.range (m + 1),
          ((Nat.choose m j : ℝ) * t ^ j) *
            ((∑ i, x i * y.1 i) ^ (m - j) *
              (∑ i, z i * y.1 i) ^ j)
          ∂normalizedSphereMeasure n := by
      rw [integral_finsetSum]
      intro j _hj
      exact (integrable_mixedSphereLinearFormMoment hn
        (m - j) j x z).const_mul _
    _ = ∫ y : sphereSet n,
        (∑ i, (x + t • z) i * y.1 i) ^ m
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      have hdot :
          (∑ i, (x + t • z) i * y.1 i) =
            (∑ i, x i * y.1 i) + t * (∑ i, z i * y.1 i) := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc
          (∑ i, (x i + t * z i) * y.1 i) =
              ∑ i, (x i * y.1 i + t * (z i * y.1 i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          _ = (∑ i, x i * y.1 i) + t * (∑ i, z i * y.1 i) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      change (∑ j ∈ Finset.range (m + 1),
        ((Nat.choose m j : ℝ) * t ^ j) *
          ((∑ i, x i * y.1 i) ^ (m - j) *
            (∑ i, z i * y.1 i) ^ j)) =
        (∑ i, (x + t • z) i * y.1 i) ^ m
      rw [hdot]
      rw [show (∑ i, x i * y.1 i) + t * (∑ i, z i * y.1 i) =
        t * (∑ i, z i * y.1 i) + (∑ i, x i * y.1 i) by ring]
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
/-- The even auxiliary moment polynomial is a scalar multiple of the q-th
power of the squared-norm quadratic. -/
theorem sphereMomentLinePolynomial_even_eq {n q : ℕ} (hn : 2 ≤ n)
    (base : sphereSet n) (x z : Fin n → ℝ) :
    sphereMomentLinePolynomial (2 * q) x z =
      Polynomial.C (sphereLinearFormMoment (2 * q) base.1) *
        sphereCoefficientNormSqLinePolynomial x z ^ q := by
  apply Polynomial.funext
  intro t
  rw [sphereMomentLinePolynomial_eval (by omega)]
  rw [sphereLinearFormMoment_even_radial hn base]
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    sphereCoefficientNormSqLinePolynomial_eval]
/-- Coefficient extraction expresses a mixed moment through the corresponding
coefficient of the radial quadratic power. -/
theorem choose_mul_mixedSphereLinearFormMoment_eq_coeff {n q d : ℕ}
    (hn : 2 ≤ n) (base : sphereSet n) (x z : Fin n → ℝ)
    (hd : d ≤ 2 * q) :
    (Nat.choose (2 * q) d : ℝ) *
        mixedSphereLinearFormMoment (2 * q - d) d x z =
      sphereLinearFormMoment (2 * q) base.1 *
        (sphereCoefficientNormSqLinePolynomial x z ^ q).coeff d := by
  rw [← sphereMomentLinePolynomial_coeff x z hd]
  rw [sphereMomentLinePolynomial_even_eq hn base]
  rw [Polynomial.coeff_C_mul]

/-- An explicit ambient polynomial representing an even mixed sphere moment.
The inverse binomial coefficient is harmless when `d ≤ 2q`. -/
noncomputable def evenMixedSphereLinearFormMomentPolynomial {n : ℕ}
    (q d : ℕ) (base : sphereSet n) (z : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C
      ((Nat.choose (2 * q) d : ℝ)⁻¹ *
        sphereLinearFormMoment (2 * q) base.1) *
    sphereRadialMomentCoefficientPolynomial q d z

/-- The explicit even mixed-moment representative has degree at most its
degree in the variable sphere point. -/
theorem evenMixedSphereLinearFormMomentPolynomial_totalDegree_le {n : ℕ}
    (q d : ℕ) (base : sphereSet n) (z : Fin n → ℝ) :
    (evenMixedSphereLinearFormMomentPolynomial q d base z).totalDegree ≤ d := by
  unfold evenMixedSphereLinearFormMomentPolynomial
  calc
    (MvPolynomial.C
          ((Nat.choose (2 * q) d : ℝ)⁻¹ *
            sphereLinearFormMoment (2 * q) base.1) *
        sphereRadialMomentCoefficientPolynomial q d z).totalDegree ≤
        (MvPolynomial.C
          ((Nat.choose (2 * q) d : ℝ)⁻¹ *
            sphereLinearFormMoment (2 * q) base.1)).totalDegree +
          (sphereRadialMomentCoefficientPolynomial q d z).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + d := Nat.add_le_add
      (le_of_eq (MvPolynomial.totalDegree_C _))
      (sphereRadialMomentCoefficientPolynomial_totalDegree_le q d z)
    _ = d := Nat.zero_add d

/-- On the sphere, the explicit representative evaluates to the mixed
moment with complementary exponent `2q-d`. -/
theorem eval_evenMixedSphereLinearFormMomentPolynomial {n q d : ℕ}
    (hn : 2 ≤ n) (base : sphereSet n) (z x : Fin n → ℝ)
    (hd : d ≤ 2 * q) (hx : x ∈ sphereSet n) :
    MvPolynomial.eval x
        (evenMixedSphereLinearFormMomentPolynomial q d base z) =
      mixedSphereLinearFormMoment (2 * q - d) d x z := by
  have hchooseNat : 0 < Nat.choose (2 * q) d := Nat.choose_pos hd
  have hchoose : (Nat.choose (2 * q) d : ℝ) ≠ 0 := by
    exact_mod_cast hchooseNat.ne'
  rw [evenMixedSphereLinearFormMomentPolynomial, map_mul, eval_C,
    eval_sphereRadialMomentCoefficientPolynomial x z hx]
  have hcoeff := choose_mul_mixedSphereLinearFormMoment_eq_coeff
    hn base x z hd
  calc
    (Nat.choose (2 * q) d : ℝ)⁻¹ *
          sphereLinearFormMoment (2 * q) base.1 *
        (sphereCoefficientNormSqLinePolynomial x z ^ q).coeff d =
        (Nat.choose (2 * q) d : ℝ)⁻¹ *
          ((Nat.choose (2 * q) d : ℝ) *
            mixedSphereLinearFormMoment (2 * q - d) d x z) := by
      rw [mul_assoc, ← hcoeff]
    _ = mixedSphereLinearFormMoment (2 * q - d) d x z := by
      field_simp

/-- Antipodal invariance forces every odd linear-form moment to vanish. -/
theorem sphereLinearFormMoment_eq_zero_of_odd {n m : ℕ}
    (z : Fin n → ℝ) (hm : Odd m) :
    sphereLinearFormMoment m z = 0 := by
  let L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.neg ℝ
  let R : sphereSet n ≃ₜ sphereSet n :=
    sphereSetLinearIsometryHomeomorph L
  let f : sphereSet n → ℝ := fun y ↦ (∑ i, z i * y.1 i) ^ m
  have hR (y : sphereSet n) : (R y).1 = -y.1 := by
    ext i
    rfl
  have hfneg (y : sphereSet n) : f (R y) = -f y := by
    have hsum : (∑ i, z i * (R y).1 i) = -(∑ i, z i * y.1 i) := by
      rw [hR, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      simp
    dsimp only [f]
    rw [hsum]
    exact hm.neg_pow _
  have hchange :
      (∫ y : sphereSet n, f (R y) ∂normalizedSphereMeasure n) =
        ∫ y : sphereSet n, f y ∂normalizedSphereMeasure n := by
    exact (sphereSetLinearIsometry_measurePreserving L).integral_comp
      R.measurableEmbedding f
  have hneg :
      (∫ y : sphereSet n, f (R y) ∂normalizedSphereMeasure n) =
        -(∫ y : sphereSet n, f y ∂normalizedSphereMeasure n) := by
    calc
      (∫ y : sphereSet n, f (R y) ∂normalizedSphereMeasure n) =
          ∫ y : sphereSet n, -f y ∂normalizedSphereMeasure n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hfneg
      _ = -(∫ y : sphereSet n, f y ∂normalizedSphereMeasure n) :=
        integral_neg f
  unfold sphereLinearFormMoment
  change (∫ y : sphereSet n, f y ∂normalizedSphereMeasure n) = 0
  linarith

/-- A mixed moment vanishes whenever its total exponent is odd.  This is
obtained by reading a coefficient of the identically-zero odd line-moment
polynomial. -/
theorem mixedSphereLinearFormMoment_eq_zero_of_odd {n a b : ℕ}
    (hn : 0 < n) (x z : Fin n → ℝ) (hab : Odd (a + b)) :
    mixedSphereLinearFormMoment a b x z = 0 := by
  have hpoly : sphereMomentLinePolynomial (a + b) x z = 0 := by
    apply Polynomial.funext
    intro t
    rw [sphereMomentLinePolynomial_eval hn]
    rw [sphereLinearFormMoment_eq_zero_of_odd (x + t • z) hab]
    simp
  have hb : b ≤ a + b := by omega
  have hcoeff := sphereMomentLinePolynomial_coeff x z hb
  rw [hpoly, Polynomial.coeff_zero] at hcoeff
  have hchooseNat : 0 < Nat.choose (a + b) b := Nat.choose_pos hb
  have hchoose : (Nat.choose (a + b) b : ℝ) ≠ 0 := by
    exact_mod_cast hchooseNat.ne'
  have hmul : (Nat.choose (a + b) b : ℝ) *
      mixedSphereLinearFormMoment a b x z = 0 := by
    simpa only [Nat.add_sub_cancel_right] using hcoeff.symm
  exact (mul_eq_zero.mp hmul).resolve_left hchoose

/-- For a power of a fixed linear form in the integration variable, every
kernel monomial moment has a polynomial representative whose degree is no
larger than the input power. -/
theorem exists_degree_le_mixedSphereLinearFormMoment {n m d : ℕ}
    (hn : 2 ≤ n) (base : sphereSet n) (z : Fin n → ℝ) :
    ∃ q : MvPolynomial (Fin n) ℝ,
      q.totalDegree ≤ d ∧
      ∀ x : Fin n → ℝ, x ∈ sphereSet n →
        MvPolynomial.eval x q = mixedSphereLinearFormMoment m d x z := by
  by_cases hodd : Odd (m + d)
  · refine ⟨0, by simp, ?_⟩
    intro x _hx
    simp only [map_zero]
    symm
    exact mixedSphereLinearFormMoment_eq_zero_of_odd (by omega) x z hodd
  · rcases Nat.not_odd_iff_even.mp hodd with ⟨q, hq⟩
    have hsum : m + d = 2 * q := by omega
    have hd : d ≤ 2 * q := by omega
    refine ⟨evenMixedSphereLinearFormMomentPolynomial q d base z,
      evenMixedSphereLinearFormMomentPolynomial_totalDegree_le q d base z, ?_⟩
    intro x hx
    have heval := eval_evenMixedSphereLinearFormMomentPolynomial
      hn base z x hd hx
    rw [show 2 * q - d = m by omega] at heval
    exact heval

/-- Summing the coordinate variables indexed by a multiset is the linear-form
polynomial whose coefficients are the corresponding multiplicities. -/
theorem multiset_sum_map_X_eq_sphereDotPolynomial_count {n : ℕ}
    (s : Multiset (Fin n)) :
    (s.map (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))).sum =
      sphereDotPolynomial (fun i ↦ (s.count i : ℝ)) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [sphereDotPolynomial]
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      simp only [sphereDotPolynomial, Multiset.count_cons, Nat.cast_add,
        Nat.cast_ite, Nat.cast_one]
      simp_rw [map_add, add_mul]
      rw [Finset.sum_add_distrib]
      simp [eq_comm, add_comm]

/-- Alternating sum underlying the polarization identity. Using
`s.card + t.card` in the sign makes the powerset recursion subtraction-free;
it has the same parity as `s.card - t.card` whenever `t ≤ s`. -/
private def polarizationAlternatingSum {R : Type*} [CommRing R]
    (s : Multiset R) (m : ℕ) : R :=
  (s.powerset.map fun t ↦
    (-1 : R) ^ (s.card + t.card) * t.sum ^ m).sum

private lemma polarizationAlternatingSum_cons {R : Type*} [CommRing R]
    (a : R) (s : Multiset R) (m : ℕ) :
    polarizationAlternatingSum (a ::ₘ s) m =
      (s.powerset.map fun t ↦
        (-1 : R) ^ (s.card + t.card) *
          ((a + t.sum) ^ m - t.sum ^ m)).sum := by
  have hneg (p q : ℕ) :
      (-1 : R) ^ (p + 1 + q) = -((-1 : R) ^ (p + q)) := by
    rw [show p + 1 + q = (p + q) + 1 by omega, pow_succ]
    simp
  have hpos (p q : ℕ) :
      (-1 : R) ^ (p + 1 + (q + 1)) = (-1 : R) ^ (p + q) := by
    rw [show p + 1 + (q + 1) = (p + q) + 2 by omega, pow_add]
    simp
  simp only [polarizationAlternatingSum, Multiset.powerset_cons,
    Multiset.card_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Multiset.sum_cons]
  simp_rw [hpos s.card, hneg s.card]
  generalize s.powerset = u
  induction u using Multiset.induction_on with
  | empty => simp
  | @cons t u ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      linear_combination ih

/-- A binomial expansion turns one further powerset difference into lower
alternating sums. -/
private lemma polarizationAlternatingSum_cons_eq_sum
    {R : Type*} [CommRing R] (a : R) (s : Multiset R) (m : ℕ) :
    polarizationAlternatingSum (a ::ₘ s) m =
      ∑ k ∈ Finset.range m,
        polarizationAlternatingSum s k *
          (a ^ (m - k) * (m.choose k : R)) := by
  rw [polarizationAlternatingSum_cons]
  have hdiff (b : R) :
      (a + b) ^ m - b ^ m =
        ∑ k ∈ Finset.range m,
          b ^ k * a ^ (m - k) * (m.choose k : R) := by
    rw [add_comm, add_pow, Finset.sum_range_succ]
    simp
  simp_rw [hdiff, mul_sum]
  rw [Multiset.sum_map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  calc
    (s.powerset.map fun t ↦
        (-1 : R) ^ (s.card + t.card) *
          (t.sum ^ k * a ^ (m - k) * (m.choose k : R))).sum =
        (s.powerset.map fun t ↦
          ((-1 : R) ^ (s.card + t.card) * t.sum ^ k) *
            (a ^ (m - k) * (m.choose k : R))).sum := by
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro t _ht
      ring
    _ = polarizationAlternatingSum s k *
          (a ^ (m - k) * (m.choose k : R)) := by
      rw [Multiset.sum_map_mul_right]
      rfl

private lemma polarizationAlternatingSum_eq_zero_of_lt
    {R : Type*} [CommRing R] (s : Multiset R) {m : ℕ}
    (hm : m < s.card) :
    polarizationAlternatingSum s m = 0 := by
  induction s using Multiset.induction_on generalizing m with
  | empty => simp at hm
  | @cons a s ih =>
      rw [polarizationAlternatingSum_cons_eq_sum]
      apply Finset.sum_eq_zero
      intro k hk
      have hkm : k < m := Finset.mem_range.mp hk
      have hms : m ≤ s.card := by
        simpa only [Multiset.card_cons, Nat.lt_succ_iff] using hm
      have hks : k < s.card := by omega
      rw [ih hks, zero_mul]

/-- The full-cardinality alternating sum retains exactly the term using
every factor, with coefficient `s.card!`. -/
private lemma polarizationAlternatingSum_card_eq_factorial_mul_prod
    {R : Type*} [CommRing R] (s : Multiset R) :
    polarizationAlternatingSum s s.card =
      (s.card.factorial : R) * s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp [polarizationAlternatingSum]
  | @cons a s ih =>
      rw [polarizationAlternatingSum_cons_eq_sum]
      simp only [Multiset.card_cons, Finset.sum_range_succ]
      have hzero :
          (∑ k ∈ Finset.range s.card,
            polarizationAlternatingSum s k *
              (a ^ (s.card + 1 - k) *
                ((s.card + 1).choose k : R))) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [polarizationAlternatingSum_eq_zero_of_lt s
          (Finset.mem_range.mp hk), zero_mul]
      rw [hzero, zero_add, ih]
      simp only [Nat.add_sub_cancel_left, pow_one, Multiset.prod_cons,
        Nat.factorial_succ]
      rw [show (s.card + 1).choose s.card = s.card + 1 by
        exact Nat.choose_succ_self_right s.card]
      push_cast
      ring

private lemma multiset_powerset_map {α β : Type*}
    (f : α → β) (s : Multiset α) :
    (s.map f).powerset = s.powerset.map (Multiset.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.powerset_cons, ih,
        Multiset.map_add, Multiset.map_map, Function.comp_apply]

private lemma neg_one_pow_card_add_eq_sub {R : Type*} [CommRing R]
    {s t : Multiset R} (ht : t ≤ s) :
    (-1 : R) ^ (s.card + t.card) =
      (-1 : R) ^ (s.card - t.card) := by
  have hle : t.card ≤ s.card := Multiset.card_le_card ht
  have hcard :
      s.card + t.card = (s.card - t.card) + 2 * t.card := by
    omega
  rw [hcard, pow_add]
  have heven : (-1 : R) ^ (2 * t.card) = 1 := by
    rw [pow_mul]
    simp
  rw [heven, mul_one]

private lemma mvPolynomial_multiset_prod_eq_polarization {n : ℕ}
    (u : Multiset (MvPolynomial (Fin n) ℝ)) :
    u.prod =
      (u.powerset.map fun t ↦
        MvPolynomial.C
            ((u.card.factorial : ℝ)⁻¹ *
              (-1 : ℝ) ^ (u.card - t.card)) *
          t.sum ^ u.card).sum := by
  symm
  calc
    (u.powerset.map fun t ↦
        MvPolynomial.C
            ((u.card.factorial : ℝ)⁻¹ *
              (-1 : ℝ) ^ (u.card - t.card)) *
          t.sum ^ u.card).sum =
        MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
          polarizationAlternatingSum u u.card := by
      calc
        _ = (u.powerset.map fun t ↦
            MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
              ((-1 : MvPolynomial (Fin n) ℝ) ^ (u.card + t.card) *
                t.sum ^ u.card)).sum := by
          apply congrArg Multiset.sum
          apply Multiset.map_congr rfl
          intro t ht
          have htu : t ≤ u := Multiset.mem_powerset.mp ht
          simp only [map_mul, map_pow, map_neg, map_one]
          rw [← neg_one_pow_card_add_eq_sub
            (R := MvPolynomial (Fin n) ℝ) htu]
          ring
        _ = MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
              (u.powerset.map fun t ↦
                (-1 : MvPolynomial (Fin n) ℝ) ^ (u.card + t.card) *
                  t.sum ^ u.card).sum := Multiset.sum_map_mul_left
        _ = _ := rfl
    _ = MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
          ((u.card.factorial : MvPolynomial (Fin n) ℝ) * u.prod) := by
      rw [polarizationAlternatingSum_card_eq_factorial_mul_prod]
    _ = u.prod := by
      rw [← mul_assoc]
      have hfactorial : (u.card.factorial : ℝ) ≠ 0 := by positivity
      have hcancel :
          MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
              (u.card.factorial : MvPolynomial (Fin n) ℝ) = 1 := by
        change MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
          MvPolynomial.C (u.card.factorial : ℝ) = 1
        rw [← map_mul, inv_mul_cancel₀ hfactorial, map_one]
      rw [hcancel, one_mul]

/-- The explicit alternating-submultiset polarization identity. Duplicate
submultisets retain their multiplicity in `Multiset.powerset`, as required for
repeated factors. -/
theorem multiset_prod_map_X_eq_polarization {n : ℕ}
    (s : Multiset (Fin n)) :
    (s.map (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))).prod =
      (s.powerset.map fun t ↦
        MvPolynomial.C
            ((s.card.factorial : ℝ)⁻¹ * (-1 : ℝ) ^ (s.card - t.card)) *
          (sphereDotPolynomial (fun i ↦ (t.count i : ℝ))) ^ s.card).sum := by
  classical
  have h := mvPolynomial_multiset_prod_eq_polarization
    (s.map (fun i ↦
      (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)))
  simpa only [multiset_powerset_map, Multiset.map_map,
    Function.comp_apply, Multiset.card_map,
    multiset_sum_map_X_eq_sphereDotPolynomial_count] using h

/-- The product of the variables in an index multiset is its associated
monomial. -/
theorem multiset_prod_map_X_eq_monomial_toFinsupp {n : ℕ}
    (s : Multiset (Fin n)) :
    (s.map (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))).prod =
      MvPolynomial.monomial s.toFinsupp (1 : ℝ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih]
      rw [show (a ::ₘ s).toFinsupp =
        s.toFinsupp + Finsupp.single a 1 by
          rw [show a ::ₘ s = ({a} : Multiset (Fin n)) + s by rfl,
            Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
          exact add_comm _ _]
      rw [MvPolynomial.monomial_add_single]
      simp [mul_comm]

/-- The subspace spanned by `d`-th powers of the repository's linear-form
polynomials. -/
noncomputable def linearFormPowSpan (n d : ℕ) :
    Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  Submodule.span ℝ
    {q | ∃ z : Fin n → ℝ, q = (sphereDotPolynomial z) ^ d}

/-- Monomial form of the polarization identity: `∏ ℓᵢ` lies in the span of
`d`-th powers of sums of the `ℓᵢ`. The proof applies the explicit alternating
subset formula to `s.toMultiset`; the preceding count lemma identifies every
subset sum with a `sphereDotPolynomial`. -/
theorem monomial_mem_linearFormPowSpan {n : ℕ} (s : Fin n →₀ ℕ) :
    MvPolynomial.monomial s (1 : ℝ) ∈ linearFormPowSpan n s.degree := by
  classical
  let u : Multiset (Fin n) := s.toMultiset
  have hu : u.toFinsupp = s := by
    simp [u]
  have hcard : u.card = s.degree := by
    simpa only [u, Finsupp.degree_apply, Finsupp.sum, Function.id_def] using
      Finsupp.card_toMultiset s
  have hprod :
      (u.map (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))).prod =
        MvPolynomial.monomial s (1 : ℝ) := by
    rw [multiset_prod_map_X_eq_monomial_toFinsupp, hu]
  rw [← hprod, multiset_prod_map_X_eq_polarization]
  induction u.powerset using Multiset.induction_on with
  | empty =>
      simp only [Multiset.map_zero, Multiset.sum_zero]
      exact (linearFormPowSpan n s.degree).zero_mem
  | @cons t ts ih =>
      rw [Multiset.map_cons, Multiset.sum_cons]
      apply (linearFormPowSpan n s.degree).add_mem
      · rw [← MvPolynomial.smul_eq_C_mul]
        apply (linearFormPowSpan n s.degree).smul_mem
        apply Submodule.subset_span
        refine ⟨fun i ↦ (t.count i : ℝ), ?_⟩
        rw [hcard]
      · exact ih

/-- Pure polarization identity: over the reals, every homogeneous polynomial
is a finite linear combination of powers of linear forms. -/
theorem exists_fin_sum_linearForm_pow_eq_of_isHomogeneous
    {n d : ℕ} (v : MvPolynomial (Fin n) ℝ) (hv : v.IsHomogeneous d) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (z : Fin N → Fin n → ℝ),
      v = ∑ j, MvPolynomial.C (c j) * (sphereDotPolynomial (z j)) ^ d := by
  have hvspan : v ∈ linearFormPowSpan n d := by
    rw [v.as_sum]
    apply Submodule.sum_mem
    intro s hs
    have hcoeff : v.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hsdeg : s.degree = d := by
      by_contra hne
      exact hcoeff (hv.coeff_eq_zero hne)
    have hmono : MvPolynomial.monomial s (1 : ℝ) ∈ linearFormPowSpan n d := by
      simpa only [hsdeg] using monomial_mem_linearFormPowSpan s
    have hsmul := (linearFormPowSpan n d).smul_mem (v.coeff s) hmono
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hsmul
  rcases Submodule.mem_span_set'.mp hvspan with ⟨N, c, g, hg⟩
  let z : Fin N → Fin n → ℝ := fun j ↦ Classical.choose (g j).2
  have hgz (j : Fin N) :
      (g j).1 = (sphereDotPolynomial (z j)) ^ d := by
    exact Classical.choose_spec (g j).2
  refine ⟨N, c, z, ?_⟩
  calc
    v = ∑ j, c j • (g j).1 := hg.symm
    _ = ∑ j, MvPolynomial.C (c j) * (sphereDotPolynomial (z j)) ^ d := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hgz]
      rw [MvPolynomial.smul_eq_C_mul]

/-- Polarization adapter from homogeneous input polynomials to powers of
linear forms, followed by the integral and degree bookkeeping required for
zonal-kernel filtration preservation. -/
theorem exists_degree_le_integral_mul_sphereDotPolynomial_pow
    {n d m : ℕ} (hn : 2 ≤ n) (base : sphereSet n)
    (v : MvPolynomial (Fin n) ℝ) (hv : v.IsHomogeneous d) :
    ∃ q : MvPolynomial (Fin n) ℝ,
      q.totalDegree ≤ d ∧
      ∀ x : Fin n → ℝ, x ∈ sphereSet n →
        MvPolynomial.eval x q =
          ∫ y : sphereSet n, MvPolynomial.eval y.1 v *
            (∑ i, x i * y.1 i) ^ m ∂normalizedSphereMeasure n := by
  obtain ⟨N, c, z, hvsum⟩ :=
    exists_fin_sum_linearForm_pow_eq_of_isHomogeneous v hv
  let w : Fin N → MvPolynomial (Fin n) ℝ := fun j ↦
    Classical.choose
      (exists_degree_le_mixedSphereLinearFormMoment (m := m) (d := d)
        hn base (z j))
  have hwdeg (j : Fin N) : (w j).totalDegree ≤ d := by
    exact (Classical.choose_spec
      (exists_degree_le_mixedSphereLinearFormMoment (m := m) (d := d)
        hn base (z j))).1
  have hweval (j : Fin N) (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
      MvPolynomial.eval x (w j) =
        mixedSphereLinearFormMoment m d x (z j) := by
    exact (Classical.choose_spec
      (exists_degree_le_mixedSphereLinearFormMoment (m := m) (d := d)
        hn base (z j))).2 x hx
  refine ⟨∑ j, MvPolynomial.C (c j) * w j, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro j _hj
    calc
      (MvPolynomial.C (c j) * w j).totalDegree ≤
          (MvPolynomial.C (c j)).totalDegree + (w j).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + d := Nat.add_le_add (le_of_eq (MvPolynomial.totalDegree_C _))
        (hwdeg j)
      _ = d := Nat.zero_add d
  · intro x hx
    calc
      MvPolynomial.eval x (∑ j, MvPolynomial.C (c j) * w j) =
          ∑ j, c j * mixedSphereLinearFormMoment m d x (z j) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [map_mul, eval_C, hweval j x hx]
      _ = ∫ y : sphereSet n,
          ∑ j, c j * ((∑ i, x i * y.1 i) ^ m *
            (∑ i, z j i * y.1 i) ^ d) ∂normalizedSphereMeasure n := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _hj
          rw [mixedSphereLinearFormMoment, integral_const_mul]
        · intro j _hj
          exact (integrable_mixedSphereLinearFormMoment (by omega)
            m d x (z j)).const_mul _
      _ = ∫ y : sphereSet n, MvPolynomial.eval y.1 v *
          (∑ i, x i * y.1 i) ^ m ∂normalizedSphereMeasure n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun y ↦ by
          rw [hvsum]
          change (∑ j, c j * ((∑ i, x i * y.1 i) ^ m *
              (∑ i, z j i * y.1 i) ^ d)) =
            MvPolynomial.eval y.1
              (∑ j, MvPolynomial.C (c j) * sphereDotPolynomial (z j) ^ d) *
                (∑ i, x i * y.1 i) ^ m
          rw [map_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [map_mul, eval_C, map_pow, eval_sphereDotPolynomial]
          ring)

/-- A chosen degree-bounded representative for one homogeneous component and
one monomial of the scalar zonal polynomial. -/
noncomputable def homogeneousSphereMomentPolynomial {n : ℕ}
    (hn : 2 ≤ n) (base : sphereSet n)
    (v : MvPolynomial (Fin n) ℝ) (d m : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  Classical.choose
    (exists_degree_le_integral_mul_sphereDotPolynomial_pow (m := m) hn base
      (MvPolynomial.homogeneousComponent d v)
      (MvPolynomial.homogeneousComponent_isHomogeneous d v))

/-- The chosen homogeneous moment representative has degree at most the
homogeneous degree. -/
theorem homogeneousSphereMomentPolynomial_totalDegree_le {n : ℕ}
    (hn : 2 ≤ n) (base : sphereSet n)
    (v : MvPolynomial (Fin n) ℝ) (d m : ℕ) :
    (homogeneousSphereMomentPolynomial hn base v d m).totalDegree ≤ d := by
  exact (Classical.choose_spec
    (exists_degree_le_integral_mul_sphereDotPolynomial_pow (m := m) hn base
      (MvPolynomial.homogeneousComponent d v)
      (MvPolynomial.homogeneousComponent_isHomogeneous d v))).1

/-- Evaluation contract for the chosen homogeneous moment representative. -/
theorem eval_homogeneousSphereMomentPolynomial {n : ℕ}
    (hn : 2 ≤ n) (base : sphereSet n)
    (v : MvPolynomial (Fin n) ℝ) (d m : ℕ)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    MvPolynomial.eval x (homogeneousSphereMomentPolynomial hn base v d m) =
      ∫ y : sphereSet n,
        MvPolynomial.eval y.1 (MvPolynomial.homogeneousComponent d v) *
          (∑ i, x i * y.1 i) ^ m ∂normalizedSphereMeasure n := by
  exact (Classical.choose_spec
    (exists_degree_le_integral_mul_sphereDotPolynomial_pow (m := m) hn base
      (MvPolynomial.homogeneousComponent d v)
      (MvPolynomial.homogeneousComponent_isHomogeneous d v))).2 x hx

/-- The finite sum of all homogeneous-input and scalar-kernel monomial
representatives. -/
noncomputable def polynomialZonalMomentPolynomial {n : ℕ}
    (hn : 2 ≤ n) (base : sphereSet n)
    (v : MvPolynomial (Fin n) ℝ) (P : Polynomial ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ d ∈ Finset.range (v.totalDegree + 1),
    ∑ m ∈ Finset.range (P.natDegree + 1),
      MvPolynomial.C (P.coeff m) *
        homogeneousSphereMomentPolynomial hn base v d m

/-- Finite assembly does not increase the degree of the input polynomial. -/
theorem polynomialZonalMomentPolynomial_totalDegree_le {n : ℕ}
    (hn : 2 ≤ n) (base : sphereSet n)
    (v : MvPolynomial (Fin n) ℝ) (P : Polynomial ℝ) :
    (polynomialZonalMomentPolynomial hn base v P).totalDegree ≤
      v.totalDegree := by
  unfold polynomialZonalMomentPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [Finset.mem_range] at hd
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m _hm
  calc
    (MvPolynomial.C (P.coeff m) *
        homogeneousSphereMomentPolynomial hn base v d m).totalDegree ≤
        (MvPolynomial.C (P.coeff m)).totalDegree +
          (homogeneousSphereMomentPolynomial hn base v d m).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + d := Nat.add_le_add
      (le_of_eq (MvPolynomial.totalDegree_C _))
      (homogeneousSphereMomentPolynomial_totalDegree_le hn base v d m)
    _ ≤ v.totalDegree := by omega

/-- Evaluation of the finite assembly is the integral against the original
ambient polynomial and scalar zonal polynomial. -/
theorem eval_polynomialZonalMomentPolynomial {n : ℕ}
    (hn : 2 ≤ n) (base : sphereSet n)
    (v : MvPolynomial (Fin n) ℝ) (P : Polynomial ℝ)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    MvPolynomial.eval x (polynomialZonalMomentPolynomial hn base v P) =
      ∫ y : sphereSet n, MvPolynomial.eval y.1 v *
        P.eval (∑ i, x i * y.1 i) ∂normalizedSphereMeasure n := by
  have hint (d m : ℕ) : Integrable (fun y : sphereSet n ↦
      P.coeff m *
        (MvPolynomial.eval y.1 (MvPolynomial.homogeneousComponent d v) *
          (∑ i, x i * y.1 i) ^ m))
      (normalizedSphereMeasure n) := by
    have h := integrable_eval_normalizedSphereMeasure (by omega)
      (MvPolynomial.C (P.coeff m) *
        MvPolynomial.homogeneousComponent d v *
          sphereDotPolynomial x ^ m)
    simpa only [map_mul, map_pow, eval_C, eval_sphereDotPolynomial,
      mul_assoc] using h
  have hpoint (y : sphereSet n) :
      MvPolynomial.eval y.1 v * P.eval (∑ i, x i * y.1 i) =
        ∑ d ∈ Finset.range (v.totalDegree + 1),
          ∑ m ∈ Finset.range (P.natDegree + 1),
            P.coeff m *
              (MvPolynomial.eval y.1 (MvPolynomial.homogeneousComponent d v) *
                (∑ i, x i * y.1 i) ^ m) := by
    have hvsum :
        (∑ d ∈ Finset.range (v.totalDegree + 1),
          MvPolynomial.eval y.1 (MvPolynomial.homogeneousComponent d v)) =
          MvPolynomial.eval y.1 v := by
      have h := congrArg (MvPolynomial.eval y.1)
        (MvPolynomial.sum_homogeneousComponent (φ := v))
      simpa only [map_sum] using h
    rw [← hvsum]
    rw [Polynomial.eval_eq_sum_range]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _hm
    ring
  rw [polynomialZonalMomentPolynomial]
  simp only [map_sum, map_mul, eval_C]
  simp_rw [eval_homogeneousSphereMomentPolynomial hn base v _ _ x hx]
  calc
    (∑ d ∈ Finset.range (v.totalDegree + 1),
        ∑ m ∈ Finset.range (P.natDegree + 1),
          P.coeff m *
            ∫ y : sphereSet n,
              MvPolynomial.eval y.1 (MvPolynomial.homogeneousComponent d v) *
                (∑ i, x i * y.1 i) ^ m
              ∂normalizedSphereMeasure n) =
        ∫ y : sphereSet n,
          ∑ d ∈ Finset.range (v.totalDegree + 1),
            ∑ m ∈ Finset.range (P.natDegree + 1),
              P.coeff m *
                (MvPolynomial.eval y.1 (MvPolynomial.homogeneousComponent d v) *
                  (∑ i, x i * y.1 i) ^ m)
          ∂normalizedSphereMeasure n := by
      symm
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro d _hd
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro m _hm
          rw [integral_const_mul]
        · intro m _hm
          exact hint d m
      · intro d _hd
        exact integrable_finsetSum _ (fun m _hm ↦ hint d m)
    _ = ∫ y : sphereSet n, MvPolynomial.eval y.1 v *
          P.eval (∑ i, x i * y.1 i)
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y ↦ (hpoint y).symm)

/-- Finite homogeneous-component and univariate-coefficient assembly for a
general polynomial zonal kernel in dimension at least two. Its only
substantive algebraic input is
`exists_degree_le_integral_mul_sphereDotPolynomial_pow`. -/
theorem exists_degree_le_integral_mul_eval_polynomial_sphereDot_of_two_le
    {n D : ℕ} (hn : 2 ≤ n) (base : sphereSet n) (P : Polynomial ℝ)
    (v : MvPolynomial (Fin n) ℝ) (hv : v.totalDegree ≤ D) :
    ∃ q : MvPolynomial (Fin n) ℝ,
      q.totalDegree ≤ D ∧
      ∀ x : Fin n → ℝ, x ∈ sphereSet n →
        MvPolynomial.eval x q =
          ∫ y : sphereSet n, MvPolynomial.eval y.1 v *
            P.eval (∑ i, x i * y.1 i) ∂normalizedSphereMeasure n := by
  refine ⟨polynomialZonalMomentPolynomial hn base v P, ?_, ?_⟩
  · exact (polynomialZonalMomentPolynomial_totalDegree_le hn base v P).trans hv
  · intro x hx
    exact eval_polynomialZonalMomentPolynomial hn base v P x hx

/-- The algebraic one-dimensional sphere consists of the two sign vectors. -/
theorem fin_one_eq_one_or_neg_one_of_mem_sphereSet
    (x : Fin 1 → ℝ) (hx : x ∈ sphereSet 1) :
    x = (1 : Fin 1 → ℝ) ∨ x = -(1 : Fin 1 → ℝ) := by
  have hx0 : x 0 ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic] using hx
  rcases sq_eq_one_iff.mp hx0 with hpos | hneg
  · left
    funext i
    fin_cases i
    exact hpos
  · right
    funext i
    fin_cases i
    exact hneg

/-- On the two-point sphere, any zonal integral has an affine representative.
This supplies the filtration claim whenever the allowed degree is positive. -/
theorem exists_degree_le_integral_mul_eval_polynomial_sphereDot_fin_one_of_pos
    {D : ℕ} (hD : 0 < D) (P : Polynomial ℝ)
    (v : MvPolynomial (Fin 1) ℝ) :
    ∃ q : MvPolynomial (Fin 1) ℝ,
      q.totalDegree ≤ D ∧
      ∀ x : Fin 1 → ℝ, x ∈ sphereSet 1 →
        MvPolynomial.eval x q =
          ∫ y : sphereSet 1, MvPolynomial.eval y.1 v *
            P.eval (∑ i, x i * y.1 i) ∂normalizedSphereMeasure 1 := by
  let F : (Fin 1 → ℝ) → ℝ := fun x ↦
    ∫ y : sphereSet 1, MvPolynomial.eval y.1 v *
      P.eval (∑ i, x i * y.1 i) ∂normalizedSphereMeasure 1
  let A : ℝ := F (1 : Fin 1 → ℝ)
  let B : ℝ := F (-(1 : Fin 1 → ℝ))
  refine ⟨MvPolynomial.C ((A + B) / 2) +
      MvPolynomial.C ((A - B) / 2) * MvPolynomial.X 0, ?_, ?_⟩
  · calc
      ((MvPolynomial.C ((A + B) / 2) : MvPolynomial (Fin 1) ℝ) +
          MvPolynomial.C ((A - B) / 2) * MvPolynomial.X (0 : Fin 1)).totalDegree ≤
          max (MvPolynomial.C ((A + B) / 2) :
            MvPolynomial (Fin 1) ℝ).totalDegree
            (MvPolynomial.C ((A - B) / 2) * MvPolynomial.X (0 : Fin 1)).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ 1 := by
        apply max_le
        · simp
        · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
      _ ≤ D := hD
  · intro x hx
    rcases fin_one_eq_one_or_neg_one_of_mem_sphereSet x hx with rfl | rfl
    · simp only [map_add, map_mul, eval_C, eval_X, Pi.one_apply]
      change (A + B) / 2 + (A - B) / 2 * 1 = F (1 : Fin 1 → ℝ)
      rw [show F (1 : Fin 1 → ℝ) = A by rfl]
      ring
    · simp only [map_add, map_mul, eval_C, eval_X, Pi.one_apply, Pi.neg_apply]
      change (A + B) / 2 + (A - B) / 2 * (-1) =
        F (-(1 : Fin 1 → ℝ))
      rw [show F (-(1 : Fin 1 → ℝ)) = B by rfl]
      ring

/-- For a constant input on the two-point sphere, antipodal averaging makes
every polynomial zonal integral constant in the center. -/
theorem exists_degree_le_integral_mul_eval_polynomial_sphereDot_fin_one_of_degree_zero
    (P : Polynomial ℝ) (v : MvPolynomial (Fin 1) ℝ)
    (hv : v.totalDegree ≤ 0) :
    ∃ q : MvPolynomial (Fin 1) ℝ,
      q.totalDegree ≤ 0 ∧
      ∀ x : Fin 1 → ℝ, x ∈ sphereSet 1 →
        MvPolynomial.eval x q =
          ∫ y : sphereSet 1, MvPolynomial.eval y.1 v *
            P.eval (∑ i, x i * y.1 i) ∂normalizedSphereMeasure 1 := by
  let e : Fin 1 → ℝ := (1 : Fin 1 → ℝ)
  let F : (Fin 1 → ℝ) → ℝ := fun x ↦
    ∫ y : sphereSet 1, MvPolynomial.eval y.1 v *
      P.eval (∑ i, x i * y.1 i) ∂normalizedSphereMeasure 1
  let L : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    LinearIsometryEquiv.neg ℝ
  let R : sphereSet 1 ≃ₜ sphereSet 1 :=
    sphereSetLinearIsometryHomeomorph L
  let c : ℝ := v.coeff 0
  let f : sphereSet 1 → ℝ := fun y ↦
    c * P.eval (∑ i, e i * y.1 i)
  have hvC : v = MvPolynomial.C c := by
    exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      (Nat.eq_zero_of_le_zero hv)
  have hR (y : sphereSet 1) : (R y).1 = -y.1 := by
    ext i
    rfl
  have hchange :
      (∫ y : sphereSet 1, f (R y) ∂normalizedSphereMeasure 1) =
        ∫ y : sphereSet 1, f y ∂normalizedSphereMeasure 1 := by
    exact (sphereSetLinearIsometry_measurePreserving L).integral_comp
      R.measurableEmbedding f
  have hneg : F (-e) = ∫ y : sphereSet 1, f (R y)
      ∂normalizedSphereMeasure 1 := by
    unfold F
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y ↦ by
      rw [hvC]
      simp only [eval_C]
      dsimp only [f]
      rw [hR]
      congr 2
      apply Finset.sum_congr rfl
      intro i _hi
      simp [e])
  have hpos : (∫ y : sphereSet 1, f y ∂normalizedSphereMeasure 1) = F e := by
    unfold F
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y ↦ by
      dsimp only [f]
      rw [hvC]
      simp only [eval_C])
  refine ⟨MvPolynomial.C (F e), by simp, ?_⟩
  intro x hx
  rcases fin_one_eq_one_or_neg_one_of_mem_sphereSet x hx with hx | hx
  · rw [hx, eval_C]
  · rw [hx, eval_C]
    change F e = F (-e)
    rw [hneg, hchange, hpos]

/-- The exceptional zero-sphere (`n = 1`) adapter. This is kept explicit:
on its two points the integral can be represented by an affine polynomial,
with the degree-zero case following from antipodal averaging. -/
theorem exists_degree_le_integral_mul_eval_polynomial_sphereDot_fin_one
    {D : ℕ} (P : Polynomial ℝ) (v : MvPolynomial (Fin 1) ℝ)
    (hv : v.totalDegree ≤ D) :
    ∃ q : MvPolynomial (Fin 1) ℝ,
      q.totalDegree ≤ D ∧
      ∀ x : Fin 1 → ℝ, x ∈ sphereSet 1 →
        MvPolynomial.eval x q =
          ∫ y : sphereSet 1, MvPolynomial.eval y.1 v *
            P.eval (∑ i, x i * y.1 i) ∂normalizedSphereMeasure 1 := by
  cases D with
  | zero =>
      exact
        exists_degree_le_integral_mul_eval_polynomial_sphereDot_fin_one_of_degree_zero
          P v hv
  | succ D =>
      exact exists_degree_le_integral_mul_eval_polynomial_sphereDot_fin_one_of_pos
        (Nat.succ_pos D) P v

/-- Finite homogeneous-component and univariate-coefficient assembly for a
general polynomial zonal kernel in every positive dimension. -/
theorem exists_degree_le_integral_mul_eval_polynomial_sphereDot
    {n D : ℕ} (hn : 0 < n) (P : Polynomial ℝ)
    (v : MvPolynomial (Fin n) ℝ) (hv : v.totalDegree ≤ D) :
    ∃ q : MvPolynomial (Fin n) ℝ,
      q.totalDegree ≤ D ∧
      ∀ x : Fin n → ℝ, x ∈ sphereSet n →
        MvPolynomial.eval x q =
          ∫ y : sphereSet n, MvPolynomial.eval y.1 v *
            P.eval (∑ i, x i * y.1 i) ∂normalizedSphereMeasure n := by
  by_cases hn_two : 2 ≤ n
  · obtain ⟨x, hx⟩ := sphereSet_nonempty hn
    exact exists_degree_le_integral_mul_eval_polynomial_sphereDot_of_two_le
      hn_two ⟨x, hx⟩ P v hv
  · have hn_one : n = 1 := by omega
    subst n
    exact exists_degree_le_integral_mul_eval_polynomial_sphereDot_fin_one P v hv

/-- On the sphere, the unnormalized polynomial-zonal integral of a degree-`D`
sphere polynomial has an ambient representative of degree at most `D`. The proof
expands into powers of linear forms, uses orthogonal invariance to evaluate radial
moments, and extracts the required coefficient by polarization. -/
theorem exists_degree_le_integral_mul_sphereDirichletZonalKernel
    {n D : ℕ} (hn : 0 < n) (p k : ℕ)
    (v : spherePolynomialSpace n D) :
    ∃ q : MvPolynomial (Fin n) ℝ,
      q.totalDegree ≤ D ∧
      ∀ x : Fin n → ℝ, x ∈ sphereSet n →
        MvPolynomial.eval x q =
          ∫ y : sphereSet n, v.1 y *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
              ∂normalizedSphereMeasure n := by
  obtain ⟨vpoly, hvdeg, hvrepr⟩ :=
    (mem_spherePolynomialSpace_iff v.1).1 v.2
  obtain ⟨q, hqdeg, hqeval⟩ :=
    exists_degree_le_integral_mul_eval_polynomial_sphereDot hn
      ((sphereDirichletPolynomial k) ^ (2 * p)) vpoly hvdeg
  refine ⟨q, hqdeg, ?_⟩
  intro x hx
  rw [hqeval x hx]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change MvPolynomial.eval y.1 vpoly *
      ((sphereDirichletPolynomial k) ^ (2 * p)).eval
        (∑ i, x i * y.1 i) =
    v.1 y * MvPolynomial.eval y.1
      (sphereDirichletZonalKernel p k x)
  have hvpoint : v.1 y = MvPolynomial.eval y.1 vpoly := by
    rw [← hvrepr]
    exact sphereRestrictionLinear_apply n vpoly y
  rw [← hvpoint, eval_sphereDirichletZonalKernel]
  simp only [Polynomial.eval_pow]

end QuarticConvergence
end OptimalConvergenceRates

end
