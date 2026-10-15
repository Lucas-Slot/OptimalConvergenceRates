/-
  The rapidly growing signed moment functional used in the sharp
  Archimedean lower bound.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.Geometry

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- The exponent of the first variable in a bivariate monomial. -/
abbrev bivarFirstExponent (α : Fin 2 →₀ ℕ) : ℕ := α 0

/-- The exponent of the second variable in a bivariate monomial. -/
abbrev bivarSecondExponent (α : Fin 2 →₀ ℕ) : ℕ := α 1

/-- The signed moment
    `F_η(a^i b^j) = (-1)^(ij) η^(i+j) exp(4(i²+j²))`. -/
def sharpMoment (η : ℝ) (α : Fin 2 →₀ ℕ) : ℝ :=
  (-1 : ℝ) ^ (bivarFirstExponent α * bivarSecondExponent α) *
    η ^ (bivarFirstExponent α + bivarSecondExponent α) *
      Real.exp
        (4 * ((bivarFirstExponent α : ℝ) ^ 2 +
          (bivarSecondExponent α : ℝ) ^ 2))

/-- The coefficient-linear extension of `sharpMoment` to bivariate
polynomials. -/
def sharpMomentFunctional (η : ℝ) :
    MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ :=
  (Finsupp.lsum ℝ)
      (fun α : Fin 2 →₀ ℕ ↦
        (LinearMap.lsmul ℝ ℝ) (sharpMoment η α)) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] theorem sharpMomentFunctional_apply (η : ℝ)
    (p : MvPolynomial (Fin 2) ℝ) :
    sharpMomentFunctional η p =
      p.coeff.sum fun α c ↦ sharpMoment η α * c :=
  rfl

@[simp] theorem sharpMomentFunctional_monomial
    (η c : ℝ) (α : Fin 2 →₀ ℕ) :
    sharpMomentFunctional η (monomial α c) =
      sharpMoment η α * c := by
  change (Finsupp.lsum ℝ) _ (Finsupp.single α c) = _
  rw [Finsupp.lsum_single]
  rfl

@[simp] theorem sharpMoment_zero (η : ℝ) :
    sharpMoment η (0 : Fin 2 →₀ ℕ) = 1 := by
  simp [sharpMoment, bivarFirstExponent, bivarSecondExponent]

@[simp] theorem sharpMomentFunctional_one (η : ℝ) :
    sharpMomentFunctional η (1 : MvPolynomial (Fin 2) ℝ) = 1 := by
  simp only [one_def, sharpMomentFunctional_monomial, sharpMoment_zero, one_mul]

/-- The exponent vector of the monomial `a^i b^j`. -/
def bivarExponent (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j

@[simp] theorem bivarExponent_zero (i j : ℕ) :
    bivarExponent i j (0 : Fin 2) = i := by
  simp [bivarExponent]

@[simp] theorem bivarExponent_one (i j : ℕ) :
    bivarExponent i j (1 : Fin 2) = j := by
  simp [bivarExponent]

theorem bivarExponent_of_exponents (α : Fin 2 →₀ ℕ) :
    bivarExponent (α 0) (α 1) = α := by
  ext k
  fin_cases k <;> simp

@[simp] theorem bivarExponent_add (i j k l : ℕ) :
    bivarExponent i j + bivarExponent k l =
      bivarExponent (i + k) (j + l) := by
  ext u
  fin_cases u <;> simp

@[simp] theorem sharpMoment_bivarExponent (η : ℝ) (i j : ℕ) :
    sharpMoment η (bivarExponent i j) =
      (-1 : ℝ) ^ (i * j) * η ^ (i + j) *
        Real.exp (4 * ((i : ℝ) ^ 2 + (j : ℝ) ^ 2)) := by
  simp only [sharpMoment, bivarFirstExponent, bivarSecondExponent,
    bivarExponent_zero, bivarExponent_one]

/-- The positive square root of the diagonal moment attached to a
bivariate monomial. -/
def sharpMomentScale (η : ℝ) (i j : ℕ) : ℝ :=
  η ^ (i + j) * Real.exp (8 * ((i : ℝ) ^ 2 + (j : ℝ) ^ 2))

theorem sharpMomentScale_pos {η : ℝ} (hη : 0 < η) (i j : ℕ) :
    0 < sharpMomentScale η i j :=
  mul_pos (pow_pos hη _) (Real.exp_pos _)

/-- After diagonal normalization, the absolute moment matrix entry is
the discrete Gaussian kernel used in the diagonal-dominance argument. -/
theorem abs_sharpMoment_add_eq_scale_mul_gaussian
    {η : ℝ} (hη : 0 < η) (i j k l : ℕ) :
    |sharpMoment η (bivarExponent i j + bivarExponent k l)| =
      sharpMomentScale η i j * sharpMomentScale η k l *
        Real.exp (-4 * (((i : ℝ) - k) ^ 2 + ((j : ℝ) - l) ^ 2)) := by
  rw [bivarExponent_add, sharpMoment_bivarExponent]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hη, abs_of_pos (Real.exp_pos _)]
  unfold sharpMomentScale
  rw [show i + k + (j + l) = (i + j) + (k + l) by omega, pow_add]
  have hexp :
      Real.exp (4 * (((i + k : ℕ) : ℝ) ^ 2 + ((j + l : ℕ) : ℝ) ^ 2)) =
        Real.exp (8 * ((i : ℝ) ^ 2 + (j : ℝ) ^ 2)) *
          Real.exp (8 * ((k : ℝ) ^ 2 + (l : ℝ) ^ 2)) *
            Real.exp (-4 * (((i : ℝ) - k) ^ 2 + ((j : ℝ) - l) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- The bivariate coordinate polynomials used in the obstruction. -/
abbrev obstructionA : MvPolynomial (Fin 2) ℝ := X 0

/-- A diagonal entry is the square of its positive normalization scale. -/
theorem sharpMoment_add_self_eq_scale_sq
    {η : ℝ} (hη : 0 < η) (i j : ℕ) :
    sharpMoment η (bivarExponent i j + bivarExponent i j) =
      sharpMomentScale η i j ^ 2 := by
  have habs := abs_sharpMoment_add_eq_scale_mul_gaussian hη i j i j
  have hmnon :
      0 ≤ sharpMoment η (bivarExponent i j + bivarExponent i j) := by
    rw [bivarExponent_add, sharpMoment_bivarExponent]
    have hii : Even (i + i) := ⟨i, by omega⟩
    have heven : Even ((i + i) * (j + j)) :=
      hii.mul_right (j + j)
    rw [Even.neg_one_pow heven]
    positivity
  rw [abs_of_nonneg hmnon] at habs
  have hscale := sharpMomentScale_pos hη i j
  simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    mul_zero, Real.exp_zero, mul_one, pow_two] using habs


/-- Positive diagonal normalization for a moment matrix shifted by the
monomial `a^u b^v`. -/
def sharpShiftedMomentScale (η : ℝ) (u v i j : ℕ) : ℝ :=
  η ^ (i + j) * Real.sqrt η ^ (u + v) *
    Real.exp (2 * ((((2 * i + u : ℕ) : ℝ) ^ 2) +
      (((2 * j + v : ℕ) : ℝ) ^ 2)))

theorem sharpShiftedMomentScale_pos {η : ℝ} (hη : 0 < η)
    (u v i j : ℕ) : 0 < sharpShiftedMomentScale η u v i j := by
  unfold sharpShiftedMomentScale
  positivity

/-- Every monomial shift has the same normalized Gaussian kernel. -/
theorem abs_sharpMoment_shift_eq_scale_mul_gaussian
    {η : ℝ} (hη : 0 < η) (u v i j k l : ℕ) :
    |sharpMoment η
        (bivarExponent i j + bivarExponent k l + bivarExponent u v)| =
      sharpShiftedMomentScale η u v i j *
        sharpShiftedMomentScale η u v k l *
          Real.exp (-4 * (((i : ℝ) - k) ^ 2 + ((j : ℝ) - l) ^ 2)) := by
  rw [bivarExponent_add, bivarExponent_add, sharpMoment_bivarExponent]
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hη, abs_of_pos (Real.exp_pos _)]
  unfold sharpShiftedMomentScale
  have hsqrt :
      Real.sqrt η ^ (u + v) * Real.sqrt η ^ (u + v) = η ^ (u + v) := by
    rw [← mul_pow, Real.mul_self_sqrt hη.le]
  have heta :
      i + k + u + (j + l + v) = (i + j) + (k + l) + (u + v) := by omega
  rw [heta, pow_add, pow_add]
  have hexp :
      Real.exp
          (4 * ((((i + k + u : ℕ) : ℝ) ^ 2) +
            (((j + l + v : ℕ) : ℝ) ^ 2))) =
        Real.exp (2 * ((((2 * i + u : ℕ) : ℝ) ^ 2) +
            (((2 * j + v : ℕ) : ℝ) ^ 2))) *
          Real.exp (2 * ((((2 * k + u : ℕ) : ℝ) ^ 2) +
            (((2 * l + v : ℕ) : ℝ) ^ 2))) *
            Real.exp (-4 * (((i : ℝ) - k) ^ 2 + ((j : ℝ) - l) ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp, ← hsqrt]
  ring

/-- After correcting the constant parity sign of the shift, the diagonal
moment is the square of its positive normalization. -/
theorem signed_sharpMoment_shift_self_eq_scale_sq
    {η : ℝ} (hη : 0 < η) (u v i j : ℕ) :
    (-1 : ℝ) ^ (u * v) *
        sharpMoment η
          (bivarExponent i j + bivarExponent i j + bivarExponent u v) =
      sharpShiftedMomentScale η u v i j ^ 2 := by
  have habs := abs_sharpMoment_shift_eq_scale_mul_gaussian
    hη u v i j i j
  have heven : Even
      (u * v + (i + i + u) * (j + j + v)) := by
    refine ⟨2 * i * j + i * v + j * u + u * v, ?_⟩
    ring
  have hsign :
      (-1 : ℝ) ^ (u * v) * (-1 : ℝ) ^ ((i + i + u) * (j + j + v)) = 1 := by
    rw [← pow_add, Even.neg_one_pow heven]
  have hnonneg :
      0 ≤ (-1 : ℝ) ^ (u * v) *
        sharpMoment η
          (bivarExponent i j + bivarExponent i j + bivarExponent u v) := by
    rw [bivarExponent_add, bivarExponent_add, sharpMoment_bivarExponent]
    calc
      0 ≤ ((-1 : ℝ) ^ (u * v) *
            (-1 : ℝ) ^ ((i + i + u) * (j + j + v))) *
          (η ^ (i + i + u + (j + j + v)) *
            Real.exp (4 * (((i + i + u : ℕ) : ℝ) ^ 2 +
              ((j + j + v : ℕ) : ℝ) ^ 2))) := by rw [hsign]; positivity
      _ = _ := by ring
  have habs' :
      |(-1 : ℝ) ^ (u * v) *
          sharpMoment η
            (bivarExponent i j + bivarExponent i j + bivarExponent u v)| =
        |sharpMoment η
            (bivarExponent i j + bivarExponent i j + bivarExponent u v)| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← habs', abs_of_nonneg hnonneg] at habs
  simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
    mul_zero, Real.exp_zero, mul_one, pow_two] using habs
/-- The bivariate coordinate polynomials used in the obstruction. -/
abbrev obstructionB : MvPolynomial (Fin 2) ℝ := X 1

@[simp] theorem sharpMoment_single_zero (η : ℝ) (i : ℕ) :
    sharpMoment η (Finsupp.single (0 : Fin 2) i) =
      η ^ i * Real.exp (4 * (i : ℝ) ^ 2) := by
  simp [sharpMoment]

@[simp] theorem sharpMoment_single_one (η : ℝ) (j : ℕ) :
    sharpMoment η (Finsupp.single (1 : Fin 2) j) =
      η ^ j * Real.exp (4 * (j : ℝ) ^ 2) := by
  simp [sharpMoment]

/-- The first mixed moment has the deliberately negative sign. -/
@[simp] theorem sharpMoment_ab (η : ℝ) :
    sharpMoment η
        (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1) =
      -(η ^ 2 * Real.exp 8) := by
  simp [sharpMoment, bivarFirstExponent, bivarSecondExponent]
  exact Or.inl (by norm_num)

/-- The functional is positive on the constant square and strictly positive
on the shifted `-(ab+η²)` term when `η > 0`.  This is the scalar
diagonal case of the localizing-matrix estimate. -/
theorem sharpMoment_neg_ab_sub_etaSq_pos {η : ℝ} (hη : 0 < η) :
    0 < sharpMomentFunctional η
      (-(obstructionA * obstructionB + C (η ^ 2))) := by
  let α : Fin 2 →₀ ℕ :=
    Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1
  have hpoly : obstructionA * obstructionB = monomial α 1 := by
    change
      monomial (Finsupp.single (0 : Fin 2) 1) 1 *
          monomial (Finsupp.single (1 : Fin 2) 1) 1 =
        monomial α 1
    simp [α, monomial_mul_monomial]
  have hab :
      sharpMomentFunctional η (obstructionA * obstructionB) =
        -(η ^ 2 * Real.exp 8) := by
    rw [hpoly, sharpMomentFunctional_monomial]
    simpa [α] using sharpMoment_ab η
  have hc :
      sharpMomentFunctional η (C (η ^ 2) : MvPolynomial (Fin 2) ℝ) =
        η ^ 2 := by
    rw [show C (η ^ 2) = monomial 0 (η ^ 2) by simp]
    rw [sharpMomentFunctional_monomial, sharpMoment_zero, one_mul]
  have he : 1 < Real.exp 8 := Real.one_lt_exp_iff.mpr (by norm_num)
  rw [map_neg, map_add, hab, hc]
  nlinarith [sq_pos_of_pos hη]

end OptimalConvergenceRates.GeneralArchimedean

end
