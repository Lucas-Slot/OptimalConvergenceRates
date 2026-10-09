/-
  OptimalConvergenceRates/ScaledRobinson/HomogenizationSpectral.lean

  Spectral polynomial estimates for the scaled Robinson homogenization.
-/
import OptimalConvergenceRates.ScaledRobinson.HomogenizationCore
import Mathlib.Analysis.Complex.Polynomial.Basic

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- Coefficientwise complex conjugation of a univariate polynomial. -/
def complexConjPoly (p : Polynomial ℂ) : Polynomial ℂ :=
  p.map (starRingEnd ℂ)

/-- Evaluation of the coefficientwise conjugate polynomial. -/
theorem complexConjPoly_eval (p : Polynomial ℂ) (z : ℂ) :
    (complexConjPoly p).eval z = star (p.eval (star z)) := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
      simp [complexConjPoly]
  | add p q hp hq =>
      simp only [complexConjPoly, Polynomial.map_add, Polynomial.eval_add]
      rw [show Polynomial.eval z (Polynomial.map (starRingEnd ℂ) p) =
          star (Polynomial.eval (star z) p) by simpa [complexConjPoly] using hp]
      rw [show Polynomial.eval z (Polynomial.map (starRingEnd ℂ) q) =
          star (Polynomial.eval (star z) q) by simpa [complexConjPoly] using hq]
      exact (map_add (starRingEnd ℂ) _ _).symm

/-- Polynomial whose evaluation is the Hermitian product of a polynomial vector at
conjugate arguments. -/
def complexVecHermitianPoly {N : ℕ} (F : Fin N → Polynomial ℂ) : Polynomial ℂ :=
  ∑ i : Fin N, complexConjPoly (F i) * F i

/-- Hermitian product on finite complex vectors, conjugate-linear in the first argument. -/
def complexVecHermitianEval {N : ℕ} (u v : Fin N → ℂ) : ℂ :=
  ∑ i : Fin N, star (u i) * v i

/-- Evaluation formula for the Hermitian product polynomial. -/
theorem complexVecHermitianPoly_eval {N : ℕ} (F : Fin N → Polynomial ℂ) (z : ℂ) :
    (complexVecHermitianPoly F).eval z =
      complexVecHermitianEval (fun i : Fin N => (F i).eval (star z))
        (fun i : Fin N => (F i).eval z) := by
  unfold complexVecHermitianPoly complexVecHermitianEval
  simp [Polynomial.eval_finset_sum, Polynomial.eval_mul, complexConjPoly_eval]

/-- Complexification of a real univariate polynomial. -/
def complexifyPoly (p : Polynomial ℝ) : Polynomial ℂ :=
  p.map (algebraMap ℝ ℂ)

/-- Real-coefficient complexified polynomials are fixed by coefficientwise conjugation. -/
theorem complexConjPoly_complexify (p : Polynomial ℝ) :
    complexConjPoly (complexifyPoly p) = complexifyPoly p := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
      simp [complexConjPoly, complexifyPoly]
  | add p q hp hq =>
      simp only [complexConjPoly, complexifyPoly, Polynomial.map_add]
      rw [show Polynomial.map (starRingEnd ℂ) (Polynomial.map (algebraMap ℝ ℂ) p) =
          Polynomial.map (algebraMap ℝ ℂ) p by
            simpa [complexConjPoly, complexifyPoly] using hp]
      rw [show Polynomial.map (starRingEnd ℂ) (Polynomial.map (algebraMap ℝ ℂ) q) =
          Polynomial.map (algebraMap ℝ ℂ) q by
            simpa [complexConjPoly, complexifyPoly] using hq]

/-- The Hermitian product polynomial of a complexified real polynomial vector is the
complexification of the real sum of squares. -/
theorem complexVecHermitianPoly_complexify {N : ℕ} (F : Fin N → Polynomial ℝ) :
    complexVecHermitianPoly (fun i : Fin N => complexifyPoly (F i)) =
      complexifyPoly (∑ i : Fin N, (F i) ^ 2) := by
  unfold complexVecHermitianPoly complexifyPoly
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show complexConjPoly (Polynomial.map (algebraMap ℝ ℂ) (F i)) =
      Polynomial.map (algebraMap ℝ ℂ) (F i) by
        simpa [complexifyPoly] using complexConjPoly_complexify (F i)]
  rw [Polynomial.map_pow]
  rw [pow_two]

/-- Evaluating a complexified real polynomial at a real point agrees with the real
value coerced to `ℂ`. -/
theorem complexifyPoly_eval_real (p : Polynomial ℝ) (t : ℝ) :
    (complexifyPoly p).eval (t : ℂ) = ((p.eval t : ℝ) : ℂ) := by
  induction p using Polynomial.induction_on' with
  | monomial n c => simp [complexifyPoly]
  | add p q hp hq =>
      unfold complexifyPoly at hp hq ⊢
      rw [Polynomial.map_add, Polynomial.eval_add, Polynomial.eval_add, hp, hq]
      norm_num

/-- Taking coordinatewise absolute values does not change the finite real Euclidean norm. -/
theorem vecNorm_abs {N : ℕ} (v : Fin N → ℝ) : vecNorm (fun i => |v i|) = vecNorm v := by
  unfold vecNorm vecSqNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [sq_abs]

/-- The complex spectral factor `1 + a^2 z^2`. -/
def complexSpectralFactor (a : ℝ) : Polynomial ℂ :=
  1 + Polynomial.C ((a : ℂ) ^ 2) * Polynomial.X ^ 2

/-- Complexifying the real spectral factor gives the complex spectral factor. -/
theorem complexify_real_spectral_factor (a : ℝ) :
    complexifyPoly (1 + Polynomial.C (a ^ 2) * Polynomial.X ^ 2) =
      complexSpectralFactor a := by
  unfold complexifyPoly complexSpectralFactor
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-- The spectral factor vanishes at `i/a`. -/
theorem complexSpectralFactor_eval_I_div {a : ℝ} (ha : a ≠ 0) :
    (complexSpectralFactor a).eval (Complex.I / (a : ℂ)) = 0 := by
  unfold complexSpectralFactor
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]
  field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast ha]
  rw [sq, Complex.I_mul_I]
  norm_num

/-- Complex conjugation sends `i/a` to `-i/a` for real `a`. -/
theorem star_I_div_real (a : ℝ) :
    star (Complex.I / (a : ℂ)) = -Complex.I / (a : ℂ) := by
  simp [div_eq_mul_inv]

/-- If the Hermitian product polynomial has the spectral factor `1 + a^2 z^2`,
then the evaluations at the two conjugate imaginary roots are Hermitian-orthogonal. -/
theorem complexHermitian_orthogonal_of_spectral_factor
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0) {Q : Polynomial ℂ}
    (hfac : complexVecHermitianPoly F = complexSpectralFactor a * Q) :
    complexVecHermitianEval (fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ)))
      (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))) = 0 := by
  have hzero : (complexVecHermitianPoly F).eval (Complex.I / (a : ℂ)) = 0 := by
    rw [hfac, Polynomial.eval_mul, complexSpectralFactor_eval_I_div ha, zero_mul]
  rw [complexVecHermitianPoly_eval] at hzero
  simpa [star_I_div_real] using hzero

/-- Multiplying a complex polynomial divisor by a nonzero scalar preserves divisibility. -/
theorem Polynomial.complex_C_mul_dvd_of_dvd {p q : Polynomial ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : p ∣ q) : Polynomial.C c * p ∣ q := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨Polynomial.C c⁻¹ * s, ?_⟩
  calc
    p * s = 1 * (p * s) := by simp
    _ = (Polynomial.C c * Polynomial.C c⁻¹) * (p * s) := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ hc]
      simp
    _ = Polynomial.C c * p * (Polynomial.C c⁻¹ * s) := by ring

/-- The two distinct complex linear factors at `z` and `-z` are coprime. -/
theorem Polynomial.isCoprime_X_sub_C_pos_neg_complex {z : ℂ} (hz : z ≠ 0) :
    IsCoprime (Polynomial.X - Polynomial.C z) (Polynomial.X - Polynomial.C (-z)) := by
  refine ⟨Polynomial.C (-(2 * z)⁻¹), Polynomial.C ((2 * z)⁻¹), ?_⟩
  apply Polynomial.funext
  intro x
  simp
  field_simp [hz]
  ring

/-- A complex polynomial with zeros at the two imaginary roots of `1 + a^2 z^2`
is divisible by the corresponding spectral factor. -/
theorem complexSpectralFactor_dvd_of_eval_roots
    {q : Polynomial ℂ} {a : ℝ} (ha : a ≠ 0)
    (hpos : q.eval (Complex.I / (a : ℂ)) = 0)
    (hneg : q.eval (-Complex.I / (a : ℂ)) = 0) :
    complexSpectralFactor a ∣ q := by
  let z : ℂ := Complex.I / (a : ℂ)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hz_ne : z ≠ 0 := by
    dsimp [z]
    exact div_ne_zero Complex.I_ne_zero haC
  have hpos_dvd : Polynomial.X - Polynomial.C z ∣ q := by
    rw [Polynomial.dvd_iff_isRoot]
    exact hpos
  have hneg_dvd : Polynomial.X - Polynomial.C (-z) ∣ q := by
    rw [Polynomial.dvd_iff_isRoot]
    change q.eval (-(Complex.I / (a : ℂ))) = 0
    rw [← neg_div]
    exact hneg
  have hprod : (Polynomial.X - Polynomial.C z) * (Polynomial.X - Polynomial.C (-z)) ∣ q :=
    (Polynomial.isCoprime_X_sub_C_pos_neg_complex hz_ne).mul_dvd hpos_dvd hneg_dvd
  have hfac : complexSpectralFactor a =
      Polynomial.C ((a : ℂ) ^ 2) *
        ((Polynomial.X - Polynomial.C z) * (Polynomial.X - Polynomial.C (-z))) := by
    apply Polynomial.funext
    intro w
    dsimp [complexSpectralFactor, z]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]
    field_simp [haC]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hfac]
  exact Polynomial.complex_C_mul_dvd_of_dvd (pow_ne_zero 2 haC) hprod

/-- Squared Euclidean norm of a finite complex vector, as a real number. -/
def complexVecSqNorm {N : ℕ} (v : Fin N → ℂ) : ℝ :=
  ∑ i : Fin N, Complex.normSq (v i)

/-- Euclidean norm of a finite complex vector. -/
def complexVecNorm {N : ℕ} (v : Fin N → ℂ) : ℝ :=
  Real.sqrt (complexVecSqNorm v)

theorem complexVecSqNorm_nonneg {N : ℕ} (v : Fin N → ℂ) :
    0 ≤ complexVecSqNorm v := by
  unfold complexVecSqNorm
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (v i)

theorem complexVecNorm_nonneg {N : ℕ} (v : Fin N → ℂ) : 0 ≤ complexVecNorm v := by
  unfold complexVecNorm
  exact Real.sqrt_nonneg _

theorem complexVecNorm_sq {N : ℕ} (v : Fin N → ℂ) :
    complexVecNorm v ^ 2 = complexVecSqNorm v := by
  unfold complexVecNorm
  exact Real.sq_sqrt (complexVecSqNorm_nonneg v)

/-- The Hermitian self-product is the squared Euclidean norm. -/
theorem complexVecHermitianEval_self {N : ℕ} (v : Fin N → ℂ) :
    complexVecHermitianEval v v = (complexVecSqNorm v : ℂ) := by
  unfold complexVecHermitianEval complexVecSqNorm
  have hcast := Complex.ofReal_sum Finset.univ (fun i : Fin N => Complex.normSq (v i))
  try rw [hcast]
  change (∑ i : Fin N, star (v i) * v i) =
    ∑ i : Fin N, ((Complex.normSq (v i) : ℝ) : ℂ)
  apply Finset.sum_congr rfl
  intro i _
  simpa [mul_comm] using Complex.mul_conj (v i)

theorem complexVecSqNorm_eq_vecSqNorm_norm {N : ℕ} (v : Fin N → ℂ) :
    complexVecSqNorm v = vecSqNorm (fun i : Fin N => ‖v i‖) := by
  unfold complexVecSqNorm vecSqNorm
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.normSq_eq_norm_sq]

theorem complexVecNorm_eq_vecNorm_norm {N : ℕ} (v : Fin N → ℂ) :
    complexVecNorm v = vecNorm (fun i : Fin N => ‖v i‖) := by
  unfold complexVecNorm vecNorm
  rw [complexVecSqNorm_eq_vecSqNorm_norm]

/-- The complex norm of a complexified real polynomial vector at a real point is the real
Euclidean norm of the original evaluations. -/
theorem complexVecNorm_complexify_eval_real {N : ℕ} (F : Fin N → Polynomial ℝ) (t : ℝ) :
    complexVecNorm (fun i => (complexifyPoly (F i)).eval (t : ℂ)) =
      vecNorm (fun i => (F i).eval t) := by
  rw [complexVecNorm_eq_vecNorm_norm]
  rw [show (fun i : Fin N => ‖(complexifyPoly (F i)).eval (t : ℂ)‖) =
      fun i : Fin N => |(F i).eval t| by
    funext i
    rw [complexifyPoly_eval_real]
    simp]
  exact vecNorm_abs _

/-- Complexification commutes with univariate polynomial derivative. -/
theorem complexifyPoly_derivative (p : Polynomial ℝ) :
    Polynomial.derivative (complexifyPoly p) = complexifyPoly (Polynomial.derivative p) := by
  exact Polynomial.derivative_map p (algebraMap ℝ ℂ)

/-- The complex norm of the derivative-at-zero vector of complexified real polynomials is
its real Euclidean norm. -/
theorem complexVecNorm_complexify_derivative_eval_zero {N : ℕ} (F : Fin N → Polynomial ℝ) :
    complexVecNorm (fun i => (Polynomial.derivative (complexifyPoly (F i))).eval 0) =
      vecNorm (fun i => (Polynomial.derivative (F i)).eval 0) := by
  rw [show (fun i : Fin N => (Polynomial.derivative (complexifyPoly (F i))).eval 0) =
      fun i : Fin N => (complexifyPoly (Polynomial.derivative (F i))).eval (0 : ℂ) by
    funext i
    rw [complexifyPoly_derivative]]
  simpa using complexVecNorm_complexify_eval_real (fun i : Fin N => Polynomial.derivative (F i)) 0

/-- Triangle inequality for the finite complex Euclidean norm. -/
theorem complexVecNorm_add_le {N : ℕ} (u v : Fin N → ℂ) :
    complexVecNorm (fun i : Fin N => u i + v i) ≤ complexVecNorm u + complexVecNorm v := by
  rw [complexVecNorm_eq_vecNorm_norm, complexVecNorm_eq_vecNorm_norm,
    complexVecNorm_eq_vecNorm_norm]
  refine (vecNorm_le_of_vecSqNorm_le
    (vecNorm_nonneg (fun i : Fin N => ‖u i‖ + ‖v i‖)) ?_).trans
      (vecNorm_add_le (fun i : Fin N => ‖u i‖) (fun i : Fin N => ‖v i‖))
  rw [vecNorm_sq]
  unfold vecSqNorm
  apply Finset.sum_le_sum
  intro i _
  have htri : ‖u i + v i‖ ≤ ‖u i‖ + ‖v i‖ := norm_add_le (u i) (v i)
  have hleft : 0 ≤ ‖u i + v i‖ := norm_nonneg _
  have hright : 0 ≤ ‖u i‖ + ‖v i‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- Scalar multiplication for the finite complex Euclidean norm. -/
theorem complexVecNorm_smul {N : ℕ} (c : ℂ) (v : Fin N → ℂ) :
    complexVecNorm (fun i : Fin N => c * v i) = ‖c‖ * complexVecNorm v := by
  rw [complexVecNorm_eq_vecNorm_norm, complexVecNorm_eq_vecNorm_norm]
  have hscale := vecNorm_smul_nonneg (N := N) ‖c‖ (norm_nonneg c) (fun i : Fin N => ‖v i‖)
  rw [show (fun i : Fin N => ‖c * v i‖) = fun i : Fin N => ‖c‖ * ‖v i‖ by
    funext i
    rw [norm_mul]]
  exact hscale

/-- Negation preserves the finite complex Euclidean norm. -/
theorem complexVecNorm_neg {N : ℕ} (v : Fin N → ℂ) :
    complexVecNorm (fun i : Fin N => -v i) = complexVecNorm v := by
  rw [show (fun i : Fin N => -v i) = fun i : Fin N => (-1 : ℂ) * v i by
    funext i
    ring]
  rw [complexVecNorm_smul]
  norm_num

/-- Matrix-vector multiplication on finite complex vectors. -/
def complexMatVec {N : ℕ} (J : Fin N → Fin N → ℂ) (v : Fin N → ℂ) : Fin N → ℂ :=
  fun i => ∑ j : Fin N, J i j * v j

/-- A complex matrix acts isometrically for the finite Euclidean norm. -/
def complexMatIsometry {N : ℕ} (J : Fin N → Fin N → ℂ) : Prop :=
  ∀ v : Fin N → ℂ, complexVecNorm (complexMatVec J v) = complexVecNorm v

/-- A complex matrix preserves the Hermitian self-product. -/
def complexMatHermitianIsometry {N : ℕ} (J : Fin N → Fin N → ℂ) : Prop :=
  ∀ v : Fin N → ℂ,
    complexVecHermitianEval (complexMatVec J v) (complexMatVec J v) =
      complexVecHermitianEval v v

/-- Preserving the Hermitian self-product implies preserving the finite Euclidean norm. -/
theorem complexMatIsometry_of_hermitian {N : ℕ} {J : Fin N → Fin N → ℂ}
    (hJ : complexMatHermitianIsometry J) : complexMatIsometry J := by
  intro v
  unfold complexVecNorm
  congr 1
  apply Complex.ofReal_injective
  calc
    (complexVecSqNorm (complexMatVec J v) : ℂ) =
        complexVecHermitianEval (complexMatVec J v) (complexMatVec J v) := by
          rw [complexVecHermitianEval_self]
    _ = complexVecHermitianEval v v := hJ v
    _ = (complexVecSqNorm v : ℂ) := by
          rw [complexVecHermitianEval_self]

/-- The scalar `i*a` has norm `a` for `a >= 0`. -/
theorem norm_I_mul_real_of_nonneg {a : ℝ} (ha : 0 ≤ a) :
    ‖Complex.I * (a : ℂ)‖ = a := by
  have hsq : ‖Complex.I * (a : ℂ)‖ ^ 2 = a ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]
    ring
  nlinarith [norm_nonneg (Complex.I * (a : ℂ))]

/-- Coordinate polynomial for applying a fixed complex matrix to a polynomial vector. -/
def complexMatVecPoly {N : ℕ} (J : Fin N → Fin N → ℂ)
    (F : Fin N → Polynomial ℂ) : Fin N → Polynomial ℂ :=
  fun i => ∑ j : Fin N, Polynomial.C (J i j) * F j

/-- The coordinate numerator `(I - i*a*z*J)F` used in factor stripping. -/
def complexStripNumerator {N : ℕ} (a : ℝ) (J : Fin N → Fin N → ℂ)
    (F : Fin N → Polynomial ℂ) : Fin N → Polynomial ℂ :=
  fun i => F i - Polynomial.C (Complex.I * (a : ℂ)) * Polynomial.X * complexMatVecPoly J F i

/-- Evaluating a matrix-applied polynomial vector is matrix multiplication on the
evaluated vector. -/
theorem complexMatVecPoly_eval {N : ℕ} (J : Fin N → Fin N → ℂ)
    (F : Fin N → Polynomial ℂ) (z : ℂ) :
    (fun i : Fin N => (complexMatVecPoly J F i).eval z) =
      complexMatVec J (fun i : Fin N => (F i).eval z) := by
  funext i
  unfold complexMatVecPoly complexMatVec
  simp [Polynomial.eval_finset_sum, Polynomial.eval_mul]

/-- Evaluation formula for the factor-stripping numerator. -/
theorem complexStripNumerator_eval {N : ℕ} (a : ℝ) (J : Fin N → Fin N → ℂ)
    (F : Fin N → Polynomial ℂ) (z : ℂ) :
    (fun i : Fin N => (complexStripNumerator a J F i).eval z) =
      fun i : Fin N => (F i).eval z - Complex.I * (a : ℂ) * z *
        complexMatVec J (fun j : Fin N => (F j).eval z) i := by
  funext i
  unfold complexStripNumerator complexMatVecPoly complexMatVec
  simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_finset_sum]

/-- If `J` has the two prescribed eigenspace values at the imaginary roots, then every
coordinate of `(I - i*a*z*J)F` is divisible by `1 + a^2 z^2`. -/
theorem complexSpectralFactor_dvd_stripNumerator
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0)
    {J : Fin N → Fin N → ℂ}
    (hposEig : complexMatVec J (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))) =
      fun i : Fin N => - (F i).eval (Complex.I / (a : ℂ)))
    (hnegEig : complexMatVec J (fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) =
      fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ)))
    (i : Fin N) :
    complexSpectralFactor a ∣ complexStripNumerator a J F i := by
  apply complexSpectralFactor_dvd_of_eval_roots ha
  · have hvec := congrFun (complexStripNumerator_eval a J F (Complex.I / (a : ℂ))) i
    rw [hvec]
    have hi := congrFun hposEig i
    rw [hi]
    field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast ha]
    rw [Complex.I_sq]
    ring
  · have hvec := congrFun (complexStripNumerator_eval a J F (-Complex.I / (a : ℂ))) i
    rw [hvec]
    have hi := congrFun hnegEig i
    rw [hi]
    field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast ha]
    rw [Complex.I_sq]
    ring

/-- The coordinate vector `(I + i*a*z*J)F`. -/
def complexPlusFactorApply {N : ℕ} (a : ℝ) (J : Fin N → Fin N → ℂ)
    (F : Fin N → Polynomial ℂ) : Fin N → Polynomial ℂ :=
  fun i => F i + Polynomial.C (Complex.I * (a : ℂ)) * Polynomial.X * complexMatVecPoly J F i

/-- Coordinate form of the matrix identity `J^2 = I`. -/
def complexMatInvolutive {N : ℕ} (J : Fin N → Fin N → ℂ) : Prop :=
  ∀ i k : Fin N, (∑ j : Fin N, J i j * J j k) = if i = k then 1 else 0

/-- The identity matrix on finite complex vectors. -/
def complexIdentityMat {N : ℕ} : Fin N → Fin N → ℂ :=
  fun i j => if i = j then 1 else 0

/-- The identity matrix acts as the identity on finite vectors. -/
theorem complexMatVec_identity {N : ℕ} (v : Fin N → ℂ) :
    complexMatVec complexIdentityMat v = v := by
  funext i
  unfold complexMatVec complexIdentityMat
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [if_neg (Ne.symm hji)]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The identity matrix is involutive. -/
theorem complexIdentityMat_involutive {N : ℕ} :
    complexMatInvolutive (complexIdentityMat : Fin N → Fin N → ℂ) := by
  intro i k
  unfold complexIdentityMat
  by_cases hik : i = k
  · subst k
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      simp [if_neg hji, if_neg (Ne.symm hji)]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  · rw [Finset.sum_eq_zero]
    · simp [if_neg hik]
    · intro j _hj
      by_cases hji : j = i
      · subst j
        simp [if_neg hik]
      · simp [if_neg (Ne.symm hji)]

/-- The identity matrix preserves the Hermitian self-product. -/
theorem complexIdentityMat_hermitian_isometry {N : ℕ} :
    complexMatHermitianIsometry (complexIdentityMat : Fin N → Fin N → ℂ) := by
  intro v
  rw [complexMatVec_identity]

/-- Applying a matrix polynomial operator to a scalar multiple of a vector lets the
scalar factor out of the finite matrix-vector sum. -/
theorem complexMatVecPoly_scalar_mul {N : ℕ} (J : Fin N → Fin N → ℂ)
    (s : Polynomial ℂ) (F : Fin N → Polynomial ℂ) :
    complexMatVecPoly J (fun i : Fin N => s * F i) =
      fun i : Fin N => s * complexMatVecPoly J F i := by
  funext i
  unfold complexMatVecPoly
  simp [Finset.mul_sum, mul_assoc, mul_comm]

/-- Matrix-vector application is additive on polynomial vectors. -/
theorem complexMatVecPoly_add {N : ℕ} (J : Fin N → Fin N → ℂ)
    (F G : Fin N → Polynomial ℂ) :
    complexMatVecPoly J (fun i : Fin N => F i + G i) =
      fun i : Fin N => complexMatVecPoly J F i + complexMatVecPoly J G i := by
  funext i
  unfold complexMatVecPoly
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Matrix-vector application is subtractive on polynomial vectors. -/
theorem complexMatVecPoly_sub {N : ℕ} (J : Fin N → Fin N → ℂ)
    (F G : Fin N → Polynomial ℂ) :
    complexMatVecPoly J (fun i : Fin N => F i - G i) =
      fun i : Fin N => complexMatVecPoly J F i - complexMatVecPoly J G i := by
  funext i
  unfold complexMatVecPoly
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Cancellation by a nonzero complex polynomial on the left. -/
theorem Polynomial.complex_mul_left_cancel_of_ne_zero {a b c : Polynomial ℂ} (ha : a ≠ 0)
    (h : a * b = a * c) : b = c := by
  have hzero : a * (b - c) = 0 := by
    rw [mul_sub, h]
    ring
  have hor := mul_eq_zero.mp hzero
  cases hor with
  | inl hz => exact False.elim (ha hz)
  | inr hz => exact sub_eq_zero.mp hz

/-- If `J^2 = I`, applying `J` twice to a polynomial vector gives the original vector. -/
theorem complexMatVecPoly_apply_twice_of_involutive {N : ℕ}
    {J : Fin N → Fin N → ℂ} (hJ : complexMatInvolutive J)
    (F : Fin N → Polynomial ℂ) :
    complexMatVecPoly J (complexMatVecPoly J F) = F := by
  funext i
  unfold complexMatVecPoly
  unfold complexMatInvolutive at hJ
  calc
    (∑ j : Fin N, Polynomial.C (J i j) *
        (∑ k : Fin N, Polynomial.C (J j k) * F k))
        = ∑ k : Fin N, Polynomial.C (∑ j : Fin N, J i j * J j k) * F k := by
          rw [show (∑ j : Fin N, Polynomial.C (J i j) *
              (∑ k : Fin N, Polynomial.C (J j k) * F k)) =
              ∑ j : Fin N, ∑ k : Fin N,
                Polynomial.C (J i j) * (Polynomial.C (J j k) * F k) by
                apply Finset.sum_congr rfl
                intro j _
                rw [Finset.mul_sum]]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [show (∑ j : Fin N, Polynomial.C (J i j) *
              (Polynomial.C (J j k) * F k)) =
              (∑ j : Fin N, Polynomial.C (J i j * J j k)) * F k by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro j _
                rw [← mul_assoc, ← Polynomial.C_mul]]
          rw [show (∑ j : Fin N, Polynomial.C (J i j * J j k)) =
              Polynomial.C (∑ j : Fin N, J i j * J j k) by
                rw [map_sum]]
    _ = ∑ k : Fin N, Polynomial.C (if i = k then (1 : ℂ) else 0) * F k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hJ i k]
    _ = F i := by
          rw [Finset.sum_eq_single i]
          · simp
          · intro k _hk hki
            simp [if_neg (Ne.symm hki)]
          · intro hi
            exact False.elim (hi (Finset.mem_univ i))

/-- The product `(I + i*a*z*J)(I - i*a*z*J)` is the scalar spectral factor when
`J^2 = I`. -/
theorem complexPlusFactorApply_stripNumerator_of_involutive {N : ℕ}
    (F : Fin N → Polynomial ℂ) (a : ℝ) {J : Fin N → Fin N → ℂ}
    (hJ : complexMatInvolutive J) :
    complexPlusFactorApply a J (complexStripNumerator a J F) =
      fun i : Fin N => complexSpectralFactor a * F i := by
  let P : Polynomial ℂ := Polynomial.C (Complex.I * (a : ℂ)) * Polynomial.X
  have hJstrip : complexMatVecPoly J (complexStripNumerator a J F) =
      fun i : Fin N => complexMatVecPoly J F i - P * F i := by
    unfold complexStripNumerator
    rw [show (fun i : Fin N => F i - Polynomial.C (Complex.I * (a : ℂ)) *
          Polynomial.X * complexMatVecPoly J F i) =
        fun i : Fin N => F i - P * complexMatVecPoly J F i by
      funext i
      simp [P]]
    rw [complexMatVecPoly_sub, complexMatVecPoly_scalar_mul,
      complexMatVecPoly_apply_twice_of_involutive hJ]
  funext i
  have hi := congrFun hJstrip i
  unfold complexPlusFactorApply
  change complexStripNumerator a J F i +
      Polynomial.C (Complex.I * (a : ℂ)) * Polynomial.X *
        complexMatVecPoly J (complexStripNumerator a J F) i =
    complexSpectralFactor a * F i
  rw [hi]
  unfold complexStripNumerator
  simp [P, complexSpectralFactor]
  ring_nf
  rw [← Polynomial.C_pow, Complex.I_sq]
  simp

/-- Derivative at zero of the plus factor `(I + i*a*z*J)G`. -/
theorem complexPlusFactorApply_derivative_eval_zero {N : ℕ}
    (G : Fin N → Polynomial ℂ) (a : ℝ) (J : Fin N → Fin N → ℂ) :
    (fun i : Fin N =>
      (Polynomial.derivative (complexPlusFactorApply a J G i)).eval 0) =
      fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
        Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i := by
  funext i
  unfold complexPlusFactorApply complexMatVecPoly complexMatVec
  rw [Polynomial.derivative_add, Polynomial.eval_add]
  rw [Polynomial.derivative_mul, Polynomial.eval_add]
  simp [Polynomial.derivative_mul, Polynomial.eval_finset_sum, Polynomial.eval_mul]

/-- Derivative at zero of the minus numerator `(I - i*a*z*J)F`. -/
theorem complexStripNumerator_derivative_eval_zero {N : ℕ}
    (F : Fin N → Polynomial ℂ) (a : ℝ) (J : Fin N → Fin N → ℂ) :
    (fun i : Fin N =>
      (Polynomial.derivative (complexStripNumerator a J F i)).eval 0) =
      fun i : Fin N => (Polynomial.derivative (F i)).eval 0 -
        Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (F j).eval 0) i := by
  funext i
  unfold complexStripNumerator complexMatVecPoly complexMatVec
  rw [Polynomial.derivative_sub, Polynomial.eval_sub]
  rw [Polynomial.derivative_mul, Polynomial.eval_add]
  simp [Polynomial.derivative_mul, Polynomial.eval_finset_sum, Polynomial.eval_mul]

/-- Algebraic factor-stripping reconstruction: if the numerator is divisible by the
spectral factor coordinatewise and `J^2 = I`, then the quotient vector reconstructs
`F` through `(I + i*a*z*J)`. -/
theorem exists_complexSpectralFactor_stripQuotient
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0)
    {J : Fin N → Fin N → ℂ} (hJ : complexMatInvolutive J)
    (hposEig : complexMatVec J (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))) =
      fun i : Fin N => - (F i).eval (Complex.I / (a : ℂ)))
    (hnegEig : complexMatVec J (fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) =
      fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) :
    ∃ G : Fin N → Polynomial ℂ,
      (∀ i : Fin N, complexStripNumerator a J F i = complexSpectralFactor a * G i) ∧
        complexPlusFactorApply a J G = F := by
  classical
  have hdiv : ∀ i : Fin N, complexSpectralFactor a ∣ complexStripNumerator a J F i :=
    complexSpectralFactor_dvd_stripNumerator F ha hposEig hnegEig
  let G : Fin N → Polynomial ℂ := fun i => (hdiv i).choose
  refine ⟨G, ?_, ?_⟩
  · intro i
    exact (hdiv i).choose_spec
  · have hplus := complexPlusFactorApply_stripNumerator_of_involutive F a hJ
    have hG : complexStripNumerator a J F = fun i : Fin N => complexSpectralFactor a * G i := by
      funext i
      exact (hdiv i).choose_spec
    rw [hG] at hplus
    rw [show complexPlusFactorApply a J (fun i : Fin N => complexSpectralFactor a * G i) =
        fun i : Fin N => complexSpectralFactor a * complexPlusFactorApply a J G i by
      funext i
      unfold complexPlusFactorApply
      rw [complexMatVecPoly_scalar_mul]
      ring] at hplus
    have hsf_ne : complexSpectralFactor a ≠ 0 := by
      intro hzero
      have heval := congrArg (fun p : Polynomial ℂ => p.eval 0) hzero
      simp [complexSpectralFactor] at heval
    funext i
    exact Polynomial.complex_mul_left_cancel_of_ne_zero hsf_ne (congrFun hplus i)

/-- Packaged algebraic factor stripping with the derivative identity needed for the
polygon-bound induction. -/
theorem exists_complexSpectralFactor_stripQuotient_with_derivative
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0)
    {J : Fin N → Fin N → ℂ} (hJ : complexMatInvolutive J)
    (hposEig : complexMatVec J (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))) =
      fun i : Fin N => - (F i).eval (Complex.I / (a : ℂ)))
    (hnegEig : complexMatVec J (fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) =
      fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) :
    ∃ G : Fin N → Polynomial ℂ,
      (∀ i : Fin N, complexStripNumerator a J F i = complexSpectralFactor a * G i) ∧
        complexPlusFactorApply a J G = F ∧
        (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) =
          fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
            Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i := by
  obtain ⟨G, hstrip, hrecon⟩ :=
    exists_complexSpectralFactor_stripQuotient F ha hJ hposEig hnegEig
  refine ⟨G, hstrip, hrecon, ?_⟩
  have hder := congrArg
    (fun H : Fin N → Polynomial ℂ =>
      fun i : Fin N => (Polynomial.derivative (H i)).eval 0) hrecon
  exact hder.symm.trans (complexPlusFactorApply_derivative_eval_zero G a J)

/-- The derivative norm estimate supplied by one factor-stripping step. -/
theorem complex_derivative_norm_le_of_factor_derivative_identity {N : ℕ}
    {F G : Fin N → Polynomial ℂ} {a : ℝ} (ha : 0 ≤ a) {J : Fin N → Fin N → ℂ}
    (hIso : complexMatIsometry J)
    (hder : (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) =
      fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
        Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i) :
    complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤
      complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
        a * complexVecNorm (fun i : Fin N => (G i).eval 0) := by
  rw [hder]
  calc
    complexVecNorm (fun i : Fin N =>
        (Polynomial.derivative (G i)).eval 0 +
          Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i)
        ≤ complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
            complexVecNorm (fun i : Fin N =>
              Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i) :=
          complexVecNorm_add_le _ _
    _ = complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
          a * complexVecNorm (fun i : Fin N => (G i).eval 0) := by
          rw [show (fun i : Fin N =>
                Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i) =
              fun i : Fin N => (Complex.I * (a : ℂ)) *
                complexMatVec J (fun j : Fin N => (G j).eval 0) i by
                funext i
                ring]
          rw [complexVecNorm_smul, hIso, norm_I_mul_real_of_nonneg ha]

/-- Reverse triangle form of the derivative contribution from one stripped factor. -/
theorem complex_factor_contribution_sub_norm_le_derivative {N : ℕ}
    {F G : Fin N → Polynomial ℂ} {a : ℝ} (ha : 0 ≤ a) {J : Fin N → Fin N → ℂ}
    (hIso : complexMatIsometry J)
    (hder : (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) =
      fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
        Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i) :
    a * complexVecNorm (fun i : Fin N => (G i).eval 0) -
        complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) ≤
      complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) := by
  let A : Fin N → ℂ := fun i => (Polynomial.derivative (G i)).eval 0
  let B : Fin N → ℂ := fun i =>
    Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i
  let D : Fin N → ℂ := fun i => (Polynomial.derivative (F i)).eval 0
  have hD : D = fun i : Fin N => A i + B i := by
    dsimp [D, A, B]
    exact hder
  have hBnorm : complexVecNorm B = a * complexVecNorm (fun i : Fin N => (G i).eval 0) := by
    dsimp [B]
    rw [show (fun i : Fin N =>
          Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i) =
        fun i : Fin N => (Complex.I * (a : ℂ)) *
          complexMatVec J (fun j : Fin N => (G j).eval 0) i by
          funext i
          ring]
    rw [complexVecNorm_smul, hIso, norm_I_mul_real_of_nonneg ha]
  have hB_le : complexVecNorm B ≤ complexVecNorm D + complexVecNorm A := by
    calc
      complexVecNorm B = complexVecNorm (fun i : Fin N => D i + -A i) := by
        congr 1
        funext i
        rw [hD]
        ring
      _ ≤ complexVecNorm D + complexVecNorm (fun i : Fin N => -A i) :=
        complexVecNorm_add_le _ _
      _ = complexVecNorm D + complexVecNorm A := by rw [complexVecNorm_neg]
  dsimp [A, D] at hB_le
  rw [hBnorm] at hB_le
  linarith

/-- Packaged factor stripping with the derivative norm estimate used in the polygon
induction. -/
theorem exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bound
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0) (ha_nonneg : 0 ≤ a)
    {J : Fin N → Fin N → ℂ} (hJ : complexMatInvolutive J) (hIso : complexMatIsometry J)
    (hposEig : complexMatVec J (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))) =
      fun i : Fin N => - (F i).eval (Complex.I / (a : ℂ)))
    (hnegEig : complexMatVec J (fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) =
      fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) :
    ∃ G : Fin N → Polynomial ℂ,
      (∀ i : Fin N, complexStripNumerator a J F i = complexSpectralFactor a * G i) ∧
        complexPlusFactorApply a J G = F ∧
        ((fun i : Fin N => (Polynomial.derivative (F i)).eval 0) =
          fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
            Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i) ∧
        complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
            a * complexVecNorm (fun i : Fin N => (G i).eval 0) := by
  obtain ⟨G, hstrip, hrecon, hder⟩ :=
    exists_complexSpectralFactor_stripQuotient_with_derivative F ha hJ hposEig hnegEig
  refine ⟨G, hstrip, hrecon, hder, ?_⟩
  exact complex_derivative_norm_le_of_factor_derivative_identity ha_nonneg hIso hder

/-- Packaged factor stripping with both triangle-inequality derivative estimates. -/
theorem exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bounds
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0) (ha_nonneg : 0 ≤ a)
    {J : Fin N → Fin N → ℂ} (hJ : complexMatInvolutive J) (hIso : complexMatIsometry J)
    (hposEig : complexMatVec J (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))) =
      fun i : Fin N => - (F i).eval (Complex.I / (a : ℂ)))
    (hnegEig : complexMatVec J (fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) =
      fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) :
    ∃ G : Fin N → Polynomial ℂ,
      (∀ i : Fin N, complexStripNumerator a J F i = complexSpectralFactor a * G i) ∧
        complexPlusFactorApply a J G = F ∧
        ((fun i : Fin N => (Polynomial.derivative (F i)).eval 0) =
          fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
            Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i) ∧
        complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
            a * complexVecNorm (fun i : Fin N => (G i).eval 0) ∧
        a * complexVecNorm (fun i : Fin N => (G i).eval 0) -
            complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) := by
  obtain ⟨G, hstrip, hrecon, hder, hupper⟩ :=
    exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bound F ha ha_nonneg hJ hIso
      hposEig hnegEig
  refine ⟨G, hstrip, hrecon, hder, hupper, ?_⟩
  exact complex_factor_contribution_sub_norm_le_derivative ha_nonneg hIso hder

/-- Packaged factor stripping with both derivative estimates, using Hermitian isometry. -/
theorem exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bounds_of_hermitian
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0) (ha_nonneg : 0 ≤ a)
    {J : Fin N → Fin N → ℂ} (hJ : complexMatInvolutive J)
    (hHerm : complexMatHermitianIsometry J)
    (hposEig : complexMatVec J (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))) =
      fun i : Fin N => - (F i).eval (Complex.I / (a : ℂ)))
    (hnegEig : complexMatVec J (fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) =
      fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) :
    ∃ G : Fin N → Polynomial ℂ,
      (∀ i : Fin N, complexStripNumerator a J F i = complexSpectralFactor a * G i) ∧
        complexPlusFactorApply a J G = F ∧
        ((fun i : Fin N => (Polynomial.derivative (F i)).eval 0) =
          fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
            Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i) ∧
        complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
            a * complexVecNorm (fun i : Fin N => (G i).eval 0) ∧
        a * complexVecNorm (fun i : Fin N => (G i).eval 0) -
            complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) := by
  exact exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bounds F ha ha_nonneg hJ
    (complexMatIsometry_of_hermitian hHerm) hposEig hnegEig

/-- Packaged factor stripping with the derivative norm estimate, using Hermitian
isometry as the matrix hypothesis. -/
theorem exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bound_of_hermitian
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0) (ha_nonneg : 0 ≤ a)
    {J : Fin N → Fin N → ℂ} (hJ : complexMatInvolutive J)
    (hHerm : complexMatHermitianIsometry J)
    (hposEig : complexMatVec J (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))) =
      fun i : Fin N => - (F i).eval (Complex.I / (a : ℂ)))
    (hnegEig : complexMatVec J (fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) =
      fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) :
    ∃ G : Fin N → Polynomial ℂ,
      (∀ i : Fin N, complexStripNumerator a J F i = complexSpectralFactor a * G i) ∧
        complexPlusFactorApply a J G = F ∧
        ((fun i : Fin N => (Polynomial.derivative (F i)).eval 0) =
          fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
            Complex.I * (a : ℂ) * complexMatVec J (fun j : Fin N => (G j).eval 0) i) ∧
        complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
            a * complexVecNorm (fun i : Fin N => (G i).eval 0) := by
  exact exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bound F ha ha_nonneg hJ
    (complexMatIsometry_of_hermitian hHerm) hposEig hnegEig

/-- Real polynomial-vector norm identities with a factor `1 + a^2 t^2` give the
Hermitian orthogonality at the conjugate imaginary roots after complexification. -/
theorem complexHermitian_orthogonal_of_real_spectral_factor
    {N : ℕ} (F : Fin N → Polynomial ℝ) {a : ℝ} (ha : a ≠ 0) {Q : Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.C (a ^ 2) * Polynomial.X ^ 2) * Q) :
    complexVecHermitianEval
        (fun i : Fin N => (complexifyPoly (F i)).eval (-Complex.I / (a : ℂ)))
        (fun i : Fin N => (complexifyPoly (F i)).eval (Complex.I / (a : ℂ))) = 0 := by
  have hfac : complexVecHermitianPoly (fun i : Fin N => complexifyPoly (F i)) =
      complexSpectralFactor a * complexifyPoly Q := by
    rw [complexVecHermitianPoly_complexify, hNorm]
    unfold complexifyPoly
    rw [Polynomial.map_mul]
    rw [show Polynomial.map (algebraMap ℝ ℂ)
        (1 + Polynomial.C (a ^ 2) * Polynomial.X ^ 2) = complexSpectralFactor a by
      simpa [complexifyPoly] using complexify_real_spectral_factor a]
  exact complexHermitian_orthogonal_of_spectral_factor
    (fun i : Fin N => complexifyPoly (F i)) ha hfac

end ScaledRobinson
end OptimalConvergenceRates

end
