/-
  OptimalConvergenceRates/ScaledRobinson/HomogenizationSpectralReflection.lean

  Explicit finite-dimensional complex reflections used by the spectral-factor
  stripping argument.
-/
import OptimalConvergenceRates.ScaledRobinson.HomogenizationSpectral

open MvPolynomial Finset


noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- A complex vector with all coordinates zero has zero squared norm. -/
theorem complexVecSqNorm_zero {N : ℕ} {v : Fin N → ℂ} (hv : ∀ i, v i = 0) :
    complexVecSqNorm v = 0 := by
  unfold complexVecSqNorm
  apply Finset.sum_eq_zero
  intro i _
  rw [hv i]
  simp

/-- The finite complex squared norm vanishes exactly on the zero vector. -/
theorem complexVecSqNorm_eq_zero_iff {N : ℕ} {v : Fin N → ℂ} :
    complexVecSqNorm v = 0 ↔ ∀ i, v i = 0 := by
  constructor
  · intro h i
    have hle : Complex.normSq (v i) ≤ complexVecSqNorm v := by
      unfold complexVecSqNorm
      exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
    have hi : Complex.normSq (v i) = 0 := by
      have hnon := Complex.normSq_nonneg (v i)
      rw [h] at hle
      linarith
    exact Complex.normSq_eq_zero.mp hi
  · intro h
    exact complexVecSqNorm_zero h

/-- The Householder reflection through the Hermitian orthogonal complement of `u`. -/
def complexHouseholderMat {N : ℕ} (u : Fin N → ℂ) : Fin N → Fin N → ℂ :=
  fun i j => (if i = j then 1 else 0) -
    (2 : ℂ) / (complexVecSqNorm u : ℂ) * u i * star (u j)

/-- Coordinate formula for the Householder reflection. -/
theorem complexHouseholderMatVec {N : ℕ} (u v : Fin N → ℂ) :
    complexMatVec (complexHouseholderMat u) v =
      fun i : Fin N => v i - ((2 : ℂ) / (complexVecSqNorm u : ℂ)) * u i *
        complexVecHermitianEval u v := by
  funext i
  unfold complexMatVec complexHouseholderMat complexVecHermitianEval
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hfirst : (∑ j : Fin N, (if i = j then 1 else 0) * v j) = v i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _hj hji
      simp [ite_eq_right (Ne.symm hji)]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [hfirst]
  congr 1
  rw [show (∑ x : Fin N, (2 : ℂ) / ↑(complexVecSqNorm u) * u i * star (u x) * v x) =
      ∑ x : Fin N, ((2 : ℂ) / ↑(complexVecSqNorm u) * u i) * (star (u x) * v x) by
    congr 1
    ext x
    ring]
  rw [Finset.mul_sum]

/-- Conjugate symmetry of the custom Hermitian product. -/
theorem complexVecHermitianEval_conj_symm {N : ℕ} (u v : Fin N → ℂ) :
    complexVecHermitianEval v u = star (complexVecHermitianEval u v) := by
  unfold complexVecHermitianEval
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

/-- Applying a Householder reflection in the second Hermitian-product argument. -/
theorem complexVecHermitianEval_householder_right_general {N : ℕ}
    (u w v : Fin N → ℂ) :
    complexVecHermitianEval w (complexMatVec (complexHouseholderMat u) v) =
      complexVecHermitianEval w v - ((2 : ℂ) / (complexVecSqNorm u : ℂ)) *
        complexVecHermitianEval w u * complexVecHermitianEval u v := by
  rw [complexHouseholderMatVec]
  unfold complexVecHermitianEval
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  calc
    (∑ x : Fin N, star (w x) *
        ((2 : ℂ) / ↑(complexVecSqNorm u) * u x * ∑ i : Fin N, star (u i) * v i))
        = ∑ x : Fin N, (((2 : ℂ) / ↑(complexVecSqNorm u)) * (star (w x) * u x)) *
            (∑ i : Fin N, star (u i) * v i) := by
          congr 1
          ext x
          ring
    _ = (∑ x : Fin N, ((2 : ℂ) / ↑(complexVecSqNorm u)) * (star (w x) * u x)) *
            (∑ i : Fin N, star (u i) * v i) := by rw [Finset.sum_mul]
    _ = (((2 : ℂ) / ↑(complexVecSqNorm u)) * (∑ x : Fin N, star (w x) * u x)) *
            (∑ i : Fin N, star (u i) * v i) := by
          congr 1
          rw [Finset.mul_sum]
    _ = (2 / ↑(complexVecSqNorm u)) * (∑ x : Fin N, star (w x) * u x) *
            (∑ i : Fin N, star (u i) * v i) := by ring

/-- Applying a Householder reflection in the first Hermitian-product argument. -/
theorem complexVecHermitianEval_householder_left_general {N : ℕ}
    (u v w : Fin N → ℂ) :
    complexVecHermitianEval (complexMatVec (complexHouseholderMat u) v) w =
      complexVecHermitianEval v w - ((2 : ℂ) / (complexVecSqNorm u : ℂ)) *
        star (complexVecHermitianEval u v) * complexVecHermitianEval u w := by
  rw [complexVecHermitianEval_conj_symm]
  rw [complexVecHermitianEval_householder_right_general]
  rw [complexVecHermitianEval_conj_symm w v]
  rw [complexVecHermitianEval_conj_symm w u]
  simp
  ring

/-- A nonzero vector is sent to its negative by its Householder reflection. -/
theorem complexHouseholderMatVec_self {N : ℕ} {u : Fin N → ℂ}
    (hu : complexVecSqNorm u ≠ 0) :
    complexMatVec (complexHouseholderMat u) u = fun i : Fin N => -u i := by
  rw [complexHouseholderMatVec, complexVecHermitianEval_self]
  funext i
  have huC : (complexVecSqNorm u : ℂ) ≠ 0 := by exact_mod_cast hu
  field_simp [huC]
  ring


/-- Every vector is sent to its negative by its own Householder reflection; in the zero
case this is just the identity acting on the zero vector. -/
theorem complexHouseholderMatVec_neg_self {N : ℕ} (u : Fin N → ℂ) :
    complexMatVec (complexHouseholderMat u) u = fun i : Fin N => -u i := by
  by_cases hu : complexVecSqNorm u = 0
  · have hzero : ∀ i, u i = 0 := complexVecSqNorm_eq_zero_iff.mp hu
    rw [show complexHouseholderMat u = complexIdentityMat by
      funext i j
      unfold complexHouseholderMat complexIdentityMat
      rw [hzero i]
      simp]
    rw [complexMatVec_identity]
    funext i
    rw [hzero i]
    simp
  · exact complexHouseholderMatVec_self hu

/-- A vector Hermitian-orthogonal to `u` is fixed by the Householder reflection. -/
theorem complexHouseholderMatVec_of_orthogonal {N : ℕ} {u v : Fin N → ℂ}
    (huv : complexVecHermitianEval u v = 0) :
    complexMatVec (complexHouseholderMat u) v = v := by
  rw [complexHouseholderMatVec, huv]
  funext i
  simp

/-- Applying a Householder reflection twice is the identity on vectors. -/
theorem complexHouseholderMatVec_apply_twice {N : ℕ} (u v : Fin N → ℂ) :
    complexMatVec (complexHouseholderMat u) (complexMatVec (complexHouseholderMat u) v) = v := by
  by_cases hu : complexVecSqNorm u = 0
  · have hzero : ∀ i, u i = 0 := complexVecSqNorm_eq_zero_iff.mp hu
    rw [show complexHouseholderMat u = complexIdentityMat by
      funext i j
      unfold complexHouseholderMat complexIdentityMat
      rw [hzero i]
      simp]
    rw [complexMatVec_identity, complexMatVec_identity]
  · rw [complexHouseholderMatVec, complexVecHermitianEval_householder_right_general,
      complexVecHermitianEval_self]
    funext i
    rw [congrFun (complexHouseholderMatVec u v) i]
    have huC : (complexVecSqNorm u : ℂ) ≠ 0 := by exact_mod_cast hu
    field_simp [huC]
    ring_nf

/-- A matrix whose vector action squares to the identity is involutive in coordinate form. -/
theorem complexMatInvolutive_of_matVec_apply_twice {N : ℕ} {J : Fin N → Fin N → ℂ}
    (hJ : ∀ v : Fin N → ℂ, complexMatVec J (complexMatVec J v) = v) :
    complexMatInvolutive J := by
  intro i k
  have hk := congrFun (hJ (fun l : Fin N => if l = k then (1 : ℂ) else 0)) i
  unfold complexMatVec at hk
  have hinner : ∀ j : Fin N,
      (∑ l : Fin N, J j l * (if l = k then (1 : ℂ) else 0)) = J j k := by
    intro j
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _hl hlk
      simp [ite_eq_right hlk]
    · intro hknot
      exact False.elim (hknot (Finset.mem_univ k))
  simp only [hinner] at hk
  simpa [complexMatInvolutive] using hk

/-- The Householder reflection is involutive. -/
theorem complexHouseholderMat_involutive {N : ℕ} (u : Fin N → ℂ) :
    complexMatInvolutive (complexHouseholderMat u) := by
  exact complexMatInvolutive_of_matVec_apply_twice (complexHouseholderMatVec_apply_twice u)



/-- The Householder reflection is self-adjoint for the custom Hermitian product. -/
theorem complexHouseholderMat_self_adjoint {N : ℕ} (u v w : Fin N → ℂ) :
    complexVecHermitianEval (complexMatVec (complexHouseholderMat u) v) w =
      complexVecHermitianEval v (complexMatVec (complexHouseholderMat u) w) := by
  rw [complexVecHermitianEval_householder_left_general]
  rw [complexVecHermitianEval_householder_right_general]
  rw [show complexVecHermitianEval v u = star (complexVecHermitianEval u v) by
    rw [complexVecHermitianEval_conj_symm]]

/-- The Householder reflection preserves the full Hermitian product. -/
theorem complexHouseholderMat_hermitian_product {N : ℕ} (u v w : Fin N → ℂ) :
    complexVecHermitianEval (complexMatVec (complexHouseholderMat u) v)
        (complexMatVec (complexHouseholderMat u) w) =
      complexVecHermitianEval v w := by
  by_cases hu : complexVecSqNorm u = 0
  · have hzero : ∀ i, u i = 0 := complexVecSqNorm_eq_zero_iff.mp hu
    rw [show complexHouseholderMat u = complexIdentityMat by
      funext i j
      unfold complexHouseholderMat complexIdentityMat
      rw [hzero i]
      simp]
    rw [complexMatVec_identity, complexMatVec_identity]
  · have huHw : complexVecHermitianEval u (complexMatVec (complexHouseholderMat u) w) =
        -complexVecHermitianEval u w := by
      rw [complexVecHermitianEval_householder_right_general, complexVecHermitianEval_self]
      have huC : (complexVecSqNorm u : ℂ) ≠ 0 := by exact_mod_cast hu
      field_simp [huC]
      ring
    rw [complexVecHermitianEval_householder_left_general]
    rw [complexVecHermitianEval_householder_right_general]
    rw [huHw]
    rw [show complexVecHermitianEval v u = star (complexVecHermitianEval u v) by
      rw [complexVecHermitianEval_conj_symm]]
    have huC : (complexVecSqNorm u : ℂ) ≠ 0 := by exact_mod_cast hu
    field_simp [huC]
    ring_nf

/-- The Householder reflection preserves the Hermitian self-product. -/
theorem complexHouseholderMat_hermitian_isometry {N : ℕ} (u : Fin N → ℂ) :
    complexMatHermitianIsometry (complexHouseholderMat u) := by
  intro v
  by_cases hu : complexVecSqNorm u = 0
  · have hzero : ∀ i, u i = 0 := complexVecSqNorm_eq_zero_iff.mp hu
    rw [show complexHouseholderMat u = complexIdentityMat by
      funext i j
      unfold complexHouseholderMat complexIdentityMat
      rw [hzero i]
      simp]
    rw [complexMatVec_identity]
  · have huHv : complexVecHermitianEval u (complexMatVec (complexHouseholderMat u) v) =
        -complexVecHermitianEval u v := by
      rw [complexVecHermitianEval_householder_right_general, complexVecHermitianEval_self]
      have huC : (complexVecSqNorm u : ℂ) ≠ 0 := by exact_mod_cast hu
      field_simp [huC]
      ring
    rw [complexVecHermitianEval_householder_left_general]
    rw [complexVecHermitianEval_householder_right_general]
    rw [huHv]
    rw [show complexVecHermitianEval v u = star (complexVecHermitianEval u v) by
      rw [complexVecHermitianEval_conj_symm]]
    have huC : (complexVecSqNorm u : ℂ) ≠ 0 := by exact_mod_cast hu
    field_simp [huC]
    ring_nf

/-- The Householder reflection is an isometry for the finite complex Euclidean norm. -/
theorem complexHouseholderMat_isometry {N : ℕ} (u : Fin N → ℂ) :
    complexMatIsometry (complexHouseholderMat u) :=
  complexMatIsometry_of_hermitian (complexHouseholderMat_hermitian_isometry u)



/-- Evaluation formula for the plus factor `(I + i*a*z*J)G`. -/
theorem complexPlusFactorApply_eval {N : ℕ} (a : ℝ) (J : Fin N → Fin N → ℂ)
    (G : Fin N → Polynomial ℂ) (z : ℂ) :
    (fun i : Fin N => (complexPlusFactorApply a J G i).eval z) =
      fun i : Fin N => (G i).eval z + Complex.I * (a : ℂ) * z *
        complexMatVec J (fun j : Fin N => (G j).eval z) i := by
  funext i
  unfold complexPlusFactorApply complexMatVecPoly complexMatVec
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_finsetSum]

/-- Additivity in the second argument of the custom Hermitian product. -/
theorem complexVecHermitianEval_add_right {N : ℕ} (u v w : Fin N → ℂ) :
    complexVecHermitianEval u (fun i => v i + w i) =
      complexVecHermitianEval u v + complexVecHermitianEval u w := by
  unfold complexVecHermitianEval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Additivity in the first argument of the custom Hermitian product. -/
theorem complexVecHermitianEval_add_left {N : ℕ} (u v w : Fin N → ℂ) :
    complexVecHermitianEval (fun i => u i + v i) w =
      complexVecHermitianEval u w + complexVecHermitianEval v w := by
  unfold complexVecHermitianEval
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

/-- Scalar multiplication in the second argument of the custom Hermitian product. -/
theorem complexVecHermitianEval_smul_right {N : ℕ} (c : ℂ) (u v : Fin N → ℂ) :
    complexVecHermitianEval u (fun i => c * v i) = c * complexVecHermitianEval u v := by
  unfold complexVecHermitianEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Scalar multiplication in the first argument of the custom Hermitian product. -/
theorem complexVecHermitianEval_smul_left {N : ℕ} (c : ℂ) (u v : Fin N → ℂ) :
    complexVecHermitianEval (fun i => c * u i) v =
      star c * complexVecHermitianEval u v := by
  unfold complexVecHermitianEval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

/-- Applying a Householder plus factor multiplies the Hermitian norm polynomial by the
corresponding spectral factor. -/
theorem complexVecHermitianPoly_plusFactorApply_householder {N : ℕ}
    (u : Fin N → ℂ) (a : ℝ) (G : Fin N → Polynomial ℂ) :
    complexVecHermitianPoly (complexPlusFactorApply a (complexHouseholderMat u) G) =
      complexSpectralFactor a * complexVecHermitianPoly G := by
  apply Polynomial.funext
  intro z
  rw [complexVecHermitianPoly_eval]
  rw [Polynomial.eval_mul, complexSpectralFactor]
  simp only [RCLike.star_def, map_pow, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  rw [complexVecHermitianPoly_eval]
  rw [complexPlusFactorApply_eval, complexPlusFactorApply_eval]
  let c : ℂ := Complex.I * (a : ℂ) * z
  let d : ℂ := Complex.I * (a : ℂ) * star z
  let gv : Fin N → ℂ := fun i => (G i).eval z
  let gw : Fin N → ℂ := fun i => (G i).eval (star z)
  let J : Fin N → Fin N → ℂ := complexHouseholderMat u
  change complexVecHermitianEval (fun i => gw i + d * complexMatVec J gw i)
      (fun i => gv i + c * complexMatVec J gv i) =
    (1 + ↑a ^ 2 * z ^ 2) * complexVecHermitianEval gw gv
  rw [complexVecHermitianEval_add_left]
  rw [complexVecHermitianEval_add_right]
  rw [complexVecHermitianEval_add_right]
  rw [complexVecHermitianEval_smul_right]
  rw [complexVecHermitianEval_smul_left]
  rw [complexVecHermitianEval_smul_right]
  rw [show complexVecHermitianEval (complexMatVec J gw) gv =
      complexVecHermitianEval gw (complexMatVec J gv) by
    dsimp [J]
    rw [complexHouseholderMat_self_adjoint]]
  rw [show complexVecHermitianEval (fun i => d * complexMatVec J gw i)
        (complexMatVec J gv) =
      star d * complexVecHermitianEval (complexMatVec J gw) (complexMatVec J gv) by
    rw [complexVecHermitianEval_smul_left]]
  rw [show complexVecHermitianEval (complexMatVec J gw) (complexMatVec J gv) =
      complexVecHermitianEval gw gv by
    dsimp [J]
    rw [complexHouseholderMat_hermitian_product]]
  dsimp [c, d]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Hermitian orthogonality is symmetric up to conjugation, hence zero-symmetric. -/
theorem complexVecHermitianEval_eq_zero_symm {N : ℕ} {u v : Fin N → ℂ}
    (huv : complexVecHermitianEval v u = 0) :
    complexVecHermitianEval u v = 0 := by
  have hsym := complexVecHermitianEval_conj_symm u v
  rw [huv] at hsym
  exact (by simpa using (congrArg star hsym).symm)

/-- A Hermitian-orthogonal pair admits an isometric involution negating the second
vector and fixing the first. -/
theorem exists_complexReflection_negates_of_orthogonal {N : ℕ} {u v : Fin N → ℂ}
    (huv : complexVecHermitianEval v u = 0) :
    ∃ J : Fin N → Fin N → ℂ,
      complexMatInvolutive J ∧ complexMatIsometry J ∧
        complexMatVec J u = (fun i : Fin N => -u i) ∧ complexMatVec J v = v := by
  by_cases hzero : ∀ i, u i = 0
  · refine ⟨complexIdentityMat, complexIdentityMat_involutive,
      complexMatIsometry_of_hermitian complexIdentityMat_hermitian_isometry, ?_, ?_⟩
    · rw [complexMatVec_identity]
      funext i
      rw [hzero i]
      simp
    · rw [complexMatVec_identity]
  · have hnorm : complexVecSqNorm u ≠ 0 := by
      intro hnorm
      exact hzero (complexVecSqNorm_eq_zero_iff.mp hnorm)
    refine ⟨complexHouseholderMat u, complexHouseholderMat_involutive u,
      complexHouseholderMat_isometry u, complexHouseholderMatVec_self hnorm, ?_⟩
    exact complexHouseholderMatVec_of_orthogonal (complexVecHermitianEval_eq_zero_symm huv)



/-- One spectral-factor stripping step using the concrete Householder reflection attached
to the positive imaginary root vector. -/
theorem exists_complexSpectralFactor_stripQuotient_householder_with_derivative_norm_bounds
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0) (ha_nonneg : 0 ≤ a)
    {Q : Polynomial ℂ} (hfac : complexVecHermitianPoly F = complexSpectralFactor a * Q) :
    ∃ G : Fin N → Polynomial ℂ,
      (∀ i : Fin N,
          complexStripNumerator a
            (complexHouseholderMat (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ)))) F i =
            complexSpectralFactor a * G i) ∧
        complexPlusFactorApply a
            (complexHouseholderMat (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ)))) G = F ∧
        ((fun i : Fin N => (Polynomial.derivative (F i)).eval 0) =
          fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
            Complex.I * (a : ℂ) * complexMatVec
              (complexHouseholderMat (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))))
              (fun j : Fin N => (G j).eval 0) i) ∧
        complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
            a * complexVecNorm (fun i : Fin N => (G i).eval 0) ∧
        a * complexVecNorm (fun i : Fin N => (G i).eval 0) -
            complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) := by
  let u : Fin N → ℂ := fun i => (F i).eval (Complex.I / (a : ℂ))
  let v : Fin N → ℂ := fun i => (F i).eval (-Complex.I / (a : ℂ))
  let J : Fin N → Fin N → ℂ := complexHouseholderMat u
  have horth : complexVecHermitianEval v u = 0 :=
    complexHermitian_orthogonal_of_spectral_factor F ha hfac
  have hposEig : complexMatVec J u = fun i : Fin N => -u i := by
    dsimp [J]
    exact complexHouseholderMatVec_neg_self u
  have hnegEig : complexMatVec J v = v := by
    dsimp [J]
    exact complexHouseholderMatVec_of_orthogonal (complexVecHermitianEval_eq_zero_symm horth)
  exact exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bounds F ha ha_nonneg
    (complexHouseholderMat_involutive u) (complexHouseholderMat_isometry u) hposEig hnegEig

/-- After a Householder stripping step, the quotient has the residual Hermitian norm
polynomial. -/
theorem complexSpectralFactor_stripQuotient_householder_norm_identity
    {N : ℕ} {F G : Fin N → Polynomial ℂ} {a : ℝ} (ha : a ≠ 0) {Q : Polynomial ℂ}
    (hfac : complexVecHermitianPoly F = complexSpectralFactor a * Q)
    (hrecon : complexPlusFactorApply a
      (complexHouseholderMat (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ)))) G = F) :
    complexVecHermitianPoly G = Q := by
  have _ha := ha
  let u : Fin N → ℂ := fun i => (F i).eval (Complex.I / (a : ℂ))
  have hplus := complexVecHermitianPoly_plusFactorApply_householder u a G
  rw [hrecon] at hplus
  rw [hfac] at hplus
  have hsf_ne : complexSpectralFactor a ≠ 0 := by
    intro hzero
    have heval := congrArg (fun p : Polynomial ℂ => p.eval 0) hzero
    simp [complexSpectralFactor] at heval
  exact Polynomial.complex_mul_left_cancel_of_ne_zero hsf_ne hplus.symm


/-- One diagonal spectral strip after complexifying a real square-root vector with norm
`(1 + X^2)^(m+1)`. -/
theorem exists_diagonal_complex_householder_strip_once
    {m N : ℕ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 = ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)) :
    ∃ G : Fin N → Polynomial ℂ,
      complexVecHermitianPoly G = complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ m) ∧
        complexVecNorm (fun i : Fin N =>
          (Polynomial.derivative (complexifyPoly (F i))).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
            complexVecNorm (fun i : Fin N => (G i).eval 0) ∧
        complexVecNorm (fun i : Fin N => (G i).eval 0) -
            complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) ≤
          complexVecNorm (fun i : Fin N =>
            (Polynomial.derivative (complexifyPoly (F i))).eval 0) := by
  let Fc : Fin N → Polynomial ℂ := fun i => complexifyPoly (F i)
  have hfac : complexVecHermitianPoly Fc =
      complexSpectralFactor (1 : ℝ) *
        complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ m) := by
    rw [show complexVecHermitianPoly Fc = complexifyPoly (∑ i : Fin N, (F i) ^ 2) by
      dsimp [Fc]
      rw [complexVecHermitianPoly_complexify]]
    have hreal : ∑ i : Fin N, (F i) ^ 2 =
        (1 + Polynomial.C ((1 : ℝ) ^ 2) * Polynomial.X ^ 2) *
          (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ m) := by
      rw [hNorm]
      simp
      ring
    rw [hreal]
    unfold complexifyPoly
    rw [Polynomial.map_mul]
    rw [show Polynomial.map (algebraMap ℝ ℂ)
        (1 + Polynomial.C ((1 : ℝ) ^ 2) * Polynomial.X ^ 2) =
          complexSpectralFactor (1 : ℝ) by
      simpa [complexifyPoly] using complexify_real_spectral_factor (1 : ℝ)]
  obtain ⟨G, _hstrip, hrecon, _hder, hupper, hlower⟩ :=
    exists_complexSpectralFactor_stripQuotient_householder_with_derivative_norm_bounds
      Fc (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : 0 ≤ (1 : ℝ)) hfac
  refine ⟨G, ?_, ?_, ?_⟩
  · exact complexSpectralFactor_stripQuotient_householder_norm_identity
      (by norm_num : (1 : ℝ) ≠ 0) hfac hrecon
  · simpa [Fc, one_mul] using hupper
  · simpa [Fc, one_mul] using hlower

/-- One axis spectral strip after complexifying a real square-root vector with norm
`(1 + X^2)^m * (1 + (lambda + 1) X^2)`. -/
theorem exists_axis_complex_householder_strip_once
    {m N : ℕ} {lambda : ℝ} (hLam : 0 < lambda + 1) {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)) :
    ∃ G : Fin N → Polynomial ℂ,
      complexVecHermitianPoly G = complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ m) ∧
        complexVecNorm (fun i : Fin N =>
          (Polynomial.derivative (complexifyPoly (F i))).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
            Real.sqrt (lambda + 1) * complexVecNorm (fun i : Fin N => (G i).eval 0) ∧
        Real.sqrt (lambda + 1) * complexVecNorm (fun i : Fin N => (G i).eval 0) -
            complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) ≤
          complexVecNorm (fun i : Fin N =>
            (Polynomial.derivative (complexifyPoly (F i))).eval 0) := by
  let a : ℝ := Real.sqrt (lambda + 1)
  let Fc : Fin N → Polynomial ℂ := fun i => complexifyPoly (F i)
  have ha_sq : a ^ 2 = lambda + 1 := by
    dsimp [a]
    exact Real.sq_sqrt (le_of_lt hLam)
  have ha_ne : a ≠ 0 := by
    dsimp [a]
    exact ne_of_gt (Real.sqrt_pos.2 hLam)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Real.sqrt_nonneg _
  have hfac : complexVecHermitianPoly Fc =
      complexSpectralFactor a *
        complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ m) := by
    rw [show complexVecHermitianPoly Fc = complexifyPoly (∑ i : Fin N, (F i) ^ 2) by
      dsimp [Fc]
      rw [complexVecHermitianPoly_complexify]]
    have hreal : ∑ i : Fin N, (F i) ^ 2 =
        (1 + Polynomial.C (a ^ 2) * Polynomial.X ^ 2) *
          (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ m) := by
      rw [hNorm, ha_sq]
      ring
    rw [hreal]
    unfold complexifyPoly
    rw [Polynomial.map_mul]
    rw [show Polynomial.map (algebraMap ℝ ℂ)
        (1 + Polynomial.C (a ^ 2) * Polynomial.X ^ 2) = complexSpectralFactor a by
      simpa [complexifyPoly] using complexify_real_spectral_factor a]
  obtain ⟨G, _hstrip, hrecon, _hder, hupper, hlower⟩ :=
    exists_complexSpectralFactor_stripQuotient_householder_with_derivative_norm_bounds
      Fc ha_ne ha_nonneg hfac
  refine ⟨G, ?_, ?_, ?_⟩
  · exact complexSpectralFactor_stripQuotient_householder_norm_identity ha_ne hfac hrecon
  · simpa [Fc, a] using hupper
  · simpa [Fc, a] using hlower

/-- One spectral-factor stripping step where the required isometric involution is built
from the Hermitian orthogonality at the conjugate roots. -/
theorem exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bounds_of_factor
    {N : ℕ} (F : Fin N → Polynomial ℂ) {a : ℝ} (ha : a ≠ 0)
    (ha_nonneg : 0 ≤ a)
    {Q : Polynomial ℂ} (hfac : complexVecHermitianPoly F = complexSpectralFactor a * Q) :
    ∃ G : Fin N → Polynomial ℂ,
      (∀ i : Fin N, complexStripNumerator a (Classical.choose
        (exists_complexReflection_negates_of_orthogonal
          (complexHermitian_orthogonal_of_spectral_factor F ha hfac))) F i =
          complexSpectralFactor a * G i) ∧
        complexPlusFactorApply a (Classical.choose
          (exists_complexReflection_negates_of_orthogonal
            (complexHermitian_orthogonal_of_spectral_factor F ha hfac))) G = F ∧
        ((fun i : Fin N => (Polynomial.derivative (F i)).eval 0) =
          fun i : Fin N => (Polynomial.derivative (G i)).eval 0 +
            Complex.I * (a : ℂ) * complexMatVec (Classical.choose
              (exists_complexReflection_negates_of_orthogonal
                (complexHermitian_orthogonal_of_spectral_factor F ha hfac)))
              (fun j : Fin N => (G j).eval 0) i) ∧
        complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) +
            a * complexVecNorm (fun i : Fin N => (G i).eval 0) ∧
        a * complexVecNorm (fun i : Fin N => (G i).eval 0) -
            complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) := by
  let horth := complexHermitian_orthogonal_of_spectral_factor F ha hfac
  let J : Fin N → Fin N → ℂ :=
    Classical.choose (exists_complexReflection_negates_of_orthogonal horth)
  have hJ : complexMatInvolutive J :=
    (Classical.choose_spec (exists_complexReflection_negates_of_orthogonal horth)).1
  have hIso : complexMatIsometry J :=
    (Classical.choose_spec (exists_complexReflection_negates_of_orthogonal horth)).2.1
  have hposEig : complexMatVec J (fun i : Fin N => (F i).eval (Complex.I / (a : ℂ))) =
      fun i : Fin N => - (F i).eval (Complex.I / (a : ℂ)) :=
    (Classical.choose_spec (exists_complexReflection_negates_of_orthogonal horth)).2.2.1
  have hnegEig : complexMatVec J (fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ))) =
      fun i : Fin N => (F i).eval (-Complex.I / (a : ℂ)) :=
    (Classical.choose_spec (exists_complexReflection_negates_of_orthogonal horth)).2.2.2
  exact exists_complexSpectralFactor_stripQuotient_with_derivative_norm_bounds F ha ha_nonneg hJ
    hIso hposEig hnegEig

end ScaledRobinson
end OptimalConvergenceRates

end
