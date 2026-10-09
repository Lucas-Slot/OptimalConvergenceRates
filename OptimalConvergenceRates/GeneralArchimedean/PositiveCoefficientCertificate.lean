/-
  Quadratic-module certificates obtained by substituting a module element into
  a univariate polynomial with nonnegative coefficients.
-/
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanEnvelope
import OptimalConvergenceRates.GeneralArchimedean.UnivariateCoefficientNorm
import OptimalConvergenceRates.GeneralArchimedean.RationalSquareRoot

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates
namespace GeneralArchimedean

open RationalSquareRoot

variable {n m : ℕ}

/-- Substitute a multivariate polynomial for the variable of a real
univariate polynomial. -/
def polynomialSubst (a : MvPolynomial (Fin n) ℝ) (P : Polynomial ℝ) :
    MvPolynomial (Fin n) ℝ :=
  Polynomial.aeval a P

@[simp]
theorem polynomialSubst_X (a : MvPolynomial (Fin n) ℝ) :
    polynomialSubst a Polynomial.X = a := by
  simp [polynomialSubst]

@[simp]
theorem polynomialSubst_C (a : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    polynomialSubst a (Polynomial.C c) = C c := by
  simp [polynomialSubst]

@[simp]
theorem polynomialSubst_add (a : MvPolynomial (Fin n) ℝ)
    (P Q : Polynomial ℝ) :
    polynomialSubst a (P + Q) = polynomialSubst a P + polynomialSubst a Q := by
  simp [polynomialSubst]

@[simp]
theorem polynomialSubst_mul (a : MvPolynomial (Fin n) ℝ)
    (P Q : Polynomial ℝ) :
    polynomialSubst a (P * Q) = polynomialSubst a P * polynomialSubst a Q := by
  simp [polynomialSubst]

@[simp]
theorem polynomialSubst_pow (a : MvPolynomial (Fin n) ℝ)
    (P : Polynomial ℝ) (k : ℕ) :
    polynomialSubst a (P ^ k) = polynomialSubst a P ^ k := by
  simp [polynomialSubst]


/-- The generic univariate substitution coefficient bound in the notation
used throughout the conversion development. -/
theorem polynomialSubst_coeffL1Norm_le
    (a : MvPolynomial (Fin n) ℝ) (P : Polynomial ℝ)
    {G : ℝ} (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (polynomialSubst a P) ≤
      polynomialCoeffL1Norm P * G ^ P.natDegree := by
  exact coeffL1Norm_polynomial_aeval_le a P hG ha


/-- Algebra-compatible version of `polynomialSubst_coeffL1Norm_le`. -/
theorem polynomialSubst_coeffL1Norm_le_embedded
    (a : MvPolynomial (Fin n) ℝ) (P : Polynomial ℝ)
    {G : ℝ} (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (polynomialSubst a P) ≤
      embeddedPolynomialCoeffL1Norm P * G ^ P.natDegree := by
  exact coeffL1Norm_polynomial_aeval_le_embedded a P hG ha

/-- Substituting a multivariate polynomial into a univariate polynomial
multiplies total degree by at most the univariate natural degree. -/
theorem polynomialSubst_totalDegree_le
    (a : MvPolynomial (Fin n) ℝ) (P : Polynomial ℝ) :
    (polynomialSubst a P).totalDegree ≤
      P.natDegree * a.totalDegree := by
  rw [polynomialSubst, Polynomial.aeval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  simp only [MvPolynomial.smul_eq_C_mul]
  calc
    (C (P.coeff k) * a ^ k).totalDegree ≤
        (C (P.coeff k) : MvPolynomial (Fin n) ℝ).totalDegree +
          (a ^ k).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ k * a.totalDegree := by
      calc
        _ ≤ 0 + k * a.totalDegree := Nat.add_le_add
          (MvPolynomial.totalDegree_C (P.coeff k)).le
          (MvPolynomial.totalDegree_pow _ _)
        _ = k * a.totalDegree := Nat.zero_add _
    _ ≤ P.natDegree * a.totalDegree := by
      have hk' : k ≤ P.natDegree := by
        have := Finset.mem_range.mp hk
        omega
      exact Nat.mul_le_mul_right a.totalDegree hk'
/-- Every nonnegative scalar multiple of a power of a module element is again
in the module. Even powers use the free SOS term; odd powers use the generator
certificate once. -/
theorem C_mul_pow_mem_of_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ}
    (ha : QuadraticModuleMem g a) {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    QuadraticModuleMem g (C c * a ^ k) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · apply QuadraticModuleMem.of_isSOS
    have hsos : IsSOS (C c * (a ^ j) ^ 2) :=
      IsSOS_mul (IsSOS_C_nonneg c hc) (IsSOS_sq (a ^ j))
    convert hsos using 1
    rw [show 2 * j = j * 2 by omega, pow_mul]
  · have hsos : IsSOS (C c * (a ^ j) ^ 2) :=
      IsSOS_mul (IsSOS_C_nonneg c hc) (IsSOS_sq (a ^ j))
    have hmul := QuadraticModuleMem.sos_mul hsos ha
    convert hmul using 1
    rw [pow_succ, pow_mul]
    ring

/-- Degree-tracked version of `C_mul_pow_mem_of_mem`. -/
theorem C_mul_pow_mem_of_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (ha : a ∈ GenQuadraticModule g r)
    {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    C c * a ^ k ∈ GenQuadraticModule g
      (r + k * a.totalDegree) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hsos : IsSOS (C c * a ^ (2 * j)) := by
      have hraw : IsSOS (C c * (a ^ j) ^ 2) :=
        IsSOS_mul (IsSOS_C_nonneg c hc) (IsSOS_sq (a ^ j))
      convert hraw using 1
      rw [show 2 * j = j * 2 by omega, pow_mul]
    have hdegree : (C c * a ^ (2 * j)).totalDegree ≤
        (2 * j) * a.totalDegree := by
      calc
        (C c * a ^ (2 * j)).totalDegree ≤
            (C c : MvPolynomial (Fin n) ℝ).totalDegree +
              (a ^ (2 * j)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ 0 + (2 * j) * a.totalDegree :=
          Nat.add_le_add (MvPolynomial.totalDegree_C c).le
            (MvPolynomial.totalDegree_pow _ _)
        _ = (2 * j) * a.totalDegree := by simp
    exact GenQuadraticModule_mono
      (Nat.le_add_left ((2 * j) * a.totalDegree) r)
      (genQuadraticModule_sos g hsos hdegree)
  · have hsos : IsSOS (C c * (a ^ j) ^ 2) :=
      IsSOS_mul (IsSOS_C_nonneg c hc) (IsSOS_sq (a ^ j))
    have hdegree : (C c * (a ^ j) ^ 2).totalDegree ≤
        (2 * j + 1) * a.totalDegree := by
      calc
        (C c * (a ^ j) ^ 2).totalDegree ≤
            (C c : MvPolynomial (Fin n) ℝ).totalDegree +
              ((a ^ j) ^ 2).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ 0 + (j * 2) * a.totalDegree := by
          apply Nat.add_le_add
          · exact (MvPolynomial.totalDegree_C c).le
          · rw [← pow_mul]
            exact MvPolynomial.totalDegree_pow _ _
        _ ≤ (2 * j + 1) * a.totalDegree := by
          simp only [Nat.zero_add]
          exact Nat.mul_le_mul_right a.totalDegree (by omega)
    have hraw := genQuadraticModule_sos_mul hsos ha
    have hmem := GenQuadraticModule_mono
      (Nat.add_le_add_left hdegree r) hraw
    convert hmem using 1
    rw [pow_succ, pow_mul]
    ring

/-- Degree-tracked positive-coefficient substitution. -/
theorem polynomialSubst_mem_of_coeffNonneg_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (ha : a ∈ GenQuadraticModule g r)
    (P : Polynomial ℝ) (hP : CoeffNonneg P) :
    polynomialSubst a P ∈ GenQuadraticModule g
      (r + P.natDegree * a.totalDegree) := by
  rw [polynomialSubst, Polynomial.aeval_eq_sum_range]
  apply genQuadraticModule_sum
  intro k hk
  have hk' : k ≤ P.natDegree := by
    have hkrange := Finset.mem_range.mp hk
    omega
  have hterm := C_mul_pow_mem_of_mem_at ha (hP k) k
  apply GenQuadraticModule_mono
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree hk') r)
  simpa only [MvPolynomial.smul_eq_C_mul] using hterm


/-- A coefficientwise nonnegative univariate polynomial remains in a
quadratic module after substituting any element of that module. -/
theorem polynomialSubst_mem_of_coeffNonneg
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ}
    (ha : QuadraticModuleMem g a)
    (P : Polynomial ℝ) (hP : CoeffNonneg P) :
    QuadraticModuleMem g (polynomialSubst a P) := by
  rw [polynomialSubst, Polynomial.aeval_eq_sum_range]
  apply QuadraticModuleMem.sum
  intro k hk
  simpa only [MvPolynomial.smul_eq_C_mul] using C_mul_pow_mem_of_mem ha (hP k) k

/-- If a coefficientwise nonnegative polynomial has constant coefficient one,
then its square minus one is still coefficientwise nonnegative. -/
theorem coeffNonneg_sq_sub_one
    {P : Polynomial ℝ} (hP : CoeffNonneg P)
    (hP0 : P.coeff 0 = 1) :
    CoeffNonneg (P ^ 2 - 1) := by
  have hsq : CoeffNonneg (P ^ 2) := hP.pow 2
  intro k
  rw [Polynomial.coeff_sub]
  by_cases hk : k = 0
  · subst k
    simp only [pow_two]
    rw [Polynomial.mul_coeff_zero]
    simp [hP0]
  · simpa [Polynomial.coeff_one, hk] using hsq k

/-- The relation V(a)^2 - 1 belongs to the module whenever V has nonnegative
coefficients and constant coefficient one. -/
theorem polynomialSubst_sq_sub_one_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ}
    (ha : QuadraticModuleMem g a)
    (V : Polynomial ℝ) (hV : CoeffNonneg V)
    (hV0 : V.coeff 0 = 1) :
    QuadraticModuleMem g (polynomialSubst a V ^ 2 - 1) := by
  have h := polynomialSubst_mem_of_coeffNonneg ha (V ^ 2 - 1)
    (coeffNonneg_sq_sub_one hV hV0)
  simpa [map_sub, map_pow, polynomialSubst] using h

/-- Degree-tracked denominator-square relation. -/
theorem polynomialSubst_sq_sub_one_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (ha : a ∈ GenQuadraticModule g r)
    (V : Polynomial ℝ) (hV : CoeffNonneg V)
    (hV0 : V.coeff 0 = 1) :
    polynomialSubst a V ^ 2 - 1 ∈ GenQuadraticModule g
      (r + 2 * V.natDegree * a.totalDegree) := by
  have hraw := polynomialSubst_mem_of_coeffNonneg_at ha (V ^ 2 - 1)
    (coeffNonneg_sq_sub_one hV hV0)
  have hdegree : (V ^ 2 - 1).natDegree ≤ 2 * V.natDegree := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le Polynomial.natDegree_pow_le (by simp))
  have hmem := GenQuadraticModule_mono
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree hdegree) r) hraw
  simpa [map_sub, map_pow, polynomialSubst, Nat.mul_assoc] using hmem


/-- Univariate SOS decompositions remain multivariate SOS after polynomial
substitution. -/
theorem isSOS_polynomialSubst
    (a : MvPolynomial (Fin n) ℝ) {P : Polynomial ℝ}
    (hP : IsSOSUni P) :
    IsSOS (polynomialSubst a P) := by
  obtain ⟨k, q, hq⟩ := hP
  refine ⟨k, fun i => polynomialSubst a (q i), ?_⟩
  have hmap := congrArg (Polynomial.aeval a) hq
  simpa [polynomialSubst, map_sum, map_pow] using hmap

/-- The normalized error remains an SOS after substituting a multivariate
polynomial for its variable. -/
theorem normalizedError_subst_isSOS
    (a : MvPolynomial (Fin n) ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ) :
    IsSOS (polynomialSubst a (normalizedError δ ell J)) :=
  isSOS_polynomialSubst a (normalizedError_isSOSUni hδ ell J)

/-- Substitution turns the normalized univariate identity into the exact
multivariate relation P(a)^2 - a V(a)^2 = E(a). -/
theorem normalizedRationalSquareRoot_subst_identity
    (a : MvPolynomial (Fin n) ℝ)
    {δ : ℝ} (hδ : 0 < δ) {ell : ℕ} (hell : 0 < ell) (J : ℕ) :
    polynomialSubst a (normalizedNumerator δ ell J) ^ 2 -
        a * polynomialSubst a (normalizedDenominator δ ell J) ^ 2 =
      polynomialSubst a (normalizedError δ ell J) := by
  have hmap := congrArg (Polynomial.aeval a)
    (normalizedNumerator_sq_sub_X_mul_denominator_sq hδ hell J)
  simpa [polynomialSubst, map_sub, map_mul, map_pow] using hmap

/-- The substituted normalized error belongs to every quadratic module as its
free SOS term. -/
theorem normalizedError_subst_mem
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (a : MvPolynomial (Fin n) ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ) :
    QuadraticModuleMem g (polynomialSubst a (normalizedError δ ell J)) :=
  QuadraticModuleMem.of_isSOS g (normalizedError_subst_isSOS a hδ ell J)


/-- The normalized dyadic denominator gives the exact relation V(a)^2 - 1
inside any quadratic module containing a. -/
theorem normalizedDenominator_subst_sq_sub_one_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ}
    (ha : QuadraticModuleMem g a)
    {δ : ℝ} (hδ : 0 < δ) {ell : ℕ} (hell : 0 < ell) (J : ℕ) :
    QuadraticModuleMem g
      (polynomialSubst a (normalizedDenominator δ ell J) ^ 2 - 1) := by
  have hpos := denominator_eval_self_pos hδ hell J
  exact polynomialSubst_sq_sub_one_mem ha _
    (normalizedDenominator_coeffNonneg hδ.le ell J hpos)
    (normalizedDenominator_coeff_zero ell J hpos)

/-- Explicit-order normalized denominator-square relation. -/
theorem normalizedDenominator_subst_sq_sub_one_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (ha : a ∈ GenQuadraticModule g r)
    {δ : ℝ} (hδ : 0 < δ) {ell : ℕ} (hell : 0 < ell) (J : ℕ) :
    polynomialSubst a (normalizedDenominator δ ell J) ^ 2 - 1 ∈
      GenQuadraticModule g
        (r + (4 * ell * (J + 1)) * a.totalDegree) := by
  have hpos := denominator_eval_self_pos hδ hell J
  have hraw := polynomialSubst_sq_sub_one_mem_at ha _
    (normalizedDenominator_coeffNonneg hδ.le ell J hpos)
    (normalizedDenominator_coeff_zero ell J hpos)
  have hdegree :
      2 * (normalizedDenominator δ ell J).natDegree ≤
        4 * ell * (J + 1) := by
    calc
      2 * (normalizedDenominator δ ell J).natDegree ≤
          2 * (2 * ell * (J + 1)) :=
        Nat.mul_le_mul_left 2
          (normalizedDenominator_degree_bound δ ell J)
      _ = 4 * ell * (J + 1) := by ring
  exact GenQuadraticModule_mono
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree hdegree) r) hraw



end GeneralArchimedean
end OptimalConvergenceRates

end
