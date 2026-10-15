/-
  OptimalConvergenceRates/ScaledRobinson/HomogenizationSpectralIteration.lean

  Iterating the spectral-factor stripping estimates.
-/
import OptimalConvergenceRates.ScaledRobinson.HomogenizationSpectralReflection

open MvPolynomial Finset


noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- The complexified polynomial `(1 + X^2)^(n+1)` has one visible spectral factor. -/
theorem complexify_one_add_X_sq_pow_succ (n : ℕ) :
    complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (n + 1)) =
      complexSpectralFactor (1 : ℝ) *
        complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n) := by
  unfold complexifyPoly complexSpectralFactor
  rw [pow_succ]
  rw [Polynomial.map_mul]
  simp
  ring

/-- A vector with Hermitian norm polynomial `(1 + X^2)^n` has norm one at zero. -/
theorem complexVecNorm_eval_zero_of_norm_power {N n : ℕ} {F : Fin N → Polynomial ℂ}
    (hNorm : complexVecHermitianPoly F =
      complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n)) :
    complexVecNorm (fun i : Fin N => (F i).eval 0) = 1 := by
  have heval := congrArg (fun p : Polynomial ℂ => p.eval 0) hNorm
  change (complexVecHermitianPoly F).eval (0 : ℂ) =
    (complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n)).eval (0 : ℂ) at heval
  rw [complexVecHermitianPoly_eval] at heval
  have hleft : complexVecHermitianEval (fun i : Fin N => (F i).eval (star (0 : ℂ)))
      (fun i : Fin N => (F i).eval (0 : ℂ)) =
        (complexVecSqNorm (fun i : Fin N => (F i).eval 0) : ℂ) := by
    simp only [star_zero]
    rw [complexVecHermitianEval_self]
  rw [hleft] at heval
  have hright : (complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n)).eval 0 =
      (1 : ℂ) := by
    change (complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n)).eval ((0 : ℝ) : ℂ) =
      (1 : ℂ)
    rw [complexifyPoly_eval_real]
    simp
  rw [hright] at heval
  have hsq : complexVecSqNorm (fun i : Fin N => (F i).eval 0) = 1 := by
    exact_mod_cast heval
  unfold complexVecNorm
  rw [hsq]
  norm_num


/-- Coefficientwise conjugation preserves the natural degree of a complex polynomial. -/
theorem complexConjPoly_natDegree (p : Polynomial ℂ) :
    (complexConjPoly p).natDegree = p.natDegree := by
  by_cases hp : p = 0
  · subst p
    simp [complexConjPoly]
  · apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      unfold complexConjPoly
      rw [Polynomial.coeff_map]
      have hpcoeff : p.coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt hn
      simp [hpcoeff]
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro n hn
      by_contra hcoeff
      have hconjcoeff : (complexConjPoly p).coeff n ≠ 0 := by
        unfold complexConjPoly
        rw [Polynomial.coeff_map]
        exact (star_ne_zero.mpr hcoeff)
      exact hconjcoeff (Polynomial.coeff_eq_zero_of_natDegree_lt hn)

/-- Leading coefficient of the coefficientwise conjugate polynomial. -/
theorem complexConjPoly_leadingCoeff (p : Polynomial ℂ) :
    (complexConjPoly p).leadingCoeff = star p.leadingCoeff := by
  unfold Polynomial.leadingCoeff
  rw [complexConjPoly_natDegree]
  unfold complexConjPoly
  rw [Polynomial.coeff_map]
  rfl

/-- The coefficient in degree `2*d` of a Hermitian norm vector, when all coordinates have
natural degree at most `d`, is the sum of squared norms of the degree-`d` coefficients. -/
theorem complexVecHermitianPoly_coeff_two_mul_of_natDegree_le
    {N d : ℕ} {F : Fin N → Polynomial ℂ} (hdeg : ∀ i : Fin N, (F i).natDegree ≤ d) :
    (complexVecHermitianPoly F).coeff (2 * d) =
      (∑ i : Fin N, Complex.normSq ((F i).coeff d) : ℝ) := by
  unfold complexVecHermitianPoly
  rw [Polynomial.finsetSum_coeff]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hconjdeg : (complexConjPoly (F i)).natDegree ≤ d := by
    rw [complexConjPoly_natDegree]
    exact hdeg i
  have hcoeff := Polynomial.coeff_mul_add_eq_of_natDegree_le hconjdeg (hdeg i)
  rw [show d + d = 2 * d by omega] at hcoeff
  rw [hcoeff]
  have hconjcoeff : (complexConjPoly (F i)).coeff d = star ((F i).coeff d) := by
    unfold complexConjPoly
    rw [Polynomial.coeff_map]
    rfl
  rw [hconjcoeff]
  simpa [mul_comm] using (Complex.normSq_eq_conj_mul_self (z := (F i).coeff d)).symm

/-- If a Hermitian norm polynomial is constant, every coordinate has degree at most zero. -/
theorem complexVecHermitianPoly_eq_one_natDegree_zero
    {N : ℕ} {F : Fin N → Polynomial ℂ}
    (hNorm : complexVecHermitianPoly F = complexifyPoly (1 : Polynomial ℝ)) :
    ∀ i : Fin N, (F i).natDegree = 0 := by
  classical
  by_cases hN : Nonempty (Fin N)
  · let d : ℕ := Finset.max' (Finset.univ.image fun i : Fin N => (F i).natDegree)
        (by
          rcases hN with ⟨i⟩
          exact ⟨(F i).natDegree, by simp⟩)
    have hdeg : ∀ i : Fin N, (F i).natDegree ≤ d := by
      intro i
      dsimp [d]
      exact Finset.le_max' _ _ (by simp)
    by_contra hbad
    push Not at hbad
    obtain ⟨i0, hi0⟩ := hbad
    have hdpos : 0 < d := lt_of_lt_of_le (Nat.pos_of_ne_zero hi0) (hdeg i0)
    have hcoeffNorm := complexVecHermitianPoly_coeff_two_mul_of_natDegree_le (N := N) (d := d)
      (F := F) hdeg
    have hcoeffZero : (complexVecHermitianPoly F).coeff (2 * d) = 0 := by
      rw [hNorm]
      unfold complexifyPoly
      rw [Polynomial.coeff_map]
      have htwo : 0 < 2 * d := by nlinarith
      simp [Polynomial.coeff_one, Nat.ne_of_gt htwo]
    rw [hcoeffNorm] at hcoeffZero
    have hsumZero : (∑ i : Fin N, Complex.normSq ((F i).coeff d)) = 0 := by
      exact Complex.ofReal_injective hcoeffZero
    have hallZero : ∀ i : Fin N, Complex.normSq ((F i).coeff d) = 0 := by
      simpa using (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin N)))
        (f := fun i : Fin N => Complex.normSq ((F i).coeff d))
        (fun i _ => Complex.normSq_nonneg _)).mp hsumZero
    have hmaxmem : d ∈ Finset.univ.image fun i : Fin N => (F i).natDegree :=
      Finset.max'_mem _ _
    obtain ⟨j, _hj, hjd⟩ := Finset.mem_image.mp hmaxmem
    have hleadZero : (F j).leadingCoeff = 0 := by
      rw [← Polynomial.coeff_natDegree, hjd]
      exact (Complex.normSq_eq_zero.mp (hallZero j))
    have hpolyZero : F j = 0 := Polynomial.leadingCoeff_eq_zero.mp hleadZero
    have hdegj : (F j).natDegree = 0 := by simp [hpolyZero]
    omega
  · intro i
    exact False.elim (hN ⟨i⟩)

/-- A vector with Hermitian norm polynomial `1` has zero derivative at the origin. -/
theorem complexVecNorm_derivative_eval_zero_of_norm_one
    {N : ℕ} {F : Fin N → Polynomial ℂ}
    (hNorm : complexVecHermitianPoly F = complexifyPoly (1 : Polynomial ℝ)) :
    complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) = 0 := by
  have hdeg := complexVecHermitianPoly_eq_one_natDegree_zero hNorm
  unfold complexVecNorm complexVecSqNorm
  rw [show (∑ i : Fin N, Complex.normSq ((Polynomial.derivative (F i)).eval 0)) = 0 by
    apply Finset.sum_eq_zero
    intro i _
    have hder : Polynomial.derivative (F i) = 0 := Polynomial.derivative_of_natDegree_zero (hdeg i)
    simp [hder]]
  simp

/-- Iterating the `1 + X^2` spectral strips leaves a norm-one residual vector and
accumulates at most one unit of derivative norm per stripped factor. -/
theorem exists_complex_norm_power_strip_residual_derivative_bound
    {N n : ℕ} (F : Fin N → Polynomial ℂ)
    (hNorm : complexVecHermitianPoly F =
      complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n)) :
    ∃ G : Fin N → Polynomial ℂ,
      complexVecHermitianPoly G = complexifyPoly (1 : Polynomial ℝ) ∧
        complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤
          complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) + (n : ℝ) := by
  induction n generalizing F with
  | zero =>
      refine ⟨F, ?_, ?_⟩
      · simpa using hNorm
      · norm_num
  | succ n ih =>
      have hfac : complexVecHermitianPoly F = complexSpectralFactor (1 : ℝ) *
          complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n) := by
        rw [hNorm, complexify_one_add_X_sq_pow_succ n]
      obtain ⟨G, _hstrip, _hrecon, _hder, hupper, _hlower⟩ :=
        exists_complexSpectralFactor_stripQuotient_householder_with_derivative_norm_bounds
          F (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : 0 ≤ (1 : ℝ)) hfac
      have hGNorm : complexVecHermitianPoly G =
          complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n) :=
        complexSpectralFactor_stripQuotient_householder_norm_identity
          (by norm_num : (1 : ℝ) ≠ 0) hfac _hrecon
      obtain ⟨H, hHNorm, hGH⟩ := ih G hGNorm
      have hGZero : complexVecNorm (fun i : Fin N => (G i).eval 0) = 1 :=
        complexVecNorm_eval_zero_of_norm_power hGNorm
      refine ⟨H, hHNorm, ?_⟩
      calc
        complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤
            complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) + 1 := by
              simpa [hGZero, one_mul] using hupper
        _ ≤ (complexVecNorm (fun i : Fin N => (Polynomial.derivative (H i)).eval 0) + n) + 1 := by
              linarith
        _ = complexVecNorm (fun i : Fin N => (Polynomial.derivative (H i)).eval 0) +
              ((n + 1 : ℕ) : ℝ) := by
              norm_num
              ring

/-- A vector with Hermitian norm polynomial `(1 + X^2)^n` has derivative norm at zero at
most `n`. -/
theorem complex_norm_power_derivative_bound
    {N n : ℕ} {F : Fin N → Polynomial ℂ}
    (hNorm : complexVecHermitianPoly F =
      complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n)) :
    complexVecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤ (n : ℝ) := by
  obtain ⟨G, hGNorm, hFG⟩ := exists_complex_norm_power_strip_residual_derivative_bound F hNorm
  have hGder : complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) = 0 :=
    complexVecNorm_derivative_eval_zero_of_norm_one hGNorm
  linarith

/-- Real form of the diagonal spectral derivative bound. -/
theorem real_norm_power_derivative_bound
    {N n : ℕ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 = ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n) :
    vecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤ (n : ℝ) := by
  have hComplexNorm : complexVecHermitianPoly (fun i : Fin N => complexifyPoly (F i)) =
      complexifyPoly (((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ n) := by
    rw [complexVecHermitianPoly_complexify]
    rw [hNorm]
  have hbound := complex_norm_power_derivative_bound hComplexNorm
  have hnorm : complexVecNorm (fun i : Fin N =>
        (Polynomial.derivative (complexifyPoly (F i))).eval 0) =
      vecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) :=
    complexVecNorm_complexify_derivative_eval_zero F
  rwa [hnorm] at hbound



/-- Diagonal restriction derivative upper bound in real form. -/
theorem diagonalRestriction_stripped_derivative_norm_le
    {m N : ℕ} {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 = ((1 : Polynomial ℝ) + Polynomial.X ^ 2) ^ (m + 1)) :
    vecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) ≤ (m : ℝ) + 1 := by
  have h := real_norm_power_derivative_bound (N := N) (n := m + 1) (F := F) hNorm
  simpa using h

/-- Axis restriction derivative lower bound in real form. -/
theorem axisRestriction_stripped_derivative_norm_ge
    {m N : ℕ} {lambda : ℝ} (hLam : 0 < lambda + 1) {F : Fin N → Polynomial ℝ}
    (hNorm : ∑ i : Fin N, (F i) ^ 2 =
      (1 + Polynomial.X ^ 2) ^ m * (1 + Polynomial.C (lambda + 1) * Polynomial.X ^ 2)) :
    Real.sqrt (lambda + 1) - (m : ℝ) ≤
      vecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) := by
  obtain ⟨G, hGNorm, _hupper, hlower⟩ :=
    exists_axis_complex_householder_strip_once hLam hNorm
  have hGZero : complexVecNorm (fun i : Fin N => (G i).eval 0) = 1 :=
    complexVecNorm_eval_zero_of_norm_power hGNorm
  have hGDer : complexVecNorm (fun i : Fin N => (Polynomial.derivative (G i)).eval 0) ≤
      (m : ℝ) :=
    complex_norm_power_derivative_bound hGNorm
  have hreal : complexVecNorm (fun i : Fin N =>
        (Polynomial.derivative (complexifyPoly (F i))).eval 0) =
      vecNorm (fun i : Fin N => (Polynomial.derivative (F i)).eval 0) :=
    complexVecNorm_complexify_derivative_eval_zero F
  rw [hGZero, mul_one, hreal] at hlower
  linarith

end ScaledRobinson
end OptimalConvergenceRates

end
