/-
  Coefficient-bounded positive-coefficient substitution certificates.
-/
import OptimalConvergenceRates.GeneralArchimedean.PositiveCoefficientCertificate
import OptimalConvergenceRates.GeneralArchimedean.Certificates

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- Common budget for one scalar multiple of a power in a
positive-coefficient substitution certificate. -/
def positiveSubstitutionTermBound
    (D : ℕ) (K G Ha : ℝ) : ℝ :=
  (K + 1) * (G + 1) ^ D * (Ha + 1)

/-- A nonnegative scalar multiple of a bounded module element's power has a
bounded certificate at one common order. -/
theorem bounded_C_mul_pow_mem_of_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ} {r D k : ℕ}
    {Ha c K G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (hc : 0 ≤ c) (hcK : c ≤ K) (hK : 0 ≤ K)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G)
    (hk : k ≤ D) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (C c * a ^ k) (r + D * a.totalDegree)
      (positiveSubstitutionTermBound D K G Ha)) := by
  have hHa : 0 ≤ Ha := ca.bound_nonneg
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hbase : 1 ≤ G + 1 := by linarith
  have hpow : G ^ k ≤ (G + 1) ^ D := by
    exact (pow_le_pow_left₀ hG0 (by linarith) k).trans
      (pow_le_pow_right₀ hbase hk)
  have hc1 : c ≤ K + 1 := by linarith
  have hnumeric :
      c * G ^ k ≤ positiveSubstitutionTermBound D K G Ha := by
    unfold positiveSubstitutionTermBound
    calc
      c * G ^ k ≤ (K + 1) * (G + 1) ^ D := by
        gcongr
      _ ≤ ((K + 1) * (G + 1) ^ D) * (Ha + 1) := by
        exact le_mul_of_one_le_right (mul_nonneg (by linarith) (by positivity))
          (by linarith)
  have htermNorm :
      coeffL1Norm (C c * a ^ k) ≤ c * G ^ k := by
    calc
      coeffL1Norm (C c * a ^ k) ≤ |c| * coeffL1Norm (a ^ k) :=
        coeffL1Norm_C_mul_le c (a ^ k)
      _ = c * coeffL1Norm (a ^ k) := by rw [abs_of_nonneg hc]
      _ ≤ c * coeffL1Norm a ^ k :=
        mul_le_mul_of_nonneg_left (coeffL1Norm_pow_le a k) hc
      _ ≤ c * G ^ k := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (coeffL1Norm_nonneg a) haNorm k) hc
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have hsos : IsSOS (C c * a ^ (2 * j)) := by
      have hraw : IsSOS (C c * (a ^ j) ^ 2) :=
        IsSOS_mul (IsSOS_C_nonneg c hc) (IsSOS_sq (a ^ j))
      convert hraw using 1
      rw [show 2 * j = j * 2 by omega, pow_mul]
    have hdegree :
        (C c * a ^ (2 * j)).totalDegree ≤
          r + D * a.totalDegree := by
      calc
        (C c * a ^ (2 * j)).totalDegree ≤
            (2 * j) * a.totalDegree := by
          calc
            _ ≤ (C c : MvPolynomial (Fin n) ℝ).totalDegree +
                (a ^ (2 * j)).totalDegree :=
              MvPolynomial.totalDegree_mul _ _
            _ ≤ 0 + (2 * j) * a.totalDegree :=
              Nat.add_le_add (MvPolynomial.totalDegree_C c).le
                (MvPolynomial.totalDegree_pow _ _)
            _ = _ := by simp
        _ ≤ r + D * a.totalDegree := by
          exact (Nat.mul_le_mul_right a.totalDegree hk).trans
            (Nat.le_add_left _ r)
    let cert := BoundedQuadraticModuleCertificate.ofSOS g
      (C c * a ^ (2 * j)) hsos hdegree
    exact ⟨cert.weakenBound (htermNorm.trans hnumeric)⟩
  · let q : MvPolynomial (Fin n) ℝ := C c * (a ^ j) ^ 2
    have hqSOS : IsSOS q :=
      IsSOS_mul (IsSOS_C_nonneg c hc) (IsSOS_sq (a ^ j))
    have hqNorm : coeffL1Norm q ≤ c * G ^ (2 * j) := by
      dsimp [q]
      calc
        coeffL1Norm (C c * (a ^ j) ^ 2) ≤
            |c| * coeffL1Norm ((a ^ j) ^ 2) :=
          coeffL1Norm_C_mul_le _ _
        _ = c * coeffL1Norm (a ^ (2 * j)) := by
          rw [abs_of_nonneg hc, show (a ^ j) ^ 2 = a ^ (2 * j) by
            rw [show 2 * j = j * 2 by omega, pow_mul]]
        _ ≤ c * coeffL1Norm a ^ (2 * j) :=
          mul_le_mul_of_nonneg_left (coeffL1Norm_pow_le a (2 * j)) hc
        _ ≤ c * G ^ (2 * j) := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (coeffL1Norm_nonneg a) haNorm _) hc
    have hqDegree : q.totalDegree ≤ (2 * j) * a.totalDegree := by
      dsimp [q]
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
        _ = (2 * j) * a.totalDegree := by ring
    have craw := ca.sosMulOfNormLe hqSOS hqNorm
    have hkEven : 2 * j ≤ D := by omega
    have horder : q.totalDegree + r ≤ r + D * a.totalDegree := by
      calc
        q.totalDegree + r ≤ (2 * j) * a.totalDegree + r :=
          Nat.add_le_add_right hqDegree r
        _ ≤ D * a.totalDegree + r :=
          Nat.add_le_add_right
            (Nat.mul_le_mul_right a.totalDegree hkEven) r
        _ = r + D * a.totalDegree := by omega
    have ceq : q * a = C c * a ^ (2 * j + 1) := by
      have hjpow : (a ^ j) ^ 2 = a ^ (2 * j) := by
        rw [show 2 * j = j * 2 by omega, pow_mul]
      dsimp [q]
      rw [hjpow, pow_succ]
      ring
    have hpowEven : G ^ (2 * j) ≤ (G + 1) ^ D := by
      exact (pow_le_pow_left₀ hG0 (by linarith) (2 * j)).trans
        (pow_le_pow_right₀ hbase hkEven)
    have hbaseTerm :
        c * G ^ (2 * j) ≤ (K + 1) * (G + 1) ^ D := by
      gcongr
    exact ⟨((craw.mono horder).congr ceq).weakenBound
      (by
        unfold positiveSubstitutionTermBound
        calc
          c * G ^ (2 * j) * Ha ≤
              ((K + 1) * (G + 1) ^ D) * Ha :=
            mul_le_mul_of_nonneg_right hbaseTerm hHa
          _ ≤ ((K + 1) * (G + 1) ^ D) * (Ha + 1) :=
            mul_le_mul_of_nonneg_left (by linarith)
              (mul_nonneg (by linarith) (by positivity)))⟩

end OptimalConvergenceRates.GeneralArchimedean

end

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot

variable {n m : ℕ}

/-- Coefficient budget for substituting a bounded module element into a
coefficientwise nonnegative univariate polynomial. -/
def positiveSubstitutionCertificateBound
    (P : Polynomial ℝ) (G Ha : ℝ) : ℝ :=
  (P.natDegree + 1 : ℕ) *
    positiveSubstitutionTermBound P.natDegree
      (polynomialCoeffL1Norm P) G Ha

theorem bounded_polynomialSubst_mem_of_coeffNonneg_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ} {r : ℕ} {Ha G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (P : Polynomial ℝ) (hP : CoeffNonneg P)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (polynomialSubst a P)
      (r + P.natDegree * a.totalDegree)
      (positiveSubstitutionCertificateBound P G Ha)) := by
  let S := Finset.range (P.natDegree + 1)
  let K := polynomialCoeffL1Norm P
  let HT := positiveSubstitutionTermBound P.natDegree K G Ha
  have hK : 0 ≤ K := polynomialCoeffL1Norm_nonneg P
  obtain ⟨csum⟩ := BoundedQuadraticModuleCertificate.sum_nonempty S
    (fun k => C (P.coeff k) * a ^ k)
    (fun k hk => by
      have hkD : k ≤ P.natDegree := by
        have := Finset.mem_range.mp hk
        omega
      have hcoeff : P.coeff k ≤ K := by
        rw [← abs_of_nonneg (hP k)]
        exact abs_polynomial_coeff_le_polynomialCoeffL1Norm P k
      simpa [HT, K] using
        bounded_C_mul_pow_mem_of_mem_at ca (hP k) hcoeff hK
          hG haNorm hkD)
  have cfinal : BoundedQuadraticModuleCertificate g
      (polynomialSubst a P)
      (r + P.natDegree * a.totalDegree)
      ((S.card : ℝ) * HT) :=
    csum.congr (by
      rw [polynomialSubst, Polynomial.aeval_eq_sum_range]
      simp only [MvPolynomial.smul_eq_C_mul, S])
  exact ⟨by
    simpa [positiveSubstitutionCertificateBound, S, HT, K] using cfinal⟩

/-- Explicit bounded certificate for a substituted square-minus-one
polynomial with nonnegative coefficients and constant coefficient one. -/
theorem bounded_polynomialSubst_sq_sub_one_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a : MvPolynomial (Fin n) ℝ} {r : ℕ} {Ha G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (V : Polynomial ℝ) (hV : CoeffNonneg V)
    (hV0 : V.coeff 0 = 1)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (polynomialSubst a V ^ 2 - 1)
      (r + 2 * V.natDegree * a.totalDegree)
      (positiveSubstitutionCertificateBound (V ^ 2 - 1) G Ha)) := by
  obtain ⟨craw⟩ := bounded_polynomialSubst_mem_of_coeffNonneg_at
    ca (V ^ 2 - 1) (coeffNonneg_sq_sub_one hV hV0) hG haNorm
  have hdegree : (V ^ 2 - 1).natDegree ≤ 2 * V.natDegree := by
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le Polynomial.natDegree_pow_le (by simp))
  have horder :
      r + (V ^ 2 - 1).natDegree * a.totalDegree ≤
        r + 2 * V.natDegree * a.totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree hdegree) r
  exact ⟨(craw.mono horder).congr (by
    simp [map_sub, map_pow, polynomialSubst])⟩

end OptimalConvergenceRates.GeneralArchimedean

end
