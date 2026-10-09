/-
  Asymptotic estimates for the bounded multiplier and the Chebyshev degree
  used to eliminate the appended perturbation generator.
-/
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeAssembly
import OptimalConvergenceRates.GeneralArchimedean.SharpBudgetAsymptotics

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Exponent constant controlling the normalization envelope of a bounded
multiplier whose order grows linearly in `1 + log x`. -/
def boundedMultiplierLogSquareConstant
    (n : ℕ) (B Dr Kh : ℝ) : ℝ :=
  Real.log 3 +
    (((n : ℝ) * (Dr + 1)) +
      (Real.log 3 + (2 * Kh + Dr * Real.log B)))

theorem boundedMultiplierLogSquareConstant_nonneg
    (n : ℕ) {B Dr Kh : ℝ}
    (hB : 1 ≤ B) (hDr : 0 ≤ Dr) (hKh : 0 ≤ Kh) :
    0 ≤ boundedMultiplierLogSquareConstant n B Dr Kh := by
  unfold boundedMultiplierLogSquareConstant
  have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  positivity

/-- The coefficient envelope used to normalize the appended-generator
multiplier stays in the same log-square class as the refutation budget. -/
theorem boundedMultiplierEnvelope_le_logSquareEnvelope
    {n r : ℕ} {B H Dr Kh x : ℝ}
    (hB : 1 ≤ B) (hH : 0 ≤ H)
    (hDr : 0 ≤ Dr) (hKh : 0 ≤ Kh) (hx : 1 ≤ x)
    (hr : (r : ℝ) ≤ Dr * (1 + Real.log x))
    (hHbound : H ≤ logSquareEnvelope Kh x) :
    boundedMultiplierEnvelope n r B H ≤
      logSquareEnvelope
        (boundedMultiplierLogSquareConstant n B Dr Kh) x := by
  let Kr := (n : ℝ) * (Dr + 1)
  let Kprod := 2 * Kh + Dr * Real.log B
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hDr1 : 0 ≤ Dr + 1 := by linarith
  have hrplus : ((r + 1 : ℕ) : ℝ) ≤
      (Dr + 1) * (1 + Real.log x) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hrplus0 : 0 ≤ ((r + 1 : ℕ) : ℝ) := by positivity
  have hrplusEnv : ((r + 1 : ℕ) : ℝ) ≤
      logSquareEnvelope (Dr + 1) x :=
    linear_log_le_logSquareEnvelope hrplus0 hDr1 hx hrplus
  have hcountCast : (boundedMonomialCount n r : ℝ) ≤
      ((r + 1 : ℕ) : ℝ) ^ n := by
    exact_mod_cast boundedMonomialCount_le_pow n r
  have hcount : (boundedMonomialCount n r : ℝ) ≤
      logSquareEnvelope Kr x := by
    calc
      (boundedMonomialCount n r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ n := hcountCast
      _ ≤ logSquareEnvelope (Dr + 1) x ^ n :=
        pow_le_pow_left₀ hrplus0 hrplusEnv n
      _ = logSquareEnvelope Kr x := by
        rw [logSquareEnvelope_pow]
  have hHsq : (H / 2) ^ 2 ≤ logSquareEnvelope (2 * Kh) x := by
    have hhalf : 0 ≤ H / 2 := by positivity
    have hhalfH : H / 2 ≤ H := by linarith
    calc
      (H / 2) ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ hhalf hhalfH 2
      _ ≤ logSquareEnvelope Kh x ^ 2 :=
        pow_le_pow_left₀ hH hHbound 2
      _ = logSquareEnvelope (2 * Kh) x := by
        rw [logSquareEnvelope_pow]
        norm_num
  have hBpow : B ^ r ≤
      logSquareEnvelope (Dr * Real.log B) x :=
    fixed_pow_le_logSquareEnvelope hB hDr hx hr
  have hprod : (H / 2) ^ 2 * B ^ r ≤
      logSquareEnvelope Kprod x := by
    dsimp [Kprod]
    exact mul_le_logSquareEnvelope (sq_nonneg _) (pow_nonneg (by linarith) _)
      hHsq hBpow
  have hKprod : 0 ≤ Kprod := by
    dsimp [Kprod]
    exact add_nonneg (mul_nonneg (by norm_num) hKh)
      (mul_nonneg hDr (Real.log_nonneg hB))
  have hinside : (H / 2) ^ 2 * B ^ r + 1 ≤
      logSquareEnvelope (Real.log 3 + Kprod) x :=
    add_one_le_logSquareEnvelope hKprod hx hprod
  have hpoly : polynomialEnvelopeBound n r B H ≤
      logSquareEnvelope (Kr + (Real.log 3 + Kprod)) x := by
    unfold polynomialEnvelopeBound
    exact mul_le_logSquareEnvelope (by positivity)
      (by positivity) hcount hinside
  have hKpoly : 0 ≤ Kr + (Real.log 3 + Kprod) := by
    dsimp [Kr]
    have hlog3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  unfold boundedMultiplierEnvelope boundedMultiplierLogSquareConstant
  simpa [Kr, Kprod] using
    (add_le_logSquareEnvelope
      (K := 0) (L := Kr + (Real.log 3 + Kprod)) zero_le_one
      (by unfold polynomialEnvelopeBound; positivity)
      (by norm_num) hKpoly hx
      (by simp [logSquareEnvelope]) hpoly)

/-- Exponent constant controlling the logarithm in the canonical Chebyshev
degree after multiplier normalization. -/
def chebyshevLogSquareConstant (K : ℝ) : ℝ := Real.log 5 + K

/-- If the normalization constant is log-square bounded, the selected
Chebyshev degree has the required inverse-square-root/log-square scale. -/
theorem chebyshevDegree_le_invSqrt_logSquare
    {epsilon Czero U K x : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hxdef : x = epsilon⁻¹)
    (hU : 2 ≤ U) (hK : 0 ≤ K)
    (hCzero : 1 ≤ Czero)
    (hCbound : Czero ≤ logSquareEnvelope K x) :
    (chebyshevDegree epsilon Czero⁻¹ U : ℝ) ≤
      (Real.sqrt (2 / U))⁻¹ * chebyshevLogSquareConstant K /
          Real.sqrt epsilon * logSquareScale x + 1 := by
  subst x
  have hx : 1 ≤ epsilon⁻¹ := (one_le_inv₀ hepsilon).2 hepsilon1
  have hUpos : 0 < U := by linarith
  have htwoU : 0 < 2 / U := div_pos (by norm_num) hUpos
  have hc : 0 < Czero⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hCzero)
  have hsmall : (2 / U) * epsilon ≤ 1 := by
    have hfac : 2 / U ≤ 1 := (div_le_one hUpos).2 hU
    nlinarith [mul_nonneg htwoU.le hepsilon.le]
  have hbase := chebyshevDegree_cast_le hepsilon hc hUpos hsmall
  have hEone : 1 ≤ logSquareEnvelope K epsilon⁻¹ :=
    one_le_logSquareEnvelope hK hx
  have hepsC : epsilon / Czero⁻¹ ≤ logSquareEnvelope K epsilon⁻¹ := by
    rw [div_eq_mul_inv, inv_inv]
    exact (mul_le_of_le_one_left (by positivity) hepsilon1).trans hCbound
  have harg : 2 * (1 + epsilon / Czero⁻¹) ≤
      logSquareEnvelope (Real.log 5 + K) epsilon⁻¹ := by
    have hfour : (4 : ℝ) ≤
        logSquareEnvelope (Real.log 5) epsilon⁻¹ := by
      have heq : Real.log ((4 : ℝ) + 1) = Real.log 5 := by norm_num
      rw [← heq]
      exact le_logSquareEnvelope_log_add_one (by norm_num) hx
    calc
      2 * (1 + epsilon / Czero⁻¹) ≤
          4 * logSquareEnvelope K epsilon⁻¹ := by nlinarith
      _ ≤ logSquareEnvelope (Real.log 5) epsilon⁻¹ *
          logSquareEnvelope K epsilon⁻¹ :=
        mul_le_mul_of_nonneg_right hfour
          (logSquareEnvelope_pos K epsilon⁻¹).le
      _ = logSquareEnvelope (Real.log 5 + K) epsilon⁻¹ :=
        logSquareEnvelope_mul _ _ _
  have hargpos : 0 < 2 * (1 + epsilon / Czero⁻¹) := by positivity
  have hlog : Real.log (2 * (1 + epsilon / Czero⁻¹)) ≤
      chebyshevLogSquareConstant K * logSquareScale epsilon⁻¹ := by
    have := Real.log_le_log hargpos harg
    simpa [logSquareEnvelope, chebyshevLogSquareConstant] using this
  have hlog0 : 0 ≤ Real.log (2 * (1 + epsilon / Czero⁻¹)) := by
    apply Real.log_nonneg
    have : 0 < epsilon / Czero⁻¹ := div_pos hepsilon hc
    linarith
  have hsqrtfac : 0 < Real.sqrt (2 / U) := Real.sqrt_pos.2 htwoU
  have hsqrteps : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon
  have hsqrt : Real.sqrt ((2 / U) * epsilon) =
      Real.sqrt (2 / U) * Real.sqrt epsilon := by
    rw [Real.sqrt_mul htwoU.le]
  calc
    (chebyshevDegree epsilon Czero⁻¹ U : ℝ) ≤
        Real.log (2 * (1 + epsilon / Czero⁻¹)) /
          Real.sqrt ((2 / U) * epsilon) + 1 := hbase
    _ ≤ (chebyshevLogSquareConstant K * logSquareScale epsilon⁻¹) /
          Real.sqrt ((2 / U) * epsilon) + 1 := by
      gcongr
    _ = (Real.sqrt (2 / U))⁻¹ * chebyshevLogSquareConstant K /
          Real.sqrt epsilon * logSquareScale epsilon⁻¹ + 1 := by
      rw [hsqrt]
      field_simp


/-- A convenient linear upper bound for the three maxima in the tracked
elimination order. -/
theorem perturbationEliminationOrder_cast_le
    (degreeP refutationOrder envelopeOrder chebyshevOrder : ℕ) :
    (perturbationEliminationOrder degreeP refutationOrder envelopeOrder
        chebyshevOrder : ℝ) ≤
      envelopeOrder + 2 * refutationOrder +
        6 * (chebyshevOrder + 1) * (degreeP + 1) := by
  unfold perturbationEliminationOrder
  norm_num only [Nat.cast_max, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  apply max_le
  · have hd : (0 : ℝ) ≤ degreeP := by positivity
    have hN : (0 : ℝ) ≤ chebyshevOrder := by positivity
    nlinarith [mul_nonneg hN hd]
  · apply max_le
    · have hd : (0 : ℝ) ≤ degreeP := by positivity
      have hN : (0 : ℝ) ≤ chebyshevOrder := by positivity
      nlinarith [mul_nonneg hN hd]
    · have hd : (0 : ℝ) ≤ degreeP := by positivity
      have hN : (0 : ℝ) ≤ chebyshevOrder := by positivity
      nlinarith [mul_nonneg hN hd]

/-- Fixed coefficient multiplying the inverse-square-root/log-square scale
after the refutation and Chebyshev bounds are inserted. -/
def perturbationEliminationLogConstant
    (degreeP : ℕ) (Dr Kn : ℝ) : ℝ :=
  2 * Dr + 6 * (Kn + 2) * (degreeP + 1)

theorem perturbationEliminationLogConstant_nonneg
    (degreeP : ℕ) {Dr Kn : ℝ} (hDr : 0 ≤ Dr) (hKn : 0 ≤ Kn) :
    0 ≤ perturbationEliminationLogConstant degreeP Dr Kn := by
  unfold perturbationEliminationLogConstant
  positivity

/-- Substituting logarithmic refutation order and
inverse-square-root/log-square Chebyshev bounds into the explicit
elimination order gives exactly the degree scale used by `UpperBound`. -/
theorem perturbationEliminationOrder_le_invSqrt_logSquare
    {degreeP refutationOrder envelopeOrder chebyshevOrder : ℕ}
    {epsilon Dr Kn : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hDr : 0 ≤ Dr) (hKn : 0 ≤ Kn)
    (hrefutation :
      (refutationOrder : ℝ) ≤
        Dr * (1 + Real.log epsilon⁻¹))
    (hchebyshev :
      (chebyshevOrder : ℝ) ≤
        Kn / Real.sqrt epsilon * logSquareScale epsilon⁻¹ + 1) :
    (perturbationEliminationOrder degreeP refutationOrder envelopeOrder
        chebyshevOrder : ℝ) ≤
      envelopeOrder +
        perturbationEliminationLogConstant degreeP Dr Kn /
          Real.sqrt epsilon * logSquareScale epsilon⁻¹ := by
  let L : ℝ := 1 + Real.log epsilon⁻¹
  let Q : ℝ := (Real.sqrt epsilon)⁻¹ * L ^ 2
  have hx : 1 ≤ epsilon⁻¹ := (one_le_inv₀ hepsilon).2 hepsilon1
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hx]
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hsqrt : 0 < Real.sqrt epsilon := Real.sqrt_pos.2 hepsilon
  have hsqrt_le : Real.sqrt epsilon ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hepsilon1
  have hinv : 1 ≤ (Real.sqrt epsilon)⁻¹ :=
    (one_le_inv₀ hsqrt).2 hsqrt_le
  have hLsq : L ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hQone : 1 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_nonneg (sub_nonneg.mpr hinv)
      (sub_nonneg.mpr (show 1 ≤ L ^ 2 by nlinarith))]
  have hLQ : L ≤ Q := by
    dsimp [Q]
    calc
      L ≤ L ^ 2 := hLsq
      _ ≤ (Real.sqrt epsilon)⁻¹ * L ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg L) hinv
  have hrefutation' : (refutationOrder : ℝ) ≤ Dr * Q := by
    calc
      (refutationOrder : ℝ) ≤ Dr * L := by
        simpa [L] using hrefutation
      _ ≤ Dr * Q := mul_le_mul_of_nonneg_left hLQ hDr
  have hchebyshev' :
      (chebyshevOrder : ℝ) + 1 ≤ (Kn + 2) * Q := by
    have hQform :
        Kn / Real.sqrt epsilon * logSquareScale epsilon⁻¹ = Kn * Q := by
      dsimp [Q, L, logSquareScale]
      rw [div_eq_mul_inv]
      ring
    rw [hQform] at hchebyshev
    nlinarith
  have hbase := perturbationEliminationOrder_cast_le
    degreeP refutationOrder envelopeOrder chebyshevOrder
  have hdegree : (0 : ℝ) ≤ degreeP + 1 := by positivity
  calc
    (perturbationEliminationOrder degreeP refutationOrder envelopeOrder
        chebyshevOrder : ℝ) ≤
        envelopeOrder + 2 * refutationOrder +
          6 * (chebyshevOrder + 1) * (degreeP + 1) := hbase
    _ ≤ envelopeOrder +
        perturbationEliminationLogConstant degreeP Dr Kn * Q := by
      unfold perturbationEliminationLogConstant
      nlinarith [mul_nonneg (sub_nonneg.mpr hchebyshev') hdegree,
        mul_nonneg (show (0 : ℝ) ≤ 6 * (degreeP + 1) by positivity)
          (sub_nonneg.mpr hchebyshev')]
    _ = envelopeOrder +
        perturbationEliminationLogConstant degreeP Dr Kn /
          Real.sqrt epsilon * logSquareScale epsilon⁻¹ := by
      dsimp [Q, L, logSquareScale]
      rw [div_eq_mul_inv]
      ring

end OptimalConvergenceRates.GeneralArchimedean

end
