/-
  Elementary calculus for uniform `exp(K (1 + log x)^2)` bounds.
-/
import OptimalConvergenceRates.GeneralArchimedean.UnivariateCoefficientNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace OptimalConvergenceRates.GeneralArchimedean

def logSquareScale (x : ℝ) : ℝ := (1 + Real.log x) ^ 2

def logSquareEnvelope (K x : ℝ) : ℝ :=
  Real.exp (K * logSquareScale x)

theorem one_le_logSquareScale {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ logSquareScale x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  unfold logSquareScale
  nlinarith [sq_nonneg (Real.log x)]

theorem logSquareEnvelope_pos (K x : ℝ) :
    0 < logSquareEnvelope K x := by
  exact Real.exp_pos _

theorem one_le_logSquareEnvelope
    {K x : ℝ} (hK : 0 ≤ K) (hx : 1 ≤ x) :
    1 ≤ logSquareEnvelope K x := by
  apply Real.one_le_exp
  exact mul_nonneg hK (zero_le_one.trans (one_le_logSquareScale hx))

theorem logSquareEnvelope_mono
    {K L x : ℝ} (hKL : K ≤ L) (hx : 1 ≤ x) :
    logSquareEnvelope K x ≤ logSquareEnvelope L x := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right hKL
    (zero_le_one.trans (one_le_logSquareScale hx))

theorem logSquareEnvelope_mul (K L x : ℝ) :
    logSquareEnvelope K x * logSquareEnvelope L x =
      logSquareEnvelope (K + L) x := by
  unfold logSquareEnvelope
  rw [← Real.exp_add]
  congr 1
  ring

theorem logSquareEnvelope_pow (K x : ℝ) (n : ℕ) :
    logSquareEnvelope K x ^ n =
      logSquareEnvelope ((n : ℝ) * K) x := by
  unfold logSquareEnvelope
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Every fixed nonnegative constant is absorbed uniformly by one
log-square envelope. -/
theorem le_logSquareEnvelope_log_add_one
    {c x : ℝ} (hc : 0 ≤ c) (hx : 1 ≤ x) :
    c ≤ logSquareEnvelope (Real.log (c + 1)) x := by
  have hc1 : 0 < c + 1 := by linarith
  have hlog : 0 ≤ Real.log (c + 1) :=
    Real.log_nonneg (by linarith)
  calc
    c ≤ c + 1 := by linarith
    _ = Real.exp (Real.log (c + 1)) := (Real.exp_log hc1).symm
    _ ≤ Real.exp (Real.log (c + 1) * logSquareScale x) := by
      apply Real.exp_le_exp.mpr
      exact le_mul_of_one_le_right hlog (one_le_logSquareScale hx)
    _ = logSquareEnvelope (Real.log (c + 1)) x := rfl

theorem mul_le_logSquareEnvelope
    {a b K L x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haK : a ≤ logSquareEnvelope K x)
    (hbL : b ≤ logSquareEnvelope L x) :
    a * b ≤ logSquareEnvelope (K + L) x := by
  rw [← logSquareEnvelope_mul]
  exact mul_le_mul haK hbL hb (logSquareEnvelope_pos K x).le

/-- Addition costs only one further fixed logarithmic constant. -/
theorem add_le_logSquareEnvelope
    {a b K L x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hx : 1 ≤ x)
    (haK : a ≤ logSquareEnvelope K x)
    (hbL : b ≤ logSquareEnvelope L x) :
    a + b ≤ logSquareEnvelope
      (Real.log 3 + K + L) x := by
  have hEK := one_le_logSquareEnvelope hK hx
  have hEL := one_le_logSquareEnvelope hL hx
  have hcommonA : a ≤
      logSquareEnvelope K x * logSquareEnvelope L x :=
    haK.trans (le_mul_of_one_le_right (logSquareEnvelope_pos K x).le hEL)
  have hcommonB : b ≤
      logSquareEnvelope K x * logSquareEnvelope L x :=
    hbL.trans (le_mul_of_one_le_left (logSquareEnvelope_pos L x).le hEK)
  have htwo : (2 : ℝ) ≤ logSquareEnvelope (Real.log 3) x := by
    have heq : Real.log ((2 : ℝ) + 1) = Real.log 3 := by norm_num
    rw [← heq]
    exact le_logSquareEnvelope_log_add_one (c := 2) (x := x) (by norm_num) hx
  calc
    a + b ≤ 2 *
        (logSquareEnvelope K x * logSquareEnvelope L x) := by
      linarith
    _ ≤ logSquareEnvelope (Real.log 3) x *
        (logSquareEnvelope K x * logSquareEnvelope L x) := by
      exact mul_le_mul_of_nonneg_right htwo
        (mul_nonneg (logSquareEnvelope_pos K x).le
          (logSquareEnvelope_pos L x).le)
    _ = logSquareEnvelope (Real.log 3 + K + L) x := by
      rw [logSquareEnvelope_mul, logSquareEnvelope_mul]
      congr 1
      ring

/-- A fixed-base power with logarithmically growing exponent is bounded by
a log-square envelope. -/
theorem fixed_pow_le_logSquareEnvelope
    {c D x : ℝ} (hc : 1 ≤ c) (hD : 0 ≤ D) (hx : 1 ≤ x)
    {N : ℕ} (hN : (N : ℝ) ≤ D * (1 + Real.log x)) :
    c ^ N ≤ logSquareEnvelope (D * Real.log c) x := by
  let L : ℝ := 1 + Real.log x
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hx]
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  apply (Real.log_le_iff_le_exp (pow_pos (zero_lt_one.trans_le hc) _)).mp
  rw [Real.log_pow]
  unfold logSquareScale
  dsimp [L] at hN hL ⊢
  have hmul := mul_le_mul_of_nonneg_right hN hlogc
  calc
    (N : ℝ) * Real.log c ≤
        D * (1 + Real.log x) * Real.log c := by
      simpa [mul_assoc] using hmul
    _ ≤ D * Real.log c * (1 + Real.log x) ^ 2 := by
      have hscale : 1 + Real.log x ≤ (1 + Real.log x) ^ 2 := by
        nlinarith [sq_nonneg (Real.log x)]
      nlinarith [mul_nonneg hD hlogc]

/-- The self-power appearing in quantitative Markov bounds is still only
exponential in the square of the logarithmic scale. -/
theorem nat_self_pow_le_logSquareEnvelope
    {D x : ℝ} (hD : 0 ≤ D) (hx : 1 ≤ x)
    {N : ℕ} (hNpos : 1 ≤ N)
    (hN : (N : ℝ) ≤ D * (1 + Real.log x)) :
    (N : ℝ) ^ (2 * N) ≤
      logSquareEnvelope (2 * D ^ 2) x := by
  let L : ℝ := 1 + Real.log x
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hx]
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hlogN : Real.log (N : ℝ) ≤ D * L := by
    exact (Real.log_le_self (by positivity)).trans (by simpa [L] using hN)
  apply (Real.log_le_iff_le_exp (pow_pos (by positivity) _)).mp
  rw [Real.log_pow]
  unfold logSquareScale
  have h2N : ((2 * N : ℕ) : ℝ) ≤ 2 * D * L := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    dsimp [L] at hN ⊢
    nlinarith
  have hmul := mul_le_mul h2N hlogN hlogN0 (by positivity)
  dsimp [L] at hmul ⊢
  nlinarith

/-- A nonnegative quantity growing at most linearly in `1 + log x` is
absorbed by a log-square envelope. -/
theorem linear_log_le_logSquareEnvelope
    {a D x : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D) (hx : 1 ≤ x)
    (haD : a ≤ D * (1 + Real.log x)) :
    a ≤ logSquareEnvelope D x := by
  let L : ℝ := 1 + Real.log x
  have hL : 1 ≤ L := by
    dsimp [L]
    linarith [Real.log_nonneg hx]
  have hscale : L ≤ L ^ 2 := by
    nlinarith [sq_nonneg (L - 1)]
  have hlinearSquare : D * L ≤ D * L ^ 2 :=
    mul_le_mul_of_nonneg_left hscale hD
  calc
    a ≤ D * L := by simpa [L] using haD
    _ ≤ D * L ^ 2 := hlinearSquare
    _ ≤ D * L ^ 2 + 1 := by linarith
    _ ≤ Real.exp (D * L ^ 2) := Real.add_one_le_exp _
    _ = logSquareEnvelope D x := by
      simp only [logSquareEnvelope, logSquareScale]
      rfl

/-- Taking a logarithm turns a fixed multiple of a fixed power into a
linear bound in `1 + log x`. -/
theorem one_add_log_le_of_le_const_mul_pow
    {x y C : ℝ} {q : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hC : 1 ≤ C)
    (hybound : y ≤ C * x ^ q) :
    1 + Real.log y ≤
      (1 + Real.log C + q) * (1 + Real.log x) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog := Real.log_le_log hypos hybound
  rw [Real.log_mul hCpos.ne' (pow_ne_zero q hxpos.ne'),
    Real.log_pow] at hlog
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ q by positivity) hlogx]

/-- A log-square envelope may be re-based along a linear bound between the
two logarithmic scales. -/
theorem logSquareEnvelope_le_of_logScale_le
    {K D x y : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hscale : 1 + Real.log y ≤ D * (1 + Real.log x)) :
    logSquareEnvelope K y ≤ logSquareEnvelope (K * D ^ 2) x := by
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  apply Real.exp_le_exp.mpr
  unfold logSquareScale
  have hsq : (1 + Real.log y) ^ 2 ≤
      (D * (1 + Real.log x)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hscale 2
  calc
    K * (1 + Real.log y) ^ 2 ≤
        K * (D * (1 + Real.log x)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hK
    _ = (K * D ^ 2) * (1 + Real.log x) ^ 2 := by ring



/-- The varying base `x` itself is absorbed by the unit log-square
envelope. -/
theorem self_le_logSquareEnvelope_one {x : ℝ} (hx : 1 ≤ x) :
    x ≤ logSquareEnvelope 1 x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  rw [← Real.exp_log hxpos]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hscale : Real.log x ≤ (1 + Real.log x) ^ 2 := by
    nlinarith [sq_nonneg (Real.log x)]
  simpa [logSquareEnvelope, logSquareScale] using hscale
end OptimalConvergenceRates.GeneralArchimedean
