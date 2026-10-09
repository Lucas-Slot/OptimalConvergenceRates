/-
  The analytic inversion from an epsilon-dependent degree estimate to the
  (log r)^4 / r^2 certificate rate.
-/
import OptimalConvergenceRates.GeneralArchimedean.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- The degree scale produced by the conversion-and-elimination argument. -/
def putinarDegreeCost (D K epsilon : ℝ) : ℝ :=
  D + K / Real.sqrt epsilon *
    (1 + Real.log epsilon⁻¹) ^ 2

/-- The fourth power of the logarithm admits a convenient elementary
linear majorant. -/
theorem log_pow_four_le_256_mul
    {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 4 ≤ 256 * x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  let y := Real.sqrt (Real.sqrt x)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy4 : y ^ 4 = x := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (Real.sqrt x) ^ 2 := by
        rw [Real.sq_sqrt (Real.sqrt_nonneg x)]
      _ = x := Real.sq_sqrt hx0
  have hlog : Real.log x = 4 * Real.log y := by
    dsimp [y]
    rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx0]
    ring
  have hlogy : Real.log y ≤ y := Real.log_le_self hy0
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hupper : Real.log x ≤ 4 * y := by
    rw [hlog]
    linarith
  have hpow := pow_le_pow_left₀ hlog0 hupper 4
  calc
    Real.log x ^ 4 ≤ (4 * y) ^ 4 := hpow
    _ = 256 * y ^ 4 := by ring
    _ = 256 * x := by rw [hy4]

/-- At the proposed perturbation scale, the logarithmic factor appearing in
the degree cost is at most three times log r. -/
theorem one_add_log_inv_scale_le
    {A x : ℝ} (hA : 1 ≤ A) (hx : 0 < x)
    (hlogx : 1 ≤ Real.log x) :
    1 + Real.log (A * Real.log x ^ 4 / x ^ 2)⁻¹ ≤
      3 * Real.log x := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hlpos : 0 < Real.log x := zero_lt_one.trans_le hlogx
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hloglog : 0 ≤ Real.log (Real.log x) :=
    Real.log_nonneg hlogx
  have hformula :
      Real.log (A * Real.log x ^ 4 / x ^ 2)⁻¹ =
        -(Real.log A + 4 * Real.log (Real.log x) -
          2 * Real.log x) := by
    rw [Real.log_inv]
    rw [Real.log_div (mul_ne_zero hApos.ne' (pow_ne_zero _ hlpos.ne'))
      (pow_ne_zero _ hx.ne')]
    rw [Real.log_mul hApos.ne' (pow_ne_zero _ hlpos.ne')]
    rw [Real.log_pow, Real.log_pow]
    ring
  rw [hformula]
  linarith

/-- The proposed perturbation is positive and at most one beyond an explicit
threshold. -/
theorem logFour_scale_pos_and_le_one
    {A x : ℝ} (hA : 0 < A) (hx : 1 < x)
    (hthreshold : 256 * A ≤ x) :
    0 < A * Real.log x ^ 4 / x ^ 2 ∧
      A * Real.log x ^ 4 / x ^ 2 ≤ 1 := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  constructor
  · positivity
  · have hlogbound := log_pow_four_le_256_mul hx.le
    have hscaled :
        A * Real.log x ^ 4 ≤ A * (256 * x) :=
      mul_le_mul_of_nonneg_left hlogbound hA.le
    have hright : A * (256 * x) ≤ x ^ 2 := by
      nlinarith
    rw [div_le_one (sq_pos_of_pos hxpos)]
    exact hscaled.trans hright

/-- Elementary cancellation of the square root at the logarithmic
perturbation scale. -/
theorem putinarDegreeCost_scale_le
    {D K A x : ℝ}
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hA : 1 ≤ A)
    (hlogx : 1 ≤ Real.log x)
    (hx : 0 < x)
    (hsmall : A * Real.log x ^ 4 / x ^ 2 ≤ 1)
    (hDsize : 2 * D ≤ x)
    (hKsize : 18 * K ≤ Real.sqrt A) :
    putinarDegreeCost D K
        (A * Real.log x ^ 4 / x ^ 2) ≤ x := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hlpos : 0 < Real.log x := zero_lt_one.trans_le hlogx
  let epsilon := A * Real.log x ^ 4 / x ^ 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hLnonneg : 0 ≤ 1 + Real.log epsilon⁻¹ := by
    have hinv : 1 ≤ epsilon⁻¹ := by
      exact (one_le_inv₀ hepsilon).2 (by simpa [epsilon] using hsmall)
    exact add_nonneg zero_le_one (Real.log_nonneg hinv)
  have hL :
      1 + Real.log epsilon⁻¹ ≤ 3 * Real.log x := by
    simpa [epsilon] using one_add_log_inv_scale_le hA hx hlogx
  have hLsq :
      (1 + Real.log epsilon⁻¹) ^ 2 ≤
        (3 * Real.log x) ^ 2 :=
    pow_le_pow_left₀ hLnonneg hL 2
  have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
  have hsqrt :
      Real.sqrt epsilon =
        Real.sqrt A * Real.log x ^ 2 / x := by
    dsimp [epsilon]
    rw [Real.sqrt_div (mul_nonneg hApos.le (pow_nonneg (le_of_lt hlpos) 4))]
    rw [Real.sqrt_mul hApos.le]
    rw [show Real.log x ^ 4 = (Real.log x ^ 2) ^ 2 by ring]
    rw [Real.sqrt_sq (sq_nonneg (Real.log x))]
    rw [Real.sqrt_sq hx.le]
  have hdenom : 0 < Real.sqrt A * Real.log x ^ 2 / x := by
    positivity
  have hcostTerm :
      K / Real.sqrt epsilon * (1 + Real.log epsilon⁻¹) ^ 2 ≤
        9 * K / Real.sqrt A * x := by
    rw [hsqrt]
    calc
      K / (Real.sqrt A * Real.log x ^ 2 / x) *
          (1 + Real.log epsilon⁻¹) ^ 2 ≤
        K / (Real.sqrt A * Real.log x ^ 2 / x) *
          (3 * Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_left hLsq (div_nonneg hK hdenom.le)
      _ = 9 * K / Real.sqrt A * x := by
        field_simp
        ring
  have hhalf : 9 * K / Real.sqrt A ≤ 1 / 2 := by
    rw [div_le_iff₀ hsqrtA]
    nlinarith
  have hlinear : 9 * K / Real.sqrt A * x ≤ x / 2 := by
    convert mul_le_mul_of_nonneg_right hhalf hx.le using 1;
      ring
  dsimp [putinarDegreeCost]
  dsimp [epsilon] at hcostTerm
  linarith

/-- Abstract quantitative input still required from the algebraic conversion:
a certificate at the square-root/log-squared degree cost. -/
def HasPutinarDegreeCostBound
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧
    ∀ {epsilon : ℝ}, 0 < epsilon → epsilon ≤ 1 →
      p + C epsilon ∈
        GenQuadraticModule g (Nat.ceil (putinarDegreeCost D K epsilon))

/-- Analytic inversion of a square-root/log-squared degree bound. -/
theorem upperRate_of_degreeCostBound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hcost : HasPutinarDegreeCostBound g p) :
    ∃ C₀ r₀, 0 < C₀ ∧ 0 < r₀ ∧
      ∀ r, r₀ ≤ r →
        p + C (C₀ * logFourOverSq r) ∈
          GenQuadraticModule g r := by
  obtain ⟨D, K, hD, hK, hcert⟩ := hcost
  let S := max 1 (18 * K)
  let A := S ^ 2
  have hS : 1 ≤ S := le_max_left _ _
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  have hA : 1 ≤ A := by
    dsimp [A]
    nlinarith
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hsqrtA : Real.sqrt A = S := by
    dsimp [A]
    exact Real.sqrt_sq hS0
  obtain ⟨r₀, hr₀⟩ := exists_nat_gt
    (max (Real.exp 1)
      (max (256 * A) (max (2 * D) 2)))
  have hr₀pos : 0 < r₀ := by
    have : (2 : ℝ) < r₀ := lt_of_le_of_lt
      ((le_max_right (2 * D) 2).trans
        ((le_max_right (256 * A) (max (2 * D) 2)).trans
          (le_max_right (Real.exp 1)
            (max (256 * A) (max (2 * D) 2)))))
      hr₀
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 2) this)
  refine ⟨A, r₀, hApos, hr₀pos, ?_⟩
  intro r hrr₀
  have hcast : (r₀ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrr₀
  have hrLower :
      max (Real.exp 1) (max (256 * A) (max (2 * D) 2)) <
        (r : ℝ) :=
    hr₀.trans_le hcast
  have hrex : Real.exp 1 ≤ (r : ℝ) :=
    (le_max_left _ _).trans hrLower.le
  have hrA : 256 * A ≤ (r : ℝ) :=
    (le_max_left (256 * A) (max (2 * D) 2)).trans
      ((le_max_right (Real.exp 1)
        (max (256 * A) (max (2 * D) 2))).trans hrLower.le)
  have hrD : 2 * D ≤ (r : ℝ) :=
    (le_max_left (2 * D) 2).trans
      ((le_max_right (256 * A) (max (2 * D) 2)).trans
        ((le_max_right (Real.exp 1)
          (max (256 * A) (max (2 * D) 2))).trans hrLower.le))
  have hrTwo : (2 : ℝ) ≤ (r : ℝ) :=
    (le_max_right (2 * D) 2).trans
      ((le_max_right (256 * A) (max (2 * D) 2)).trans
        ((le_max_right (Real.exp 1)
          (max (256 * A) (max (2 * D) 2))).trans hrLower.le))
  have hrNat : 2 ≤ r := by exact_mod_cast hrTwo
  have hmax : max r 2 = r := max_eq_left hrNat
  have hlog : 1 ≤ Real.log (r : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hrex
  let epsilon := A * logFourOverSq r
  have hepsilonEq :
      epsilon =
        A * Real.log (r : ℝ) ^ 4 / (r : ℝ) ^ 2 := by
    simp [epsilon, logFourOverSq, hmax]
    ring
  have hscaleExplicit := logFour_scale_pos_and_le_one hApos
    (show (1 : ℝ) < r by linarith) hrA
  have hscale : 0 < epsilon ∧ epsilon ≤ 1 := by
    rw [hepsilonEq]
    exact hscaleExplicit
  have hKsize : 18 * K ≤ Real.sqrt A := by
    rw [hsqrtA]
    exact le_max_right 1 (18 * K)
  have hdegree :
      putinarDegreeCost D K epsilon ≤ (r : ℝ) := by
    rw [hepsilonEq]
    exact putinarDegreeCost_scale_le hD hK hA hlog
      (show (0 : ℝ) < r by linarith) hscaleExplicit.2 hrD hKsize
  have hbase := hcert hscale.1 hscale.2
  apply GenQuadraticModule_mono _ hbase
  exact Nat.ceil_le.mpr hdegree

end OptimalConvergenceRates.GeneralArchimedean

end
