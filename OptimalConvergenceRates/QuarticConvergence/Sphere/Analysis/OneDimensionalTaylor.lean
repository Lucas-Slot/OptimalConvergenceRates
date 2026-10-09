/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/OneDimensionalTaylor.lean

  One-dimensional Taylor estimates used by the nonnegative-jet inequalities.
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

open Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Third-order Taylor approximation with a unit fourth-derivative bound. -/
theorem norm_sub_taylorWithinEval_three_le {f : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hf : ContDiffOn ℝ 4 f (Icc a b)) (hx : x ∈ Icc a b)
    (hfourth : ∀ y ∈ Icc a b, ‖iteratedDerivWithin 4 f (Icc a b) y‖ ≤ 1) :
    ‖f x - taylorWithinEval f 3 (Icc a b) a x‖ ≤ (x - a) ^ 4 / 6 := by
  simpa using taylor_mean_remainder_bound (n := 3) hab hf hx hfourth

/-- Scalar absolute-value form of the third-order Taylor remainder bound. -/
theorem abs_sub_taylorWithinEval_three_le {f : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hf : ContDiffOn ℝ 4 f (Icc a b)) (hx : x ∈ Icc a b)
    (hfourth : ∀ y ∈ Icc a b, ‖iteratedDerivWithin 4 f (Icc a b) y‖ ≤ 1) :
    |f x - taylorWithinEval f 3 (Icc a b) a x| ≤ (x - a) ^ 4 / 6 := by
  simpa [Real.norm_eq_abs] using
    norm_sub_taylorWithinEval_three_le hab hf hx hfourth

/-- A nonnegative function with a fourth-order Taylor error lies below a
nonnegative quartic majorant. This isolates the order argument used by all
three nonnegative-jet estimates. -/
theorem quartic_majorant_nonnegative {f : ℝ → ℝ} {a b c e t : ℝ}
    (hf : 0 ≤ f t)
    (hrem :
      |f t - (a + b * t + c * t ^ 2 / 2 + e * t ^ 3 / 6)| ≤ t ^ 4 / 6) :
    0 ≤ a + b * t + c * t ^ 2 / 2 + e * t ^ 3 / 6 + t ^ 4 / 6 := by
  rw [abs_le] at hrem
  linarith

/-- Averaging a nonnegative quartic majorant at `t` and `-t` removes its odd
part. -/
theorem even_quartic_nonnegative {a b c e : ℝ}
    (hpoly :
      ∀ t : ℝ, 0 ≤ a + b * t + c * t ^ 2 / 2 + e * t ^ 3 / 6 + t ^ 4 / 6) :
    ∀ t : ℝ, 0 ≤ a + c * t ^ 2 / 2 + t ^ 4 / 6 := by
  intro t
  have hp := hpoly t
  have hm := hpoly (-t)
  nlinarith

/-- The quadratic coefficient of an everywhere nonnegative even quartic is
bounded below by the square root of its constant coefficient. The constant
`2` is deliberately a little larger than the optimal `sqrt (8 / 3)`. -/
theorem quadratic_coefficient_lower_of_even_quartic_nonnegative {a c : ℝ}
    (ha : 0 ≤ a)
    (hpoly : ∀ t : ℝ, 0 ≤ a + c * t ^ 2 / 2 + t ^ 4 / 6) :
    -(2 * Real.sqrt a) ≤ c := by
  by_cases hc : 0 ≤ c
  · nlinarith [Real.sqrt_nonneg a]
  · have hcneg : c < 0 := lt_of_not_ge hc
    let z : ℝ := -3 * c / 2
    have hz : 0 ≤ z := by
      dsimp [z]
      linarith
    let t : ℝ := Real.sqrt z
    have ht2 : t ^ 2 = z := by
      dsimp [t]
      exact Real.sq_sqrt hz
    have hp := hpoly t
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2] at hp
    dsimp [z] at hp
    have hsqa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
    have hsqrta : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    by_contra hgoal
    have hlt : c < -(2 * Real.sqrt a) := lt_of_not_ge hgoal
    nlinarith

/-- Evaluating a nonnegative quartic at the two scales `R` and `2R`
controls its cubic coefficient. -/
theorem cubic_coefficient_bound_of_quartic_nonnegative {a b c e R : ℝ}
    (hR : 0 < R) (haUpper : a ≤ R ^ 4) (hcUpper : |c| ≤ R ^ 2)
    (hpoly :
      ∀ t : ℝ, 0 ≤ a + b * t + c * t ^ 2 / 2 + e * t ^ 3 / 6 + t ^ 4 / 6) :
    |e| ≤ 9 * R := by
  have hpR := hpoly R
  have hmR := hpoly (-R)
  have hp2R := hpoly (2 * R)
  have hm2R := hpoly (-(2 * R))
  have hc_le : c ≤ R ^ 2 := le_trans (le_abs_self c) hcUpper
  have hnegc_le : -c ≤ R ^ 2 := le_trans (neg_le_abs c) hcUpper
  have he_mul_upper : e * R ^ 3 ≤ 9 * R ^ 4 := by
    nlinarith
  have he_mul_lower : -(e * R ^ 3) ≤ 9 * R ^ 4 := by
    nlinarith
  have hR3 : 0 < R ^ 3 := pow_pos hR 3
  rw [abs_le]
  constructor
  · have hcancel : (-9 * R) * R ^ 3 ≤ e * R ^ 3 := by
      nlinarith
    exact le_of_mul_le_mul_right (by convert hcancel using 1; ring) hR3
  · have hcancel : e * R ^ 3 ≤ (9 * R) * R ^ 3 := by
      nlinarith
    exact le_of_mul_le_mul_right hcancel hR3

/-- The same two-scale calculation controls the linear coefficient at the
coarser `R³` scale. -/
theorem linear_coefficient_coarse_bound_of_quartic_nonnegative {a b c e R : ℝ}
    (hR : 0 < R) (haUpper : a ≤ R ^ 4) (hcUpper : |c| ≤ R ^ 2)
    (hpoly :
      ∀ t : ℝ, 0 ≤ a + b * t + c * t ^ 2 / 2 + e * t ^ 3 / 6 + t ^ 4 / 6) :
    |b| ≤ 4 * R ^ 3 := by
  have hpR := hpoly R
  have hmR := hpoly (-R)
  have hp2R := hpoly (2 * R)
  have hm2R := hpoly (-(2 * R))
  have hc_le : c ≤ R ^ 2 := le_trans (le_abs_self c) hcUpper
  have hnegc_le : -c ≤ R ^ 2 := le_trans (neg_le_abs c) hcUpper
  have he_mul_upper : e * R ^ 3 ≤ 9 * R ^ 4 := by
    nlinarith
  have he_mul_lower : -(e * R ^ 3) ≤ 9 * R ^ 4 := by
    nlinarith
  have hb_mul_upper : b * R ≤ 4 * R ^ 4 := by
    nlinarith
  have hb_mul_lower : -(b * R) ≤ 4 * R ^ 4 := by
    nlinarith
  rw [abs_le]
  constructor
  · have hcancel : (-4 * R ^ 3) * R ≤ b * R := by
      nlinarith
    exact le_of_mul_le_mul_right (by convert hcancel using 1; ring) hR
  · have hcancel : b * R ≤ (4 * R ^ 3) * R := by
      nlinarith
    exact le_of_mul_le_mul_right hcancel hR

/-- At a positive constant term, evaluating at the finer scale
`sqrt a / R` improves the coarse linear estimate to the sharper
`R * sqrt a` scale. -/
theorem linear_coefficient_refined_bound_of_quartic_nonnegative {a b c e R : ℝ}
    (ha : 0 < a) (hR : 0 < R) (haUpper : a ≤ R ^ 4) (hcUpper : |c| ≤ R ^ 2)
    (hpoly :
      ∀ t : ℝ, 0 ≤ a + b * t + c * t ^ 2 / 2 + e * t ^ 3 / 6 + t ^ 4 / 6) :
    |b| ≤ 4 * R * Real.sqrt a := by
  have ha0 : 0 ≤ a := le_of_lt ha
  have hRne : R ≠ 0 := ne_of_gt hR
  have heBound : |e| ≤ 9 * R :=
    cubic_coefficient_bound_of_quartic_nonnegative hR haUpper hcUpper hpoly
  let s : ℝ := Real.sqrt a / R
  have hspos : 0 < s := div_pos (Real.sqrt_pos.2 ha) hR
  have hs0 : 0 ≤ s := le_of_lt hspos
  have hs2 : s ^ 2 = a / R ^ 2 := by
    dsimp [s]
    rw [div_pow, Real.sq_sqrt ha0]
  have hR2ne : R ^ 2 ≠ 0 := pow_ne_zero _ hRne
  have hR2s2 : R ^ 2 * s ^ 2 = a := by
    rw [hs2]
    exact mul_div_cancel₀ a hR2ne
  have hRs : R * s = Real.sqrt a := by
    dsimp [s]
    field_simp
  have hsqrta2 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha0
  have hsqrta0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsqrt_le_R2 : Real.sqrt a ≤ R ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt a + R ^ 2), sq_nonneg R]
  have hs2_le_R2 : s ^ 2 ≤ R ^ 2 := by
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos hR)
    calc
      R ^ 2 * s ^ 2 = a := hR2s2
      _ ≤ R ^ 4 := haUpper
      _ = R ^ 2 * R ^ 2 := by ring
  have hs4_le_a : s ^ 4 ≤ a := by
    calc
      s ^ 4 = s ^ 2 * s ^ 2 := by ring
      _ ≤ R ^ 2 * s ^ 2 := mul_le_mul_of_nonneg_right hs2_le_R2 (sq_nonneg s)
      _ = a := hR2s2
  have hsqrt_s2_le_a : Real.sqrt a * s ^ 2 ≤ a := by
    calc
      Real.sqrt a * s ^ 2 ≤ R ^ 2 * s ^ 2 :=
        mul_le_mul_of_nonneg_right hsqrt_le_R2 (sq_nonneg s)
      _ = a := hR2s2
  have he_upper : e ≤ 9 * R := le_trans (le_abs_self e) heBound
  have he_lower : -(9 * R) ≤ e := by
    nlinarith [neg_abs_le e]
  have hscale : R * s ^ 3 ≤ a := by
    rw [show R * s ^ 3 = Real.sqrt a * s ^ 2 by rw [← hRs]; ring]
    exact hsqrt_s2_le_a
  have heS_upper : e * s ^ 3 ≤ 9 * a := by
    have hm := mul_le_mul_of_nonneg_right he_upper (pow_nonneg hs0 3)
    nlinarith
  have heS_lower : -(9 * a) ≤ e * s ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right he_lower (pow_nonneg hs0 3)
    nlinarith
  have hc_upper : c ≤ R ^ 2 := le_trans (le_abs_self c) hcUpper
  have hcS_upper : c * s ^ 2 ≤ a := by
    calc
      c * s ^ 2 ≤ R ^ 2 * s ^ 2 :=
        mul_le_mul_of_nonneg_right hc_upper (sq_nonneg s)
      _ = a := hR2s2
  have hp := hpoly s
  have hm := hpoly (-s)
  have hbS_upper : b * s ≤ 4 * a := by
    nlinarith
  have hbS_lower : -(4 * a) ≤ b * s := by
    nlinarith
  rw [abs_le]
  constructor
  · apply le_of_mul_le_mul_right _ hspos
    convert hbS_lower using 1
    rw [neg_mul]
    congr 1
    calc
      (4 * R * Real.sqrt a) * s = 4 * (R * s) * Real.sqrt a := by ring
      _ = 4 * a := by rw [hRs]; nlinarith
  · apply le_of_mul_le_mul_right _ hspos
    convert hbS_upper using 1
    calc
      (4 * R * Real.sqrt a) * s = 4 * (R * s) * Real.sqrt a := by ring
      _ = 4 * a := by rw [hRs]; nlinarith


/-- If the constant coefficient vanishes, nonnegativity forces the linear
coefficient to vanish. This is the division-free edge case in the refined
linear estimate. -/
theorem linear_coefficient_eq_zero_of_quartic_nonnegative {b c e : ℝ}
    (hpoly : ∀ t : ℝ, 0 ≤ b * t + c * t ^ 2 / 2 + e * t ^ 3 / 6 + t ^ 4 / 6) :
    b = 0 := by
  let p : ℝ → ℝ := fun t => b * t + c * t ^ 2 / 2 + e * t ^ 3 / 6 + t ^ 4 / 6
  have hp0 : p 0 = 0 := by simp [p]
  have hmin : IsLocalMin p 0 := by
    filter_upwards [] with t
    rw [hp0]
    exact hpoly t
  have hlinear : HasDerivAt (fun t : ℝ => b * t) b 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 0).const_mul b using 1; norm_num
  have hquadratic : HasDerivAt (fun t : ℝ => c * t ^ 2 / 2) 0 0 := by
    convert (((hasDerivAt_id (𝕜 := ℝ) 0).pow 2).const_mul c).div_const 2 using 1;
      norm_num
  have hcubic : HasDerivAt (fun t : ℝ => e * t ^ 3 / 6) 0 0 := by
    convert (((hasDerivAt_id (𝕜 := ℝ) 0).pow 3).const_mul e).div_const 6 using 1;
      norm_num
  have hquartic : HasDerivAt (fun t : ℝ => t ^ 4 / 6) 0 0 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) 0).pow 4).div_const 6 using 1; norm_num
  have hpderiv : HasDerivAt p b 0 := by
    simpa [p] using ((hlinear.add hquadratic).add hcubic).add hquartic
  exact hmin.hasDerivAt_eq_zero hpderiv

/-- The cubic coefficient bound remains valid at the degenerate scale
`R = 0`. In that case nonnegativity successively forces the constant, linear,
quadratic, and cubic coefficients to vanish. -/
theorem cubic_coefficient_bound_of_quartic_nonnegative_of_nonneg {a b c e R : ℝ}
    (hR : 0 ≤ R) (haUpper : a ≤ R ^ 4) (hcUpper : |c| ≤ R ^ 2)
    (hpoly :
      ∀ t : ℝ, 0 ≤ a + b * t + c * t ^ 2 / 2 + e * t ^ 3 / 6 + t ^ 4 / 6) :
    |e| ≤ 9 * R := by
  rcases hR.eq_or_lt with rfl | hRpos
  · have ha0 : a = 0 := by
      have := hpoly 0
      norm_num at this haUpper
      linarith
    have hc0 : c = 0 := by
      norm_num at hcUpper
      exact hcUpper
    have hb0 : b = 0 :=
      linear_coefficient_eq_zero_of_quartic_nonnegative (b := b) (c := 0) (e := e) (by
        intro t
        simpa [ha0, hc0] using hpoly t)
    have heval := hpoly (-e / 2)
    rw [ha0, hb0, hc0] at heval
    ring_nf at heval
    have he4 : e ^ 4 = 0 := by
      nlinarith [sq_nonneg (e ^ 2)]
    have he0 : e = 0 := eq_zero_of_pow_eq_zero he4
    simp [he0]
  · exact cubic_coefficient_bound_of_quartic_nonnegative hRpos haUpper hcUpper hpoly

/-- Global `C⁴` form of the Taylor bound with the first four coefficients
written explicitly. The positive endpoint convention is later applied to
both `v` and `-v`. -/
theorem abs_sub_explicit_taylor_three_le {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : ContDiff ℝ 4 f) (hfourth : ∀ t, ‖iteratedDeriv 4 f t‖ ≤ 1) :
    |f T - (f 0 + deriv f 0 * T + iteratedDeriv 2 f 0 * T ^ 2 / 2 +
      iteratedDeriv 3 f 0 * T ^ 3 / 6)| ≤ T ^ 4 / 6 := by
  have hud : UniqueDiffOn ℝ (Icc 0 T) := uniqueDiffOn_Icc hT
  have hzero : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.2 hT.le
  have hwithin (k : ℕ) (hk : k ≤ 4) :
      iteratedDerivWithin k f (Icc 0 T) 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hud
      (hf.contDiffAt.of_le (by exact_mod_cast hk)) hzero
  have hrem := abs_sub_taylorWithinEval_three_le (f := f) (a := 0) (b := T) (x := T)
    hT.le hf.contDiffOn ⟨hT.le, le_rfl⟩ (by
      intro y hy
      rw [iteratedDerivWithin_eq_iteratedDeriv hud hf.contDiffAt hy]
      exact hfourth y)
  rw [taylor_within_apply] at hrem
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hrem
  rw [hwithin 0 (by norm_num), hwithin 1 (by norm_num), hwithin 2 (by norm_num),
    hwithin 3 (by norm_num)] at hrem
  norm_num [iteratedDeriv_zero, iteratedDeriv_one, smul_eq_mul, Nat.factorial] at hrem
  convert hrem using 1; ring_nf
end QuarticConvergence
end OptimalConvergenceRates

end
