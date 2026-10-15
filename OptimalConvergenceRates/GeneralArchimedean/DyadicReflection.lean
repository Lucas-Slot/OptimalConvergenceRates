/-
  Pointwise reflection estimates for the dyadic rational-square-root product.
-/
import OptimalConvergenceRates.GeneralArchimedean.RationalSquareRoot
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open Finset

namespace OptimalConvergenceRates
namespace GeneralArchimedean
namespace RationalSquareRoot

open UnivariateParity

/-- One factor in W(-t) / W(t). -/
def reflectionFactor (δ t : ℝ) (ell j : ℕ) : ℝ :=
  ((gridPoint δ j - t) / (gridPoint δ j + t)) ^ (2 * ell)

/-- Product of all reflection factors. -/
def reflectionProduct (δ t : ℝ) (ell J : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (J + 1), reflectionFactor δ t ell j

theorem abs_reflection_ratio_le_one
    {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    |(b - t) / (b + t)| ≤ 1 := by
  by_cases hzero : b + t = 0
  · simp [hzero]
  have hpos : 0 < b + t := lt_of_le_of_ne (add_nonneg hb ht) (Ne.symm hzero)
  rw [abs_div, abs_of_pos hpos]
  rw [div_le_one hpos]
  rw [abs_le]
  constructor <;> linarith

theorem abs_reflection_ratio_le_third
    {b t : ℝ} (hb : 0 ≤ b) (hbt : b ≤ t) (htb : t ≤ 2 * b) :
    |(b - t) / (b + t)| ≤ (1 / 3 : ℝ) := by
  by_cases hb0 : b = 0
  · subst b
    have ht0 : t = 0 := by linarith
    subst t
    norm_num
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hdenom : 0 < b + t := by linarith
  rw [abs_div, abs_of_pos hdenom, abs_of_nonpos (sub_nonpos.mpr hbt)]
  rw [div_le_iff₀ hdenom]
  nlinarith

theorem reflectionFactor_nonneg
    (δ t : ℝ) (ell j : ℕ) :
    0 ≤ reflectionFactor δ t ell j := by
  dsimp [reflectionFactor]
  rw [show 2 * ell = ell * 2 by omega, pow_mul]
  exact sq_nonneg _

theorem reflectionFactor_le_one
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) (ell j : ℕ) :
    reflectionFactor δ t ell j ≤ 1 := by
  let z := (gridPoint δ j - t) / (gridPoint δ j + t)
  have hz : |z| ≤ 1 :=
    abs_reflection_ratio_le_one (gridPoint_nonneg hδ j) ht
  have hpow : |z| ^ (2 * ell) ≤ (1 : ℝ) ^ (2 * ell) :=
    pow_le_pow_left₀ (abs_nonneg z) hz _
  have hnonneg : 0 ≤ z ^ (2 * ell) := by
    rw [show 2 * ell = ell * 2 by omega, pow_mul]
    exact sq_nonneg _
  dsimp [reflectionFactor, z]
  rw [← abs_pow, abs_of_nonneg hnonneg] at hpow
  simpa using hpow

theorem reflectionFactor_le_third_pow
    {δ t : ℝ} {j : ℕ}
    (hδ : 0 ≤ δ) (ht : 0 ≤ t)
    (hlow : gridPoint δ j ≤ t) (hhigh : t ≤ 2 * gridPoint δ j)
    (ell : ℕ) :
    reflectionFactor δ t ell j ≤ (1 / 3 : ℝ) ^ (2 * ell) := by
  let z := (gridPoint δ j - t) / (gridPoint δ j + t)
  have hz : |z| ≤ (1 / 3 : ℝ) :=
    abs_reflection_ratio_le_third (gridPoint_nonneg hδ j) hlow hhigh
  have hpow := pow_le_pow_left₀ (abs_nonneg z) hz (2 * ell)
  have hnonneg : 0 ≤ z ^ (2 * ell) := by
    rw [show 2 * ell = ell * 2 by omega, pow_mul]
    exact sq_nonneg _
  dsimp [reflectionFactor, z]
  rw [← abs_pow, abs_of_nonneg hnonneg] at hpow
  exact hpow

theorem prod_le_selected_of_nonneg_le_one
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    {i : ι} (hi : i ∈ s)
    (hf0 : ∀ j ∈ s, 0 ≤ f j) (hf1 : ∀ j ∈ s, f j ≤ 1) :
    ∏ j ∈ s, f j ≤ f i := by
  rw [← Finset.prod_erase_mul _ _ hi]
  have herase : ∏ j ∈ s.erase i, f j ≤ 1 :=
    Finset.prod_le_one₀ (fun j hj => hf0 j (Finset.mem_of_mem_erase hj))
      (fun j hj => hf1 j (Finset.mem_of_mem_erase hj))
  have hfi : 0 ≤ f i := hf0 i hi
  nlinarith

theorem reflectionProduct_le_third_pow
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t)
    {j : ℕ} {J : ℕ} (hj : j ∈ Finset.range (J + 1))
    (hlow : gridPoint δ j ≤ t) (hhigh : t ≤ 2 * gridPoint δ j)
    (ell : ℕ) :
    reflectionProduct δ t ell J ≤ (1 / 3 : ℝ) ^ (2 * ell) := by
  unfold reflectionProduct
  exact (prod_le_selected_of_nonneg_le_one (Finset.range (J + 1))
      (fun k => reflectionFactor δ t ell k) hj
      (fun k _ => reflectionFactor_nonneg δ t ell k)
      (fun k _ => reflectionFactor_le_one hδ ht ell k)).trans
    (reflectionFactor_le_third_pow hδ ht hlow hhigh ell)

theorem gridProduct_eval_neg_eq_reflectionProduct_mul
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t) (ell J : ℕ) :
    (gridProduct δ ell J).eval (-t) =
      reflectionProduct δ t ell J * (gridProduct δ ell J).eval t := by
  rw [gridProduct_eval, gridProduct_eval]
  unfold reflectionProduct reflectionFactor
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hdenom : gridPoint δ j + t ≠ 0 := by
    have : 0 < gridPoint δ j + t := lt_of_le_of_lt
      (gridPoint_nonneg hδ j) (lt_add_of_pos_right _ ht)
    exact this.ne'
  rw [div_pow]
  field_simp
  ring

/-- If one dyadic grid point lies between t/2 and t, the residual is small
relative to the even numerator. -/
theorem gridResidual_sq_le_four_third_pow_mul_numerator_sq
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 < t)
    {j J : ℕ} (hj : j ∈ Finset.range (J + 1))
    (hlow : gridPoint δ j ≤ t) (hhigh : t ≤ 2 * gridPoint δ j)
    (ell : ℕ) :
    (gridResidual δ ell J).eval (t ^ 2) ^ 2 ≤
      4 * (1 / 3 : ℝ) ^ (2 * ell) *
        (numerator δ ell J).eval (t ^ 2) ^ 2 := by
  let x := (gridProduct δ ell J).eval t
  let y := (gridProduct δ ell J).eval (-t)
  let rho := reflectionProduct δ t ell J
  let p := (numerator δ ell J).eval (t ^ 2)
  let q := (1 / 3 : ℝ) ^ (2 * ell)
  have hx : 0 < x := by
    dsimp [x]
    rw [gridProduct_eval]
    apply Finset.prod_pos
    intro k hk
    apply pow_pos
    have hg : 0 ≤ gridPoint δ k := gridPoint_nonneg hδ k
    linarith
  have hrho0 : 0 ≤ rho := by
    dsimp [rho, reflectionProduct]
    exact Finset.prod_nonneg fun k _ => reflectionFactor_nonneg δ t ell k
  have hrhoq : rho ≤ q := by
    exact reflectionProduct_le_third_pow hδ ht.le hj hlow hhigh ell
  have hy : y = rho * x := by
    dsimp [x, y, rho]
    exact gridProduct_eval_neg_eq_reflectionProduct_mul hδ ht ell J
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hp : p = (x + y) / 2 := by
    dsimp [p, x, y, numerator]
    rw [evenContract_eval_sq, evenPart_eval]
  have hres : x * y = (gridResidual δ ell J).eval (t ^ 2) ^ 2 := by
    dsimp [x, y]
    exact gridProduct_mul_reflected_eval δ t ell J
  have hxy : x * y ≤ q * x ^ 2 := by
    rw [hy]
    have := mul_le_mul_of_nonneg_right hrhoq (sq_nonneg x)
    nlinarith
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hxle : x ≤ 2 * p := by rw [hp]; linarith
  have hx_sq_le : x ^ 2 ≤ 4 * p ^ 2 := by nlinarith
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hfinal := mul_le_mul_of_nonneg_left hx_sq_le hq0
  rw [← hres]
  dsimp [p, q] at hfinal ⊢
  nlinarith

/-- The dyadic grid covers an interval of squared arguments when every square
root in that interval lies within a factor of two of one grid point. -/
def CoversInterval (δ B : ℝ) (J : ℕ) : Prop :=
  ∀ v : ℝ, δ ≤ v → v ≤ B + δ →
    ∃ j ∈ Finset.range (J + 1),
      gridPoint δ j ≤ Real.sqrt v ∧ Real.sqrt v ≤ 2 * gridPoint δ j


theorem exists_dyadic_bracket
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    ∀ J : ℕ, t ≤ (2 : ℝ) ^ (J + 1) * a →
      ∃ j ∈ Finset.range (J + 1),
        (2 : ℝ) ^ j * a ≤ t ∧ t ≤ 2 * ((2 : ℝ) ^ j * a) := by
  intro J
  induction J with
  | zero =>
      intro ht
      refine ⟨0, by simp, ?_, ?_⟩
      · simpa using hat
      · norm_num at ht ⊢
        exact ht
  | succ J ih =>
      intro ht
      by_cases hsmall : t ≤ (2 : ℝ) ^ (J + 1) * a
      · obtain ⟨j, hj, hlow, hhigh⟩ := ih hsmall
        exact ⟨j, Finset.mem_range.mpr
          (lt_trans (Finset.mem_range.mp hj) (by omega)), hlow, hhigh⟩
      · refine ⟨J + 1, by simp, le_of_lt (lt_of_not_ge hsmall), ?_⟩
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using ht

theorem coversInterval_of_endpoint
    {δ B : ℝ} (hδ : 0 < δ) (J : ℕ)
    (hend : Real.sqrt (B + δ) ≤
      (2 : ℝ) ^ (J + 1) * Real.sqrt δ) :
    CoversInterval δ B J := by
  intro v hv0 hvB
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hvnonneg : 0 ≤ v := le_trans hδ.le hv0
  have hBnonneg : 0 ≤ B + δ := le_trans hvnonneg hvB
  have hlower : Real.sqrt δ ≤ Real.sqrt v :=
    Real.sqrt_le_sqrt hv0
  have hupper : Real.sqrt v ≤
      (2 : ℝ) ^ (J + 1) * Real.sqrt δ :=
    (Real.sqrt_le_sqrt hvB).trans hend
  obtain ⟨j, hj, hlow, hhigh⟩ :=
    exists_dyadic_bracket hsδ hlower J hupper
  exact ⟨j, hj, by simpa [gridPoint] using hlow,
    by simpa [gridPoint] using hhigh⟩


theorem exists_coversInterval
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ J, CoversInterval δ B J := by
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsle : Real.sqrt δ ≤ Real.sqrt (B + δ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hratio : 1 ≤ Real.sqrt (B + δ) / Real.sqrt δ := by
    rw [le_div_iff₀ hsδ]
    simpa using hsle
  obtain ⟨J, _, hJ⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  refine ⟨J, coversInterval_of_endpoint hδ J ?_⟩
  exact ((div_lt_iff₀ hsδ).mp hJ).le


/-- The dyadic covering index can be chosen with the expected logarithmic
bound. -/
theorem exists_coversInterval_with_log_bound
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ J, CoversInterval δ B J ∧
      (J : ℝ) ≤
        Real.log (Real.sqrt (B + δ) / Real.sqrt δ) /
          Real.log 2 := by
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsle : Real.sqrt δ ≤ Real.sqrt (B + δ) :=
    Real.sqrt_le_sqrt (by linarith)
  let ratio := Real.sqrt (B + δ) / Real.sqrt δ
  have hratio : 1 ≤ ratio := by
    dsimp [ratio]
    rw [le_div_iff₀ hsδ]
    simpa using hsle
  obtain ⟨J, hJlow, hJhigh⟩ :=
    exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  refine ⟨J, coversInterval_of_endpoint hδ J ?_, ?_⟩
  · exact ((div_lt_iff₀ hsδ).mp hJhigh).le
  · have hlog :=
      Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) J) hJlow
    rw [Real.log_pow] at hlog
    rw [le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    simpa [ratio, mul_comm] using hlog
theorem exists_positive_ell_for_theta
    {theta : ℝ} (hθ0 : 0 < theta) :
    ∃ ell : ℕ, 0 < ell ∧
      4 * (1 / 3 : ℝ) ^ (2 * ell) ≤ theta := by
  let x := min 1 (theta / 4)
  have hx0 : 0 < x := lt_min (by norm_num) (div_pos hθ0 (by norm_num))
  have hx1 : x ≤ 1 := min_le_left _ _
  obtain ⟨n, hn, _⟩ :=
    exists_nat_pow_near_of_lt_one hx0 hx1
      (by norm_num : 0 < (1 / 9 : ℝ))
      (by norm_num : (1 / 9 : ℝ) < 1)
  refine ⟨n + 1, by omega, ?_⟩
  have hpow :
      (1 / 3 : ℝ) ^ (2 * (n + 1)) = (1 / 9 : ℝ) ^ (n + 1) := by
    rw [show (1 / 9 : ℝ) = (1 / 3) * (1 / 3) by norm_num, mul_pow,
      show 2 * (n + 1) = (n + 1) + (n + 1) by omega, pow_add]
  rw [hpow]
  have hxtheta : x ≤ theta / 4 := min_le_right _ _
  nlinarith [hn.le, hxtheta]

/-- For a target at most one, the attenuation exponent can be chosen
with an explicit logarithmic bound. -/
theorem exists_positive_ell_for_theta_with_log_bound
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    ∃ ell : ℕ, 0 < ell ∧
      4 * (1 / 3 : ℝ) ^ (2 * ell) ≤ theta ∧
      (ell : ℝ) ≤
        Real.log (theta / 4) / Real.log (1 / 9) + 1 := by
  let x : ℝ := theta / 4
  have hx0 : 0 < x := div_pos htheta0 (by norm_num)
  have hx1 : x ≤ 1 := by
    dsimp [x]
    linarith
  obtain ⟨n, hnlow, hxpow⟩ :=
    exists_nat_pow_near_of_lt_one hx0 hx1
      (by norm_num : 0 < (1 / 9 : ℝ))
      (by norm_num : (1 / 9 : ℝ) < 1)
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · have hpow :
        (1 / 3 : ℝ) ^ (2 * (n + 1)) = (1 / 9 : ℝ) ^ (n + 1) := by
      rw [show (1 / 9 : ℝ) = (1 / 3) * (1 / 3) by norm_num, mul_pow,
        show 2 * (n + 1) = (n + 1) + (n + 1) by omega, pow_add]
    rw [hpow]
    dsimp [x] at hnlow
    nlinarith [hnlow.le]
  · have hlog :
        Real.log x ≤ Real.log ((1 / 9 : ℝ) ^ n) :=
      Real.log_le_log hx0 hxpow
    rw [Real.log_pow] at hlog
    have hlogBase : Real.log (1 / 9 : ℝ) < 0 :=
      Real.log_neg (by norm_num) (by norm_num)
    have hncast :
        (n : ℝ) ≤ Real.log x / Real.log (1 / 9) := by
      rw [le_div_iff_of_neg hlogBase]
      simpa [mul_comm] using hlog
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
theorem gridResidual_sq_le_on_covered_interval
    {δ B : ℝ} (hδ : 0 < δ) {J : ℕ} (hcover : CoversInterval δ B J)
    {v : ℝ} (hv0 : δ ≤ v) (hvB : v ≤ B + δ) (ell : ℕ) :
    (gridResidual δ ell J).eval v ^ 2 ≤
      4 * (1 / 3 : ℝ) ^ (2 * ell) *
        (numerator δ ell J).eval v ^ 2 := by
  let t := Real.sqrt v
  have hvpos : 0 < v := hδ.trans_le hv0
  have ht : 0 < t := by
    dsimp [t]
    exact Real.sqrt_pos.2 hvpos
  have ht_sq : t ^ 2 = v := Real.sq_sqrt hvpos.le
  obtain ⟨j, hj, hlow, hhigh⟩ := hcover v hv0 hvB
  have h := gridResidual_sq_le_four_third_pow_mul_numerator_sq
    hδ.le ht hj hlow hhigh ell
  simpa [t, ht_sq] using h

theorem normalizedResidual_sq_le_on_covered_interval
    {δ B : ℝ} (hδ : 0 < δ) {ell : ℕ} (hell : 0 < ell)
    {J : ℕ} (hcover : CoversInterval δ B J)
    {u : ℝ} (hu0 : 0 ≤ u) (huB : u ≤ B) :
    (normalizedResidual δ ell J).eval u ^ 2 ≤
      4 * (1 / 3 : ℝ) ^ (2 * ell) *
        (normalizedNumerator δ ell J).eval u ^ 2 := by
  have hraw := gridResidual_sq_le_on_covered_interval hδ hcover
    (v := u + δ) (by linarith) (by linarith) ell
  let c : ℝ := (denominator δ ell J).eval δ
  have hc : 0 < c := denominator_eval_self_pos hδ hell J
  have hscale := mul_le_mul_of_nonneg_left hraw (sq_nonneg c⁻¹)
  simp only [normalizedResidual, normalizedNumerator, normalizeShift,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X]
  change (c⁻¹ * (gridResidual δ ell J).eval (u + δ)) ^ 2 ≤
    4 * (1 / 3 : ℝ) ^ (2 * ell) *
      (c⁻¹ * (numerator δ ell J).eval (u + δ)) ^ 2
  nlinarith

/-- The first interval inequality E ≤ theta P² + δ V². -/
theorem normalizedError_le
    {δ B theta : ℝ} (hδ : 0 < δ) {ell : ℕ} (hell : 0 < ell)
    {J : ℕ} (hcover : CoversInterval δ B J)
    (htheta : 4 * (1 / 3 : ℝ) ^ (2 * ell) ≤ theta)
    {u : ℝ} (hu0 : 0 ≤ u) (huB : u ≤ B) :
    (normalizedError δ ell J).eval u ≤
      theta * (normalizedNumerator δ ell J).eval u ^ 2 +
        δ * (normalizedDenominator δ ell J).eval u ^ 2 := by
  have hres := normalizedResidual_sq_le_on_covered_interval
    hδ hell hcover hu0 huB
  have hp2 : 0 ≤ (normalizedNumerator δ ell J).eval u ^ 2 := sq_nonneg _
  have htheta' := mul_le_mul_of_nonneg_right htheta hp2
  simp only [normalizedError, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow]
  linarith

/-- The second interval inequality follows formally from the first and the
identity P²-uV²=E. -/
theorem normalizedNumerator_sq_le
    {δ B theta B' : ℝ} (hδ : 0 < δ) {ell : ℕ} (hell : 0 < ell)
    {J : ℕ} (hcover : CoversInterval δ B J)
    (htheta : 4 * (1 / 3 : ℝ) ^ (2 * ell) ≤ theta)
    (htheta1 : theta < 1)
    (hB' : B + δ ≤ (1 - theta) * B')
    {u : ℝ} (hu0 : 0 ≤ u) (huB : u ≤ B) :
    (normalizedNumerator δ ell J).eval u ^ 2 ≤
      B' * (normalizedDenominator δ ell J).eval u ^ 2 := by
  have herr := normalizedError_le hδ hell hcover htheta hu0 huB
  have hid := congrArg (fun P : Polynomial ℝ => P.eval u)
    (normalizedNumerator_sq_sub_X_mul_denominator_sq hδ hell J)
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X] at hid
  let p2 := (normalizedNumerator δ ell J).eval u ^ 2
  let v2 := (normalizedDenominator δ ell J).eval u ^ 2
  have hp2 : 0 ≤ p2 := by dsimp [p2]; positivity
  have hv2 : 0 ≤ v2 := by dsimp [v2]; positivity
  have huv : (u + δ) * v2 ≤ (B + δ) * v2 :=
    mul_le_mul_of_nonneg_right (by linarith) hv2
  have hBv : (B + δ) * v2 ≤ ((1 - theta) * B') * v2 :=
    mul_le_mul_of_nonneg_right hB' hv2
  dsimp [p2, v2] at hp2 hv2 huv hBv ⊢
  nlinarith


end RationalSquareRoot
end GeneralArchimedean
end OptimalConvergenceRates

end
