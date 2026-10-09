/-
  The concrete Chebyshev weight used to eliminate an artificial constraint.
-/
import OptimalConvergenceRates.Chebyshev.ChebyshevGrowth
import OptimalConvergenceRates.GeneralArchimedean.ChebyshevElimination
import OptimalConvergenceRates.GeneralArchimedean.PositiveCoefficientCertificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

noncomputable section

open Polynomial

namespace OptimalConvergenceRates
namespace GeneralArchimedean

open RationalSquareRoot

/-- The translate `T_N(1+X)`. -/
def shiftedChebyshev (N : ℕ) : Polynomial ℝ :=
  (chebyshevT N).comp (Polynomial.X + 1)

@[simp]
theorem shiftedChebyshev_zero :
    shiftedChebyshev 0 = 1 := by
  simp [shiftedChebyshev]

@[simp]
theorem shiftedChebyshev_one :
    shiftedChebyshev 1 = Polynomial.X + 1 := by
  simp [shiftedChebyshev]

theorem shiftedChebyshev_succ_succ (N : ℕ) :
    shiftedChebyshev (N + 2) =
      2 * (Polynomial.X + 1) * shiftedChebyshev (N + 1) -
        shiftedChebyshev N := by
  simp [shiftedChebyshev, chebyshevT_succ_succ]

/-- Simultaneous positivity of `T_N(1+X)` and its forward difference.
This elementary recurrence avoids introducing an explicit binomial formula
for Chebyshev coefficients. -/
theorem shiftedChebyshev_coeffNonneg_and_diff (N : ℕ) :
    CoeffNonneg (shiftedChebyshev N) ∧
      CoeffNonneg (shiftedChebyshev (N + 1) - shiftedChebyshev N) := by
  induction N with
  | zero =>
      constructor
      · simpa using coeffNonneg_one
      · simpa using coeffNonneg_X
  | succ N ih =>
      change CoeffNonneg (shiftedChebyshev (N + 1)) ∧
        CoeffNonneg
          (shiftedChebyshev (N + 2) - shiftedChebyshev (N + 1))
      obtain ⟨hS, hD⟩ := ih
      have hSnext : CoeffNonneg (shiftedChebyshev (N + 1)) := by
        have heq :
            shiftedChebyshev (N + 1) =
              shiftedChebyshev N +
                (shiftedChebyshev (N + 1) - shiftedChebyshev N) := by
          ring
        rw [heq]
        exact hS.add hD
      refine ⟨hSnext, ?_⟩
      have hdiff :
          shiftedChebyshev (N + 2) - shiftedChebyshev (N + 1) =
            2 * Polynomial.X * shiftedChebyshev (N + 1) +
              (shiftedChebyshev (N + 1) - shiftedChebyshev N) := by
        rw [shiftedChebyshev_succ_succ]
        ring
      rw [hdiff]
      have htwo : CoeffNonneg (2 : Polynomial ℝ) := by
        simpa using coeffNonneg_C (show (0 : ℝ) ≤ 2 by norm_num)
      exact ((htwo.mul coeffNonneg_X).mul hSnext).add hD

theorem shiftedChebyshev_coeffNonneg (N : ℕ) :
    CoeffNonneg (shiftedChebyshev N) :=
  (shiftedChebyshev_coeffNonneg_and_diff N).1

theorem shiftedChebyshev_coeff_zero (N : ℕ) :
    (shiftedChebyshev N).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [shiftedChebyshev, Polynomial.eval_comp, chebyshevT_eval_one]

/-- The positive-coefficient polynomial `T_N(1+X)^2-1`. -/
def chebyshevRemainder (N : ℕ) : Polynomial ℝ :=
  shiftedChebyshev N ^ 2 - 1

theorem chebyshevRemainder_coeffNonneg (N : ℕ) :
    CoeffNonneg (chebyshevRemainder N) :=
  coeffNonneg_sq_sub_one (shiftedChebyshev_coeffNonneg N)
    (shiftedChebyshev_coeff_zero N)

theorem chebyshevRemainder_coeff_zero (N : ℕ) :
    (chebyshevRemainder N).coeff 0 = 0 := by
  simp [chebyshevRemainder, pow_two, Polynomial.mul_coeff_zero,
    shiftedChebyshev_coeff_zero]

/-- The weight `u ↦ T_N(1-2u/U)^2`. -/
def chebyshevWeight (U : ℝ) (N : ℕ) : Polynomial ℝ :=
  (chebyshevT N).comp
      (Polynomial.C 1 - Polynomial.C (2 / U) * Polynomial.X) ^ 2

theorem chebyshevWeight_isSOSUni (U : ℝ) (N : ℕ) :
    IsSOSUni (chebyshevWeight U N) :=
  IsSOSUni_sq _

theorem chebyshevWeight_eval_neg (U v : ℝ) (N : ℕ) :
    (chebyshevWeight U N).eval (-v) =
      (chebyshevRemainder N).eval ((2 / U) * v) + 1 := by
  simp [chebyshevWeight, chebyshevRemainder, shiftedChebyshev,
    Polynomial.eval_comp]
  ring

theorem chebyshevWeight_le_one_on_interval
    {U : ℝ} (hU : 0 < U) (N : ℕ) :
    ∀ u : ℝ, u ∈ Set.Icc 0 U →
      (chebyshevWeight U N).eval u ≤ 1 := by
  intro u hu
  let x : ℝ := 1 - (2 / U) * u
  have hxlo : -1 ≤ x := by
    dsimp [x]
    have := hu.2
    field_simp
    nlinarith
  have hxhi : x ≤ 1 := by
    dsimp [x]
    have := hu.1
    have hfac : 0 ≤ 2 / U := (div_pos (by norm_num) hU).le
    nlinarith [mul_nonneg hfac hu.1]
  have habs := chebyshevT_abs_le_one N x hxlo hxhi
  have hsq :
      (chebyshevT N).eval x ^ 2 ≤ (1 : ℝ) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg ((chebyshevT N).eval x))
        (by norm_num : (0 : ℝ) ≤ 1)).2 habs
  simpa [chebyshevWeight, x, Polynomial.eval_comp] using hsq

/-- Once the weight is large enough at `-epsilon`, coefficient positivity
propagates the required growth to the whole negative half-line. -/
theorem chebyshevWeight_negative_growth
    {epsilon c U : ℝ} (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hU : 0 < U) (N : ℕ)
    (hlarge : epsilon ≤
      c * (chebyshevRemainder N).eval ((2 / U) * epsilon)) :
    ∀ v : ℝ, epsilon ≤ v →
      v ≤ epsilon + c * (chebyshevWeight U N).eval (-v) := by
  intro v hev
  let P := chebyshevRemainder N
  let a : ℝ := 2 / U
  have ha : 0 < a := div_pos (by norm_num) hU
  have hx : 0 ≤ a * epsilon :=
    mul_nonneg ha.le hepsilon.le
  have hxy : a * epsilon ≤ a * v :=
    mul_le_mul_of_nonneg_left hev ha.le
  have hscale0 :
      (a * v) * P.eval (a * epsilon) ≤
        (a * epsilon) * P.eval (a * v) :=
    (chebyshevRemainder_coeffNonneg N).mul_eval_le_mul_eval
      (chebyshevRemainder_coeff_zero N) hx hxy
  have hscale :
      v * P.eval (a * epsilon) ≤
        epsilon * P.eval (a * v) := by
    apply le_of_mul_le_mul_left _ ha
    convert hscale0 using 1 <;> ring
  have hv0 : 0 ≤ v := hepsilon.le.trans hev
  have hfirst :
      v * epsilon ≤ v * (c * P.eval (a * epsilon)) :=
    mul_le_mul_of_nonneg_left (by simpa [P, a] using hlarge) hv0
  have hsecond :
      c * (v * P.eval (a * epsilon)) ≤
        c * (epsilon * P.eval (a * v)) :=
    mul_le_mul_of_nonneg_left hscale hc.le
  have hmul : v * epsilon ≤ (c * P.eval (a * v)) * epsilon := by
    calc
      v * epsilon ≤ v * (c * P.eval (a * epsilon)) := hfirst
      _ = c * (v * P.eval (a * epsilon)) := by ring
      _ ≤ c * (epsilon * P.eval (a * v)) := hsecond
      _ = (c * P.eval (a * v)) * epsilon := by ring
  have hvP : v ≤ c * P.eval (a * v) :=
    le_of_mul_le_mul_right hmul hepsilon
  rw [chebyshevWeight_eval_neg]
  change v ≤ epsilon +
    c * ((chebyshevRemainder N).eval ((2 / U) * v) + 1)
  dsimp [P, a] at hvP
  nlinarith [hc.le, hepsilon.le]

/-- A concrete Chebyshev weight satisfying the abstract elimination
interface. -/
def chebyshevEliminationWeight
    {epsilon c U : ℝ} (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hU : 0 < U) (N : ℕ)
    (hlarge : epsilon ≤
      c * (chebyshevRemainder N).eval ((2 / U) * epsilon)) :
    EliminationWeight epsilon c U where
  w := chebyshevWeight U N
  isSOS := chebyshevWeight_isSOSUni U N
  le_one_on_interval := chebyshevWeight_le_one_on_interval hU N
  negative_growth :=
    chebyshevWeight_negative_growth hepsilon hc hU N hlarge

theorem chebyshevWeight_natDegree_le (U : ℝ) (N : ℕ) :
    (chebyshevWeight U N).natDegree ≤ 2 * N := by
  have hinner :
      (Polynomial.C 1 - Polynomial.C (2 / U) * Polynomial.X).natDegree ≤ 1 := by
    compute_degree
  calc
    (chebyshevWeight U N).natDegree
        ≤ 2 * ((chebyshevT N).comp
          (Polynomial.C 1 -
            Polynomial.C (2 / U) * Polynomial.X)).natDegree := by
              exact Polynomial.natDegree_pow_le
    _ ≤ 2 * ((chebyshevT N).natDegree * 1) := by
      gcongr
      exact Polynomial.natDegree_comp_le.trans
        (Nat.mul_le_mul_left _ hinner)
    _ = 2 * N := by rw [natDegree_chebyshevT, mul_one]

/-- The elementary lower bound on hyperbolic cosine used in the degree
selection. -/
theorem exp_div_two_le_cosh (x : ℝ) :
    Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have := Real.exp_pos (-x)
  linarith

/-- Near one, arcosh has the square-root lower bound needed for the sharp
Chebyshev degree estimate. -/
theorem sqrt_le_arcosh_one_add
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1) :
    Real.sqrt x ≤ Real.arcosh (1 + x) := by
  let t := Real.arcosh (1 + x)
  have ht : 0 ≤ t := Real.arcosh_nonneg (by linarith)
  have hcosh : Real.cosh t = 1 + x :=
    Real.cosh_arcosh (by linarith)
  have hupper := Real.cosh_le_exp_half_sq t
  rw [hcosh] at hupper
  have hlogupper : Real.log (1 + x) ≤ t ^ 2 / 2 := by
    rw [← Real.exp_le_exp]
    rw [Real.exp_log (by linarith : 0 < 1 + x)]
    exact hupper
  have hlogbase := Real.one_sub_inv_le_log_of_pos
    (show 0 < 1 + x by linarith)
  have heq : 1 - (1 + x)⁻¹ = x / (1 + x) := by
    field_simp
    ring
  rw [heq] at hlogbase
  have hxhalf : x / 2 ≤ x / (1 + x) :=
    div_le_div_of_nonneg_left hx.le (by linarith) (by linarith)
  have hsq : x ≤ t ^ 2 := by
    linarith [hxhalf.trans hlogbase]
  rw [Real.sqrt_le_iff]
  exact ⟨ht, hsq⟩

/-- The canonical Chebyshev degree making the weight large at `-epsilon`. -/
noncomputable def chebyshevDegree (epsilon c U : ℝ) : ℕ :=
  Nat.ceil
    (Real.log (2 * (1 + epsilon / c)) /
      Real.arcosh (1 + (2 / U) * epsilon))

/-- The canonical degree makes the shifted weight large enough for
elimination. -/
theorem chebyshevDegree_large
    {epsilon c U : ℝ} (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hU : 0 < U) :
    epsilon ≤ c *
      (chebyshevRemainder (chebyshevDegree epsilon c U)).eval
        ((2 / U) * epsilon) := by
  let x : ℝ := (2 / U) * epsilon
  let t : ℝ := Real.arcosh (1 + x)
  let L : ℝ := Real.log (2 * (1 + epsilon / c))
  let N : ℕ := chebyshevDegree epsilon c U
  have hx : 0 < x := mul_pos (div_pos (by norm_num) hU) hepsilon
  have ht : 0 < t := Real.arcosh_pos (by linarith [hx])
  have htarget : 0 < 2 * (1 + epsilon / c) := by positivity
  have hL : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    have : 0 < epsilon / c := div_pos hepsilon hc
    linarith
  have hceil : L / t ≤ (N : ℝ) := by
    dsimp [N, chebyshevDegree, L, t, x]
    exact Nat.le_ceil _
  have hNt : L ≤ (N : ℝ) * t := by
    calc
      L = (L / t) * t := by field_simp
      _ ≤ (N : ℝ) * t :=
        mul_le_mul_of_nonneg_right hceil ht.le
  have hexp :
      2 * (1 + epsilon / c) ≤
        Real.exp ((N : ℝ) * t) := by
    rw [← Real.exp_log htarget]
    exact Real.exp_le_exp.mpr hNt
  have hcosh : Real.cosh t = 1 + x :=
    Real.cosh_arcosh (by linarith)
  have hcheb :
      (chebyshevT N).eval (1 + x) =
        Real.cosh ((N : ℝ) * t) := by
    rw [← hcosh, chebyshevT_cosh]
  have hT :
      1 + epsilon / c ≤ (chebyshevT N).eval (1 + x) := by
    rw [hcheb]
    have hhalf := exp_div_two_le_cosh ((N : ℝ) * t)
    linarith
  have hTone : 1 ≤ (chebyshevT N).eval (1 + x) := by
    have : 0 < epsilon / c := div_pos hepsilon hc
    linarith
  have hsq :
      epsilon / c ≤ (chebyshevT N).eval (1 + x) ^ 2 - 1 := by
    nlinarith
  have hrem :
      (chebyshevRemainder N).eval x =
        (chebyshevT N).eval (1 + x) ^ 2 - 1 := by
    simp [chebyshevRemainder, shiftedChebyshev,
      Polynomial.eval_comp, add_comm]
  calc
    epsilon = c * (epsilon / c) := by field_simp
    _ ≤ c * ((chebyshevT N).eval (1 + x) ^ 2 - 1) :=
      mul_le_mul_of_nonneg_left hsq hc.le
    _ = c * (chebyshevRemainder N).eval x := by rw [hrem]
    _ = c * (chebyshevRemainder
        (chebyshevDegree epsilon c U)).eval
          ((2 / U) * epsilon) := by rfl

/-- The selected degree has the quantitative
`epsilon⁻¹ᐟ² · log(2+epsilon/c)` scale. -/
theorem chebyshevDegree_cast_le
    {epsilon c U : ℝ} (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hU : 0 < U)
    (hsmall : (2 / U) * epsilon ≤ 1) :
    (chebyshevDegree epsilon c U : ℝ) ≤
      Real.log (2 * (1 + epsilon / c)) /
          Real.sqrt ((2 / U) * epsilon) + 1 := by
  let x : ℝ := (2 / U) * epsilon
  let t : ℝ := Real.arcosh (1 + x)
  let L : ℝ := Real.log (2 * (1 + epsilon / c))
  let N : ℕ := chebyshevDegree epsilon c U
  have hx : 0 < x := mul_pos (div_pos (by norm_num) hU) hepsilon
  have ht : 0 < t := Real.arcosh_pos (by linarith [hx])
  have hL : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    have : 0 < epsilon / c := div_pos hepsilon hc
    linarith
  have hsqrt : Real.sqrt x ≤ t :=
    sqrt_le_arcosh_one_add hx (by simpa [x] using hsmall)
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hceil :
      (N : ℝ) < L / t + 1 := by
    dsimp [N, chebyshevDegree, L, t, x]
    exact Nat.ceil_lt_add_one (div_nonneg hL.le ht.le)
  have hdiv : L / t ≤ L / Real.sqrt x :=
    div_le_div_of_nonneg_left hL.le hsqrtpos hsqrt
  calc
    (chebyshevDegree epsilon c U : ℝ) = (N : ℝ) := rfl
    _ ≤ L / t + 1 := hceil.le
    _ ≤ L / Real.sqrt x + 1 := by linarith
    _ = Real.log (2 * (1 + epsilon / c)) /
          Real.sqrt ((2 / U) * epsilon) + 1 := by rfl

/-- Existence of a fully certified weight at the canonical degree. -/
theorem chebyshevEliminationWeight_exists
    {epsilon c U : ℝ} (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hU : 0 < U) :
    ∃ W : EliminationWeight epsilon c U,
      W.w.natDegree ≤ 2 * chebyshevDegree epsilon c U := by
  let N := chebyshevDegree epsilon c U
  let W := chebyshevEliminationWeight hepsilon hc hU N
    (chebyshevDegree_large hepsilon hc hU)
  refine ⟨W, ?_⟩
  exact chebyshevWeight_natDegree_le U N

end GeneralArchimedean
end OptimalConvergenceRates

end
