/-
  OptimalConvergenceRates/Chebyshev/ChebyshevGrowth.lean

  Chebyshev growth estimates outside [-1,1] and the univariate extremal property.
-/
import OptimalConvergenceRates.Chebyshev.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

open MvPolynomial Finset Polynomial

noncomputable section

namespace OptimalConvergenceRates

/-! ## Chebyshev growth bounds for x ≥ 1 (Lemma 3.5) -/

/-- The "cosh form" of the Chebyshev upper bound:
    T_d(cosh t) = cosh(dt) for t ≥ 0.
    This follows from T_d(cos θ) = cos(dθ) and cos(it) = cosh(t). -/
theorem chebyshevT_cosh (d : ℕ) (t : ℝ) :
    (chebyshevT d).eval (Real.cosh t) = Real.cosh (d * t) := by
  rw [chebyshevT_eq_T_nat]
  exact Polynomial.Chebyshev.T_real_cosh t d

/-- Key inequality: cosh(t) ≤ exp(t) for all t ≥ 0.
    Standard: cosh t = (e^t + e^{-t})/2 ≤ (e^t + e^t)/2 = e^t. -/
theorem cosh_le_exp (t : ℝ) (ht : 0 ≤ t) : Real.cosh t ≤ Real.exp t := by
  rw [Real.cosh_eq]
  have : Real.exp (-t) ≤ Real.exp t := by
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Key identity: exp(t) = cosh(t) + sinh(t). -/
theorem exp_eq_cosh_add_sinh (t : ℝ) :
    Real.exp t = Real.cosh t + Real.sinh t := by
  rw [Real.cosh_eq, Real.sinh_eq]; ring

/-- For x ≥ 1, we have x² - 1 ≥ 0. -/
theorem sq_sub_one_nonneg_of_ge_one (x : ℝ) (hx : 1 ≤ x) : 0 ≤ x ^ 2 - 1 := by
  nlinarith [sq_nonneg (x - 1)]

/-- **Lemma 3.5 (upper bound):** For x ≥ 1 and d ≥ 1,
    T_d(x) ≤ (x + √(x² - 1))^d.

    Proof sketch: Write x = cosh(t) for t = arccosh(x) ≥ 0.
    Then T_d(x) = T_d(cosh(t)) = cosh(d·t) ≤ exp(d·t) = (exp(t))^d
    = (cosh(t) + sinh(t))^d = (x + √(x²-1))^d. -/
theorem chebyshevT_upper_bound (d : ℕ) (x : ℝ) (hx : 1 ≤ x) (_hd : 1 ≤ d) :
    (chebyshevT d).eval x ≤ (x + Real.sqrt (x ^ 2 - 1)) ^ d := by
  -- Write x = cosh(arcosh x), then T_d(x) = cosh(d * arcosh x)
  set t := Real.arcosh x with ht_def
  have ht_nn : 0 ≤ t := Real.arcosh_nonneg hx
  have hcosh_t : Real.cosh t = x := Real.cosh_arcosh hx
  rw [← hcosh_t, chebyshevT_cosh]
  -- cosh(d*t) ≤ exp(d*t) = (exp t)^d = (cosh t + sinh t)^d
  have hsinh : Real.sinh t = Real.sqrt (Real.cosh t ^ 2 - 1) := by
    rw [ht_def, Real.sinh_arcosh hx, hcosh_t]
  calc Real.cosh (↑d * t)
      ≤ Real.exp (↑d * t) := cosh_le_exp _ (mul_nonneg (Nat.cast_nonneg d) ht_nn)
    _ = (Real.exp t) ^ d := by
        rw [← Real.exp_nat_mul t d]
    _ = (Real.cosh t + Real.sinh t) ^ d := by rw [← exp_eq_cosh_add_sinh]
    _ = (Real.cosh t + Real.sqrt (Real.cosh t ^ 2 - 1)) ^ d := by
        rw [hsinh]

/-- For x ≥ 1, T_d(x) ≥ 1. Follows from T_d(cos θ) = cos(dθ) and that
    for x ≥ 1, we can write x = cosh(t), so T_d(x) = cosh(dt) ≥ 1. -/
theorem chebyshevT_lower_bound_ge_one (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ (chebyshevT d).eval x := by
  rw [← Real.cosh_arcosh hx, chebyshevT_cosh]
  exact Real.one_le_cosh _

/-- T_d is monotone increasing on [1, ∞) for d ≥ 1.
    Since T_d(cosh t) = cosh(dt) and cosh is increasing on [0,∞),
    composing with the increasing arccosh gives monotonicity. -/
theorem chebyshevT_monotone_ge_one (d : ℕ) (_hd : 1 ≤ d) (x y : ℝ)
    (hx : 1 ≤ x) (hxy : x ≤ y) :
    (chebyshevT d).eval x ≤ (chebyshevT d).eval y := by
  have hy : 1 ≤ y := le_trans hx hxy
  rw [← Real.cosh_arcosh hx, ← Real.cosh_arcosh hy, chebyshevT_cosh, chebyshevT_cosh]
  -- cosh is monotone on [0,∞), and arcosh is monotone on [1,∞)
  have hax : 0 ≤ Real.arcosh x := Real.arcosh_nonneg hx
  have hay : 0 ≤ Real.arcosh y := Real.arcosh_nonneg hy
  have h_arcosh_le : Real.arcosh x ≤ Real.arcosh y := by
    rwa [Real.arcosh_le_arcosh (by linarith : (0 : ℝ) < x) (by linarith : (0 : ℝ) < y)]
  have h_mul_le : d * Real.arcosh x ≤ d * Real.arcosh y := by
    exact mul_le_mul_of_nonneg_left h_arcosh_le (Nat.cast_nonneg d)
  exact (Real.cosh_strictMonoOn.monotoneOn
    (Set.mem_Ici.mpr (mul_nonneg (Nat.cast_nonneg d) hax))
    (Set.mem_Ici.mpr (mul_nonneg (Nat.cast_nonneg d) hay))
    h_mul_le)

/-! ## Derivative bounds on [-1,1] -/

/-- The Chebyshev polynomial U_{d-1} of the second kind satisfies
    |U_{d-1}(x)| ≤ d for x ∈ [-1,1].
    (Since U_{d-1}(cos θ) = sin(dθ)/sin(θ), and by L'Hopital at θ=0,kπ
     the value is at most d.) -/
theorem chebyshevU_abs_le (d : ℕ) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |Polynomial.eval x (Polynomial.Chebyshev.U ℝ (d - 1 : ℤ))| ≤ d := by
  -- Proof by strong induction on d using U_{n+1} = x·U_n + T_{n+1}
  induction d using Nat.strongRecOn with
  | _ d ih =>
  match d with
  | 0 =>
    -- U ℝ (-1) = 0
    simp [Polynomial.Chebyshev.U_neg_one]
  | 1 =>
    -- U ℝ 0 = 1
    simp [Polynomial.Chebyshev.U_zero]
  | d + 2 =>
    -- U ℝ (d+1) = X · U ℝ d + T ℝ (d+1) (by U_eq_X_mul_U_add_T with n = d)
    have hU_rec : Polynomial.Chebyshev.U ℝ (↑(d + 2) - 1 : ℤ) =
        Polynomial.X * Polynomial.Chebyshev.U ℝ (↑(d + 1) - 1 : ℤ) +
        Polynomial.Chebyshev.T ℝ (↑(d + 2) - 1 : ℤ) := by
      push_cast
      have : (↑d + 2 - 1 : ℤ) = (↑d : ℤ) + 1 := by omega
      rw [this]
      have : (↑d + 1 - 1 : ℤ) = (↑d : ℤ) := by omega
      rw [this]
      exact Polynomial.Chebyshev.U_eq_X_mul_U_add_T ℝ ↑d
    rw [hU_rec]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    have habs_x : |x| ≤ 1 := abs_le.mpr ⟨by linarith, hx2⟩
    have ih_step : |Polynomial.eval x (Polynomial.Chebyshev.U ℝ (↑(d + 1) - 1))| ≤ ↑(d + 1) :=
      ih (d + 1) (by omega)
    have hT_bound : |Polynomial.eval x (Polynomial.Chebyshev.T ℝ (↑(d + 2) - 1 : ℤ))| ≤ 1 := by
      have : (↑(d + 2) - 1 : ℤ) = ↑(d + 1) := by omega
      rw [this, ← chebyshevT_eq_T_nat]
      exact chebyshevT_abs_le_one (d + 1) x hx1 hx2
    calc |x * Polynomial.eval x (Polynomial.Chebyshev.U ℝ (↑(d + 1) - 1)) +
            Polynomial.eval x (Polynomial.Chebyshev.T ℝ (↑(d + 2) - 1))|
        ≤ |x * Polynomial.eval x (Polynomial.Chebyshev.U ℝ (↑(d + 1) - 1))| +
          |Polynomial.eval x (Polynomial.Chebyshev.T ℝ (↑(d + 2) - 1))| :=
        abs_add_le _ _
      _ = |x| * |Polynomial.eval x (Polynomial.Chebyshev.U ℝ (↑(d + 1) - 1))| +
          |Polynomial.eval x (Polynomial.Chebyshev.T ℝ (↑(d + 2) - 1))| := by
        rw [abs_mul]
      _ ≤ 1 * (↑(d + 1) : ℝ) + 1 := by
        apply add_le_add
        · exact mul_le_mul habs_x ih_step (abs_nonneg _) (by norm_num)
        · exact hT_bound
      _ = ↑(d + 2) := by push_cast; ring

/-- **Derivative bound, k=0 (trivial):** |T_d(x)| ≤ 1 for x ∈ [-1,1].
    Already proved as chebyshevT_abs_le_one. -/
theorem chebyshevT_deriv_bound_k0 (d : ℕ) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |(chebyshevT d).eval x| ≤ 1 :=
  chebyshevT_abs_le_one d x hx1 hx2

/-- **Derivative bound, k=1:** |T_d'(x)| ≤ d² for x ∈ [-1,1].
    Uses the identity T_d' = d · U_{d-1} and |U_{d-1}(x)| ≤ d. -/
theorem chebyshevT_deriv_bound_k1 (d : ℕ) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |Polynomial.eval x (Polynomial.derivative (chebyshevT d))| ≤ (d : ℝ) ^ 2 := by
  -- Use T' = d · U_{d-1} (Mathlib's T_derivative_eq_U)
  rw [chebyshevT_eq_T_nat, Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [Polynomial.eval_mul, Polynomial.eval_intCast]
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
  -- Now need: d * |U_{d-1}(x)| ≤ d²
  calc (d : ℝ) * |Polynomial.eval x (Polynomial.Chebyshev.U ℝ (↑d - 1))|
      ≤ (d : ℝ) * d := by
        apply mul_le_mul_of_nonneg_left (chebyshevU_abs_le d x hx1 hx2) (Nat.cast_nonneg d)
    _ = (d : ℝ) ^ 2 := by ring

/-- U(n) - U(n-2) = 2·T(n). Derived from `U_sub_two` and `T_eq_U_sub_X_mul_U`. -/
private theorem chebyshevU_sub_eq_two_T (n : ℤ) :
    Polynomial.Chebyshev.U ℝ n - Polynomial.Chebyshev.U ℝ (n - 2) =
      2 * Polynomial.Chebyshev.T ℝ n := by
  have h1 := Polynomial.Chebyshev.U_sub_two ℝ n
  have h2 := Polynomial.Chebyshev.T_eq_U_sub_X_mul_U ℝ n
  linear_combination (norm := ring_nf) -h1 - 2 * h2

/-- Differentiating U(n) - U(n-2) = 2·T(n) gives a recurrence for U'(n). -/
private theorem chebyshevU_deriv_recurrence (n : ℤ) :
    Polynomial.derivative (Polynomial.Chebyshev.U ℝ n) =
      2 * (n : ℝ[X]) * Polynomial.Chebyshev.U ℝ (n - 1) +
      Polynomial.derivative (Polynomial.Chebyshev.U ℝ (n - 2)) := by
  have hsub := chebyshevU_sub_eq_two_T n
  have hd : Polynomial.derivative (Polynomial.Chebyshev.U ℝ n) -
      Polynomial.derivative (Polynomial.Chebyshev.U ℝ (n - 2)) =
      2 * ((n : ℝ[X]) * Polynomial.Chebyshev.U ℝ (n - 1)) := by
    rw [← Polynomial.derivative_sub, hsub]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_ofNat, zero_mul, zero_add]
    rw [Polynomial.Chebyshev.T_derivative_eq_U]
  linear_combination (norm := ring_nf) hd

/-- |U'_{d-1}(x)| ≤ d³ for x ∈ [-1,1], by strong induction stepping down by 2. -/
private theorem chebyshevU_deriv_abs_le (d : ℕ) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |Polynomial.eval x (Polynomial.derivative (Polynomial.Chebyshev.U ℝ (d - 1 : ℤ)))| ≤
      (d : ℝ) ^ 3 := by
  induction d using Nat.strongRecOn with
  | _ d ih =>
  match d with
  | 0 => simp [Polynomial.Chebyshev.U_neg_one]
  | 1 => simp [Polynomial.Chebyshev.U_zero]
  | d + 2 =>
    have hrec : Polynomial.derivative (Polynomial.Chebyshev.U ℝ (↑(d + 2) - 1 : ℤ)) =
        2 * ((↑d + 1 : ℤ) : ℝ[X]) * Polynomial.Chebyshev.U ℝ (↑d : ℤ) +
        Polynomial.derivative (Polynomial.Chebyshev.U ℝ (↑d - 1 : ℤ)) := by
      have : (↑(d + 2) - 1 : ℤ) = (↑d : ℤ) + 1 := by omega
      rw [this]
      convert chebyshevU_deriv_recurrence ((↑d : ℤ) + 1) using 2 <;> push_cast <;> ring_nf
    rw [hrec, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_intCast, Polynomial.eval_ofNat]
    have hU_bound : |Polynomial.eval x (Polynomial.Chebyshev.U ℝ (↑d : ℤ))| ≤
        (d + 1 : ℝ) := by
      have : (↑d : ℤ) = ↑(d + 1) - 1 := by omega
      rw [this]; exact_mod_cast chebyshevU_abs_le (d + 1) x hx1 hx2
    have ih_step : |Polynomial.eval x (Polynomial.derivative
        (Polynomial.Chebyshev.U ℝ (↑d - 1 : ℤ)))| ≤ (d : ℝ) ^ 3 :=
      ih d (by omega)
    calc |2 * ↑(↑d + 1 : ℤ) * Polynomial.eval x (Polynomial.Chebyshev.U ℝ ↑d) +
            Polynomial.eval x (Polynomial.derivative
              (Polynomial.Chebyshev.U ℝ (↑d - 1)))| ≤
          |2 * ↑(↑d + 1 : ℤ) * Polynomial.eval x (Polynomial.Chebyshev.U ℝ ↑d)| +
            |Polynomial.eval x (Polynomial.derivative
              (Polynomial.Chebyshev.U ℝ (↑d - 1)))| :=
        abs_add_le _ _
      _ ≤ 2 * (↑d + 1) * (↑d + 1) + (↑d : ℝ) ^ 3 := by
        apply add_le_add
        · rw [abs_mul, abs_mul]
          have : |↑(↑d + 1 : ℤ)| = ((d : ℝ) + 1) := by
            rw [show (↑(↑d + 1 : ℤ) : ℝ) = (d : ℝ) + 1 from by push_cast; ring]
            exact abs_of_nonneg (by positivity)
          rw [this, show |(2 : ℝ)| = 2 from by norm_num]
          exact mul_le_mul_of_nonneg_left hU_bound (by positivity)
        · exact ih_step
      _ ≤ (↑(d + 2) : ℝ) ^ 3 := by
        push_cast; nlinarith [sq_nonneg (d : ℝ), sq_nonneg ((d : ℝ) - 1)]

/-- The proof of the second derivative bound: |T''_d(x)| ≤ d⁴. -/
private theorem chebyshevT_deriv_bound_k2_proof (d : ℕ) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |Polynomial.eval x (Polynomial.derivative (Polynomial.derivative (chebyshevT d)))| ≤
      (d : ℝ) ^ 4 := by
  rw [chebyshevT_eq_T_nat]
  simp only [Polynomial.Chebyshev.T_derivative_eq_U,
    Polynomial.derivative_mul, Polynomial.derivative_intCast,
    zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_intCast]
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
  calc (d : ℝ) * |Polynomial.eval x (Polynomial.derivative
        (Polynomial.Chebyshev.U ℝ (↑d - 1)))| ≤ (d : ℝ) * (d : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left (chebyshevU_deriv_abs_le d x hx1 hx2) (Nat.cast_nonneg d)
    _ = (d : ℝ) ^ 4 := by ring

/-- **Derivative bound, k=2:** |T_d''(x)| ≤ d⁴ for x ∈ [-1,1].
    The second derivative satisfies a similar bound by iterated use of the
    recurrence for derivatives of Chebyshev polynomials. -/
theorem chebyshevT_deriv_bound_k2 (d : ℕ) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |Polynomial.eval x (Polynomial.derivative (Polynomial.derivative (chebyshevT d)))| ≤
      (d : ℝ) ^ 4 := by
  exact chebyshevT_deriv_bound_k2_proof d x hx1 hx2

/-! ## Extremal property (Equation 3.2, Markov k=0) -/

/-- Helper: if p is bounded by 1 on [-1,1] and has degree ≤ d, then |p(x)| ≤ T_d(x) for x ≥ 1.
    This is the Chebyshev extremal bound, proved by contradiction using root counting.
    If p(x₀) > T_d(x₀) for some x₀ ≥ 1, then q = p(x₀)·T_d - T_d(x₀)·p alternates sign at
    the d+1 Chebyshev nodes, giving d roots in [-1,1] by IVT, plus a root at x₀, totaling d+1
    roots for a polynomial of degree ≤ d — a contradiction.
    The absolute value version follows by applying to both p and -p. -/
private theorem chebyshevT_extremal_one_sided (d : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ d)
    (hpbnd : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → |p.eval t| ≤ 1)
    (x : ℝ) (hx : 1 ≤ x) :
    p.eval x ≤ (chebyshevT d).eval x := by
  -- Handle d = 0: T_0(x) = 1 and p is constant with |p| ≤ 1
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · -- d = 0: p has natDegree ≤ 0, so p = C(p.eval 0)
    simp only [chebyshevT_zero, Polynomial.eval_one]
    have h0 := hpbnd 0 (by norm_num) (by norm_num)
    have hp0 : p.natDegree = 0 := Nat.le_zero.mp hp
    have hconst : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hp0
    rw [hconst, Polynomial.eval_C]
    rw [hconst, Polynomial.eval_C] at h0
    exact le_of_abs_le h0
  -- d ≥ 1
  by_contra h_neg
  push Not at h_neg
  -- h_neg: (chebyshevT d).eval x < p.eval x
  -- Define px = p.eval x, Tx = T_d(x)
  set px := p.eval x with hpx_def
  set Tx := (chebyshevT d).eval x with hTx_def
  have hTx_ge_one : 1 ≤ Tx := chebyshevT_lower_bound_ge_one d x hx
  have hTx_pos : 0 < Tx := lt_of_lt_of_le zero_lt_one hTx_ge_one
  have hpx_pos : 0 < px := lt_of_lt_of_le hTx_pos (le_of_lt h_neg)
  -- Define q = px * T_d - Tx * p, so q(x) = 0
  set q := Polynomial.C px * chebyshevT d - Polynomial.C Tx * p with hq_def
  -- q(x) = px * Tx - Tx * px = 0
  have hq_eval_x : q.eval x = 0 := by
    simp [hq_def, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  -- q has natDegree ≤ d
  have hq_deg : q.natDegree ≤ d := by
    calc q.natDegree ≤ max (Polynomial.C px * chebyshevT d).natDegree
            (Polynomial.C Tx * p).natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ max d d := by
          apply max_le_max
          · exact (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_chebyshevT d).le
          · exact (Polynomial.natDegree_C_mul_le _ _).trans hp
      _ = d := max_self d
  -- At nodes t_k = cos(k*π/d) for k = 0,...,d: T_d(t_k) = (-1)^k
  -- q(t_k) = px * (-1)^k - Tx * p(t_k)
  -- Since px > Tx ≥ 1 and |p(t_k)| ≤ 1, we have |Tx * p(t_k)| ≤ Tx < px
  -- So sign(q(t_k)) = sign((-1)^k * px) = (-1)^k (since px > 0)

  -- Use Mathlib's Chebyshev nodes
  have hd_ne : d ≠ 0 := by omega
  -- q alternates sign at consecutive nodes, giving roots by IVT
  -- Between node k and node k+1 (where node k > node k+1 since cos is decreasing),
  -- q changes sign, so there exists a root in (node(k+1), node(k))

  -- Evaluate q at nodes
  have hq_eval_node : ∀ k : ℕ, k ≤ d →
      q.eval (Polynomial.Chebyshev.node d k) =
      px * (-1 : ℝ) ^ k - Tx * p.eval (Polynomial.Chebyshev.node d k) := by
    intro k hk
    simp only [hq_def, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    congr 1
    -- T_d(node d k) = (-1)^k via Mathlib's eval_T_real_node
    have heval := Polynomial.Chebyshev.eval_T_real_node (n := d) (i := k)
      (Finset.mem_Iic.mpr hk)
    -- heval : (T ℝ d).eval (node d k) = (-1) ^ k
    -- We need: (chebyshevT d).eval (node d k) = (-1) ^ k
    rw [chebyshevT_eq_T_nat, heval]
  -- The sign of q at node k is (-1)^k
  have hq_sign : ∀ k : ℕ, k ≤ d →
      0 < (-1 : ℝ) ^ k * q.eval (Polynomial.Chebyshev.node d k) := by
    intro k hk
    rw [hq_eval_node k hk]
    -- (-1)^k * (px * (-1)^k - Tx * p(node d k))
    -- = (-1)^(2k) * px - (-1)^k * Tx * p(node d k)
    -- = px - (-1)^k * Tx * p(node d k)
    have h1 : (-1 : ℝ) ^ k * (px * (-1 : ℝ) ^ k - Tx * p.eval (Polynomial.Chebyshev.node d k)) =
        px - (-1 : ℝ) ^ k * (Tx * p.eval (Polynomial.Chebyshev.node d k)) := by
      have hmul : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
        rw [← pow_add, ← two_mul, neg_one_pow_eq_one_iff_even (by norm_num)]
        exact even_two_mul k
      nlinarith [hmul]
    rw [h1]
    -- Need: px > |(-1)^k * Tx * p(node d k)|
    -- |(-1)^k * Tx * p(node d k)| = Tx * |p(node d k)| ≤ Tx * 1 = Tx < px
    have hnode_mem := Polynomial.Chebyshev.node_mem_Icc (n := d) (i := k)
    have hnode_bnd := hpbnd (Polynomial.Chebyshev.node d k)
      (Set.mem_Icc.mp hnode_mem).1 (Set.mem_Icc.mp hnode_mem).2
    have h2 : |(-1 : ℝ) ^ k * (Tx * p.eval (Polynomial.Chebyshev.node d k))| ≤ Tx := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
          abs_of_nonneg (le_of_lt hTx_pos)]
      calc Tx * |p.eval (Polynomial.Chebyshev.node d k)|
          ≤ Tx * 1 := by exact mul_le_mul_of_nonneg_left hnode_bnd (le_of_lt hTx_pos)
        _ = Tx := mul_one Tx
    -- |(-1)^k * (Tx * p(node))| ≤ Tx < px, so px - (-1)^k*(Tx*p(node)) > 0
    have h3 : (-1 : ℝ) ^ k * (Tx * p.eval (Polynomial.Chebyshev.node d k)) ≤ Tx :=
      (le_abs_self _).trans h2
    linarith
  -- Now q changes sign between consecutive nodes. By IVT, q has a root between them.
  -- nodes: node d 0 > node d 1 > ... > node d d (strictly decreasing)
  -- q is continuous (it's a polynomial)
  have hq_cont : Continuous (fun t => q.eval t) := Polynomial.continuous_aeval q
  -- Between node k and node k+1, q changes sign, so there's a root
  -- We need d roots in [-1,1] (between d+1 nodes there are d intervals)
  -- Plus the root at x ≥ 1 (which is > node d 0 = 1)

  -- First show q ≠ 0 (since q(x) = 0 but q alternates sign at nodes)
  have hq_ne_zero : q ≠ 0 := by
    intro heq
    have := hq_sign 0 (Nat.zero_le d)
    rw [heq, Polynomial.eval_zero, mul_zero] at this
    linarith
  -- Collect d distinct roots in (-1, 1) using IVT
  -- Between node (k+1) and node k (since node(k+1) < node(k)), q changes sign
  -- IVT gives a root in the open interval (node(k+1), node(k))

  -- We'll show that q has at least d+1 roots by finding d roots between consecutive nodes
  -- plus the root at x

  -- Key: for k = 0, ..., d-1, q has opposite signs at node k and node (k+1)
  -- Indeed: (-1)^k * q(node k) > 0 and (-1)^(k+1) * q(node(k+1)) > 0
  -- So q(node k) and q(node(k+1)) have opposite signs

  -- IVT root between node(k+1) and node(k) for each k = 0,...,d-1
  have hq_roots_interior : ∀ k : ℕ, k < d → ∃ r : ℝ,
      Polynomial.Chebyshev.node d (k + 1) < r ∧ r < Polynomial.Chebyshev.node d k ∧
      q.eval r = 0 := by
    intro k hk
    have hk1 : k + 1 ≤ d := hk
    have hk0 : k ≤ d := le_of_lt (Nat.lt_of_lt_of_le hk (le_refl d))
    -- node(k+1) < node(k)
    have hnode_lt : Polynomial.Chebyshev.node d (k + 1) < Polynomial.Chebyshev.node d k :=
      Polynomial.Chebyshev.node_lt hk1 (Nat.lt_succ_of_le (le_refl k))
    -- q has opposite signs at node k and node(k+1)
    have hsign_k := hq_sign k hk0
    have hsign_k1 := hq_sign (k + 1) hk1
    -- (-1)^k * q(node k) > 0 and (-1)^(k+1) * q(node(k+1)) > 0
    -- Since (-1)^(k+1) = -(-1)^k, these have "opposite parity"
    -- q(node k) > 0 ↔ k is even; q(node(k+1)) > 0 ↔ k+1 is even ↔ k is odd
    -- So q(node k) and q(node(k+1)) have opposite signs
    have hopp : q.eval (Polynomial.Chebyshev.node d k) *
        q.eval (Polynomial.Chebyshev.node d (k + 1)) < 0 := by
      -- (-1)^k * q_k > 0 and (-1)^(k+1) * q_{k+1} > 0
      -- q_k * q_{k+1} = ((-1)^k * q_k) * ((-1)^(k+1) * q_{k+1}) * ((-1)^k * (-1)^(k+1))
      -- = pos * pos * (-1)^(2k+1) = pos * (-1) < 0
      have h1 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k + 1) = -1 := by
        rw [pow_succ, ← mul_assoc, ← pow_add, ← two_mul,
            neg_one_pow_eq_one_iff_even (by norm_num) |>.mpr (even_two_mul k)]
        ring
      nlinarith
    -- Use IVT: q is continuous on [node(k+1), node(k)], and q changes sign
    -- So there exists r in (node(k+1), node(k)) with q(r) = 0
    -- q changes sign between node(k+1) and node(k), so by IVT there's a root
    -- Use intermediate_value_uIcc for simplicity
    have hqk_ne : q.eval (Polynomial.Chebyshev.node d k) ≠ 0 := by
      intro heq; simp [heq] at hsign_k
    have hqk1_ne : q.eval (Polynomial.Chebyshev.node d (k + 1)) ≠ 0 := by
      intro heq; simp [heq] at hsign_k1
    -- By IVT, there's a root between node(k+1) and node(k)
    by_cases hqk_pos : 0 < q.eval (Polynomial.Chebyshev.node d k)
    · have hqk1_neg : q.eval (Polynomial.Chebyshev.node d (k + 1)) < 0 := by nlinarith
      -- 0 ∈ Icc(f(node(k+1)), f(node(k))) and intermediate_value_Icc gives this ⊆ image
      obtain ⟨r, hr_mem, hr_eq⟩ := intermediate_value_Icc (le_of_lt hnode_lt)
        hq_cont.continuousOn
        (Set.mem_Icc.mpr ⟨le_of_lt hqk1_neg, le_of_lt hqk_pos⟩)
      simp only at hr_eq
      refine ⟨r, ?_, ?_, hr_eq⟩
      · exact lt_of_le_of_ne (Set.mem_Icc.mp hr_mem).1
          (fun h => by rw [← h] at hr_eq; linarith)
      · exact lt_of_le_of_ne (Set.mem_Icc.mp hr_mem).2
          (fun h => by rw [h] at hr_eq; linarith)
    · push Not at hqk_pos
      have hqk_neg : q.eval (Polynomial.Chebyshev.node d k) < 0 :=
        lt_of_le_of_ne hqk_pos hqk_ne
      have hqk1_pos : 0 < q.eval (Polynomial.Chebyshev.node d (k + 1)) := by nlinarith
      obtain ⟨r, hr_mem, hr_eq⟩ := intermediate_value_Icc' (le_of_lt hnode_lt)
        hq_cont.continuousOn
        (Set.mem_Icc.mpr ⟨le_of_lt hqk_neg, le_of_lt hqk1_pos⟩)
      simp only at hr_eq
      refine ⟨r, ?_, ?_, hr_eq⟩
      · exact lt_of_le_of_ne (Set.mem_Icc.mp hr_mem).1
          (fun h => by rw [← h] at hr_eq; linarith)
      · exact lt_of_le_of_ne (Set.mem_Icc.mp hr_mem).2
          (fun h => by rw [h] at hr_eq; linarith)
  -- Now extract d roots using choice, parametrized by Fin d
  -- For each k : Fin d, choose a root in (node(k+1), node(k))
  have hq_roots_fin : ∀ k : Fin d, ∃ r : ℝ,
      Polynomial.Chebyshev.node d (k.val + 1) < r ∧
      r < Polynomial.Chebyshev.node d k.val ∧
      q.eval r = 0 :=
    fun k => hq_roots_interior k.val k.isLt
  choose roots hroots_lb hroots_ub hroots_eq using hq_roots_fin
  -- These d roots are distinct (they lie in disjoint intervals)
  have hroots_distinct : ∀ i j : Fin d, i < j → roots i ≠ roots j := by
    intro i j hij habs
    -- roots i ∈ (node(i+1), node(i)) and roots j ∈ (node(j+1), node(j))
    -- Since i < j, node d j ≤ node d (i+1), so intervals are disjoint
    -- roots j < node d j ≤ node d (i+1) < roots i
    have h1 : roots j < Polynomial.Chebyshev.node d j.val := hroots_ub j
    have h2 : Polynomial.Chebyshev.node d (i.val + 1) < roots i := hroots_lb i
    have h4 : i.val + 1 ≤ d := i.isLt
    have h5 : i.val + 1 ≤ j.val := hij
    have h6 : Polynomial.Chebyshev.node d j.val ≤ Polynomial.Chebyshev.node d (i.val + 1) := by
      rcases eq_or_lt_of_le h5 with heq | hlt
      · rw [heq]
      · exact le_of_lt (Polynomial.Chebyshev.node_lt (le_of_lt j.isLt) hlt)
    linarith
  -- x is distinct from all the interior roots (x ≥ 1 = node d 0 > roots k for all k)
  have hx_ne_roots : ∀ k : Fin d, roots k ≠ x := by
    intro k habs
    have : roots k < Polynomial.Chebyshev.node d k.val := hroots_ub k
    have : Polynomial.Chebyshev.node d k.val ≤ Polynomial.Chebyshev.node d 0 := by
      rcases Nat.eq_zero_or_pos k.val with hk0 | hk_pos
      · simp [hk0]
      · exact le_of_lt (Polynomial.Chebyshev.node_lt (le_of_lt k.isLt) hk_pos)
    have : Polynomial.Chebyshev.node d 0 = 1 := Polynomial.Chebyshev.node_eq_one
    linarith
  -- Now we have d+1 distinct roots of q: roots 0, ..., roots (d-1), and x
  -- q ≠ 0 and q.natDegree ≤ d, but a nonzero polynomial of degree ≤ d has at most d roots
  -- Show each root is in q.roots (the multiset of roots)
  have hroots_mem : ∀ k : Fin d, roots k ∈ q.roots :=
    fun k => (Polynomial.mem_roots hq_ne_zero).mpr (hroots_eq k)
  have hx_mem : x ∈ q.roots :=
    (Polynomial.mem_roots hq_ne_zero).mpr hq_eval_x
  -- Build an injection Fin (d+1) → q.roots.toFinset to get a contradiction
  have : d + 1 ≤ q.roots.card := by
    -- Define f : Fin (d+1) → ℝ by f(i) = roots i for i < d, f(d) = x
    let f : Fin (d + 1) → ℝ := fun i =>
      if h : i.val < d then roots ⟨i.val, h⟩ else x
    -- f is injective
    have hf_inj : Function.Injective f := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp only [f] at heq
      split_ifs at heq with h1 h2 h2
      · -- both < d
        ext
        by_contra hab
        push Not at hab
        rcases lt_or_gt_of_ne hab with hij | hji
        · exact hroots_distinct ⟨i, h1⟩ ⟨j, h2⟩ hij heq
        · exact hroots_distinct ⟨j, h2⟩ ⟨i, h1⟩ hji heq.symm
      · -- i < d, j ≥ d (so j = d)
        exfalso; exact hx_ne_roots ⟨i, h1⟩ heq
      · -- i ≥ d, j < d
        exfalso; exact hx_ne_roots ⟨j, h2⟩ heq.symm
      · -- both ≥ d, so both = d
        simp only [Fin.mk.injEq]; omega
    -- Each f(i) ∈ q.roots
    have hf_mem : ∀ i : Fin (d + 1), f i ∈ q.roots := by
      intro ⟨i, hi⟩
      simp only [f]
      split_ifs with h
      · exact hroots_mem ⟨i, h⟩
      · exact hx_mem
    -- Finset.image f univ ⊆ q.roots.toFinset, and has card d+1
    have hcard := Finset.card_le_card
      (Finset.image_subset_iff.mpr (fun i _ => Multiset.mem_toFinset.mpr (hf_mem i)) :
        Finset.image f Finset.univ ⊆ q.roots.toFinset)
    rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin] at hcard
    exact le_trans hcard (Multiset.toFinset_card_le q.roots)
  -- But q.roots.card ≤ q.natDegree ≤ d
  have hcard_le := Polynomial.card_roots' q
  omega

/-- Two-sided version: if p is bounded by 1 on [-1,1] and has degree ≤ d,
    then |p(x)| ≤ T_d(x) for x ≥ 1. Follows from one-sided applied to p and -p. -/
private theorem chebyshevT_extremal_abs (d : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ d)
    (hpbnd : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → |p.eval t| ≤ 1)
    (x : ℝ) (hx : 1 ≤ x) :
    |p.eval x| ≤ (chebyshevT d).eval x := by
  rw [abs_le]
  constructor
  · -- -(T_d(x)) ≤ p(x), equivalently (-p)(x) ≤ T_d(x)
    have h := chebyshevT_extremal_one_sided d (-p)
      ((Polynomial.natDegree_neg p).le.trans hp) (by
        intro t ht1 ht2; rw [Polynomial.eval_neg, abs_neg]; exact hpbnd t ht1 ht2) x hx
    simp only [Polynomial.eval_neg] at h; linarith
  · exact chebyshevT_extremal_one_sided d p hp hpbnd x hx

/-- T_d(x) is nonneg for x ≥ 1 (immediate from lower bound). -/
theorem chebyshevT_nonneg_ge_one (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ (chebyshevT d).eval x :=
  le_trans (by norm_num) (chebyshevT_lower_bound_ge_one d x hx)

/-- **Chebyshev extremal property (Markov inequality, k=0):**
    For any polynomial p of degree ≤ d and |x| ≥ 1,
    |p(x)| ≤ ‖p‖_{[-1,1]} · T_d(|x|).

    This is the classical Chebyshev extremal result: T_d grows fastest
    outside [-1,1] among all degree-d polynomials with sup-norm ≤ 1. -/
theorem chebyshevT_extremal (d : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ d) (x : ℝ)
    (hx : 1 ≤ |x|) :
    |p.eval x| ≤ polySupNormUni p * (chebyshevT d).eval |x| := by
  -- Handle polySupNormUni p = 0
  by_cases hsup_pos : polySupNormUni p = 0
  · -- p = 0 (vanishes on [-1,1] which is infinite)
    have hp_zero : p = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).mono
      intro t ht
      have ht_mem := Set.mem_Icc_of_Ioo ht
      have := polySupNormUni_eval_le p t ht_mem.1 ht_mem.2
      rw [hsup_pos] at this
      exact abs_nonpos_iff.mp this
    subst hp_zero
    simp only [Polynomial.eval_zero, abs_zero]
    exact mul_nonneg (polySupNormUni_nonneg 0) (chebyshevT_nonneg_ge_one d |x| hx)
  · -- polySupNormUni p > 0
    have hsup_pos' : 0 < polySupNormUni p :=
      lt_of_le_of_ne (polySupNormUni_nonneg p) (Ne.symm hsup_pos)
    set c := polySupNormUni p with hc_def
    -- For x with |x| ≥ 1, consider the polynomial at |x|
    -- We need a polynomial that evaluates at |x| to give |p(x)|
    -- Strategy: use p ∘ (sign(x) · id), i.e., r(t) = p(sign(x) · t)
    -- For x ≥ 0: r = p, for x < 0: r(t) = p(-t)
    -- In both cases: r has same degree and same sup-norm on [-1,1]
    -- And |r(|x|)| = |p(x)|

    -- Construct the "reflected" polynomial if needed
    -- p.comp (-X) gives p(-t), which has same natDegree and same sup-norm on [-1,1]
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0, so |x| = x
      rw [abs_of_nonneg hx_nn] at hx ⊢
      -- Apply abs version to p at x
      have hbnd : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → |(Polynomial.C c⁻¹ * p).eval t| ≤ 1 := by
        intro t ht1 ht2
        simp only [Polynomial.eval_mul, Polynomial.eval_C]
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hsup_pos')),
            inv_mul_le_iff₀ hsup_pos', mul_one]
        exact polySupNormUni_eval_le p t ht1 ht2
      have hdeg : (Polynomial.C c⁻¹ * p).natDegree ≤ d :=
        (Polynomial.natDegree_C_mul_le _ _).trans hp
      have h := chebyshevT_extremal_abs d (Polynomial.C c⁻¹ * p) hdeg hbnd x hx
      -- h : |c⁻¹ * p(x)| ≤ T_d(x)
      simp only [Polynomial.eval_mul, Polynomial.eval_C] at h
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hsup_pos'))] at h
      -- h : c⁻¹ * |p(x)| ≤ T_d(x)
      calc |p.eval x| = c * (c⁻¹ * |p.eval x|) := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsup_pos'), one_mul]
        _ ≤ c * (chebyshevT d).eval x := by
            exact mul_le_mul_of_nonneg_left h (le_of_lt hsup_pos')
    · -- x < 0, so |x| = -x and -x ≥ 1
      push Not at hx_nn
      rw [abs_of_neg hx_nn] at hx ⊢
      -- Consider r(t) = p(-t) = p.comp (-X)
      set r := p.comp (-Polynomial.X) with hr_def
      -- r has same natDegree
      have hr_deg : r.natDegree ≤ d := by
        calc r.natDegree ≤ p.natDegree * (-Polynomial.X : Polynomial ℝ).natDegree :=
              Polynomial.natDegree_comp_le
          _ = p.natDegree * 1 := by
              congr 1; rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
          _ = p.natDegree := mul_one _
          _ ≤ d := hp
      -- r has same sup-norm on [-1,1]: |r(t)| = |p(-t)| and -t ∈ [-1,1]
      have hr_bnd : ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
          |(Polynomial.C c⁻¹ * r).eval t| ≤ 1 := by
        intro t ht1 ht2
        simp only [Polynomial.eval_mul, Polynomial.eval_C, hr_def,
                    Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hsup_pos')),
            inv_mul_le_iff₀ hsup_pos', mul_one]
        exact polySupNormUni_eval_le p (-t) (by linarith) (by linarith)
      have hcr_deg : (Polynomial.C c⁻¹ * r).natDegree ≤ d :=
        (Polynomial.natDegree_C_mul_le _ _).trans hr_deg
      have h := chebyshevT_extremal_abs d (Polynomial.C c⁻¹ * r) hcr_deg hr_bnd (-x) hx
      simp only [Polynomial.eval_mul, Polynomial.eval_C, hr_def,
                  Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] at h
      rw [neg_neg] at h
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hsup_pos'))] at h
      calc |p.eval x| = c * (c⁻¹ * |p.eval x|) := by
            rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsup_pos'), one_mul]
        _ ≤ c * (chebyshevT d).eval (-x) := by
            exact mul_le_mul_of_nonneg_left h (le_of_lt hsup_pos')

/-- Variant with x ≥ 1 directly. -/
theorem chebyshevT_extremal' (d : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ d) (x : ℝ)
    (hx : 1 ≤ x) :
    |p.eval x| ≤ polySupNormUni p * (chebyshevT d).eval x := by
  have habsx : |x| = x := abs_of_nonneg (by linarith)
  have h := chebyshevT_extremal d p hp x (by rwa [habsx])
  rwa [habsx] at h

/-! ## Lemma 3.6: Chebyshev evaluated near 1 -/

/-- Auxiliary: for 0 ≤ δ ≤ 1/2, we have 1/(1-δ) ≤ 1 + 2δ. -/
theorem inv_one_sub_le (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    1 / (1 - δ) ≤ 1 + 2 * δ := by
  have h1 : 0 < 1 - δ := by linarith
  rw [div_le_iff₀ h1]
  nlinarith

/-- Auxiliary: √(1/(1-δ)² - 1) ≤ √(5δ) for 0 ≤ δ ≤ 1/4.
    Since 1/(1-δ)² - 1 = (2δ-δ²)/(1-δ)² ≤ 5δ when δ ≤ 1/4. -/
theorem sqrt_bound_near_one (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) :
    Real.sqrt ((1 / (1 - δ)) ^ 2 - 1) ≤ Real.sqrt (5 * δ) := by
  apply Real.sqrt_le_sqrt
  have h1 : 0 < 1 - δ := by linarith
  have h2 : 0 < (1 - δ) ^ 2 := sq_pos_of_pos h1
  rw [div_pow, one_pow]
  rw [div_sub_one (ne_of_gt h2)]
  rw [div_le_iff₀ h2]
  -- Need: 1 - (1-δ)² ≤ 5δ(1-δ)², i.e. 2δ-δ² ≤ 5δ-10δ²+5δ³
  -- i.e. 0 ≤ 3δ - 9δ² + 5δ³ = δ(3 - 9δ + 5δ²)
  -- For δ ≤ 1/4: 3 - 9(1/4) + 5(1/16) = 3 - 2.25 + 0.3125 = 1.0625 > 0
  nlinarith [sq_nonneg δ, sq_nonneg (1 - 2 * δ)]

/-- Auxiliary: (1 + t)^d ≤ exp(t*d) for t ≥ 0.
    Standard: 1 + t ≤ exp(t), so (1+t)^d ≤ exp(t)^d = exp(td). -/
theorem one_add_pow_le_exp (t : ℝ) (ht : 0 ≤ t) (d : ℕ) :
    (1 + t) ^ d ≤ Real.exp (t * d) := by
  have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have h1' : 1 + t ≤ Real.exp t := by linarith
  calc (1 + t) ^ d
      ≤ (Real.exp t) ^ d :=
        pow_le_pow_left₀ (by linarith) h1' d
    _ = Real.exp (t * d) := by
        rw [← Real.exp_nat_mul]; ring_nf

/-- For √δ ≤ 1/d (i.e. δ ≤ 1/d²), we have 5·√δ ≤ 5/d. -/
theorem five_sqrt_le (d : ℕ) (δ : ℝ) (hd : 2 ≤ d) (_hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (d : ℝ) ^ 2) :
    5 * Real.sqrt δ ≤ 5 / d := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have h1 : Real.sqrt δ ≤ Real.sqrt (1 / (d : ℝ) ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt (1 / (d : ℝ) ^ 2) = 1 / d := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_sq (le_of_lt hd_pos), one_div]
  have h3 : Real.sqrt δ ≤ 1 / d := h2 ▸ h1
  have h4 : 5 * Real.sqrt δ ≤ 5 * (1 / d) := by nlinarith
  have h5 : 5 * (1 / (d : ℝ)) = 5 / d := by ring
  linarith

/-! ## Bernoulli-type inequalities needed for Lemma 3.6 -/

/-- (1 + t/d)^d ≤ exp(t) for t ≥ 0 and d ≥ 1.
    Special case of the standard limit (1 + t/d)^d → exp(t). -/
theorem one_add_div_pow_le_exp (t : ℝ) (ht : 0 ≤ t) (d : ℕ) (hd : 1 ≤ d) :
    (1 + t / d) ^ d ≤ Real.exp t := by
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  calc (1 + t / d) ^ d ≤ Real.exp (t / d * d) :=
        one_add_pow_le_exp (t / d) (div_nonneg ht (le_of_lt hd_pos)) d
       _ = Real.exp t := by rw [div_mul_cancel₀ t (ne_of_gt hd_pos)]

/-- δ ≤ 1/d² and d ≥ 2 implies δ ≤ 1/2. -/
theorem delta_le_half (d : ℕ) (hd : 2 ≤ d) (δ : ℝ) (_hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (d : ℝ) ^ 2) : δ ≤ 1 / 2 := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := Nat.ofNat_le_cast.mpr hd
  have hd_sq : (d : ℝ) ^ 2 ≥ 4 := by nlinarith
  have : 1 / (d : ℝ) ^ 2 ≤ 1 / 4 :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ (d : ℝ) ^ 2)
  linarith

/-- δ ≤ 1/d² and d ≥ 2 implies 1 - δ > 0. -/
theorem one_sub_delta_pos (d : ℕ) (hd : 2 ≤ d) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (d : ℝ) ^ 2) : 0 < 1 - δ := by
  have := delta_le_half d hd δ hδ0 hδ
  linarith

/-- δ ≤ 1/d² and d ≥ 2 implies 1/(1-δ) ≥ 1. -/
theorem one_le_inv_one_sub (d : ℕ) (hd : 2 ≤ d) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (d : ℝ) ^ 2) : 1 ≤ 1 / (1 - δ) := by
  have h_pos := one_sub_delta_pos d hd δ hδ0 hδ
  rw [le_div_iff₀ h_pos]
  linarith

/-- **(Lemma 3.6):** There exists a constant c ∈ [1, e^5] such that for all
    d ≥ 2 and δ ≤ 1/d², we have T_d(1/(1-δ)) ≤ c.

    Proof idea:
    T_d(1/(1-δ)) ≤ (1/(1-δ) + √((1/(1-δ))²-1))^d       (by Lemma 3.5)
                  ≤ (1 + 2δ + √(5δ))^d                     (estimates)
                  ≤ (1 + 5√δ)^d                             (since 2δ ≤ 2√δ for δ ≤ 1)
                  ≤ (1 + 5/d)^d                             (since √δ ≤ 1/d)
                  ≤ e^5                                      (since (1+t/d)^d ≤ e^t)
-/
theorem chebyshevT_constant_c (d : ℕ) (hd : 2 ≤ d) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (d : ℝ) ^ 2) :
    (chebyshevT d).eval (1 / (1 - δ)) ≤ Real.exp 5 := by
  have hd1 : 1 ≤ d := by omega
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hδ_half : δ ≤ 1 / 2 := delta_le_half d hd δ hδ0 hδ
  have hδ_quarter : δ ≤ 1 / 4 := by
    have hd2 : (2 : ℝ) ≤ (d : ℝ) := Nat.ofNat_le_cast.mpr hd
    have : 1 / (d : ℝ) ^ 2 ≤ 1 / 4 :=
      div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity) (by nlinarith)
    linarith
  have h_one_le : 1 ≤ 1 / (1 - δ) := one_le_inv_one_sub d hd δ hδ0 hδ
  -- Step 1: T_d(1/(1-δ)) ≤ (1/(1-δ) + √((1/(1-δ))²-1))^d
  have h_ub := chebyshevT_upper_bound d (1 / (1 - δ)) h_one_le hd1
  -- Step 2: 1/(1-δ) + √((1/(1-δ))²-1) ≤ (1 + 2δ) + √(5δ)
  have h_inv_le : 1 / (1 - δ) ≤ 1 + 2 * δ := inv_one_sub_le δ hδ0 hδ_half
  have h_sqrt_le : Real.sqrt ((1 / (1 - δ)) ^ 2 - 1) ≤ Real.sqrt (5 * δ) :=
    sqrt_bound_near_one δ hδ0 hδ_quarter
  have h_sum_le : 1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1) ≤
      (1 + 2 * δ) + Real.sqrt (5 * δ) := by linarith
  -- Step 3: (1 + 2δ) + √(5δ) ≤ 1 + 5√δ
  -- We need 2δ + √(5δ) ≤ 5√δ, i.e. 2δ ≤ 5√δ - √(5δ) = (5 - √5)√δ
  -- Since δ ≤ 1, we have δ ≤ √δ, so 2δ ≤ 2√δ. And √(5δ) = √5·√δ ≤ 3√δ.
  -- Hence 2δ + √(5δ) ≤ 2√δ + √5·√δ = (2+√5)√δ ≤ 5√δ (since 2+√5 ≈ 4.24 ≤ 5).
  have h_sqrt5_le : Real.sqrt (5 * δ) = Real.sqrt 5 * Real.sqrt δ := by
    rw [Real.sqrt_mul (by norm_num : (5 : ℝ) ≥ 0)]
  have h_sqrt_delta_nn : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have h_delta_le_sqrt_delta : δ ≤ Real.sqrt δ := by
    -- Suffices to show δ^2 ≤ δ (then √(δ²) = δ and √(δ²) ≤ √δ)
    -- Equivalently: δ ≤ 1 implies δ^2 ≤ δ
    calc δ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq hδ0).symm
      _ ≤ Real.sqrt δ := by
          apply Real.sqrt_le_sqrt
          -- δ^2 ≤ δ since δ ≤ 1/2 ≤ 1
          calc δ ^ 2 = δ * δ := sq δ
            _ ≤ δ * 1 := by
                apply mul_le_mul_of_nonneg_left _ hδ0
                linarith
            _ = δ := mul_one δ
  have h_sqrt5_bound : Real.sqrt 5 ≤ 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 from by
      rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h_step3 : (1 + 2 * δ) + Real.sqrt (5 * δ) ≤ 1 + 5 * Real.sqrt δ := by
    rw [h_sqrt5_le]
    have h1 : 2 * δ ≤ 2 * Real.sqrt δ := by nlinarith
    have h2 : Real.sqrt 5 * Real.sqrt δ ≤ 3 * Real.sqrt δ := by
      nlinarith [h_sqrt_delta_nn]
    linarith
  -- Step 4: (1 + 5√δ)^d ≤ (1 + 5/d)^d
  have h_five_sqrt : 5 * Real.sqrt δ ≤ 5 / d := five_sqrt_le d δ hd hδ0 hδ
  -- Step 5: (1 + 5/d)^d ≤ e^5
  have h_exp5 : (1 + 5 / d) ^ d ≤ Real.exp 5 :=
    one_add_div_pow_le_exp 5 (by norm_num) d hd1
  -- Combine everything
  have h_base_le : 1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1) ≤ 1 + 5 / ↑d := by
    calc 1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1)
        ≤ (1 + 2 * δ) + Real.sqrt (5 * δ) := h_sum_le
      _ ≤ 1 + 5 * Real.sqrt δ := h_step3
      _ ≤ 1 + 5 / ↑d := by linarith
  have h_base_pos : 0 ≤ 1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1) := by
    have : 0 ≤ Real.sqrt ((1 / (1 - δ)) ^ 2 - 1) := Real.sqrt_nonneg _
    linarith
  calc (chebyshevT d).eval (1 / (1 - δ))
      ≤ (1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1)) ^ d := h_ub
    _ ≤ (1 + 5 / ↑d) ^ d := by
        exact pow_le_pow_left₀ h_base_pos h_base_le d
    _ ≤ Real.exp 5 := h_exp5

/-- The constant c from Lemma 3.6: we take c = e^5.
    This satisfies 1 ≤ c (since e^5 > 1) and the bound from chebyshevT_constant_c. -/
noncomputable def constCChebyshev : ℝ := Real.exp 5

theorem constCChebyshev_pos : 0 < constCChebyshev := Real.exp_pos 5

theorem one_le_constCChebyshev : 1 ≤ constCChebyshev := by
  unfold constCChebyshev
  calc (1 : ℝ) ≤ Real.exp 0 := by simp
    _ ≤ Real.exp 5 := Real.exp_le_exp.mpr (by norm_num)

theorem constCChebyshev_le_exp5 : constCChebyshev ≤ Real.exp 5 := le_refl _

/-- Lemma 3.6 restated with the named constant. -/
theorem chebyshevT_le_constCChebyshev (d : ℕ) (hd : 2 ≤ d) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (d : ℝ) ^ 2) :
    (chebyshevT d).eval (1 / (1 - δ)) ≤ constCChebyshev :=
  chebyshevT_constant_c d hd δ hδ0 hδ

/-- Chebyshev growth at 1+ε is bounded by constCChebyshev when ε ≤ 1/d².
    Uses: 1+ε ≤ 1/(1-ε) (since (1+ε)(1-ε) = 1-ε² ≤ 1) and monotonicity of T_d. -/
theorem chebyshevT_one_plus_le_constCChebyshev (d : ℕ) (ε : ℝ)
    (hε_nn : 0 ≤ ε) (hε_le : ε ≤ 1 / (d : ℝ) ^ 2) :
    |(chebyshevT d).eval (1 + ε)| ≤ constCChebyshev := by
  -- T_d(1+ε) ≥ 0 since 1+ε ≥ 1
  have h1ε : 1 ≤ 1 + ε := le_add_of_nonneg_right hε_nn
  rw [abs_of_nonneg (chebyshevT_nonneg_ge_one d (1 + ε) h1ε)]
  -- Handle small d cases
  by_cases hd0 : d = 0
  · subst hd0; simp only [chebyshevT, eval_one, ge_iff_le]; exact one_le_constCChebyshev
  by_cases hd1 : d = 1
  · subst hd1
    simp [chebyshevT_one]
    -- T_1(1+ε) = 1+ε ≤ 2 ≤ constCChebyshev
    have hε1 : ε ≤ 1 := by linarith [hε_le, (show (1 : ℝ) ^ 2 = 1 by norm_num)]
    have hc2 : 2 ≤ constCChebyshev := by
      unfold constCChebyshev
      calc (2 : ℝ) ≤ Real.exp 1 := by
              have := Real.add_one_le_exp (1 : ℝ)
              linarith
        _ ≤ Real.exp 5 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  · -- d ≥ 2
    have hd2 : 2 ≤ d := by omega
    have hd1' : 1 ≤ d := by omega
    -- Need ε < 1 for 1/(1-ε) to be well-defined
    have hε_lt1 : ε < 1 := by
      have hd_sq_pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
      calc ε ≤ 1 / (d : ℝ) ^ 2 := hε_le
        _ ≤ 1 / (2 : ℝ) ^ 2 := by
          have : (2:ℝ)^2 ≤ (d:ℝ)^2 := by exact_mod_cast Nat.pow_le_pow_left (by omega) 2
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) this
        _ = 1 / 4 := by norm_num
        _ < 1 := by norm_num
    -- 1+ε ≤ 1/(1-ε) since (1+ε)(1-ε) = 1-ε² ≤ 1
    have h_le_inv : 1 + ε ≤ 1 / (1 - ε) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - ε)]
      nlinarith [sq_nonneg ε]
    -- By monotonicity: T_d(1+ε) ≤ T_d(1/(1-ε))
    calc (chebyshevT d).eval (1 + ε)
        ≤ (chebyshevT d).eval (1 / (1 - ε)) :=
          chebyshevT_monotone_ge_one d hd1' (1 + ε) (1 / (1 - ε)) h1ε h_le_inv
      _ ≤ constCChebyshev :=
          chebyshevT_le_constCChebyshev d hd2 ε hε_nn hε_le

/-! ## Additional useful bounds -/

/-- For x ≥ 1, x + √(x²-1) ≥ 1.
    Since x ≥ 1 and √(x²-1) ≥ 0, the sum is ≥ 1. -/
theorem one_le_x_add_sqrt (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ x + Real.sqrt (x ^ 2 - 1) := by
  have : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
  linarith

/-- The function x + √(x²-1) is monotone increasing for x ≥ 1. -/
theorem x_add_sqrt_mono (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    x + Real.sqrt (x ^ 2 - 1) ≤ y + Real.sqrt (y ^ 2 - 1) := by
  have hxsq : 0 ≤ x ^ 2 - 1 := sq_sub_one_nonneg_of_ge_one x hx
  have hysq : 0 ≤ y ^ 2 - 1 := sq_sub_one_nonneg_of_ge_one y (le_trans hx hxy)
  have hsqrt : Real.sqrt (x ^ 2 - 1) ≤ Real.sqrt (y ^ 2 - 1) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  linarith

/-- Combined bound for Lemma 3.5: both directions.
    For x ≥ 1 and d ≥ 1: 1 ≤ T_d(x) ≤ (x + √(x²-1))^d. -/
theorem chebyshevT_bounds_ge_one (d : ℕ) (x : ℝ) (hx : 1 ≤ x) (hd : 1 ≤ d) :
    1 ≤ (chebyshevT d).eval x ∧
    (chebyshevT d).eval x ≤ (x + Real.sqrt (x ^ 2 - 1)) ^ d :=
  ⟨chebyshevT_lower_bound_ge_one d x hx, chebyshevT_upper_bound d x hx hd⟩

/-! ## Polynomial evaluation monotonicity helpers -/

/-- If f is a polynomial with f.eval monotone on [a,∞) and a ≤ x ≤ y,
    then f.eval x ≤ f.eval y. This is just a specialization. -/
theorem eval_mono_of_monotone_on (p : Polynomial ℝ) (a : ℝ)
    (hmono : ∀ x y : ℝ, a ≤ x → x ≤ y → p.eval x ≤ p.eval y)
    (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) :
    p.eval x ≤ p.eval y :=
  hmono x y hax hxy

/-! ## Collecting derivative bounds into a combined statement -/

/-- Combined derivative bounds on [-1,1] for k = 0, 1, 2.
    - k=0: |T_d(x)| ≤ 1
    - k=1: |T_d'(x)| ≤ d²
    - k=2: |T_d''(x)| ≤ d⁴ -/
theorem chebyshevT_deriv_bounds (d : ℕ) (k : Fin 3) (x : ℝ)
    (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |Polynomial.eval x ((Polynomial.derivative^[k.val] (chebyshevT d)))| ≤
      (d : ℝ) ^ (2 * k.val) := by
  fin_cases k
  · -- k = 0
    simp only [Function.iterate_zero, id]
    exact chebyshevT_abs_le_one d x hx1 hx2
  · -- k = 1
    simp only [Function.iterate_one]
    exact chebyshevT_deriv_bound_k1 d x hx1 hx2
  · -- k = 2
    simp only [Function.iterate_succ,
      Function.comp, Nat.reduceMul]
    exact chebyshevT_deriv_bound_k2 d x hx1 hx2

end OptimalConvergenceRates
