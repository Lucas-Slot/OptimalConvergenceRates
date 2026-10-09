/-
  OptimalConvergenceRates/MarkovInequality/MarkovInequalityClassical.lean

  Classical univariate Markov inequalities, including higher derivatives by induction.
-/
import OptimalConvergenceRates.MarkovInequality.MarkovFirstDerivativeProof
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Polynomial

noncomputable section

namespace OptimalConvergenceRates

/-! ## Univariate Markov's inequality (classical result) -/

/-- Interior Markov brothers' inequality (Theorem 3.2, k=1, ‖x‖ ≤ 1):
    |p'(x)| ≤ d² · ‖p‖ for |x| ≤ 1. -/
theorem univariate_markov_first_derivative_inside
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.natDegree ≤ d)
    (x : ℝ) (hx : |x| ≤ 1) :
    |(Polynomial.derivative p).eval x| ≤ d ^ 2 * polySupNormUni p := by
  exact univariate_markov_first_derivative_inside_proof p d hdeg x hx

/-! ## General-order Markov inequality from the first-derivative theorem -/

/-- The sup-norm of p' on [-1,1] is at most d² times the sup-norm of p. -/
private theorem polySupNormUni_derivative_le (p : Polynomial ℝ) (d : ℕ)
    (hdeg : p.natDegree ≤ d) :
    polySupNormUni (Polynomial.derivative p) ≤ (d : ℝ) ^ 2 * polySupNormUni p := by
  apply polySupNormUni_le_of_bound
  intro x hx1 hx2
  exact univariate_markov_first_derivative_inside p d hdeg x (abs_le.mpr ⟨by linarith, hx2⟩)

/-- The analytic derivative of a polynomial evaluation function equals
    evaluation of the algebraic derivative. -/
private theorem deriv_poly_eval (p : Polynomial ℝ) :
    deriv p.eval = (Polynomial.derivative p).eval := by
  funext x
  have h := Polynomial.deriv_aeval (𝕜 := ℝ) p (x := x)
  simp only [Polynomial.coe_aeval_eq_eval] at h
  exact h

/-- Interior Markov brothers' inequality, general order (Theorem 3.2, all k):
    |p^(m)(x)| ≤ d^{2m} · ‖p‖ for |x| ≤ 1.
    This is a weak form; the sharp bound is ∏_{j=0}^{m-1} (d²−j²)/(2j+1) · ‖p‖.
    Reference: V.A. Markov 1892, "On functions deviating least from zero
    in a given interval." Also Cheney 1966, Theorem 5.1.3.
    Proved by induction on m from `univariate_markov_first_derivative_inside`. -/
theorem univariate_markov_general_inside
    (p : Polynomial ℝ) (d m : ℕ) (hdeg : p.natDegree ≤ d)
    (x : ℝ) (hx : |x| ≤ 1) :
    |iteratedDeriv m p.eval x| ≤ (d : ℝ) ^ (2 * m) * polySupNormUni p := by
  induction m generalizing p with
  | zero =>
    simp only [mul_zero, pow_zero, one_mul, iteratedDeriv_zero]
    exact polySupNormUni_eval_le p x (by linarith [(abs_le.mp hx).1]) (abs_le.mp hx).2
  | succ m ih =>
    have hstep : iteratedDeriv (m + 1) p.eval = iteratedDeriv m (Polynomial.derivative p).eval := by
      rw [iteratedDeriv_succ', deriv_poly_eval]
    simp only [hstep]
    have hdeg' : (Polynomial.derivative p).natDegree ≤ d :=
      (Polynomial.natDegree_derivative_le p).trans ((Nat.sub_le _ _).trans hdeg)
    calc |iteratedDeriv m (Polynomial.derivative p).eval x|
        ≤ (d : ℝ) ^ (2 * m) * polySupNormUni (Polynomial.derivative p) := ih _ hdeg'
      _ ≤ (d : ℝ) ^ (2 * m) * ((d : ℝ) ^ 2 * polySupNormUni p) :=
          mul_le_mul_of_nonneg_left (polySupNormUni_derivative_le p d hdeg) (by positivity)
      _ = (d : ℝ) ^ (2 * (m + 1)) * polySupNormUni p := by ring

/-! ## Corollary: weak second-derivative bound from general theorem -/

/-- Weak interior Markov bound for the second derivative (from general theorem at m=2):
    |p''(x)| ≤ d⁴ · ‖p‖ for |x| ≤ 1. -/
theorem univariate_markov_second_derivative_weak
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.natDegree ≤ d)
    (x : ℝ) (hx : |x| ≤ 1) :
    |(Polynomial.derivative (Polynomial.derivative p)).eval x| ≤
      (d : ℝ) ^ 4 * polySupNormUni p := by
  have h := univariate_markov_general_inside p d 2 hdeg x hx
  rw [show 2 * 2 = 4 from rfl] at h
  -- Connect iteratedDeriv 2 to double algebraic derivative
  have key : iteratedDeriv 2 p.eval = (Polynomial.derivative (Polynomial.derivative p)).eval := by
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', deriv_poly_eval,
        iteratedDeriv_one, deriv_poly_eval]
  rwa [key] at h

end OptimalConvergenceRates

end
