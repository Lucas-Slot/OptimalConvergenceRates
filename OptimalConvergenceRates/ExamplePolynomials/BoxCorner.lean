/-
  OptimalConvergenceRates/ExamplePolynomials/BoxCorner.lean

  The two-variable corner polynomial (1 - x^2)(1 - y^2) + epsilon and its box identities.
-/
import OptimalConvergenceRates.BasicNotions.BoxCones

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-! ## The polynomial f_ε(x,y) = (1-x²)(1-y²) + ε -/

/-- The two-variable polynomial f_ε(x,y) = (1-x²)(1-y²) + ε over B² = [-1,1]².
    This is the key test polynomial: it is nonneg on B² for ε ≥ 0,
    but lies in QM(B²)_r only for r ≥ Ω(ε^{-1/8}). -/
def f_eps (ε : ℝ) : MvPolynomial (Fin 2) ℝ :=
  (1 - (X 0) ^ 2) * (1 - (X 1) ^ 2) + MvPolynomial.C ε

/-- f_ε evaluated at (x,y) gives (1-x²)(1-y²) + ε. -/
theorem f_eps_eval (ε : ℝ) (v : Fin 2 → ℝ) :
    MvPolynomial.eval v (f_eps ε) = (1 - v 0 ^ 2) * (1 - v 1 ^ 2) + ε := by
  simp [f_eps, map_add, map_mul, map_sub, map_one, map_pow, eval_X, MvPolynomial.eval_C]

/-- f_ε is nonneg on B² when ε ≥ 0. -/
theorem f_eps_nonneg_on_hypercube (ε : ℝ) (hε : 0 ≤ ε) (v : Fin 2 → ℝ)
    (hv : v ∈ Hypercube 2) :
    0 ≤ MvPolynomial.eval v (f_eps ε) := by
  rw [f_eps_eval]
  have h0 := (Hypercube_mem_iff v).mp hv 0
  have h1 := (Hypercube_mem_iff v).mp hv 1
  have hx : 0 ≤ 1 - v 0 ^ 2 := by nlinarith [h0.1, h0.2, sq_abs (v 0)]
  have hy : 0 ≤ 1 - v 1 ^ 2 := by nlinarith [h1.1, h1.2, sq_abs (v 1)]
  linarith [mul_nonneg hx hy]

/-- f_ε is strictly positive on B² when ε > 0. -/
theorem f_eps_pos_on_hypercube (ε : ℝ) (hε : 0 < ε) (v : Fin 2 → ℝ)
    (hv : v ∈ Hypercube 2) :
    0 < MvPolynomial.eval v (f_eps ε) := by
  rw [f_eps_eval]
  have h0 := (Hypercube_mem_iff v).mp hv 0
  have h1 := (Hypercube_mem_iff v).mp hv 1
  have hx : 0 ≤ 1 - v 0 ^ 2 := by nlinarith [h0.1, h0.2, sq_abs (v 0)]
  have hy : 0 ≤ 1 - v 1 ^ 2 := by nlinarith [h1.1, h1.2, sq_abs (v 1)]
  linarith [mul_nonneg hx hy]

/-- f_0(x,y) = (1-x²)(1-y²), the "zero epsilon" case. -/
def f_zero : MvPolynomial (Fin 2) ℝ :=
  (1 - (X 0) ^ 2) * (1 - (X 1) ^ 2)

theorem f_zero_eq : f_zero = f_eps 0 := by
  simp [f_zero, f_eps, map_zero]

theorem f_zero_eval (v : Fin 2 → ℝ) :
    MvPolynomial.eval v f_zero = (1 - v 0 ^ 2) * (1 - v 1 ^ 2) := by
  simp [f_zero, map_mul, map_sub, map_one, map_pow, eval_X]

/-! ## f_ε = g₁·g₂ + ε, relating to generators -/

/-- f_ε decomposes as g₁·g₂ + ε where g_i = BoxSemialgebraicGenerator i. -/
theorem f_eps_eq_gen_prod_add (ε : ℝ) :
    f_eps ε = BoxSemialgebraicGenerator (0 : Fin 2) * BoxSemialgebraicGenerator (1 : Fin 2)
              + MvPolynomial.C ε := by
  simp [f_eps, BoxSemialgebraicGenerator]

/-- The corner point (1,1) ∈ B². -/
def corner_11 : Fin 2 → ℝ := ![1, 1]

theorem corner_11_in_hypercube : corner_11 ∈ Hypercube 2 := by
  rw [Hypercube_mem_iff]; intro i; fin_cases i <;> simp [corner_11, Matrix.cons_val_zero,
    Matrix.cons_val_one]

theorem corner_11_val_0 : corner_11 0 = 1 := by simp [corner_11, Matrix.cons_val_zero]
theorem corner_11_val_1 : corner_11 1 = 1 := by
  simp [corner_11, Matrix.cons_val_one]

/-- At the corner (1,1), f_ε evaluates to ε. -/
theorem f_eps_eval_corner (ε : ℝ) :
    MvPolynomial.eval corner_11 (f_eps ε) = ε := by
  rw [f_eps_eval]; simp [corner_11_val_0, corner_11_val_1]


end OptimalConvergenceRates

end
