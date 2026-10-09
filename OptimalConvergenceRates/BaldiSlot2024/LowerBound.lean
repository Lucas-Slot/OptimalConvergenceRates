/-
  OptimalConvergenceRates/BaldiSlot2024/LowerBound.lean

  Baldi-Slot 2024 Putinar lower degree bound for the two-variable corner polynomial.
-/
import OptimalConvergenceRates.BasicNotions.SumsOfSquares
import OptimalConvergenceRates.BaldiSlot2024.BoxQuadraticModuleTwoVariable
import OptimalConvergenceRates.Chebyshev.ChebyshevGrowth
import OptimalConvergenceRates.BaldiSlot2024.Defs
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityCorollaries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-! ## Evaluation constraints at boundary points

Key observations:
- At (1, y): g₁ = 1 - 1 = 0, so σ₁·g₁ vanishes.
- At (x, 1): g₂ = 1 - 1 = 0, so σ₂·g₂ vanishes.
- At (1, 1): both σ₁·g₁ and σ₂·g₂ vanish, so σ₀(1,1) = f_ε(1,1) = ε.
-/

/-- BoxSemialgebraicGenerator 0 vanishes at x₀ = 1. -/
theorem gen0_vanishes_at_one (v : Fin 2 → ℝ) (hv0 : v 0 = 1) :
    MvPolynomial.eval v (BoxSemialgebraicGenerator (0 : Fin 2)) = 0 := by
  rw [BoxSemialgebraicGenerator_eval]; simp [hv0]

/-- BoxSemialgebraicGenerator 1 vanishes at x₁ = 1. -/
theorem gen1_vanishes_at_one (v : Fin 2 → ℝ) (hv1 : v 1 = 1) :
    MvPolynomial.eval v (BoxSemialgebraicGenerator (1 : Fin 2)) = 0 := by
  rw [BoxSemialgebraicGenerator_eval]; simp [hv1]

/-- BoxSemialgebraicGenerator 0 vanishes at x₀ = -1. -/
theorem gen0_vanishes_at_neg_one (v : Fin 2 → ℝ) (hv0 : v 0 = -1) :
    MvPolynomial.eval v (BoxSemialgebraicGenerator (0 : Fin 2)) = 0 := by
  rw [BoxSemialgebraicGenerator_eval]; simp [hv0]

/-- BoxSemialgebraicGenerator 1 vanishes at x₁ = -1. -/
theorem gen1_vanishes_at_neg_one (v : Fin 2 → ℝ) (hv1 : v 1 = -1) :
    MvPolynomial.eval v (BoxSemialgebraicGenerator (1 : Fin 2)) = 0 := by
  rw [BoxSemialgebraicGenerator_eval]; simp [hv1]

/-! ## ArXiv v3, Proposition 29: qualitative non-membership in QM(B²)

The proof is by contradiction. If f_zero ∈ QM(B²)_r for some r, then
  f_zero = σ₀ + σ₁·(1-x²) + σ₂·(1-y²)
Evaluating at (1,1):
  f_zero(1,1) = 0 = σ₀(1,1) + σ₁(1,1)·0 + σ₂(1,1)·0 = σ₀(1,1)
So σ₀(1,1) = 0. Since σ₀ is SOS and nonneg, σ₀(1,1) = 0 means σ₀ vanishes at (1,1).
Examining second derivatives at (1,1) yields that σ₁(1,y) = 1-y²
which is not nonneg everywhere -- contradiction since σ₁ is SOS.
-/

/-- If an SOS polynomial evaluates to 0 at a point, each square summand also evaluates to 0. -/
private theorem IsSOS_eval_zero_implies (p : MvPolynomial (Fin 2) ℝ) (_hp : IsSOS p)
    (v : Fin 2 → ℝ) (hv : MvPolynomial.eval v p = 0) :
    ∀ (m : ℕ) (q : Fin m → MvPolynomial (Fin 2) ℝ),
    p = ∑ i : Fin m, (q i) ^ 2 → ∀ i, MvPolynomial.eval v (q i) = 0 := by
  intro m q hpq i
  have heval : ∑ j : Fin m, (MvPolynomial.eval v (q j)) ^ 2 = 0 := by
    rw [← hv, hpq, map_sum]; simp [map_pow]
  have := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (MvPolynomial.eval v (q j)))
    |>.mp heval i (Finset.mem_univ i)
  exact pow_eq_zero_iff (n := 2) (by omega) |>.mp this

/-- If p = Σ q_i² and each q_i(v) = 0, then the partial derivative (pderiv j p)(v) = 0.
    This is because pderiv j (q_i²) = 2 * q_i * pderiv j q_i, and q_i(v) = 0. -/
private theorem pderiv_SOS_eval_zero
    (p : MvPolynomial (Fin 2) ℝ) (m : ℕ) (q : Fin m → MvPolynomial (Fin 2) ℝ)
    (hpq : p = ∑ i : Fin m, (q i) ^ 2)
    (v : Fin 2 → ℝ) (hq_van : ∀ i, MvPolynomial.eval v (q i) = 0)
    (j : Fin 2) :
    MvPolynomial.eval v (MvPolynomial.pderiv j p) = 0 := by
  -- pderiv j (Σ q_i²) = Σ 2 * q_i * pderiv j q_i  (by linearity + power rule)
  -- eval at v: Σ 2 * q_i(v) * (pderiv j q_i)(v) = Σ 0 = 0  (since q_i(v) = 0)
  have key : ∀ i : Fin m, MvPolynomial.eval v (MvPolynomial.pderiv j ((q i) ^ 2)) = 0 := by
    intro i
    rw [pderiv_pow, pow_one]
    -- Now goal: eval v (↑2 * q i * pderiv j (q i)) = 0
    simp only [map_mul]
    -- Now: eval v ↑2 * eval v (q i) * eval v (pderiv j (q i)) = 0
    rw [hq_van i, mul_zero, zero_mul]
  subst hpq
  simp only [map_sum]
  exact Finset.sum_eq_zero (fun i _ => key i)

/-- Restrict a bivariate polynomial to x = a, yielding a univariate polynomial in y.
    Uses MvPolynomial.aeval to substitute X 0 ↦ C a, X 1 ↦ X. -/
private noncomputable def restrictX0 (a : ℝ) (p : MvPolynomial (Fin 2) ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then Polynomial.C a else Polynomial.X) p

/-- Evaluating the restriction agrees with evaluating the bivariate polynomial. -/
private theorem restrictX0_eval (a : ℝ) (p : MvPolynomial (Fin 2) ℝ) (y : ℝ) :
    (restrictX0 a p).eval y = MvPolynomial.eval (![a, y]) p := by
  unfold restrictX0
  -- Use induction on the MvPolynomial
  apply MvPolynomial.induction_on p
  · -- p = C c
    intro c
    simp [MvPolynomial.eval_C]
  · -- p = p₁ + p₂
    intro p₁ p₂ ih₁ ih₂
    simp only [map_add, Polynomial.eval_add]
    rw [ih₁, ih₂]
  · -- p = p₁ * X i
    intro p₁ i ih₁
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_mul]
    rw [ih₁]
    congr 1
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Restrict a bivariate polynomial to y = b, yielding a univariate polynomial in x. -/
private noncomputable def restrictX1 (b : ℝ) (p : MvPolynomial (Fin 2) ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 1 then Polynomial.C b else Polynomial.X) p

/-- Evaluating the y-restriction agrees with evaluating the bivariate polynomial. -/
private theorem restrictX1_eval (b : ℝ) (p : MvPolynomial (Fin 2) ℝ) (x : ℝ) :
    (restrictX1 b p).eval x = MvPolynomial.eval (![x, b]) p := by
  unfold restrictX1
  apply MvPolynomial.induction_on p
  · intro c; simp [MvPolynomial.eval_C]
  · intro p₁ p₂ ih₁ ih₂; simp only [map_add, Polynomial.eval_add]; rw [ih₁, ih₂]
  · intro p₁ i ih₁
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_mul]
    rw [ih₁]; congr 1
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- If an SOS bivariate polynomial vanishes on (-1,1) × {b}, it vanishes on ℝ × {b}. -/
private theorem IsSOS_vanishing_on_line_y
    (p : MvPolynomial (Fin 2) ℝ) (hp : IsSOS p) (b : ℝ)
    (hvan : ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → MvPolynomial.eval (![x, b]) p = 0) :
    ∀ x : ℝ, MvPolynomial.eval (![x, b]) p = 0 := by
  obtain ⟨m, q, hpq⟩ := hp
  intro x
  have hqi_van : ∀ i : Fin m, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      MvPolynomial.eval (![t, b]) (q i) = 0 := by
    intro i t ht
    have heval := hvan t ht
    rw [hpq, map_sum] at heval; simp only [map_pow] at heval
    have := Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      sq_nonneg (MvPolynomial.eval (![t, b]) (q j))) |>.mp heval i (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by omega) |>.mp this
  have hqi_zero : ∀ i : Fin m, restrictX1 b (q i) = 0 := by
    intro i
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).mono
    intro t ht
    change Polynomial.IsRoot (restrictX1 b (q i)) t
    rw [Polynomial.IsRoot, restrictX1_eval]
    exact hqi_van i t ht
  have heval_zero : ∀ i : Fin m, MvPolynomial.eval (![x, b]) (q i) = 0 := by
    intro i; rw [← restrictX1_eval, hqi_zero i, Polynomial.eval_zero]
  rw [hpq, map_sum]; simp only [map_pow]
  apply Finset.sum_eq_zero
  intro i _; rw [heval_zero i]; ring

/-- If an SOS bivariate polynomial vanishes on {a} × (-1,1), it vanishes on {a} × ℝ.
    Proof: restrict to x = a to get a univariate SOS polynomial.
    Each square summand vanishes on (-1,1) (infinite set), hence is the zero polynomial. -/
private theorem IsSOS_vanishing_on_line
    (p : MvPolynomial (Fin 2) ℝ) (hp : IsSOS p) (a : ℝ)
    (hvan : ∀ y : ℝ, y ∈ Set.Ioo (-1 : ℝ) 1 → MvPolynomial.eval (![a, y]) p = 0) :
    ∀ y : ℝ, MvPolynomial.eval (![a, y]) p = 0 := by
  -- The restriction p_r = restrictX0 a p is a univariate SOS polynomial
  -- vanishing on (-1,1). Each square summand vanishes on (-1,1), hence is zero.
  obtain ⟨m, q, hpq⟩ := hp
  intro y
  -- Each q_i(a, ·) vanishes on (-1,1)
  have hqi_van : ∀ i : Fin m, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      MvPolynomial.eval (![a, t]) (q i) = 0 := by
    intro i t ht
    have heval := hvan t ht
    rw [hpq, map_sum] at heval; simp only [map_pow] at heval
    have := Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      sq_nonneg (MvPolynomial.eval (![a, t]) (q j))) |>.mp heval i (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by omega) |>.mp this
  -- Each restrictX0 a (q i) is a univariate polynomial vanishing on (-1,1)
  have hqi_zero : ∀ i : Fin m, restrictX0 a (q i) = 0 := by
    intro i
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).mono
    intro t ht
    change Polynomial.IsRoot (restrictX0 a (q i)) t
    rw [Polynomial.IsRoot, restrictX0_eval]
    exact hqi_van i t ht
  -- Hence p(a,y) = Σ (q_i(a,y))² = 0 for all y
  have heval_zero : ∀ i : Fin m, MvPolynomial.eval (![a, y]) (q i) = 0 := by
    intro i
    rw [← restrictX0_eval, hqi_zero i, Polynomial.eval_zero]
  rw [hpq, map_sum]; simp only [map_pow]
  apply Finset.sum_eq_zero
  intro i _
  rw [heval_zero i]; ring

/-- Key algebraic fact: if σ₁ is SOS and σ₁(x,1) = 0 for all x, and the polynomial identity
    (1-x²)(1-y²) = σ₀ + σ₁(1-x²) + σ₂(1-y²) holds, then σ₁(1,y) = 1-y² for all y.
    Since σ₁ is SOS (hence nonneg everywhere), evaluating at y=2 gives 1-4 = -3 < 0,
    contradiction. -/
theorem f_not_in_quadratic_module (r : ℕ) :
    f_zero ∉ BoxQuadraticModule 2 r := by
  intro ⟨σ₀, σ, hsos₀, hsos, _, _, hsum⟩
  -- Step 1: Evaluate the polynomial identity at specific points
  -- At (1,y): f_zero(1,y) = 0, g₁(1,y) = 0, so 0 = σ₀(1,y) + σ(1)(1,y)·(1-y²)
  have heval_1y : ∀ y : ℝ, MvPolynomial.eval (![1, y]) σ₀ +
      MvPolynomial.eval (![1, y]) (σ 1) * (1 - y ^ 2) = 0 := by
    intro y
    have hid := congr_arg (MvPolynomial.eval (![1, y])) hsum
    simp only [f_zero, map_add, map_mul, map_sub, map_one, map_pow, eval_X,
      Fin.sum_univ_two, BoxSemialgebraicGenerator_eval] at hid
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] at hid
    linarith
  -- Step 2: For y ∈ (-1,1), both σ₀(1,y) ≥ 0 and σ(1)(1,y)·(1-y²) ≥ 0,
  -- and their sum is 0, so both are 0.
  have hσ₀_1y : ∀ y : ℝ, y ∈ Set.Ioo (-1 : ℝ) 1 →
      MvPolynomial.eval (![1, y]) σ₀ = 0 := by
    intro y hy
    have h_sum := heval_1y y
    have h_nonneg₀ : 0 ≤ MvPolynomial.eval (![1, y]) σ₀ :=
      IsSOS_nonneg σ₀ hsos₀ _ (Set.mem_univ _)
    have h_nonneg₁ : 0 ≤ MvPolynomial.eval (![1, y]) (σ 1) :=
      IsSOS_nonneg (σ 1) (hsos 1) _ (Set.mem_univ _)
    have h1y : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2, sq_abs y]
    nlinarith [mul_nonneg h_nonneg₁ h1y.le]
  -- Step 3: σ₀(1,·) is a polynomial in y vanishing on (-1,1),
  -- hence it's the zero polynomial, so σ₀(1,y) = 0 for all y.
  -- (A nonzero polynomial has finitely many roots, but (-1,1) is infinite.)
  -- This step requires the algebraic fact about polynomial zero sets.
  have hσ₀_1y_all : ∀ y : ℝ, MvPolynomial.eval (![1, y]) σ₀ = 0 :=
    IsSOS_vanishing_on_line σ₀ hsos₀ 1 hσ₀_1y
  -- Step 4: σ(1)(1,y) = 0 for y ∈ (-1,1).
  have hσ1_1y : ∀ y : ℝ, y ∈ Set.Ioo (-1 : ℝ) 1 →
      MvPolynomial.eval (![1, y]) (σ 1) = 0 := by
    intro y hy
    have h_sum := heval_1y y
    have h_σ₀ := hσ₀_1y_all y
    have h_nonneg₁ : 0 ≤ MvPolynomial.eval (![1, y]) (σ 1) :=
      IsSOS_nonneg (σ 1) (hsos 1) _ (Set.mem_univ _)
    have h1y : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2, sq_abs y]
    nlinarith [mul_nonneg h_nonneg₁ h1y.le]
  have hσ1_1y_all : ∀ y : ℝ, MvPolynomial.eval (![1, y]) (σ 1) = 0 :=
    IsSOS_vanishing_on_line (σ 1) (hsos 1) 1 hσ1_1y
  -- Step 5: At (x,1): f_zero(x,1) = 0, g₂(x,1) = 0, so 0 = σ₀(x,1) + σ(0)(x,1)·(1-x²)
  have heval_x1 : ∀ x : ℝ, MvPolynomial.eval (![x, 1]) σ₀ +
      MvPolynomial.eval (![x, 1]) (σ 0) * (1 - x ^ 2) = 0 := by
    intro x
    have hid := congr_arg (MvPolynomial.eval (![x, 1])) hsum
    simp only [f_zero, map_add, map_mul, map_sub, map_one, map_pow, eval_X,
      Fin.sum_univ_two, BoxSemialgebraicGenerator_eval] at hid
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] at hid
    linarith
  -- Step 6: σ₀(x,1) = 0 for all x
  have hσ₀_x1 : ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
      MvPolynomial.eval (![x, 1]) σ₀ = 0 := by
    intro x hx
    have h_sum := heval_x1 x
    have h_nonneg₀ : 0 ≤ MvPolynomial.eval (![x, 1]) σ₀ :=
      IsSOS_nonneg σ₀ hsos₀ _ (Set.mem_univ _)
    have h_nonneg₀' : 0 ≤ MvPolynomial.eval (![x, 1]) (σ 0) :=
      IsSOS_nonneg (σ 0) (hsos 0) _ (Set.mem_univ _)
    have h1x : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_abs x]
    nlinarith [mul_nonneg h_nonneg₀' h1x.le]
  have hσ₀_x1_all : ∀ x : ℝ, MvPolynomial.eval (![x, 1]) σ₀ = 0 :=
    IsSOS_vanishing_on_line_y σ₀ hsos₀ 1 hσ₀_x1
  -- Step 7: σ(0)(x,1) = 0 for x ∈ (-1,1), hence for all x.
  have hσ0_x1 : ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 →
      MvPolynomial.eval (![x, 1]) (σ 0) = 0 := by
    intro x hx
    have h_sum := heval_x1 x
    have h_σ₀ := hσ₀_x1_all x
    have h_nonneg₀ : 0 ≤ MvPolynomial.eval (![x, 1]) (σ 0) :=
      IsSOS_nonneg (σ 0) (hsos 0) _ (Set.mem_univ _)
    have h1x : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_abs x]
    nlinarith [mul_nonneg h_nonneg₀ h1x.le]
  have hσ0_x1_all : ∀ x : ℝ, MvPolynomial.eval (![x, 1]) (σ 0) = 0 :=
    IsSOS_vanishing_on_line_y (σ 0) (hsos 0) 1 hσ0_x1
  -- Differentiate the decomposition w.r.t. X₀ at (1,y).
  -- Since σ₀(1,y)=0 and g₀(1,y)=0, only σ₁·g₁ contributes: σ₁(1,y) = 1-y².
  have hσ1_eq : ∀ y : ℝ, MvPolynomial.eval (![1, y]) (σ 0) = 1 - y ^ 2 := by
    intro y
    -- Differentiate hsum w.r.t. X 0
    have hderiv := congr_arg (MvPolynomial.pderiv (0 : Fin 2)) hsum
    -- Evaluate at ![1, y]
    have heval_deriv := congr_arg (MvPolynomial.eval (![1, y])) hderiv
    -- Auxiliary evaluation facts
    -- Evaluate g₀(1,y) = 0
    have hg0_eval : MvPolynomial.eval (![1, y]) (BoxSemialgebraicGenerator (0 : Fin 2)) = 0 := by
      rw [BoxSemialgebraicGenerator_eval]; simp [Matrix.cons_val_zero]
    -- Evaluate g₁(1,y) = 1 - y²
    have hg1_eval : MvPolynomial.eval (![1, y])
        (BoxSemialgebraicGenerator (1 : Fin 2)) = 1 - y ^ 2 := by
      rw [BoxSemialgebraicGenerator_eval]; simp [Matrix.cons_val_one]
    -- Evaluate pderiv 0 g₀ at (1,y): pderiv 0 (1 - X₀²) = -2X₀, at (1,y) = -2
    have hpderiv_g0 : MvPolynomial.eval (![1, y])
        (MvPolynomial.pderiv (0 : Fin 2) (BoxSemialgebraicGenerator (0 : Fin 2))) = -2 := by
      simp [BoxSemialgebraicGenerator, map_sub,
        map_mul, eval_X, Matrix.cons_val_zero, mul_comm]
    -- pderiv 0 g₁ = 0 (g₁ = 1 - X₁² has no X₀)
    have hpderiv_g1 :
        MvPolynomial.pderiv (0 : Fin 2) (BoxSemialgebraicGenerator (1 : Fin 2)) = 0 := by
      simp [BoxSemialgebraicGenerator, map_sub, mul_zero,
        pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 from by decide)]
    -- pderiv 0 (σ₀) at (1,y) = 0 (SOS with each summand vanishing at (1,y))
    have hpderiv_σ₀ : MvPolynomial.eval (![1, y])
        (MvPolynomial.pderiv (0 : Fin 2) σ₀) = 0 := by
      obtain ⟨m₀, q₀, hσ₀_eq⟩ := hsos₀
      exact pderiv_SOS_eval_zero σ₀ m₀ q₀ hσ₀_eq (![1, y])
        (fun i =>
          IsSOS_eval_zero_implies σ₀ ⟨m₀, q₀, hσ₀_eq⟩ (![1, y])
            (hσ₀_1y_all y) m₀ q₀ hσ₀_eq i) 0
    -- pderiv 0 (σ 1) at (1,y) = 0
    have hpderiv_σ1 : MvPolynomial.eval (![1, y])
        (MvPolynomial.pderiv (0 : Fin 2) (σ 1)) = 0 := by
      obtain ⟨m₁, q₁, hσ1_decomp⟩ := hsos 1
      exact pderiv_SOS_eval_zero (σ 1) m₁ q₁ hσ1_decomp (![1, y])
        (fun i =>
          IsSOS_eval_zero_implies (σ 1) ⟨m₁, q₁, hσ1_decomp⟩ (![1, y])
            (hσ1_1y_all y) m₁ q₁ hσ1_decomp i) 0
    -- LHS: pderiv 0 f_zero at (1,y) = -2(1-y²)
    have hf_eq : f_zero = BoxSemialgebraicGenerator (0 : Fin 2) *
        BoxSemialgebraicGenerator (1 : Fin 2) := by
      simp [f_zero, BoxSemialgebraicGenerator]
    have hLHS : MvPolynomial.eval (![1, y])
        (MvPolynomial.pderiv (0 : Fin 2) f_zero) = -2 * (1 - y ^ 2) := by
      rw [hf_eq, pderiv_mul, hpderiv_g1, mul_zero, add_zero]
      simp only [MvPolynomial.eval_mul]
      rw [hpderiv_g0, hg1_eval]
    -- Product-rule terms at (1,y)
    have hterm0 : MvPolynomial.eval (![1, y])
        (MvPolynomial.pderiv (0 : Fin 2) (σ 0 * BoxSemialgebraicGenerator (0 : Fin 2))) =
        -2 * MvPolynomial.eval (![1, y]) (σ 0) := by
      rw [pderiv_mul]
      simp only [map_add, map_mul]
      rw [hg0_eval, hpderiv_g0]; ring
    have hterm1 : MvPolynomial.eval (![1, y])
        (MvPolynomial.pderiv (0 : Fin 2) (σ 1 * BoxSemialgebraicGenerator (1 : Fin 2))) = 0 := by
      rw [pderiv_mul, hpderiv_g1, mul_zero, add_zero]
      simp only [MvPolynomial.eval_mul]
      rw [hpderiv_σ1, zero_mul]
    -- And eval (pderiv 0 f_zero) at (1,y) = -2(1-y²)  (from hLHS)
    have hRHS : MvPolynomial.eval (![1, y])
        (MvPolynomial.pderiv (0 : Fin 2)
          (σ₀ + ∑ i : Fin 2, σ i * BoxSemialgebraicGenerator i)) =
        -2 * MvPolynomial.eval (![1, y]) (σ 0) := by
      -- Expand the sum over Fin 2
      rw [Fin.sum_univ_two]
      -- Distribute pderiv through + (three times)
      simp only [map_add]
      -- Now goal involves eval of sum of pderiv terms
      -- Substitute known values
      rw [hpderiv_σ₀, hterm0, hterm1]; ring
    -- From the identity: LHS = RHS
    rw [hLHS] at heval_deriv
    rw [hRHS] at heval_deriv
    linarith
  -- Contradiction: σ 0 is SOS hence nonneg, but σ 0 (1,2) = 1 - 4 = -3 < 0.
  have h_neg := hσ1_eq 2
  have h_nonneg := IsSOS_nonneg (σ 0) (hsos 0) (![1, 2]) (Set.mem_univ _)
  simp at h_neg h_nonneg
  linarith

/-! ## The diagonal restriction

For the quantitative bound, assume `f_eps ε ∈ QM(B²)_r` and analyze `σ₁` in the
decomposition `f_eps ε = σ₀ + σ₁ * (1 - x²) + σ₂ * (1 - y²)` along the diagonal
path through the corner `(1,1)`.

Define the diagonal path γ(t) = (1+t, 1-t) through the corner (1,1).
Along this path:
  g₁(γ(t)) = 1 - (1+t)² = -t² - 2t
  g₂(γ(t)) = 1 - (1-t)² = 2t - t²
  f_ε(γ(t)) = g₁ · g₂ + ε = (-t²-2t)(2t-t²) + ε = t²(t²-4) + ε

The key restriction is g(t) = σ₁(1+t, 1-t), which is a univariate polynomial
of degree ≤ deg(σ₁).
-/

/-- The diagonal path γ(t) = (1+t, 1-t) through corner (1,1). -/
def diagonal_path (t : ℝ) : Fin 2 → ℝ := ![1 + t, 1 - t]

theorem diagonal_path_zero : diagonal_path 0 = corner_11 := by
  ext i; fin_cases i <;> simp [diagonal_path, corner_11, Matrix.cons_val_zero,
    Matrix.cons_val_one]

theorem diagonal_path_val_0 (t : ℝ) : diagonal_path t 0 = 1 + t := by
  simp [diagonal_path, Matrix.cons_val_zero]

theorem diagonal_path_val_1 (t : ℝ) : diagonal_path t 1 = 1 - t := by
  simp [diagonal_path, Matrix.cons_val_one]

/-- The generator g₁ along the diagonal: g₁(1+t, 1-t) = -t² - 2t. -/
theorem gen0_on_diagonal (t : ℝ) :
    MvPolynomial.eval (diagonal_path t) (BoxSemialgebraicGenerator (0 : Fin 2))
    = -t ^ 2 - 2 * t := by
  rw [BoxSemialgebraicGenerator_eval, diagonal_path_val_0]; ring

/-- The generator g₂ along the diagonal: g₂(1+t, 1-t) = 2t - t². -/
theorem gen1_on_diagonal (t : ℝ) :
    MvPolynomial.eval (diagonal_path t) (BoxSemialgebraicGenerator (1 : Fin 2))
    = 2 * t - t ^ 2 := by
  rw [BoxSemialgebraicGenerator_eval, diagonal_path_val_1]; ring

/-- f_ε along the diagonal: f_ε(1+t, 1-t) = t²(t²-4) + ε. -/
theorem f_eps_on_diagonal (ε : ℝ) (t : ℝ) :
    MvPolynomial.eval (diagonal_path t) (f_eps ε)
    = t ^ 2 * (t ^ 2 - 4) + ε := by
  rw [f_eps_eval, diagonal_path_val_0, diagonal_path_val_1]; ring

/-! ## The univariate restriction of σ₁

Given the QM decomposition f_ε = σ₀ + σ₁·g₁ + σ₂·g₂, define
  g(t) := σ₁(1+t, 1-t)
as a (continuous, polynomial) function ℝ → ℝ.

Key properties that g inherits:
- g is nonneg everywhere (since σ₁ is SOS)
- g(0) = σ₁(1,1)
-/

/-- The univariate restriction of a bivariate polynomial along the diagonal.
    For p : MvPolynomial (Fin 2) ℝ, define p_diag(t) := eval (1+t, 1-t) p. -/
def diagRestriction (p : MvPolynomial (Fin 2) ℝ) : ℝ → ℝ :=
  fun t => MvPolynomial.eval (diagonal_path t) p

theorem diagRestriction_eval (p : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    diagRestriction p t = MvPolynomial.eval (diagonal_path t) p := rfl

theorem diagRestriction_zero (p : MvPolynomial (Fin 2) ℝ) :
    diagRestriction p 0 = MvPolynomial.eval corner_11 p := by
  simp [diagRestriction, diagonal_path_zero]

/-! ## Fact 2: sup-norm of σ₁ on [-1,1]² via Chebyshev growth

Since σ₁ is SOS (hence nonneg), its sup-norm on [-1,1]² can be bounded
using the Chebyshev growth estimate: for a nonneg polynomial of degree d
on [-1,1], its value at a point x with |x| > 1 is at most
T_d(|x|)² times its sup on [-1,1].

For σ₁ restricted to the diagonal, g(t) = σ₁(1+t, 1-t) is a polynomial
of degree ≤ r on a scaled interval. The Chebyshev bound gives:
  max_{[-1,1]²} σ₁ ≤ T_r(1/(1-δ)) · max_{[-δ,δ]} g
for suitable δ.
-/

/-- Fact 2 (from Section 5, Chebyshev growth bound):
    max_{[-1,1]²} σ₁ ≤ T_r(1/(1-δ)) · (2 / δ).

    This follows from the reverse Chebyshev growth inequality for general
    polynomials combined with the bound σ₁(x) ≤ f_ε(x)/g₁(x) ≤ 2/δ on (1-δ)·B².

    From the decomposition f_ε = σ₀ + σ₁·g₁ + σ₂·g₂:
    - On (1-δ)·B², g₁(x) = 1-x₀² ≥ 1-(1-δ)² = δ(2-δ) ≥ δ
    - σ₁(x)·g₁(x) ≤ f_ε(x) ≤ 1+ε ≤ 2 (on B²)
    - So σ₁(x) ≤ 2/(δ(2-δ)) ≤ 2/δ on (1-δ)·B²
    - By Chebyshev growth: polySupNorm σ₁ ≤ |T_r(1/(1-δ))| · polySupNormScaled σ₁ (1-δ)
    - polySupNormScaled σ₁ (1-δ) ≤ 2/δ -/
theorem fact2_sigma1_sup (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdeg₁ : σ₁.totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1) :
    polySupNorm σ₁ ≤ (Polynomial.eval (1 / (1 - δ)) (chebyshevT r))
                      * (2 / δ) := by
  -- Step 1: Apply reverse Chebyshev growth for general polynomials
  have h1mδ : 0 < 1 - δ := by linarith
  have hBM := markov_scaled_reverse_delta σ₁ r hdeg₁ δ hδ hδ1
  -- |T_r(1/(1-δ))| = T_r(1/(1-δ)) since 1/(1-δ) ≥ 1
  have hs : 1 ≤ 1 / (1 - δ) := by rw [le_div_iff₀ h1mδ]; linarith
  have hT_nn : 0 ≤ (chebyshevT r).eval (1 / (1 - δ)) := chebyshevT_nonneg_ge_one r _ hs
  rw [abs_of_nonneg hT_nn] at hBM
  -- Step 2: Bound polySupNormScaled σ₁ (1-δ) ≤ 2/δ
  -- For any x with |x_i| ≤ 1-δ, σ₁(x) ≤ 2/δ
  suffices h : polySupNormScaled σ₁ (1 - δ) ≤ 2 / δ by
    calc polySupNorm σ₁
        ≤ (Polynomial.eval (1 / (1 - δ)) (chebyshevT r)) *
            polySupNormScaled σ₁ (1 - δ) := hBM
      _ ≤ (Polynomial.eval (1 / (1 - δ)) (chebyshevT r)) * (2 / δ) := by
          apply mul_le_mul_of_nonneg_left h hT_nn
  -- Show polySupNormScaled σ₁ (1-δ) ≤ 2/δ
  rw [polySupNormScaled_unfold _ _ (by linarith)]
  apply csSup_le
  · -- Nonempty
    exact ⟨|MvPolynomial.eval 0 σ₁|, ⟨0, by
      change linftyNorm 0 ≤ 1 - δ
      simp only [linftyNorm]; split
      · linarith
      · rename_i h; apply Finset.sup'_le; intro i _; simp; linarith, rfl⟩⟩
  · -- Each |σ₁(x)| ≤ 2/δ for x in (1-δ)-cube
    rintro _ ⟨x, hx, rfl⟩
    -- σ₁(x) ≥ 0 since SOS
    have hσ₁_nn : 0 ≤ MvPolynomial.eval x σ₁ :=
      IsSOS_nonneg σ₁ hsos₁ x (Set.mem_univ _)
    change |MvPolynomial.eval x σ₁| ≤ 2 / δ
    rw [abs_of_nonneg hσ₁_nn]
    -- x is in (1-δ)-cube, hence in B² (since 1-δ < 1)
    have hx_hyp : x ∈ Hypercube 2 := by
      rw [Hypercube_mem_iff]; intro i
      have hi := (linftyNorm_le_iff (by linarith : (0:ℝ) ≤ 1 - δ)).mp hx i
      constructor <;> [linarith [abs_le.mp hi]; linarith [abs_le.mp hi]]
    -- g₁(x) = 1 - x₀² ≥ 1 - (1-δ)² = δ(2-δ) ≥ δ
    have hx0_bound : |x 0| ≤ 1 - δ := by
      exact (linftyNorm_le_iff (by linarith : (0:ℝ) ≤ 1 - δ)).mp hx 0
    have hg₁_pos : δ ≤ MvPolynomial.eval x (BoxSemialgebraicGenerator (0 : Fin 2)) := by
      rw [BoxSemialgebraicGenerator_eval]
      have : x 0 ^ 2 ≤ (1 - δ) ^ 2 := by
        exact sq_le_sq' (by linarith [abs_le.mp hx0_bound]) (by linarith [abs_le.mp hx0_bound])
      nlinarith
    -- From decomposition: σ₁(x)·g₁(x) ≤ f_ε(x) (since σ₀, σ₂·g₂ ≥ 0)
    have hσ₀_nn : 0 ≤ MvPolynomial.eval x σ₀ :=
      IsSOS_nonneg σ₀ hsos₀ x (Set.mem_univ _)
    have hσ₂_nn : 0 ≤ MvPolynomial.eval x σ₂ :=
      IsSOS_nonneg σ₂ hsos₂ x (Set.mem_univ _)
    have hg₂_nn : 0 ≤ MvPolynomial.eval x (BoxSemialgebraicGenerator (1 : Fin 2)) := by
      rw [BoxSemialgebraicGenerator_eval]
      have h1 := (Hypercube_mem_iff x).mp hx_hyp 1
      nlinarith [h1.1, h1.2, sq_nonneg (1 - x 1), sq_nonneg (1 + x 1)]
    have hprod_le : MvPolynomial.eval x σ₁ *
        MvPolynomial.eval x (BoxSemialgebraicGenerator (0 : Fin 2)) ≤
        MvPolynomial.eval x (f_eps ε) := by
      have hid := congr_arg (MvPolynomial.eval x) hdecomp
      simp only [map_add, MvPolynomial.eval_mul] at hid
      linarith [mul_nonneg hσ₂_nn hg₂_nn]
    -- f_ε(x) ≤ 1 + ε ≤ 2 on B²
    have hf_le : MvPolynomial.eval x (f_eps ε) ≤ 2 := by
      rw [f_eps_eval]
      have h0 := (Hypercube_mem_iff x).mp hx_hyp 0
      have h1 := (Hypercube_mem_iff x).mp hx_hyp 1
      have hx' : 0 ≤ 1 - x 0 ^ 2 := by
        nlinarith [h0.1, h0.2, sq_nonneg (1 - x 0), sq_nonneg (1 + x 0)]
      have hy' : 0 ≤ 1 - x 1 ^ 2 := by
        nlinarith [h1.1, h1.2, sq_nonneg (1 - x 1), sq_nonneg (1 + x 1)]
      have hx_le1 : 1 - x 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 0)]
      have hy_le1 : 1 - x 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 1)]
      nlinarith [mul_le_one₀ hx_le1 hy' hy_le1, mul_nonneg hx' hy']
    -- So σ₁(x) · g₁(x) ≤ 2 and g₁(x) ≥ δ > 0
    -- Therefore σ₁(x) ≤ 2/δ
    have hg₁_pos' : 0 < MvPolynomial.eval x (BoxSemialgebraicGenerator (0 : Fin 2)) := by
      linarith
    rw [le_div_iff₀ hδ]
    calc MvPolynomial.eval x σ₁ * δ
        ≤ MvPolynomial.eval x σ₁ *
          MvPolynomial.eval x (BoxSemialgebraicGenerator (0 : Fin 2)) :=
          mul_le_mul_of_nonneg_left hg₁_pos hσ₁_nn
      _ ≤ MvPolynomial.eval x (f_eps ε) := hprod_le
      _ ≤ 2 := hf_le

/-! ## Chebyshev growth bound

For x > 1, T_r(x) ≤ (x + √(x²-1))^r. Combined with x = 1/(1-δ)
and optimizing δ = √ε yields the final lower bound r ≥ c·ε^{-1/8}.
-/

/-- Chebyshev growth bound: for x > 1, T_r(x) ≤ (x + √(x²-1))^r.
    This is the standard bound from the explicit formula
    T_r(x) = cosh(r · acosh(x)). -/
theorem chebyshev_growth_bound (r : ℕ) (x : ℝ) (hx : 1 < x) :
    (Polynomial.eval x (chebyshevT r)) ≤ (x + Real.sqrt (x ^ 2 - 1)) ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [chebyshevT_zero]
  · exact chebyshevT_upper_bound r x (le_of_lt hx) hr

/-- For small δ, the argument 1/(1-δ) ≈ 1 + δ, so
    √((1/(1-δ))² - 1) ≈ √(2δ), and
    T_r(1/(1-δ)) ≤ (1 + δ + √(2δ))^r ≤ exp(r·(δ + √(2δ))). -/
theorem chebyshev_at_one_over_one_sub (r : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (Polynomial.eval (1 / (1 - δ)) (chebyshevT r)) ≤
      (1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1)) ^ r := by
  apply chebyshev_growth_bound
  have h1mδ : 0 < 1 - δ := by linarith
  rw [one_div, lt_inv_comm₀ (by linarith) h1mδ]
  linarith

/-! ## ArXiv v3, Proposition 13: the bivariate quantitative lower bound

Set δ = √ε. Evaluating the decomposition at `(1+δ, 1-δ)` gives the structural
lower bound `2δ/3 ≤ g(δ)`, while Taylor's theorem and the second-derivative
Markov bound control `g(δ)` using `g(0)` and `polySupNorm σ₁`. Fact 1 controls
`g(0)`, and scaled Chebyshev growth controls the sup norm. If
`r < lower_bound_const * ε⁻¹/⁸`, the resulting upper bound is strictly less than
`2δ/3`, a contradiction.
-/

/-- Structural lower bound: evaluating the QM decomposition at (1+δ, 1-δ)
    (outside B²) where g₁ < 0, using σ₁ ≥ 0 (SOS), gives g(δ) ≥ 2δ/3.
    This is the key insight: outside the hypercube, g₁ flips sign,
    turning the decomposition into a LOWER bound on σ₁. -/
theorem structural_lower_bound_g_delta
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε_δ : ε = δ ^ 2)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1) :
    2 * δ / 3 ≤ MvPolynomial.eval (diagonal_path δ) σ₁ := by
  -- Evaluate the decomposition at P = (1+δ, 1-δ)
  have heval := congr_arg (MvPolynomial.eval (diagonal_path δ)) hdecomp
  simp only [map_add, MvPolynomial.eval_mul] at heval
  -- Compute the generator values at P
  have hg0 : MvPolynomial.eval (diagonal_path δ) (BoxSemialgebraicGenerator (0 : Fin 2))
      = -δ ^ 2 - 2 * δ := gen0_on_diagonal δ
  have hg1 : MvPolynomial.eval (diagonal_path δ) (BoxSemialgebraicGenerator (1 : Fin 2))
      = 2 * δ - δ ^ 2 := gen1_on_diagonal δ
  have hf : MvPolynomial.eval (diagonal_path δ) (f_eps ε )
      = δ ^ 2 * (δ ^ 2 - 4) + ε := f_eps_on_diagonal ε δ
  -- σ₀(P) ≥ 0, σ₂(P) ≥ 0 (SOS)
  have hσ₀_nn := IsSOS_nonneg σ₀ hsos₀ (diagonal_path δ) (Set.mem_univ _)
  have hσ₂_nn := IsSOS_nonneg σ₂ hsos₂ (diagonal_path δ) (Set.mem_univ _)
  have hσ₁_nn := IsSOS_nonneg σ₁ hsos₁ (diagonal_path δ) (Set.mem_univ _)
  -- g₂(P) = 2δ - δ² ≥ 0 for δ ∈ (0, 1)
  have hg1_nn : 0 ≤ 2 * δ - δ ^ 2 := by nlinarith
  -- Set up abbreviations
  set s₀ := MvPolynomial.eval (diagonal_path δ) σ₀
  set s₁ := MvPolynomial.eval (diagonal_path δ) σ₁
  set s₂ := MvPolynomial.eval (diagonal_path δ) σ₂
  -- From decomposition: f_ε(P) = s₀ + s₁·(-δ²-2δ) + s₂·(2δ-δ²)
  rw [hf, hg0, hg1] at heval
  -- Since s₀ ≥ 0 and s₂·(2δ-δ²) ≥ 0: s₁·(-δ²-2δ) ≤ f_ε(P)
  have h1 : s₁ * (-δ ^ 2 - 2 * δ) ≤ δ ^ 2 * (δ ^ 2 - 4) + ε := by
    nlinarith [mul_nonneg hσ₂_nn hg1_nn]
  -- (-δ²-2δ) = -(δ²+2δ), and δ²+2δ ≥ 2δ > 0
  have h2 : 0 < δ ^ 2 + 2 * δ := by nlinarith
  -- s₁ * (-(δ²+2δ)) ≤ -4δ²+δ⁴+ε, so (δ²+2δ)*s₁ ≥ 4δ²-δ⁴-ε
  have h3 : 4 * δ ^ 2 - δ ^ 4 - ε ≤ (δ ^ 2 + 2 * δ) * s₁ := by nlinarith
  -- With ε ≤ δ², the left side is at least δ²(3-δ²),
  -- which is at least 2δ² when δ ≤ 1.
  have h4 : 2 * δ ^ 2 ≤ 4 * δ ^ 2 - δ ^ 4 - ε := by
    have hδ_sq : δ ^ 2 ≤ 1 := by nlinarith
    have : δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
    nlinarith [mul_le_of_le_one_right (sq_nonneg δ) hδ_sq]
  -- And δ²+2δ ≤ 3δ (for δ ≤ 1)
  have h5 : δ ^ 2 + 2 * δ ≤ 3 * δ := by nlinarith
  -- So 3δ·s₁ ≥ (δ²+2δ)·s₁ ≥ 2δ², giving s₁ ≥ 2δ/3
  nlinarith

/-- Taylor upper bound on the diagonal restriction g(δ) = σ₁(1+δ, 1-δ):
    g(δ) ≤ 2·g(0) + 2·max|g''|·δ² where g(0) = σ₁(1,1) and max|g''| is
    bounded by the Markov second-derivative inequality.

    The proof combines the Taylor expansion and Markov analysis using three
    applications of the mean value theorem and
    `multivariate_markov_k2_exterior_weak`. -/
theorem taylor_upper_bound_diagonal
    (σ₁ : MvPolynomial (Fin 2) ℝ) (r : ℕ) (hd : σ₁.totalDegree ≤ r)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hsos : IsSOS σ₁) :
    MvPolynomial.eval (diagonal_path δ) σ₁ ≤
      2 * MvPolynomial.eval corner_11 σ₁ +
      2 * δ ^ 2 * (8 * (r : ℝ) ^ 4 *
        |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁) := by
  -- Let G = univariateRestriction σ₁ corner_11 ![1, -1]
  -- G(t) = σ₁(corner_11 + t • ![1, -1]) = σ₁(diagonal_path t)
  set dir : Fin 2 → ℝ := ![1, -1] with hdir_def
  set G := univariateRestriction σ₁ corner_11 dir with hG_def
  -- Helper: corner_11 + t • dir = diagonal_path t
  have hpoint_eq : ∀ t, corner_11 + t • dir = diagonal_path t := by
    intro t; ext i; fin_cases i
    · simp [diagonal_path, corner_11, dir, Pi.add_apply, smul_eq_mul,
            Matrix.cons_val_zero]
    · simp [diagonal_path, corner_11, dir, Pi.add_apply, smul_eq_mul,
            Matrix.cons_val_one]; ring
  -- Key identity: G.eval t = σ₁(diagonal_path t)
  have hG_eval : ∀ t, G.eval t = MvPolynomial.eval (diagonal_path t) σ₁ := by
    intro t; rw [hG_def, univariateRestriction_eval, hpoint_eq]
  -- G(0) = σ₁(corner_11)
  have hG0 : G.eval 0 = MvPolynomial.eval corner_11 σ₁ := by
    rw [hG_eval, diagonal_path_zero]
  -- G(-δ) = σ₁(diagonal_path (-δ)) ≥ 0 since σ₁ is SOS
  have hG_neg_nn : 0 ≤ G.eval (-δ) := by
    rw [hG_eval]; exact IsSOS_nonneg σ₁ hsos _ (Set.mem_univ _)
  -- natDegree G ≤ r
  have hG_deg : G.natDegree ≤ r :=
    le_trans (univariateRestriction_natDegree_le σ₁ corner_11 dir) hd
  -- Step 1: MVT on G on [0, δ]: G(δ) - G(0) = G'(c₁) · δ for c₁ ∈ (0, δ)
  obtain ⟨c₁, hc₁_mem, hc₁_eq⟩ := exists_hasDerivAt_eq_slope
    (fun t => G.eval t) (fun t => (Polynomial.derivative G).eval t) hδ
    G.continuous.continuousOn (fun t _ => G.hasDerivAt t)
  -- Step 2: MVT on G on [-δ, 0]: G(0) - G(-δ) = G'(c₂) · δ for c₂ ∈ (-δ, 0)
  have hneg_δ_lt : -δ < 0 := neg_lt_zero.mpr hδ
  obtain ⟨c₂, hc₂_mem, hc₂_eq⟩ := exists_hasDerivAt_eq_slope
    (fun t => G.eval t) (fun t => (Polynomial.derivative G).eval t) hneg_δ_lt
    G.continuous.continuousOn (fun t _ => G.hasDerivAt t)
  -- Step 3: MVT on G' on [c₂, c₁]: G'(c₁) - G'(c₂) = G''(c₃) · (c₁ - c₂)
  have hc₂_lt_c₁ : c₂ < c₁ := by linarith [hc₁_mem.1, hc₂_mem.2]
  set G' := Polynomial.derivative G
  set G'' := Polynomial.derivative G'
  obtain ⟨c₃, hc₃_mem, hc₃_eq⟩ := exists_hasDerivAt_eq_slope
    (fun t => G'.eval t) (fun t => G''.eval t) hc₂_lt_c₁
    G'.continuous.continuousOn (fun t _ => G'.hasDerivAt t)
  -- Extract slope equations
  -- MVT gives: (f b - f a) / (b - a) = f'(c), i.e., f b - f a = f'(c) * (b - a)
  have hsub_eq1 : G.eval δ - G.eval 0 = G'.eval c₁ * δ := by
    have := hc₁_eq; rw [sub_zero] at this; field_simp at this; linarith
  have hsub_eq2 : G.eval 0 - G.eval (-δ) = G'.eval c₂ * δ := by
    have hδ_ne : δ ≠ 0 := ne_of_gt hδ
    -- hc₂_eq : G'.eval c₂ = (G.eval 0 - G.eval (-δ)) / (0 - (-δ))
    have h := hc₂_eq
    -- 0 - (-δ) = δ
    have hsimp : (0 : ℝ) - (-δ) = δ := by ring
    rw [hsimp] at h
    rw [h]; field_simp
  have hsub_eq3 : G'.eval c₁ - G'.eval c₂ = G''.eval c₃ * (c₁ - c₂) := by
    have := hc₃_eq
    have hne : c₁ - c₂ ≠ 0 := ne_of_gt (sub_pos.mpr hc₂_lt_c₁)
    rw [this]; field_simp
  -- From (2): G'(c₂) · δ = G(0) - G(-δ) ≤ G(0) (since G(-δ) ≥ 0)
  have hGc₂_bound : G'.eval c₂ * δ ≤ G.eval 0 := by linarith
  have hGc₂_le : G'.eval c₂ ≤ G.eval 0 / δ := by
    rw [le_div_iff₀ hδ]; linarith
  -- |c₁ - c₂| ≤ 2δ
  have hc₁_c₂_le : c₁ - c₂ ≤ 2 * δ := by linarith [hc₁_mem.2, hc₂_mem.1]
  have hc₁_c₂_pos : 0 < c₁ - c₂ := sub_pos.mpr hc₂_lt_c₁
  -- G'(c₁) ≤ G(0)/δ + |G''(c₃)| · 2δ
  have hGc₁_bound : G'.eval c₁ ≤ G.eval 0 / δ + |G''.eval c₃| * (2 * δ) := by
    have hstep : G'.eval c₁ = G'.eval c₂ + G''.eval c₃ * (c₁ - c₂) := by linarith
    calc G'.eval c₁ = G'.eval c₂ + G''.eval c₃ * (c₁ - c₂) := hstep
      _ ≤ G.eval 0 / δ + G''.eval c₃ * (c₁ - c₂) := by linarith
      _ ≤ G.eval 0 / δ + |G''.eval c₃| * (c₁ - c₂) := by
          have := le_abs_self (G''.eval c₃)
          nlinarith
      _ ≤ G.eval 0 / δ + |G''.eval c₃| * (2 * δ) := by
          nlinarith [abs_nonneg (G''.eval c₃)]
  -- G(δ) = G(0) + G'(c₁)·δ ≤ 2G(0) + 2δ²|G''(c₃)|
  have hG_delta_bound : G.eval δ ≤ 2 * G.eval 0 + 2 * δ ^ 2 * |G''.eval c₃| := by
    have h1 : G.eval δ = G.eval 0 + G'.eval c₁ * δ := by linarith
    calc G.eval δ = G.eval 0 + G'.eval c₁ * δ := h1
      _ ≤ G.eval 0 + (G.eval 0 / δ + |G''.eval c₃| * (2 * δ)) * δ := by
          nlinarith [hδ.le]
      _ = G.eval 0 + G.eval 0 / δ * δ + |G''.eval c₃| * (2 * δ) * δ := by ring
      _ = G.eval 0 + G.eval 0 + |G''.eval c₃| * (2 * δ) * δ := by
          rw [div_mul_cancel₀ _ (ne_of_gt hδ)]
      _ = 2 * G.eval 0 + 2 * δ ^ 2 * |G''.eval c₃| := by ring
  -- Bound |G''(c₃)| via multivariate Markov second-derivative inequality
  have hc₃_abs_lt : |c₃| < δ := by
    rw [abs_lt]; constructor
    · linarith [hc₃_mem.1, hc₂_mem.1]
    · linarith [hc₃_mem.2, hc₁_mem.2]
  -- G''(c₃) = directionalDeriv2 σ₁ (corner_11 + c₃ • dir) dir
  -- The second derivative of the univariate restriction at t₀ equals directionalDeriv2
  -- at the shifted point. We prove this via the shift property.
  have hG''_eq : |G''.eval c₃| =
      |directionalDeriv2 σ₁ (corner_11 + c₃ • dir) dir| := by
    -- directionalDeriv2 f x y = (derivative (derivative (univariateRestriction f x y))).eval 0
    -- univariateRestriction f (x + t₀ • y) y = (univariateRestriction f x y).comp (X + C t₀)
    -- For any polynomial p and shift polynomial q = X + C a:
    --   derivative(p.comp q) = (p.derivative.comp q) * q.derivative = p.derivative.comp q
    --   (since q.derivative = 1)
    -- So derivative(derivative(p.comp q)) = p.derivative.derivative.comp q
    -- Eval at 0: (p''.comp q).eval 0 = p''.eval (0 + a) = p''.eval a
    unfold directionalDeriv2
    rw [univariateRestriction_shift σ₁ corner_11 dir c₃]
    congr 1
    -- Goal: G''.eval c₃ = (derivative (derivative (G.comp (X + C c₃)))).eval 0
    -- Use the fact that for q = X + C c₃ with derivative 1:
    -- derivative(G.comp q) = G'.comp q  (chain rule with q' = 1)
    -- derivative(G'.comp q) = G''.comp q
    -- eval at 0: G''.comp(X + C c₃).eval 0 = G''.eval c₃
    have hq_deriv : Polynomial.derivative (Polynomial.X + Polynomial.C c₃) = 1 := by
      simp [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C]
    -- First derivative of composition
    have step1 : Polynomial.derivative (G.comp (Polynomial.X + Polynomial.C c₃)) =
        G'.comp (Polynomial.X + Polynomial.C c₃) := by
      rw [Polynomial.derivative_comp, hq_deriv, one_mul]
    -- Second derivative
    have step2 : Polynomial.derivative (G'.comp (Polynomial.X + Polynomial.C c₃)) =
        G''.comp (Polynomial.X + Polynomial.C c₃) := by
      rw [Polynomial.derivative_comp, hq_deriv, one_mul]
    rw [step1, step2, Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C, zero_add]
  -- linftyNorm dir ≤ 1
  have hdir_norm : linftyNorm dir ≤ 1 := by
    rw [linftyNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
    intro i; fin_cases i <;>
      simp [dir, Matrix.cons_val_zero, Matrix.cons_val_one]
  -- linftyNorm (diagonal_path c₃) ≤ 1 + δ
  have hpath_norm : linftyNorm (diagonal_path c₃) ≤ 1 + δ := by
    rw [linftyNorm_le_iff (by linarith : 0 ≤ 1 + δ)]
    have habs := abs_lt.mp hc₃_abs_lt
    intro i; fin_cases i
    · change |diagonal_path c₃ 0| ≤ 1 + δ
      rw [diagonal_path_val_0]; rw [abs_le]; constructor <;> linarith
    · change |diagonal_path c₃ 1| ≤ 1 + δ
      rw [diagonal_path_val_1]; rw [abs_le]; constructor <;> linarith
  -- Apply multivariate_markov_k2_exterior_weak with s = 1 + δ
  have h1δ_ge : 1 ≤ 1 + δ := le_add_of_nonneg_right hδ.le
  have hmarkov2 : |directionalDeriv2 σ₁ (diagonal_path c₃) dir| ≤
      8 * (r : ℝ) ^ 4 *
      |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁ :=
    multivariate_markov_k2_exterior_weak σ₁ r hd (diagonal_path c₃) dir
      hdir_norm (1 + δ) h1δ_ge hpath_norm
  have hG''_final : |G''.eval c₃| ≤
      8 * (r : ℝ) ^ 4 *
      |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁ := by
    rw [hG''_eq, hpoint_eq c₃]; exact hmarkov2
  -- Conclude
  rw [← hG_eval, ← hG0]
  calc G.eval δ
      ≤ 2 * G.eval 0 + 2 * δ ^ 2 * |G''.eval c₃| := hG_delta_bound
    _ ≤ 2 * G.eval 0 + 2 * δ ^ 2 *
        (8 * (r : ℝ) ^ 4 *
        |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁) := by
        nlinarith [hG''_final, sq_nonneg δ]

set_option maxHeartbeats 400000 in
-- The contradiction keeps the Taylor estimate, Chebyshev growth bound, and explicit rational
-- constant arithmetic active through the final nonlinear comparison.
/-- Chebyshev growth arithmetic for the degree lower bound.

    Derives a contradiction from the combined Taylor bound and Chebyshev growth.
    The key insight is that with the tight bound polySupNorm σ₁ ≤ 2 T_r(1/(1-δ)),
    and the Chebyshev chain, we get T_r < exp(1) < 3.
    Then the RHS of the combined bound is less than 289δ/65536 < 2δ/3 = LHS,
    contradiction. -/
theorem chebyshev_arithmetic_contradiction
    (ε : ℝ) (_hε : 0 < ε) (_hε1 : ε < 1) (r : ℕ) (hr : 0 < r) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε_δ : ε = δ ^ 2)
    (σ₁ : MvPolynomial (Fin 2) ℝ)
    (_hsos₁ : IsSOS σ₁) (_hdeg₁ : σ₁.totalDegree ≤ r)
    (_hfact1 : MvPolynomial.eval corner_11 σ₁ ≤ ε * (r : ℝ) ^ 2 / 2)
    (hfact2_tight : polySupNorm σ₁ ≤ 2 * (Polynomial.eval (1 / (1 - δ)) (chebyshevT r)))
    (_h_contra : (r : ℝ) < lower_bound_const * ε ^ (-(1 : ℝ) / 8))
    (_h_trivial : 1 < lower_bound_const * ε ^ (-(1 : ℝ) / 8))
    (h_combined : 2 * δ / 3 ≤ ε * (r : ℝ) ^ 2 + 2 * δ ^ 2 *
        (8 * (r : ℝ) ^ 4 *
        |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁))
    (hδr4 : δ * (r : ℝ) ^ 4 < 1 / 65536) :
    False := by
  -- Step 1: Derive δ ≤ 1/r² from hδr4
  have hr1_cast : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
  have hr1_sq : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hr2_le_r4 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 4 := by nlinarith
  have hδ_le_inv_r_sq : δ ≤ 1 / (r : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < (r:ℝ)^2)]
    have : δ * (r:ℝ)^2 ≤ δ * (r:ℝ)^4 := by nlinarith [hδ.le]
    linarith
  -- Step 2: Basic Chebyshev bounds
  have h1mδ_pos : 0 < 1 - δ := by linarith
  have h_inv_ge_1 : 1 ≤ 1 / (1 - δ) := by rw [le_div_iff₀ h1mδ_pos]; linarith
  have hTr_nn : 0 ≤ (chebyshevT r).eval (1 / (1 - δ)) :=
    chebyshevT_nonneg_ge_one r _ h_inv_ge_1
  have h1δ_le_inv : 1 + δ ≤ 1 / (1 - δ) := by
    rw [le_div_iff₀ h1mδ_pos]; nlinarith [sq_nonneg δ]
  have h1δ_ge : 1 ≤ 1 + δ := le_add_of_nonneg_right hδ.le
  have hTr_mono : (chebyshevT r).eval (1 + δ) ≤ (chebyshevT r).eval (1 / (1 - δ)) :=
    chebyshevT_monotone_ge_one r (by omega : 1 ≤ r) (1 + δ) (1 / (1 - δ)) h1δ_ge h1δ_le_inv
  have hT1δ_nn : 0 ≤ (chebyshevT r).eval (1 + δ) :=
    chebyshevT_nonneg_ge_one r (1 + δ) h1δ_ge
  have hT1δ_abs : |(chebyshevT r).eval (1 + δ)| = (chebyshevT r).eval (1 + δ) :=
    abs_of_nonneg hT1δ_nn
  -- Step 3: T_r(1/(1-δ)) < 3 via Chebyshev chain
  -- 5r√δ < 1
  have h5rsqrtδ_lt_1 : 5 * (r : ℝ) * Real.sqrt δ < 1 := by
    have h_sq : (5 * (r : ℝ) * Real.sqrt δ) ^ 2 = 25 * (r : ℝ) ^ 2 * δ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hδ.le]; ring
    have h_sq_lt : 25 * (r : ℝ) ^ 2 * δ < 1 := by
      calc 25 * (r:ℝ)^2 * δ
          ≤ 25 * (r:ℝ)^4 * δ := by nlinarith [hδ.le]
        _ = 25 * (δ * (r:ℝ)^4) := by ring
        _ < 25 * (1/65536) := by nlinarith [hδr4]
        _ = 25/65536 := by ring
        _ < 1 := by norm_num
    nlinarith [sq_nonneg (5 * (r : ℝ) * Real.sqrt δ - 1),
               (by positivity : 0 ≤ 5 * (r : ℝ) * Real.sqrt δ)]
  -- (1+5√δ)^r ≤ exp(5r√δ)
  have h_base_chain : (1 + 5 * Real.sqrt δ) ^ r ≤ Real.exp (5 * Real.sqrt δ * ↑r) :=
    one_add_pow_le_exp (5 * Real.sqrt δ) (by positivity) r
  -- exp(5r√δ) < exp(1)
  have h_exp_lt : Real.exp (5 * Real.sqrt δ * ↑r) < Real.exp 1 := by
    apply Real.exp_lt_exp.mpr
    rw [mul_comm (5 * Real.sqrt δ) ↑r, ← mul_assoc]
    linarith [h5rsqrtδ_lt_1]
  -- exp(1) < 3 (via Real.exp_bound with n=3)
  have h_exp1_lt_3 : Real.exp 1 < 3 := by
    have hbound := @Real.exp_bound (x := 1) (by norm_num : |1| ≤ (1 : ℝ)) (n := 3) (by norm_num)
    simp only [one_pow, one_div, sum_range_succ, range_one, sum_singleton, Nat.factorial_zero,
      Nat.cast_one, inv_one, Nat.factorial_one, Nat.factorial_two, Nat.cast_ofNat, abs_one,
      Nat.succ_eq_add_one, Nat.reduceAdd, one_mul] at hbound
    rw [abs_le] at hbound
    linarith [hbound.2]
  -- δ < 1/65536 (since r⁴ ≥ 1), hence δ ≤ 1/2 and δ ≤ 1/4
  have hδ_small : δ < 1 / 65536 := by
    calc δ = δ * 1 := (mul_one δ).symm
      _ ≤ δ * (r : ℝ) ^ 4 := by nlinarith
      _ < 1 / 65536 := hδr4
  have hδ_half : δ ≤ 1 / 2 := by linarith
  have hδ_quarter : δ ≤ 1 / 4 := by linarith
  have h_ub : (chebyshevT r).eval (1 / (1 - δ)) ≤
      (1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1)) ^ r :=
    chebyshevT_upper_bound r (1 / (1 - δ)) h_inv_ge_1 (by omega : 1 ≤ r)
  have h_inv_le : 1 / (1 - δ) ≤ 1 + 2 * δ := inv_one_sub_le δ hδ.le hδ_half
  have h_sqrt_le : Real.sqrt ((1 / (1 - δ)) ^ 2 - 1) ≤ Real.sqrt (5 * δ) :=
    sqrt_bound_near_one δ hδ.le hδ_quarter
  have h_sqrt5_le : Real.sqrt (5 * δ) = Real.sqrt 5 * Real.sqrt δ := by
    rw [Real.sqrt_mul (by norm_num : (5 : ℝ) ≥ 0)]
  have h_sqrt_delta_nn : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have h_delta_le_sqrt_delta : δ ≤ Real.sqrt δ := by
    calc δ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq hδ.le).symm
      _ ≤ Real.sqrt δ := Real.sqrt_le_sqrt (by
          have := mul_le_mul_of_nonneg_left hδ1.le hδ.le; linarith [sq δ])
  have h_sqrt5_bound : Real.sqrt 5 ≤ 3 := by
    rw [show (3 : ℝ) = Real.sqrt 9 from by
      rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h_base_le : 1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1) ≤ 1 + 5 * Real.sqrt δ := by
    have h1 : 2 * δ ≤ 2 * Real.sqrt δ :=
      mul_le_mul_of_nonneg_left h_delta_le_sqrt_delta (by norm_num)
    have h2 : Real.sqrt 5 * Real.sqrt δ ≤ 3 * Real.sqrt δ :=
      mul_le_mul_of_nonneg_right h_sqrt5_bound h_sqrt_delta_nn
    rw [h_sqrt5_le] at h_sqrt_le
    linarith
  have h_base_pos : 0 ≤ 1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1) := by
    linarith [Real.sqrt_nonneg ((1 / (1 - δ)) ^ 2 - 1)]
  -- T_r(1/(1-δ)) < 3
  have hTr_lt_3 : (chebyshevT r).eval (1 / (1 - δ)) < 3 :=
    calc (chebyshevT r).eval (1 / (1 - δ))
        ≤ (1 / (1 - δ) + Real.sqrt ((1 / (1 - δ)) ^ 2 - 1)) ^ r := h_ub
      _ ≤ (1 + 5 * Real.sqrt δ) ^ r := pow_le_pow_left₀ h_base_pos h_base_le r
      _ ≤ Real.exp (5 * Real.sqrt δ * ↑r) := h_base_chain
      _ < Real.exp 1 := h_exp_lt
      _ < 3 := h_exp1_lt_3
  -- Step 4: Derive contradiction from h_combined
  -- polySupNorm σ₁ < 6, |T_r(1+δ)| < 3
  have hsup_lt_6 : polySupNorm σ₁ < 6 := by linarith [hfact2_tight]
  have hT1δ_lt_3 : |(chebyshevT r).eval (1 + δ)| < 3 := by
    rw [hT1δ_abs]; linarith [hTr_mono]
  have hsup_nn : 0 ≤ polySupNorm σ₁ := polySupNorm_nonneg σ₁
  -- δ²r⁴ < δ/65536
  have hδ2r4 : δ ^ 2 * (r : ℝ) ^ 4 < δ / 65536 := by
    have : δ ^ 2 * (r : ℝ) ^ 4 = δ * (δ * (r : ℝ) ^ 4) := by ring
    rw [this, show δ / 65536 = δ * (1 / 65536) from by ring]
    exact mul_lt_mul_of_pos_left hδr4 hδ
  -- δ²r² < δ/65536
  have hδ2r2 : δ ^ 2 * (r : ℝ) ^ 2 < δ / 65536 := by
    calc δ ^ 2 * (r : ℝ) ^ 2 ≤ δ ^ 2 * (r : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_left hr2_le_r4 (sq_nonneg δ)
      _ < δ / 65536 := hδ2r4
  -- Bound RHS < 2δ/3
  -- 8r⁴ · |T| · ‖σ₁‖ < 8 · 3 · 6 · r⁴ = 144r⁴
  -- 2δ² · 144r⁴ = 288δ²r⁴, total < δ/65536 + 288δ/65536 = 289δ/65536 < 2δ/3
  rw [hε_δ] at h_combined
  have h_rhs_bound : δ ^ 2 * (r : ℝ) ^ 2 + 2 * δ ^ 2 *
      (8 * (r : ℝ) ^ 4 *
      |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁) < 2 * δ / 3 := by
    have h2 : 2 * δ ^ 2 * (8 * (r : ℝ) ^ 4 *
        |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁) <
        288 * (δ ^ 2 * (r : ℝ) ^ 4) := by
      by_cases h0 : polySupNorm σ₁ = 0
      · simp only [h0, mul_zero]; positivity
      · have hsup_pos : 0 < polySupNorm σ₁ := lt_of_le_of_ne hsup_nn (Ne.symm h0)
        -- |T| · ‖σ₁‖ < 3 · 6 = 18
        have h_prod_lt : |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁ < 18 := by
          calc |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁
              < 3 * polySupNorm σ₁ :=
                mul_lt_mul_of_pos_right hT1δ_lt_3 hsup_pos
            _ < 3 * 6 := mul_lt_mul_of_pos_left hsup_lt_6 (by norm_num)
            _ = 18 := by norm_num
        -- 8r⁴ · 18 = 144r⁴
        have h_M_lt : 8 * (r:ℝ)^4 *
            |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁ < 144 * (r:ℝ)^4 := by
          nlinarith
        have hδ2_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ
        have := mul_lt_mul_of_pos_left h_M_lt hδ2_pos
        linarith
    calc δ ^ 2 * (r : ℝ) ^ 2 + 2 * δ ^ 2 *
            (8 * (r : ℝ) ^ 4 *
            |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁)
        < δ / 65536 + 288 * (δ / 65536) := by linarith [hδ2r2, hδ2r4]
      _ = 289 * δ / 65536 := by ring
      _ < 2 * δ / 3 := by nlinarith
  linarith

set_option maxHeartbeats 400000 in
-- This core theorem composes structural, Taylor, and Chebyshev-growth lemmas while preserving
-- the quantitative hypotheses needed for the final contradiction.
/-- Core analytic argument for the degree lower bound.

    Combines the structural lower bound (g(δ) ≥ 2δ/3) from
    structural_lower_bound_g_delta with the Taylor upper bound
    from taylor_upper_bound_diagonal and Chebyshev growth arithmetic. -/
theorem lower_degree_bound_core
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ) (hr : 0 < r) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε_δ : ε = δ ^ 2)
    (σ₀ σ₁ σ₂ : MvPolynomial (Fin 2) ℝ)
    (hsos₀ : IsSOS σ₀) (hsos₁ : IsSOS σ₁) (hsos₂ : IsSOS σ₂)
    (_hdeg₀ : σ₀.totalDegree ≤ r)
    (_hdeg₁ : (σ₁ * BoxSemialgebraicGenerator 0).totalDegree ≤ r)
    (_hdeg₂ : (σ₂ * BoxSemialgebraicGenerator 1).totalDegree ≤ r)
    (hdeg₁' : σ₁.totalDegree ≤ r)
    (hdecomp : f_eps ε = σ₀ + σ₁ * BoxSemialgebraicGenerator 0
                            + σ₂ * BoxSemialgebraicGenerator 1)
    (hfact1 : MvPolynomial.eval corner_11 σ₁ ≤ ε * (r : ℝ) ^ 2 / 2)
    (_hfact2 : polySupNorm σ₁ ≤ (Polynomial.eval (1 / (1 - δ)) (chebyshevT r))
                      * (2 / δ))
    (h_contra : (r : ℝ) < lower_bound_const * ε ^ (-(1 : ℝ) / 8)) :
    False := by
  -- Step 1: Structural lower bound g(δ) ≥ 2δ/3
  have h_lower := structural_lower_bound_g_delta ε hε δ hδ hδ1
    hε_δ σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂ hdecomp
  -- Step 2: Taylor upper bound g(δ) ≤ 2g(0) + 2δ²·M
  have h_upper := taylor_upper_bound_diagonal σ₁ r hdeg₁' δ hδ hδ1 hsos₁
  -- Step 3: g(0) = σ₁(1,1) ≤ εr²/2
  -- Step 4: Bound the second derivative coefficient using Chebyshev growth
  -- M = 8r⁴ · |T_r(1+δ)| · polySupNorm σ₁
  -- Bound: |T_r(1+δ)| · polySupNorm σ₁ ≤ |T_r(1+δ)| · T_r(1/(1-δ)) · (2/δ)
  -- And |T_r(1+δ)| ≤ T_r(1/(1-δ)) (monotonicity, since 1+δ ≤ 1/(1-δ))
  -- Combined: g(δ) ≤ εr² + 2δ²·M

  -- Step 5: Derive contradiction from 2δ/3 ≤ εr² + 4δr⁴T_r²
  -- With ε = δ² and r < (1/16)·δ^{-1/4}, T_r ≤ exp(5r√δ) < exp(5/16) < 2
  -- The RHS is ≈ 0 for small δ while LHS = 2δ/3 > 0

  -- Trivial case: if c·ε^{-1/8} ≤ 1, then r < 1 contradicts hr.
  by_cases h_trivial : lower_bound_const * ε ^ (-(1 : ℝ) / 8) ≤ 1
  · -- r < 1 but r ≥ 1
    have : (r : ℝ) < 1 := lt_of_lt_of_le h_contra h_trivial
    have : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
    linarith
  · -- The non-trivial case: ε is small, need the full argument
    push_neg at h_trivial
    -- h_trivial : 1 < lower_bound_const * ε ^ (-(1:ℝ)/8)
    -- This means ε < lower_bound_const^8 = (1/16)^8

    -- Use h_lower and h_upper to derive the bound
    -- g(δ) ≥ 2δ/3 and g(δ) ≤ 2·εr²/2 + 2δ²·M = εr² + 2δ²M
    set g_val := MvPolynomial.eval (diagonal_path δ) σ₁
    set M := 8 * (r : ℝ) ^ 4 *
        |(chebyshevT r).eval (1 + δ)| * polySupNorm σ₁
    -- Need polySupNorm σ₁ ≥ 0
    have hsup_nn : 0 ≤ polySupNorm σ₁ := polySupNorm_nonneg σ₁
    -- Bound |T_r(1+δ)| using Chebyshev monotonicity
    have h1δ_ge : 1 ≤ 1 + δ := le_add_of_nonneg_right hδ.le
    have hT_nn : 0 ≤ (chebyshevT r).eval (1 + δ) :=
      chebyshevT_nonneg_ge_one r (1 + δ) h1δ_ge
    have hT_abs : |(chebyshevT r).eval (1 + δ)| = (chebyshevT r).eval (1 + δ) :=
      abs_of_nonneg hT_nn
    -- From the structural and Taylor bounds:
    -- 2δ/3 ≤ g_val ≤ εr² + 2δ²M
    have h_combined : 2 * δ / 3 ≤ ε * (r : ℝ) ^ 2 + 2 * δ ^ 2 * M := by
      calc 2 * δ / 3 ≤ g_val := h_lower
        _ ≤ 2 * MvPolynomial.eval corner_11 σ₁ + 2 * δ ^ 2 * M := h_upper
        _ ≤ 2 * (ε * (r : ℝ) ^ 2 / 2) + 2 * δ ^ 2 * M := by
            linarith [hfact1]
        _ = ε * (r : ℝ) ^ 2 + 2 * δ ^ 2 * M := by ring
    -- Derive tight Fact 2: polySupNorm σ₁ ≤ 2 · T_r(1/(1-δ))
    -- Key idea: for |x_i| ≤ √(1-δ), g₁(x) = 1-x₀² ≥ δ,
    -- so σ₁(x) ≤ ((1-x₀²)(1-x₁²) + ε)/(1-x₀²) = (1-x₁²) + ε/(1-x₀²)
    -- ≤ 1 + ε/δ = 1 + δ²/δ = 1 + δ < 2.
    -- Then polySupNormScaled σ₁ √(1-δ) ≤ 2.
    -- By markov_scaled_reverse with s = 1/√(1-δ):
    -- polySupNorm σ₁ ≤ T_r(1/√(1-δ)) · 2 ≤ T_r(1/(1-δ)) · 2.
    have h1mδ_pos : 0 < 1 - δ := by linarith
    have h_sqrt_1mδ_pos : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr h1mδ_pos
    have h_sqrt_1mδ_le_1 : Real.sqrt (1 - δ) ≤ 1 := by
      rw [Real.sqrt_le_one]; linarith
    have h_sqrt_1mδ_lt_1 : Real.sqrt (1 - δ) < 1 := by
      calc Real.sqrt (1 - δ) < Real.sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
        _ = 1 := Real.sqrt_one
    -- 1/√(1-δ) ≥ 1
    have h_inv_sqrt_ge_1 : 1 ≤ 1 / Real.sqrt (1 - δ) := by
      rw [le_div_iff₀ h_sqrt_1mδ_pos]; linarith
    -- √(1-δ) ≥ 1-δ (true for 0 ≤ δ ≤ 1)
    have h_sqrt_ge_1mδ : 1 - δ ≤ Real.sqrt (1 - δ) := by
      calc 1 - δ = Real.sqrt ((1 - δ) ^ 2) := by
            rw [Real.sqrt_sq (by linarith)]
        _ ≤ Real.sqrt (1 - δ) := by
            apply Real.sqrt_le_sqrt
            have : (1 - δ) ^ 2 ≤ 1 - δ := by nlinarith
            linarith
    -- 1/√(1-δ) ≤ 1/(1-δ) (by monotonicity of 1/x)
    have h_inv_sqrt_le_inv : 1 / Real.sqrt (1 - δ) ≤ 1 / (1 - δ) := by
      apply div_le_div_of_nonneg_left (by norm_num) h1mδ_pos h_sqrt_ge_1mδ
    -- Apply markov_scaled_reverse with s = 1/√(1-δ)
    have hBM_tight := markov_scaled_reverse σ₁ r hdeg₁'
      (1 / Real.sqrt (1 - δ)) h_inv_sqrt_ge_1
    -- |T_r(1/√(1-δ))| is positive
    have hTr_inv_sqrt_nn : 0 ≤ (chebyshevT r).eval (1 / Real.sqrt (1 - δ)) :=
      chebyshevT_nonneg_ge_one r _ h_inv_sqrt_ge_1
    rw [abs_of_nonneg hTr_inv_sqrt_nn] at hBM_tight
    -- 1/(1/√(1-δ)) = √(1-δ)
    have h_recip : 1 / (1 / Real.sqrt (1 - δ)) = Real.sqrt (1 - δ) := by
      rw [one_div, one_div, inv_inv]
    rw [h_recip] at hBM_tight
    -- Bound polySupNormScaled σ₁ √(1-δ) ≤ 2
    have h_scaled_le_2 : polySupNormScaled σ₁ (Real.sqrt (1 - δ)) ≤ 2 := by
      rw [polySupNormScaled_unfold _ _ (le_of_lt h_sqrt_1mδ_pos)]
      apply csSup_le
      · have : linftyNorm (0 : Fin 2 → ℝ) ≤ Real.sqrt (1 - δ) := by
          unfold linftyNorm; split
          · exact h_sqrt_1mδ_pos.le
          · rename_i h; apply Finset.sup'_le; intro i _
            simp [le_of_lt h_sqrt_1mδ_pos]
        exact ⟨|MvPolynomial.eval 0 σ₁|, ⟨0, this, rfl⟩⟩
      · rintro _ ⟨x, hx, rfl⟩
        change |MvPolynomial.eval x σ₁| ≤ 2
        have hσ₁_nn : 0 ≤ MvPolynomial.eval x σ₁ :=
          IsSOS_nonneg σ₁ hsos₁ x (Set.mem_univ _)
        rw [abs_of_nonneg hσ₁_nn]
        -- x is in √(1-δ)-cube, hence in B²
        have hx_hyp : x ∈ Hypercube 2 := by
          rw [Hypercube_mem_iff]; intro i
          have hi := (linftyNorm_le_iff h_sqrt_1mδ_pos.le).mp hx i
          constructor <;> [linarith [abs_le.mp hi, h_sqrt_1mδ_le_1];
                           linarith [abs_le.mp hi, h_sqrt_1mδ_le_1]]
        -- g₁(x) = 1 - x₀² ≥ 1 - (√(1-δ))² = 1 - (1-δ) = δ
        have hx0_bound : |x 0| ≤ Real.sqrt (1 - δ) :=
          (linftyNorm_le_iff h_sqrt_1mδ_pos.le).mp hx 0
        have hx0_sq : x 0 ^ 2 ≤ 1 - δ := by
          have h1 : x 0 ^ 2 ≤ (Real.sqrt (1 - δ)) ^ 2 :=
            sq_le_sq' (by linarith [abs_le.mp hx0_bound])
              (by linarith [abs_le.mp hx0_bound])
          rwa [Real.sq_sqrt (by linarith)] at h1
        have hg₁_ge_δ : δ ≤ 1 - x 0 ^ 2 := by linarith
        -- σ₀(x) ≥ 0, σ₂(x)·g₂(x) ≥ 0
        have hσ₀_nn : 0 ≤ MvPolynomial.eval x σ₀ :=
          IsSOS_nonneg σ₀ hsos₀ x (Set.mem_univ _)
        have hσ₂_nn : 0 ≤ MvPolynomial.eval x σ₂ :=
          IsSOS_nonneg σ₂ hsos₂ x (Set.mem_univ _)
        have hg₂_nn : 0 ≤ MvPolynomial.eval x (BoxSemialgebraicGenerator (1 : Fin 2)) := by
          rw [BoxSemialgebraicGenerator_eval]
          have h1 := (Hypercube_mem_iff x).mp hx_hyp 1
          nlinarith [h1.1, h1.2, sq_nonneg (1 - x 1), sq_nonneg (1 + x 1)]
        -- From decomposition: σ₁(x)·(1-x₀²) ≤ f_ε(x)
        have hprod_le : MvPolynomial.eval x σ₁ * (1 - x 0 ^ 2) ≤
            MvPolynomial.eval x (f_eps ε) := by
          have hid := congr_arg (MvPolynomial.eval x) hdecomp
          simp only [map_add, MvPolynomial.eval_mul, BoxSemialgebraicGenerator_eval] at hid
          have hg₂_nn' : 0 ≤ 1 - x 1 ^ 2 := by
            rw [← BoxSemialgebraicGenerator_eval]; exact hg₂_nn
          nlinarith [mul_nonneg hσ₂_nn hg₂_nn']
        -- f_ε(x) = (1-x₀²)(1-x₁²) + ε
        have hf_eval : MvPolynomial.eval x (f_eps ε) =
            (1 - x 0 ^ 2) * (1 - x 1 ^ 2) + ε := f_eps_eval ε x
        -- σ₁(x) ≤ (1-x₁²) + ε/(1-x₀²) ≤ 1 + δ < 2
        have hg₁_pos : 0 < 1 - x 0 ^ 2 := by linarith
        rw [hf_eval] at hprod_le
        have hσ₁_le : MvPolynomial.eval x σ₁ ≤ (1 - x 1 ^ 2) + ε / (1 - x 0 ^ 2) := by
          -- σ₁(x) · g₁ ≤ g₁·(1-x₁²) + ε, divide by g₁ > 0
          have h1 : MvPolynomial.eval x σ₁ ≤
              ((1 - x 0 ^ 2) * (1 - x 1 ^ 2) + ε) / (1 - x 0 ^ 2) := by
            rw [le_div_iff₀ hg₁_pos]
            linarith
          rw [add_div, mul_div_cancel_left₀ _ hg₁_pos.ne'] at h1
          exact h1
        have hx1_sq : 1 - x 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x 1)]
        have hε_over_g₁ : ε / (1 - x 0 ^ 2) ≤ δ := by
          rw [hε_δ, div_le_iff₀ hg₁_pos]
          -- δ² / (1-x₀²) ≤ δ ⟺ δ² ≤ δ(1-x₀²) ⟺ δ ≤ 1-x₀² (since δ > 0)
          nlinarith [hg₁_ge_δ]
        linarith
    -- T_r(1/√(1-δ)) ≤ T_r(1/(1-δ)) by monotonicity
    have h_inv_ge_1' : 1 ≤ 1 / (1 - δ) := by rw [le_div_iff₀ h1mδ_pos]; linarith
    have hTr_mono : (chebyshevT r).eval (1 / Real.sqrt (1 - δ)) ≤
        (chebyshevT r).eval (1 / (1 - δ)) :=
      chebyshevT_monotone_ge_one r (by omega : 1 ≤ r)
        (1 / Real.sqrt (1 - δ)) (1 / (1 - δ))
        h_inv_sqrt_ge_1 h_inv_sqrt_le_inv
    -- Combine: polySupNorm σ₁ ≤ 2 · T_r(1/(1-δ))
    have hfact2_tight : polySupNorm σ₁ ≤ 2 * (chebyshevT r).eval (1 / (1 - δ)) := by
      calc polySupNorm σ₁
          ≤ (chebyshevT r).eval (1 / Real.sqrt (1 - δ)) *
            polySupNormScaled σ₁ (Real.sqrt (1 - δ)) := hBM_tight
        _ ≤ (chebyshevT r).eval (1 / Real.sqrt (1 - δ)) * 2 := by
            apply mul_le_mul_of_nonneg_left h_scaled_le_2 hTr_inv_sqrt_nn
        _ ≤ (chebyshevT r).eval (1 / (1 - δ)) * 2 := by
            apply mul_le_mul_of_nonneg_right hTr_mono (by norm_num)
        _ = 2 * (chebyshevT r).eval (1 / (1 - δ)) := by ring
    -- Derive δ · r⁴ < 1/65536 from h_contra
    have hδr4 : δ * (r : ℝ) ^ 4 < 1 / 65536 := by
      unfold lower_bound_const at h_contra
      rw [hε_δ] at h_contra
      -- (δ²)^{-1/8} = δ^{-1/4}
      have h1 : (δ ^ 2) ^ (-(1:ℝ)/8) = δ ^ (-(1:ℝ)/4) := by
        rw [← Real.rpow_natCast δ 2, ← Real.rpow_mul hδ.le]; norm_num
      rw [h1] at h_contra
      have hδ14_pos : 0 < δ ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hδ _
      rw [show (-(1:ℝ)/4) = -((1:ℝ)/4) from by ring, Real.rpow_neg hδ.le] at h_contra
      have h3 : (r : ℝ) * δ ^ ((1:ℝ)/4) < 1 / 16 := by
        have h' := mul_lt_mul_of_pos_right h_contra hδ14_pos
        rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hδ14_pos), mul_one] at h'
      have h4 : ((r : ℝ) * δ ^ ((1:ℝ)/4)) ^ 4 < (1/16 : ℝ) ^ 4 :=
        pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
      have h5 : (δ ^ ((1:ℝ)/4)) ^ (4:ℕ) = δ := by
        rw [← Real.rpow_natCast (δ ^ ((1:ℝ)/4)) 4,
            show ((4:ℕ):ℝ) = 4 from by norm_num,
            ← Real.rpow_mul hδ.le]; norm_num
      rw [mul_pow, h5, show (1/16:ℝ)^4 = 1/65536 from by norm_num] at h4
      linarith
    exact chebyshev_arithmetic_contradiction ε hε hε1 r hr δ hδ hδ1 hε_δ
      σ₁ hsos₁ hdeg₁' hfact1 hfact2_tight h_contra h_trivial h_combined hδr4

/-- **ArXiv v3, Proposition 13**: Degree lower bound for f_ε in QM(B²).

    If (1-x²)(1-y²) + ε ∈ QM(B²)_r with ε > 0, then
    r ≥ lower_bound_const · ε^{-1/8}.

    The proof writes f_ε = σ₀ + σ₁·g₁ + σ₂·g₂ and sets δ = √ε. Evaluation
    outside the box gives `2δ/3 ≤ σ₁(1+δ, 1-δ)`. A Taylor estimate, Fact 1 at
    `(1,1)`, and scaled Chebyshev growth give the conflicting upper bound when
    `r < lower_bound_const * ε⁻¹/⁸`. -/
theorem lower_degree_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ)
    (hmem : f_eps ε ∈ BoxQuadraticModule 2 r) :
    lower_bound_const * ε ^ (-(1 : ℝ) / 8) ≤ (r : ℝ) := by
  -- Proof by contradiction: assume r < c · ε^{-1/8}
  by_contra h_contra
  push_neg at h_contra
  -- Extract QM decomposition
  obtain ⟨σ₀, σ₁, σ₂, hsos₀, hsos₁, hsos₂, hdeg₀, hdeg₁, hdeg₂, hdecomp⟩ :=
    box_qm_decomp_n2 (f_eps ε) r hmem
  -- Handle r = 0
  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
  · -- r = 0: f_eps ε can't be in QM(B²)_0 since it has degree 4
    -- but all terms in QM(B²)_0 have degree ≤ 0 (for σ₀) or ≤ 0 (for σ_i * g_i)
    -- Contradiction with f_eps having degree 4.
    exfalso
    -- With r = 0, deg(σ₁ * g₁) ≤ 0 forces σ₁ * g₁ = 0 (since ℝ[x] is a domain)
    -- Similarly σ₂ * g₂ = 0, and σ₀ has degree 0 (constant).
    -- So f_eps ε = constant. But f_eps(0,0) = 1+ε ≠ ε = f_eps(1,0).
    simp only [Nat.le_zero] at hdeg₀ hdeg₁ hdeg₂
    have hσ₁g₁_const : σ₁ * BoxSemialgebraicGenerator 0 =
        MvPolynomial.C ((σ₁ * BoxSemialgebraicGenerator 0).coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg₁
    have hσ₂g₂_const : σ₂ * BoxSemialgebraicGenerator 1 =
        MvPolynomial.C ((σ₂ * BoxSemialgebraicGenerator 1).coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg₂
    have hσ₀_const : σ₀ = MvPolynomial.C (σ₀.coeff 0) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg₀
    -- Evaluate σ₁·g₁ and σ₂·g₂ at corner (1,1): both generators vanish
    have hσ₁g₁_at_11 :
        MvPolynomial.eval corner_11 (σ₁ * BoxSemialgebraicGenerator 0) = 0 := by
      simp [MvPolynomial.eval_mul, BoxSemialgebraicGenerator_eval, corner_11_val_0]
    have hσ₂g₂_at_11 :
        MvPolynomial.eval corner_11 (σ₂ * BoxSemialgebraicGenerator 1) = 0 := by
      simp [MvPolynomial.eval_mul, BoxSemialgebraicGenerator_eval, corner_11_val_1]
    -- Since σ₁·g₁ is constant and equals 0 at (1,1), it's identically 0
    have hσ₁g₁_zero : σ₁ * BoxSemialgebraicGenerator 0 = 0 := by
      rw [hσ₁g₁_const]
      have : MvPolynomial.eval corner_11
          (MvPolynomial.C ((σ₁ * BoxSemialgebraicGenerator 0).coeff 0)) = 0 := by
        rw [← hσ₁g₁_const]; exact hσ₁g₁_at_11
      simp only [Fin.isValue, eval_C] at this
      rw [this, map_zero]
    have hσ₂g₂_zero : σ₂ * BoxSemialgebraicGenerator 1 = 0 := by
      rw [hσ₂g₂_const]
      have : MvPolynomial.eval corner_11
          (MvPolynomial.C ((σ₂ * BoxSemialgebraicGenerator 1).coeff 0)) = 0 := by
        rw [← hσ₂g₂_const]; exact hσ₂g₂_at_11
      simp only [Fin.isValue, eval_C] at this
      rw [this, map_zero]
    -- So f_eps ε = σ₀ = constant
    have hf_const : f_eps ε = MvPolynomial.C (σ₀.coeff 0) := by
      rw [hdecomp, hσ₁g₁_zero, hσ₂g₂_zero, add_zero, add_zero]; exact hσ₀_const
    -- But f_eps(0,0) = 1+ε and f_eps(1,1) = ε, contradiction
    have h1 : MvPolynomial.eval (![0, 0]) (f_eps ε) = 1 + ε := by
      rw [f_eps_eval]; simp
    have h2 : MvPolynomial.eval corner_11 (f_eps ε) = ε := by
      exact f_eps_eval_corner ε
    rw [hf_const, MvPolynomial.eval_C] at h1 h2
    linarith
  -- Set δ = √ε
  set δ := Real.sqrt ε with hδ_def
  have hδ_pos : 0 < δ := Real.sqrt_pos.mpr hε
  have hδ_lt_1 : δ < 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt hε.le hε1
  -- Degree bound on σ₁
  have hdeg₁' : σ₁.totalDegree ≤ r := sigma1_degree_bound σ₁ r hdeg₁
  -- Fact 1: σ₁(1,1) ≤ ε · r² / 2
  have hfact1 := fact1_sigma1_bound ε hε r σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂
    hdeg₀ hdeg₁ hdeg₂ hdecomp
  -- Preserve the published auxiliary sup-norm bound in the core theorem interface.
  have hfact2 := fact2_sigma1_sup ε hε hε1 r δ hδ_pos hδ_lt_1
    σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂ hdeg₁' hdecomp
  -- Apply `lower_degree_bound_core`.
  have hε_δ : ε = δ ^ 2 := by
    rw [hδ_def]; exact (Real.sq_sqrt hε.le).symm
  exact lower_degree_bound_core ε hε hε1 r hr_pos δ hδ_pos hδ_lt_1 hε_δ
    σ₀ σ₁ σ₂ hsos₀ hsos₁ hsos₂ hdeg₀ hdeg₁ hdeg₂ hdeg₁' hdecomp
    hfact1 hfact2 h_contra

/-- Alternative formulation: r ≥ c / ε^{1/8}. -/
theorem lower_degree_bound' (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ)
    (hmem : f_eps ε ∈ BoxQuadraticModule 2 r) :
    lower_bound_const / ε ^ ((1 : ℝ) / 8) ≤ (r : ℝ) := by
  have h := lower_degree_bound ε hε hε1 r hmem
  have hconv : ε ^ (-(1 : ℝ) / 8) = (ε ^ ((1 : ℝ) / 8))⁻¹ := by
    rw [show (-(1 : ℝ) / 8) = -((1 : ℝ) / 8) from by ring]
    exact Real.rpow_neg hε.le ((1 : ℝ) / 8)
  rwa [hconv, ← div_eq_mul_inv] at h

/-- Contrapositive form: if r < c·ε^{-1/8}, then f_ε ∉ QM(B²)_r. -/
theorem lower_degree_bound_contra (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ)
    (hr : (r : ℝ) < lower_bound_const * ε ^ (-(1 : ℝ) / 8)) :
    f_eps ε ∉ BoxQuadraticModule 2 r := by
  intro hmem
  have := lower_degree_bound ε hε hε1 r hmem
  linarith

/-! ## Lasserre-gap consequence of arXiv v3, Proposition 13

Since polyMin(f_ε) = ε and f_ε ∈ QM(B²)_r only for r ≥ c·ε^{-1/8},
setting ε = (c/(2r))^8 gives a gap of Ω(1/r^8) for the QM-Lasserre bound.
-/

/-- polyMin of f_ε equals ε (the minimum is at the corners). -/
theorem f_eps_polyMin (ε : ℝ) (_hε : 0 ≤ ε) :
    polyMin (f_eps ε) = ε := by
  apply le_antisymm
  · -- polyMin ≤ ε : the corner (1,1) achieves ε
    exact polyMin_le_eval (f_eps ε) corner_11 corner_11_in_hypercube |>.trans
      (le_of_eq (f_eps_eval_corner ε))
  · -- ε ≤ polyMin : for all x ∈ B², f_eps(x) ≥ ε
    apply le_csInf (Hypercube_image_nonempty (f_eps ε))
    rintro _ ⟨v, hv, rfl⟩
    change ε ≤ MvPolynomial.eval v (f_eps ε)
    rw [f_eps_eval]
    have h0 := (Hypercube_mem_iff v).mp hv 0
    have h1 := (Hypercube_mem_iff v).mp hv 1
    have hx : 0 ≤ 1 - v 0 ^ 2 := by nlinarith [h0.1, h0.2, sq_abs (v 0)]
    have hy : 0 ≤ 1 - v 1 ^ 2 := by nlinarith [h1.1, h1.2, sq_abs (v 1)]
    linarith [mul_nonneg hx hy]

/-- For the Lasserre bound, if f_ε ∉ QM(B²)_r, then
    lasserre_bound_box_qm(f_ε, r) < ε (the bound cannot certify f_ε ≥ 0
    at its true minimum). -/
theorem lasserre_box_qm_gap (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ)
    (hr : (r : ℝ) < lower_bound_const * ε ^ (-(1 : ℝ) / 8)) :
    lasserre_bound_box_qm (f_eps ε) r < ↑ε := by
  -- Key: every feasible λ satisfies λ ≤ 0 (hence < ε).
  -- For l > 0: f_eps ε - C l = f_eps(ε-l) with 0 < ε-l < ε < 1.
  --   Then lower_degree_bound_contra applies since r < c·ε^{-1/8} ≤ c·(ε-l)^{-1/8}.
  -- For l ≤ 0: already l ≤ 0 < ε.
  have key : ∀ l : ℝ, (f_eps ε - MvPolynomial.C l) ∈ BoxQuadraticModule 2 r → l ≤ 0 := by
    intro l hl
    -- f_eps ε - C l = f_eps(ε - l)
    have hfl : f_eps ε - MvPolynomial.C l = f_eps (ε - l) := by
      simp [f_eps, map_sub]; ring
    rw [hfl] at hl
    by_contra h_contra
    push_neg at h_contra  -- h_contra : 0 < l
    -- Since l > 0, ε - l < ε < 1 and ε - l could be ≤ 0 or > 0
    -- First: ε - l ≥ 0 (from nonnegativity on hypercube)
    have hge0 : 0 ≤ ε - l := by
      have := BoxQuadraticModule_subset_nonneg hl corner_11 corner_11_in_hypercube
      rw [f_eps_eval, corner_11_val_0, corner_11_val_1] at this
      linarith
    -- ε - l < ε < 1
    have hlt1 : ε - l < 1 := by linarith
    -- Subcase: ε - l = 0
    by_cases heq : ε - l = 0
    · -- f_eps(0) = f_zero ∈ QM, contradiction
      rw [heq, ← f_zero_eq] at hl
      exact (f_not_in_quadratic_module r) hl
    · -- 0 < ε - l < ε, so (ε-l)^{-1/8} > ε^{-1/8}
      have hpos : 0 < ε - l := lt_of_le_of_ne hge0 (Ne.symm heq)
      have hle_eps : ε - l ≤ ε := by linarith
      have hr' : (r : ℝ) < lower_bound_const * (ε - l) ^ (-(1 : ℝ) / 8) := by
        calc (r : ℝ) < lower_bound_const * ε ^ (-(1 : ℝ) / 8) := hr
          _ ≤ lower_bound_const * (ε - l) ^ (-(1 : ℝ) / 8) := by
            apply mul_le_mul_of_nonneg_left _ lower_bound_const_pos.le
            exact Real.rpow_le_rpow_of_nonpos hpos hle_eps (by norm_num)
      exact lower_degree_bound_contra (ε - l) hpos hlt1 r hr' hl
  -- Now show lasserre_bound_box_qm < ε
  unfold lasserre_bound_box_qm
  split_ifs with hne
  · -- Feasible set nonempty: sSup S ≤ 0 < ε
    apply WithBot.coe_lt_coe.mpr
    calc sSup { l : ℝ | (f_eps ε - MvPolynomial.C l) ∈ BoxQuadraticModule 2 r }
        ≤ 0 := csSup_le hne (fun l hl => key l hl)
      _ < ε := hε
  · -- Feasible set empty: ⊥ < ↑ε
    exact WithBot.bot_lt_coe ε

/-! ## ArXiv v3, Theorem 4: Extension to n > 2

Embed the 2-variable construction into ℝⁿ by setting x₃=...=xₙ=0.
If F_ε ∈ QM(Bⁿ)_r, restricting gives f_ε ∈ QM(B²)_r (extra generators
evaluate to 1 at x_i = 0). The same lower bound r ≥ c·ε^{-1/8} follows.
-/

/-- The n-variable version of f_ε: depends only on the first two coordinates.
    F_ε(x) = (1 - x₀²)(1 - x₁²) + ε.
    Requires n ≥ 2 so that Fin.mk 0 and Fin.mk 1 are valid indices. -/
def f_eps_n (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) : MvPolynomial (Fin n) ℝ :=
  (1 - (X ⟨0, by omega⟩) ^ 2) * (1 - (X ⟨1, by omega⟩) ^ 2) + MvPolynomial.C ε

theorem f_eps_n_eval (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (v : Fin n → ℝ) :
    MvPolynomial.eval v (f_eps_n n hn ε)
    = (1 - v ⟨0, by omega⟩ ^ 2) * (1 - v ⟨1, by omega⟩ ^ 2) + ε := by
  simp [f_eps_n, map_add, map_mul, map_sub, map_one, map_pow, eval_X,
        MvPolynomial.eval_C]

/-- Helper: an `aeval` that maps each variable to a single variable or 0
    does not increase total degree. -/
private theorem totalDegree_restrictAeval_le
    (f : Fin n → MvPolynomial (Fin 2) ℝ)
    (hf : ∀ i, f i = 0 ∨ ∃ j, f i = X j)
    (p : MvPolynomial (Fin n) ℝ) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  -- Expand p = ∑ d ∈ p.support, monomial d (coeff d p)
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  -- The totalDegree of a sum ≤ sup of totalDegrees of summands
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  -- Need: (aeval f (monomial d (coeff d p))).totalDegree ≤ p.totalDegree
  rw [MvPolynomial.aeval_monomial]
  -- Check if any variable in d.support has f i = 0
  by_cases h_vanish : ∃ i ∈ d.support, f i = 0
  · -- Some f i = 0 with d i > 0, so the product vanishes
    obtain ⟨i, hi_supp, hi_zero⟩ := h_vanish
    have hzp : f i ^ d i = 0 := by
      rw [hi_zero]; exact zero_pow (Finsupp.mem_support_iff.mp hi_supp)
    have : d.prod (fun i k => f i ^ k) = 0 := by
      simp only [Finsupp.prod]
      exact Finset.prod_eq_zero hi_supp hzp
    simp [this]
  · -- All variables in d.support have f i = X j for some j
    push_neg at h_vanish
    have hf_X : ∀ i ∈ d.support, ∃ j, f i = X j := by
      intro i hi
      rcases hf i with h | h
      · exact absurd h (h_vanish i hi)
      · exact h
    -- The product is ∏_{i ∈ d.support} (X (j i)) ^ (d i)
    calc (algebraMap ℝ (MvPolynomial (Fin 2) ℝ) (MvPolynomial.coeff d p) *
          d.prod fun i k => f i ^ k).totalDegree
        ≤ (algebraMap ℝ (MvPolynomial (Fin 2) ℝ) (MvPolynomial.coeff d p)).totalDegree +
          (d.prod fun i k => f i ^ k).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = (d.prod fun i k => f i ^ k).totalDegree := by
          rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C]; simp
      _ ≤ ∑ i ∈ d.support, (f i ^ d i).totalDegree := by
          simp only [Finsupp.prod]
          exact MvPolynomial.totalDegree_finset_prod d.support _
      _ ≤ ∑ i ∈ d.support, d i := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨j, hj⟩ := hf_X i hi
          rw [hj]
          calc (X j ^ d i : MvPolynomial (Fin 2) ℝ).totalDegree
              ≤ d i * (X j : MvPolynomial (Fin 2) ℝ).totalDegree :=
                MvPolynomial.totalDegree_pow _ _
            _ = d i := by rw [MvPolynomial.totalDegree_X]; ring
      _ = d.sum (fun _ e => e) := by rfl
      _ ≤ p.totalDegree := Finset.le_sup (f := fun s => s.sum fun _ e => e) hd

/-- The embedding: restricting from n variables to 2 variables by
    setting x₂ = ... = x_{n-1} = 0. If F_ε ∈ QM(Bⁿ)_r then
    the restriction to the first two coordinates gives f_ε ∈ QM(B²)_r. -/
theorem restriction_to_two_vars (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (r : ℕ)
    (hmem : f_eps_n n hn ε ∈ BoxQuadraticModule n r) :
    f_eps ε ∈ BoxQuadraticModule 2 r := by
  -- Extract QM decomposition: f_eps_n = σ₀ + Σᵢ σᵢ · gᵢ
  obtain ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩ := hmem
  -- The restriction map: x_i ↦ x_i for i < 2, x_i ↦ 0 for i ≥ 2
  let ι : Fin 2 → Fin n := fun i => ⟨i.val, by omega⟩
  let φ : Fin n → MvPolynomial (Fin 2) ℝ :=
    fun i => if h : i.val < 2 then X ⟨i.val, h⟩ else 0
  let restrict : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.aeval φ
  -- restrict preserves SOS (ring hom maps Σ q_i² to Σ (restrict q_i)²)
  have restrict_isSOS : ∀ p : MvPolynomial (Fin n) ℝ, IsSOS p → IsSOS (restrict p) := by
    intro p ⟨m, q, hpq⟩
    exact ⟨m, fun i => restrict (q i), by rw [hpq]; simp [map_sum, map_pow]⟩
  -- restrict doesn't increase degree
  have restrict_deg_le : ∀ p : MvPolynomial (Fin n) ℝ,
      (restrict p).totalDegree ≤ p.totalDegree :=
    totalDegree_restrictAeval_le φ (fun i => by
      simp only [φ]; split
      · next h => exact Or.inr ⟨⟨i.val, h⟩, rfl⟩
      · exact Or.inl rfl)
  -- restrict(f_eps_n) = f_eps
  have h_restrict_f : restrict (f_eps_n n hn ε) = f_eps ε := by
    simp only [restrict, φ, f_eps_n, f_eps, map_add, map_mul, map_sub, map_one, map_pow,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    simp
  -- restrict(g_j) = g_j for j : Fin 2 (via ι)
  have h_rg_lt : ∀ (j : Fin 2),
      restrict (BoxSemialgebraicGenerator (ι j)) = BoxSemialgebraicGenerator j := by
    intro j
    simp only [restrict, φ, ι, BoxSemialgebraicGenerator, map_sub, map_one, map_pow,
      MvPolynomial.aeval_X, dif_pos j.isLt]
  -- restrict(g_i) = 1 for i ≥ 2
  have h_rg_ge : ∀ (i : Fin n), ¬(i.val < 2) →
      restrict (BoxSemialgebraicGenerator i) = 1 := by
    intro i hi
    simp only [restrict, φ, BoxSemialgebraicGenerator, map_sub, map_one, map_pow,
      MvPolynomial.aeval_X, dif_neg hi]; simp
  -- Build QM decomposition for Fin 2
  let σ' : Fin 2 → MvPolynomial (Fin 2) ℝ := fun j => restrict (σ (ι j))
  let σ₀' : MvPolynomial (Fin 2) ℝ := restrict σ₀ +
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬(i.val < 2)), restrict (σ i)
  refine ⟨σ₀', σ', ?_, ?_, ?_, ?_, ?_⟩
  · -- σ₀' is SOS
    exact IsSOS_add (restrict_isSOS σ₀ hsos₀)
      (IsSOS_sum_finset (fun i _ => restrict_isSOS (σ i) (hsos i)))
  · -- Each σ'(j) is SOS
    intro j; exact restrict_isSOS (σ (ι j)) (hsos (ι j))
  · -- totalDegree σ₀' ≤ r
    calc σ₀'.totalDegree
        ≤ max (restrict σ₀).totalDegree
            (∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬(i.val < 2)),
              restrict (σ i)).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ r := by
          rw [max_le_iff]; refine ⟨(restrict_deg_le σ₀).trans hdeg₀, ?_⟩
          exact MvPolynomial.totalDegree_finsetSum_le (fun i hi => by
            have hge := (Finset.mem_filter.mp hi).2
            have : restrict (σ i) = restrict (σ i * BoxSemialgebraicGenerator i) := by
              simp [map_mul, h_rg_ge i hge, mul_one]
            rw [this]; exact (restrict_deg_le _).trans (hdeg i))
  · -- totalDegree (σ'(j) * g_j) ≤ r
    intro j
    have heq : σ' j * BoxSemialgebraicGenerator j =
        restrict (σ (ι j) * BoxSemialgebraicGenerator (ι j)) := by
      simp only [map_mul, σ', h_rg_lt]
    rw [heq]; exact (restrict_deg_le _).trans (hdeg (ι j))
  · -- The identity: f_eps ε = σ₀' + Σ_{j : Fin 2} σ'(j) * g_j
    -- Apply restrict to hsum
    have h_id := congr_arg restrict hsum
    simp only [map_add, map_sum, map_mul] at h_id
    rw [h_restrict_f] at h_id
    -- Apply restrict (ring hom) to the identity, then split the sum over Fin n
    -- into i < 2 (which gives the Fin 2 generators) and i ≥ 2 (which gives constants
    -- absorbed into σ₀'). This is finset bookkeeping.
    rw [h_id]
    -- Split Σ_{i : Fin n} into i < 2 and i ≥ 2
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < 2)
      (fun i => restrict (σ i) * restrict (BoxSemialgebraicGenerator i))
    -- For i ≥ 2: restrict(g_i) = 1, so the term simplifies to restrict(σ i)
    have h_ge2 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬(i.val < 2)),
        restrict (σ i) * restrict (BoxSemialgebraicGenerator i) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬(i.val < 2)), restrict (σ i) :=
      Finset.sum_congr rfl (fun i hi => by rw [h_rg_ge i (Finset.mem_filter.mp hi).2, mul_one])
    -- For i < 2: the filtered sum over Fin n bijects with Σ_{j : Fin 2}
    have h_lt2 : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < 2),
        restrict (σ i) * restrict (BoxSemialgebraicGenerator i) =
        ∑ j : Fin 2, σ' j * BoxSemialgebraicGenerator j := by
      -- Use Finset.sum_nbij with the injection ι : Fin 2 → Fin n
      symm
      apply Finset.sum_nbij ι
      · -- ι maps Fin 2 into the filter
        intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
      · -- ι is injective on univ
        intro j₁ _ j₂ _ h
        exact Fin.ext (by simp only [ι] at h; exact Fin.mk.inj h)
      · -- ι is surjective onto the filter
        intro i hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq,
          Finset.mem_univ, true_and] at hi
        have hiv : (i : ℕ) < 2 := hi
        exact ⟨⟨i.val, hiv⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
      · -- The summands agree
        intro j _
        simp only [σ']
        congr 1; exact (h_rg_lt j).symm
    -- Combine: Σᵢ = (i<2 part) + (i≥2 part) = Σⱼ σ'(j)*g_j + extra
    calc restrict σ₀ + ∑ i : Fin n, restrict (σ i) * restrict (BoxSemialgebraicGenerator i)
        = restrict σ₀ + (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < 2),
            restrict (σ i) * restrict (BoxSemialgebraicGenerator i) +
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬(i.val < 2)),
            restrict (σ i) * restrict (BoxSemialgebraicGenerator i)) := by
          rw [hsplit]
      _ = restrict σ₀ + (∑ j : Fin 2, σ' j * BoxSemialgebraicGenerator j +
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬(i.val < 2)), restrict (σ i)) := by
          rw [h_lt2, h_ge2]
      _ = σ₀' + ∑ j : Fin 2, σ' j * BoxSemialgebraicGenerator j := by
          simp only [σ₀']; ring

/-- **ArXiv v3, Theorem 4**: Lower bound for general n ≥ 2.

    If (1-x₁²)(1-x₂²) + ε ∈ QM(Bⁿ)_r with n ≥ 2 and 0 < ε < 1,
    then r ≥ c · ε^{-1/8}.

    Proof: Restrict to the first two coordinates via restriction_to_two_vars,
    then apply lower_degree_bound. -/
theorem lower_bound_general_n (n : ℕ) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ)
    (hmem : f_eps_n n hn ε ∈ BoxQuadraticModule n r) :
    lower_bound_const * ε ^ (-(1 : ℝ) / 8) ≤ (r : ℝ) := by
  exact lower_degree_bound ε hε hε1 r (restriction_to_two_vars n hn ε r hmem)

/-- Contrapositive form of the general-n lower bound. -/
theorem lower_bound_general_n_contra (n : ℕ) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ)
    (hr : (r : ℝ) < lower_bound_const * ε ^ (-(1 : ℝ) / 8)) :
    f_eps_n n hn ε ∉ BoxQuadraticModule n r := by
  intro hmem
  have := lower_bound_general_n n hn ε hε hε1 r hmem
  linarith

/-! ## Asymptotic interpretation

The QM-Lasserre relaxation converges at rate Ω(1/r^8), much slower than the
O(1/r²) rate of the full preordering (Slot-Laurent 2022). This shows
QM(B²) is strictly weaker than the preordering T(B²).
-/

/-- The QM-Lasserre relaxation for f_ε converges no faster than Ω(1/r^8):
    for any r, there exists ε > 0 such that the gap is at least Ω(1/r^8). -/
theorem box_qm_convergence_lower_bound (r : ℕ) (hr : 0 < r) :
    ∃ (f : MvPolynomial (Fin 2) ℝ),
      IsNonnegOn f (Hypercube 2) ∧
      (polyMin f : ℝ) - (lasserre_bound_box_qm f r).getD 0 ≥
        lower_bound_const ^ 8 / (2 * r) ^ 8 := by
  -- Use f = f_eps(1/2)
  refine ⟨f_eps (1/2), ?_, ?_⟩
  · -- f_eps(1/2) is nonneg on B²
    intro x hx
    exact le_of_lt (f_eps_pos_on_hypercube (1/2) (by norm_num) x hx)
  · -- The gap is at least c^8 / (2r)^8
    have hr_pos : (0 : ℝ) < ↑r := Nat.cast_pos.mpr hr
    have hc_pos : 0 < lower_bound_const := lower_bound_const_pos
    rw [f_eps_polyMin (1/2) (by norm_num : (0:ℝ) ≤ 1/2)]
    -- Need: 1/2 - getD 0 (lasserre_bound_box_qm (f_eps (1/2)) r) ≥ c^8 / (2r)^8
    -- Case split on whether lasserre_bound_box_qm is ⊥ or real
    set lb := lasserre_bound_box_qm (f_eps (1/2)) r with hlb_def
    -- Every feasible λ satisfies λ ≤ 1/2 - (c/r)^8
    have key : ∀ l : ℝ, (f_eps (1/2) - MvPolynomial.C l) ∈ BoxQuadraticModule 2 r →
        l ≤ 1/2 - (lower_bound_const / ↑r) ^ 8 := by
      intro l hl
      have hfl : f_eps (1/2) - MvPolynomial.C l = f_eps (1/2 - l) := by
        simp [f_eps, map_sub]; ring
      rw [hfl] at hl
      have hge0 : 0 ≤ 1/2 - l := by
        have := BoxQuadraticModule_subset_nonneg hl corner_11 corner_11_in_hypercube
        rw [f_eps_eval, corner_11_val_0, corner_11_val_1] at this; linarith
      by_cases heq0 : 1/2 - l = 0
      · exfalso; rw [heq0, ← f_zero_eq] at hl; exact f_not_in_quadratic_module r hl
      · have hpos : 0 < 1/2 - l := lt_of_le_of_ne hge0 (Ne.symm heq0)
        by_cases hge1 : 1 ≤ 1/2 - l
        · have : (lower_bound_const / ↑r) ^ 8 ≤ 1 := by
            apply pow_le_one₀ (div_nonneg hc_pos.le hr_pos.le)
            rw [div_le_one hr_pos]; unfold lower_bound_const
            calc (1:ℝ) / 16 ≤ 1 := by norm_num
              _ ≤ ↑r := by exact_mod_cast hr
          linarith
        · push_neg at hge1
          have hbound := lower_degree_bound (1/2 - l) hpos hge1 r hl
          have h1 : lower_bound_const / ↑r ≤ (1/2 - l) ^ ((1:ℝ)/8) := by
            rw [div_le_iff₀ hr_pos]
            rw [show (-(1:ℝ)/8) = -((1:ℝ)/8) from by ring] at hbound
            rw [Real.rpow_neg hpos.le] at hbound
            rw [mul_inv_le_iff₀ (Real.rpow_pos_of_pos hpos _)] at hbound
            linarith
          have hcr_nn : 0 ≤ lower_bound_const / ↑r := div_nonneg hc_pos.le hr_pos.le
          have h2 : (lower_bound_const / ↑r) ^ 8 ≤ 1/2 - l := by
            have step := pow_le_pow_left₀ hcr_nn h1 8
            have eq1 : ((1/2 - l) ^ ((1:ℝ)/8)) ^ (8 : ℕ) = 1/2 - l := by
              rw [← Real.rpow_natCast ((1/2 - l) ^ ((1:ℝ)/8)) 8,
                  ← Real.rpow_mul hpos.le]; simp [Real.rpow_one]
            linarith
          linarith
    -- Now use the bound to conclude
    -- First establish: (c/r)^8 ≥ c^8/(2r)^8
    have h_gap : lower_bound_const ^ 8 / (2 * ↑r) ^ 8 ≤
        (lower_bound_const / ↑r) ^ 8 := by
      rw [div_pow]
      apply div_le_div_of_nonneg_left (pow_pos hc_pos 8).le (pow_pos hr_pos 8)
      apply pow_le_pow_left₀ hr_pos.le
      linarith
    -- Case split on lb
    cases hlb_eq : lb with
    | bot =>
      -- lb = ⊥, getD ⊥ 0 = 0
      simp only [Option.getD]
      -- Need: 1/2 - 0 ≥ c^8 / (2r)^8
      have : lower_bound_const ^ 8 / (2 * ↑r) ^ 8 ≤ 1 / 2 := by
        have hr_ge1 : (1 : ℝ) ≤ ↑r := by exact_mod_cast hr
        have h2r : (2 : ℝ) ≤ 2 * ↑r := by linarith
        have h2r_pos : (0 : ℝ) < 2 * ↑r := by linarith
        calc lower_bound_const ^ 8 / (2 * ↑r) ^ 8
            ≤ lower_bound_const ^ 8 / 2 ^ 8 := by
              apply div_le_div_of_nonneg_left (pow_pos hc_pos 8).le
                (pow_pos (by norm_num : (0:ℝ) < 2) 8)
              exact pow_le_pow_left₀ (by norm_num) h2r 8
          _ ≤ 1 / 2 := by unfold lower_bound_const; norm_num
      linarith
    | coe val =>
      -- lb = ↑val, getD (some val) 0 = val
      simp only [Option.getD]
      -- Need: 1/2 - val ≥ c^8 / (2r)^8
      have hval_bound : val ≤ 1/2 - (lower_bound_const / ↑r) ^ 8 := by
        have hlb_eq' : lasserre_bound_box_qm (f_eps (1/2)) r = ↑val := hlb_eq
        unfold lasserre_bound_box_qm at hlb_eq'
        split_ifs at hlb_eq' with hne
        · have hval_eq : val = sSup { l : ℝ | (f_eps (1/2) - MvPolynomial.C l) ∈
              BoxQuadraticModule 2 r } := by
            exact WithBot.coe_injective hlb_eq'.symm
          rw [hval_eq]
          exact csSup_le hne (fun l hl => key l hl)
        · exact absurd hlb_eq' (by simp)
      linarith

end OptimalConvergenceRates

end
