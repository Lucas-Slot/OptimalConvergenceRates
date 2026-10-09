/-
  OptimalConvergenceRates/MarkovInequality/MarkovInequalityCorollaries.lean

  Multivariate Markov-type corollaries via line restrictions and Chebyshev growth.
-/
import OptimalConvergenceRates.Chebyshev.ChebyshevGrowth
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityClassical
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue

open MvPolynomial Finset Polynomial

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Part I: Infrastructure -/

/-! ## The l-infinity norm -/

/-- The l-infinity norm of a vector x : Fin n → ℝ, defined as max_i |x_i|.
    For n = 0 this returns 0. -/
noncomputable def linftyNorm (x : Fin n → ℝ) : ℝ :=
  if h : n = 0 then 0
  else Finset.sup' Finset.univ
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero h)))
    (fun i => |x i|)

theorem linftyNorm_nonneg (x : Fin n → ℝ) : 0 ≤ linftyNorm x := by
  unfold linftyNorm
  split
  · exact le_refl _
  · rename_i h
    have hn : 0 < n := Nat.pos_of_ne_zero h
    have ⟨i⟩ := Fin.pos_iff_nonempty.mp hn
    exact le_trans (abs_nonneg (x i)) (Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i))

theorem linftyNorm_le_iff {x : Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    linftyNorm x ≤ c ↔ ∀ i, |x i| ≤ c := by
  unfold linftyNorm
  split
  · rename_i h
    subst h
    refine ⟨fun _ i => Fin.elim0 i, fun _ => hc⟩
  · rename_i h
    constructor
    · intro hle i
      exact le_trans (Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)) hle
    · intro hall
      exact Finset.sup'_le _ _ (fun i _ => hall i)

theorem abs_le_linftyNorm (x : Fin n → ℝ) (i : Fin n) : |x i| ≤ linftyNorm x := by
  unfold linftyNorm
  split
  · rename_i h
    exfalso
    have : n ≠ 0 := (Fin.pos i).ne'
    contradiction
  · exact Finset.le_sup' (fun i => |x i|) (Finset.mem_univ i)

theorem linftyNorm_mem_hypercube_iff (x : Fin n → ℝ) :
    x ∈ Hypercube n ↔ linftyNorm x ≤ 1 := by
  rw [Hypercube_mem_iff]
  constructor
  · intro h
    rw [linftyNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    exact abs_le.mpr ⟨(h i).1, (h i).2⟩
  · intro h i
    have hi := abs_le_linftyNorm x i
    have : |x i| ≤ 1 := le_trans hi h
    exact abs_le.mp this

/-- The set of vectors with l-infinity norm ≤ r is the scaled hypercube. -/
def scaledHypercube (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) :=
  { x | linftyNorm x ≤ r }

theorem scaledHypercube_one : scaledHypercube n 1 = Hypercube n := by
  ext x; simp [scaledHypercube, linftyNorm_mem_hypercube_iff]

/-! ## Univariate restriction of a multivariate polynomial to a line -/

/-- The restriction of a multivariate polynomial f to the line t ↦ x + t • y,
    yielding a univariate polynomial in t.
    For f : MvPolynomial (Fin n) ℝ, x y : Fin n → ℝ, we define
    F(t) = f(x + t · y) as a univariate polynomial. -/
noncomputable def univariateRestriction
    (f : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) : Polynomial ℝ :=
  -- We use MvPolynomial.aeval to substitute x_i + t * y_i for each variable,
  -- where the target is Polynomial ℝ with t = X.
  MvPolynomial.aeval (R := ℝ) (fun i => Polynomial.C (x i) + Polynomial.C (y i) * Polynomial.X) f

/-- Evaluating the univariate restriction at t gives f(x + t • y). -/
theorem univariateRestriction_eval (f : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) (t : ℝ) :
    (univariateRestriction f x y).eval t = MvPolynomial.eval (x + t • y) f := by
  unfold univariateRestriction
  -- LHS = eval t (aeval g f) where g(i) = C(x i) + C(y i) * X
  -- = (Polynomial.aeval t ∘ MvPolynomial.aeval g) f
  -- By comp_aeval, = MvPolynomial.aeval (fun i => Polynomial.aeval t (g i)) f
  -- = MvPolynomial.aeval (fun i => x i + y i * t) f
  -- = MvPolynomial.eval (x + t • y) f
  rw [← Polynomial.coe_aeval_eq_eval]
  rw [show (Polynomial.aeval t : Polynomial ℝ → ℝ) (MvPolynomial.aeval
      (fun i => Polynomial.C (x i) + Polynomial.C (y i) * Polynomial.X) f) =
    ((Polynomial.aeval t).comp (MvPolynomial.aeval
      (fun i => Polynomial.C (x i) + Polynomial.C (y i) * Polynomial.X))) f from rfl]
  rw [MvPolynomial.comp_aeval]
  simp only [map_add, Polynomial.aeval_C, map_mul, Polynomial.aeval_X]
  -- algebraMap ℝ ℝ = id, and aeval = eval for the base ring
  have : (fun i => (algebraMap ℝ ℝ) (x i) + (algebraMap ℝ ℝ) (y i) * t) = (x + t • y) := by
    ext i; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [this, MvPolynomial.aeval_eq_eval]

/-- The degree of the univariate restriction is at most the total degree of f. -/
theorem univariateRestriction_natDegree_le
    (f : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) :
    (univariateRestriction f x y).natDegree ≤ f.totalDegree := by
  unfold univariateRestriction
  set g := fun i => Polynomial.C (x i) + Polynomial.C (y i) * Polynomial.X with hg_def
  -- Each g(i) has natDegree ≤ 1
  have hg_deg : ∀ i, (g i).natDegree ≤ 1 := by
    intro i
    calc (g i).natDegree
        ≤ max (Polynomial.C (x i)).natDegree
            (Polynomial.C (y i) * Polynomial.X).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ ≤ max 0 1 := by
          apply max_le_max
          · exact (Polynomial.natDegree_C _).le
          · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      _ = 1 := by simp
  -- Write f = ∑ v ∈ f.support, monomial v (coeff v f)
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  -- Bound the natDegree of the sum
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro v hv
  -- aeval g (monomial v c) = C c * ∏ i in v.support, g(i) ^ v(i)
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  -- natDegree(C c * prod) ≤ natDegree(prod)
  calc (Polynomial.C (MvPolynomial.coeff v f) *
        Finsupp.prod v fun i k => g i ^ k).natDegree
      ≤ (Finsupp.prod v fun i k => g i ^ k).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
    _ ≤ ∑ i ∈ v.support, (g i ^ v i).natDegree := by
        exact Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i ∈ v.support, (v i * 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact (Polynomial.natDegree_pow_le_of_le _ (hg_deg i))
    _ = ∑ i ∈ v.support, v i := by simp
    _ = v.sum (fun _ e => e) := by simp [Finsupp.sum]
    _ ≤ f.totalDegree := Finset.le_sup (f := fun s => s.sum fun _ e => e) hv

/-- Univariate restriction at x=0 with y being a standard basis vector
    reduces to a single-variable restriction. -/
theorem univariateRestriction_zero_basis (f : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    univariateRestriction f 0 (Pi.single i 1) =
    MvPolynomial.aeval (R := ℝ)
      (fun j => if j = i then Polynomial.X else Polynomial.C 0) f := by
  unfold univariateRestriction
  congr 1; ext j
  simp only [Pi.zero_apply, Pi.single_apply, map_zero, zero_add]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-! ## Shift and scaling lemmas for univariateRestriction -/

/-- Shifting the base point: F(t+s) with base x equals F(s) with base x + t•y. -/
theorem univariateRestriction_shift
    (f : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) (t₀ : ℝ) :
    univariateRestriction f (x + t₀ • y) y =
    (univariateRestriction f x y).comp (Polynomial.X + Polynomial.C t₀) := by
  apply Polynomial.funext
  intro s
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      univariateRestriction_eval, univariateRestriction_eval]
  have : x + t₀ • y + s • y = x + (s + t₀) • y := by
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [this]

/-- Scaling the direction: F with direction c•y equals F∘(c·t) with direction y. -/
theorem univariateRestriction_smul_dir
    (f : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) (c : ℝ) :
    univariateRestriction f x (c • y) =
    (univariateRestriction f x y).comp (Polynomial.C c * Polynomial.X) := by
  apply Polynomial.funext
  intro s
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      univariateRestriction_eval, univariateRestriction_eval]
  have : x + s • (c • y) = x + (c * s) • y := by
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [this]

/-! ## Directional derivative -/

/-- The directional derivative of f at x in direction y, defined as
    d/dt f(x + ty)|_{t=0}. -/
noncomputable def directionalDeriv
    (f : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) : ℝ :=
  (Polynomial.derivative (univariateRestriction f x y)).eval 0

/-- The second directional derivative of f at x in direction y, defined as
    d²/dt² f(x + ty)|_{t=0}. -/
noncomputable def directionalDeriv2
    (f : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) : ℝ :=
  (Polynomial.derivative (Polynomial.derivative (univariateRestriction f x y))).eval 0

/-- The derivative of the univariate restriction at t equals the directional
    derivative at the shifted point: (d/dt f(x + ty))|_{t=t₀} = ∇_y f(x + t₀y). -/
theorem univariateRestriction_deriv_eq_directionalDeriv
    (f : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) (t₀ : ℝ) :
    (Polynomial.derivative (univariateRestriction f x y)).eval t₀ =
    directionalDeriv f (x + t₀ • y) y := by
  unfold directionalDeriv
  rw [univariateRestriction_shift f x y t₀]
  rw [Polynomial.derivative_comp]
  simp [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
        Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C]

/-- Linearity of directional derivative in the direction: ∇_{c·y} f(x) = c · ∇_y f(x). -/
theorem directionalDeriv_smul
    (f : MvPolynomial (Fin n) ℝ) (x y : Fin n → ℝ) (c : ℝ) :
    directionalDeriv f x (c • y) = c * directionalDeriv f x y := by
  unfold directionalDeriv
  rw [univariateRestriction_smul_dir f x y c]
  rw [Polynomial.derivative_comp]
  simp [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
        Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
        mul_zero, zero_mul, zero_add]

/-- Chebyshev extremal property: |p(x)| ≤ |T_d(x)| · ‖p‖ for |x| ≥ 1. -/
theorem chebyshev_extremal_pointwise
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.natDegree ≤ d)
    (x : ℝ) (hx : 1 ≤ |x|) :
    |p.eval x| ≤ |(chebyshevT d).eval x| * polySupNormUni p := by
  -- From chebyshevT_extremal: |p.eval x| ≤ polySupNormUni p * (chebyshevT d).eval |x|
  have h := chebyshevT_extremal d p hdeg x hx
  -- (chebyshevT d).eval |x| ≥ 0 since |x| ≥ 1
  have hT_nn : 0 ≤ (chebyshevT d).eval |x| :=
    chebyshevT_nonneg_ge_one d |x| hx
  -- Show |(chebyshevT d).eval x| = (chebyshevT d).eval |x|
  have habs_eq : |(chebyshevT d).eval x| = (chebyshevT d).eval |x| := by
    by_cases hx_nn : 0 ≤ x
    · -- x ≥ 0, so |x| = x and T_d(x) ≥ 0
      rw [abs_of_nonneg hx_nn]
      rw [abs_of_nonneg hx_nn] at hT_nn
      exact abs_of_nonneg hT_nn
    · -- x < 0, so |x| = -x ≥ 1
      push_neg at hx_nn
      rw [abs_of_neg hx_nn]
      -- Show |T_d(x)| = T_d(-x)
      -- From T_eval_neg: T_d(-x) = negOnePow(d) * T_d(x)
      -- So |T_d(x)| = |T_d(x)| and T_d(-x) ≥ 0 (since -x ≥ 1)
      -- We have |negOnePow(d)| = 1, so |T_d(-x)| = |T_d(x)|
      -- Combined with T_d(-x) ≥ 0: |T_d(x)| = T_d(-x)
      rw [chebyshevT_eq_T_nat]
      rw [abs_of_neg hx_nn, chebyshevT_eq_T_nat] at hT_nn
      have hT_neg := Polynomial.Chebyshev.T_eval_neg (d : ℤ) x (R := ℝ)
      -- hT_neg: eval (-x) (T ℝ d) = ↑↑(d:ℤ).negOnePow * eval x (T ℝ d)
      -- From this: |eval (-x) (T ℝ d)| = |↑↑negOnePow * eval x (T ℝ d)|
      --   = |↑↑negOnePow| * |eval x (T ℝ d)| = 1 * |eval x (T ℝ d)| = |eval x (T ℝ d)|
      have hab : |(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (-x)| =
          |(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval x| := by
        rw [hT_neg, abs_mul]
        have : |((↑(d : ℤ).negOnePow : ℤ) : ℝ)| = 1 := by
          rw [← Int.cast_abs, Int.abs_negOnePow, Int.cast_one]
        rw [this, one_mul]
      rw [← hab, abs_of_nonneg hT_nn]
  rw [habs_eq]; linarith

/-! ## Lemma 3.3: Chebyshev growth on the scaled hypercube -/

theorem scaledHypercube_eq_ScaledHypercube (hr : 0 ≤ r) :
    scaledHypercube n r = ScaledHypercube r n := by
  ext x
  simp only [scaledHypercube, Set.mem_setOf_eq, ScaledHypercube, Set.mem_pi, Set.mem_univ,
             true_implies, Set.mem_Icc]
  constructor
  · intro hle i
    exact abs_le.mp ((linftyNorm_le_iff hr).mp hle i)
  · intro hall
    rw [linftyNorm_le_iff hr]
    intro i
    exact abs_le.mpr (hall i)

theorem polySupNormScaled_unfold (f : MvPolynomial (Fin n) ℝ) (r : ℝ) (hr : 0 ≤ r) :
    polySupNormScaled f r =
      sSup ((fun x => |MvPolynomial.eval x f|) '' scaledHypercube n r) := by
  simp only [polySupNormScaled, ← scaledHypercube_eq_ScaledHypercube hr]

/-- Pointwise version: for any x with linftyNorm x ≤ s where s ≥ 1,
    |f(x)| ≤ |T_d(s)| · polySupNorm f. -/
theorem markov_scaled_pointwise
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (s : ℝ) (hs : 1 ≤ s) (x : Fin n → ℝ) (hx : linftyNorm x ≤ s) :
    |MvPolynomial.eval x f| ≤ |(chebyshevT d).eval s| * polySupNorm f := by
  -- Let y = (1/s) • x, so linftyNorm y ≤ 1 and s • y = x
  have hs_pos : 0 < s := by linarith
  set y := (s⁻¹ : ℝ) • x with hy_def
  -- linftyNorm y ≤ 1
  have hy_norm : linftyNorm y ≤ 1 := by
    rw [linftyNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    simp only [hy_def, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hs_pos]
    rw [inv_mul_le_iff₀ hs_pos]
    calc |x i| ≤ linftyNorm x := abs_le_linftyNorm x i
      _ ≤ s := hx
      _ = s * 1 := (mul_one s).symm
  -- y ∈ Hypercube n
  have hy_hyp : y ∈ Hypercube n := (linftyNorm_mem_hypercube_iff y).mpr hy_norm
  -- s • y = x
  have hsy_eq : s • y = x := by
    simp only [hy_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hs_pos), one_smul]
  -- Consider F(t) = f(t • y) = univariateRestriction f 0 y evaluated at t
  set F := univariateRestriction f 0 y with hF_def
  -- F(s) = f(x)
  have hFs : F.eval s = MvPolynomial.eval x f := by
    rw [hF_def, univariateRestriction_eval]
    -- Goal: MvPolynomial.eval (0 + s • y) f = MvPolynomial.eval x f
    have : (0 : Fin n → ℝ) + s • y = x := by
      rw [zero_add]; exact hsy_eq
    rw [this]
  -- natDegree F ≤ d
  have hF_deg : F.natDegree ≤ d :=
    le_trans (univariateRestriction_natDegree_le f 0 y) hd
  -- polySupNormUni F ≤ polySupNorm f
  have hF_sup : polySupNormUni F ≤ polySupNorm f := by
    apply polySupNormUni_le_of_bound
    intro t ht1 ht2
    -- f(t•y) where |t| ≤ 1 and linftyNorm y ≤ 1
    rw [hF_def, univariateRestriction_eval]
    -- 0 + t • y = t • y, and linftyNorm(t•y) ≤ 1
    have h_in_hyp : (0 + t • y) ∈ Hypercube n := by
      rw [zero_add]
      rw [linftyNorm_mem_hypercube_iff]
      rw [linftyNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      calc |t| * |y i| ≤ 1 * |y i| := by
              exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨ht1, ht2⟩) (abs_nonneg _)
        _ = |y i| := one_mul _
        _ ≤ linftyNorm y := abs_le_linftyNorm y i
        _ ≤ 1 := hy_norm
    exact le_csSup
      (Hypercube_compact.image (continuous_abs.comp (MvPolynomial.continuous_eval f))).bddAbove
      ⟨0 + t • y, h_in_hyp, rfl⟩
  -- By chebyshevT_extremal': |F(s)| ≤ polySupNormUni F * T_d(s)
  have h_ext := chebyshevT_extremal' d F hF_deg s hs
  -- T_d(s) ≥ 0 for s ≥ 1
  have hT_nn : 0 ≤ (chebyshevT d).eval s := chebyshevT_nonneg_ge_one d s hs
  -- |T_d(s)| = T_d(s)
  rw [abs_of_nonneg hT_nn]
  -- Combine: |f(x)| = |F(s)| ≤ polySupNormUni F * T_d(s) ≤ polySupNorm f * T_d(s)
  rw [← hFs]
  calc |F.eval s|
      ≤ polySupNormUni F * (chebyshevT d).eval s := h_ext
    _ ≤ polySupNorm f * (chebyshevT d).eval s :=
        mul_le_mul_of_nonneg_right hF_sup hT_nn
    _ = (chebyshevT d).eval s * polySupNorm f := mul_comm _ _

/-- Variant of markov_scaled with a general scaling factor s ≥ 1. -/
theorem markov_scaled' (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (s : ℝ) (hs : 1 ≤ s) :
    polySupNormScaled f s ≤ |(chebyshevT d).eval s| * polySupNorm f := by
  rw [polySupNormScaled_unfold _ _ (by linarith)]
  apply csSup_le
  · -- Nonempty
    exact ⟨|MvPolynomial.eval 0 f|, ⟨0, by
      change linftyNorm 0 ≤ s
      simp only [linftyNorm]; split
      · linarith
      · rename_i h; apply Finset.sup'_le; intro i _; simp; linarith, rfl⟩⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact markov_scaled_pointwise f d hd s hs x hx

/-- **Lemma 3.3** (Chebyshev growth on scaled hypercube):
    polySupNormScaled f (1/(1-δ)) ≤ |T_d(1/(1-δ))| · polySupNorm f. -/
theorem markov_scaled
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1) :
    polySupNormScaled f (1 / (1 - δ)) ≤
      |(chebyshevT d).eval (1 / (1 - δ))| * polySupNorm f := by
  apply markov_scaled' f d hd
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
  linarith

/-! ## Reverse Chebyshev growth (between-scales Markov inequality)

For a polynomial f of degree ≤ d and s ≥ 1, the sup-norm on B^n is bounded
by |T_d(s)| times the sup-norm on the smaller (1/s)·B^n:
  polySupNorm f ≤ |T_d(s)| · polySupNormScaled f (1/s).

This is the "reverse direction" of markov_scaled': while that bounds the
sup on a *larger* cube by the sup on B^n, this bounds the sup on B^n by
the sup on a *smaller* cube.

Reference: Baldi-Slot 2024, Lemma 3.3 (change of variables). -/

/-- Reverse Chebyshev growth (pointwise): for x ∈ Hypercube n and s ≥ 1,
    |f(x)| ≤ |T_d(s)| · polySupNormScaled f (1/s).
    Proof: apply chebyshevT_extremal' to G(t) = f((t/s)·x). -/
theorem markov_scaled_reverse_pointwise
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (s : ℝ) (hs : 1 ≤ s) (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    |MvPolynomial.eval x f| ≤ |(chebyshevT d).eval s| * polySupNormScaled f (1 / s) := by
  have hs_pos : 0 < s := by linarith
  -- G(t) = f((t/s)·x)
  set v := (s⁻¹ : ℝ) • x with hv_def
  set G := univariateRestriction f 0 v with hG_def
  -- G(s) = f(x)
  have hGs : G.eval s = MvPolynomial.eval x f := by
    rw [hG_def, univariateRestriction_eval]
    have : (0 : Fin n → ℝ) + s • v = x := by
      simp only [hv_def, zero_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hs_pos), one_smul]
    rw [this]
  -- natDegree G ≤ d
  have hG_deg : G.natDegree ≤ d :=
    le_trans (univariateRestriction_natDegree_le f 0 v) hd
  -- polySupNormUni G ≤ polySupNormScaled f (1/s)
  have hG_sup : polySupNormUni G ≤ polySupNormScaled f (1 / s) := by
    apply polySupNormUni_le_of_bound
    intro t ht1 ht2
    rw [hG_def, univariateRestriction_eval]
    -- The point 0 + t • v has linftyNorm ≤ 1/s
    have hinvs : 0 ≤ 1 / s := by positivity
    have h_in_scaled : linftyNorm (0 + t • v) ≤ 1 / s := by
      rw [zero_add, linftyNorm_le_iff hinvs]
      intro i
      simp only [hv_def, Pi.smul_apply, smul_eq_mul]
      have hx_le : |x i| ≤ 1 := by
        have := (linftyNorm_mem_hypercube_iff x).mp hx
        exact le_trans (abs_le_linftyNorm x i) this
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hs_pos)]
      calc |t| * (s⁻¹ * |x i|)
          ≤ 1 * (s⁻¹ * 1) := by
            apply mul_le_mul (abs_le.mpr ⟨ht1, ht2⟩)
              (mul_le_mul_of_nonneg_left hx_le (inv_nonneg.mpr (le_of_lt hs_pos)))
              (mul_nonneg (inv_nonneg.mpr (le_of_lt hs_pos)) (abs_nonneg _)) (by norm_num)
        _ = 1 / s := by rw [mul_one, one_mul, one_div]
    -- bddAbove for the image on ScaledHypercube
    have h_in_scaled' : 0 + t • v ∈ ScaledHypercube (1 / s) n :=
      (scaledHypercube_eq_ScaledHypercube hinvs) ▸ h_in_scaled
    exact le_csSup
      ((ScaledHypercube_compact (1 / s)).image
        (continuous_abs.comp (MvPolynomial.continuous_eval f))).bddAbove
      ⟨0 + t • v, h_in_scaled', rfl⟩
  -- By chebyshevT_extremal': |G(s)| ≤ polySupNormUni G · |T_d(s)|
  have h_ext := chebyshevT_extremal' d G hG_deg s hs
  have hT_nn : 0 ≤ (chebyshevT d).eval s := chebyshevT_nonneg_ge_one d s hs
  rw [abs_of_nonneg hT_nn]
  rw [← hGs]
  calc |G.eval s|
      ≤ polySupNormUni G * (chebyshevT d).eval s := h_ext
    _ ≤ polySupNormScaled f (1 / s) * (chebyshevT d).eval s :=
        mul_le_mul_of_nonneg_right hG_sup hT_nn
    _ = (chebyshevT d).eval s * polySupNormScaled f (1 / s) := mul_comm _ _

/-- Reverse Chebyshev growth (sup-norm version): for s ≥ 1,
    polySupNorm f ≤ |T_d(s)| · polySupNormScaled f (1/s). -/
theorem markov_scaled_reverse
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (s : ℝ) (hs : 1 ≤ s) :
    polySupNorm f ≤ |(chebyshevT d).eval s| * polySupNormScaled f (1 / s) := by
  unfold polySupNorm
  apply csSup_le
  · obtain ⟨x, hx⟩ := Hypercube_nonempty
    exact ⟨|MvPolynomial.eval x f|, ⟨x, hx, rfl⟩⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact markov_scaled_reverse_pointwise f d hd s hs x hx

/-- Corollary with δ parameter: for δ ∈ (0,1),
    polySupNorm f ≤ |T_d(1/(1-δ))| · polySupNormScaled f (1-δ). -/
theorem markov_scaled_reverse_delta
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    polySupNorm f ≤ |(Polynomial.eval (1 / (1 - δ)) (chebyshevT d))| *
      polySupNormScaled f (1 - δ) := by
  have h1mδ : 0 < 1 - δ := by linarith
  have hs : 1 ≤ 1 / (1 - δ) := by rw [le_div_iff₀ h1mδ]; linarith
  have hinv : 1 / (1 / (1 - δ)) = 1 - δ := by rw [one_div, one_div, inv_inv]
  have h := markov_scaled_reverse f d hd (1 / (1 - δ)) hs
  rwa [hinv] at h

/-! ## Nonnegativity of polySupNorm -/

theorem polySupNorm_nonneg (f : MvPolynomial (Fin n) ℝ) : 0 ≤ polySupNorm f := by
  unfold polySupNorm
  obtain ⟨x, hx⟩ := Hypercube_nonempty
  apply le_csSup_of_le
    (Hypercube_compact.image (continuous_abs.comp (MvPolynomial.continuous_eval f))).bddAbove
  · exact ⟨x, hx, rfl⟩
  · exact abs_nonneg _

/-! ## Connecting polySupNorm to polySupNormScaled -/

theorem polySupNorm_eq_polySupNormScaled_one (f : MvPolynomial (Fin n) ℝ) :
    polySupNorm f = polySupNormScaled f 1 := by
  unfold polySupNorm polySupNormScaled
  rw [ScaledHypercube_one]

/-- The sup-norm on a larger scaled hypercube is at least as large. -/
theorem polySupNormScaled_mono (f : MvPolynomial (Fin n) ℝ) {r s : ℝ}
    (hrs : r ≤ s) (hr : 0 ≤ r) :
    polySupNormScaled f r ≤ polySupNormScaled f s := by
  rw [polySupNormScaled_unfold _ _ hr, polySupNormScaled_unfold _ _ (le_trans hr hrs)]
  apply csSup_le_csSup
  · -- bddAbove for the larger set: use compactness for polynomials on bounded sets
    have hs : 0 ≤ s := le_trans hr hrs
    have hcomp : IsCompact (scaledHypercube n s) := by
      have : scaledHypercube n s = Set.pi Set.univ (fun _ => Set.Icc (-s) s) := by
        ext x
        simp only [scaledHypercube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
                    Set.mem_Icc]
        constructor
        · intro hle i
          have := (linftyNorm_le_iff hs).mp hle i
          exact abs_le.mp this
        · intro hall
          rw [linftyNorm_le_iff hs]
          intro i
          exact abs_le.mpr (hall i)
      rw [this]
      exact isCompact_univ_pi (fun _ => isCompact_Icc)
    exact (hcomp.image (continuous_abs.comp (MvPolynomial.continuous_eval f))).bddAbove
  · -- Nonempty for smaller set
    exact ⟨|MvPolynomial.eval 0 f|, ⟨0, by
      change linftyNorm 0 ≤ r
      simp only [linftyNorm]
      split
      · exact hr
      · rename_i h
        apply Finset.sup'_le
        intro i _
        simp [hr], rfl⟩⟩
  · -- image of smaller set ⊆ image of larger set
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, le_trans hx hrs, rfl⟩

/-! ## Chebyshev growth constant interaction -/

/-- Combining markov_scaled with chebyshevT_upper_bound:
    For f of degree ≤ d and s ≥ 1,
    polySupNormScaled f s ≤ (s + √(s²-1))^d · polySupNorm f. -/
theorem markov_scaled_exponential
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (s : ℝ) (hs : 1 ≤ s) :
    polySupNormScaled f s ≤
      (s + Real.sqrt (s ^ 2 - 1)) ^ d * polySupNorm f := by
  by_cases hd1 : 1 ≤ d
  · have step1 := markov_scaled' f d hd s hs
    have step2 : |(chebyshevT d).eval s| ≤ (s + Real.sqrt (s ^ 2 - 1)) ^ d := by
      rw [abs_of_nonneg (chebyshevT_nonneg_ge_one d s hs)]
      exact chebyshevT_upper_bound d s hs hd1
    calc polySupNormScaled f s
        ≤ |(chebyshevT d).eval s| * polySupNorm f := step1
      _ ≤ (s + Real.sqrt (s ^ 2 - 1)) ^ d * polySupNorm f := by
          exact mul_le_mul_of_nonneg_right step2 (polySupNorm_nonneg f)
  · -- d = 0 case: f is constant, so sup norms are equal
    have hd0 : d = 0 := by omega
    subst hd0
    simp only [pow_zero, one_mul]
    -- f has totalDegree ≤ 0, so f = C (MvPolynomial.constantCoeff f)
    have hf_deg0 : f.totalDegree = 0 := Nat.le_zero.mp hd
    have hf_const : f = MvPolynomial.C (MvPolynomial.constantCoeff f) :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hf_deg0
    -- For constant f, eval x f = eval y f for all x, y
    have heval_eq : ∀ x y : Fin n → ℝ,
        MvPolynomial.eval x f = MvPolynomial.eval y f := by
      intro x y; rw [hf_const, MvPolynomial.eval_C, MvPolynomial.eval_C]
    have h0_mem : (0 : Fin n → ℝ) ∈ Hypercube n := by
      rw [Hypercube_mem_iff]; intro i; constructor <;> simp
    -- polySupNormScaled f s ≤ polySupNorm f since f is constant
    change polySupNormScaled f s ≤ polySupNorm f
    rw [polySupNormScaled_unfold _ _ (by linarith)]
    unfold polySupNorm
    apply csSup_le
    · -- nonempty: image of scaledHypercube
      exact ⟨|MvPolynomial.eval 0 f|, ⟨0, by
        change linftyNorm 0 ≤ s
        simp only [linftyNorm]
        split
        · linarith
        · rename_i h
          apply Finset.sup'_le
          intro i _
          simp; linarith, rfl⟩⟩
    · -- each element ≤ sSup of Hypercube image
      intro y hy
      obtain ⟨x, _, rfl⟩ := hy
      change |MvPolynomial.eval x f| ≤
        sSup ((fun x => |MvPolynomial.eval x f|) '' Hypercube n)
      calc |MvPolynomial.eval x f|
          = |MvPolynomial.eval 0 f| := by rw [heval_eq x 0]
        _ ≤ sSup ((fun x => |MvPolynomial.eval x f|) '' Hypercube n) :=
          le_csSup
            (Hypercube_compact.image
              (continuous_abs.comp (MvPolynomial.continuous_eval f))).bddAbove
            ⟨0, h0_mem, rfl⟩

/-! ## Derived exterior Markov inequality (k=2)

The exterior k=2 bound follows from:
1. The weak general Markov theorem gives ‖p''‖_{[-1,1]} ≤ d⁴ · ‖p‖_{[-1,1]}
2. The Chebyshev extremal property gives |p''(x)| ≤ |T_d(x)| · ‖p''‖_{[-1,1]} for |x| ≥ 1
3. Chaining: |p''(x)| ≤ d⁴ · |T_d(x)| · ‖p‖_{[-1,1]}
-/

/-- The weak general Markov theorem implies a sup-norm bound on the second derivative. -/
theorem polySupNormUni_second_deriv_le
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.natDegree ≤ d) :
    polySupNormUni (Polynomial.derivative (Polynomial.derivative p)) ≤
      (d : ℝ) ^ 4 * polySupNormUni p := by
  apply polySupNormUni_le_of_bound
  intro x hx1 hx2
  exact univariate_markov_second_derivative_weak p d hdeg x (abs_le.mpr ⟨hx1, hx2⟩)

/-- Exterior Markov inequality (k=2, |x| ≥ 1), derived from the weak general theorem
    via the Chebyshev extremal property:
    |p''(x)| ≤ d⁴ · |T_d(x)| · ‖p‖ for |x| ≥ 1. -/
theorem univariate_markov_second_derivative_outside
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.natDegree ≤ d)
    (x : ℝ) (hx : 1 ≤ |x|) :
    |(Polynomial.derivative (Polynomial.derivative p)).eval x| ≤
      (d : ℝ) ^ 4 * |(chebyshevT d).eval x| * polySupNormUni p := by
  set q := Polynomial.derivative (Polynomial.derivative p) with hq_def
  have hq_deg : q.natDegree ≤ d := calc q.natDegree
      ≤ (Polynomial.derivative p).natDegree - 1 := Polynomial.natDegree_derivative_le _
    _ ≤ (Polynomial.derivative p).natDegree := Nat.sub_le _ _
    _ ≤ p.natDegree - 1 := Polynomial.natDegree_derivative_le _
    _ ≤ p.natDegree := Nat.sub_le _ _
    _ ≤ d := hdeg
  have h_ext := chebyshev_extremal_pointwise q d hq_deg x hx
  have h_sup := polySupNormUni_second_deriv_le p d hdeg
  calc |q.eval x|
      ≤ |(chebyshevT d).eval x| * polySupNormUni q := h_ext
    _ ≤ |(chebyshevT d).eval x| * ((d : ℝ) ^ 4 * polySupNormUni p) :=
        mul_le_mul_of_nonneg_left h_sup (abs_nonneg _)
    _ = (d : ℝ) ^ 4 * |(chebyshevT d).eval x| * polySupNormUni p := by ring


/-! ## Part II: Multivariate Markov inequality (suboptimal constants) -/
/-! ## Key lemma: convex combination stays in the hypercube -/

/-- The convex combination φ(t) = ((1+t)/2)·x + ((t-1)/2)·w stays in Hypercube
    for t ∈ [-1,1] when x, w ∈ Hypercube. -/
private theorem convex_comb_in_hypercube
    (x w : Fin n → ℝ) (hx : x ∈ Hypercube n) (hw : w ∈ Hypercube n)
    (t : ℝ) (ht1 : -1 ≤ t) (ht2 : t ≤ 1) :
    ((1 + t) / 2) • x + ((t - 1) / 2) • w ∈ Hypercube n := by
  rw [Hypercube_mem_iff]; intro i
  have hxi := (Hypercube_mem_iff x).mp hx i
  have hwi := (Hypercube_mem_iff w).mp hw i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  -- φ_i = ((1+t)/2) x_i + ((t-1)/2) w_i
  -- (1+t)/2 ∈ [0,1] and (1-t)/2 ∈ [0,1], and (t-1)/2 = -(1-t)/2
  have h1t : 0 ≤ (1 + t) / 2 := by linarith
  have h1t' : (1 + t) / 2 ≤ 1 := by linarith
  have hmt : 0 ≤ (1 - t) / 2 := by linarith
  have hmt' : (1 - t) / 2 ≤ 1 := by linarith
  -- φ_i = ((1+t)/2) x_i - ((1-t)/2) w_i
  have hrw : (t - 1) / 2 = -((1 - t) / 2) := by ring
  rw [hrw]
  constructor
  · -- -1 ≤ ((1+t)/2) x_i - ((1-t)/2) w_i
    -- ≥ ((1+t)/2)(-1) - ((1-t)/2)(1) = -(1+t)/2 - (1-t)/2 = -1
    nlinarith [hxi.1, hxi.2, hwi.1, hwi.2]
  · -- ((1+t)/2) x_i - ((1-t)/2) w_i ≤ 1
    -- ≤ ((1+t)/2)(1) + ((1-t)/2)(1) = (1+t)/2 + (1-t)/2 = 1
    nlinarith [hxi.1, hxi.2, hwi.1, hwi.2]

/-! ## The φ-restriction and its derivative at t=1 -/

/-- The φ-restriction has sup norm ≤ polySupNorm f (since φ(t) ∈ Hypercube for |t| ≤ 1). -/
private theorem phi_supNorm_le
    (f : MvPolynomial (Fin n) ℝ) (x w : Fin n → ℝ)
    (hx : x ∈ Hypercube n) (hw : w ∈ Hypercube n) :
    polySupNormUni (univariateRestriction f ((x - w) / 2) ((x + w) / 2)) ≤ polySupNorm f := by
  apply polySupNormUni_le_of_bound
  intro t ht1 ht2
  rw [univariateRestriction_eval]
  -- Need: |(x-w)/2 + t•(x+w)/2| ≤ polySupNorm f
  -- i.e., the point ((x-w)/2 + t(x+w)/2) ∈ Hypercube
  have hpoint : (x - w) / 2 + t • ((x + w) / 2) ∈ Hypercube n := by
    -- This equals ((1+t)/2)·x + ((t-1)/2)·w
    have : (x - w) / 2 + t • ((x + w) / 2) = ((1 + t) / 2) • x + ((t - 1) / 2) • w := by
      ext i; simp [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact convex_comb_in_hypercube x w hx hw t ht1 ht2
  exact le_csSup
    (Hypercube_compact.image (continuous_abs.comp (MvPolynomial.continuous_eval f))).bddAbove
    ⟨(x - w) / 2 + t • ((x + w) / 2), hpoint, rfl⟩

/-! ## Derivative at t=1 gives directional derivative -/

/-- The derivative of the φ-restriction at t=1 equals directionalDeriv f x ((x+w)/2). -/
private theorem phi_deriv_at_one
    (f : MvPolynomial (Fin n) ℝ) (x w : Fin n → ℝ) :
    (Polynomial.derivative (univariateRestriction f ((x - w) / 2) ((x + w) / 2))).eval 1 =
    directionalDeriv f x ((x + w) / 2) := by
  rw [univariateRestriction_deriv_eq_directionalDeriv]
  congr 1
  ext i; simp; ring

/-! ## Main result: multivariate Markov k=1 with constant 2d² -/

/-- **Bound on directional derivative in direction x+w:**
    |∇_{x+w} f(x)| ≤ 2d² · polySupNorm f for x, w ∈ B^n.
    Uses: φ(t) stays in B^n, univariate Markov at t=1, directionalDeriv_smul. -/
private theorem dirDeriv_sum_bound
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (x w : Fin n → ℝ) (hx : x ∈ Hypercube n) (hw : w ∈ Hypercube n) :
    |directionalDeriv f x ((x + w) / 2)| ≤ d ^ 2 * polySupNorm f := by
  -- The φ-restriction has degree ≤ d and sup norm ≤ polySupNorm f
  set F := univariateRestriction f ((x - w) / 2) ((x + w) / 2) with hF_def
  have hdeg : F.natDegree ≤ d :=
    (univariateRestriction_natDegree_le f _ _).trans hd
  have hsup : polySupNormUni F ≤ polySupNorm f :=
    phi_supNorm_le f x w hx hw
  -- Apply univariate Markov at t = 1 (|1| = 1 ≤ 1)
  have hmarkov := univariate_markov_first_derivative_inside F d hdeg 1 (by norm_num)
  -- F'(1) = directionalDeriv f x ((x+w)/2)
  rw [phi_deriv_at_one] at hmarkov
  calc |directionalDeriv f x ((x + w) / 2)|
      ≤ d ^ 2 * polySupNormUni F := hmarkov
    _ ≤ d ^ 2 * polySupNorm f :=
        mul_le_mul_of_nonneg_left hsup (by positivity)

/-! ## Linearity of directional derivative in the direction -/

/-- `directionalDeriv` is additive in the direction:
    ∇_{u+v} f(x) = ∇_u f(x) + ∇_v f(x).
    Proved by induction on the MvPolynomial structure. -/
theorem directionalDeriv_add
    (f : MvPolynomial (Fin n) ℝ) (x u v : Fin n → ℝ) :
    directionalDeriv f x (u + v) =
    directionalDeriv f x u + directionalDeriv f x v := by
  unfold directionalDeriv univariateRestriction
  -- Induction on the MvPolynomial f
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [Polynomial.derivative_C, Polynomial.eval_zero]
  | add p q ihp ihq =>
    simp only [map_add, Polynomial.eval_add]
    linarith [ihp, ihq]
  | mul_X p j ihp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add,
      Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, zero_add, mul_one]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, mul_zero, add_zero]
    -- Key: (aeval g_w p).eval 0 = MvPolynomial.eval x p (doesn't depend on w)
    have heval_eq : ∀ (w : Fin n → ℝ),
        (MvPolynomial.aeval (fun i => Polynomial.C (x i) +
          Polynomial.C (w i) * Polynomial.X) p).eval 0 =
        MvPolynomial.eval x p := by
      intro w
      change (univariateRestriction p x w).eval 0 = _
      rw [univariateRestriction_eval]; simp
    -- Unify (u i + v i) with ((u+v) i) in the aeval argument
    have hconv : (fun i => Polynomial.C (x i) + Polynomial.C (u i + v i) * Polynomial.X) =
        (fun i => Polynomial.C (x i) + Polynomial.C ((u + v) i) * Polynomial.X) := by
      ext i; simp [Pi.add_apply]
    rw [heval_eq (u + v), heval_eq u, heval_eq v]
    -- Use ihp and Pi.add_apply for (u+v) j = u j + v j
    rw [show (u + v) j = u j + v j from Pi.add_apply u v j, ihp]
    ring

/-- `directionalDeriv` respects subtraction:
    ∇_{u-v} f(x) = ∇_u f(x) - ∇_v f(x). -/
theorem directionalDeriv_sub
    (f : MvPolynomial (Fin n) ℝ) (x u v : Fin n → ℝ) :
    directionalDeriv f x (u - v) =
    directionalDeriv f x u - directionalDeriv f x v := by
  have h1 := directionalDeriv_add f x (u - v) v
  have h2 : u - v + v = u := by ext i; simp
  rw [h2] at h1; linarith

/-- **Multivariate Markov k=1, interior, with constant 2d².**
    |∇_y f(x)| ≤ 2d² · polySupNorm f for x ∈ B^n, ‖y‖_∞ ≤ 1. -/
theorem multivariate_markov_k1_interior_weak
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (x y : Fin n → ℝ) (hy : linftyNorm y ≤ 1)
    (hx : x ∈ Hypercube n) :
    |directionalDeriv f x y| ≤ 2 * d ^ 2 * polySupNorm f := by
  -- y ∈ Hypercube (since ‖y‖∞ ≤ 1)
  have hy_hyp : y ∈ Hypercube n := (linftyNorm_mem_hypercube_iff y).mpr hy
  -- -y ∈ Hypercube
  have hny_hyp : -y ∈ Hypercube n := by
    rw [Hypercube_mem_iff]; intro i
    have := (Hypercube_mem_iff y).mp hy_hyp i
    simp only [Pi.neg_apply]; constructor <;> linarith [this.1, this.2]
  -- From dirDeriv_sum_bound with w = y:
  -- |∇_{(x+y)/2} f(x)| ≤ d² polySupNorm f
  have h1 := dirDeriv_sum_bound f d hd x y hx hy_hyp
  -- From dirDeriv_sum_bound with w = -y:
  -- |∇_{(x-y)/2} f(x)| ≤ d² polySupNorm f
  have h2 := dirDeriv_sum_bound f d hd x (-y) hx hny_hyp
  -- ∇_{(x+y)/2} f(x) - ∇_{(x-y)/2} f(x) = ∇_y f(x)
  -- by directionalDeriv_smul:
  -- ∇_{(x+y)/2} f(x) = (1/2) ∇_{x+y} f(x) [uses smul]
  -- ∇_{(x-y)/2} f(x) = (1/2) ∇_{x-y} f(x)
  -- And ∇_{x+y} - ∇_{x-y} = 2∇_y by linearity of directional derivative.
  -- But I don't have linearity directly. Instead, use smul:
  -- ∇_{(x+y)/2} = (1/2) ∇_{x+y} and ∇_{(x+(-y))/2} = ∇_{(x-y)/2} = (1/2) ∇_{x-y}
  -- Actually: (x + (-y)) / 2 = (x - y) / 2. ✓
  have hsmul1 : directionalDeriv f x ((x + y) / 2) =
      (1/2) * directionalDeriv f x (x + y) := by
    rw [show (x + y) / 2 = (1/2 : ℝ) • (x + y) from by
      ext i; simp [Pi.smul_apply, smul_eq_mul]; ring]
    exact directionalDeriv_smul f x (x + y) (1/2)
  have hsmul2 : directionalDeriv f x ((x + (-y)) / 2) =
      (1/2) * directionalDeriv f x (x + (-y)) := by
    rw [show (x + (-y)) / 2 = (1/2 : ℝ) • (x + (-y)) from by
      ext i; simp [Pi.smul_apply, smul_eq_mul]; ring]
    exact directionalDeriv_smul f x (x + (-y)) (1/2)
  -- Now: x + (-y) = x - y, so h2 gives bound on |∇_{(x-y)/2} f(x)|
  have hny_eq : (x + -y) / 2 = (x - y) / 2 := by
    ext i; simp [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.div_apply]; ring
  -- y = (x+y)/2 - (x-y)/2, so ∇_y = ∇_{(x+y)/2} - ∇_{(x-y)/2} by directionalDeriv_sub.
  have hy_decomp : y = (x + y) / 2 - (x - y) / 2 := by
    ext i; simp [Pi.add_apply, Pi.sub_apply, Pi.div_apply]; ring
  have hny_decomp : (x + -y) / 2 = (x - y) / 2 := hny_eq
  rw [hy_decomp, directionalDeriv_sub]
  -- |∇_{(x+y)/2} - ∇_{(x-y)/2}| ≤ |∇_{(x+y)/2}| + |∇_{(x-y)/2}|
  calc |directionalDeriv f x ((x + y) / 2) - directionalDeriv f x ((x - y) / 2)|
      ≤ |directionalDeriv f x ((x + y) / 2)| + |directionalDeriv f x ((x - y) / 2)| :=
        abs_sub _ _
    _ ≤ d ^ 2 * polySupNorm f + d ^ 2 * polySupNorm f := by
        apply add_le_add h1
        rw [← hny_eq]; exact h2
    _ = 2 * d ^ 2 * polySupNorm f := by ring

/-! ## Multivariate Markov k=1 exterior, and k=2 bounds

  Suboptimal constants: factor 2 for k=1, factor 8 for k=2.
  Exterior versions use `markov_scaled_pointwise` for Chebyshev growth.
  The k=2 bounds use the φ-restriction second derivative and Schur polarization.
-/

/-- Sup norm bound for the φ-restriction when x has ‖·‖∞ ≤ s:
    uses markov_scaled_pointwise to bound |f(z)| ≤ |T_d(s)| · polySupNorm f
    for ‖z‖∞ ≤ s. -/
private theorem phi_supNorm_le_scaled
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (x w : Fin n → ℝ) (s : ℝ) (hs : 1 ≤ s)
    (hx : linftyNorm x ≤ s) (hw : linftyNorm w ≤ s) :
    polySupNormUni (univariateRestriction f ((x - w) / 2) ((x + w) / 2)) ≤
      |(chebyshevT d).eval s| * polySupNorm f := by
  apply polySupNormUni_le_of_bound
  intro t ht1 ht2
  rw [univariateRestriction_eval]
  -- The point (x-w)/2 + t•(x+w)/2 = ((1+t)/2)x + ((t-1)/2)w has ‖·‖∞ ≤ s
  have hpoint_norm : linftyNorm ((x - w) / 2 + t • ((x + w) / 2)) ≤ s := by
    rw [linftyNorm_le_iff (by linarith : 0 ≤ s)]
    intro i
    have : ((x - w) / 2 + t • ((x + w) / 2)) i =
        ((1 + t) / 2) * x i + ((t - 1) / 2) * w i := by
      simp [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    have hxi : |x i| ≤ s := le_trans (abs_le_linftyNorm x i) hx
    have hwi : |w i| ≤ s := le_trans (abs_le_linftyNorm w i) hw
    have h1t : 0 ≤ (1 + t) / 2 := by linarith
    have hmt : 0 ≤ (1 - t) / 2 := by linarith
    calc |((1 + t) / 2) * x i + ((t - 1) / 2) * w i|
        ≤ |(1 + t) / 2| * |x i| + |(t - 1) / 2| * |w i| := by
            calc |((1 + t) / 2) * x i + ((t - 1) / 2) * w i|
                ≤ |((1 + t) / 2) * x i| + |((t - 1) / 2) * w i| := abs_add_le _ _
              _ = |(1 + t) / 2| * |x i| + |(t - 1) / 2| * |w i| := by
                  rw [abs_mul, abs_mul]
        _ = (1 + t) / 2 * |x i| + (1 - t) / 2 * |w i| := by
            rw [abs_of_nonneg h1t, show |(t - 1) / 2| = (1 - t) / 2 from by
              rw [show (t - 1) / 2 = -((1 - t) / 2) from by ring, abs_neg, abs_of_nonneg hmt]]
        _ ≤ (1 + t) / 2 * s + (1 - t) / 2 * s := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hxi h1t
            · exact mul_le_mul_of_nonneg_left hwi hmt
        _ = s := by ring
  exact markov_scaled_pointwise f d hd s hs _ hpoint_norm

/-- Directional derivative bound for direction (x+w)/2, exterior version. -/
private theorem dirDeriv_sum_bound_scaled
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (x w : Fin n → ℝ) (s : ℝ) (hs : 1 ≤ s)
    (hx : linftyNorm x ≤ s) (hw : linftyNorm w ≤ s) :
    |directionalDeriv f x ((x + w) / 2)| ≤
      d ^ 2 * |(chebyshevT d).eval s| * polySupNorm f := by
  set F := univariateRestriction f ((x - w) / 2) ((x + w) / 2)
  have hdeg : F.natDegree ≤ d := (univariateRestriction_natDegree_le f _ _).trans hd
  have hsup := phi_supNorm_le_scaled f d hd x w s hs hx hw
  have hmarkov := univariate_markov_first_derivative_inside F d hdeg 1 (by norm_num)
  rw [phi_deriv_at_one] at hmarkov
  calc |directionalDeriv f x ((x + w) / 2)|
      ≤ d ^ 2 * polySupNormUni F := hmarkov
    _ ≤ d ^ 2 * (|(chebyshevT d).eval s| * polySupNorm f) :=
        mul_le_mul_of_nonneg_left hsup (by positivity)
    _ = d ^ 2 * |(chebyshevT d).eval s| * polySupNorm f := by ring

theorem multivariate_markov_k1_exterior_weak
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (x y : Fin n → ℝ) (hy : linftyNorm y ≤ 1)
    (s : ℝ) (hs : 1 ≤ s) (hx : linftyNorm x ≤ s) :
    |directionalDeriv f x y| ≤
      2 * d ^ 2 * |(chebyshevT d).eval s| * polySupNorm f := by
  -- y and -y have ‖·‖∞ ≤ 1 ≤ s
  have hy_le : linftyNorm y ≤ s := le_trans hy hs
  have hny_le : linftyNorm (-y) ≤ s := by
    rw [show (-y) = (-1 : ℝ) • y from by ext i; simp]
    rw [linftyNorm_le_iff (by linarith : 0 ≤ s)]; intro i
    simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul, abs_neg]
    exact le_trans (le_trans (abs_le_linftyNorm y i) hy) hs
  have h1 := dirDeriv_sum_bound_scaled f d hd x y s hs hx hy_le
  have h2 := dirDeriv_sum_bound_scaled f d hd x (-y) s hs hx hny_le
  -- y = (x+y)/2 - (x-y)/2
  have hy_decomp : y = (x + y) / 2 - (x - y) / 2 := by
    ext i; simp [Pi.add_apply, Pi.sub_apply, Pi.div_apply]; ring
  have hny_eq : (x + -y) / 2 = (x - y) / 2 := by
    ext i; simp [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.div_apply]; ring
  rw [hy_decomp, directionalDeriv_sub]
  set M := d ^ 2 * |(chebyshevT d).eval s| * polySupNorm f
  calc |directionalDeriv f x ((x + y) / 2) - directionalDeriv f x ((x - y) / 2)|
      ≤ |directionalDeriv f x ((x + y) / 2)| + |directionalDeriv f x ((x - y) / 2)| :=
        abs_sub _ _
    _ ≤ M + M := by
        apply add_le_add h1; rw [← hny_eq]; exact h2
    _ = 2 * d ^ 2 * |(chebyshevT d).eval s| * polySupNorm f := by ring

/-! ## Infrastructure for k=2: second directional derivative -/

-- D²_{c·v} f(x) = c² · D²_v f(x) (chain rule for second derivative).
-- Proof: F(t) = f(x+t(cv)) = G(ct) where G = univRestr f x v. F'' = c²G''.
theorem directionalDeriv2_smul
    (f : MvPolynomial (Fin n) ℝ) (x v : Fin n → ℝ) (c : ℝ) :
    directionalDeriv2 f x (c • v) = c ^ 2 * directionalDeriv2 f x v := by
  unfold directionalDeriv2
  rw [univariateRestriction_smul_dir]
  set F := univariateRestriction f x v
  have hcx_deriv : Polynomial.derivative (Polynomial.C c * Polynomial.X) = Polynomial.C c := by
    simp [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X]
  rw [Polynomial.derivative_comp, hcx_deriv,
      Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_comp, hcx_deriv]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_X, mul_zero]
  ring

-- φ-restriction second derivative at t=1 = directionalDeriv2 f x ((x+w)/2).
-- Proof: G = F.comp(X + C 1) by shift, G''(0) = F''(1) since (X+C1)' = 1.
private theorem phi_deriv2_at_one
    (f : MvPolynomial (Fin n) ℝ) (x w : Fin n → ℝ) :
    (Polynomial.derivative (Polynomial.derivative
      (univariateRestriction f ((x - w) / 2) ((x + w) / 2)))).eval 1 =
    directionalDeriv2 f x ((x + w) / 2) := by
  unfold directionalDeriv2
  suffices hcomp : univariateRestriction f x ((x + w) / 2) =
      (univariateRestriction f ((x - w) / 2) ((x + w) / 2)).comp
        (Polynomial.X + Polynomial.C 1) by
    rw [hcomp, Polynomial.derivative_comp,
      show Polynomial.derivative (Polynomial.X + Polynomial.C (1:ℝ)) = 1 from by simp,
      one_mul, Polynomial.derivative_comp,
      show Polynomial.derivative (Polynomial.X + Polynomial.C (1:ℝ)) = 1 from by simp, one_mul]
    simp [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  apply Polynomial.funext; intro t
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [univariateRestriction_eval, univariateRestriction_eval]
  have : x + t • ((x + w) / 2) = (x - w) / 2 + (t + 1) • ((x + w) / 2) := by
    ext i
    change x i + t * ((x + w) / 2) i = ((x - w) / 2) i + (t + 1) * ((x + w) / 2) i
    have h2 : (2 : Fin n → ℝ) i = 2 := Pi.ofNat_apply 2 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, h2]; ring
  rw [this]

-- NOTE: directionalDeriv2 is NOT additive (it's quadratic/bilinear in direction).
-- But the POLARIZATION IDENTITY holds: D²_{u+v} + D²_{u-v} = 2D²_u + 2D²_v.
theorem directionalDeriv2_polarization
    (f : MvPolynomial (Fin n) ℝ) (x u v : Fin n → ℝ) :
    directionalDeriv2 f x (u + v) + directionalDeriv2 f x (u - v) =
    2 * directionalDeriv2 f x u + 2 * directionalDeriv2 f x v := by
  unfold directionalDeriv2 univariateRestriction
  induction f using MvPolynomial.induction_on with
  | C a => simp [Polynomial.derivative_C]
  | add p q ihp ihq =>
    simp only [map_add, Polynomial.eval_add]; linarith
  | mul_X p j ihp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add,
      Polynomial.derivative_C, Polynomial.derivative_X,
      mul_one, zero_mul, mul_zero, add_zero, zero_add,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hderiv : ∀ (w : Fin n → ℝ),
        (Polynomial.derivative (MvPolynomial.aeval
          (fun i => Polynomial.C (x i) + Polynomial.C (w i) * Polynomial.X) p)).eval 0 =
        directionalDeriv p x w := by intro w; rfl
    simp only [hderiv]
    rw [directionalDeriv_add, directionalDeriv_sub,
        show (u + v) j = u j + v j from Pi.add_apply u v j,
        show (u - v) j = u j - v j from Pi.sub_apply u v j]
    linear_combination (x j) * ihp

/-- **Multivariate Markov k=2, interior, with constant 8.**
    Proof: use φ(t) = ((1+t)x + (t-1)w)/2 as before.
    q''(1) = (1/4) D̂²f(x)(x+w), by weak Markov k=2:
    |q''(1)| ≤ d⁴ · polySupNormUni q ≤ d⁴ · polySupNorm f.
    So |D̂²f(x)(x+w)| ≤ 4d⁴ · polySupNorm f.
    Extract D̂²f(x)(y) via two Schur iterations (factor 2 each):
    |D̂²f(x)(y)| ≤ 4 · 2 · d⁴ · polySupNorm f = 8d⁴ · polySupNorm f. -/
theorem multivariate_markov_k2_interior_weak
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (x y : Fin n → ℝ) (hy : linftyNorm y ≤ 1)
    (hx : x ∈ Hypercube n) :
    |directionalDeriv2 f x y| ≤
      8 * (d : ℝ) ^ 4 * polySupNorm f := by
  -- For d ≤ 1, the second directional derivative is 0 (f has degree ≤ 1).
  by_cases hd1 : d ≤ 1
  · have hF_deg : (univariateRestriction f x y).natDegree ≤ 1 :=
      (univariateRestriction_natDegree_le f x y).trans (hd.trans hd1)
    have hF'_deg : (Polynomial.derivative (univariateRestriction f x y)).natDegree = 0 :=
      Nat.le_zero.mp ((Polynomial.natDegree_derivative_le _).trans (by omega))
    unfold directionalDeriv2
    rw [Polynomial.derivative_of_natDegree_zero hF'_deg, Polynomial.eval_zero, abs_zero]
    apply mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) (by positivity)) (polySupNorm_nonneg f)
  · push_neg at hd1
    have hy_hyp : y ∈ Hypercube n := (linftyNorm_mem_hypercube_iff y).mpr hy
    have hny_hyp : -y ∈ Hypercube n := by
      rw [Hypercube_mem_iff]; intro i
      have := (Hypercube_mem_iff y).mp hy_hyp i
      simp only [Pi.neg_apply]; constructor <;> linarith [this.1, this.2]
    have h0_hyp : (0 : Fin n → ℝ) ∈ Hypercube n := by
      rw [Hypercube_mem_iff]; intro i; simp
    set C := (d : ℝ) ^ 4
    have hC_nn : 0 ≤ C := by positivity
    -- Step 1: Bound |D²_{(x+w)/2}| ≤ C·M for each w ∈ Hypercube
    have h_bound_w : ∀ (w : Fin n → ℝ), w ∈ Hypercube n →
        |directionalDeriv2 f x ((x + w) / 2)| ≤ C * polySupNorm f := by
      intro w hw
      set F := univariateRestriction f ((x - w) / 2) ((x + w) / 2)
      have hdeg : F.natDegree ≤ d := (univariateRestriction_natDegree_le f _ _).trans hd
      have hsup : polySupNormUni F ≤ polySupNorm f := phi_supNorm_le f x w hx hw
      have hmarkov := univariate_markov_second_derivative_weak F d hdeg 1 (by norm_num)
      rw [phi_deriv2_at_one] at hmarkov
      calc |directionalDeriv2 f x ((x + w) / 2)|
          ≤ C * polySupNormUni F := hmarkov
        _ ≤ C * polySupNorm f := mul_le_mul_of_nonneg_left hsup hC_nn
    -- Step 2: By directionalDeriv2_smul, |D²_{x+w}| ≤ 4C·M
    have h_xy := h_bound_w y hy_hyp     -- |D²_{(x+y)/2}| ≤ CM
    have h_xny := h_bound_w (-y) hny_hyp -- |D²_{(x-y)/2}| ≤ CM
    have h_x0 := h_bound_w 0 h0_hyp     -- |D²_{x/2}| ≤ CM
    have hsmul_xy : directionalDeriv2 f x ((x + y) / 2) =
        (1/2)^2 * directionalDeriv2 f x (x + y) := by
      rw [show (x + y) / 2 = (1/2 : ℝ) • (x + y) from by
        ext i; simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.div_apply]; ring]
      exact directionalDeriv2_smul f x (x + y) (1/2)
    have hsmul_xny : directionalDeriv2 f x ((x + (-y)) / 2) =
        (1/2)^2 * directionalDeriv2 f x (x + (-y)) := by
      rw [show (x + (-y)) / 2 = (1/2 : ℝ) • (x + (-y)) from by
        ext i
        simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.neg_apply, Pi.div_apply]
        ring]
      exact directionalDeriv2_smul f x (x + (-y)) (1/2)
    have hsmul_x0 : directionalDeriv2 f x ((x + 0) / 2) =
        (1/2)^2 * directionalDeriv2 f x x := by
      rw [show (x + (0 : Fin n → ℝ)) / 2 = (1/2 : ℝ) • x from by
        ext i; simp [Pi.smul_apply, smul_eq_mul, Pi.div_apply]; ring]
      exact directionalDeriv2_smul f x x (1/2)
    have hny_eq : (x + -y) / 2 = (x - y) / 2 := by
      ext i; simp [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.div_apply]; ring
    -- Extract: |D²_{x+w}| ≤ 4CM using smul
    have hb : ∀ (w : Fin n → ℝ), w ∈ Hypercube n →
        |directionalDeriv2 f x (x + w)| ≤ 4 * C * polySupNorm f := by
      intro w hw
      have hbd := h_bound_w w hw
      have hsmul : directionalDeriv2 f x ((x + w) / 2) =
          (1/2)^2 * directionalDeriv2 f x (x + w) := by
        rw [show (x + w) / 2 = (1/2 : ℝ) • (x + w) from by
          ext i; simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.div_apply]; ring]
        exact directionalDeriv2_smul f x (x + w) (1/2)
      rw [hsmul] at hbd
      rw [abs_mul] at hbd
      have h14 : |(1 / 2 : ℝ) ^ 2| = 1 / 4 := by norm_num
      rw [h14] at hbd
      have := abs_nonneg (directionalDeriv2 f x (x + w)); nlinarith
    have hb1 := hb y hy_hyp
    have hb2 := hb (-y) hny_hyp
    have hb3 := hb 0 h0_hyp
    rw [show x + (0 : Fin n → ℝ) = x from by ext i; simp] at hb3
    -- Step 3: By polarization with u=x, v=y:
    -- D²_{x+y} + D²_{x-y} = 2D²_x + 2D²_y
    -- So D²_y = (D²_{x+y} + D²_{x-y} - 2D²_x) / 2
    have hpol := directionalDeriv2_polarization f x x y
    -- hpol: D²_{x+y} + D²_{x-y} = 2D²_x + 2D²_y
    -- Convert hb2 from x+(-y) to x-y
    have hxmy : x + (-y) = x - y := by ext i; simp [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
    rw [hxmy] at hb2
    -- |2D²_y| = |D²_{x+y} + D²_{x-y} - 2D²_x|
    have h2Dy : 2 * directionalDeriv2 f x y =
        directionalDeriv2 f x (x + y) + directionalDeriv2 f x (x - y) -
        2 * directionalDeriv2 f x x := by linarith
    calc |directionalDeriv2 f x y|
        = |2 * directionalDeriv2 f x y| / 2 := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; ring
      _ = |(directionalDeriv2 f x (x + y) + directionalDeriv2 f x (x - y) -
            2 * directionalDeriv2 f x x)| / 2 := by rw [h2Dy]
      _ ≤ (|directionalDeriv2 f x (x + y)| + |directionalDeriv2 f x (x - y)| +
            |2 * directionalDeriv2 f x x|) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 2).le
          calc |_ + _ - _| ≤ |_ + _| + |2 * directionalDeriv2 f x x| := abs_sub _ _
            _ ≤ |directionalDeriv2 f x (x + y)| + |directionalDeriv2 f x (x - y)| +
                |2 * directionalDeriv2 f x x| := by
                linarith [abs_add_le (directionalDeriv2 f x (x + y))
                  (directionalDeriv2 f x (x - y))]
      _ ≤ (4*C*polySupNorm f + 4*C*polySupNorm f + 2*(4*C*polySupNorm f)) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 2).le
          have : |2 * directionalDeriv2 f x x| ≤ 2 * (4*C*polySupNorm f) := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
            linarith
          linarith [hb1, hb2]
      _ = 8 * C * polySupNorm f := by ring

/-- **Multivariate Markov k=2, exterior, with constant 8.**
    |D̂²_y f(x)| ≤ 8 · d⁴ · |T_d(s)| · polySupNorm f
    for ‖x‖∞ ≤ s, s ≥ 1, ‖y‖∞ ≤ 1. -/
theorem multivariate_markov_k2_exterior_weak
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (x y : Fin n → ℝ) (hy : linftyNorm y ≤ 1)
    (s : ℝ) (hs : 1 ≤ s) (hx : linftyNorm x ≤ s) :
    |directionalDeriv2 f x y| ≤
      8 * (d : ℝ) ^ 4 * |(chebyshevT d).eval s| * polySupNorm f := by
  by_cases hd1 : d ≤ 1
  · have hF_deg : (univariateRestriction f x y).natDegree ≤ 1 :=
      (univariateRestriction_natDegree_le f x y).trans (hd.trans hd1)
    have hF'_deg : (Polynomial.derivative (univariateRestriction f x y)).natDegree = 0 :=
      Nat.le_zero.mp ((Polynomial.natDegree_derivative_le _).trans (by omega))
    unfold directionalDeriv2
    rw [Polynomial.derivative_of_natDegree_zero hF'_deg, Polynomial.eval_zero, abs_zero]
    apply mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) (by positivity))
      (abs_nonneg _)) (polySupNorm_nonneg f)
  · push_neg at hd1
    have hy_le : linftyNorm y ≤ s := le_trans hy hs
    have hny_le : linftyNorm (-y) ≤ s := by
      rw [show (-y) = (-1 : ℝ) • y from by ext i; simp]
      rw [linftyNorm_le_iff (by linarith : 0 ≤ s)]; intro i
      simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul, abs_neg]
      exact le_trans (le_trans (abs_le_linftyNorm y i) hy) hs
    have h0_le : linftyNorm (0 : Fin n → ℝ) ≤ s := by
      rw [linftyNorm_le_iff (by linarith : 0 ≤ s)]; intro i; simp; linarith
    set C := (d : ℝ) ^ 4
    have hC_nn : 0 ≤ C := by positivity
    -- |D²_{x+w}| ≤ 4C|T_d(s)|M via φ-trick + scaled sup norm
    have hb : ∀ (w : Fin n → ℝ), linftyNorm w ≤ s →
        |directionalDeriv2 f x (x + w)| ≤
          4 * C * |(chebyshevT d).eval s| * polySupNorm f := by
      intro w hw
      have hbd := phi_supNorm_le_scaled f d hd x w s hs hx hw
      have hdeg := (univariateRestriction_natDegree_le f ((x-w)/2) ((x+w)/2)).trans hd
      have hmarkov := univariate_markov_second_derivative_weak
        (univariateRestriction f ((x-w)/2) ((x+w)/2)) d hdeg 1 (by norm_num)
      rw [phi_deriv2_at_one] at hmarkov
      have hsmul : directionalDeriv2 f x ((x + w) / 2) =
          (1/2)^2 * directionalDeriv2 f x (x + w) := by
        rw [show (x + w) / 2 = (1/2 : ℝ) • (x + w) from by
          ext i; simp [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.div_apply]; ring]
        exact directionalDeriv2_smul f x (x + w) (1/2)
      rw [hsmul, abs_mul] at hmarkov
      have h14 : |(1 / 2 : ℝ) ^ 2| = 1 / 4 := by norm_num
      rw [h14] at hmarkov
      -- hmarkov: 1/4 |D²| ≤ C * supNormUni
      -- hbd: supNormUni ≤ |T_d(s)| * polySupNorm f
      -- Chain: 1/4 |D²| ≤ C * |T_d(s)| * M
      have hchain : C * polySupNormUni (univariateRestriction f ((x-w)/2) ((x+w)/2)) ≤
          C * (|(chebyshevT d).eval s| * polySupNorm f) :=
        mul_le_mul_of_nonneg_left hbd hC_nn
      have hab := abs_nonneg (directionalDeriv2 f x (x + w))
      calc |directionalDeriv2 f x (x + w)|
          = 4 * (1/4 * |directionalDeriv2 f x (x + w)|) := by ring
        _ ≤ 4 * (C * polySupNormUni (univariateRestriction f ((x-w)/2) ((x+w)/2))) := by
            have : 4 * (1 / 4 * |directionalDeriv2 f x (x + w)|) ≤
                4 * (C * polySupNormUni (univariateRestriction f ((x-w)/2) ((x+w)/2))) :=
              mul_le_mul_of_nonneg_left hmarkov (by norm_num)
            linarith
        _ ≤ 4 * (C * (|(chebyshevT d).eval s| * polySupNorm f)) := by
            nlinarith
        _ = 4 * C * |(chebyshevT d).eval s| * polySupNorm f := by ring
    have hb1 := hb y hy_le
    have hb2 := hb (-y) hny_le
    have hb3 := hb 0 h0_le
    rw [show x + (0 : Fin n → ℝ) = x from by ext i; simp] at hb3
    have hxmy : x + (-y) = x - y := by
      ext i; simp [Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
    rw [hxmy] at hb2
    have hpol := directionalDeriv2_polarization f x x y
    have h2Dy : 2 * directionalDeriv2 f x y =
        directionalDeriv2 f x (x + y) + directionalDeriv2 f x (x - y) -
        2 * directionalDeriv2 f x x := by linarith
    set M := 4 * C * |(chebyshevT d).eval s| * polySupNorm f
    calc |directionalDeriv2 f x y|
        = |2 * directionalDeriv2 f x y| / 2 := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; ring
      _ = |(directionalDeriv2 f x (x + y) + directionalDeriv2 f x (x - y) -
            2 * directionalDeriv2 f x x)| / 2 := by rw [h2Dy]
      _ ≤ (|directionalDeriv2 f x (x + y)| + |directionalDeriv2 f x (x - y)| +
            |2 * directionalDeriv2 f x x|) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 2).le
          calc |_ + _ - _| ≤ |_ + _| + |2 * directionalDeriv2 f x x| := abs_sub _ _
            _ ≤ |directionalDeriv2 f x (x + y)| + |directionalDeriv2 f x (x - y)| +
                |2 * directionalDeriv2 f x x| := by
                linarith [abs_add_le (directionalDeriv2 f x (x + y))
                  (directionalDeriv2 f x (x - y))]
      _ ≤ (M + M + 2*M) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 2).le
          have : |2 * directionalDeriv2 f x x| ≤ 2 * M := by
            rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
          linarith [hb1, hb2]
      _ = 2 * M := by ring
      _ = 8 * (d : ℝ) ^ 4 * |(chebyshevT d).eval s| * polySupNorm f := by
          change 2 * (4 * C * |(chebyshevT d).eval s| * polySupNorm f) = _; ring

/-! ## Perturbation bound (suboptimal, factor 2 worse than optimal) -/

/-- Extended perturbation bound with suboptimal constant:
    |f(z) - f(ẑ)| ≤ 2𝔠 · d² · ε · ‖f‖ for ẑ ∈ B^n, ‖z-ẑ‖_∞ ≤ ε ≤ 1/d².
    Factor 2 worse than optimal due to using multivariate_markov_k1_exterior_weak. -/
theorem markov_perturbation_extended_weak
    (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (hd : f.totalDegree ≤ d)
    (z : Fin n → ℝ) (z_hat : Fin n → ℝ)
    (hz_hat : z_hat ∈ Hypercube n)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / (d : ℝ) ^ 2)
    (hclose : ∀ i, |z i - z_hat i| ≤ ε) :
    |MvPolynomial.eval z f - MvPolynomial.eval z_hat f| ≤
      2 * constCChebyshev * d ^ 2 * ε * polySupNorm f := by
  set v := z - z_hat with hv_def
  set w := ε⁻¹ • v with hw_def
  have hw_norm : linftyNorm w ≤ 1 := by
    rw [linftyNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    simp only [hw_def, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hε_pos]
    rw [inv_mul_le_iff₀ hε_pos]
    calc |v i| = |z i - z_hat i| := by simp [hv_def, Pi.sub_apply]
      _ ≤ ε := hclose i
      _ = ε * 1 := (mul_one ε).symm
  set F := univariateRestriction f z_hat w with hF_def
  have hF0 : F.eval 0 = MvPolynomial.eval z_hat f := by
    rw [hF_def, univariateRestriction_eval]; simp
  have hFε : F.eval ε = MvPolynomial.eval z f := by
    rw [hF_def, univariateRestriction_eval]
    have : z_hat + ε • w = z := by
      ext i; simp only [hw_def, hv_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      field_simp; ring
    rw [this]
  rw [← hFε, ← hF0]
  set s := 1 + ε with hs_def
  have hs_ge : 1 ≤ s := le_add_of_nonneg_right hε_pos.le
  have hT_bound : |(chebyshevT d).eval s| ≤ constCChebyshev :=
    chebyshevT_one_plus_le_constCChebyshev d ε hε_pos.le hε_le
  have hderiv_bound : ∀ t ∈ Set.Icc 0 ε,
      |(Polynomial.derivative F).eval t| ≤
        2 * (d : ℝ) ^ 2 * constCChebyshev * polySupNorm f := by
    intro t ht
    rw [hF_def, univariateRestriction_deriv_eq_directionalDeriv]
    have h_norm_le_s : linftyNorm (z_hat + t • w) ≤ s := by
      rw [linftyNorm_le_iff (by linarith : 0 ≤ s)]
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |z_hat i + t * w i|
          ≤ |z_hat i| + |t * w i| := abs_add_le _ _
        _ = |z_hat i| + |t| * |w i| := by rw [abs_mul]
        _ ≤ 1 + ε * 1 := by
            have hzh : |z_hat i| ≤ 1 := by
              have := (linftyNorm_mem_hypercube_iff z_hat).mp hz_hat
              exact le_trans (abs_le_linftyNorm z_hat i) this
            have ht_le : |t| ≤ ε := by
              rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
            have hw_le : |w i| ≤ 1 := by
              exact le_trans (abs_le_linftyNorm w i) hw_norm
            nlinarith [abs_nonneg (w i)]
        _ = s := by rw [hs_def, mul_one]
    calc |directionalDeriv f (z_hat + t • w) w|
        ≤ 2 * d ^ 2 * |(chebyshevT d).eval s| * polySupNorm f :=
          multivariate_markov_k1_exterior_weak f d hd _ w hw_norm s hs_ge h_norm_le_s
      _ ≤ 2 * d ^ 2 * constCChebyshev * polySupNorm f := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left hT_bound (by positivity)
          · exact polySupNorm_nonneg f
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope
    (fun t => F.eval t) (fun t => (Polynomial.derivative F).eval t) hε_pos
    F.continuous.continuousOn
    (fun t _ => F.hasDerivAt t)
  have hc_icc : c ∈ Set.Icc 0 ε := Set.Ioo_subset_Icc_self hc_mem
  have hsub_eq : F.eval ε - F.eval 0 = (Polynomial.derivative F).eval c * ε := by
    have := hc_eq; rw [sub_zero] at this; rw [this]; field_simp
  rw [hsub_eq, abs_mul, abs_of_pos hε_pos]
  calc |(Polynomial.derivative F).eval c| * ε
      ≤ (2 * (d : ℝ) ^ 2 * constCChebyshev * polySupNorm f) * ε :=
        mul_le_mul_of_nonneg_right (hderiv_bound c hc_icc) hε_pos.le
    _ = 2 * constCChebyshev * d ^ 2 * ε * polySupNorm f := by ring


end OptimalConvergenceRates

end
