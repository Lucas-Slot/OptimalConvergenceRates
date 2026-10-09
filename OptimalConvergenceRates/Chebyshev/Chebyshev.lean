/-
  OptimalConvergenceRates/Chebyshev/Chebyshev.lean

  Univariate and multivariate Chebyshev polynomials, coefficients, orthogonality, and Parseval identities.
-/
import OptimalConvergenceRates.BasicNotions.Defs
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Data.Sym.Card
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.MvPolynomial

open MvPolynomial Finset Polynomial MeasureTheory

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Univariate Chebyshev polynomials -/

/-- Chebyshev polynomial of the first kind, defined by recurrence:
    T_0(x) = 1, T_1(x) = x, T_{n+2}(x) = 2x·T_{n+1}(x) - T_n(x)
    (see https://en.wikipedia.org/wiki/Chebyshev_polynomials) -/
noncomputable def chebyshevT : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 => 2 * Polynomial.X * chebyshevT (n + 1) - chebyshevT n

@[simp] theorem chebyshevT_zero : chebyshevT 0 = 1 := rfl
@[simp] theorem chebyshevT_one : chebyshevT 1 = Polynomial.X := rfl
theorem chebyshevT_succ_succ (n : ℕ) :
    chebyshevT (n + 2) = 2 * Polynomial.X * chebyshevT (n + 1) - chebyshevT n := rfl

/-- Trigonometric characterization: T_k(cos θ) = cos(kθ).
    Proof by strong induction using cos addition formulas. -/
theorem chebyshevT_cos (k : ℕ) (θ : ℝ) :
    (chebyshevT k).eval (Real.cos θ) = Real.cos (k * θ) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => simp [chebyshevT_zero, Real.cos_zero]
    | 1 => simp [chebyshevT_one]
    | k + 2 =>
      rw [chebyshevT_succ_succ]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_ofNat, Polynomial.eval_X]
      rw [ih (k + 1) (by omega), ih k (by omega)]
      have hcast1 : (↑(k + 1) : ℝ) = ↑k + 1 := by push_cast; ring
      have hcast2 : (↑(k + 2) : ℝ) = ↑k + 2 := by push_cast; ring
      rw [hcast1, hcast2]
      have h1 := Real.cos_add θ ((↑k + 1) * θ)
      have h2 := Real.cos_sub θ ((↑k + 1) * θ)
      have heq1 : θ + (↑k + 1) * θ = (↑k + 2) * θ := by ring
      have heq2 : θ - (↑k + 1) * θ = -((↑k : ℝ) * θ) := by ring
      rw [heq1] at h1; rw [heq2, Real.cos_neg] at h2
      linarith

/-- T_k(1) = 1 for all k -/
theorem chebyshevT_eval_one (k : ℕ) : (chebyshevT k).eval 1 = 1 := by
  have h := chebyshevT_cos k 0
  simp only [Real.cos_zero, mul_zero] at h
  exact h

/-- |T_k(x)| ≤ 1 for x ∈ [-1, 1] -/
theorem chebyshevT_abs_le_one (k : ℕ) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |(chebyshevT k).eval x| ≤ 1 := by
  rw [(Real.cos_arccos hx1 hx2).symm]
  rw [chebyshevT_cos]
  exact Real.abs_cos_le_one _

/-! ## Degree and leading coefficient of Chebyshev polynomials -/

private theorem chebyshevT_ne_zero (k : ℕ) : chebyshevT k ≠ 0 := by
  intro h; have := chebyshevT_eval_one k
  rw [h, Polynomial.eval_zero] at this; linarith

private lemma two_poly_ne_zero : (2 : Polynomial ℝ) ≠ 0 := by
  intro h; have : (2 : Polynomial ℝ).eval 0 = (0 : Polynomial ℝ).eval 0 := by rw [h]
  simp at this

private lemma two_X_ne_zero : (2 * Polynomial.X : Polynomial ℝ) ≠ 0 :=
  mul_ne_zero two_poly_ne_zero X_ne_zero

private lemma natDegree_two_X :
    (2 * Polynomial.X : Polynomial ℝ).natDegree = 1 := by
  rw [Polynomial.natDegree_mul two_poly_ne_zero X_ne_zero,
      @Polynomial.natDegree_ofNat _ _ 2 _, Polynomial.natDegree_X]

private lemma leadingCoeff_two_X :
    (2 * Polynomial.X : Polynomial ℝ).leadingCoeff = 2 := by
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X, mul_one,
      Polynomial.leadingCoeff, @Polynomial.natDegree_ofNat _ _ 2 _]; simp

theorem natDegree_chebyshevT (k : ℕ) : (chebyshevT k).natDegree = k := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => simp [chebyshevT_zero]
    | 1 => simp [chebyshevT_one]
    | k + 2 =>
      rw [chebyshevT_succ_succ]
      have hprod_deg :
          (2 * Polynomial.X * chebyshevT (k + 1)).natDegree = k + 2 := by
        rw [Polynomial.natDegree_mul two_X_ne_zero (chebyshevT_ne_zero _),
            natDegree_two_X, ih (k + 1) (by omega)]; omega
      have hlt : (chebyshevT k).natDegree <
          (2 * Polynomial.X * chebyshevT (k + 1)).natDegree := by
        rw [hprod_deg, ih k (by omega)]; omega
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hprod_deg]

theorem leadingCoeff_chebyshevT_pos (k : ℕ) :
    0 < (chebyshevT k).leadingCoeff := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => simp [chebyshevT_zero, Polynomial.leadingCoeff]
    | 1 => simp [chebyshevT_one]
    | k + 2 =>
      rw [chebyshevT_succ_succ]
      have hnat_lt : (chebyshevT k).natDegree <
          (2 * Polynomial.X * chebyshevT (k + 1)).natDegree := by
        rw [Polynomial.natDegree_mul two_X_ne_zero (chebyshevT_ne_zero _),
            natDegree_two_X, natDegree_chebyshevT,
            natDegree_chebyshevT]; omega
      have hdeg_lt : (chebyshevT k).degree <
          (2 * Polynomial.X * chebyshevT (k + 1)).degree :=
        Polynomial.degree_lt_degree hnat_lt
      rw [Polynomial.leadingCoeff_sub_of_degree_lt hdeg_lt,
          Polynomial.leadingCoeff_mul, leadingCoeff_two_X]
      exact mul_pos two_pos (ih (k + 1) (by omega))

theorem chebyshevT_mem_degreeLT (k : ℕ) (r : ℕ) (hk : k ≤ r) :
    chebyshevT k ∈ Polynomial.degreeLT ℝ (r + 1) := by
  rw [Polynomial.mem_degreeLT]
  exact lt_of_le_of_lt (Polynomial.degree_le_natDegree)
    (by rw [natDegree_chebyshevT]; exact Nat.cast_lt.mpr (by omega))

/-! ## Chebyshev measure and inner product -/

/-- The univariate Chebyshev measure density: 1/(π√(1-x²)) -/
noncomputable def chebyshevDensity (x : ℝ) : ℝ :=
  1 / (Real.pi * Real.sqrt (1 - x ^ 2))

/-- The Chebyshev inner product on univariate polynomials, via angular parameterization:
    ⟨f, g⟩ = (1/π) ∫₀^π f(cos θ) g(cos θ) dθ
    Equivalent to ∫_{-1}^{1} f(x)g(x) dx/(π√(1-x²)) by x = cos θ. -/
noncomputable def chebyInner (f g : Polynomial ℝ) : ℝ :=
  (1 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi,
    f.eval (Real.cos θ) * g.eval (Real.cos θ)

/-! ## Relating our chebyshevT to Mathlib's Polynomial.Chebyshev.T -/

/-- Our `chebyshevT k` equals Mathlib's `Polynomial.Chebyshev.T ℝ k`. -/
theorem chebyshevT_eq_T_nat (k : ℕ) :
    chebyshevT k = Polynomial.Chebyshev.T ℝ (k : ℤ) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => simp [chebyshevT_zero, Polynomial.Chebyshev.T_zero]
    | 1 => simp [chebyshevT_one, Polynomial.Chebyshev.T_one]
    | k + 2 =>
      rw [chebyshevT_succ_succ, ih (k + 1) (by omega), ih k (by omega)]
      have h1 : (↑(k + 2) : ℤ) = (↑k : ℤ) + 2 := by omega
      have h2 : (↑(k + 1) : ℤ) = (↑k : ℤ) + 1 := by omega
      rw [h1, h2, Polynomial.Chebyshev.T_add_two]

/-! ## Orthogonality relations -/

/-- Univariate Chebyshev orthogonality:
    ⟨T_a, T_b⟩ = 0 if a ≠ b, 1 if a=b=0, 1/2 if a=b≠0 -/
theorem chebyshevT_orthogonality (a b : ℕ) :
    chebyInner (chebyshevT a) (chebyshevT b) =
      if a ≠ b then 0
      else if a = 0 then 1
      else 1 / 2 := by
  -- Unfold chebyInner
  unfold chebyInner
  -- Rewrite using chebyshevT_cos to get cos(aθ)cos(bθ)
  simp_rw [chebyshevT_cos]
  -- Rewrite cos(aθ)cos(bθ) using product-to-sum formula via Mathlib's T
  -- Key: ∫₀^π cos(aθ)cos(bθ) dθ = (1/2)(∫₀^π cos((a-b)θ) dθ + ∫₀^π cos((a+b)θ) dθ)
  -- We use Mathlib's Chebyshev orthogonality results indirectly
  -- via: T_k(cos θ) = cos(kθ), and measureT integral = ∫₀^π f(cos θ) dθ
  -- Strategy: relate back to measureT integrals
  have key : ∀ (n m : ℕ),
      ∫ θ in (0 : ℝ)..Real.pi, Real.cos (↑n * θ) * Real.cos (↑m * θ) =
      ∫ x, (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x *
        (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x
          ∂Polynomial.Chebyshev.measureT := by
    intro n m
    rw [Polynomial.Chebyshev.integral_measureT_eq_integral_cos_of_continuous (by fun_prop)]
    congr 1; ext θ
    simp [Polynomial.Chebyshev.T_real_cos]
  rw [key a b]
  -- Now case-split
  by_cases hab : a ≠ b
  · -- a ≠ b: integral = 0
    rw [if_pos hab]
    rw [Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hab,
        mul_zero]
  · push_neg at hab; subst hab
    rw [if_neg (not_not.mpr rfl)]
    by_cases ha : a = 0
    · -- a = b = 0: integral = π
      subst ha
      rw [if_pos rfl]
      simp only [Nat.cast_zero] at *
      rw [Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero]
      rw [div_mul_cancel₀ _ (ne_of_gt Real.pi_pos)]
    · -- a = b ≠ 0: integral = π/2
      rw [if_neg ha]
      rw [Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero ha]
      field_simp

/-! ## Multivariate Chebyshev polynomials -/

/-- The multivariate Chebyshev polynomial T_κ(x) = ∏_i T_{κ_i}(x_i).
    Built from our custom univariate Chebyshev polynomials. -/
noncomputable def chebyshevMulti (κ : Fin n → ℕ) : MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin n, embedUnivariate i (chebyshevT (κ i))

theorem eval_embedUnivariate (i : Fin n) (p : Polynomial ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (embedUnivariate i p) = Polynomial.eval (x i) p := by
  change MvPolynomial.eval x (p.toMvPolynomial i) = Polynomial.eval (x i) p
  exact MvPolynomial.eval_toMvPolynomial x i p

/-- T_κ is bounded by 1 on the hypercube -/
theorem chebyshevMulti_bounded (κ : Fin n → ℕ) (x : Fin n → ℝ)
    (hx : x ∈ Hypercube n) :
    |MvPolynomial.eval x (chebyshevMulti κ)| ≤ 1 := by
  simp only [chebyshevMulti, map_prod]
  rw [abs_prod]
  apply Finset.prod_le_one (fun i _ => abs_nonneg _)
  intro i _
  rw [eval_embedUnivariate]
  have hi : x i ∈ Set.Icc (-1 : ℝ) 1 := hx i trivial
  exact chebyshevT_abs_le_one (κ i) (x i) hi.1 hi.2

/-- T_κ(1,...,1) = 1 for all κ -/
theorem chebyshevMulti_eval_one (κ : Fin n → ℕ) :
    MvPolynomial.eval (fun _ => (1 : ℝ)) (chebyshevMulti κ) = 1 := by
  simp only [chebyshevMulti, map_prod]
  apply Finset.prod_eq_one
  intro i _
  rw [eval_embedUnivariate]
  exact chebyshevT_eval_one (κ i)

/-- Evaluating T_κ at (cos θ₁, ..., cos θ_n) gives ∏ cos(κ_i θ_i). -/
theorem eval_chebyshevMulti_cos {n : ℕ} (κ : Fin n → ℕ) (θ : Fin n → ℝ) :
    MvPolynomial.eval (fun i => Real.cos (θ i)) (chebyshevMulti κ) =
    ∏ i : Fin n, Real.cos (↑(κ i) * θ i) := by
  simp only [chebyshevMulti, map_prod, eval_embedUnivariate, chebyshevT_cos]

/-! ## Multivariate Chebyshev inner product -/

/-- The multivariate Chebyshev inner product as an integral:
    ⟨f, g⟩ = (1/π)^n ∫_{[0,π]^n} f(cos θ) g(cos θ) dθ -/
noncomputable def chebyInnerMulti {n : ℕ}
    (f g : MvPolynomial (Fin n) ℝ) : ℝ :=
  (1 / Real.pi) ^ n *
  ∫ θ : Fin n → ℝ,
    MvPolynomial.eval (fun i => Real.cos (θ i)) f *
    MvPolynomial.eval (fun i => Real.cos (θ i)) g
    ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc 0 Real.pi)))

/-! ## Hamming weight -/

/-- The Hamming weight w(κ) = |{i : κ_i ≠ 0}| -/
def hammingWeight (κ : Fin n → ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun i => κ i ≠ 0))

theorem hammingWeight_le_n (κ : Fin n → ℕ) : hammingWeight κ ≤ n := by
  unfold hammingWeight
  calc Finset.card (Finset.univ.filter (fun i => κ i ≠ 0))
      ≤ Finset.card (Finset.univ : Finset (Fin n)) := Finset.card_filter_le _ _
    _ = n := Finset.card_fin n

theorem hammingWeight_zero : hammingWeight (fun (_ : Fin n) => 0) = 0 := by
  simp [hammingWeight]

/-! ## Multi-index set ℕ^n_d -/

/-- The total degree of a multi-index κ : |κ| = ∑ κ_i -/
def multiDegree (κ : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, κ i

/-- The set of multi-indices with total degree ≤ d:
    ℕ^n_d = {κ ∈ ℕ^n : |κ| ≤ d} -/
noncomputable def multiIndices (n d : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (d + 1))).filter
    (fun κ => multiDegree κ ≤ d)

theorem multiIndices_mem_iff {d : ℕ} {κ : Fin n → ℕ} :
    κ ∈ multiIndices n d ↔ multiDegree κ ≤ d ∧ ∀ i, κ i ≤ d := by
  unfold multiIndices
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · intro ⟨hrange, hdeg⟩
    exact ⟨hdeg, fun i => Nat.lt_succ_iff.mp (hrange i)⟩
  · intro ⟨hdeg, hle⟩
    exact ⟨fun i => Nat.lt_succ_iff.mpr (hle i), hdeg⟩

/-- Upper bound on the cardinality: |ℕ^n_d| ≤ (d+1)^n -/
theorem multiIndices_card_le_pow (n d : ℕ) :
    (multiIndices n d).card ≤ (d + 1) ^ n := by
  unfold multiIndices
  calc (Finset.filter _ _).card
      ≤ (Fintype.piFinset (fun _ : Fin n => Finset.range (d + 1))).card :=
        Finset.card_filter_le _ _
    _ = (d + 1) ^ n := by simp [Fintype.card_piFinset, Finset.card_range]

/-- The key combinatorial inequality: C(n+d, d) ≤ (n+1)^d.
    Proof by double induction on n and d, using Pascal's rule. -/
private theorem choose_add_le_pow : ∀ n d : ℕ, Nat.choose (n + d) d ≤ (n + 1) ^ d := by
  intro n
  induction n with
  | zero => intro d; simp
  | succ n ihn =>
    intro d
    induction d with
    | zero => simp
    | succ d ihd =>
      have hm : n + 1 + (d + 1) = (n + d + 1) + 1 := by omega
      rw [hm, Nat.choose_succ_succ]
      have h2 : n + d + 1 = (n + 1) + d := by omega
      have h3 : n + d + 1 = n + (d + 1) := by omega
      have hfirst : Nat.choose (n + d + 1) d ≤ (n + 2) ^ d := h2 ▸ ihd
      have hsecond : Nat.choose (n + d + 1) (d + 1) ≤ (n + 1) ^ (d + 1) := h3 ▸ ihn (d + 1)
      calc Nat.choose (n + d + 1) d + Nat.choose (n + d + 1) (d + 1)
          ≤ (n + 2) ^ d + (n + 1) ^ (d + 1) :=
            Nat.add_le_add hfirst hsecond
        _ = (n + 2) ^ d + (n + 1) ^ d * (n + 1) := by rw [pow_succ]
        _ ≤ (n + 2) ^ d + (n + 2) ^ d * (n + 1) := by
            apply Nat.add_le_add_left
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) d)
        _ = (n + 2) ^ d * (1 + (n + 1)) := by ring
        _ = (n + 2) ^ d * (n + 2) := by congr 1; omega
        _ = (n + 2) ^ (d + 1) := (pow_succ (n + 2) d).symm

/-- Alternate upper bound: |ℕ^n_d| ≤ (n+1)^d -/
theorem multiIndices_card_le_pow' (n d : ℕ) :
    (multiIndices n d).card ≤ (n + 1) ^ d := by
  let f : (Fin n → ℕ) → (Fin (n + 1) → ℕ) := fun κ => Fin.snoc κ (d - multiDegree κ)
  have h_inj : ∀ κ ∈ multiIndices n d,
      f κ ∈ Finset.Nat.antidiagonalTuple (n + 1) d := by
    intro κ hκ
    simp only [f, Finset.Nat.mem_antidiagonalTuple, Fin.sum_snoc]
    have hdeg := (multiIndices_mem_iff.mp hκ).1
    unfold multiDegree at hdeg ⊢
    omega
  have h_inj' : ∀ κ₁ ∈ multiIndices n d, ∀ κ₂ ∈ multiIndices n d,
      f κ₁ = f κ₂ → κ₁ = κ₂ := by
    intro κ₁ _ κ₂ _ h
    funext i
    have := congr_fun h (Fin.castSucc i)
    simp only [f, Fin.snoc_castSucc] at this
    exact this
  have h_card_le : (multiIndices n d).card ≤ (Finset.Nat.antidiagonalTuple (n + 1) d).card :=
    Finset.card_le_card_of_injOn f h_inj h_inj'
  have h_card_anti : (Finset.Nat.antidiagonalTuple (n + 1) d).card =
      Nat.choose (n + d) d := by
    rw [(Finset.piAntidiag_univ_fin_eq_antidiagonalTuple d (n + 1)).symm,
        ← Finset.map_sym_eq_piAntidiag (Finset.univ : Finset (Fin (n + 1))) d,
        Finset.card_map]
    rw [Finset.sym_univ, Finset.card_univ, Sym.card_sym_eq_choose, Fintype.card_fin]
    congr 1; omega
  calc (multiIndices n d).card
      ≤ (Finset.Nat.antidiagonalTuple (n + 1) d).card := h_card_le
    _ = Nat.choose (n + d) d := h_card_anti
    _ ≤ (n + 1) ^ d := choose_add_le_pow n d

/-- The max Hamming weight over ℕ^n_d is at most min(n, d) -/
theorem hammingWeight_le_of_mem {d : ℕ} {κ : Fin n → ℕ}
    (hκ : κ ∈ multiIndices n d) : hammingWeight κ ≤ min n d := by
  apply le_min (hammingWeight_le_n κ)
  have hdeg := (multiIndices_mem_iff.mp hκ).1
  unfold hammingWeight
  set S := Finset.univ.filter (fun i => κ i ≠ 0)
  calc S.card = ∑ _i ∈ S, 1 := by simp
      _ ≤ ∑ i ∈ S, κ i := Finset.sum_le_sum
          (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hi).2)
      _ ≤ ∑ i : Fin n, κ i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = multiDegree κ := rfl
      _ ≤ d := hdeg

/-! ## Total degree of chebyshevMulti -/

/-- The total degree of chebyshevMulti κ is at most multiDegree κ. -/
theorem chebyshevMulti_totalDegree_le {n : ℕ} (κ : Fin n → ℕ) :
    (chebyshevMulti κ).totalDegree ≤ multiDegree κ := by
  unfold chebyshevMulti multiDegree
  calc (∏ i, embedUnivariate i (chebyshevT (κ i))).totalDegree
      ≤ ∑ i, (embedUnivariate i (chebyshevT (κ i))).totalDegree :=
        MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ i, (chebyshevT (κ i)).natDegree :=
        Finset.sum_le_sum (fun i _ => totalDegree_embedUnivariate i _)
    _ = ∑ i, κ i := by simp [natDegree_chebyshevT]

/-! ## Chebyshev expansion

The multivariate Chebyshev polynomials {T_κ : κ ∈ ℕ^n_r} form a basis for
polynomials of total degree ≤ r. The transition matrix from monomials to
Chebyshev polynomials is upper triangular with nonzero diagonal, hence
invertible. We define the Chebyshev coefficient extraction function via
back-substitution and prove its key properties. -/

/-- Back-substitution to extract Chebyshev coefficients from a univariate
    polynomial. `chebyCoeffUni_aux m p k` = coefficient of T_k in the
    Chebyshev expansion of p (peeling from degree m down to 0). -/
noncomputable def chebyCoeffUni_aux : ℕ → Polynomial ℝ → ℕ → ℝ
  | 0, p, 0 => p.coeff 0
  | 0, _, (_ + 1) => 0
  | (m + 1), p, k =>
    let c := p.coeff (m + 1) / (chebyshevT (m + 1)).leadingCoeff
    if k = m + 1 then c
    else chebyCoeffUni_aux m (p - Polynomial.C c * chebyshevT (m + 1)) k

/-- Additivity of the univariate back-substitution. -/
theorem chebyCoeffUni_aux_add (m : ℕ) (p q : Polynomial ℝ) (k : ℕ) :
    chebyCoeffUni_aux m (p + q) k =
    chebyCoeffUni_aux m p k + chebyCoeffUni_aux m q k := by
  induction m generalizing p q k with
  | zero =>
    match k with
    | 0 => simp [chebyCoeffUni_aux, Polynomial.coeff_add]
    | k + 1 => simp [chebyCoeffUni_aux]
  | succ m ih =>
    simp only [chebyCoeffUni_aux]
    split
    · simp [Polynomial.coeff_add, add_div]
    · have : p + q -
          Polynomial.C ((p + q).coeff (m + 1) /
            (chebyshevT (m + 1)).leadingCoeff) * chebyshevT (m + 1) =
        (p - Polynomial.C (p.coeff (m + 1) /
            (chebyshevT (m + 1)).leadingCoeff) * chebyshevT (m + 1)) +
        (q - Polynomial.C (q.coeff (m + 1) /
            (chebyshevT (m + 1)).leadingCoeff) * chebyshevT (m + 1)) := by
        simp [Polynomial.coeff_add, add_div, Polynomial.C_add, add_mul]; ring
      rw [this, ih]

/-- Scalar multiplication for univariate back-substitution. -/
theorem chebyCoeffUni_aux_smul (m : ℕ) (a : ℝ) (p : Polynomial ℝ)
    (k : ℕ) :
    chebyCoeffUni_aux m (Polynomial.C a * p) k =
    a * chebyCoeffUni_aux m p k := by
  induction m generalizing p k with
  | zero =>
    match k with
    | 0 => simp [chebyCoeffUni_aux]
    | k + 1 => simp [chebyCoeffUni_aux, mul_zero]
  | succ m ih =>
    simp only [chebyCoeffUni_aux]
    split
    · simp [Polynomial.coeff_C_mul, mul_div_assoc]
    · have : Polynomial.C a * p -
          Polynomial.C ((Polynomial.C a * p).coeff (m + 1) /
            (chebyshevT (m + 1)).leadingCoeff) * chebyshevT (m + 1) =
        Polynomial.C a * (p -
          Polynomial.C (p.coeff (m + 1) /
            (chebyshevT (m + 1)).leadingCoeff) * chebyshevT (m + 1)) := by
        simp [Polynomial.coeff_C_mul, mul_div_assoc, Polynomial.C_mul,
              mul_sub, mul_assoc]
      rw [this, ih]

/-- `chebyCoeffUni_aux m 0 k = 0` for all k. -/
private theorem chebyCoeffUni_aux_zero (m k : ℕ) :
    chebyCoeffUni_aux m (0 : Polynomial ℝ) k = 0 := by
  induction m generalizing k with
  | zero =>
    match k with
    | 0 => simp [chebyCoeffUni_aux]
    | _ + 1 => rfl
  | succ m ih =>
    simp only [chebyCoeffUni_aux]
    by_cases h : k = m + 1 <;> simp [h, ih k]

/-- Coefficient of T_j at degree m+1 is zero when j < m+1. -/
private theorem chebyshevT_coeff_of_lt (j m : ℕ) (h : j < m + 1) :
    (chebyshevT j).coeff (m + 1) = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_chebyshevT]; omega)

/-- Back-substitution correctly extracts Chebyshev coefficients from T_j. -/
theorem chebyCoeffUni_aux_chebyshevT (m j k : ℕ) (hj : j ≤ m) :
    chebyCoeffUni_aux m (chebyshevT j) k = if j = k then 1 else 0 := by
  revert j k
  induction m with
  | zero =>
    intro j k hj; simp only [Nat.le_zero] at hj; subst hj
    simp only [chebyshevT_zero]
    match k with | 0 => norm_num [chebyCoeffUni_aux] | _ + 1 => rfl
  | succ m ih =>
    intro j k hj
    by_cases hj_le : j ≤ m
    · -- j ≤ m: coeff(T_j, m+1) = 0, remainder = T_j, recurse
      have hcoeff : (chebyshevT j).coeff (m + 1) = 0 :=
        chebyshevT_coeff_of_lt j m (by omega)
      by_cases hk : k = m + 1
      · have : j ≠ m + 1 := by omega
        simp only [chebyCoeffUni_aux, hk, hcoeff]; simp [this]
      · simp only [chebyCoeffUni_aux, hk, hcoeff, zero_div,
            Polynomial.C_0, zero_mul, sub_zero]
        exact ih j k hj_le
    · -- j = m + 1: extract leading coefficient
      have hj_eq : j = m + 1 := by omega
      subst hj_eq
      have h_coeff : (chebyshevT (m + 1)).coeff (m + 1) =
          (chebyshevT (m + 1)).leadingCoeff := by
        simp [Polynomial.leadingCoeff, natDegree_chebyshevT]
      have h_ne : (chebyshevT (m + 1)).leadingCoeff ≠ 0 :=
        ne_of_gt (leadingCoeff_chebyshevT_pos _)
      by_cases hk : k = m + 1
      · subst hk
        simp only [chebyCoeffUni_aux, ite_true, h_coeff]
        exact div_self h_ne
      · have hc_eq : (chebyshevT (m + 1)).coeff (m + 1) /
            (chebyshevT (m + 1)).leadingCoeff = 1 :=
          div_self h_ne ▸ (by rw [h_coeff])
        simp only [chebyCoeffUni_aux, hk, ite_false, hc_eq,
          Polynomial.C_1, one_mul, sub_self]
        have : ¬(m + 1 = k) := fun c => hk c.symm
        simp [this, chebyCoeffUni_aux_zero]

/-- Chebyshev coefficient: extracts the coefficient of T_κ in the
    Chebyshev expansion of a polynomial p. Defined via back-substitution
    on the monomial decomposition of p. -/
noncomputable def chebyCoeff (n r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (κ : Fin n → ℕ) : ℝ :=
  (p : (Fin n →₀ ℕ) →₀ ℝ).sum fun α c =>
    c * ∏ i : Fin n, chebyCoeffUni_aux r
      (Polynomial.X ^ (α i) : Polynomial ℝ) (κ i)

/-- Additivity of Chebyshev coefficients. -/
theorem chebyCoeff_add {n : ℕ} (r : ℕ) (p q : MvPolynomial (Fin n) ℝ)
    (κ : Fin n → ℕ) :
    chebyCoeff n r (p + q) κ =
      chebyCoeff n r p κ + chebyCoeff n r q κ := by
  simp only [chebyCoeff]
  exact Finsupp.sum_add_index' (fun α => by simp) (fun α _ _ => by ring)

/-- Scalar multiplication: chebyCoeff(C(a) * p, κ) = a * chebyCoeff(p, κ). -/
theorem chebyCoeff_C_mul {n : ℕ} (r : ℕ) (a : ℝ)
    (p : MvPolynomial (Fin n) ℝ) (κ : Fin n → ℕ) :
    chebyCoeff n r (MvPolynomial.C a * p) κ =
      a * chebyCoeff n r p κ := by
  simp only [chebyCoeff, MvPolynomial.C_mul']
  rw [Finsupp.sum_smul_index (fun α => by simp)]
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro α _; ring

/-- `chebyCoeffUni_aux m p k = 0` when `k > m`. -/
theorem chebyCoeffUni_aux_gt (m : ℕ) (p : Polynomial ℝ) (k : ℕ)
    (hk : m < k) : chebyCoeffUni_aux m p k = 0 := by
  induction m generalizing p k with
  | zero =>
    match k, hk with | k + 1, _ => rfl
  | succ m ih =>
    simp only [chebyCoeffUni_aux]
    have hk_ne : k ≠ m + 1 := by omega
    rw [if_neg hk_ne]
    exact ih _ k (by omega)

/-- The remainder `p - C c * T_{m+1}` has `natDegree ≤ m` when `c` cancels the
    leading coefficient. -/
private theorem natDegree_sub_cancel_leading (m : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ m + 1) :
    (p - Polynomial.C (p.coeff (m + 1) / (chebyshevT (m + 1)).leadingCoeff) *
      chebyshevT (m + 1)).natDegree ≤ m := by
  set c := p.coeff (m + 1) / (chebyshevT (m + 1)).leadingCoeff with hc_def
  set q := p - Polynomial.C c * chebyshevT (m + 1) with hq_def
  have h_deg_T : (chebyshevT (m + 1)).natDegree = m + 1 := natDegree_chebyshevT _
  have h_lc_ne : (chebyshevT (m + 1)).leadingCoeff ≠ 0 :=
    ne_of_gt (leadingCoeff_chebyshevT_pos _)
  -- Show all coefficients of q at degree > m are zero
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [hq_def, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  by_cases hj_eq : j = m + 1
  · subst hj_eq
    -- At degree m+1: c * leadingCoeff(T_{m+1}) = p.coeff(m+1)
    have : (chebyshevT (m + 1)).coeff (m + 1) =
        (chebyshevT (m + 1)).leadingCoeff := by
      rw [Polynomial.leadingCoeff, h_deg_T]
    rw [this, hc_def, div_mul_cancel₀ _ h_lc_ne, sub_self]
  · -- At degree j > m+1: both p and T_{m+1} have zero coefficients
    have hj_gt : j > m + 1 := by omega
    have hp_zero : p.coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hT_zero : (chebyshevT (m + 1)).coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [h_deg_T]; omega)
    rw [hp_zero, hT_zero, mul_zero, sub_zero]

/-- Univariate reconstruction: any polynomial of `natDegree ≤ m` equals its
    Chebyshev expansion up to degree `m`. -/
private theorem uni_cheby_reconstruction (m : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ m) :
    p = ∑ k ∈ Finset.range (m + 1),
      Polynomial.C (chebyCoeffUni_aux m p k) * chebyshevT k := by
  induction m generalizing p with
  | zero =>
    rw [Finset.sum_range_one]
    simp only [chebyCoeffUni_aux, chebyshevT_zero, mul_one]
    exact Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hp)
  | succ m ih =>
    set c := p.coeff (m + 1) / (chebyshevT (m + 1)).leadingCoeff with hc_def
    set p' := p - Polynomial.C c * chebyshevT (m + 1) with hp'_def
    have hp'_deg : p'.natDegree ≤ m := natDegree_sub_cancel_leading m p hp
    have ih_p' := ih p' hp'_deg
    -- Key: chebyCoeffUni_aux (m+1) p (m+1) = c
    have h_last : chebyCoeffUni_aux (m + 1) p (m + 1) = c := by
      change (if (m + 1) = (m + 1) then _ else _) = c
      rw [if_pos rfl]
    -- Key: for k ≤ m, chebyCoeffUni_aux (m+1) p k = chebyCoeffUni_aux m p' k
    have h_rest : ∀ k, k ≤ m →
        chebyCoeffUni_aux (m + 1) p k = chebyCoeffUni_aux m p' k := by
      intro k hk
      simp only [chebyCoeffUni_aux]
      rw [if_neg (by omega : k ≠ m + 1)]
    -- Prove RHS = LHS
    -- RHS = ∑ k in range(m+2), C(chebyCoeffUni_aux (m+1) p k) * T_k
    --     = (∑ k in range(m+1), C(chebyCoeffUni_aux (m+1) p k) * T_k) + C(c)*T_{m+1}
    --     = (∑ k in range(m+1), C(chebyCoeffUni_aux m p' k) * T_k) + C(c)*T_{m+1}
    --     = p' + C(c)*T_{m+1} = p
    symm
    calc ∑ k ∈ Finset.range (m + 1 + 1),
          Polynomial.C (chebyCoeffUni_aux (m + 1) p k) * chebyshevT k
        = (∑ k ∈ Finset.range (m + 1),
            Polynomial.C (chebyCoeffUni_aux (m + 1) p k) * chebyshevT k) +
          Polynomial.C (chebyCoeffUni_aux (m + 1) p (m + 1)) * chebyshevT (m + 1) :=
        Finset.sum_range_succ _ _
      _ = (∑ k ∈ Finset.range (m + 1),
            Polynomial.C (chebyCoeffUni_aux m p' k) * chebyshevT k) +
          Polynomial.C c * chebyshevT (m + 1) := by
        congr 1
        · exact Finset.sum_congr rfl fun k hk => by
            rw [h_rest k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
        · rw [h_last]
      _ = p' + Polynomial.C c * chebyshevT (m + 1) := by rw [← ih_p']
      _ = p := by simp [hp'_def]

/-- `embedUnivariate i (C a) = MvPolynomial.C a`. -/
private theorem embedUnivariate_C (i : Fin n) (a : ℝ) :
    embedUnivariate i (Polynomial.C a) = MvPolynomial.C a := by
  simp [embedUnivariate, Polynomial.aeval_C]

/-- `embedUnivariate i (X ^ k) = (MvPolynomial.X i) ^ k`. -/
private theorem embedUnivariate_X_pow (i : Fin n) (k : ℕ) :
    embedUnivariate i (Polynomial.X ^ k) = (MvPolynomial.X i) ^ k := by
  simp [embedUnivariate, map_pow, Polynomial.aeval_X]

/-- `natDegree (X ^ a) = a` for univariate polynomials over ℝ. -/
private theorem natDegree_X_pow_real (a : ℕ) :
    (Polynomial.X ^ a : Polynomial ℝ).natDegree = a := by
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]

/-- `chebyCoeffUni_aux m (X^a) k = 0` when `k > a` and `a ≤ m`. -/
theorem chebyCoeffUni_aux_X_pow_gt_deg (m a k : ℕ)
    (ha : a ≤ m) (hk : a < k) :
    chebyCoeffUni_aux m
      (Polynomial.X ^ a : Polynomial ℝ) k = 0 := by
  induction m with
  | zero =>
    interval_cases a
    match k with | k + 1 => rfl
  | succ m ihm =>
    simp only [chebyCoeffUni_aux]
    by_cases hk_eq : k = m + 1
    · -- k = m + 1, and a < k = m + 1, so a ≤ m, coeff(m+1, X^a) = 0
      subst hk_eq
      have : (Polynomial.X ^ a : Polynomial ℝ).coeff (m + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (by rw [natDegree_X_pow_real]; omega)
      simp [this]
    · rw [if_neg hk_eq]
      by_cases ha_le : a ≤ m
      · have hcoeff :
            (Polynomial.X ^ a : Polynomial ℝ).coeff (m + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [natDegree_X_pow_real]; omega)
        simp only [hcoeff, zero_div, map_zero, zero_mul, sub_zero]
        exact ihm ha_le
      · -- a = m + 1, k > m + 1, k ≠ m + 1, so k > m + 1
        -- The remainder has natDegree ≤ m, and k > m, so result is 0
        have ha_eq : a = m + 1 := by omega
        subst ha_eq
        have hk_gt : k > m := by omega
        exact chebyCoeffUni_aux_gt m _ k hk_gt

/-- If `∑ κ i > ∑ α i` (as functions `Fin n → ℕ`), then `∃ i, κ i > α i`. -/
theorem exists_gt_of_sum_gt {n : ℕ} (α : Fin n →₀ ℕ)
    (κ : Fin n → ℕ)
    (h : (α.sum fun _ e => e) < ∑ i, κ i) :
    ∃ i : Fin n, α i < κ i := by
  by_contra hall
  push_neg at hall
  have hle : ∑ i, κ i ≤ ∑ i, (α i : ℕ) :=
    Finset.sum_le_sum (fun i _ => hall i)
  have heq : ∑ i ∈ Finset.univ, (α i : ℕ) = α.sum fun _ e => e := by
    rw [Finsupp.sum]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun i _ hi => by rwa [Finsupp.mem_support_iff, not_not] at hi)).symm
  omega

/-- chebyCoeff vanishes for multi-indices beyond the polynomial's degree. -/
theorem chebyCoeff_zero_of_degree_lt {n : ℕ} (r : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (κ : Fin n → ℕ)
    (hκ_deg : p.totalDegree < multiDegree κ) :
    chebyCoeff n r p κ = 0 := by
  simp only [chebyCoeff, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro α hα
  have hα_deg : (α.sum fun _ e => e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hα
  have hsum : (α.sum fun _ e => e) < ∑ i, κ i := by unfold multiDegree at hκ_deg; omega
  have hsum_eq : α.sum (fun _ e => e) = ∑ i : Fin n, α i := by
    rw [Finsupp.sum, ← Finset.sum_subset (Finset.subset_univ α.support)]
    intro i _ hi; exact Finsupp.notMem_support_iff.mp hi
  have ⟨i, hi⟩ : ∃ i : Fin n, α i < κ i := by
    by_contra hall; push_neg at hall
    have : ∑ i : Fin n, κ i ≤ ∑ i : Fin n, (α i : ℕ) :=
      Finset.sum_le_sum (fun i _ => hall i)
    omega
  have hzero : chebyCoeffUni_aux r
      (Polynomial.X ^ (α i) : Polynomial ℝ) (κ i) = 0 := by
    by_cases hα_i_le : α i ≤ r
    · exact chebyCoeffUni_aux_X_pow_gt_deg r (α i) (κ i) hα_i_le hi
    · push_neg at hα_i_le
      exact chebyCoeffUni_aux_gt r _ (κ i) (by omega)
  have : ∏ j : Fin n, chebyCoeffUni_aux r
      (Polynomial.X ^ (α j) : Polynomial ℝ) (κ j) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hzero
  simp [this]

/-- Univariate reconstruction applied via embedUnivariate: `X_i^a` can be written
    as a sum of embedded Chebyshev polynomials. -/
private theorem embed_X_pow_cheby_expansion (i : Fin n) (a r : ℕ)
    (ha : a ≤ r) :
    (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ a =
    ∑ k ∈ Finset.range (r + 1),
      MvPolynomial.C (chebyCoeffUni_aux r
        (Polynomial.X ^ a : Polynomial ℝ) k) *
      embedUnivariate i (chebyshevT k) := by
  have hrec := uni_cheby_reconstruction r
    (Polynomial.X ^ a : Polynomial ℝ) (by rw [natDegree_X_pow_real]; exact ha)
  -- Apply embedUnivariate i to both sides
  have := congr_arg (embedUnivariate i) hrec
  rw [embedUnivariate_X_pow, map_sum] at this
  convert this using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, embedUnivariate_C]

/-- Chebyshev expansion: any polynomial of degree ≤ r can be reconstructed
    from its Chebyshev coefficients. -/
theorem chebyshev_expansion {n : ℕ} (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ r) :
    p = ∑ κ ∈ multiIndices n r,
      MvPolynomial.C (chebyCoeff n r p κ) * chebyshevMulti κ := by
  -- Abbreviation
  set h := fun (a k : ℕ) =>
    chebyCoeffUni_aux r (Polynomial.X ^ a : Polynomial ℝ) k
  -- For α ∈ p.support: each α i ≤ r, and Finsupp.sum ≤ r
  have hα_le_r : ∀ α ∈ p.support, ∀ i : Fin n, α i ≤ r := by
    intro α hα i
    by_cases hαi : (α i : ℕ) = 0
    · omega
    · exact le_trans
        (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finsupp.mem_support_iff.mpr hαi))
          (MvPolynomial.le_totalDegree hα)) hp
  have hα_sum_le_r : ∀ α ∈ p.support,
      (α.sum fun _ e => e) ≤ r :=
    fun α hα => le_trans (MvPolynomial.le_totalDegree hα) hp
  -- Key lemma: for each α ∈ p.support,
  -- monomial α (coeff α p) =
  --   ∑ κ ∈ MI, C(coeff α p * ∏ i h(α i)(κ i)) * chebyshevMulti κ
  have monomial_expand :
      ∀ α ∈ p.support,
      MvPolynomial.monomial α (MvPolynomial.coeff α p) =
      ∑ κ ∈ multiIndices n r,
        MvPolynomial.C (MvPolynomial.coeff α p *
          ∏ i, h (α i) (κ i)) *
        chebyshevMulti κ := by
    intro α hα
    -- monomial α c = C c * ∏ i, X_i^(α i)
    have hmon : MvPolynomial.monomial α (MvPolynomial.coeff α p) =
        MvPolynomial.C (MvPolynomial.coeff α p) *
          ∏ i : Fin n,
            (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ (α i) := by
      rw [MvPolynomial.monomial_eq, Finsupp.prod]
      congr 1
      exact Finset.prod_subset (Finset.subset_univ _)
        (fun i _ hi => by
          rw [Finsupp.mem_support_iff, not_not] at hi; simp [hi])
    rw [hmon]
    -- = C(coeff) * ∏ i, X_i^(α i)
    -- Expand each X_i^(α i) via Chebyshev
    have hfactor : ∀ i : Fin n,
        (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ (α i) =
        ∑ k ∈ Finset.range (r + 1),
          MvPolynomial.C (h (α i) k) *
            embedUnivariate i (chebyshevT k) :=
      fun i => embed_X_pow_cheby_expansion i (α i) r (hα_le_r α hα i)
    conv_lhs => arg 2; arg 2; ext i; rw [hfactor i]
    rw [Finset.prod_univ_sum]
    -- = C(coeff) * ∑ κ ∈ piFinset, ∏ i, C(h(α i, κ i)) * embed(T_{κ i})
    -- Factor each summand
    have hsummand : ∀ κ,
        (∏ i, MvPolynomial.C (h (α i) (κ i)) *
          embedUnivariate i (chebyshevT (κ i))) =
        MvPolynomial.C (∏ i, h (α i) (κ i)) * chebyshevMulti κ := by
      intro κ; rw [Finset.prod_mul_distrib, map_prod]; rfl
    simp_rw [hsummand]
    -- = C(coeff) * ∑ κ ∈ piFinset, C(∏ h) * T_κ
    -- Restrict to multiIndices
    have hrestrict :
        ∑ κ ∈ Fintype.piFinset
          (fun _ : Fin n => Finset.range (r + 1)),
          MvPolynomial.C (∏ i, h (α i) (κ i)) * chebyshevMulti κ =
        ∑ κ ∈ multiIndices n r,
          MvPolynomial.C (∏ i, h (α i) (κ i)) * chebyshevMulti κ := by
      symm
      apply Finset.sum_subset
      · -- multiIndices ⊆ piFinset
        intro κ hκ
        rw [Fintype.mem_piFinset]
        intro i; rw [Finset.mem_range]
        exact Nat.lt_succ_of_le ((multiIndices_mem_iff.mp hκ).2 i)
      · -- terms in piFinset \ multiIndices are zero
        intro κ hκ_pi hκ_not_mi
        have hκ_le : ∀ i, κ i ≤ r := fun i =>
          Nat.lt_succ_iff.mp (Finset.mem_range.mp
            (Fintype.mem_piFinset.mp hκ_pi i))
        have hdeg : r < multiDegree κ := by
          by_contra hnd; push_neg at hnd
          exact hκ_not_mi (multiIndices_mem_iff.mpr ⟨hnd, hκ_le⟩)
        have hsum_lt : (α.sum fun _ e => e) < ∑ i, κ i := by
          have := hα_sum_le_r α hα
          unfold multiDegree at hdeg
          exact lt_of_le_of_lt this hdeg
        obtain ⟨i, hi⟩ := exists_gt_of_sum_gt α κ hsum_lt
        have hαi_le : α i ≤ r := hα_le_r α hα i
        have hzero : h (α i) (κ i) = 0 :=
          chebyCoeffUni_aux_X_pow_gt_deg r (α i) (κ i) hαi_le hi
        have hprod_zero : ∏ j : Fin n, h (α j) (κ j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) hzero
        simp [hprod_zero]
    rw [hrestrict]
    -- = C(coeff) * ∑ κ ∈ MI, C(∏ h) * T_κ
    -- Distribute C(coeff) * into the sum
    rw [Finset.mul_sum]
    congr 1; ext κ
    rw [← mul_assoc, ← map_mul]
  -- Main proof: sum of monomial_expand
  conv_lhs => rw [p.as_sum]
  rw [Finset.sum_congr rfl monomial_expand]
  -- LHS = ∑ α, ∑ κ ∈ MI, C(coeff α p * ∏ h) * T_κ
  rw [Finset.sum_comm]
  -- = ∑ κ ∈ MI, ∑ α, C(coeff α p * ∏ h) * T_κ
  congr 1; ext κ
  -- Need: ∑ α, C(coeff α p * ∏ h) * T_κ = C(chebyCoeff n r p κ) * T_κ
  rw [← Finset.sum_mul]
  congr 1
  -- Need: ∑ α, C(coeff α p * ∏ h) = C(chebyCoeff n r p κ)
  rw [← map_sum]
  -- Need: C(∑ α, coeff α p * ∏ h) = C(chebyCoeff n r p κ)
  rfl

/-- `chebyCoeff` of a monomial reduces to a product of univariate extractions. -/
private theorem chebyCoeff_monomial {n : ℕ} (r : ℕ) (α : Fin n →₀ ℕ) (c : ℝ)
    (κ : Fin n → ℕ) :
    chebyCoeff n r (MvPolynomial.monomial α c) κ =
    c * ∏ i : Fin n, chebyCoeffUni_aux r (Polynomial.X ^ (α i)) (κ i) := by
  simp only [chebyCoeff]
  rw [← MvPolynomial.single_eq_monomial]
  rw [Finsupp.sum_single_index]
  · simp

/-- `chebyCoeff` distributes over Finset sums. -/
theorem chebyCoeff_finset_sum {n : ℕ} (r : ℕ) {ι : Type*}
    (S : Finset ι) (f : ι → MvPolynomial (Fin n) ℝ)
    (κ : Fin n → ℕ) :
    chebyCoeff n r (∑ x ∈ S, f x) κ =
    ∑ x ∈ S, chebyCoeff n r (f x) κ := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    have : chebyCoeff n r 0 κ = 0 := by
      have h := chebyCoeff_add r (0 : MvPolynomial (Fin n) ℝ) 0 κ
      simp at h; linarith
    exact this
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, chebyCoeff_add, ih, Finset.sum_insert ha]

/-- Orthogonality: the Chebyshev coefficients of T_μ are delta functions. -/
theorem chebyCoeff_chebyshev {n : ℕ} (r : ℕ) (κ μ : Fin n → ℕ)
    (hκ : κ ∈ multiIndices n r) (hμ : μ ∈ multiIndices n r) :
    chebyCoeff n r (chebyshevMulti μ) κ = if μ = κ then 1 else 0 := by
  -- Step 1: Reduce to product of univariate coefficients
  suffices hprod : chebyCoeff n r (chebyshevMulti μ) κ =
      ∏ i : Fin n, chebyCoeffUni_aux r (chebyshevT (μ i)) (κ i) by
    rw [hprod]
    -- Step 2: Apply chebyCoeffUni_aux_chebyshevT
    have hμ_le : ∀ i, μ i ≤ r := (multiIndices_mem_iff.mp hμ).2
    conv_lhs =>
      arg 2; ext i
      rw [chebyCoeffUni_aux_chebyshevT r (μ i) (κ i) (hμ_le i)]
    -- Step 3: Product of ite
    by_cases h : μ = κ
    · subst h; simp
    · rw [if_neg h]
      have : ∃ i, μ i ≠ κ i := by
        by_contra hall; push_neg at hall
        exact h (funext hall)
      obtain ⟨i, hi⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  -- Step 4: Prove hprod
  -- Abbreviations for polynomial coefficients
  set c : Fin n → ℕ → ℝ := fun i k => (chebyshevT (μ i)).coeff k with hc_def
  set S : Fin n → Finset ℕ := fun i => (chebyshevT (μ i)).support with hS_def
  -- Each embedUnivariate i (chebyshevT (μ i)) expands as a sum of C(c_k) * X_i^k
  have embed_expand : ∀ i : Fin n,
      embedUnivariate i (chebyshevT (μ i)) =
      ∑ k ∈ S i, MvPolynomial.C (c i k) *
        (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ k := by
    intro i
    conv_lhs => rw [(chebyshevT (μ i)).as_sum_support]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, embedUnivariate_C,
        embedUnivariate_X_pow]
  -- Expand chebyshevMulti as product of sums
  have multi_expand : chebyshevMulti μ =
      ∑ f ∈ Fintype.piFinset S,
        MvPolynomial.C (∏ i, c i (f i)) *
        ∏ i, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ (f i) := by
    simp only [chebyshevMulti]
    conv_lhs => arg 2; ext i; rw [embed_expand i]
    rw [Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.prod_mul_distrib, map_prod]
  -- Apply chebyCoeff to multi_expand
  rw [multi_expand, chebyCoeff_finset_sum]
  -- Each term: chebyCoeff of C(coeff_prod) * monomial
  -- Key lemma: ∏ i, X_i^(f i) = monomial (equivFunOnFinite.symm f) 1
  have prod_eq_monomial : ∀ f : Fin n → ℕ,
      ∏ i, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ (f i) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm f) 1 := by
    intro f
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    symm
    rw [Finset.prod_subset (Finset.subset_univ _)]
    · apply Finset.prod_congr rfl
      intro i _
      simp [Finsupp.equivFunOnFinite]
    · intro i _ hi
      rw [Finsupp.mem_support_iff, not_not] at hi
      simp [Finsupp.equivFunOnFinite] at hi
      simp [hi]
  have term_eval : ∀ f ∈ Fintype.piFinset S,
      chebyCoeff n r (MvPolynomial.C (∏ i, c i (f i)) *
        ∏ i, (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ (f i)) κ =
      (∏ i, c i (f i)) *
        ∏ i, chebyCoeffUni_aux r (Polynomial.X ^ (f i)) (κ i) := by
    intro f _
    rw [prod_eq_monomial, MvPolynomial.C_mul_monomial, mul_one,
        chebyCoeff_monomial]
    congr 2 with i
  rw [Finset.sum_congr rfl term_eval]
  -- Now LHS = ∑ f ∈ piFinset S, (∏ i, c i (f i)) * ∏ i, chebyCoeffUni_aux ...
  -- Define the combined function for prod_univ_sum
  set g : Fin n → ℕ → ℝ := fun i k =>
    c i k * chebyCoeffUni_aux r (Polynomial.X ^ k) (κ i) with hg_def
  -- Factor: (∏ i, a_i) * (∏ i, b_i) = ∏ i, (a_i * b_i)
  have hfactor : ∀ f : Fin n → ℕ,
      (∏ i, c i (f i)) * ∏ i, chebyCoeffUni_aux r (Polynomial.X ^ (f i)) (κ i) =
      ∏ i, g i (f i) := by
    intro f; rw [← Finset.prod_mul_distrib]
  simp_rw [hfactor]
  -- LHS = ∑ f ∈ piFinset S, ∏ i, g i (f i)
  -- By prod_univ_sum (reversed):
  rw [← Finset.prod_univ_sum]
  -- Now need: ∀ i, ∑ k ∈ S i, g i k = chebyCoeffUni_aux r (chebyshevT (μ i)) (κ i)
  apply Finset.prod_congr rfl
  intro i _
  simp only [hg_def]
  -- Need: ∑ k ∈ S i, c i k * chebyCoeffUni_aux r (X^k) (κ i) =
  --           chebyCoeffUni_aux r (chebyshevT (μ i)) (κ i)
  -- Use linearity of chebyCoeffUni_aux
  -- chebyshevT (μ i) = ∑ k ∈ S i, C(c i k) * X^k (by as_sum_support)
  have hpoly : chebyshevT (μ i) = ∑ k ∈ S i,
      Polynomial.C (c i k) * Polynomial.X ^ k := by
    conv_lhs => rw [(chebyshevT (μ i)).as_sum_support]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
  symm; rw [hpoly]
  -- Need: chebyCoeffUni_aux r (∑ k ∈ S i, C(c i k) * X^k) (κ i) =
  --       ∑ k ∈ S i, c i k * chebyCoeffUni_aux r (X^k) (κ i)
  -- Distribute chebyCoeffUni_aux over the sum using add + smul
  -- General: chebyCoeffUni_aux distributes over Finset sums by linearity
  suffices hlin : ∀ (T : Finset ℕ) (f : ℕ → Polynomial ℝ),
      chebyCoeffUni_aux r (∑ k ∈ T, f k) (κ i) =
      ∑ k ∈ T, chebyCoeffUni_aux r (f k) (κ i) by
    rw [hlin]
    apply Finset.sum_congr rfl
    intro k _
    rw [chebyCoeffUni_aux_smul]
  intro T
  induction T using Finset.induction with
  | empty => intro _; simp [chebyCoeffUni_aux_zero]
  | @insert a U ha ih =>
    intro f
    rw [Finset.sum_insert ha, chebyCoeffUni_aux_add, ih, Finset.sum_insert ha]

/-- Helper: integral over Icc equals interval integral (for Lebesgue measure on ℝ). -/
private theorem integral_Icc_eq_intervalIntegral (f : ℝ → ℝ) :
    ∫ θ, f θ ∂(volume.restrict (Set.Icc 0 Real.pi)) =
    ∫ θ in (0 : ℝ)..Real.pi, f θ := by
  rw [intervalIntegral.integral_of_le (le_of_lt Real.pi_pos)]
  congr 1
  exact Measure.restrict_congr_set (α := ℝ) (Ioc_ae_eq_Icc' (μ := volume)
    (by simp)).symm

/-- Each factor after Fubini equals the univariate Chebyshev inner product
    (up to the 1/π factor). -/
private theorem factor_eq_chebyInner (a b : ℕ) :
    (1 / Real.pi) * ∫ θ, Real.cos (↑a * θ) * Real.cos (↑b * θ)
      ∂(volume.restrict (Set.Icc 0 Real.pi)) =
    chebyInner (chebyshevT a) (chebyshevT b) := by
  unfold chebyInner
  congr 1
  rw [integral_Icc_eq_intervalIntegral]
  congr 1; ext θ
  rw [chebyshevT_cos, chebyshevT_cos]

/-- Multivariate Chebyshev orthogonality:
    `⟨T_α, T_β⟩ = 2^{-w(α)} · δ_{αβ}`. -/
theorem chebyshevMulti_orthogonality {n : ℕ} (α β : Fin n → ℕ) :
    chebyInnerMulti (chebyshevMulti α) (chebyshevMulti β) =
      if α = β then (2 : ℝ) ^ (-(hammingWeight α : ℤ))
      else 0 := by
  -- Step 1: Unfold and rewrite evals
  unfold chebyInnerMulti
  simp_rw [eval_chebyshevMulti_cos]
  -- Step 2: Combine products ∏ cos(α_i θ_i) * ∏ cos(β_i θ_i) = ∏ (cos(α_i θ_i) * cos(β_i θ_i))
  simp_rw [← Finset.prod_mul_distrib]
  -- Step 3: Apply Fubini
  -- We need to match the integrand to the form ∏ i, f i (θ i)
  have fubini : ∫ θ : Fin n → ℝ,
      ∏ i : Fin n, (Real.cos (↑(α i) * θ i) * Real.cos (↑(β i) * θ i))
      ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc 0 Real.pi))) =
      ∏ i : Fin n, ∫ θ_i : ℝ,
        (Real.cos (↑(α i) * θ_i) * Real.cos (↑(β i) * θ_i))
        ∂(volume.restrict (Set.Icc 0 Real.pi)) := by
    exact integral_fin_nat_prod_eq_prod
      (fun i θ_i => Real.cos (↑(α i) * θ_i) * Real.cos (↑(β i) * θ_i))
  rw [fubini]
  -- Step 4: Pull (1/π)^n into the product
  have : (1 / Real.pi) ^ n = ∏ _i : Fin n, (1 / Real.pi) := by
    simp only [Finset.prod_const, Finset.card_fin]
  rw [this]
  rw [← Finset.prod_mul_distrib]
  -- Step 5: Apply factor_eq_chebyInner and chebyshevT_orthogonality
  have hfactor : ∀ i : Fin n,
      (1 / Real.pi) * ∫ θ_i : ℝ,
        (Real.cos (↑(α i) * θ_i) * Real.cos (↑(β i) * θ_i))
        ∂(volume.restrict (Set.Icc 0 Real.pi)) =
      chebyInner (chebyshevT (α i)) (chebyshevT (β i)) :=
    fun i => factor_eq_chebyInner (α i) (β i)
  simp_rw [hfactor, chebyshevT_orthogonality]
  -- Step 6: Now we have ∏ i, (if α i ≠ β i then 0 else if α i = 0 then 1 else 1/2)
  -- Case split on α = β
  by_cases hab : α = β
  · -- α = β: product of (if α_i = 0 then 1 else 1/2)
    subst hab
    rw [if_pos rfl]
    simp only [ne_eq, not_true_eq_false, ite_false]
    -- Now: ∏ i, (if α i = 0 then 1 else 1/2) = 2^{-w(α)}
    -- Rewrite the product of ite into a product over the nonzero set
    have hprod : ∏ i : Fin n, (if α i = 0 then (1 : ℝ) else 1 / 2) =
        (1 / 2 : ℝ) ^ hammingWeight α := by
      rw [show ∏ i : Fin n, (if α i = 0 then (1 : ℝ) else 1 / 2) =
          ∏ i : Fin n, (if α i ≠ 0 then (1 / 2 : ℝ) else 1) from by
          congr 1; ext i; split_ifs with h1 h2 <;> simp_all]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one,
          Finset.prod_const]
      congr 1
    rw [hprod, zpow_neg, zpow_natCast, one_div, inv_pow]
  · -- α ≠ β: some index i has α i ≠ β i, so that factor = 0
    rw [if_neg hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos hi])

/-! ## Helper lemmas for chebyCoeff_inner -/

/-- The product measure `Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc 0 π))`
    is a finite measure, so bounded measurable functions are integrable. -/
private theorem chebyInnerMulti_integrand_integrable {n : ℕ}
    (f g : MvPolynomial (Fin n) ℝ) :
    Integrable
      (fun θ : Fin n → ℝ =>
        MvPolynomial.eval (fun i => Real.cos (θ i)) f *
        MvPolynomial.eval (fun i => Real.cos (θ i)) g)
      (Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc 0 Real.pi))) := by
  rw [← Measure.restrict_pi_pi (μ := fun _ => volume) (s := fun _ => Set.Icc 0 Real.pi)]
  have hcont : Continuous (fun θ : Fin n → ℝ =>
      MvPolynomial.eval (fun i => Real.cos (θ i)) f *
      MvPolynomial.eval (fun i => Real.cos (θ i)) g) := by
    apply Continuous.mul <;>
    · change Continuous ((fun x => MvPolynomial.eval x _) ∘
        (fun θ : Fin n → ℝ => fun i => Real.cos (θ i)))
      exact (MvPolynomial.continuous_eval _).comp
        (continuous_pi fun i => Real.continuous_cos.comp (continuous_apply i))
  exact hcont.continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ => isCompact_Icc)

/-- Left-linearity: chebyInnerMulti distributes over linear combinations in
    the first argument. -/
private theorem chebyInnerMulti_linearComb_left {n : ℕ} {ι : Type*}
    (S : Finset ι) (c : ι → ℝ) (p : ι → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ) :
    chebyInnerMulti (∑ i ∈ S, MvPolynomial.C (c i) * p i) g =
    ∑ i ∈ S, c i * chebyInnerMulti (p i) g := by
  simp only [chebyInnerMulti]
  -- eval distributes over sum and scalar (eval is an AlgHom)
  simp_rw [map_sum, map_mul, MvPolynomial.eval_C]
  -- (∑ c_i * eval(p_i θ)) * eval(g θ) = ∑ c_i * (eval(p_i θ) * eval(g θ))
  simp_rw [Finset.sum_mul, mul_assoc]
  -- Pull finite sum through integral
  rw [integral_finset_sum S (fun i _ =>
    (chebyInnerMulti_integrand_integrable (p i) g).const_mul (c i))]
  -- Pull constant c_i through each integral, distribute (1/π)^n
  simp_rw [integral_const_mul, mul_sum]
  congr 1; ext i; ring

/-- Right-linearity: chebyInnerMulti distributes over linear combinations in
    the second argument. -/
private theorem chebyInnerMulti_linearComb_right {n : ℕ} {ι : Type*}
    (S : Finset ι) (d : ι → ℝ) (q : ι → MvPolynomial (Fin n) ℝ)
    (f : MvPolynomial (Fin n) ℝ) :
    chebyInnerMulti f (∑ j ∈ S, MvPolynomial.C (d j) * q j) =
    ∑ j ∈ S, d j * chebyInnerMulti f (q j) := by
  simp only [chebyInnerMulti]
  simp_rw [map_sum, map_mul, MvPolynomial.eval_C]
  -- eval(f θ) * (∑ d_j * eval(q_j θ)) = ∑ d_j * (eval(f θ) * eval(q_j θ))
  simp_rw [Finset.mul_sum, mul_left_comm]
  rw [integral_finset_sum S (fun j _ =>
    (chebyInnerMulti_integrand_integrable f (q j)).const_mul (d j))]
  simp_rw [integral_const_mul, mul_sum]
  congr 1; ext j; ring

/-- Parseval's identity for the multivariate Chebyshev inner product:
    ⟨f, g⟩ = ∑_κ 2^{-w(κ)} · c_κ(f) · c_κ(g)
    Connects the integral definition to the algebraic expansion. -/
theorem chebyInnerMulti_eq_parseval {n : ℕ} (r : ℕ)
    (f g : MvPolynomial (Fin n) ℝ)
    (hf : f.totalDegree ≤ r) (hg : g.totalDegree ≤ r) :
    chebyInnerMulti f g = ∑ κ ∈ multiIndices n r,
      (2 : ℝ) ^ (-(hammingWeight κ : ℤ)) *
      chebyCoeff n r f κ * chebyCoeff n r g κ := by
  -- Step 1: Expand f using Chebyshev basis
  conv_lhs => rw [chebyshev_expansion r f hf]
  -- Step 2: Distribute chebyInnerMulti over the linear combination in f
  rw [chebyInnerMulti_linearComb_left (multiIndices n r)
    (fun κ => chebyCoeff n r f κ) (fun κ => chebyshevMulti κ) g]
  -- Step 3: For each κ ∈ multiIndices n r, expand g and simplify
  apply Finset.sum_congr rfl
  intro κ hκ
  -- Now need: chebyCoeff n r f κ * chebyInnerMulti (chebyshevMulti κ) g
  --         = 2^{-w(κ)} * chebyCoeff n r f κ * chebyCoeff n r g κ
  -- Expand g
  conv_lhs => rw [chebyshev_expansion r g hg]
  -- Distribute chebyInnerMulti over the linear combination in g
  rw [chebyInnerMulti_linearComb_right (multiIndices n r)
    (fun μ => chebyCoeff n r g μ) (fun μ => chebyshevMulti μ) (chebyshevMulti κ)]
  -- Apply orthogonality: chebyInnerMulti T_κ T_μ = δ_{κ,μ} 2^{-w(κ)}
  simp_rw [chebyshevMulti_orthogonality]
  -- Collapse the sum using the Kronecker delta
  rw [Finset.sum_eq_single κ]
  · -- The κ-term
    rw [if_pos rfl]; ring
  · -- Off-diagonal: μ ≠ κ → term vanishes
    intro μ _ hμκ
    rw [if_neg (Ne.symm hμκ), mul_zero]
  · -- κ ∉ multiIndices n r is contradicted by hκ
    intro habs; exact absurd hκ habs

/-- Connection to the inner product: `chebyCoeff = 2^{w(κ)} · ⟨T_κ, p⟩`. -/
theorem chebyCoeff_inner {n : ℕ} (r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ r)
    (κ : Fin n → ℕ) (hκ : κ ∈ multiIndices n r) :
    chebyCoeff n r p κ = (2 : ℝ) ^ (hammingWeight κ : ℤ) *
      chebyInnerMulti (chebyshevMulti κ) p := by
  -- totalDegree(chebyshevMulti κ) ≤ multiDegree κ ≤ r
  have hκ_le : multiDegree κ ≤ r := (multiIndices_mem_iff.mp hκ).1
  have hT_deg : (chebyshevMulti κ).totalDegree ≤ r :=
    le_trans (chebyshevMulti_totalDegree_le κ) hκ_le
  -- Apply Parseval
  rw [chebyInnerMulti_eq_parseval r (chebyshevMulti κ) p hT_deg hp]
  -- chebyCoeff(r, T_κ, μ) = δ_{κ,μ}, so sum collapses
  have h_sum : ∑ μ ∈ multiIndices n r,
      (2 : ℝ) ^ (-(hammingWeight μ : ℤ)) *
      chebyCoeff n r (chebyshevMulti κ) μ * chebyCoeff n r p μ =
    (2 : ℝ) ^ (-(hammingWeight κ : ℤ)) * chebyCoeff n r p κ := by
    rw [Finset.sum_eq_single κ]
    · rw [chebyCoeff_chebyshev r κ κ hκ hκ, if_pos rfl, mul_one]
    · intro μ hμ hμκ
      rw [chebyCoeff_chebyshev r μ κ hμ hκ, if_neg (Ne.symm hμκ), mul_zero, zero_mul]
    · intro h; exact absurd hκ h
  rw [h_sum]
  -- 2^{w(κ)} * 2^{-w(κ)} * c = c
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  rw [← mul_assoc, ← zpow_add₀ h2ne, add_neg_cancel, zpow_zero, one_mul]

/-- Subtraction for Chebyshev coefficients (derived from add + smul). -/
theorem chebyCoeff_sub {n : ℕ} (r : ℕ) (p q : MvPolynomial (Fin n) ℝ)
    (κ : Fin n → ℕ) :
    chebyCoeff n r (p - q) κ =
      chebyCoeff n r p κ - chebyCoeff n r q κ := by
  have h : p - q = p + MvPolynomial.C (-1) * q := by
    simp [neg_mul, sub_eq_add_neg]
  rw [h, chebyCoeff_add, chebyCoeff_C_mul]; ring

/-! ## Chebyshev coefficient helpers -/

theorem chebyCoeff_zero (r : ℕ) (μ : Fin n → ℕ) :
    chebyCoeff n r 0 μ = 0 := by
  have h := chebyCoeff_add r (0 : MvPolynomial (Fin n) ℝ) 0 μ
  simp at h; linarith

/-- chebyCoeff of a Chebyshev expansion gives back the coefficients -/
theorem chebyCoeff_expansion_coeff (r : ℕ) (c : (Fin n → ℕ) → ℝ) (μ : Fin n → ℕ)
    (hμ : μ ∈ multiIndices n r) :
    chebyCoeff n r (∑ κ ∈ multiIndices n r,
      MvPolynomial.C (c κ) * chebyshevMulti κ) μ = c μ := by
  rw [chebyCoeff_finset_sum]
  simp only [chebyCoeff_C_mul]
  rw [Finset.sum_eq_single μ
    (fun κ hκ hκμ => by
      rw [chebyCoeff_chebyshev r μ κ hμ hκ]
      rw [if_neg hκμ]; ring)
    (fun h => absurd hμ h)]
  rw [chebyCoeff_chebyshev r μ μ hμ hμ, if_pos rfl]; ring

/-- multiDegree κ ≤ d implies κ ∈ multiIndices n d -/
theorem multiDegree_le_mem {d : ℕ} {κ : Fin n → ℕ} (h : multiDegree κ ≤ d) :
    κ ∈ multiIndices n d := by
  rw [multiIndices_mem_iff]
  exact ⟨h, fun i => le_trans
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) h⟩

/-- T_κ has totalDegree ≤ multiDegree κ -/
theorem chebyshevMulti_totalDegree (κ : Fin n → ℕ) :
    (chebyshevMulti κ).totalDegree ≤ multiDegree κ :=
  chebyshevMulti_totalDegree_le κ

end OptimalConvergenceRates

end
