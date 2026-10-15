/-
  OptimalConvergenceRates/BaldiSlot2024/DegreeShift.lean

  Degree-shift machinery converting box preorderings into box quadratic-module certificates.
-/
import OptimalConvergenceRates.BasicNotions.GeneralCones
import OptimalConvergenceRates.BasicNotions.Lasserre
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Funext

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-- The standard BoxQuadraticModule is the generalized one for the SemialgebraicGenerators. -/
theorem BoxQuadraticModule_eq_GenQuadraticModule :
    BoxQuadraticModule n r = GenQuadraticModule (fun i => BoxSemialgebraicGenerator i) r := by
  ext p; constructor
  · rintro ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩
    exact ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩
  · rintro ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩
    exact ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩

/-! ## Degree shifting: arXiv v3, Lemma 24(i) -/

/-- **ArXiv v3, Lemma 24(i)**: Degree shifting for quadratic modules.
    If each hᵢ ∈ Q(g)_{deg hᵢ + l}, then Q(h)_d ⊆ Q(g)_{d+l}. -/
-- Helper: multiplying a GenQM element by an SOS polynomial shifts the degree additively.
private theorem GenQuadraticModule_sos_mul {m : ℕ}
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (σ : MvPolynomial (Fin n) ℝ) (hσ : IsSOS σ)
    (hq : q ∈ GenQuadraticModule g r) :
    σ * q ∈ GenQuadraticModule g (r + σ.totalDegree) := by
  obtain ⟨τ₀, τ, hsos₀, hsos, hdeg₀, hdeg, hqeq⟩ := hq
  refine ⟨σ * τ₀, fun j => σ * τ j, IsSOS_mul hσ hsos₀,
    fun j => IsSOS_mul hσ (hsos j), ?_, ?_, ?_⟩
  · calc (σ * τ₀).totalDegree
        ≤ σ.totalDegree + τ₀.totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ σ.totalDegree + r := Nat.add_le_add_left hdeg₀ _
      _ = r + σ.totalDegree := Nat.add_comm _ _
  · intro j
    calc (σ * τ j * g j).totalDegree
        = (σ * (τ j * g j)).totalDegree := by ring_nf
      _ ≤ σ.totalDegree + (τ j * g j).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ σ.totalDegree + r := Nat.add_le_add_left (hdeg j) _
      _ = r + σ.totalDegree := Nat.add_comm _ _
  · rw [hqeq, mul_add, Finset.mul_sum]; simp only [mul_assoc]

-- Helper: zero is in any GenQuadraticModule.
private theorem zero_mem_GenQuadraticModule {m : ℕ}
    {g : Fin m → MvPolynomial (Fin n) ℝ} {r : ℕ} :
    (0 : MvPolynomial (Fin n) ℝ) ∈ GenQuadraticModule g r :=
  ⟨0, 0, IsSOS_zero, fun _ => IsSOS_zero, by simp, fun _ => by simp, by simp⟩

-- Helper: an SOS polynomial is in any GenQuadraticModule with sufficient degree.
private theorem sos_mem_GenQuadraticModule {m : ℕ}
    {g : Fin m → MvPolynomial (Fin n) ℝ} {r : ℕ}
    (σ : MvPolynomial (Fin n) ℝ) (hsos : IsSOS σ) (hdeg : σ.totalDegree ≤ r) :
    σ ∈ GenQuadraticModule g r :=
  ⟨σ, 0, hsos, fun _ => IsSOS_zero, hdeg, fun _ => by simp, by simp⟩

-- Helper: for a SINGLE generator g, GenQM({g}) is closed under multiplication.
-- If a ∈ GenQM({g})(r_a) and b ∈ GenQM({g})(r_b), then a*b ∈ GenQM({g})(r_a + r_b).
-- Proof: expand a = σ₀_a + σ₁_a·g, b = σ₀_b + σ₁_b·g, then
-- a·b = (σ₀_a·σ₀_b + σ₁_a·σ₁_b·g²) + (σ₀_a·σ₁_b + σ₁_a·σ₀_b)·g
-- All components are SOS (g² is a perfect square), and degree bounds follow.
private theorem GenQuadraticModule_single_mul
    {g₁ : MvPolynomial (Fin n) ℝ}
    {a b : MvPolynomial (Fin n) ℝ} {r_a r_b : ℕ}
    (ha : a ∈ GenQuadraticModule (fun _ : Fin 1 => g₁) r_a)
    (hb : b ∈ GenQuadraticModule (fun _ : Fin 1 => g₁) r_b) :
    a * b ∈ GenQuadraticModule (fun _ : Fin 1 => g₁) (r_a + r_b) := by
  obtain ⟨σ₀_a, σ_a, hsos₀_a, hsos_a, hdeg₀_a, hdeg_a, ha_eq⟩ := ha
  obtain ⟨σ₀_b, σ_b, hsos₀_b, hsos_b, hdeg₀_b, hdeg_b, hb_eq⟩ := hb
  -- Extract the single coefficients
  set σ₁_a := σ_a 0 with hσ₁_a_def
  set σ₁_b := σ_b 0 with hσ₁_b_def
  have hsos₁_a : IsSOS σ₁_a := hsos_a 0
  have hsos₁_b : IsSOS σ₁_b := hsos_b 0
  have hdeg₁_a : (σ₁_a * g₁).totalDegree ≤ r_a := hdeg_a 0
  have hdeg₁_b : (σ₁_b * g₁).totalDegree ≤ r_b := hdeg_b 0
  -- Rewrite a and b
  have ha_form : a = σ₀_a + σ₁_a * g₁ := by
    have : ∑ i : Fin 1, σ_a i * (fun _ : Fin 1 => g₁) i = σ₁_a * g₁ := by
      rw [Fin.sum_univ_one]
    rw [ha_eq, this]
  have hb_form : b = σ₀_b + σ₁_b * g₁ := by
    have : ∑ i : Fin 1, σ_b i * (fun _ : Fin 1 => g₁) i = σ₁_b * g₁ := by
      rw [Fin.sum_univ_one]
    rw [hb_eq, this]
  -- Compute the product
  -- a*b = (σ₀_a + σ₁_a*g₁)(σ₀_b + σ₁_b*g₁)
  --     = σ₀_a*σ₀_b + σ₀_a*σ₁_b*g₁ + σ₁_a*g₁*σ₀_b + σ₁_a*g₁*σ₁_b*g₁
  --     = [σ₀_a*σ₀_b + σ₁_a*σ₁_b*g₁²] + [σ₀_a*σ₁_b + σ₁_a*σ₀_b]*g₁
  -- New SOS components:
  set new_σ₀ := σ₀_a * σ₀_b + σ₁_a * σ₁_b * g₁ ^ 2
  set new_σ₁ := σ₀_a * σ₁_b + σ₁_a * σ₀_b
  refine ⟨new_σ₀, fun _ => new_σ₁, ?_, ?_, ?_, ?_, ?_⟩
  · -- new_σ₀ is SOS
    apply IsSOS_add
    · exact IsSOS_mul hsos₀_a hsos₀_b
    · exact IsSOS_mul (IsSOS_mul hsos₁_a hsos₁_b) (IsSOS_sq g₁)
  · -- new_σ₁ is SOS
    intro _
    exact IsSOS_add (IsSOS_mul hsos₀_a hsos₁_b) (IsSOS_mul hsos₁_a hsos₀_b)
  · -- deg(new_σ₀) ≤ r_a + r_b
    -- Key: σ₁_a * σ₁_b * g₁² = (σ₁_a * g₁) * (σ₁_b * g₁)
    have hrewrite : σ₁_a * σ₁_b * g₁ ^ 2 = (σ₁_a * g₁) * (σ₁_b * g₁) := by ring
    calc new_σ₀.totalDegree
        ≤ max (σ₀_a * σ₀_b).totalDegree (σ₁_a * σ₁_b * g₁ ^ 2).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ max (r_a + r_b) (r_a + r_b) := by
          apply max_le_max
          · exact le_trans (MvPolynomial.totalDegree_mul _ _)
              (Nat.add_le_add hdeg₀_a hdeg₀_b)
          · rw [hrewrite]
            exact le_trans (MvPolynomial.totalDegree_mul _ _)
              (Nat.add_le_add hdeg₁_a hdeg₁_b)
      _ = r_a + r_b := max_self _
  · -- deg(new_σ₁ * g₁) ≤ r_a + r_b
    intro _
    -- new_σ₁ * g₁ = (σ₀_a * σ₁_b + σ₁_a * σ₀_b) * g₁
    -- = σ₀_a * (σ₁_b * g₁) + (σ₁_a * g₁) * σ₀_b
    have hrewrite : new_σ₁ * g₁ = σ₀_a * (σ₁_b * g₁) + (σ₁_a * g₁) * σ₀_b := by
      simp only [new_σ₁]; ring
    rw [hrewrite]
    calc (σ₀_a * (σ₁_b * g₁) + (σ₁_a * g₁) * σ₀_b).totalDegree
        ≤ max (σ₀_a * (σ₁_b * g₁)).totalDegree ((σ₁_a * g₁) * σ₀_b).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ max (r_a + r_b) (r_a + r_b) := by
          apply max_le_max
          · exact le_trans (MvPolynomial.totalDegree_mul _ _)
              (Nat.add_le_add hdeg₀_a hdeg₁_b)
          · exact le_trans (MvPolynomial.totalDegree_mul _ _)
              (Nat.add_le_add hdeg₁_a hdeg₀_b)
      _ = r_a + r_b := max_self _
  · -- a * b = new_σ₀ + new_σ₁ * g₁
    rw [ha_form, hb_form]
    simp only [new_σ₀, new_σ₁, Fin.sum_univ_one]
    ring

theorem degree_shift_box_qmod {m₁ m₂ : ℕ}
    {g : Fin m₁ → MvPolynomial (Fin n) ℝ}
    {h : Fin m₂ → MvPolynomial (Fin n) ℝ}
    {l d : ℕ}
    (hgen : ∀ i, h i ∈ GenQuadraticModule g ((h i).totalDegree + l))
    (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ GenQuadraticModule h d) :
    p ∈ GenQuadraticModule g (d + l) := by
  obtain ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩ := hp
  rw [hsum]
  -- Show σ₀ ∈ GenQM(g)_{d+l}: it's SOS with degree ≤ d ≤ d+l
  have hσ₀_mem : σ₀ ∈ GenQuadraticModule g (d + l) :=
    sos_mem_GenQuadraticModule σ₀ hsos₀ (le_trans hdeg₀ (Nat.le_add_right d l))
  -- Show each σ i * h i ∈ GenQM(g)_{d+l}
  suffices hterms : ∑ i : Fin m₂, σ i * h i ∈ GenQuadraticModule g (d + l) from
    GenQuadraticModule_add hσ₀_mem hterms
  -- Prove each summand is in GenQM(g)_{d+l} and use closure under addition
  apply Finset.sum_induction _ (· ∈ GenQuadraticModule g (d + l))
    (fun _ _ ha hb => GenQuadraticModule_add ha hb)
    zero_mem_GenQuadraticModule
  intro i _
  -- For each i: σ i * h i ∈ GenQM(g)_{d+l}
  -- Case split: if σ i = 0 or h i = 0, the product is 0
  by_cases hσ_zero : σ i = 0
  · simp only [hσ_zero, zero_mul]; exact zero_mem_GenQuadraticModule
  by_cases hh_zero : h i = 0
  · simp only [hh_zero, mul_zero]; exact zero_mem_GenQuadraticModule
  -- When both are nonzero, use totalDegree_mul_of_isDomain to get the equality
  have hdeg_eq : (σ i * h i).totalDegree = (σ i).totalDegree + (h i).totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain hσ_zero hh_zero
  -- From the QM(h) degree bound: deg(σ i * h i) ≤ d
  have hdeg_prod := hdeg i
  -- So deg(σ i) + deg(h i) ≤ d
  have hbound : (σ i).totalDegree + (h i).totalDegree ≤ d := hdeg_eq ▸ hdeg_prod
  -- Since h i ∈ GenQM(g)_{deg(h i)+l}, by sos_mul:
  -- σ i * h i ∈ GenQM(g)_{deg(h i)+l+deg(σ i)}
  have hmem := GenQuadraticModule_sos_mul (σ i) (hsos i) (hgen i)
  -- deg(h i)+l+deg(σ i) ≤ d+l follows from deg(σ i)+deg(h i) ≤ d
  have hle : (h i).totalDegree + l + (σ i).totalDegree ≤ d + l := by omega
  exact GenQuadraticModule_mono hle hmem

/-! ## Degree shifting: arXiv v3, Lemma 24(ii) -/

/-- **ArXiv v3, Lemma 24(ii)**: Degree shifting from preordering to quadratic module.
    For a single generator g₁, if ∏_{j∈J} hⱼ ∈ Q(g₁)_{deg(∏ hⱼ) + |J|·l}
    for all J, then T(h)_d ⊆ Q(g₁)_{d + m·l}. -/
theorem degree_shift_box_preo_to_box_qmod {m : ℕ}
    {g₁ : MvPolynomial (Fin n) ℝ}
    {h : Fin m → MvPolynomial (Fin n) ℝ}
    {l d : ℕ}
    (hprod : ∀ J : Finset (Fin m),
      (∏ j ∈ J, h j) ∈ GenQuadraticModule (fun _ : Fin 1 => g₁)
        ((∏ j ∈ J, h j).totalDegree + J.card * l))
    (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ GenPreordering h d) :
    p ∈ GenQuadraticModule (fun _ : Fin 1 => g₁) (d + m * l) := by
  obtain ⟨σ, hsos, hdeg, hpeq⟩ := hp
  rw [hpeq]
  -- Each term σ J * ∏_{j∈J} h j ∈ GenQM({g₁})_{d + m*l}
  apply Finset.sum_induction _ (· ∈ GenQuadraticModule (fun _ : Fin 1 => g₁) (d + m * l))
    (fun _ _ ha hb => GenQuadraticModule_add ha hb)
    zero_mem_GenQuadraticModule
  intro J _
  by_cases hσ_zero : σ J = 0
  · simp only [hσ_zero, zero_mul]; exact zero_mem_GenQuadraticModule
  by_cases hprod_zero : ∏ j ∈ J, h j = 0
  · simp only [hprod_zero, mul_zero]; exact zero_mem_GenQuadraticModule
  -- Both nonzero: use totalDegree_mul_of_isDomain
  have hdeg_eq : (σ J * ∏ j ∈ J, h j).totalDegree =
      (σ J).totalDegree + (∏ j ∈ J, h j).totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain hσ_zero hprod_zero
  have hbound : (σ J).totalDegree + (∏ j ∈ J, h j).totalDegree ≤ d := hdeg_eq ▸ hdeg J
  -- σ J * ∏ h_j ∈ GenQM({g₁})_{deg(∏ h_j) + |J|·l + deg(σ J)}
  have hmem := GenQuadraticModule_sos_mul (σ J) (hsos J) (hprod J)
  -- The degree bound: deg(∏ h_j) + |J|·l + deg(σ J) ≤ d + m·l
  have hcard : J.card ≤ m := by
    calc J.card ≤ Finset.univ.card := J.card_le_univ
      _ = m := Fintype.card_fin m
  have hle : (∏ j ∈ J, h j).totalDegree + J.card * l + (σ J).totalDegree ≤ d + m * l := by
    have hmul : J.card * l ≤ m * l := Nat.mul_le_mul_right l hcard
    linarith
  exact GenQuadraticModule_mono hle hmem

/-! ## Univariate auxiliary: the SOS identity from Appendix A -/

/-- The polynomial f_q(x_j) = ∑_{i=1}^{q-1} ((q-i)/q) · x_j^{2(i-1)} · (1-x_j²)²
    from Appendix A of Baldi-Slot 2024, for the j-th variable.
    This is a sum of squares: each term is a nonneg constant times a square. -/
def fPoly (j : Fin n) (q : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ i ∈ Finset.range (q - 1),
    MvPolynomial.C ((q - (i + 1 : ℕ) : ℝ) / q) *
    (X j) ^ (2 * i) *
    (1 - (X j) ^ 2) ^ 2

/-- f_q is a sum of squares. Each term ((q-i)/q) · x^{2(i-1)} · (1-x²)²
    equals ((q-i)/q) · (x^{i-1} · (1-x²))², and (q-i)/q ≥ 0 for i ≤ q-1. -/
theorem fPoly_isSOS (j : Fin n) (q : ℕ) (hq : 1 ≤ q) : IsSOS (fPoly j q) := by
  unfold fPoly
  apply IsSOS_sum_finset
  intro i hi
  -- Each term: C((q - (i+1)) / q) * X(j) ^ (2*i) * (1 - X(j) ^ 2) ^ 2
  -- = C(c) * (X(j)^i * (1 - X(j)^2))^2, with c ≥ 0
  have hc : (0 : ℝ) ≤ (q - (i + 1 : ℕ) : ℝ) / q := by
    apply div_nonneg
    · have hi' : i + 1 ≤ q := by
        rw [Finset.mem_range] at hi
        omega
      exact sub_nonneg.mpr (Nat.cast_le.mpr hi')
    · exact Nat.cast_nonneg _
  -- Rewrite as C(c) * (X(j)^i * (1 - X(j)^2))^2
  have hsq : (X j) ^ (2 * i) * ((1 : MvPolynomial (Fin n) ℝ) - (X j) ^ 2) ^ 2 =
      ((X j) ^ i * (1 - (X j) ^ 2)) ^ 2 := by ring
  rw [mul_assoc, hsq]
  exact IsSOS_nonneg_scale (IsSOS_sq _) _ hc

/-! ## ArXiv v3, Lemma 25: 1 - x² ∈ Q(1 - x^{2q})_{2q} -/

/-- The generator 1 - x^{2q} for a given variable, as a multivariate polynomial. -/
def higherGenerator (i : Fin n) (q : ℕ) : MvPolynomial (Fin n) ℝ :=
  1 - (X i) ^ (2 * q)

theorem totalDegree_higherGenerator (i : Fin n) (q : ℕ) :
    (higherGenerator i q).totalDegree ≤ 2 * q := by
  unfold higherGenerator
  calc ((1 : MvPolynomial (Fin n) ℝ) - (X i) ^ (2 * q)).totalDegree
      ≤ max (1 : MvPolynomial (Fin n) ℝ).totalDegree ((X i) ^ (2 * q)).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ = max 0 (2 * q) := by rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X_pow]
    _ = 2 * q := by omega

/-- **ArXiv v3, Lemma 25**: 1 - xᵢ² ∈ Q(1 - xᵢ^{2q})_{2q}.
    Uses the identity 1 - x² = f_q(x) + (1/q)(1 - x^{2q}) from Appendix A. -/
-- Multiplied form of the identity: (1-t²)²·∑(q-i-1)t^{2i} + (1-t^{2q}) = q·(1-t²)
-- This avoids division by q, making the proof cleaner.
private theorem fPoly_identity_scaled (t : ℝ) : ∀ q : ℕ, 1 ≤ q →
    (1 - t ^ 2) ^ 2 * ∑ i ∈ Finset.range (q - 1),
      ((q - (i + 1 : ℕ) : ℕ) : ℝ) * t ^ (2 * i) +
    (1 - t ^ (2 * q)) = (q : ℝ) * (1 - t ^ 2) := by
  intro q
  induction q with
  | zero => omega
  | succ q ih =>
    intro hq
    by_cases hq0 : q = 0
    · subst hq0; norm_num
    · have hq_ge : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
      have ih' := ih hq_ge
      -- Key: (q+1)-1 = q and the coefficient simplification
      have hsucc_sub : q + 1 - 1 = q := by omega
      rw [hsucc_sub]
      -- Coefficient simplification: for i < q, (q+1)-(i+1) = q-i as ℕ
      have hcoeff : ∀ i ∈ Finset.range q,
          ((q + 1 - (i + 1) : ℕ) : ℝ) = ((q - i : ℕ) : ℝ) := by
        intro i hi; congr 1; rw [Finset.mem_range] at hi; omega
      rw [Finset.sum_congr rfl (fun i hi => by rw [hcoeff i hi])]
      -- Split: ∑_{i<q} (q-i) t^{2i} = ∑_{i<q} ((q-(i+1))+1) t^{2i}
      -- But need to handle the last term separately since q-(q-1+1) = 0 in ℕ
      -- Strategy: ∑_{i<q} (q-i) t^{2i} = ∑_{i<q} (q-1-i+1) t^{2i}
      -- = ∑_{i<q} (q-(i+1)) t^{2i} + ∑_{i<q} t^{2i}   [since q-i = (q-(i+1)) + 1 for i<q]
      have hcoeff2 : ∀ i ∈ Finset.range q,
          ((q - i : ℕ) : ℝ) = ((q - (i + 1) : ℕ) : ℝ) + 1 := by
        intro i hi; rw [Finset.mem_range] at hi
        have : q - i = (q - (i + 1)) + 1 := by omega
        rw [this, Nat.cast_add, Nat.cast_one]
      have hsum_split : ∑ i ∈ Finset.range q, ((q - i : ℕ) : ℝ) * t ^ (2 * i) =
          ∑ i ∈ Finset.range q, ((q - (i + 1) : ℕ) : ℝ) * t ^ (2 * i) +
          ∑ i ∈ Finset.range q, t ^ (2 * i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoeff2 i hi, add_mul, one_mul]
      rw [hsum_split, mul_add]
      -- The sum ∑_{i<q} (q-(i+1)) t^{2i} extends to range (q-1) by adding a zero term
      have hsum_extend : ∑ i ∈ Finset.range q, ((q - (i + 1) : ℕ) : ℝ) * t ^ (2 * i) =
          ∑ i ∈ Finset.range (q - 1), ((q - (i + 1) : ℕ) : ℝ) * t ^ (2 * i) := by
        have hq_rw : q = q - 1 + 1 := by omega
        conv_lhs => rw [hq_rw]
        rw [Finset.sum_range_succ]
        have : (q - 1 + 1 : ℕ) - ((q - 1 : ℕ) + 1) = 0 := by omega
        rw [this, Nat.cast_zero, zero_mul, add_zero]
        congr 1; ext i; congr 2; omega
      rw [hsum_extend]
      -- Use geom_sum_mul_neg: (∑_{i<q} (t²)^i) * (1-t²) = 1 - (t²)^q
      have hgeom := geom_sum_mul_neg (t ^ 2) q
      simp only [← pow_mul] at hgeom
      -- Set abbreviations
      set S := ∑ i ∈ Finset.range (q - 1),
        ((q - (i + 1) : ℕ) : ℝ) * t ^ (2 * i)
      set G := ∑ i ∈ Finset.range q, t ^ (2 * i)
      -- (1-t²)² * G = (1-t²) * (G * (1-t²)) = (1-t²) * (1-t^{2q})
      have hGsub : (1 - t ^ 2) ^ 2 * G = (1 - t ^ 2) * (1 - t ^ (2 * q)) := by
        calc (1 - t ^ 2) ^ 2 * G = (1 - t ^ 2) * (G * (1 - t ^ 2)) := by ring
          _ = (1 - t ^ 2) * (1 - t ^ (2 * q)) := by rw [hgeom]
      -- Rewrite t^{2*(q+1)} = t^{2q} * t²
      have hpow : t ^ (2 * (q + 1)) = t ^ (2 * q) * t ^ 2 := by ring
      rw [hpow]
      -- Expand products for linarith
      have hexpand : (1 - t ^ 2) * (1 - t ^ (2 * q)) =
          1 - t ^ 2 - t ^ (2 * q) + t ^ (2 * q) * t ^ 2 := by ring
      have hcast : (↑(q + 1) : ℝ) * (1 - t ^ 2) =
          (↑q : ℝ) * (1 - t ^ 2) + (1 - t ^ 2) := by push_cast; ring
      -- Now goal is linear in the atomic nonlinear terms
      linarith [ih', hGsub, hexpand, hcast]

-- The key algebraic identity: 1 - x² = f_q(x) + (1/q)(1 - x^{2q}).
-- Proved by reducing to fPoly_identity_scaled via MvPolynomial.funext.
private theorem fPoly_add_higherGen (j : Fin n) (q : ℕ) (hq : 1 ≤ q) :
    fPoly j q + MvPolynomial.C (1 / (q : ℝ)) * higherGenerator j q =
      BoxSemialgebraicGenerator j := by
  apply MvPolynomial.funext
  intro x
  -- Use the identity from fPoly_identity_scaled after evaluating both sides
  have hq_pos : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq_pos' : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have h := fPoly_identity_scaled (x j) q hq
  -- h: (1-(x j)²)² * ∑ (q-(i+1))*(x j)^{2i} + (1-(x j)^{2q}) = q*(1-(x j)²)
  -- Evaluate both sides
  simp only [map_add, map_mul, map_sub, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, map_one, map_sum, fPoly, higherGenerator,
    BoxSemialgebraicGenerator]
  -- Goal: ∑ ((q-(i+1))/q) * (x j)^{2i} * (1-(x j)²)² + (1/q)*(1-(x j)^{2q}) = 1-(x j)²
  -- Factor the 1/q out and use h
  -- Each summand: ((q-(i+1))/q) * a = (1/q) * (q-(i+1)) * a
  have hfactor : ∀ i ∈ Finset.range (q - 1),
      ((↑q - ↑(i + 1)) / ↑q : ℝ) * x j ^ (2 * i) * (1 - x j ^ 2) ^ 2 =
      (1 / ↑q) * (↑(q - (i + 1)) * x j ^ (2 * i) * (1 - x j ^ 2) ^ 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi_le : i + 1 ≤ q := by omega
    rw [show (↑q - ↑(i + 1) : ℝ) = (↑(q - (i + 1)) : ℝ) from by
      rw [Nat.cast_sub hi_le]]
    field_simp
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
  -- Goal: (1/q) * [(1-(x j)²)² * ∑ (q-(i+1))*(x j)^{2i}] + (1/q)*(1-(x j)^{2q}) = 1-(x j)²
  -- Factor: (1/q) * [(1-(x j)²)² * ∑ ... + (1-(x j)^{2q})]
  rw [show ∀ a b c : ℝ, (1 / c) * a + (1 / c) * b = (1 / c) * (a + b) from
    fun a b c => by ring]
  -- Rewrite ∑ (q-(i+1)) * xⱼ^{2i} * (1-xⱼ²)² to (1-xⱼ²)² * ∑ (q-(i+1)) * xⱼ^{2i}
  rw [show (∑ i ∈ Finset.range (q - 1), ↑(q - (i + 1)) * x j ^ (2 * i) * (1 - x j ^ 2) ^ 2) =
      (1 - x j ^ 2) ^ 2 * ∑ i ∈ Finset.range (q - 1), ↑(q - (i + 1)) * x j ^ (2 * i) from by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  -- Now use h: (1-xⱼ²)² * ∑ ... + (1 - xⱼ^{2q}) = q * (1 - xⱼ²)
  rw [h]
  -- Goal: (1/q) * (q * (1 - x j ^ 2)) = 1 - x j ^ 2
  field_simp

-- Degree bound for fPoly.
private theorem totalDegree_fPoly (j : Fin n) (q : ℕ) :
    (fPoly j q).totalDegree ≤ 2 * q := by
  unfold fPoly
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  rw [Finset.mem_range] at hi
  -- We bound each term C((q-(i+1))/q) * X(j)^(2i) * (1 - X(j)^2)^2
  set p := (X j : MvPolynomial (Fin n) ℝ) ^ (2 * i)
  set q_part := ((1 : MvPolynomial (Fin n) ℝ) - (X j) ^ 2) ^ 2
  set c := MvPolynomial.C ((q - (i + 1 : ℕ) : ℝ) / q)
  have : (c * p * q_part).totalDegree ≤ 2 * q := by
    have deg_c : c.totalDegree = 0 := MvPolynomial.totalDegree_C _
    have deg_p : p.totalDegree = 2 * i := MvPolynomial.totalDegree_X_pow _ _
    have deg_q_part : q_part.totalDegree ≤ 4 := by
      calc q_part.totalDegree ≤ 2 * ((1 : MvPolynomial (Fin n) ℝ) - (X j) ^ 2).totalDegree :=
            MvPolynomial.totalDegree_pow _ _
        _ ≤ 2 * (max (1 : MvPolynomial (Fin n) ℝ).totalDegree ((X j) ^ 2).totalDegree) :=
            Nat.mul_le_mul_left _ (MvPolynomial.totalDegree_sub _ _)
        _ = 2 * (max 0 2) := by rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X_pow]
        _ = 4 := by omega
    have h1 : (c * p).totalDegree ≤ c.totalDegree + p.totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    have h2 : (c * p * q_part).totalDegree ≤ (c * p).totalDegree + q_part.totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    calc (c * p * q_part).totalDegree
        ≤ (c * p).totalDegree + q_part.totalDegree := h2
      _ ≤ (c.totalDegree + p.totalDegree) + q_part.totalDegree := Nat.add_le_add_right h1 _
      _ = 0 + 2 * i + q_part.totalDegree := by rw [deg_c, deg_p]
      _ = 2 * i + q_part.totalDegree := by ring
      _ ≤ 2 * i + 4 := Nat.add_le_add_left deg_q_part (2 * i)
      _ ≤ 2 * q := by omega
  exact this

theorem one_sub_sq_in_box_qmod (i : Fin n) (q : ℕ) (hq : 1 ≤ q) :
    BoxSemialgebraicGenerator i ∈
      GenQuadraticModule (fun _ : Fin 1 => higherGenerator i q) (2 * q) := by
  -- Use the identity: BoxSemialgebraicGenerator i = fPoly i q + C(1/q) * higherGenerator i q
  rw [← fPoly_add_higherGen i q hq]
  -- Now we need: fPoly i q + C(1/q) * hg ∈ Q(hg)_{2q}
  -- σ₀ = fPoly i q (SOS, deg ≤ 2q), σ₁ = C(1/q) (SOS since 1/q ≥ 0)
  refine ⟨fPoly i q, fun _ => MvPolynomial.C (1 / (q : ℝ)),
    fPoly_isSOS i q hq, ?_, ?_, ?_, ?_⟩
  · intro _
    exact IsSOS_C_nonneg _ (div_nonneg one_pos.le (Nat.cast_nonneg _))
  · exact totalDegree_fPoly i q
  · intro _
    calc (MvPolynomial.C (1 / (q : ℝ)) * higherGenerator i q).totalDegree
        ≤ (MvPolynomial.C (1 / (q : ℝ))).totalDegree +
            (higherGenerator i q).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 2 * q := by
          apply Nat.add_le_add
          · exact le_of_eq (MvPolynomial.totalDegree_C _)
          · exact totalDegree_higherGenerator i q
      _ = 2 * q := by omega
  · simp

/-! ## Norm polynomials and eta -/

/-- The 2q-norm polynomial: ‖x‖_{2q}^{2q} = ∑ⱼ xⱼ^{2q} -/
def normPoly2q (q : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin n, (X j) ^ (2 * q)

theorem totalDegree_normPoly2q (q : ℕ) :
    (normPoly2q (n := n) q).totalDegree ≤ 2 * q := by
  unfold normPoly2q
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  rw [MvPolynomial.totalDegree_X_pow]

/-- η(n,q) = n^{1/(2q)}, the scaling constant.
    Uses Real.rpow for real-valued exponents. -/
def eta (n : ℕ) (q : ℕ) : ℝ :=
  (n : ℝ).rpow ((1 : ℝ) / (2 * (q : ℝ)))

/-- η² = n^{1/q} -/
theorem eta_sq (_hn : 0 < n) (hq : 0 < q) :
    eta n q ^ 2 = (n : ℝ).rpow ((1 : ℝ) / (q : ℝ)) := by
  unfold eta
  change ((n : ℝ) ^ ((1 : ℝ) / (2 * (q : ℝ)))) ^ 2 = (n : ℝ) ^ ((1 : ℝ) / (q : ℝ))
  rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / (2 * (q : ℝ)))) 2,
      ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  field_simp
  ring

/-- (η²)^q = n, i.e., (n^{1/q})^q = n. -/
theorem eta_sq_pow_q (_hn : 0 < n) (hq : 0 < q) :
    (eta n q ^ 2) ^ q = (n : ℝ) := by
  rw [← pow_mul]
  unfold eta
  -- Goal: (↑n).rpow (1 / (2 * ↑q)) ^ (2 * q) = ↑n
  -- Use rpow_natCast to convert ^ (2*q) to rpow
  change ((↑n : ℝ) ^ ((1 : ℝ) / (2 * ↑q))) ^ (2 * q) = ↑n
  rw [← Real.rpow_natCast ((↑n : ℝ) ^ ((1 : ℝ) / (2 * ↑q))) (2 * q)]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  have h : (1 : ℝ) / (2 * ↑q) * ↑(2 * q) = 1 := by push_cast; field_simp
  rw [h, Real.rpow_one]

/-- The scaled generator: η² - xᵢ², where η = n^{1/(2q)}. -/
def scaledGenerator (i : Fin n) (q : ℕ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (eta n q ^ 2) - (X i) ^ 2

/-- The "n minus norm" polynomial: n - ∑ⱼ xⱼ^{2q}.
    This equals ∑ⱼ (1 - xⱼ^{2q}), which is a sum of the higher generators. -/
def nSubNorm (q : ℕ) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (n : ℝ) - normPoly2q q

theorem totalDegree_scaledGenerator (i : Fin n) (q : ℕ) :
    (scaledGenerator i q).totalDegree ≤ 2 := by
  unfold scaledGenerator
  calc (MvPolynomial.C (eta n q ^ 2) - (X i) ^ 2).totalDegree
      ≤ max (MvPolynomial.C (eta n q ^ 2)).totalDegree ((X i) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ = max 0 2 := by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow]
    _ = 2 := by omega

theorem totalDegree_nSubNorm (q : ℕ) (_hq : 1 ≤ q) :
    (nSubNorm (n := n) q).totalDegree ≤ 2 * q := by
  unfold nSubNorm
  calc (MvPolynomial.C (n : ℝ) - normPoly2q q).totalDegree
      ≤ max (MvPolynomial.C (n : ℝ)).totalDegree (normPoly2q q).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ max 0 (2 * q) := by
        apply max_le_max
        · exact le_of_eq (MvPolynomial.totalDegree_C _)
        · exact totalDegree_normPoly2q q
    _ = 2 * q := by omega

theorem totalDegree_scaledGenerator_eq (i : Fin n) (q : ℕ) :
    (scaledGenerator i q).totalDegree = 2 := by
  apply le_antisymm
  · exact totalDegree_scaledGenerator i q
  · -- Show 2 ≤ totalDegree by exhibiting monomial Finsupp.single i 2 in support
    set s : Fin n →₀ ℕ := Finsupp.single i 2 with hs_def
    have hs_sum : s.sum (fun _ e => e) = 2 := Finsupp.sum_single_index rfl
    rw [← hs_sum]
    apply MvPolynomial.le_totalDegree
    rw [MvPolynomial.mem_support_iff]
    simp only [scaledGenerator, MvPolynomial.coeff_sub]
    have hs_ne : s ≠ 0 := Finsupp.single_ne_zero.mpr (by omega)
    have hC : (MvPolynomial.C (eta n q ^ 2) :
        MvPolynomial (Fin n) ℝ).coeff s = 0 := by
      rw [MvPolynomial.coeff_C]
      exact ite_eq_right (fun h => hs_ne h.symm)
    have hX : ((X i : MvPolynomial (Fin n) ℝ) ^ 2).coeff s = 1 := by
      rw [MvPolynomial.coeff_X_pow]
      simp [hs_def]
    rw [hC, hX]
    norm_num

theorem scaledGenerator_ne_zero (i : Fin n) (q : ℕ) :
    scaledGenerator i q ≠ 0 := by
  intro h
  have : (scaledGenerator i q).totalDegree = 2 := totalDegree_scaledGenerator_eq i q
  rw [h, MvPolynomial.totalDegree_zero] at this
  omega

theorem prod_scaledGenerator_ne_zero {s : Finset (Fin n)} (q : ℕ) :
    (∏ i ∈ s, scaledGenerator i q) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => scaledGenerator_ne_zero i q)

/-! ## ArXiv v3, Lemma 26: η² - xᵢ² ∈ Q(n - ‖x‖_{2q})_{2q} -/

/-- **ArXiv v3, Lemma 26**: η² - xᵢ² ∈ Q(n - ∑ⱼ xⱼ^{2q})_{2q},
    where η = n^{1/(2q)}.
    Writes η² - xᵢ² = σ₀ + c · (n - ‖x‖_{2q}^{2q}) with σ₀ SOS and c = η²/(qn). -/
theorem eta_sq_sub_in_box_qmod (i : Fin n) (q : ℕ) (hq : 1 ≤ q) (hn : 0 < n) :
    scaledGenerator i q ∈
      GenQuadraticModule (fun _ : Fin 1 => nSubNorm (n := n) q) (2 * q) := by
  -- The coefficient σ₁ = C(η²/(q·n)), a nonneg constant
  set η2 := eta n q ^ 2 with hη2_def
  have heta_pos : 0 < eta n q := by
    unfold eta
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hη2_pos : 0 < η2 := by
    rw [hη2_def]; exact pow_pos heta_pos 2
  have hqn_pos : (0 : ℝ) < q * n := by positivity
  set c : ℝ := η2 / (q * n) with hc_def
  have hc_nonneg : 0 ≤ c := div_nonneg hη2_pos.le hqn_pos.le
  -- Define σ₁ and σ₀
  set σ₁ : MvPolynomial (Fin n) ℝ := MvPolynomial.C c
  set σ₀ : MvPolynomial (Fin n) ℝ := scaledGenerator i q - σ₁ * nSubNorm q
  -- The identity: scaledGenerator = σ₀ + σ₁ * nSubNorm q (by definition)
  -- The GenQM witness
  have hsum_eq : scaledGenerator i q =
      σ₀ + ∑ x : Fin 1, (fun _ => σ₁) x * (fun _ : Fin 1 => nSubNorm q) x := by
    simp only [Fin.sum_univ_one, σ₀]; ring
  refine ⟨σ₀, fun _ => σ₁, ?_, ?_, ?_, ?_, hsum_eq⟩
  · -- σ₀ is SOS
    -- We show σ₀ is a sum of two SOS parts:
    -- Part 1: ∑_{k<q-1} C(c_k) * ((X i)^k * (C(η²) - (X i)²))²  (each term nonneg*sq)
    -- Part 2: C(c) * ∑_{j≠i} ((X j)^q)²                          (nonneg * sum-of-sq)
    -- The identity σ₀ = Part1 + Part2 uses fPoly_identity_scaled.
    have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
    have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hη2_ne : η2 ≠ 0 := ne_of_gt hη2_pos
    -- η^{2q} = n
    have hη2q : (eta n q) ^ (2 * q) = (n : ℝ) := by
      rw [pow_mul]; exact eta_sq_pow_q hn (by omega : 0 < q)
    -- η2^q = n
    have hη2q' : η2 ^ q = (n : ℝ) := by
      change (eta n q ^ 2) ^ q = ↑n
      rw [← pow_mul]; exact hη2q
    -- c * n = η2 / q
    have hcn : c * (n : ℝ) = η2 / q := by
      rw [hc_def]; field_simp
    -- The SOS polynomial that equals σ₀
    set sos_poly : MvPolynomial (Fin n) ℝ :=
      (∑ k ∈ Finset.range (q - 1),
        MvPolynomial.C ((↑(q - (k + 1)) : ℝ) / (↑q * η2 ^ (k + 1))) *
        ((X i) ^ k * (MvPolynomial.C η2 - (X i) ^ 2)) ^ 2) +
      MvPolynomial.C c * ∑ j ∈ Finset.univ.erase i, ((X j) ^ q) ^ 2
    -- sos_poly is SOS
    have hsos_poly : IsSOS sos_poly := by
      apply IsSOS_add
      · apply IsSOS_sum_finset
        intro k hk
        rw [Finset.mem_range] at hk
        exact IsSOS_nonneg_scale (IsSOS_sq _) _
          (div_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hη2_pos.le _)))
      · exact IsSOS_nonneg_scale (IsSOS_sum_finset (fun j _ => IsSOS_sq _)) c hc_nonneg
    -- Prove σ₀ = sos_poly via MvPolynomial.funext
    suffices h : σ₀ = sos_poly by rw [h]; exact hsos_poly
    -- We will use funext but first establish a real-number identity.
    -- Key identity: for any t : ℝ,
    --   η2 - t² - c*n + c*t^{2q} =
    --     ∑_{k<q-1} ((q-k-1)/(q*η2^{k+1})) * (t^k*(η2-t²))²
    have hreal_id : ∀ t : ℝ,
        η2 - t ^ 2 - c * ↑n + c * t ^ (2 * q) =
        ∑ k ∈ Finset.range (q - 1),
          ↑(q - (k + 1)) / (↑q * η2 ^ (k + 1)) * (t ^ k * (η2 - t ^ 2)) ^ 2 := by
      intro t
      -- Use fPoly_identity_scaled with t / η
      have heta_ne : eta n q ≠ 0 := ne_of_gt heta_pos
      have hfp := fPoly_identity_scaled (t / eta n q) q hq
      -- Rewrite (t/η)^2
      have hdiv2 : (t / eta n q) ^ 2 = t ^ 2 / η2 := by
        rw [div_pow]
      -- Rewrite (t/η)^{2q}
      have hdiv2q : (t / eta n q) ^ (2 * q) = t ^ (2 * q) / ↑n := by
        rw [div_pow, pow_mul (eta n q) 2 q, hη2q']
      -- Rewrite (t/η)^{2k}
      have hdiv2k : ∀ k : ℕ, (t / eta n q) ^ (2 * k) = t ^ (2 * k) / η2 ^ k := by
        intro k; rw [div_pow, pow_mul (eta n q) 2 k, ← hη2_def]
      rw [hdiv2, hdiv2q] at hfp
      simp_rw [hdiv2k] at hfp
      -- hfp : (1 - t²/η2)² * ∑_{k<q-1} (q-(k+1)) * (t^{2k}/η2^k)
      --   + (1 - t^{2q}/n) = q * (1 - t²/η2)
      -- Multiply both sides by η2/q
      have h1 : η2 / ↑q * ((1 - t ^ 2 / η2) ^ 2 *
          ∑ k ∈ Finset.range (q - 1), ↑(q - (k + 1)) * (t ^ (2 * k) / η2 ^ k)) +
          η2 / ↑q * (1 - t ^ (2 * q) / ↑n) =
          η2 / ↑q * (↑q * (1 - t ^ 2 / η2)) := by
        rw [← mul_add, hfp]
      -- Simplify the RHS: η2/q * (q * (1 - t²/η2)) = η2 - t²
      have h2 : η2 / ↑q * (↑q * (1 - t ^ 2 / η2)) = η2 - t ^ 2 := by
        field_simp
      -- Simplify the second term: η2/q * (1 - t^{2q}/n) = c*n - c*t^{2q}
      have h3 : η2 / ↑q * (1 - t ^ (2 * q) / ↑n) = c * ↑n - c * t ^ (2 * q) := by
        rw [hc_def]; field_simp
      -- Simplify the first term: η2/q * ((1-t²/η2)² * ∑...) = ∑ target terms
      have h4 : η2 / ↑q * ((1 - t ^ 2 / η2) ^ 2 *
          ∑ k ∈ Finset.range (q - 1), ↑(q - (k + 1)) * (t ^ (2 * k) / η2 ^ k)) =
          ∑ k ∈ Finset.range (q - 1),
            ↑(q - (k + 1)) / (↑q * η2 ^ (k + 1)) * (t ^ k * (η2 - t ^ 2)) ^ 2 := by
        have hη2_sq : (1 - t ^ 2 / η2) ^ 2 = (η2 - t ^ 2) ^ 2 / η2 ^ 2 := by
          field_simp
        rw [hη2_sq, Finset.mul_sum, Finset.mul_sum]
        congr 1; ext k
        have : (t ^ k * (η2 - t ^ 2)) ^ 2 = t ^ (2 * k) * (η2 - t ^ 2) ^ 2 := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm]
        rw [this]
        field_simp; ring
      rw [h2, h3, h4] at h1; linarith
    -- Prove σ₀ = sos_poly by direct MvPolynomial manipulation + funext
    -- Strategy: rewrite σ₀ into sos_poly's form algebraically.
    --
    -- σ₀ = C η2 - (X i)^2 - C c * (C ↑n - ∑_j (X j)^{2q})
    -- Split ∑_j (X j)^{2q} = (X i)^{2q} + ∑_{j≠i} (X j)^{2q}
    -- σ₀ = C η2 - (X i)^2 - C(c*↑n) + C c * (X i)^{2q} + C c * ∑_{j≠i} (X j)^{2q}
    -- = [C η2 - (X i)^2 - C(c*↑n) + C c * (X i)^{2q}] + C c * ∑_{j≠i} (X j)^{2q}
    -- The bracket equals Part1 (by hreal_id via funext), and
    -- ∑_{j≠i} (X j)^{2q} = ∑ ((X j)^q)^2.
    -- So σ₀ = Part1 + Part2 = sos_poly.
    --
    -- Abbreviations for the two summands of sos_poly:
    set Part1 : MvPolynomial (Fin n) ℝ :=
      ∑ k ∈ Finset.range (q - 1),
        MvPolynomial.C (↑(q - (k + 1)) / (↑q * η2 ^ (k + 1))) *
        ((X i) ^ k * (MvPolynomial.C η2 - (X i) ^ 2)) ^ 2 with hPart1_def
    set Part2 : MvPolynomial (Fin n) ℝ :=
      MvPolynomial.C c * ∑ j ∈ Finset.univ.erase i, ((X j) ^ q) ^ 2 with hPart2_def
    have hsos_eq : sos_poly = Part1 + Part2 := rfl
    -- Step 1: ((X j)^q)^2 = (X j)^{2q}
    have hpow_sq_poly : ∀ j : Fin n,
        ((X j : MvPolynomial (Fin n) ℝ) ^ q) ^ 2 = (X j) ^ (2 * q) := by
      intro j; rw [← pow_mul, Nat.mul_comm]
    -- Step 2: Part2 = C c * ∑_{j≠i} (X j)^{2q}
    have hPart2_alt : Part2 = MvPolynomial.C c *
        ∑ j ∈ Finset.univ.erase i, (X j) ^ (2 * q) := by
      simp only [hPart2_def]
      congr 1; exact Finset.sum_congr rfl (fun j _ => hpow_sq_poly j)
    -- Step 3: σ₀ = [C η2 - (X i)^2 - C(c*↑n) + C c*(X i)^{2q}] + Part2
    have hσ₀_split : σ₀ = (MvPolynomial.C η2 - (X i) ^ 2 -
        MvPolynomial.C (c * ↑n) + MvPolynomial.C c * (X i) ^ (2 * q)) + Part2 := by
      rw [hPart2_alt]
      simp only [σ₀, σ₁, scaledGenerator, nSubNorm, normPoly2q]
      rw [show ∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ (2 * q) =
          (X i) ^ (2 * q) + ∑ j ∈ Finset.univ.erase i, (X j) ^ (2 * q) from
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm]
      simp only [← hη2_def, map_mul, map_natCast]
      ring
    -- Step 4: The bracket equals Part1 (by funext + hreal_id)
    have hbracket : MvPolynomial.C η2 - (X i) ^ 2 -
        MvPolynomial.C (c * ↑n) + MvPolynomial.C c * (X i) ^ (2 * q) = Part1 := by
      apply MvPolynomial.funext
      intro x
      simp only [hPart1_def, map_add, map_sub, map_mul, map_pow, map_sum,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      have hid := hreal_id (x i)
      linarith
    -- Conclude: σ₀ = bracket + Part2 = Part1 + Part2 = sos_poly
    rw [hσ₀_split, hbracket]
  · -- σ₁ is SOS (nonneg constant)
    intro _
    exact IsSOS_C_nonneg c hc_nonneg
  · -- deg(σ₀) ≤ 2q
    -- σ₀ = scaledGenerator i q - C(c) * nSubNorm q
    -- deg(scaledGenerator) ≤ 2, deg(C(c) * nSubNorm q) ≤ 0 + 2q = 2q
    -- So deg(σ₀) ≤ max(2, 2q) = 2q
    calc σ₀.totalDegree
        = (scaledGenerator i q - σ₁ * nSubNorm q).totalDegree := rfl
      _ ≤ max (scaledGenerator i q).totalDegree (σ₁ * nSubNorm q).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ ≤ max 2 (2 * q) := by
          apply max_le_max
          · exact totalDegree_scaledGenerator i q
          · calc (σ₁ * nSubNorm q).totalDegree
                ≤ σ₁.totalDegree + (nSubNorm q).totalDegree :=
                  MvPolynomial.totalDegree_mul _ _
              _ ≤ 0 + 2 * q := by
                  apply Nat.add_le_add
                  · exact le_of_eq (MvPolynomial.totalDegree_C _)
                  · exact totalDegree_nSubNorm q hq
              _ = 2 * q := by omega
      _ = 2 * q := by omega
  · -- deg(σ₁ * nSubNorm q) ≤ 2q
    intro _
    calc (σ₁ * nSubNorm (n := n) q).totalDegree
        ≤ σ₁.totalDegree + (nSubNorm q).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 2 * q := by
          apply Nat.add_le_add
          · exact le_of_eq (MvPolynomial.totalDegree_C _)
          · exact totalDegree_nSubNorm q hq
      _ = 2 * q := by omega

/-! ## n - ∑ xᵢ^{2q} ∈ Q(1-x₁²,...,1-xₙ²)_{2q} -/

/-- The geometric sum: 1 + x² + x⁴ + ... + x^{2(q-1)} -/
def geometricSumPoly (i : Fin n) (q : ℕ) : MvPolynomial (Fin n) ℝ :=
  ∑ k ∈ Finset.range q, (X i) ^ (2 * k)

/-- The geometric sum is SOS (each x^{2k} = (x^k)² is a square). -/
theorem geometricSumPoly_isSOS (i : Fin n) (q : ℕ) :
    IsSOS (geometricSumPoly i q) := by
  unfold geometricSumPoly
  apply IsSOS_sum_finset
  intro k _
  refine ⟨1, fun _ => (X i) ^ k, ?_⟩
  simp only [Fin.sum_univ_one, sq]
  ring

/-- The geometric sum identity (as multivariate polynomials):
    (1 - xᵢ²) · (1 + xᵢ² + ... + xᵢ^{2(q-1)}) = 1 - xᵢ^{2q}. -/
theorem geometric_sum_identity (i : Fin n) (q : ℕ) :
    BoxSemialgebraicGenerator i * geometricSumPoly i q = higherGenerator i q := by
  unfold BoxSemialgebraicGenerator geometricSumPoly higherGenerator
  -- We need (1 - (X i)^2) * (∑ k in range q, (X i) ^ (2*k)) = 1 - (X i)^(2*q)
  -- This follows from geom_sum_mul_neg with x = (X i)^2
  have h := geom_sum_mul_neg ((X i : MvPolynomial (Fin n) ℝ) ^ 2) q
  simp only [← pow_mul] at h
  rw [mul_comm]
  exact h

/-- **n - ∑ xⱼ^{2q} ∈ Q(1-x₁²,...,1-xₙ²)_{2q}**.
    Proof: n - ∑ⱼ xⱼ^{2q} = ∑ⱼ (1 - xⱼ^{2q})
                             = ∑ⱼ (1-xⱼ²)(1+xⱼ²+...+xⱼ^{2(q-1)})
                             = ∑ⱼ gⱼ · sⱼ
    where gⱼ = 1 - xⱼ² is the j-th BoxSemialgebraicGenerator and
    sⱼ = 1 + xⱼ² + ... + xⱼ^{2(q-1)} is SOS.
    This has degree 2q, so it's in Q(g₁,...,gₙ)_{2q}. -/
theorem n_sub_norm_in_box_qmod (q : ℕ) (_hq : 1 ≤ q) :
    nSubNorm (n := n) q ∈ BoxQuadraticModule n (2 * q) := by
  -- nSubNorm q = C n - ∑ⱼ Xⱼ^{2q} = ∑ⱼ (1 - Xⱼ^{2q})
  --            = ∑ⱼ BoxSemialgebraicGenerator j * geometricSumPoly j q
  -- This is 0 + ∑ⱼ (geometricSumPoly j q) * (BoxSemialgebraicGenerator j)
  -- where 0 is SOS, each geometricSumPoly j q is SOS, and degree ≤ 2q.
  refine ⟨0, fun j => geometricSumPoly j q, IsSOS_zero, ?_, ?_, ?_, ?_⟩
  · intro j; exact geometricSumPoly_isSOS j q
  · simp
  · intro j
    have : geometricSumPoly j q * BoxSemialgebraicGenerator j =
        BoxSemialgebraicGenerator j * geometricSumPoly j q := mul_comm _ _
    rw [this, geometric_sum_identity]
    exact totalDegree_higherGenerator j q
  · -- Need: nSubNorm q = 0 + ∑ j, geometricSumPoly j q * BoxSemialgebraicGenerator j
    simp only [zero_add]
    -- ∑ j, geometricSumPoly j q * BoxSemialgebraicGenerator j = nSubNorm q
    have hid : ∀ j : Fin n, geometricSumPoly j q * BoxSemialgebraicGenerator j =
        higherGenerator j q := by
      intro j; rw [mul_comm]; exact geometric_sum_identity j q
    simp_rw [hid]
    -- ∑ j, higherGenerator j q = ∑ j, (1 - Xⱼ^{2q}) = n - ∑ j, Xⱼ^{2q} = nSubNorm q
    change nSubNorm (n := n) q = ∑ j : Fin n, higherGenerator j q
    simp only [higherGenerator, nSubNorm, normPoly2q, Finset.sum_sub_distrib,
               Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
               map_natCast]

/-! ## Combining the ingredients -/

/-- The higher generators can be expressed in the standard quadratic module.
    For each i: 1 - xᵢ^{2q} = (1-xᵢ²)(1+xᵢ²+...+xᵢ^{2(q-1)}) ∈ Q(g)_{2q}. -/
theorem higherGenerator_in_box_qmod (i : Fin n) (q : ℕ) (_hq : 1 ≤ q) :
    higherGenerator i q ∈ BoxQuadraticModule n (2 * q) := by
  -- 1 - xᵢ^{2q} = (1 - xᵢ²) * geometricSumPoly
  --   = BoxSemialgebraicGenerator i * geometricSumPoly i q
  -- Write as: 0 + geometricSumPoly i q * g_i + ∑_{j≠i} 0 * g_j
  let σ : Fin n → MvPolynomial (Fin n) ℝ :=
    Function.update (fun _ => 0) i (geometricSumPoly i q)
  refine ⟨0, σ, IsSOS_zero, ?_, ?_, ?_, ?_⟩
  · intro j; by_cases hj : j = i
    · simp only [σ, hj, Function.update_self]; exact geometricSumPoly_isSOS i q
    · simp only [σ, Function.update_of_ne hj]; exact IsSOS_zero
  · exact Nat.zero_le _
  · intro j; by_cases hj : j = i
    · simp only [σ, hj, Function.update_self]
      rw [mul_comm, geometric_sum_identity]
      exact totalDegree_higherGenerator i q
    · simp only [σ, Function.update_of_ne hj, zero_mul]; exact Nat.zero_le _
  · simp only [σ, zero_add]
    rw [← geometric_sum_identity i q]
    rw [Finset.sum_eq_single i
      (fun j _ hj => by rw [Function.update_of_ne hj, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [Function.update_self, mul_comm]

/-- Each `BoxSemialgebraicGenerator` (1-xᵢ²) can be expressed in the quadratic module
    generated by the higher generators (1-xⱼ^{2q}), using arXiv v3 Lemmas 24 and 25
    as intermediate steps. -/
theorem semialg_gen_in_highergen_box_qmod (i : Fin n) (q : ℕ) (hq : 1 ≤ q) :
    BoxSemialgebraicGenerator i ∈
      GenQuadraticModule (fun j : Fin n => higherGenerator j q) (2 * q) := by
  -- By arXiv v3 Lemma 25 (`one_sub_sq_in_box_qmod`), the box generator is in
  -- GenQM({1-xᵢ^{2q}})_{2q}.
  -- Extract the witness from the single-generator QM.
  obtain ⟨σ₀, σ₁, hsos₀, hsos₁, hdeg₀, hdeg₁, hsum⟩ :=
    one_sub_sq_in_box_qmod i q hq
  -- Embed into the n-generator QM: use σ₁ (Fin 1 → ...) at position i, 0 elsewhere
  refine ⟨σ₀, Function.update 0 i (σ₁ 0), hsos₀, ?_, hdeg₀, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hsos₁ 0
    · rw [Function.update_of_ne hj, Pi.zero_apply]; exact IsSOS_zero
  · intro j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hdeg₁ 0
    · rw [Function.update_of_ne hj, Pi.zero_apply, zero_mul]; exact Nat.zero_le _
  · rw [hsum]
    congr 1
    rw [show (∑ i_1 : Fin 1, σ₁ i_1 * higherGenerator i q) =
      σ₁ 0 * higherGenerator i q from by simp]
    rw [Finset.sum_eq_single i
      (fun j _ hj => by rw [Function.update_of_ne hj, Pi.zero_apply, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [Function.update_self]

/-! ## Product bounds for preordering-to-box_qmod conversion -/

/-- For the degree shift from preordering to quadratic module (arXiv v3, Lemma 24(ii)),
    we need bounds on products of the scaled generators in terms of the
    quadratic module generated by n - ‖x‖_{2q}. -/
theorem prod_scaledGenerator_in_box_qmod {s : Finset (Fin n)} (q : ℕ)
    (hq : 1 ≤ q) (hn : 0 < n) :
    (∏ i ∈ s, scaledGenerator i q) ∈
      GenQuadraticModule (fun _ : Fin 1 => nSubNorm (n := n) q)
        ((∏ i ∈ s, scaledGenerator i q).totalDegree + s.card * (2 * q - 2)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    -- ∏_∅ = 1 is SOS with degree 0
    simp only [Finset.prod_empty, Finset.card_empty, Nat.zero_mul, add_zero]
    have : (1 : MvPolynomial (Fin n) ℝ) = 1 ^ 2 := by ring
    rw [this]
    exact sos_mem_GenQuadraticModule (1 ^ 2) (IsSOS_sq 1) (by simp)
  | @insert j s' hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    -- Let P = ∏_{s'} scaledGenerator i q, h = scaledGenerator j q
    set P := ∏ i ∈ s', scaledGenerator i q with hP_def
    set h := scaledGenerator j q with hh_def
    -- By IH: P ∈ GenQM({nSubNorm q})(totalDeg(P) + |s'|*(2q-2))
    -- By eta_sq_sub_in_box_qmod: h ∈ GenQM({nSubNorm q})(2q)
    have h_mem : h ∈ GenQuadraticModule (fun _ : Fin 1 => nSubNorm (n := n) q) (2 * q) :=
      eta_sq_sub_in_box_qmod j q hq hn
    -- By GenQuadraticModule_single_mul:
    -- P * h ∈ GenQM({nSubNorm q})(totalDeg(P) + |s'|*(2q-2) + 2q)
    have hmul := GenQuadraticModule_single_mul ih h_mem
    -- Now use GenQuadraticModule_mono to get the target degree
    -- Target: totalDeg(P * h) + (|s'|+1)*(2q-2)
    -- Have: totalDeg(P) + |s'|*(2q-2) + 2q
    -- Since P and h are nonzero over an integral domain:
    -- totalDeg(P * h) = totalDeg(P) + totalDeg(h) = totalDeg(P) + 2
    have hP_ne : P ≠ 0 := prod_scaledGenerator_ne_zero q
    have hh_ne : h ≠ 0 := scaledGenerator_ne_zero j q
    have hdeg_prod : (P * h).totalDegree = P.totalDegree + h.totalDegree :=
      MvPolynomial.totalDegree_mul_of_isDomain hP_ne hh_ne
    have hdeg_h : h.totalDegree = 2 := totalDegree_scaledGenerator_eq j q
    -- Target degree: totalDeg(P) + 2 + (|s'|+1)*(2q-2)
    --             = totalDeg(P) + 2 + |s'|*(2q-2) + (2q-2)
    --             = totalDeg(P) + |s'|*(2q-2) + 2q
    -- Source degree: totalDeg(P) + |s'|*(2q-2) + 2q
    -- They're equal!
    rw [mul_comm]
    apply GenQuadraticModule_mono _ hmul
    rw [hdeg_prod, hdeg_h]
    have : (s'.card + 1) * (2 * q - 2) = s'.card * (2 * q - 2) + (2 * q - 2) := by ring
    omega

/-- The exact total degree of `nSubNorm` is 2q when n ≥ 1 and q ≥ 1.
    This is needed for the degree-shift argument in arXiv v3, Theorem 27. -/
theorem totalDegree_nSubNorm_eq (q : ℕ) (hq : 1 ≤ q) (hn : 0 < n) :
    (nSubNorm (n := n) q).totalDegree = 2 * q := by
  apply le_antisymm
  · exact totalDegree_nSubNorm q hq
  · -- Exhibit a monomial of degree 2*q in the support
    set j₀ : Fin n := ⟨0, hn⟩
    set s : Fin n →₀ ℕ := Finsupp.single j₀ (2 * q) with hs_def
    have hs_sum : s.sum (fun _ e => e) = 2 * q :=
      Finsupp.sum_single_index rfl
    rw [← hs_sum]
    apply MvPolynomial.le_totalDegree
    rw [MvPolynomial.mem_support_iff]
    -- coeff s (C n - normPoly2q q) = 0 - 1 = -1 ≠ 0
    simp only [nSubNorm, MvPolynomial.coeff_sub]
    have hs_ne : s ≠ 0 := Finsupp.single_ne_zero.mpr (by omega)
    have hC : (MvPolynomial.C (n : ℝ) : MvPolynomial (Fin n) ℝ).coeff s = 0 := by
      rw [MvPolynomial.coeff_C]
      exact ite_eq_right (fun h => hs_ne h.symm)
    have hN : (normPoly2q (n := n) q).coeff s = 1 := by
      simp only [normPoly2q, MvPolynomial.coeff_sum, MvPolynomial.coeff_X_pow]
      rw [Finset.sum_eq_single j₀]
      · simp [hs_def]
      · intro j _ hj
        simp only [hs_def, ite_eq_right_iff, one_ne_zero]
        intro heq
        exact absurd ((Finsupp.single_left_inj (by omega : (2 * q) ≠ 0)).mp heq) hj
      · exact fun h => absurd (Finset.mem_univ j₀) h
    rw [hC, hN]
    norm_num

/-! ## ArXiv v3, Theorem 27: BoxPreordering to quadratic module -/

/-- **ArXiv v3, Theorem 27**: The main degree-shifting theorem.
    T(η²-x₁²,...,η²-xₙ²)_k ⊆ Q(1-x₁²,...,1-xₙ²)_{k + n·(2q-2)}.

    Proof chain:
    Step 1: T(h)_k ⊆ Q(n-‖x‖_{2q})_{k+n·(2q-2)} via Lemmas 24(ii) and 26.
    Step 2: Q(n-‖x‖_{2q})_d ⊆ Q(g)_d since n-‖x‖_{2q} ∈ Q(g)_{2q} by the
            geometric sum identity, combined with Lemma 24(i). -/
theorem box_preordering_to_box_quadratic_module (q : ℕ) (hq : 1 ≤ q) (hn : 0 < n)
    (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ GenPreordering (fun i : Fin n => scaledGenerator i q) k) :
    p ∈ BoxQuadraticModule n (k + n * (2 * q - 2)) := by
  -- Step 1: T(scaledGen)_k ⊆ Q({nSubNorm q})_{k + n*(2q-2)}
  -- via degree_shift_box_preo_to_box_qmod + prod_scaledGenerator_in_box_qmod
  have step1 : p ∈ GenQuadraticModule (fun _ : Fin 1 => nSubNorm (n := n) q)
      (k + n * (2 * q - 2)) := by
    apply degree_shift_box_preo_to_box_qmod
        (fun J => prod_scaledGenerator_in_box_qmod q hq hn) p hp
  -- Step 2: Q({nSubNorm q})_d ⊆ Q(BoxSemialgebraicGenerator)_{d+0}
  -- via degree_shift_box_qmod + n_sub_norm_in_box_qmod
  have step2 : p ∈ GenQuadraticModule
      (fun i : Fin n => BoxSemialgebraicGenerator i)
      (k + n * (2 * q - 2) + 0) := by
    apply degree_shift_box_qmod (h := fun _ : Fin 1 => nSubNorm (n := n) q) (l := 0)
    · intro i
      rw [add_zero]
      -- The goal is: nSubNorm q ∈ GenQM(SemialgebraicGen)(totalDeg(nSubNorm q))
      -- By totalDegree_nSubNorm_eq, totalDeg(nSubNorm q) = 2*q
      -- And n_sub_norm_in_box_qmod gives nSubNorm q ∈ BoxQuadraticModule n (2*q)
      rw [totalDegree_nSubNorm_eq q hq hn]
      have h := n_sub_norm_in_box_qmod (n := n) q hq
      rw [BoxQuadraticModule_eq_GenQuadraticModule] at h
      exact h
    · exact step1
  rw [add_zero] at step2
  rw [BoxQuadraticModule_eq_GenQuadraticModule]
  exact step2

/-! ## Corollary: degree bound for Schmüdgen-type certificates -/

/-- The degree shift constant: n · (2q - 2).
    When q is chosen as a function of the approximation parameter,
    this gives the additional degree cost of moving from a preordering
    certificate to a quadratic module certificate. -/
def degreeShiftConst (n q : ℕ) : ℕ := n * (2 * q - 2)

theorem degreeShiftConst_eq (hq : 2 ≤ q) :
    degreeShiftConst n q = 2 * n * (q - 1) := by
  unfold degreeShiftConst
  have h1 : 2 * q - 2 = 2 * (q - 1) := by omega
  rw [h1]; ring

/-- For q = 1, the degree shift is zero (no extra cost). -/
theorem degreeShiftConst_one : degreeShiftConst n 1 = 0 := by
  unfold degreeShiftConst; simp

/-- Monotonicity: the degree shift constant increases with q. -/
theorem degreeShiftConst_mono {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) :
    degreeShiftConst n q₁ ≤ degreeShiftConst n q₂ := by
  unfold degreeShiftConst
  apply Nat.mul_le_mul_left
  apply Nat.sub_le_sub_right
  exact Nat.mul_le_mul_left 2 hq

/-! ## Connecting back to the standard definitions -/

/-- The standard preordering T(1-x₁²,...,1-xₙ²)_r coincides with
    the generalized preordering for the SemialgebraicGenerators. -/
theorem BoxPreordering_eq_GenPreordering :
    BoxPreordering n r =
      GenPreordering (fun i : Fin n => BoxSemialgebraicGenerator i) r := by
  ext p
  constructor
  · rintro ⟨σ, hsos, hdeg, hsum⟩
    -- Need to convert from Finset (Fin n)-indexed to powerset-indexed
    -- The existing BoxPreordering sums over powerset of Fin n
    -- and uses BoxSemialgebraicGeneratorProd J = ∏ j ∈ J, BoxSemialgebraicGenerator j
    refine ⟨σ, hsos, ?_, hsum⟩
    intro J; exact hdeg J
  · rintro ⟨σ, hsos, hdeg, hsum⟩
    exact ⟨σ, hsos, hdeg, hsum⟩

/-- Convenience reformulation of arXiv v3, Theorem 27 using `BoxPreordering`:
    If p is in the preordering of scaled generators at degree k,
    then p is in the standard quadratic module at degree k + n·(2q-2). -/
theorem box_preordering_scaledGen_to_box_qmod (q : ℕ) (hq : 1 ≤ q) (hn : 0 < n)
    (k : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p ∈ GenPreordering (fun i : Fin n => scaledGenerator i q) k) :
    p ∈ BoxQuadraticModule n (k + degreeShiftConst n q) := by
  unfold degreeShiftConst
  exact box_preordering_to_box_quadratic_module q hq hn k p hp

/-! ## Auxiliary: totalDegree bounds for generators -/

theorem totalDegree_BoxSemialgebraicGenerator (i : Fin n) :
    (BoxSemialgebraicGenerator i).totalDegree ≤ 2 := by
  show (BoxSemialgebraicGenerator i).totalDegree ≤ 2
  unfold BoxSemialgebraicGenerator
  have h1 : (1 : MvPolynomial (Fin n) ℝ).totalDegree = 0 := MvPolynomial.totalDegree_one
  have h2 : ((X i : MvPolynomial (Fin n) ℝ) ^ 2).totalDegree = 2 :=
    MvPolynomial.totalDegree_X_pow i 2
  calc ((1 : MvPolynomial (Fin n) ℝ) - (X i) ^ 2).totalDegree
      ≤ max (1 : MvPolynomial (Fin n) ℝ).totalDegree ((X i) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ = max 0 2 := by rw [h1, h2]
    _ = 2 := by omega

end OptimalConvergenceRates

end
