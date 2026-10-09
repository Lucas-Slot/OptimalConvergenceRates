/-
  OptimalConvergenceRates/SlotLaurent2022/JacksonKernel.lean

  Jackson kernel coefficients, positivity, polynomial form, and quadrature reproducing identities.
-/
import OptimalConvergenceRates.Chebyshev.GaussChebyshevQuadrature
import OptimalConvergenceRates.MarkovLukacz.MarkovLukacz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric

open Real Finset Set MvPolynomial

noncomputable section

namespace OptimalConvergenceRates

/-! ## Jackson kernel parameters -/

/-- θ_r = π / (r + 2), the Jackson kernel angle parameter -/
noncomputable def jacksonTheta (r : ℕ) : ℝ :=
  Real.pi / (r + 2 : ℝ)

/-- The Jackson coefficient `λ_k^r`.
    For k = 0 we set λ_0^r = 1.
    For 1 ≤ k ≤ r:
      λ_k^r = (1/(r+2)) · ((r+2-k) · cos(k·θ_r) + sin(k·θ_r)/sin(θ_r) · cos(θ_r))
    For k > r we set λ_k^r = 0. -/
noncomputable def jacksonCoeff (k r : ℕ) : ℝ :=
  if k = 0 then 1
  else if k ≤ r then
    let θ := jacksonTheta r
    (1 / (r + 2 : ℝ)) *
      ((r + 2 - k : ℝ) * Real.cos (k * θ) +
       Real.sin (k * θ) / Real.sin θ * Real.cos θ)
  else 0

/-- Multivariate Jackson coefficient: λ_κ^r = ∏_i λ_{κ_i}^r -/
noncomputable def jacksonCoeffMulti {n : ℕ} (κ : Fin n → ℕ) (r : ℕ) : ℝ :=
  ∏ i : Fin n, jacksonCoeff (κ i) r

/-! ## Jackson kernel as a real-valued function -/

/-- The univariate Jackson kernel as a function:
    K^ja_r(x,y) = 1 + 2 ∑_{k=1}^r λ_k^r T_k(x) T_k(y) -/
noncomputable def jacksonKernelUni (r : ℕ) (x y : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.range r, jacksonCoeff (k + 1) r *
    (chebyshevT (k + 1)).eval x *
    (chebyshevT (k + 1)).eval y

/-! ## Helper lemmas about `jacksonTheta` -/

private lemma r_plus_two_pos (r : ℕ) : (0 : ℝ) < (r : ℝ) + 2 := by positivity

private lemma jacksonTheta_pos (r : ℕ) : 0 < jacksonTheta r := by
  unfold jacksonTheta
  exact div_pos pi_pos (r_plus_two_pos r)

private lemma jacksonTheta_lt_pi (r : ℕ) : jacksonTheta r < π := by
  unfold jacksonTheta
  rw [div_lt_iff₀ (r_plus_two_pos r)]
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith [pi_pos]

private lemma sin_jacksonTheta_pos (r : ℕ) : 0 < Real.sin (jacksonTheta r) :=
  sin_pos_of_pos_of_lt_pi (jacksonTheta_pos r) (jacksonTheta_lt_pi r)

private lemma jacksonTheta_le_pi_div_two (r : ℕ) : jacksonTheta r ≤ π / 2 := by
  unfold jacksonTheta
  have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have h2 : (0 : ℝ) < (r : ℝ) + 2 := by linarith
  rw [div_le_div_iff₀ h2 (show (0:ℝ) < 2 from by positivity)]
  nlinarith [pi_pos]

private lemma cos_jacksonTheta_nonneg (r : ℕ) : 0 ≤ Real.cos (jacksonTheta r) := by
  apply cos_nonneg_of_mem_Icc
  exact ⟨by linarith [jacksonTheta_pos r, pi_pos], jacksonTheta_le_pi_div_two r⟩

/-! ## Spectral factorization definitions for nonnegativity proof -/

/-- G(t) = 1/2 + ∑_{k=1}^r λ_k cos(kt), the half-kernel in angle space. -/
noncomputable def jacksonG (r : ℕ) (t : ℝ) : ℝ :=
  1 / 2 + ∑ k ∈ Finset.range r, jacksonCoeff (k + 1) r * Real.cos ((k + 1) * t)

/-- Spectral factor coefficient c_k = sin((k+1)·θ_r). -/
noncomputable def jacksonC (r : ℕ) (k : ℕ) : ℝ :=
  Real.sin ((k + 1) * jacksonTheta r)

/-- Cosine component A(t) = ∑_{k=0}^r c_k cos(kt). -/
noncomputable def jacksonA (r : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (r + 1), jacksonC r k * Real.cos (k * t)

/-- Sine component B(t) = ∑_{k=0}^r c_k sin(kt). -/
noncomputable def jacksonB (r : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (r + 1), jacksonC r k * Real.sin (k * t)

/-! ## Additional helper lemmas for Jackson coefficient positivity -/

/-- For `0 < a < b ≤ π`, `sin` is strictly concave on `[0, π]` with `sin 0 = 0`, so
    `sin(a)/a > sin(b)/b`, equivalently `b * sin a > a * sin b`. -/
private lemma mul_sin_gt_of_lt {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ π) :
    a * Real.sin b < b * Real.sin a := by
  -- From strict concavity: sin(t*b) > t*sin(b) for t = a/b ∈ (0,1)
  -- i.e., sin(a) > (a/b)*sin(b), i.e., b*sin(a) > a*sin(b)
  have hb_pos : (0 : ℝ) < b := lt_trans ha hab
  have hab_ratio : a / b < 1 := (div_lt_one hb_pos).mpr hab
  have ha_ratio : 0 < a / b := div_pos ha hb_pos
  have hb_ratio : 0 < 1 - a / b := by linarith
  have hsum : a / b + (1 - a / b) = 1 := by ring
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_refl _, pi_pos.le⟩
  have hb_mem : b ∈ Set.Icc 0 π := ⟨hb_pos.le, hb⟩
  have hne : b ≠ 0 := ne_of_gt hb_pos
  -- Apply strict concavity: (a/b) * sin(b) + (1 - a/b) * sin(0) < sin((a/b)*b + (1-a/b)*0)
  have hsc := strictConcaveOn_sin_Icc.2 hb_mem h0_mem hne ha_ratio hb_ratio hsum
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, add_zero, div_mul_cancel₀ _ hne] at hsc
  -- hsc : a/b * sin(b) < sin(a)
  have := (div_lt_iff₀ hb_pos).mp (by rwa [div_mul_eq_mul_div] at hsc)
  linarith

/-! ## Proposition 3: Key properties of the Jackson kernel -/

/-! ### Step 1: Kernel decomposition K(cos α, cos β) = G(α-β) + G(α+β) -/

private lemma jacksonKernelUni_eq_trig (r : ℕ) (α β : ℝ) :
    jacksonKernelUni r (Real.cos α) (Real.cos β) =
    jacksonG r (α - β) + jacksonG r (α + β) := by
  unfold jacksonKernelUni jacksonG
  simp_rw [chebyshevT_cos]
  -- Each term: 2 * λ_k * cos(kα) * cos(kβ) = λ_k * (cos(k(α-β)) + cos(k(α+β)))
  have hterm : ∀ k ∈ Finset.range r,
      2 * (jacksonCoeff (k + 1) r * Real.cos ((↑k + 1) * α) *
        Real.cos ((↑k + 1) * β)) =
      jacksonCoeff (k + 1) r * Real.cos ((↑k + 1) * (α - β)) +
      jacksonCoeff (k + 1) r * Real.cos ((↑k + 1) * (α + β)) := by
    intro k _
    have h := Real.two_mul_cos_mul_cos ((↑k + 1) * α) ((↑k + 1) * β)
    have h1 : (↑k + 1) * α - (↑k + 1) * β = (↑k + 1) * (α - β) := by ring
    have h2 : (↑k + 1) * α + (↑k + 1) * β = (↑k + 1) * (α + β) := by ring
    rw [h1, h2] at h
    -- h : 2 * cos(A) * cos(B) = cos(C) + cos(D)
    -- goal: 2 * (λ * cos(A) * cos(B)) = λ * cos(C) + λ * cos(D)
    have : 2 * (jacksonCoeff (k + 1) r * Real.cos ((↑k + 1) * α) *
        Real.cos ((↑k + 1) * β)) =
      jacksonCoeff (k + 1) r * (2 * Real.cos ((↑k + 1) * α) * Real.cos ((↑k + 1) * β)) := by ring
    rw [this, h]; ring
  -- Distribute 2 * Σ into Σ (2 * ...)
  simp_rw [Finset.mul_sum]
  -- Now use hterm: need to match the right cast pattern
  have hterm' : ∀ k ∈ Finset.range r,
      2 * (jacksonCoeff (k + 1) r * Real.cos (↑(k + 1) * α) *
        Real.cos (↑(k + 1) * β)) =
      jacksonCoeff (k + 1) r * Real.cos (↑(k + 1) * (α - β)) +
      jacksonCoeff (k + 1) r * Real.cos (↑(k + 1) * (α + β)) := by
    intro k hk
    have h := Real.two_mul_cos_mul_cos (↑(k + 1) * α) (↑(k + 1) * β)
    have h1 : ↑(k + 1) * α - ↑(k + 1) * β = ↑(k + 1) * (α - β) := by ring
    have h2 : ↑(k + 1) * α + ↑(k + 1) * β = ↑(k + 1) * (α + β) := by ring
    rw [h1, h2] at h
    have : 2 * (jacksonCoeff (k + 1) r * Real.cos (↑(k + 1) * α) *
        Real.cos (↑(k + 1) * β)) =
      jacksonCoeff (k + 1) r * (2 * Real.cos (↑(k + 1) * α) * Real.cos (↑(k + 1) * β)) := by ring
    rw [this, h]; ring
  rw [Finset.sum_congr rfl hterm']
  simp only [Finset.sum_add_distrib]
  -- The goal now is: 1 + (∑...) + (∑...) = (1/2 + ∑...) + (1/2 + ∑...)
  norm_num
  ring

/-! ### Step 2: Trigonometric sum helpers -/

/-- Roots-of-unity cosine sum: Σ_{j=0}^{N-2} cos(2(j+1)π/N) = -1 for N ≥ 2.
    Proved by telescoping with 2sin(π/N). -/
private lemma cos_sum_eq_neg_one (N : ℕ) (hN : 2 ≤ N) :
    ∑ j ∈ Finset.range (N - 1),
      Real.cos (2 * (↑j + 1) * Real.pi / ↑N) = -1 := by
  have hN_pos : (0 : ℝ) < ↑N := by positivity
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  -- sin(π/N) > 0 since 0 < π/N < π
  have hα_pos : 0 < Real.pi / ↑N := div_pos Real.pi_pos hN_pos
  have hα_lt_pi : Real.pi / ↑N < Real.pi := by
    have : (1 : ℝ) < ↑N := by exact_mod_cast (show 1 < N by omega)
    rw [div_lt_iff₀ hN_pos]
    nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin (Real.pi / ↑N) :=
    Real.sin_pos_of_pos_of_lt_pi hα_pos hα_lt_pi
  -- Suffices: 2·sin(π/N)·S = -2·sin(π/N), then S = -1
  suffices hkey : 2 * Real.sin (Real.pi / ↑N) *
      ∑ j ∈ Finset.range (N - 1),
        Real.cos (2 * (↑j + 1) * Real.pi / ↑N) =
      -(2 * Real.sin (Real.pi / ↑N)) by
    have h2sin_ne : (2 * Real.sin (Real.pi / ↑N)) ≠ 0 := by positivity
    have hmul : (2 * Real.sin (Real.pi / ↑N)) *
        (∑ j ∈ Finset.range (N - 1),
          Real.cos (2 * (↑j + 1) * Real.pi / ↑N)) =
      (2 * Real.sin (Real.pi / ↑N)) * (-1) := by linarith
    exact mul_left_cancel₀ h2sin_ne hmul
  rw [Finset.mul_sum]
  -- Each term telescopes via 2sin(B)cos(A) = sin(A+B) - sin(A-B)
  have hterm : ∀ j ∈ Finset.range (N - 1),
      2 * Real.sin (Real.pi / ↑N) * Real.cos (2 * (↑j + 1) * Real.pi / ↑N) =
      Real.sin ((2 * ↑j + 3) * Real.pi / ↑N) -
        Real.sin ((2 * ↑j + 1) * Real.pi / ↑N) := by
    intro j _
    have h := Real.sin_add (2 * (↑j + 1) * Real.pi / ↑N) (Real.pi / ↑N)
    have h' := Real.sin_sub (2 * (↑j + 1) * Real.pi / ↑N) (Real.pi / ↑N)
    have heq_add : 2 * (↑j + 1) * Real.pi / ↑N + Real.pi / ↑N =
        (2 * ↑j + 3) * Real.pi / ↑N := by field_simp; ring
    have heq_sub : 2 * (↑j + 1) * Real.pi / ↑N - Real.pi / ↑N =
        (2 * ↑j + 1) * Real.pi / ↑N := by field_simp; ring
    rw [heq_add] at h; rw [heq_sub] at h'; linarith
  rw [Finset.sum_congr rfl hterm]
  -- Telescope by induction
  have htel : ∀ p : ℕ, ∑ j ∈ Finset.range p,
      (Real.sin ((2 * ↑j + 3) * Real.pi / ↑N) -
       Real.sin ((2 * ↑j + 1) * Real.pi / ↑N)) =
      Real.sin ((2 * ↑p + 1) * Real.pi / ↑N) -
        Real.sin (Real.pi / ↑N) := by
    intro p; induction p with
    | zero => simp
    | succ p ih =>
      rw [Finset.sum_range_succ, ih]; push_cast; ring_nf
  rw [htel]
  -- sin((2(N-1)+1)π/N) = sin((2N-1)π/N) = sin(2π - π/N) = -sin(π/N)
  have harg : (2 * (↑(N - 1) : ℝ) + 1) * Real.pi / ↑N = 2 * Real.pi - Real.pi / ↑N := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]; field_simp; ring
  rw [harg, Real.sin_two_pi_sub]; ring

/-- Sum of sin²((k+1)θ_r) = (r+2)/2 for the spectral factorization. -/
private lemma sin_sq_sum (r : ℕ) :
    ∑ k ∈ Finset.range (r + 1),
      jacksonC r k ^ 2 = (r + 2 : ℝ) / 2 := by
  unfold jacksonC
  -- sin²(x) = (1 - cos(2x))/2
  have hrewrite : ∀ k ∈ Finset.range (r + 1),
      Real.sin ((↑k + 1) * jacksonTheta r) ^ 2 =
      1 / 2 - Real.cos (2 * ((↑k + 1) * jacksonTheta r)) / 2 := by
    intro k _
    have hcos2 := Real.cos_two_mul ((↑k + 1) * jacksonTheta r)
    -- cos(2x) = 2cos²x - 1, so cos²x = (1+cos(2x))/2
    -- sin²x = 1 - cos²x = 1 - (1+cos(2x))/2 = (1-cos(2x))/2 = 1/2 - cos(2x)/2
    have h := Real.sin_sq_add_cos_sq ((↑k + 1) * jacksonTheta r)
    nlinarith
  rw [Finset.sum_congr rfl hrewrite, Finset.sum_sub_distrib]
  simp_rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Now: (r+1) * (1/2) - Σ cos(2(k+1)θ) / 2 = (r+2)/2
  -- θ = π/(r+2), so 2(k+1)θ = 2(k+1)π/(r+2)
  have hθ : jacksonTheta r = Real.pi / (↑r + 2) := rfl
  have hcos_rewrite : ∀ k ∈ Finset.range (r + 1),
      Real.cos (2 * ((↑k + 1) * jacksonTheta r)) / 2 =
      Real.cos (2 * (↑k + 1) * Real.pi / (↑r + 2)) / 2 := by
    intro k _
    have h : (2 : ℝ) * ((↑k + 1) * jacksonTheta r) = 2 * (↑k + 1) * Real.pi / (↑r + 2) := by
      rw [hθ]; field_simp
    rw [h]
  rw [Finset.sum_congr rfl hcos_rewrite]
  -- Factor out /2 from sum
  have h_div : ∑ k ∈ Finset.range (r + 1),
      Real.cos (2 * (↑k + 1) * Real.pi / (↑r + 2)) / 2 =
    (∑ k ∈ Finset.range (r + 1),
      Real.cos (2 * (↑k + 1) * Real.pi / (↑r + 2))) / 2 := by
    rw [Finset.sum_div]
  rw [h_div]
  -- Goal: ↑(r+1) * (1/2) - (∑ k in range(r+1), cos(2*(↑k+1)*π/(↑r+2))) / 2 = (↑r+2)/2
  -- Apply cos_sum_eq_neg_one with N = r+2
  have hN : r + 1 = (r + 2) - 1 := by omega
  rw [hN]
  have hcast : ∀ k ∈ Finset.range ((r + 2) - 1),
      Real.cos (2 * (↑k + 1) * Real.pi / (↑r + 2)) =
      Real.cos (2 * (↑k + 1) * Real.pi / ↑(r + 2)) := by
    intro k _; congr 1; push_cast; ring
  rw [Finset.sum_congr rfl hcast, cos_sum_eq_neg_one (r + 2) (by omega)]
  push_cast; ring

/-- Telescoping cosine sum for the autocorrelation identity.
    For 1 ≤ m ≤ r: Σ_{k=0}^{r-m} cos((2k+m+2)θ) = -sin((m+1)θ)/sin(θ)
    where θ = π/(r+2). -/
private lemma arithmetic_cos_sum (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r) :
    ∑ k ∈ Finset.range (r + 1 - m),
      Real.cos ((2 * ↑k + ↑m + 2) * jacksonTheta r) =
    -Real.sin ((↑m + 1) * jacksonTheta r) / Real.sin (jacksonTheta r) := by
  set θ := jacksonTheta r with hθ_def
  have hθ_pos : 0 < θ := jacksonTheta_pos r
  have hsin_pos : 0 < Real.sin θ := sin_jacksonTheta_pos r
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
  have hNθ : ((r : ℝ) + 2) * θ = Real.pi := by
    simp [hθ_def, jacksonTheta]; field_simp
  -- Suffices: 2sin(θ) · S = -2sin((m+1)θ)
  suffices hkey : 2 * Real.sin θ *
      ∑ k ∈ Finset.range (r + 1 - m),
        Real.cos ((2 * ↑k + ↑m + 2) * θ) =
      -(2 * Real.sin ((↑m + 1) * θ)) by
    have h2sin_ne : (2 * Real.sin θ) ≠ 0 := by positivity
    have h : 2 * Real.sin θ * (-Real.sin ((↑m + 1) * θ) / Real.sin θ) =
        -(2 * Real.sin ((↑m + 1) * θ)) := by
      field_simp
    have hmul := hkey.trans h.symm
    exact mul_left_cancel₀ h2sin_ne hmul
  rw [Finset.mul_sum]
  -- Each term: 2sin(θ)cos(A) = sin(A+θ) - sin(A-θ)
  have hterm : ∀ k ∈ Finset.range (r + 1 - m),
      2 * Real.sin θ * Real.cos ((2 * ↑k + ↑m + 2) * θ) =
      Real.sin ((2 * ↑k + ↑m + 3) * θ) -
        Real.sin ((2 * ↑k + ↑m + 1) * θ) := by
    intro k _
    have h := Real.sin_add ((2 * ↑k + ↑m + 2) * θ) θ
    have h' := Real.sin_sub ((2 * ↑k + ↑m + 2) * θ) θ
    have heq_add : (2 * ↑k + ↑m + 2) * θ + θ = (2 * ↑k + ↑m + 3) * θ := by ring
    have heq_sub : (2 * ↑k + ↑m + 2) * θ - θ = (2 * ↑k + ↑m + 1) * θ := by ring
    rw [heq_add] at h; rw [heq_sub] at h'; linarith
  rw [Finset.sum_congr rfl hterm]
  -- Telescope by induction
  have htel : ∀ p : ℕ, ∑ j ∈ Finset.range p,
      (Real.sin ((2 * ↑j + ↑m + 3) * θ) -
       Real.sin ((2 * ↑j + ↑m + 1) * θ)) =
      Real.sin ((2 * ↑p + ↑m + 1) * θ) -
        Real.sin ((↑m + 1) * θ) := by
    intro p; induction p with
    | zero => simp
    | succ p ih =>
      rw [Finset.sum_range_succ, ih]; push_cast; ring_nf
  rw [htel]
  -- sin((2(r+1-m) + m + 1)θ) = sin((2r+3-m)θ) = sin((2(r+2)-(m+1))θ)
  -- = sin(2π - (m+1)θ) = -sin((m+1)θ)
  have harg : (2 * (↑(r + 1 - m) : ℝ) + ↑m + 1) * θ =
      2 * ((↑r + 2) * θ) - (↑m + 1) * θ := by
    rw [Nat.cast_sub (by omega : m ≤ r + 1)]; push_cast; ring
  rw [harg, hNθ, Real.sin_two_pi_sub]; ring

/-! ### Step 3: Autocorrelation identity -/

/-- Autocorrelation identity: (2/N) Σ_{k=0}^{r-m} c_{k+m} c_k = λ_m for 1 ≤ m ≤ r.
    Here c_k = sin((k+1)θ) and λ_m = jacksonCoeff m r. -/
private lemma autocorrelation_sum (r m : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r) :
    (2 / (r + 2 : ℝ)) * ∑ k ∈ Finset.range (r + 1 - m),
      jacksonC r (k + m) * jacksonC r k = jacksonCoeff m r := by
  set θ := jacksonTheta r with hθ_def
  set N := (r : ℝ) + 2 with hN_def
  have hN_pos : (0 : ℝ) < N := r_plus_two_pos r
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hsin_pos : 0 < Real.sin θ := sin_jacksonTheta_pos r
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
  unfold jacksonC
  -- Apply product-to-sum: 2sin(A)sin(B) = cos(A-B) - cos(A+B)
  have hprod : ∀ k ∈ Finset.range (r + 1 - m),
      2 * (Real.sin ((↑(k + m) + 1) * θ) * Real.sin ((↑k + 1) * θ)) =
      Real.cos ((↑m : ℝ) * θ) - Real.cos ((2 * ↑k + ↑m + 2) * θ) := by
    intro k _
    have h := Real.two_mul_sin_mul_sin ((↑(k + m) + 1) * θ) ((↑k + 1) * θ)
    have h1 : (↑(k + m) + 1) * θ - (↑k + 1) * θ = (↑m : ℝ) * θ := by push_cast; ring
    have h2 : (↑(k + m) + 1) * θ + (↑k + 1) * θ = (2 * ↑k + ↑m + 2) * θ := by push_cast; ring
    rw [h1, h2] at h; linarith
  -- 2 * Σ c_{k+m} c_k = Σ (cos(mθ) - cos((2k+m+2)θ))
  have hsum : 2 * ∑ k ∈ Finset.range (r + 1 - m),
      Real.sin ((↑(k + m) + 1) * θ) * Real.sin ((↑k + 1) * θ) =
    (↑(r + 1 - m) : ℝ) * Real.cos ((↑m : ℝ) * θ) -
      ∑ k ∈ Finset.range (r + 1 - m),
        Real.cos ((2 * ↑k + ↑m + 2) * θ) := by
    rw [Finset.mul_sum]
    have : ∀ k ∈ Finset.range (r + 1 - m),
        2 * (Real.sin ((↑(k + m) + 1) * θ) * Real.sin ((↑k + 1) * θ)) =
        Real.cos ((↑m : ℝ) * θ) - Real.cos ((2 * ↑k + ↑m + 2) * θ) :=
      fun k hk => hprod k hk
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Apply arithmetic_cos_sum
  have hcos_sum := arithmetic_cos_sum r m hm hmr
  -- sin((m+1)θ) = sin(mθ)cos(θ) + cos(mθ)sin(θ)
  have hsin_add : Real.sin ((↑m + 1) * θ) =
      Real.sin (↑m * θ) * Real.cos θ + Real.cos (↑m * θ) * Real.sin θ := by
    rw [show (↑m + 1) * θ = ↑m * θ + θ from by ring]; exact Real.sin_add _ _
  have hrm_cast : (↑(r + 1 - m) : ℝ) = ↑r + 1 - ↑m := by
    rw [Nat.cast_sub (by omega : m ≤ r + 1)]; push_cast; ring
  -- From hsum + hcos_sum: 2*Σ = (r+1-m)*cos(mθ) + sin((m+1)θ)/sin(θ)
  have hsum2 : 2 * ∑ k ∈ Finset.range (r + 1 - m),
      Real.sin ((↑(k + m) + 1) * θ) * Real.sin ((↑k + 1) * θ) =
    (↑(r + 1 - m) : ℝ) * Real.cos ((↑m : ℝ) * θ) +
      Real.sin ((↑m + 1) * θ) / Real.sin θ := by
    rw [hsum, hcos_sum]; ring
  -- sin((m+1)θ)/sin(θ) = sin(mθ)cos(θ)/sin(θ) + cos(mθ)
  have hsin_ratio : Real.sin ((↑m + 1) * θ) / Real.sin θ =
      Real.sin (↑m * θ) * Real.cos θ / Real.sin θ + Real.cos (↑m * θ) := by
    rw [hsin_add, add_div, mul_div_cancel_of_imp (fun h => absurd h hsin_ne)]
  -- So 2*Σ = (r+1-m)*cos(mθ) + sin(mθ)*cos(θ)/sin(θ) + cos(mθ)
  --        = (r+2-m)*cos(mθ) + sin(mθ)*cos(θ)/sin(θ)
  -- And (2/N)*Σ = (1/N)*((r+2-m)*cos(mθ) + sin(mθ)/sin(θ)*cos(θ))
  -- which is exactly jacksonCoeff m r.
  unfold jacksonCoeff
  simp only [show m ≠ 0 from by omega, ite_false, hmr, ite_true]
  -- Goal: (2/(r+2)) * Σ = (1/(r+2)) * (...)
  -- i.e., 2*Σ = (r+2-m)*cos(mθ) + sin(mθ)/sin(θ)*cos(θ)
  -- From hsum2: 2*Σ = (r+1-m)*cos(mθ) + sin((m+1)θ)/sin(θ)
  --           = (r+1-m)*cos(mθ) + sin(mθ)*cos(θ)/sin(θ) + cos(mθ)
  --           = (r+2-m)*cos(mθ) + sin(mθ)*cos(θ)/sin(θ)
  -- Both sides have factor 1/(r+2), so suffices: 2*Σ = (r+2-m)*cos(mθ) + sin(mθ)/sin(θ)*cos(θ)
  -- First, show the 2*Σ equals the RHS expression, then the fractions match.
  suffices hsuff : 2 * ∑ k ∈ Finset.range (r + 1 - m),
      Real.sin ((↑(k + m) + 1) * θ) * Real.sin ((↑k + 1) * θ) =
    (↑r + 2 - ↑m) * Real.cos ((↑m : ℝ) * θ) +
      Real.sin ((↑m : ℝ) * θ) / Real.sin θ * Real.cos θ by
    simp only [hN_def, hθ_def] at *
    rw [show (2 : ℝ) / (↑r + 2) *
      ∑ k ∈ Finset.range (r + 1 - m),
        Real.sin ((↑(k + m) + 1) * jacksonTheta r) *
          Real.sin ((↑k + 1) * jacksonTheta r) =
      (2 * ∑ k ∈ Finset.range (r + 1 - m),
        Real.sin ((↑(k + m) + 1) * jacksonTheta r) *
          Real.sin ((↑k + 1) * jacksonTheta r)) / (↑r + 2) from by ring]
    rw [hsuff]
    ring
  -- Now prove: 2*Σ = (r+2-m)*cos(mθ) + sin(mθ)/sin(θ)*cos(θ)
  -- From hsum2: 2*Σ = (r+1-m)*cos(mθ) + sin((m+1)θ)/sin(θ)
  -- From hsin_ratio: sin((m+1)θ)/sin(θ) = sin(mθ)*cos(θ)/sin(θ) + cos(mθ)
  rw [hsum2, hsin_ratio, hrm_cast]
  ring

/-! ### Step 4: Spectral factorization G = (1/N)(A² + B²) -/

/-- A² + B² expanded as a double sum using cos(a-b) identity. -/
private lemma ABsq_eq_double_sum (r : ℕ) (t : ℝ) :
    jacksonA r t ^ 2 + jacksonB r t ^ 2 =
    ∑ k ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r + 1),
      jacksonC r k * jacksonC r l * Real.cos ((↑k - ↑l) * t) := by
  have hA : jacksonA r t ^ 2 = ∑ k ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r + 1),
      jacksonC r k * Real.cos (↑k * t) * (jacksonC r l * Real.cos (↑l * t)) := by
    unfold jacksonA; simp_rw [sq, Finset.sum_mul_sum]
  have hB : jacksonB r t ^ 2 = ∑ k ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r + 1),
      jacksonC r k * Real.sin (↑k * t) * (jacksonC r l * Real.sin (↑l * t)) := by
    unfold jacksonB; simp_rw [sq, Finset.sum_mul_sum]
  calc jacksonA r t ^ 2 + jacksonB r t ^ 2
      = (∑ k ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r + 1),
          jacksonC r k * Real.cos (↑k * t) * (jacksonC r l * Real.cos (↑l * t))) +
        (∑ k ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r + 1),
          jacksonC r k * Real.sin (↑k * t) * (jacksonC r l * Real.sin (↑l * t))) := by rw [hA, hB]
    _ = ∑ k ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r + 1),
        (jacksonC r k * Real.cos (↑k * t) * (jacksonC r l * Real.cos (↑l * t)) +
         jacksonC r k * Real.sin (↑k * t) * (jacksonC r l * Real.sin (↑l * t))) := by
      simp only [← Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.range (r + 1), ∑ l ∈ Finset.range (r + 1),
        jacksonC r k * jacksonC r l * Real.cos ((↑k - ↑l) * t) := by
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      have hcos := Real.cos_sub (↑k * t) (↑l * t)
      rw [show ↑k * t - ↑l * t = (↑k - ↑l) * t from by ring] at hcos
      -- hcos : cos(kt)*cos(lt) + sin(kt)*sin(lt) = cos((k-l)*t)
      -- Goal: c_k*cos(kt)*(c_l*cos(lt)) + c_k*sin(kt)*(c_l*sin(lt)) = c_k*c_l*cos((k-l)*t)
      have : jacksonC r k * Real.cos (↑k * t) * (jacksonC r l * Real.cos (↑l * t)) +
             jacksonC r k * Real.sin (↑k * t) * (jacksonC r l * Real.sin (↑l * t)) =
             jacksonC r k * jacksonC r l * (Real.cos (↑k * t) * Real.cos (↑l * t) +
               Real.sin (↑k * t) * Real.sin (↑l * t)) := by ring
      rw [this, hcos]

/-- Double sum reorganization: diagonal extraction and off-diagonal grouping.
    Splits ∑_k ∑_l c_k c_l cos((k-l)t) into diagonal + off-diagonal terms.

    The key identity:
    ∑_{k=0}^n ∑_{l=0}^n c_k c_l cos((k-l)t) =
      ∑_{k=0}^n c_k² + 2 ∑_{d=0}^{n-1} (∑_{j=0}^{n-1-d} c_{j+d+1} c_j) cos((d+1)t)
-/
private lemma double_sum_reorganize (n : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      c k * c l * Real.cos ((↑k - ↑l) * t) =
    ∑ k ∈ Finset.range (n + 1), c k ^ 2 +
    2 * ∑ d ∈ Finset.range n,
      (∑ j ∈ Finset.range (n - d), c (j + d + 1) * c j) *
        Real.cos ((↑d + 1) * t) := by
  induction n with
  | zero =>
    simp [sq, mul_comm]
  | succ n ih =>
    -- Write n+1+1 = n+2 throughout
    change ∑ k ∈ Finset.range (n + 2), ∑ l ∈ Finset.range (n + 2),
        c k * c l * Real.cos ((↑k - ↑l) * t) =
      ∑ k ∈ Finset.range (n + 2), c k ^ 2 +
      2 * ∑ d ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1 - d), c (j + d + 1) * c j) *
          Real.cos ((↑d + 1) * t)
    -- Peel outer sum on LHS
    rw [Finset.sum_range_succ (f := fun k =>
      ∑ l ∈ Finset.range (n + 2),
        c k * c l * Real.cos ((↑k - ↑l) * t))]
    -- Peel each inner sum for k ≤ n
    have hinner_peel : ∀ k ∈ Finset.range (n + 1),
        ∑ l ∈ Finset.range (n + 2),
          c k * c l * Real.cos ((↑k - ↑l) * t) =
        (∑ l ∈ Finset.range (n + 1),
          c k * c l * Real.cos ((↑k - ↑l) * t)) +
        c k * c (n + 1) * Real.cos ((↑k - ↑(n + 1)) * t) := by
      intro k _; rw [Finset.sum_range_succ]
    rw [Finset.sum_congr rfl hinner_peel, Finset.sum_add_distrib]
    -- Apply IH to ∑_{k<n+1} ∑_{l<n+1}
    rw [ih]
    -- Peel the last inner sum (for k = n+1)
    rw [Finset.sum_range_succ (f := fun l =>
      c (n + 1) * c l * Real.cos ((↑(n + 1) - ↑l) * t))]
    -- Simplify the diagonal term c(n+1)*c(n+1)*cos(0) = c(n+1)^2
    have hdiag : c (n + 1) * c (n + 1) *
        Real.cos ((↑(n + 1) - ↑(n + 1)) * t) = c (n + 1) ^ 2 := by
      simp [sub_self, Real.cos_zero, sq]
    rw [hdiag]
    -- Use cos(-x) = cos(x) to match the two cross-term sums
    have hcos_neg : ∀ k ∈ Finset.range (n + 1),
        c k * c (n + 1) * Real.cos ((↑k - ↑(n + 1)) * t) =
        c (n + 1) * c k * Real.cos ((↑(n + 1) - ↑k) * t) := by
      intro k _
      have : (↑k - ↑(n + 1)) * t = -((↑(n + 1) - ↑k) * t) := by ring
      rw [this, Real.cos_neg]; ring
    rw [Finset.sum_congr rfl hcos_neg]
    -- RHS: peel diagonal and off-diagonal sums
    rw [Finset.sum_range_succ (f := fun k => c k ^ 2)]
    rw [Finset.sum_range_succ (f := fun d =>
      (∑ j ∈ Finset.range (n + 1 - d),
        c (j + d + 1) * c j) * Real.cos ((↑d + 1) * t))]
    -- Split inner sums on RHS for d ≤ n-1: range(n+1-d) = range(n-d) ++ [n-d]
    have hsplit_inner : ∀ d ∈ Finset.range n,
        (∑ j ∈ Finset.range (n + 1 - d), c (j + d + 1) * c j) *
          Real.cos ((↑d + 1) * t) =
        ((∑ j ∈ Finset.range (n - d), c (j + d + 1) * c j) *
          Real.cos ((↑d + 1) * t) +
        c (n + 1) * c (n - d) * Real.cos ((↑d + 1) * t)) := by
      intro d hd
      have hd_lt : d < n := Finset.mem_range.mp hd
      rw [show n + 1 - d = (n - d) + 1 from by omega, Finset.sum_range_succ]
      rw [show n - d + d + 1 = n + 1 from by omega]; ring
    rw [Finset.sum_congr rfl hsplit_inner, Finset.sum_add_distrib]
    -- The d = n term: inner sum over range(n+1-n) = range(1)
    rw [show n + 1 - n = 1 from by omega, Finset.sum_range_one]
    -- The cross sum ∑_{k<n+1} c(n+1)*c(k)*cos((n+1-k)*t) appears twice.
    -- Re-index via k ↦ n-k: ∑_{k=0}^{n} f(k) = ∑_{d=0}^{n} f(n-d) =
    -- ∑_{d=0}^{n} c(n+1)*c(n-d)*cos((d+1)*t)
    -- This is sum_range_reflect.
    have hreindex :
        ∑ k ∈ Finset.range (n + 1), c (n + 1) * c k *
          Real.cos ((↑(n + 1) - ↑k) * t) =
        ∑ d ∈ Finset.range (n + 1), c (n + 1) * c (n - d) *
          Real.cos ((↑d + 1) * t) := by
      set g : ℕ → ℝ := fun k => c (n + 1) * c k * Real.cos ((↑(n + 1) - ↑k) * t)
      have hrefl := Finset.sum_range_reflect g (n + 1)
      rw [← hrefl]
      apply Finset.sum_congr rfl; intro k hk
      have hk_lt : k < n + 1 := Finset.mem_range.mp hk
      have hk_le_n : k ≤ n := by omega
      -- g(n+1-1-k) = g(n-k) = c(n+1)*c(n-k)*cos((↑(n+1)-↑(n-k))*t)
      -- Need: ↑(n+1) - ↑(n-k) = ↑k + 1 in ℝ
      change g (n + 1 - 1 - k) = c (n + 1) * c (n - k) * Real.cos ((↑k + 1) * t)
      simp only [g, show n + 1 - 1 - k = n - k from by omega]
      have h1 : (↑(n - k) : ℝ) = ↑n - ↑k := Nat.cast_sub hk_le_n
      have h2 : (↑(n + 1) : ℝ) = ↑n + 1 := by push_cast; ring
      have h3 : (↑(n + 1) - ↑(n - k) : ℝ) = ↑k + 1 := by linarith
      rw [show (↑(n + 1) - ↑(n - k)) * t = (↑k + 1) * t from by rw [h3]]
    -- Rewrite the two cross sums using hreindex
    simp only [hreindex]
    -- Peel d=n from the reindexed sum: ∑_{d<n+1} = ∑_{d<n} + (d=n term)
    simp only [Finset.sum_range_succ_comm (f := fun d =>
      c (n + 1) * c (n - d) * Real.cos ((↑d + 1) * t))]
    simp only [show n - n = 0 from by omega]
    -- Peel the RHS diagonal sum: ∑_{k<n+2} c(k)^2 = ∑_{k<n} c(k)^2 + c(n)^2 + c(n+1)^2
    rw [show n + 2 = (n + 1) + 1 from by omega,
        Finset.sum_range_succ (f := fun k => c k ^ 2),
        Finset.sum_range_succ (f := fun k => c k ^ 2)]
    -- Normalize 0+n+1 to n+1
    simp only [show 0 + n + 1 = n + 1 from by omega]
    -- Both sides now have identical atomic summands, just reordered; close by linarith
    linarith

/-- The key spectral factorization: G(t) = (1/(r+2)) · (A(t)² + B(t)²).
    Proof strategy: multiply both sides by N = r+2 and show N·G = A²+B²
    by matching constant and cosine terms using sin_sq_sum and autocorrelation_sum. -/
private lemma jacksonG_eq_sq (r : ℕ) (t : ℝ) :
    jacksonG r t = (1 / (r + 2 : ℝ)) * (jacksonA r t ^ 2 + jacksonB r t ^ 2) := by
  set N := (r : ℝ) + 2 with hN_def
  have hN_pos : (0 : ℝ) < N := r_plus_two_pos r
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  -- Suffices: N * G = A² + B²
  suffices hsuff : N * jacksonG r t = jacksonA r t ^ 2 + jacksonB r t ^ 2 by
    field_simp; linarith
  -- Step 1: Expand N * G
  have hNG : N * jacksonG r t = N / 2 +
      ∑ k ∈ Finset.range r, N * jacksonCoeff (k + 1) r * Real.cos ((↑k + 1) * t) := by
    unfold jacksonG
    rw [mul_add, mul_one_div, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro k _; ring
  rw [hNG]
  -- Step 2: Expand A² + B² using the double sum
  rw [ABsq_eq_double_sum]
  -- Step 3: Reorganize the double sum using double_sum_reorganize
  rw [double_sum_reorganize r (jacksonC r) t]
  -- Now goal: N/2 + ∑_{k<r} N*λ_{k+1}*cos((k+1)t)
  --         = ∑_{k<r+1} c_k² + 2*∑_{d<r} (∑_{j<r-d} c(j+d+1)c(j)) cos((d+1)t)
  -- Match constant terms: N/2 = ∑ c_k² by sin_sq_sum
  -- Match cosine terms: N*λ_{k+1} = 2*∑_{j<r-k} c(j+k+1)c(j) by autocorrelation_sum
  have hconst : (N : ℝ) / 2 = ∑ k ∈ Finset.range (r + 1), jacksonC r k ^ 2 := by
    rw [sin_sq_sum]
  rw [hconst]
  -- Now goal: ∑ c_k^2 + ∑_{k<r} N*λ_{k+1}*cos((k+1)t)
  --         = ∑ c_k^2 + 2*∑_{d<r} (∑_{j<r-d} c(j+d+1)c(j)) cos((d+1)t)
  -- Cancel the diagonal sums
  congr 1
  -- Match cosine coefficients: need to pull the 2 inside and match term by term
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_lt : k < r := Finset.mem_range.mp hk
  -- Need: N * jacksonCoeff (k+1) r * cos((k+1)t)
  --     = 2 * (∑_{j<r-k} c(j+k+1)c(j)) * cos((k+1)t)
  -- i.e., N * λ_{k+1} = 2 * ∑_{j<r-k} c(j+k+1)*c(j)
  -- From autocorrelation_sum: (2/N) * ∑_{j<r+1-(k+1)} c(j+(k+1))*c(j) = λ_{k+1}
  -- i.e., 2 * ∑ = N * λ_{k+1}
  have hac := autocorrelation_sum r (k + 1) (by omega) (by omega)
  -- hac : (2 / N) * ∑_{j<r+1-(k+1)} c(j+(k+1))*c(j) = jacksonCoeff (k+1) r
  have hrange_eq : r + 1 - (k + 1) = r - k := by omega
  -- From hac: N * jacksonCoeff (k+1) r = 2 * ∑ ...
  have hcoeff : N * jacksonCoeff (k + 1) r =
      2 * ∑ j ∈ Finset.range (r - k), jacksonC r (j + k + 1) * jacksonC r j := by
    -- hac : (2 / (r + 2 : ℝ)) * ∑ ... = jacksonCoeff (k+1) r
    rw [hrange_eq] at hac
    simp_rw [show ∀ j, j + (k + 1) = j + k + 1 from fun j => by omega] at hac
    have hN_eq : N = (r : ℝ) + 2 := rfl
    rw [hN_eq]
    field_simp at hac ⊢
    linarith
  -- Now multiply by cos and wrap with 2*
  calc N * jacksonCoeff (k + 1) r * Real.cos ((↑k + 1) * t)
      = (N * jacksonCoeff (k + 1) r) * Real.cos ((↑k + 1) * t) := by ring
    _ = (2 * ∑ j ∈ Finset.range (r - k),
          jacksonC r (j + k + 1) * jacksonC r j) *
          Real.cos ((↑k + 1) * t) := by rw [hcoeff]
    _ = 2 * ((∑ j ∈ Finset.range (r - k),
          jacksonC r (j + k + 1) * jacksonC r j) *
          Real.cos ((↑k + 1) * t)) := by ring

/-- Nonnegativity of G: G(t) ≥ 0 follows from G = (1/N)(A²+B²). -/
private lemma jacksonG_nonneg (r : ℕ) (t : ℝ) : 0 ≤ jacksonG r t := by
  rw [jacksonG_eq_sq]
  apply mul_nonneg
  · apply div_nonneg one_pos.le; exact (r_plus_two_pos r).le
  · exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-! ### Step 5: Final assembly -/

/-- Proposition 3(i): The Jackson kernel is nonneg on [-1,1]². -/
theorem jackson_nonneg (r : ℕ) (x y : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ jacksonKernelUni r x y := by
  set α := Real.arccos x
  set β := Real.arccos y
  have hx_eq : x = Real.cos α := (Real.cos_arccos hx.1 hx.2).symm
  have hy_eq : y = Real.cos β := (Real.cos_arccos hy.1 hy.2).symm
  rw [hx_eq, hy_eq, jacksonKernelUni_eq_trig]
  exact add_nonneg (jacksonG_nonneg r _) (jacksonG_nonneg r _)

/-- Product-to-sum identity: 2 cos(A) sin(B) = sin(A+B) - sin(A-B) -/
private lemma two_cos_mul_sin (A B : ℝ) :
    2 * Real.cos A * Real.sin B = Real.sin (A + B) - Real.sin (A - B) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- For k ≤ r with k ≠ 0, the inner expression of the Jackson coefficient is positive.
    Uses the identity 2 sin(θ) E = (m+2) sin(mθ) - m sin((m+2)θ) where m = r+1-k,
    combined with the strict decrease of sinc on (0, π]. -/
private lemma jackson_inner_pos {k r : ℕ} (hk : k ≤ r) (hk0 : k ≠ 0) :
    0 < ((r : ℝ) + 2 - (k : ℝ)) * Real.cos ((k : ℝ) * jacksonTheta r) +
      Real.sin ((k : ℝ) * jacksonTheta r) / Real.sin (jacksonTheta r) *
        Real.cos (jacksonTheta r) := by
  set θ := jacksonTheta r with hθ_def
  set N := (r : ℝ) + 2 with hN_def
  -- It suffices to show that 2 * sin(θ) * E > 0 (since sin(θ) > 0)
  have hsinθ : 0 < Real.sin θ := sin_jacksonTheta_pos r
  -- Suffices to show the numerator is positive after clearing sin(θ) > 0
  suffices hsuff : 0 < (N - ↑k) * Real.cos (↑k * θ) * Real.sin θ +
      Real.sin (↑k * θ) * Real.cos θ by
    have heq : (N - ↑k) * Real.cos (↑k * θ) +
        Real.sin (↑k * θ) / Real.sin θ * Real.cos θ =
      ((N - ↑k) * Real.cos (↑k * θ) * Real.sin θ +
        Real.sin (↑k * θ) * Real.cos θ) / Real.sin θ := by
      field_simp
    rw [heq]; exact div_pos hsuff hsinθ
  -- Step 1: Use sin_add to rewrite sin(kθ)*cos(θ) + cos(kθ)*sin(θ) = sin((k+1)θ)
  -- So the expression = (N - k - 1)*cos(kθ)*sin(θ) + sin((k+1)*θ)
  have hsin_add : Real.sin ((k : ℝ) * θ) * Real.cos θ + Real.cos ((k : ℝ) * θ) * Real.sin θ =
      Real.sin (((k : ℝ) + 1) * θ) := by
    rw [← Real.sin_add]; ring_nf
  -- Step 2: Use the product-to-sum: 2*cos(kθ)*sin(θ) = sin((k+1)θ) - sin((k-1)θ)
  have hprod : 2 * Real.cos ((k : ℝ) * θ) * Real.sin θ =
      Real.sin (((k : ℝ) + 1) * θ) - Real.sin (((k : ℝ) - 1) * θ) := by
    have := two_cos_mul_sin ((k : ℝ) * θ) θ
    convert this using 2 <;> ring_nf
  -- Step 3: Therefore 2*sin(θ)*E = (N-k+1)*sin((k+1)*θ) - (N-k-1)*sin((k-1)*θ)
  -- But we use the sin_pi_sub identity to rewrite.
  -- sin((k+1)*θ) = sin(π - (k+1)*θ) = sin((N-k-1)*θ) since (k+1+N-k-1)*θ = N*θ = π
  -- sin((k-1)*θ) = sin(π - (k-1)*θ) = sin((N-k+1)*θ)
  have hNθ : N * θ = π := by simp only [hN_def, hθ_def, jacksonTheta]; field_simp
  have hsin_sym1 : Real.sin (((k : ℝ) + 1) * θ) = Real.sin ((N - (k : ℝ) - 1) * θ) := by
    conv_lhs => rw [show ((k : ℝ) + 1) * θ = π - (N - (k : ℝ) - 1) * θ by nlinarith]
    exact Real.sin_pi_sub _
  have hsin_sym2 : Real.sin (((k : ℝ) - 1) * θ) = Real.sin ((N - (k : ℝ) + 1) * θ) := by
    conv_lhs => rw [show ((k : ℝ) - 1) * θ = π - (N - (k : ℝ) + 1) * θ by nlinarith]
    exact Real.sin_pi_sub _
  -- Set m = N - k - 1 = r + 1 - k (as real)
  set m := N - (k : ℝ) - 1 with hm_def
  -- Then N - k + 1 = m + 2 (as reals)
  have hm2 : N - (k : ℝ) + 1 = m + 2 := by simp only [hm_def]; ring
  -- Now the key inequality via mul_sin_gt_of_lt:
  -- We need (m+2) * sin(m*θ) > m * sin((m+2)*θ)
  -- This follows from mul_sin_gt_of_lt with a = m*θ, b = (m+2)*θ
  have hm_pos : 0 < m := by
    simp only [hm_def, hN_def]
    have : (k : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr hk
    have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
    linarith
  have hmθ_pos : 0 < m * θ := mul_pos hm_pos (jacksonTheta_pos r)
  have hm2θ_pos : 0 < (m + 2) * θ := mul_pos (by linarith) (jacksonTheta_pos r)
  have hmθ_lt : m * θ < (m + 2) * θ := by
    apply mul_lt_mul_of_pos_right _ (jacksonTheta_pos r)
    linarith
  have hm2θ_le_pi : (m + 2) * θ ≤ π := by
    have hk_ge : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hk0)
    calc (m + 2) * θ = (N - (k : ℝ) + 1) * θ := by rw [hm2]
      _ ≤ N * θ := by
          apply mul_le_mul_of_nonneg_right _ (jacksonTheta_pos r).le
          linarith
      _ = π := hNθ
  -- Apply mul_sin_gt_of_lt
  have hkey : m * θ * Real.sin ((m + 2) * θ) < (m + 2) * θ * Real.sin (m * θ) :=
    mul_sin_gt_of_lt hmθ_pos hmθ_lt hm2θ_le_pi
  -- Divide by θ > 0 to get: m * sin((m+2)*θ) < (m+2) * sin(m*θ)
  have hθ_pos := jacksonTheta_pos r
  have hkey2 : m * Real.sin ((m + 2) * θ) < (m + 2) * Real.sin (m * θ) := by
    have h1 : m * θ * Real.sin ((m + 2) * θ) = θ * (m * Real.sin ((m + 2) * θ)) := by ring
    have h2 : (m + 2) * θ * Real.sin (m * θ) = θ * ((m + 2) * Real.sin (m * θ)) := by ring
    nlinarith
  -- Now we need to connect this to our original goal
  -- Goal: 0 < (N - k)*cos(kθ)*sin(θ) + sin(kθ)*cos(θ)
  -- We showed: (m+2)*sin(mθ) > m*sin((m+2)θ), i.e.,
  --   (N-k+1)*sin((N-k-1)*θ) > (N-k-1)*sin((N-k+1)*θ)
  -- Using hsin_sym1: sin((k+1)*θ) = sin((N-k-1)*θ) = sin(m*θ)
  -- Using hsin_sym2: sin((k-1)*θ) = sin((N-k+1)*θ) = sin((m+2)*θ)
  -- So: (m+2)*sin((k+1)*θ) > m*sin((k-1)*θ)
  -- i.e., (N-k+1)*sin((k+1)*θ) > (N-k-1)*sin((k-1)*θ)
  rw [hsin_sym1, hsin_sym2, hm2] at hprod
  -- Now use hprod and hkey2 to conclude
  -- 2*sin(θ)*(N-k)*cos(kθ) = (N-k)*[sin((k+1)θ) - sin((k-1)θ)]
  --                         = (N-k)*[sin(mθ) - sin((m+2)θ)]
  -- And 2*[sin(kθ)*cos(θ)] = 2*sin(kθ)*cos(θ)
  -- So 2*sin(θ)*E = 2*(N-k)*cos(kθ)*sin(θ) + 2*sin(kθ)*cos(θ)
  -- We need 0 < (N-k)*cos(kθ)*sin(θ) + sin(kθ)*cos(θ)
  -- which is the same as 0 < 2*[(N-k)*cos(kθ)*sin(θ) + sin(kθ)*cos(θ)] / 2
  -- 2*[(N-k)*cos(kθ)*sin(θ)] = (N-k)*[sin((k+1)θ) - sin((k-1)θ)]
  -- and 2*sin(kθ)*cos(θ) = sin((k+1)θ) + sin((k-1)θ)
  -- (from sin_add and sin_sub)
  have hprod2 : 2 * Real.sin ((k : ℝ) * θ) * Real.cos θ =
      Real.sin (((k : ℝ) + 1) * θ) + Real.sin (((k : ℝ) - 1) * θ) := by
    have h := Real.sin_add ((k : ℝ) * θ) θ
    have h' := Real.sin_sub ((k : ℝ) * θ) θ
    have heq1 : ((k : ℝ) * θ + θ) = ((k : ℝ) + 1) * θ := by ring
    have heq2 : ((k : ℝ) * θ - θ) = ((k : ℝ) - 1) * θ := by ring
    rw [heq1] at h; rw [heq2] at h'
    linarith
  -- Now compute 2 * goal:
  suffices h : 0 < 2 * ((N - (k : ℝ)) * Real.cos ((k : ℝ) * θ) * Real.sin θ +
      Real.sin ((k : ℝ) * θ) * Real.cos θ) by linarith
  -- 2 * goal = (N-k)*2*cos(kθ)*sin(θ) + 2*sin(kθ)*cos(θ)
  --          = (N-k)*[sin((k+1)θ) - sin((k-1)θ)] + sin((k+1)θ) + sin((k-1)θ)
  --          = (N-k+1)*sin((k+1)θ) + (1-N+k)*sin((k-1)θ)
  --          = (N-k+1)*sin((k+1)θ) - (N-k-1)*sin((k-1)θ)
  -- Rewriting with sym identities:
  --          = (m+2)*sin(mθ) - m*sin((m+2)θ)
  -- which is > 0 by hkey2
  -- Goal: 0 < 2 * ((N - k) * cos(kθ) * sin(θ) + sin(kθ) * cos(θ))
  -- = (N-k) * [sin((k+1)θ) - sin((k-1)θ)] + sin((k+1)θ) + sin((k-1)θ)  (using hprod, hprod2)
  -- = (N-k+1)*sin((k+1)θ) - (N-k-1)*sin((k-1)θ)
  -- = (m+2)*sin(mθ) - m*sin((m+2)θ)  (using hsin_sym1, hsin_sym2, hm2)
  -- > 0 by hkey2
  nlinarith [hprod, hprod2, hsin_sym1, hsin_sym2, hm2, hkey2]

/-- Proposition 3(ii): Jackson coefficients are positive for k ≤ r -/
theorem jackson_coeff_pos {k r : ℕ} (hk : k ≤ r) :
    0 < jacksonCoeff k r := by
  unfold jacksonCoeff
  split_ifs with hk0
  · -- k = 0: coefficient is 1
    norm_num
  · -- 1 ≤ k ≤ r: use jackson_inner_pos
    apply mul_pos (div_pos one_pos (r_plus_two_pos r))
    exact jackson_inner_pos hk hk0

/-- For k ∈ ℕ with k ≥ 1, θ > 0, and k*θ ≤ π, we have sin(k*θ) ≤ k*sin(θ).
    Proof: sin is concave on [0, π] with sin(0) = 0, so by concavity
    sin(θ) = sin((1/k)·(kθ)) ≥ (1/k)·sin(kθ), giving sin(kθ) ≤ k·sin(θ). -/
private lemma sin_mul_le_mul_sin {k : ℕ} {θ : ℝ} (hk : 1 ≤ k) (hθ : 0 < θ)
    (hkθ : (k : ℝ) * θ ≤ π) :
    Real.sin ((k : ℝ) * θ) ≤ (k : ℝ) * Real.sin θ := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hkθ_nonneg : (0 : ℝ) ≤ (k : ℝ) * θ := mul_nonneg hk_pos.le hθ.le
  have hkθ_mem : (k : ℝ) * θ ∈ Set.Icc 0 π := ⟨hkθ_nonneg, hkθ⟩
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 π := ⟨le_refl _, pi_pos.le⟩
  -- Apply concavity of sin on [0,π] at x = kθ, y = 0, with weights a = 1/k, b = 1-1/k
  have ha : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hb : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one hk_pos]; exact Nat.one_le_cast.mpr hk
  have hab : 1 / (k : ℝ) + (1 - 1 / (k : ℝ)) = 1 := by ring
  have hconc := strictConcaveOn_sin_Icc.concaveOn.2 hkθ_mem h0_mem ha hb hab
  -- hconc : 1/k • sin(kθ) + (1-1/k) • sin(0) ≤ sin(1/k • kθ + (1-1/k) • 0)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, add_zero] at hconc
  -- hconc : 1/k * sin(kθ) ≤ sin(1/k * (kθ))
  -- Note: 1/k * (kθ) = θ
  have hsimp : 1 / (k : ℝ) * ((k : ℝ) * θ) = θ := by field_simp
  rw [hsimp] at hconc
  -- hconc : 1/k * sin(kθ) ≤ sin(θ)
  -- Multiply both sides by k > 0
  have := mul_le_mul_of_nonneg_left hconc hk_pos.le
  rwa [← mul_assoc, mul_div_cancel₀ _ hk_ne, one_mul] at this

/-- Proposition 3(ii): Jackson coefficients are at most 1.
    For 1 ≤ k ≤ r: use sin(kθ) ≤ k·sin(θ) and cos ≤ 1. -/
theorem jackson_coeff_le_one (k r : ℕ) :
    jacksonCoeff k r ≤ 1 := by
  unfold jacksonCoeff
  split_ifs with hk0 hkr
  · -- k = 0: coefficient is 1
    linarith
  · -- 1 ≤ k ≤ r
    -- Need: (1/(r+2)) * ((r+2-k)*cos(kθ) + sin(kθ)/sin(θ)*cos(θ)) ≤ 1
    -- i.e., (r+2-k)*cos(kθ) + sin(kθ)/sin(θ)*cos(θ) ≤ r+2
    set θ := jacksonTheta r
    set N := (r : ℝ) + 2
    have hN_pos : (0 : ℝ) < N := r_plus_two_pos r
    have hsinθ_pos : 0 < Real.sin θ := sin_jacksonTheta_pos r
    have hcosθ_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hcoskθ_le : Real.cos ((k : ℝ) * θ) ≤ 1 := Real.cos_le_one _
    have hk_le_N : (k : ℝ) ≤ N := by
      have : (k : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr hkr
      simp only [N]; linarith
    have hNk_nonneg : (0 : ℝ) ≤ N - (k : ℝ) := by linarith
    -- sin(kθ)/sin(θ) ≤ k
    have hk_ge_1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hkθ_le_pi : (k : ℝ) * θ ≤ π := by
      calc (k : ℝ) * θ ≤ N * θ := by
            apply mul_le_mul_of_nonneg_right hk_le_N (jacksonTheta_pos r).le
        _ = π := by simp [N, θ, jacksonTheta]; field_simp
    have hsinkθ_le : Real.sin ((k : ℝ) * θ) ≤ (k : ℝ) * Real.sin θ :=
      sin_mul_le_mul_sin hk_ge_1 (jacksonTheta_pos r) hkθ_le_pi
    -- sin(kθ)/sin(θ) ≤ k
    have hdiv_le : Real.sin ((k : ℝ) * θ) / Real.sin θ ≤ (k : ℝ) :=
      (div_le_iff₀ hsinθ_pos).mpr hsinkθ_le
    -- Now bound the expression: (1/N) * E ≤ 1, i.e., E ≤ N
    rw [show (1 : ℝ) / N * ((N - (k : ℝ)) * Real.cos ((k : ℝ) * θ) +
        Real.sin ((k : ℝ) * θ) / Real.sin θ * Real.cos θ) ≤ 1 ↔
      (N - (k : ℝ)) * Real.cos ((k : ℝ) * θ) +
        Real.sin ((k : ℝ) * θ) / Real.sin θ * Real.cos θ ≤ N from by
        rw [div_mul_eq_mul_div, one_mul, div_le_one hN_pos]]
    -- Goal: (N-k)*cos(kθ) + sin(kθ)/sin(θ)*cos(θ) ≤ N
    have hcosθ_nonneg : 0 ≤ Real.cos θ := cos_jacksonTheta_nonneg r
    calc (N - (k : ℝ)) * Real.cos ((k : ℝ) * θ) +
          Real.sin ((k : ℝ) * θ) / Real.sin θ * Real.cos θ
        ≤ (N - (k : ℝ)) * 1 + (k : ℝ) * 1 := by
          gcongr
        _ = N := by ring
  · -- k > r: coefficient is 0
    linarith

/-- Proposition 3(iii): Approximation bound |1 - λ_k^r| ≤ π²d²/(r+2)² for k ≤ d ≤ r.
    Uses cos(x) ≥ 1 - x²/2, sin(x) > x - x³/4 (for 0 < x ≤ 1), and sin(x) < x. -/
theorem jackson_coeff_approx {k d r : ℕ} (hk : k ≤ d) (hd : d ≤ r) :
    |1 - jacksonCoeff k r| ≤ Real.pi ^ 2 * d ^ 2 / (r + 2 : ℝ) ^ 2 := by
  have hkr : k ≤ r := le_trans hk hd
  have hcoeff_pos : 0 < jacksonCoeff k r := jackson_coeff_pos hkr
  have hcoeff_le : jacksonCoeff k r ≤ 1 := jackson_coeff_le_one k r
  rw [abs_of_nonneg (by linarith)]
  have hN_pos : (0 : ℝ) < (r : ℝ) + 2 := r_plus_two_pos r
  have hRHS_nonneg : (0 : ℝ) ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 / ((r : ℝ) + 2) ^ 2 := by positivity
  -- Case k = 0
  by_cases hk0 : k = 0
  · subst hk0; simp only [jacksonCoeff, ite_true, sub_self]; exact hRHS_nonneg
  -- Case k ≥ 1: suffices 1 - λ_k ≤ π²k²/(r+2)² then use k ≤ d
  have hk_ge_1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  suffices h : 1 - jacksonCoeff k r ≤ Real.pi ^ 2 * (k : ℝ) ^ 2 / ((r : ℝ) + 2) ^ 2 by
    calc 1 - jacksonCoeff k r ≤ Real.pi ^ 2 * (k : ℝ) ^ 2 / ((r : ℝ) + 2) ^ 2 := h
      _ ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 / ((r : ℝ) + 2) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Nat.cast_nonneg k) (Nat.cast_le.mpr hk) 2) (by positivity)
  -- Setup
  set θ := jacksonTheta r with hθ_def
  set N := (r : ℝ) + 2 with hN_def
  have hθ_pos : 0 < θ := jacksonTheta_pos r
  have hsinθ_pos : 0 < Real.sin θ := sin_jacksonTheta_pos r
  have hkθ_pos : 0 < (k : ℝ) * θ := mul_pos (by positivity) hθ_pos
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hNk_nonneg : (0 : ℝ) ≤ N - (k : ℝ) := by
    have : (k : ℝ) ≤ (r : ℝ) := Nat.cast_le.mpr hkr
    linarith
  -- (kθ)² = π²k²/N²
  have hkθ_sq : ((k : ℝ) * θ) ^ 2 = Real.pi ^ 2 * (k : ℝ) ^ 2 / N ^ 2 := by
    simp only [θ, jacksonTheta, N]; field_simp
  -- Suffices: 1 - λ_k ≤ (kθ)²
  suffices h : 1 - jacksonCoeff k r ≤ ((k : ℝ) * θ) ^ 2 by rwa [hkθ_sq] at h
  -- Unfold the coefficient
  have hcoeff_eq : jacksonCoeff k r =
      (1 / N) * ((N - (k : ℝ)) * Real.cos ((k : ℝ) * θ) +
        Real.sin ((k : ℝ) * θ) / Real.sin θ * Real.cos θ) := by
    unfold jacksonCoeff; simp [hk0, hkr, θ, N]
  -- If (kθ)² ≥ 1 then trivial since 1 - λ_k ≤ 1 ≤ (kθ)²
  by_cases hbig : 1 ≤ ((k : ℝ) * θ) ^ 2
  · linarith
  push_neg at hbig
  have hkθ_lt_one : (k : ℝ) * θ < 1 := by
    rwa [sq_lt_one_iff_abs_lt_one, abs_of_pos hkθ_pos] at hbig
  have hθ_lt_one : θ < 1 :=
    lt_of_le_of_lt (le_mul_of_one_le_left hθ_pos.le (Nat.one_le_cast.mpr hk_ge_1)) hkθ_lt_one
  have hkθ_le_one : (k : ℝ) * θ ≤ 1 := hkθ_lt_one.le
  have hθ_le_one : θ ≤ 1 := hθ_lt_one.le
  -- Key trig bounds
  -- (A) cos(kθ) ≥ 1 - (kθ)²/2
  have hcos_lb : 1 - ((k : ℝ) * θ) ^ 2 / 2 ≤ Real.cos ((k : ℝ) * θ) :=
    Real.one_sub_sq_div_two_le_cos
  -- (B) sin(kθ) > kθ - (kθ)³/4
  have hsin_lb : (k : ℝ) * θ - ((k : ℝ) * θ) ^ 3 / 4 < Real.sin ((k : ℝ) * θ) :=
    Real.sin_gt_sub_cube hkθ_pos hkθ_le_one
  -- (C) sin(θ) < θ
  have hsin_ub : Real.sin θ < θ := Real.sin_lt hθ_pos
  -- (D) cos(θ) ≥ 1 - θ²/2
  have hcos_θ_lb : 1 - θ ^ 2 / 2 ≤ Real.cos θ := Real.one_sub_sq_div_two_le_cos
  -- Lower bound on sin(kθ)/sin(θ)*cos(θ):
  -- Step 1: sin(kθ)*cos(θ)/sin(θ) ≥ k*(1 - k²θ²/4)*(1-θ²/2)
  -- Because: sin(kθ)/sin(θ) ≥ (kθ - (kθ)³/4)/θ = k(1-k²θ²/4) [using sin(kθ)>... and sin(θ)<θ]
  -- and cos(θ) ≥ 1-θ²/2
  have hsin_ratio_lb : (k : ℝ) * (1 - (k : ℝ) ^ 2 * θ ^ 2 / 4) * (1 - θ ^ 2 / 2) ≤
      Real.sin ((k : ℝ) * θ) / Real.sin θ * Real.cos θ := by
    have hstep1_nonneg : 0 ≤ (k : ℝ) * (1 - (k : ℝ) ^ 2 * θ ^ 2 / 4) := by
      nlinarith [sq_nonneg ((k : ℝ) * θ)]
    have hstep1 : (k : ℝ) * (1 - (k : ℝ) ^ 2 * θ ^ 2 / 4) ≤
        Real.sin ((k : ℝ) * θ) / Real.sin θ := by
      rw [le_div_iff₀ hsinθ_pos]
      calc (k : ℝ) * (1 - (k : ℝ) ^ 2 * θ ^ 2 / 4) * Real.sin θ
          ≤ (k : ℝ) * (1 - (k : ℝ) ^ 2 * θ ^ 2 / 4) * θ := by
            apply mul_le_mul_of_nonneg_left hsin_ub.le hstep1_nonneg
        _ = (k : ℝ) * θ - ((k : ℝ) * θ) ^ 3 / 4 := by ring
        _ ≤ Real.sin ((k : ℝ) * θ) := hsin_lb.le
    have hsin_div_nonneg : 0 ≤ Real.sin ((k : ℝ) * θ) / Real.sin θ := by
      apply div_nonneg
      · exact Real.sin_nonneg_of_nonneg_of_le_pi hkθ_pos.le (by linarith [two_le_pi])
      · exact hsinθ_pos.le
    have hcos_θ_lb_nonneg : 0 ≤ 1 - θ ^ 2 / 2 := by nlinarith [sq_nonneg θ]
    calc (k : ℝ) * (1 - (k : ℝ) ^ 2 * θ ^ 2 / 4) * (1 - θ ^ 2 / 2)
        ≤ Real.sin ((k : ℝ) * θ) / Real.sin θ * (1 - θ ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_right hstep1 hcos_θ_lb_nonneg
      _ ≤ Real.sin ((k : ℝ) * θ) / Real.sin θ * Real.cos θ := by
          apply mul_le_mul_of_nonneg_left hcos_θ_lb hsin_div_nonneg
  -- Now the main bound. We need E ≥ N*(1 - k²θ²), where
  -- E = (N-k)*cos(kθ) + sin(kθ)/sin(θ)*cos(θ)
  -- Lower bound: E ≥ (N-k)*(1-(kθ)²/2) + k*(1-k²θ²/4)*(1-θ²/2)
  rw [hcoeff_eq]
  rw [show 1 - 1 / N * ((N - (k : ℝ)) * Real.cos ((k : ℝ) * θ) +
      Real.sin ((k : ℝ) * θ) / Real.sin θ * Real.cos θ) =
    (N - ((N - (k : ℝ)) * Real.cos ((k : ℝ) * θ) +
      Real.sin ((k : ℝ) * θ) / Real.sin θ * Real.cos θ)) / N by
      field_simp]
  rw [div_le_iff₀ hN_pos]
  -- Goal: N - E ≤ N * (kθ)²
  -- Use: E ≥ LB where LB = (N-k)*(1-(kθ)²/2) + k*(1-k²θ²/4)*(1-θ²/2)
  -- So N - E ≤ N - LB. Need N - LB ≤ N*(kθ)².
  -- N - LB = N - (N-k)(1-(kθ)²/2) - k(1-k²θ²/4)(1-θ²/2)
  --        = N - (N-k) + (N-k)(kθ)²/2 - k + k·k²θ²/4 + kθ²/2 - k·k²θ²·θ²/8
  --        = k + (N-k)k²θ²/2 - k + k³θ²/4 + kθ²/2 - k³θ⁴/8
  --        = (N-k)k²θ²/2 + k³θ²/4 + kθ²/2 - k³θ⁴/8
  -- And N*(kθ)² = Nk²θ².
  -- Need: (N-k)k²θ²/2 + k³θ²/4 + kθ²/2 - k³θ⁴/8 ≤ Nk²θ²
  -- i.e., Nk²θ² - (N-k)k²θ²/2 - k³θ²/4 - kθ²/2 + k³θ⁴/8 ≥ 0
  -- Factor out θ²/8: θ²/8 · (8Nk² - 4(N-k)k² - 2k³ - 4k + k³θ²)
  --                = θ²/8 · (8Nk² - 4Nk² + 4k³ - 2k³ - 4k + k³θ²)
  --                = θ²/8 · (4Nk² + 2k³ - 4k + k³θ²)
  --                = θ²k/8 · (4Nk + 2k² - 4 + k²θ²)
  -- Since k ≥ 1, N ≥ 2: 4Nk ≥ 8 > 4, rest nonneg. So positive.
  -- We need: N - E ≤ N*(kθ)² where E = (N-k)*cos(kθ) + sin(kθ)/sin(θ)*cos(θ)
  -- Using E ≥ (N-k)*(1-(kθ)²/2) + k*(1-k²θ²/4)*(1-θ²/2), it suffices to show:
  -- N - [(N-k)*(1-(kθ)²/2) + k*(1-k²θ²/4)*(1-θ²/2)] ≤ N*(kθ)²
  -- After algebra, this reduces to: θ²k(4Nk + 2k² - 4 + k²θ²)/8 ≥ 0
  -- which holds since k ≥ 1, N ≥ 2.
  --
  -- Step 1: Lower bound E ≥ LB
  have hE_lb : (N - (k : ℝ)) * (1 - ((k : ℝ) * θ) ^ 2 / 2) +
      (k : ℝ) * (1 - (k : ℝ) ^ 2 * θ ^ 2 / 4) * (1 - θ ^ 2 / 2) ≤
    (N - (k : ℝ)) * Real.cos ((k : ℝ) * θ) +
      Real.sin ((k : ℝ) * θ) / Real.sin θ * Real.cos θ := by
    have h1 : (N - (k : ℝ)) * (1 - ((k : ℝ) * θ) ^ 2 / 2) ≤
        (N - (k : ℝ)) * Real.cos ((k : ℝ) * θ) :=
      mul_le_mul_of_nonneg_left hcos_lb hNk_nonneg
    linarith [hsin_ratio_lb]
  -- Step 2: Algebraic bound: N - LB ≤ N*(kθ)²
  have hN_ge : (2 : ℝ) ≤ N := by simp [N]
  have hk_ge : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk_ge_1
  nlinarith [sq_nonneg θ, sq_nonneg ((k : ℝ) * θ), sq_nonneg ((k : ℝ) * θ ^ 2),
             hE_lb, hNk_nonneg, mul_nonneg hk_pos.le (sq_nonneg θ)]

/-- Multivariate coefficients are positive -/
theorem jacksonCoeffMulti_pos {n : ℕ} {κ : Fin n → ℕ} {r : ℕ}
    (hκ : ∀ i, κ i ≤ r) :
    0 < jacksonCoeffMulti κ r := by
  unfold jacksonCoeffMulti
  exact Finset.prod_pos (fun i _ => jackson_coeff_pos (hκ i))


/-! ## Jackson kernel polynomial and quadrature reproducing identities -/

/-- Jackson kernel as a polynomial in x, for fixed y -/
noncomputable def jacksonKernelPoly (r : ℕ) (y : ℝ) : Polynomial ℝ :=
  Polynomial.C 1 + Polynomial.C 2 * ∑ k ∈ Finset.range r,
    Polynomial.C (jacksonCoeff (k+1) r * (chebyshevT (k+1)).eval y) * chebyshevT (k+1)

theorem jacksonKernelPoly_eval (r : ℕ) (x y : ℝ) :
    (jacksonKernelPoly r y).eval x = jacksonKernelUni r x y := by
  unfold jacksonKernelPoly jacksonKernelUni
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_finset_sum]
  congr 1; congr 1
  apply Finset.sum_congr rfl
  intro k _; ring

theorem jacksonKernelPoly_nonneg (r : ℕ) (y : ℝ) (hy : y ∈ Set.Icc (-1 : ℝ) 1)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ (jacksonKernelPoly r y).eval x := by
  rw [jacksonKernelPoly_eval]
  exact jackson_nonneg r x y hx hy

/-- The Jackson kernel polynomial has degree ≤ r -/
theorem jacksonKernelPoly_natDegree_le (r : ℕ) (y : ℝ) :
    (jacksonKernelPoly r y).natDegree ≤ r := by
  unfold jacksonKernelPoly
  set p := Polynomial.C 1 + Polynomial.C 2 *
    ∑ k ∈ Finset.range r,
      Polynomial.C (jacksonCoeff (k + 1) r *
        (chebyshevT (k + 1)).eval y) *
      chebyshevT (k + 1) with hp_def
  -- Show p ∈ degreeLT ℝ (r+1), then convert to natDegree ≤ r
  suffices hmem : p ∈ Polynomial.degreeLT ℝ (r + 1) by
    rw [Polynomial.mem_degreeLT] at hmem
    by_cases hp0 : p = 0
    · simp [hp0]
    · rw [Polynomial.degree_eq_natDegree hp0] at hmem
      exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp hmem)
  apply (Polynomial.degreeLT ℝ (r + 1)).add_mem
  · exact Polynomial.mem_degreeLT.mpr
      (lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.succ_pos r))
  · rw [show Polynomial.C (2 : ℝ) * _ = (2 : ℝ) • _ from
      Polynomial.C_mul' _ _]
    apply (Polynomial.degreeLT ℝ (r + 1)).smul_mem
    apply (Polynomial.degreeLT ℝ (r + 1)).sum_mem
    intro k hk
    rw [show Polynomial.C _ * chebyshevT (k + 1) = _ • chebyshevT (k + 1) from
      Polynomial.C_mul' _ _]
    apply (Polynomial.degreeLT ℝ (r + 1)).smul_mem
    exact chebyshevT_mem_degreeLT (k + 1) r
      (by rw [Finset.mem_range] at hk; omega)

/-- The Jackson kernel polynomial for y ∈ [-1,1] belongs to BoxUniPreordering (r+1).
    This follows from Markov-Lukacz: it has degree ≤ r and is nonneg on [-1,1]. -/
theorem jacksonKernelPoly_in_BoxUniPreordering (r : ℕ) (y : ℝ) (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    jacksonKernelPoly r y ∈ BoxUniPreordering (r + 1) :=
  markov_lukacz _ (jacksonKernelPoly_natDegree_le r y)
    (fun x hx => jacksonKernelPoly_nonneg r y hy x hx)


/-! ## Quadrature representation helper lemmas -/

/-- The normalized Jackson coefficient: for k = 0 it is 1, for k ≥ 1 it is 2·λ_k.
    This arises when expanding the Jackson kernel as ∑_{k=0}^r a_k T_k(x)T_k(y). -/
noncomputable def jacksonNormCoeff (k r : ℕ) : ℝ :=
  if k = 0 then 1 else 2 * jacksonCoeff k r

/-- The Jackson kernel evaluated at (x,y) equals ∑_{k=0}^{r} a_k T_k(x) T_k(y)
    where a_0 = 1 and a_k = 2λ_k for k ≥ 1. -/
theorem jacksonKernelUni_chebyshev_sum (r : ℕ) (x y : ℝ) :
    jacksonKernelUni r x y =
    ∑ k ∈ Finset.range (r + 1),
      jacksonNormCoeff k r * (chebyshevT k).eval x * (chebyshevT k).eval y := by
  unfold jacksonKernelUni
  -- RHS: split off k=0 term
  rw [Finset.sum_range_succ']
  simp only [jacksonNormCoeff, chebyshevT_zero, Polynomial.eval_one, ite_true, mul_one]
  -- Simplify remaining sum: (if k+1=0 then 1 else 2λ_{k+1}) = 2λ_{k+1}
  have hsimpl : ∀ k ∈ Finset.range r,
      (if k + 1 = 0 then (1 : ℝ) else 2 * jacksonCoeff (k + 1) r) *
      (chebyshevT (k + 1)).eval x * (chebyshevT (k + 1)).eval y =
      2 * (jacksonCoeff (k + 1) r * (chebyshevT (k + 1)).eval x * (chebyshevT (k + 1)).eval y) :=
    fun k _ => by simp; ring
  rw [Finset.sum_congr rfl hsimpl, ← Finset.mul_sum]; ring

/-- For each coordinate i, applying discrete orthogonality and collapsing the k-sum:
    ∑_{k=0}^r a_k · T_k(x) · [(1/(r+2)) ∑_j T_k(y_j) · T_μ(y_j)] = λ_μ · T_μ(x).
    This is proved by applying discrete_chebyshev_orthogonality and noting only k = μ survives. -/
private theorem jackson_reproducing_1d (r μ : ℕ) (hμ : μ ≤ r) (x : ℝ) :
    ∑ k ∈ Finset.range (r + 1),
      jacksonNormCoeff k r * (chebyshevT k).eval x *
      ((1 / (r + 2 : ℝ)) * ∑ j ∈ Finset.range (r + 2),
        (chebyshevT k).eval (chebyNode r j) * (chebyshevT μ).eval (chebyNode r j)) =
    jacksonCoeff μ r * (chebyshevT μ).eval x := by
  -- Rewrite each inner sum using discrete orthogonality
  have hortho : ∀ k, k ≤ r →
      (1 / (r + 2 : ℝ)) * ∑ j ∈ Finset.range (r + 2),
        (chebyshevT k).eval (chebyNode r j) * (chebyshevT μ).eval (chebyNode r j) =
      if k ≠ μ then 0 else if k = 0 then 1 else 1 / 2 :=
    fun k hk => discrete_chebyshev_orthogonality r k μ hk hμ
  -- Only k = μ survives in the sum
  rw [Finset.sum_eq_single μ]
  · -- The μ-term: a_μ * T_μ(x) * ortho(μ,μ)
    rw [hortho μ hμ, if_neg (not_not.mpr rfl)]
    unfold jacksonNormCoeff
    by_cases hμ0 : μ = 0
    · simp [hμ0, jacksonCoeff]
    · simp [hμ0]; ring
  · -- For k ≠ μ: ortho(k,μ) = 0
    intro k hk hkμ
    have hk_le : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [hortho k hk_le, if_pos hkμ, mul_zero]
  · -- μ ∉ range(r+1) is impossible
    intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The multivariate reproducing property: for μ with μ_i ≤ r for all i,
    ∑_κ (∏_i a_{κ_i} T_{κ_i}(x_i)) · ∏_i [(1/(r+2)) ∑_j T_{κ_i}(y_j) T_{μ_i}(y_j)]
    = (∏_i λ_{μ_i}) · ∏_i T_{μ_i}(x_i) = λ_μ · T_μ(x).
    Proved by factoring as a product of 1D sums, each given by jackson_reproducing_1d. -/
private theorem jackson_reproducing_multi {n : ℕ} (r : ℕ) (μ : Fin n → ℕ)
    (hμ : ∀ i, μ i ≤ r) (x : Fin n → ℝ) :
    ∑ κ ∈ Fintype.piFinset (fun _ : Fin n => Finset.range (r + 1)),
      (∏ i, jacksonNormCoeff (κ i) r * (chebyshevT (κ i)).eval (x i)) *
      (∏ i, ((1 / (r + 2 : ℝ)) * ∑ j ∈ Finset.range (r + 2),
        (chebyshevT (κ i)).eval (chebyNode r j) *
        (chebyshevT (μ i)).eval (chebyNode r j))) =
    jacksonCoeffMulti μ r * ∏ i, (chebyshevT (μ i)).eval (x i) := by
  -- Factor the product ∏_i (a * T) * ∏_i (ortho) = ∏_i (a * T * ortho)
  simp_rw [← Finset.prod_mul_distrib]
  -- Define the helper function g so that ∏ i, g i (κ i) is the body of the sum
  -- and sum_prod_piFinset can be applied
  -- Go the other way: rewrite RHS to match LHS
  -- RHS: λ_μ * ∏ T_μ(x) = ∏_i (λ_{μ_i} * T_{μ_i}(x_i))
  --     = ∏_i (jackson_reproducing_1d) = ∏_i ∑_k ...
  --     = ∑_{piFinset} ∏_i ... (by prod_univ_sum)
  symm
  unfold jacksonCoeffMulti
  rw [← Finset.prod_mul_distrib]
  simp_rw [← jackson_reproducing_1d r _ (hμ _)]
  exact Finset.prod_univ_sum _ _

/-- The core quadrature-kernel identity at the evaluation level.
    ∑_j (1/(r+2))^n · p(y_j) · ∏_i K^ja(x_i, y_{j_i})
    = ∑_{κ ∈ MI} λ_κ · c_κ · ∏_i T_{κ_i}(x_i)

    Strategy: expand p and K^ja in Chebyshev bases, factor products of sums,
    swap sum order, factor j-sum as product of 1D sums, apply discrete orthogonality
    via jackson_reproducing_multi. -/
theorem quadrature_eval_eq_kernel_eval (n r : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (_hp : p.totalDegree ≤ r) (x : Fin n → ℝ) :
    ∑ j ∈ quadratureNodes n r,
      (1 / (r + 2 : ℝ)) ^ n *
      (∑ μ ∈ multiIndices n r,
        chebyCoeff n r p μ * ∏ i, (chebyshevT (μ i)).eval (chebyNode r (j i))) *
      (∏ i, ∑ k ∈ Finset.range (r + 1),
        jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
        (chebyshevT k).eval (chebyNode r (j i))) =
    ∑ κ ∈ multiIndices n r,
      jacksonCoeffMulti κ r * chebyCoeff n r p κ *
      ∏ i, (chebyshevT (κ i)).eval (x i) := by
  -- Abbreviations
  set w := (1 / (r + 2 : ℝ)) with hw
  -- Step 1: Transform each j-summand by factoring ∏_i ∑_k as ∑_κ ∏_i,
  -- distributing products, and rearranging.
  -- After: ∑_j ∑_μ ∑_κ c_μ · ∏_i(a_{κ_i} T_{κ_i}(x_i) T_{κ_i}(y_{j_i})) · w^n ·
  -- ∏_i T_{μ_i}(y_{j_i})
  -- Then swap sums to μ, κ, j and pull c_μ out of κ,j-sum.
  -- Then factor the j-sum as a product, apply jackson_reproducing_multi.

  -- Direct approach: transform the whole expression in one go
  -- Pull the sum apart step by step using have statements
  -- so Lean can check each step.

  -- First, expand the product of sums using prod_univ_sum
  -- and rearrange the triple sum.
  -- Key fact: ∑_{j ∈ QN} ∏_i f_i(j_i) = ∏_i ∑_{k} f_i(k)
  -- (this is Finset.prod_univ_sum for piFinset)

  -- Main computation: transform LHS to ∑_μ c_μ · (jackson_reproducing_multi result)
  -- = ∑_μ c_μ · λ_μ · ∏ T_{μ_i}(x_i)
  -- = RHS

  -- Step A: Show LHS = ∑_μ c_μ · F(μ) where F(μ) is defined below
  -- F(μ) = ∑_j w^n · (∏_i T_{μ_i}(y_{j_i})) · ∏_i (∑_k a_k T_k(x_i) T_k(y_{j_i}))
  -- Note: ∏_i (∑_k a_k T_k(x_i) T_k(y_{j_i})) = jacksonKernelUni r x_i y_{j_i}
  -- evaluated at each coordinate

  -- Step B: Show F(μ) = λ_μ · ∏_i T_{μ_i}(x_i) using jackson_reproducing_multi.
  -- This requires: factor ∏_i(∑_k) = ∑_κ ∏_i, swap with j-sum, factor j-sum as ∏_i(∑_j).

  -- Let's define the intermediate expression
  -- LHS = ∑_j w^n · (∑_μ c_μ ∏ T_μ(y_j)) · K(x,y_j)
  -- = ∑_μ c_μ · ∑_j w^n · (∏ T_μ(y_j)) · K(x,y_j)   (by distributing and swapping)
  -- where K(x,y_j) = ∏_i K^ja_1d(x_i, y_{j_i})

  -- Step 1: Distribute the μ-sum and swap with j-sum
  calc ∑ j ∈ quadratureNodes n r,
      w ^ n *
      (∑ μ ∈ multiIndices n r,
        chebyCoeff n r p μ * ∏ i, (chebyshevT (μ i)).eval (chebyNode r (j i))) *
      (∏ i, ∑ k ∈ Finset.range (r + 1),
        jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
        (chebyshevT k).eval (chebyNode r (j i)))
  -- = ∑_j ∑_μ c_μ · w^n · (∏ T_{μ_i}(y_j)) · ∏_i(∑_k ...)
    _ = ∑ j ∈ quadratureNodes n r, ∑ μ ∈ multiIndices n r,
        chebyCoeff n r p μ * (w ^ n *
        (∏ i, (chebyshevT (μ i)).eval (chebyNode r (j i))) *
        (∏ i, ∑ k ∈ Finset.range (r + 1),
          jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
          (chebyshevT k).eval (chebyNode r (j i)))) := by
      apply Finset.sum_congr rfl; intro j _
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro μ _; ring
  -- = ∑_μ ∑_j ... (swap)
    _ = ∑ μ ∈ multiIndices n r, ∑ j ∈ quadratureNodes n r,
        chebyCoeff n r p μ * (w ^ n *
        (∏ i, (chebyshevT (μ i)).eval (chebyNode r (j i))) *
        (∏ i, ∑ k ∈ Finset.range (r + 1),
          jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
          (chebyshevT k).eval (chebyNode r (j i)))) := by
      rw [Finset.sum_comm]
  -- = ∑_μ c_μ · ∑_j w^n · (∏ T_μ(y_j)) · ∏(∑ ...)
    _ = ∑ μ ∈ multiIndices n r,
        chebyCoeff n r p μ * ∑ j ∈ quadratureNodes n r,
        w ^ n *
        (∏ i, (chebyshevT (μ i)).eval (chebyNode r (j i))) *
        (∏ i, ∑ k ∈ Finset.range (r + 1),
          jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
          (chebyshevT k).eval (chebyNode r (j i))) := by
      apply Finset.sum_congr rfl; intro μ _
      rw [← Finset.mul_sum]
  -- Step 2: For each μ, transform the j-sum.
  -- Factor ∏_i(∑_k) = ∑_κ ∏_i, combine products, factor j-sum as ∏_i(∑_j),
  -- apply jackson_reproducing_multi.
    _ = ∑ μ ∈ multiIndices n r,
        chebyCoeff n r p μ * (jacksonCoeffMulti μ r * ∏ i, (chebyshevT (μ i)).eval (x i)) := by
      apply Finset.sum_congr rfl; intro μ hμ
      congr 1
      have hμ_le : ∀ i, μ i ≤ r := (multiIndices_mem_iff.mp hμ).2
      -- Goal: ∑_j w^n * (∏ T_μ(y_j)) * (∏_i ∑_k a_k T_k(x_i) T_k(y_{j_i}))
      --     = λ_μ * ∏ T_μ(x)
      -- Strategy: use jackson_reproducing_multi (proved via sym + prod_univ_sum)
      -- First combine the two products
      have step1 : ∀ j ∈ quadratureNodes n r,
          w ^ n * (∏ i, (chebyshevT (μ i)).eval (chebyNode r (j i))) *
          (∏ i, ∑ k ∈ Finset.range (r + 1),
            jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
            (chebyshevT k).eval (chebyNode r (j i))) =
          w ^ n * ∏ i, (chebyshevT (μ i)).eval (chebyNode r (j i)) *
            (∑ k ∈ Finset.range (r + 1),
              jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
              (chebyshevT k).eval (chebyNode r (j i))) :=
        fun _ _ => by rw [mul_assoc, ← Finset.prod_mul_distrib]
      rw [Finset.sum_congr rfl step1]
      -- Factor w^n = ∏ w and combine
      have step2 : ∀ j ∈ quadratureNodes n r,
          w ^ n * ∏ i, (chebyshevT (μ i)).eval (chebyNode r (j i)) *
            (∑ k ∈ Finset.range (r + 1),
              jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
              (chebyshevT k).eval (chebyNode r (j i))) =
          ∏ i, w * (chebyshevT (μ i)).eval (chebyNode r (j i)) *
            (∑ k ∈ Finset.range (r + 1),
              jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
              (chebyshevT k).eval (chebyNode r (j i))) :=
        fun _ _ => by
          rw [show w ^ n = ∏ (_ : Fin n), w from by rw [Finset.prod_const, Finset.card_fin],
              ← Finset.prod_mul_distrib]; congr 1; ext i; ring
      rw [Finset.sum_congr rfl step2]
      -- Rearrange: w * T_μ(y) * ∑_k ... = ∑_k a_k T_k(x) * (w * T_k(y) * T_μ(y))
      have step3 : ∀ j ∈ quadratureNodes n r,
          ∏ i, w * (chebyshevT (μ i)).eval (chebyNode r (j i)) *
            (∑ k ∈ Finset.range (r + 1),
              jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
              (chebyshevT k).eval (chebyNode r (j i))) =
          ∏ i, ∑ k ∈ Finset.range (r + 1),
            jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
            (w * (chebyshevT k).eval (chebyNode r (j i)) *
              (chebyshevT (μ i)).eval (chebyNode r (j i))) :=
        fun _ _ => by
          apply Finset.prod_congr rfl; intro i _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      rw [Finset.sum_congr rfl step3]
      -- Factor ∑_j ∏_i f(i, j_i) = ∏_i ∑_{j_i} f(i, j_i)
      -- Use trans to introduce the factored form explicitly
      trans (∏ i : Fin n, ∑ j_i ∈ Finset.range (r + 2),
        ∑ k ∈ Finset.range (r + 1),
          jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
          (w * (chebyshevT k).eval (chebyNode r j_i) *
            (chebyshevT (μ i)).eval (chebyNode r j_i)))
      · -- ∑_j ∏_i f(j_i, i) = ∏_i ∑_{j_i} f(j_i, i)
        unfold quadratureNodes
        exact (Finset.sum_prod_piFinset (κ := ℕ) (Finset.range (r + 2))
          (fun (i : Fin n) (j_i : ℕ) =>
            ∑ k ∈ Finset.range (r + 1),
              jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
              (w * (chebyshevT k).eval (chebyNode r j_i) *
                (chebyshevT (μ i)).eval (chebyNode r j_i))))
      · -- ∏_i ∑_{j_i} ∑_k ... = jacksonCoeffMulti μ r * ∏ T_μ(x)
        -- Show each factor simplifies via jackson_reproducing_1d
        suffices h : ∀ i : Fin n,
            ∑ j_i ∈ Finset.range (r + 2),
              ∑ k ∈ Finset.range (r + 1),
                jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
                (w * (chebyshevT k).eval (chebyNode r j_i) *
                  (chebyshevT (μ i)).eval (chebyNode r j_i)) =
            jacksonCoeff (μ i) r * (chebyshevT (μ i)).eval (x i) by
          simp_rw [h]; unfold jacksonCoeffMulti
          exact Finset.prod_mul_distrib
        intro i; rw [Finset.sum_comm]
        -- Rearrange: a * (w * b * c) = a * (w * (b * c))
        simp_rw [show ∀ (k j_i : ℕ),
            jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
            (w * (chebyshevT k).eval (chebyNode r j_i) *
              (chebyshevT (μ i)).eval (chebyNode r j_i)) =
            jacksonNormCoeff k r * (chebyshevT k).eval (x i) *
            (w * ((chebyshevT k).eval (chebyNode r j_i) *
              (chebyshevT (μ i)).eval (chebyNode r j_i)))
          from fun _ _ => by ring]
        simp_rw [← Finset.mul_sum]
        exact jackson_reproducing_1d r (μ i) (hμ_le i) (x i)
  -- = ∑_μ c_μ · λ_μ · ∏ T_{μ_i}(x_i) = RHS
    _ = ∑ κ ∈ multiIndices n r,
        jacksonCoeffMulti κ r * chebyCoeff n r p κ *
        ∏ i, (chebyshevT (κ i)).eval (x i) := by
      apply Finset.sum_congr rfl; intro κ _; ring

end OptimalConvergenceRates

end
