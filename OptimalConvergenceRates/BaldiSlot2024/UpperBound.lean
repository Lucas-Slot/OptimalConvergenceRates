/-
  OptimalConvergenceRates/BaldiSlot2024/UpperBound.lean

  Baldi-Slot 2024 Putinar upper degree bound on the hypercube.
-/
import OptimalConvergenceRates.BasicNotions.SumsOfSquares
import OptimalConvergenceRates.Chebyshev.ChebyshevGrowth
import OptimalConvergenceRates.BaldiSlot2024.Defs
import OptimalConvergenceRates.BaldiSlot2024.DegreeShift
import OptimalConvergenceRates.BaldiSlot2024.ScaledSchmudgen
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityCorollaries
import OptimalConvergenceRates.SlotLaurent2022.MainResults

open MvPolynomial Finset Real

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## The extended hypercube [-1-ε, 1+ε]^n -/

/-- The extended hypercube [-1-ε, 1+ε]^n.
    This is the set of points within coordinate-wise distance ε of [-1,1]^n. -/
def ExtendedHypercube (ε : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-(1 + ε)) (1 + ε))

theorem ExtendedHypercube_mem_iff (ε : ℝ) (x : Fin n → ℝ) :
    x ∈ ExtendedHypercube ε n ↔ ∀ i, x i ∈ Set.Icc (-(1 + ε)) (1 + ε) := by
  simp only [ExtendedHypercube, Set.mem_pi, Set.mem_univ, true_implies]

theorem ExtendedHypercube_mem_abs (ε : ℝ) (_hε : 0 ≤ ε) (x : Fin n → ℝ) :
    x ∈ ExtendedHypercube ε n ↔ ∀ i, |x i| ≤ 1 + ε := by
  rw [ExtendedHypercube_mem_iff]
  constructor
  · intro h i
    have hi := h i
    exact abs_le.mpr ⟨by linarith [hi.1], hi.2⟩
  · intro h i
    have hi := abs_le.mp (h i)
    exact ⟨by linarith [hi.1], hi.2⟩

theorem Hypercube_subset_ExtendedHypercube (ε : ℝ) (hε : 0 ≤ ε) :
    Hypercube n ⊆ ExtendedHypercube ε n := by
  intro x hx
  rw [ExtendedHypercube_mem_iff]
  intro i
  have hi := (Hypercube_mem_iff x).mp hx i
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

theorem ExtendedHypercube_nonempty (ε : ℝ) (hε : 0 ≤ ε) :
    (ExtendedHypercube ε n).Nonempty :=
  ⟨fun _ => 0, fun _ _ => ⟨by linarith, by linarith⟩⟩

/-! ## Clamping to the hypercube -/

/-- Clamp a real number to [-1, 1]. -/
def clamp (x : ℝ) : ℝ :=
  max (-1) (min x 1)

theorem clamp_mem_Icc (x : ℝ) : clamp x ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold clamp
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

theorem clamp_eq_self {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) : clamp x = x := by
  unfold clamp
  simp [max_eq_right hx1, min_eq_left hx2]

theorem abs_sub_clamp_le (x : ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hx : |x| ≤ 1 + ε) : |x - clamp x| ≤ ε := by
  have hx_bounds := abs_le.mp hx
  unfold clamp
  by_cases h1 : x ≤ 1
  · by_cases h2 : -1 ≤ x
    · -- x ∈ [-1, 1], so clamp x = x
      rw [min_eq_left h1, max_eq_right h2, sub_self, abs_zero]; exact hε
    · -- x < -1, so min x 1 = x (since x < -1 < 1) and max(-1, x) = -1 (since x < -1)
      push Not at h2
      rw [min_eq_left (by linarith : x ≤ 1), max_eq_left (by linarith : x ≤ -1)]
      rw [abs_of_nonpos (by linarith)]
      linarith [hx_bounds.1]
  · -- x > 1, so min x 1 = 1 and max(-1, 1) = 1
    push Not at h1
    rw [min_eq_right (by linarith : 1 ≤ x)]
    rw [show max (-1 : ℝ) 1 = 1 from by norm_num]
    rw [abs_of_nonneg (by linarith)]
    linarith [hx_bounds.2]

/-- Clamp a vector coordinate-wise to [-1,1]^n. -/
def clampVec (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => clamp (x i)

theorem clampVec_mem_Hypercube (x : Fin n → ℝ) : clampVec x ∈ Hypercube n := by
  rw [Hypercube_mem_iff]
  intro i
  exact clamp_mem_Icc (x i)

theorem clampVec_eq_self {x : Fin n → ℝ} (hx : x ∈ Hypercube n) :
    clampVec x = x := by
  ext i
  have hi := (Hypercube_mem_iff x).mp hx i
  exact clamp_eq_self hi.1 hi.2

/-- Each coordinate of z - clampVec z has absolute value ≤ ε,
    provided z ∈ [-1-ε, 1+ε]^n. -/
theorem coord_diff_le_eps (z : Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hz : z ∈ ExtendedHypercube ε n) (i : Fin n) :
    |z i - clampVec z i| ≤ ε := by
  have hi := (ExtendedHypercube_mem_abs ε hε z).mp hz i
  exact abs_sub_clamp_le (z i) ε hε hi

/-! ## Auxiliary lemmas for the proof -/

/-- polyMin is positive when f is strictly positive on the hypercube. -/
theorem polyMin_pos_of_pos (f : MvPolynomial (Fin n) ℝ)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f) :
    0 < polyMin f := by
  obtain ⟨x, hx, heval⟩ := polyMin_mem f
  rw [← heval]; exact hf_pos x hx

/-- polySupNorm is positive when f is strictly positive somewhere. -/
theorem polySupNorm_pos_of_pos (f : MvPolynomial (Fin n) ℝ)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f) :
    0 < polySupNorm f := by
  obtain ⟨x, hx, _⟩ := polyMin_mem f
  have heval_pos := hf_pos x hx
  unfold polySupNorm
  apply lt_of_lt_of_le (abs_pos.mpr (ne_of_gt heval_pos))
  apply le_csSup
  · exact (Hypercube_compact.image
      (continuous_abs.comp (MvPolynomial.continuous_eval f))).bddAbove
  · exact ⟨x, hx, rfl⟩

/-- polyMax f ≤ polySupNorm f. -/
theorem polyMax_le_polySupNorm (f : MvPolynomial (Fin n) ℝ) :
    polyMax f ≤ polySupNorm f := by
  unfold polyMax polySupNorm
  apply csSup_le (Hypercube_image_nonempty f)
  rintro _ ⟨x, hx, rfl⟩
  apply le_csSup_of_le
    (Hypercube_compact.image
      (continuous_abs.comp (MvPolynomial.continuous_eval f))).bddAbove
  · exact ⟨x, hx, rfl⟩
  · exact le_abs_self _

/-- polyMin f ≤ polySupNorm f (follows from |f(x)| ≥ |f_min| at a minimizer). -/
theorem polyMin_le_polySupNorm (f : MvPolynomial (Fin n) ℝ)
    (_hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f) :
    polyMin f ≤ polySupNorm f := by
  calc polyMin f ≤ polyMax f := polyMin_le_polyMax f
    _ ≤ polySupNorm f := polyMax_le_polySupNorm f

/-- The condition number polySupNorm f / polyMin f is ≥ 1 when f > 0 on B^n. -/
theorem condition_number_ge_one (f : MvPolynomial (Fin n) ℝ)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f) :
    1 ≤ polySupNorm f / polyMin f := by
  rw [le_div_iff₀ (polyMin_pos_of_pos f hf_pos)]
  rw [one_mul]
  exact polyMin_le_polySupNorm f hf_pos

/-- The oscillation Δf = f_max - f_min satisfies Δf ≤ 2 · ‖f‖. -/
theorem oscillation_le_two_supnorm (f : MvPolynomial (Fin n) ℝ) :
    polyMax f - polyMin f ≤ 2 * polySupNorm f := by
  have hmax : polyMax f ≤ polySupNorm f := polyMax_le_polySupNorm f
  -- Show -polySupNorm f ≤ polyMin f
  have hmin : -polySupNorm f ≤ polyMin f := by
    unfold polyMin
    apply le_csInf (Hypercube_image_nonempty f)
    rintro _ ⟨x, hx, rfl⟩
    have := polySupNorm_eval_le f (polySupNorm f) (le_refl _) x hx
    linarith [abs_le.mp this]
  linarith

/-! ## Markov-type perturbation bound (from MarkovInequality) -/

/-- **Markov perturbation bound** (used in arXiv v3, Lemma 28):
    For f of degree ≤ d and z ∈ [-1-ε, 1+ε]^n with ẑ = clamp(z) ∈ B^n,
    |f(z) - f(ẑ)| ≤ constCChebyshev · d² · ε · ‖f‖_{B^n}.

    This follows from the multivariate Markov inequality: each coordinate
    deviation is ≤ ε, and the Chebyshev growth bound controls how fast
    a polynomial of degree d can grow outside [-1,1].

    The precise argument uses the mean value theorem coordinate by coordinate
    and the Chebyshev derivative estimate from arXiv v3, Lemma 20. -/
theorem markov_perturbation_bound (f : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hd : f.totalDegree ≤ d)
    (z : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) (hε_le : ε ≤ 1 / (d : ℝ) ^ 2)
    (hz : z ∈ ExtendedHypercube ε n) :
    |MvPolynomial.eval z f - MvPolynomial.eval (clampVec z) f| ≤
      2 * constCChebyshev * d ^ 2 * ε * polySupNorm f := by
  have hzhat : clampVec z ∈ Hypercube n := clampVec_mem_Hypercube z
  have hclose : ∀ i, |z i - clampVec z i| ≤ ε :=
    fun i => coord_diff_le_eps z ε hε.le hz i
  exact markov_perturbation_extended_weak f d hd z (clampVec z) hzhat ε hε hε_le hclose

/-! ## ArXiv v3, Lemma 28: Choice of epsilon -/

/-- The threshold for ε in arXiv v3, Lemma 28:
    ε₀(f, d) = polyMin f / (4 · constCChebyshev · d² · polySupNorm f).
    When ε ≤ ε₀, the polynomial f remains ≥ f_min/2 on [-1-ε, 1+ε]^n. -/
noncomputable def epsilon_threshold (f : MvPolynomial (Fin n) ℝ) (d : ℕ) : ℝ :=
  polyMin f / (4 * constCChebyshev * d ^ 2 * polySupNorm f)

theorem epsilon_threshold_pos (f : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hd : 1 ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f) :
    0 < epsilon_threshold f d := by
  unfold epsilon_threshold
  apply div_pos (polyMin_pos_of_pos f hf_pos)
  apply mul_pos
  · apply mul_pos
    · apply mul_pos
      · linarith
      · exact constCChebyshev_pos
    · positivity
  · exact polySupNorm_pos_of_pos f hf_pos

/-- **ArXiv v3, Lemma 28** (choice of ε):
    If f > 0 on B^n and ε ≤ f_min/(4𝔠d²‖f‖), then
    f(z) ≥ f_min/2 for all z ∈ [-1-ε, 1+ε]^n. -/
theorem choice_of_epsilon (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (ε : ℝ)
    (hd : 1 ≤ d)
    (hd' : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hε_pos : 0 < ε)
    (hε_bound : ε ≤ polyMin f / (4 * constCChebyshev * d ^ 2 * polySupNorm f)) :
    ∀ z ∈ ExtendedHypercube ε n, polyMin f / 2 ≤ MvPolynomial.eval z f := by
  intro z hz
  -- Let zhat = clampVec z in B^n
  have hzhat : clampVec z ∈ Hypercube n := clampVec_mem_Hypercube z
  -- f(zhat) >= polyMin f
  have hfzhat : polyMin f ≤ MvPolynomial.eval (clampVec z) f :=
    polyMin_le_eval f (clampVec z) hzhat
  -- |f(z) - f(ẑ)| ≤ c · d² · ε · ‖f‖
  have hmin_pos := polyMin_pos_of_pos f hf_pos
  have hsup_pos := polySupNorm_pos_of_pos f hf_pos
  have hc_pos := constCChebyshev_pos
  have hd_pos : (0 : ℝ) < d ^ 2 := by positivity
  have hε_le : ε ≤ 1 / (d : ℝ) ^ 2 := by
    calc ε ≤ polyMin f / (4 * constCChebyshev * d ^ 2 * polySupNorm f) := hε_bound
      _ ≤ polySupNorm f / (4 * constCChebyshev * d ^ 2 * polySupNorm f) := by
          apply div_le_div_of_nonneg_right (polyMin_le_polySupNorm f hf_pos) (by positivity)
      _ = 1 / (4 * constCChebyshev * (d : ℝ) ^ 2) := by field_simp
      _ ≤ 1 / (d : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact le_mul_of_one_le_left (by positivity) (by nlinarith [one_le_constCChebyshev])
  have hperturb := markov_perturbation_bound f d hd' z ε hε_pos hε_le hz
  -- 2c · d² · ε · ‖f‖ ≤ 2c · d² · (f_min/(4cd²‖f‖)) · ‖f‖ = f_min/2
  have hbound : 2 * constCChebyshev * d ^ 2 * ε * polySupNorm f ≤ polyMin f / 2 := by
    have hcd_pos : (0 : ℝ) < 2 * constCChebyshev * (d : ℝ) ^ 2 := by positivity
    calc 2 * constCChebyshev * (d : ℝ) ^ 2 * ε * polySupNorm f
        ≤ 2 * constCChebyshev * (d : ℝ) ^ 2 *
          (polyMin f / (4 * constCChebyshev * (d : ℝ) ^ 2 * polySupNorm f)) *
          polySupNorm f := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hε_bound (le_of_lt hcd_pos)
          · exact le_of_lt hsup_pos
      _ = polyMin f / 2 := by
          have hne1 : constCChebyshev ≠ 0 := ne_of_gt hc_pos
          have hne2 : (d : ℝ) ^ 2 ≠ 0 := ne_of_gt hd_pos
          have hne3 : polySupNorm f ≠ 0 := ne_of_gt hsup_pos
          field_simp; ring
  -- |f(z) - f(zhat)| ≤ polyMin f / 2
  have hperturb_bound : |MvPolynomial.eval z f - MvPolynomial.eval (clampVec z) f| ≤
      polyMin f / 2 := le_trans hperturb hbound
  -- Extract: -(polyMin f / 2) ≤ f(z) - f(zhat)
  have hab := (abs_le.mp hperturb_bound).1
  linarith

/-- Variant of arXiv v3, Lemma 28 with a strict positivity conclusion. -/
theorem choice_of_epsilon_pos (f : MvPolynomial (Fin n) ℝ) (d : ℕ) (ε : ℝ)
    (hd : 1 ≤ d)
    (hd' : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hε_pos : 0 < ε)
    (hε_bound : ε ≤ polyMin f / (4 * constCChebyshev * d ^ 2 * polySupNorm f)) :
    ∀ z ∈ ExtendedHypercube ε n, 0 < MvPolynomial.eval z f := by
  intro z hz
  have hmin_pos : 0 < polyMin f := by
    obtain ⟨x, hx, heval⟩ := polyMin_mem f
    rw [← heval]; exact hf_pos x hx
  linarith [choice_of_epsilon f d ε hd hd' hf_pos hε_pos hε_bound z hz]

/-! ## Relating η = n^{1/(2q)} to ε -/

/-- For q chosen appropriately, η = n^{1/(2q)} satisfies η ≤ 1 + ε,
    so [-η,η]^n ⊆ [-1-ε, 1+ε]^n. -/
theorem ScaledHypercube_subset_ExtendedHypercube (η ε : ℝ) (_hη : 0 ≤ η)
    (hηε : η ≤ 1 + ε) :
    ScaledHypercube η n ⊆ ExtendedHypercube ε n := by
  intro x hx
  rw [ExtendedHypercube_mem_iff]
  intro i
  have hi := (ScaledHypercube_mem_iff η x).mp hx i
  exact ⟨by linarith [hi.1], by linarith [hi.2]⟩

/-! ## Choosing q from ε -/

/-- The choice of q given ε > 0 and n ≥ 2:
    q = ⌈log(n) / (2 · log(1 + ε))⌉.
    This ensures η = n^{1/(2q)} ≤ (1+ε), i.e. the scaled hypercube
    fits inside the extended hypercube. -/
noncomputable def choose_q (n : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil (Real.log n / (2 * Real.log (1 + ε)))

/-- choose_q is always >= 1 when n >= 2 and eps > 0. -/
theorem one_le_choose_q (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    1 ≤ choose_q n ε := by
  unfold choose_q
  rw [Nat.one_le_ceil_iff]
  apply div_pos
  · exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  · exact mul_pos (by norm_num : (0 : ℝ) < 2) (Real.log_pos (by linarith))

/-- When q = choose_q n ε, we have η = n^{1/(2q)} ≤ 1 + ε. -/
theorem eta_le_one_add_eps (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    eta n (choose_q n ε) ≤ 1 + ε := by
  unfold eta
  set q := choose_q n ε
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1ε_pos : (0 : ℝ) < 1 + ε := by linarith
  have hlog1ε : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have hq_ge : 1 ≤ q := one_le_choose_q hn ε hε
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hq_ge
  -- n^(1/(2q)) ≤ 1+ε ↔ (1/(2q)) · log(n) ≤ log(1+ε)
  -- Use log monotonicity
  rw [show (↑n : ℝ).rpow (1 / (2 * ↑q)) =
      (↑n : ℝ) ^ ((1 : ℝ) / (2 * (↑q : ℝ))) from rfl]
  rw [Real.rpow_le_iff_le_log hn_pos h1ε_pos]
  -- Goal: 1 / (2 * q) * Real.log n ≤ Real.log (1 + ε)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ↑q)]
  -- Goal: Real.log n ≤ Real.log (1 + ε) * (2 * q)
  rw [mul_comm]
  -- Goal: Real.log n ≤ 2 * q * Real.log (1 + ε)
  have hceil := Nat.le_ceil (Real.log ↑n / (2 * Real.log (1 + ε)))
  calc Real.log ↑n
      = Real.log ↑n / (2 * Real.log (1 + ε)) * (2 * Real.log (1 + ε)) := by
        field_simp
    _ ≤ ↑q * (2 * Real.log (1 + ε)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hceil
        · positivity
    _ = 2 * ↑q * Real.log (1 + ε) := by ring

/-- Upper bound on choose_q: q ≤ ⌈log(n)/(2·log(1+ε))⌉ + 1. -/
theorem choose_q_le (n : ℕ) (ε : ℝ) (_hε : 0 < ε) :
    choose_q n ε ≤ Nat.ceil (Real.log n / (2 * Real.log (1 + ε))) + 1 := by
  unfold choose_q; omega

/-- For ε ≤ 1, we have log(1+ε) ≥ ε/2, so 1/log(1+ε) ≤ 2/ε. -/
theorem inv_log_one_add_le (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 / Real.log (1 + ε) ≤ 2 / ε := by
  -- Suffices to show ε/2 ≤ log(1+ε)
  -- Then 1/log(1+ε) ≤ 1/(ε/2) = 2/ε
  have h1ε : 0 < 1 + ε := by linarith
  have hlog_pos : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  -- From one_sub_inv_le_log_of_pos with x = 1+ε: 1 - 1/(1+ε) ≤ log(1+ε)
  have hlog_bound := Real.one_sub_inv_le_log_of_pos h1ε
  -- 1 - (1+ε)⁻¹ = ε/(1+ε)
  have heq : 1 - (1 + ε)⁻¹ = ε / (1 + ε) := by field_simp; ring
  rw [heq] at hlog_bound
  -- ε/(1+ε) ≥ ε/2 when 1+ε ≤ 2
  have heps_half : ε / 2 ≤ ε / (1 + ε) :=
    div_le_div_of_nonneg_left hε.le h1ε (by linarith)
  -- So ε/2 ≤ log(1+ε)
  have heps_le_log : ε / 2 ≤ Real.log (1 + ε) := le_trans heps_half hlog_bound
  -- Therefore 1/log(1+ε) ≤ 2/ε
  rw [div_le_div_iff₀ hlog_pos hε]
  linarith

/-- Bound on q in terms of d, n, and the polynomial data.
    When ε = polyMin f / (4 · c · d² · ‖f‖), we get
    q ≤ C' · d² · ‖f‖ · log(n) / polyMin f
    for some absolute constant C'. -/
theorem choose_q_bound (f : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hn : 2 ≤ n)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f) :
    (choose_q n (epsilon_threshold f d) : ℝ) ≤
      4 * constCChebyshev * d ^ 2 * polySupNorm f / polyMin f *
        Real.log n + 1 := by
  set ε := epsilon_threshold f d with hε_def
  have hε_pos := epsilon_threshold_pos f d hd hf_pos
  have hmin_pos := polyMin_pos_of_pos f hf_pos
  have hsup_pos := polySupNorm_pos_of_pos f hf_pos
  have hc_pos := constCChebyshev_pos
  have hd_pos : (0 : ℝ) < d ^ 2 := by positivity
  -- choose_q = ⌈log n / (2 · log(1+ε))⌉ ≤ log n / (2 · log(1+ε)) + 1
  have hceil_bound : (choose_q n ε : ℝ) ≤ Real.log n / (2 * Real.log (1 + ε)) + 1 := by
    have hlog1ε : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
    calc (choose_q n ε : ℝ)
        = (Nat.ceil (Real.log n / (2 * Real.log (1 + ε))) : ℝ) := by rfl
      _ ≤ Real.log n / (2 * Real.log (1 + ε)) + 1 :=
            le_of_lt (Nat.ceil_lt_add_one (by positivity))
  -- ε ≤ 1 (since ε = polyMin f / (4·c·d²·polySupNorm f)
  --   ≤ polySupNorm f / (4·c·d²·polySupNorm f) = 1/(4cd²) ≤ 1)
  have hε_le_one : ε ≤ 1 := by
    simp only [hε_def]; unfold epsilon_threshold
    calc polyMin f / (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f)
        ≤ polySupNorm f / (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f) := by
          apply div_le_div_of_nonneg_right (polyMin_le_polySupNorm f hf_pos)
          positivity
      _ = 1 / (4 * constCChebyshev * ↑d ^ 2) := by
          field_simp
      _ ≤ 1 := by
          rw [div_le_one (by positivity)]
          have hd_cast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
          have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
          nlinarith [one_le_constCChebyshev]
  -- 1/log(1+ε) ≤ 2/ε
  have hinv_log := inv_log_one_add_le ε hε_pos hε_le_one
  -- log n / (2 · log(1+ε)) = (log n / 2) · (1 / log(1+ε))
  --                         ≤ (log n / 2) · (2/ε) = log n / ε
  -- log n / (2 · log(1+ε)) ≤ log n · (1/log(1+ε)) / 2 ≤ log n · (2/ε) / 2 = log n / ε
  have hlog_n_nonneg : (0 : ℝ) ≤ Real.log n := by
    exact le_of_lt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  have hstep : Real.log ↑n / (2 * Real.log (1 + ε)) ≤
      Real.log ↑n * (1 / ε) := by
    calc Real.log ↑n / (2 * Real.log (1 + ε))
        = Real.log ↑n * (1 / (2 * Real.log (1 + ε))) := by ring
      _ = Real.log ↑n * (1 / Real.log (1 + ε) / 2) := by ring
      _ ≤ Real.log ↑n * (2 / ε / 2) := by
          apply mul_le_mul_of_nonneg_left _ hlog_n_nonneg
          apply div_le_div_of_nonneg_right hinv_log
          norm_num
      _ = Real.log ↑n * (1 / ε) := by ring
  have hfinal : Real.log ↑n * (1 / ε) =
      4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f * Real.log ↑n := by
    simp only [hε_def]; unfold epsilon_threshold
    rw [one_div, inv_div]; ring
  linarith

/-- Lower bound on constC: since the multiIndices set contains 0 (with card ≥ 1)
    and 2^{w(0)/2} = 1, we get constC n d ≥ 2nπ²d². -/
theorem constC_lower_bound (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    2 * ↑n * Real.pi ^ 2 * ↑d ^ 2 ≤ constC n d := by
  unfold constC
  have hne : (multiIndices n d).Nonempty :=
    ⟨0, multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩⟩
  -- card ≥ 1
  have hcard : (1 : ℝ) ≤ ((multiIndices n d).card : ℝ) :=
    Nat.one_le_cast.mpr (Finset.card_pos.mpr hne)
  -- sup' ≥ 2^{w(0)/2} = 2^0 = 1
  have hsup : (1 : ℝ) ≤ Finset.sup' (multiIndices n d) hne
      (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) := by
    have h0_mem : (0 : Fin n → ℕ) ∈ multiIndices n d :=
      multiIndices_mem_iff.mpr ⟨by simp [multiDegree], fun _ => Nat.zero_le _⟩
    have h0_val : (2 : ℝ) ^ ((hammingWeight (0 : Fin n → ℕ) : ℝ) / 2) = 1 := by
      have hw_zero : hammingWeight (0 : Fin n → ℕ) = 0 := @hammingWeight_zero n
      rw [hw_zero]
      norm_num
    rw [← h0_val]
    exact Finset.le_sup' (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) h0_mem
  calc 2 * ↑n * Real.pi ^ 2 * ↑d ^ 2
      = 1 * 1 * (2 * ↑n * Real.pi ^ 2 * ↑d ^ 2) := by ring
    _ ≤ ↑(multiIndices n d).card *
        Finset.sup' (multiIndices n d) hne
          (fun κ => (2 : ℝ) ^ ((hammingWeight κ : ℝ) / 2)) *
        (2 * ↑n * Real.pi ^ 2 * ↑d ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul hcard hsup (by positivity) (by positivity)
        · positivity

/-! ## The overall constant for arXiv v3, Theorem 3 -/

/-! ## Assembly of the qualitative upper bound (arXiv v3, Theorem 3) -/

/-- Step 1: Choose ε via arXiv v3, Lemma 28 and obtain positivity on the enlarged box. -/
private theorem step1_positivity_extension (f : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hd' : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f) :
    let ε := epsilon_threshold f d
    0 < ε ∧
    ∀ z ∈ ExtendedHypercube ε n, 0 < MvPolynomial.eval z f := by
  constructor
  · exact epsilon_threshold_pos f d hd hf_pos
  · exact choice_of_epsilon_pos f d _ hd hd' hf_pos
      (epsilon_threshold_pos f d hd hf_pos) (le_refl _)

/-- Step 2: Choose q so that η = n^{1/(2q)} ≤ 1 + ε, giving positivity on [-η,η]^n. -/
private theorem step2_scaled_positivity (f : MvPolynomial (Fin n) ℝ) (_d : ℕ) (ε : ℝ)
    (hn : 2 ≤ n) (hε : 0 < ε)
    (hf_ext_pos : ∀ z ∈ ExtendedHypercube ε n, 0 < MvPolynomial.eval z f) :
    let q := choose_q n ε
    ∀ x, (∀ i, |x i| ≤ eta n q) → 0 < MvPolynomial.eval x f := by
  intro q x hx
  apply hf_ext_pos
  apply ScaledHypercube_subset_ExtendedHypercube (eta n q) ε
      (by unfold eta; exact Real.rpow_nonneg (Nat.cast_nonneg n) _) (eta_le_one_add_eps hn ε hε)
  rw [ScaledHypercube_mem_abs _ (by unfold eta; exact Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact hx

/-- Step 3: Apply scaled_schmudgen to get f in the scaled preordering. -/
private theorem step3_scaled_schmudgen (f : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hn : 2 ≤ n) (_hd : 1 ≤ d) (hd' : f.totalDegree ≤ d)
    (q : ℕ) (_hq : 1 ≤ q)
    (hf_scaled_pos : ∀ x, (∀ i, |x i| ≤ eta n q) → 0 < MvPolynomial.eval x f)
    (r_schmudgen : ℕ)
    (hr1 : Real.pi * d * Real.sqrt (2 * n) ≤ r_schmudgen)
    (hr2 : Real.sqrt (constC n d * (polyMax (polyScale (eta n q) f) -
      polyMin (polyScale (eta n q) f)) / polyMin (polyScale (eta n q) f)) ≤
      r_schmudgen) :
    f ∈ ScaledBoxPreordering (eta n q) n ((r_schmudgen + 1) * n) := by
  exact scaled_schmudgen' f (eta n q) d r_schmudgen
    (by unfold eta; exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _)
    hd' hf_scaled_pos hr1 hr2

/-- The ScaledBoxPreordering with η = n^{1/(2q)} coincides with the generalized
    preordering for the scaled generators scaledGenerator i q. -/
private theorem ScaledBoxPreordering_eq_GenPreordering_scaledGen (q : ℕ) :
    ScaledBoxPreordering (eta n q) n r =
      GenPreordering (fun i : Fin n => scaledGenerator i q) r := by
  -- ScaledBoxGenerator (eta n q) i = scaledGenerator i q
  have hgen : ∀ i : Fin n, ScaledBoxGenerator (eta n q) i = scaledGenerator i q := by
    intro i
    simp only [ScaledBoxGenerator, scaledGenerator]
  -- ScaledBoxGeneratorProd (eta n q) J = ∏ j ∈ J, scaledGenerator j q
  have hprod : ∀ J : Finset (Fin n),
      ScaledBoxGeneratorProd (eta n q) J = ∏ j ∈ J, scaledGenerator j q := by
    intro J; unfold ScaledBoxGeneratorProd
    exact Finset.prod_congr rfl (fun j _ => hgen j)
  ext p
  simp only [ScaledBoxPreordering, GenPreordering, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨σ, hsos, hdeg, hsum⟩
    refine ⟨σ, hsos, fun J => ?_, ?_⟩
    · rw [← hprod]; exact hdeg J
    · simp_rw [← hprod]; exact hsum
  · rintro ⟨σ, hsos, hdeg, hsum⟩
    refine ⟨σ, hsos, fun J => ?_, ?_⟩
    · rw [hprod]; exact hdeg J
    · simp_rw [hprod]; exact hsum

/-- Step 4: Apply arXiv v3, Theorem 27 (`box_preordering_to_box_quadratic_module`)
    to shift from the scaled preordering to the standard quadratic module.

    The chain is:
    - f ∈ ScaledBoxPreordering(η, n, k)
    - = GenPreordering(scaledGenerator · q, k)  (by the identification above)
    - ⊆ BoxQuadraticModule n (k + n·(2q-2))  (by arXiv v3, Theorem 27) -/
private theorem step4_degree_shift (q : ℕ) (hq : 1 ≤ q) (hn : 0 < n)
    (k : ℕ) (f : MvPolynomial (Fin n) ℝ)
    (hf : f ∈ ScaledBoxPreordering (eta n q) n k) :
    f ∈ BoxQuadraticModule n (k + n * (2 * q - 2)) := by
  -- Convert ScaledBoxPreordering to GenPreordering
  rw [ScaledBoxPreordering_eq_GenPreordering_scaledGen] at hf
  -- Apply arXiv v3, Theorem 27.
  exact box_preordering_to_box_quadratic_module q hq hn k f hf

/-- Step 5: Combine the degree bounds.
    The total degree is:
    - From scaled Schmudgen: (r_schmudgen + 1) · n
    - From degree shift (arXiv v3, Theorem 27): + n · (2q - 2)
    Total: ((r_schmudgen + 1) + (2q - 2)) · n = (r_schmudgen + 2q - 1) · n -/
private theorem step5_total_degree (r_schmudgen q : ℕ) (hq : 1 ≤ q) :
    (r_schmudgen + 1) * n + n * (2 * q - 2) ≤ (r_schmudgen + 2 * q) * n := by
  -- (r+1)*n + n*(2q-2) = n*(r+1+2q-2) = n*(r+2q-1) ≤ n*(r+2q) = (r+2q)*n
  calc (r_schmudgen + 1) * n + n * (2 * q - 2)
      = n * (r_schmudgen + 1 + (2 * q - 2)) := by ring
    _ ≤ n * (r_schmudgen + 2 * q) := by
        apply Nat.mul_le_mul_left; omega
    _ = (r_schmudgen + 2 * q) * n := by ring

/-- For n = 1, the BoxPreordering equals the BoxQuadraticModule (since the only
    generator subsets are ∅ and {0}, matching the QM structure). -/
private theorem BoxPreordering_subset_BoxQuadraticModule_one (r : ℕ) :
    BoxPreordering 1 r ⊆ BoxQuadraticModule 1 r := by
  intro p ⟨σ, hsos, hdeg, hsum⟩
  -- For n=1, Finset.univ.powerset = {∅, {0}}, so the sum has two terms:
  -- σ ∅ * BoxSemialgebraicGeneratorProd ∅ + σ {0} * BoxSemialgebraicGeneratorProd {0}
  -- = σ ∅ * 1 + σ {0} * BoxSemialgebraicGenerator 0
  -- which matches the QM structure: σ₀ + σ 0 * BoxSemialgebraicGenerator 0
  refine ⟨σ ∅, fun i => σ {i}, hsos ∅, fun i => hsos {i}, ?_, ?_, ?_⟩
  · -- σ₀.totalDegree ≤ r
    have := hdeg ∅
    rwa [BoxSemialgebraicGeneratorProd_empty, mul_one] at this
  · -- (σ {i} * BoxSemialgebraicGenerator i).totalDegree ≤ r for each i : Fin 1
    intro i
    have := hdeg {i}
    have hprod : BoxSemialgebraicGeneratorProd ({i} : Finset (Fin 1)) =
        BoxSemialgebraicGenerator i := by
      unfold BoxSemialgebraicGeneratorProd
      simp
    rwa [hprod] at this
  · -- p = σ₀ + ∑ i : Fin 1, σ {i} * BoxSemialgebraicGenerator i
    rw [hsum, Fin.sum_univ_one]
    -- The powerset sum for Fin 1 is over {∅, {0}}
    have hpow : (Finset.univ : Finset (Fin 1)).powerset = {∅, {(0 : Fin 1)}} := rfl
    rw [hpow, Finset.sum_pair (by simp)]
    rw [BoxSemialgebraicGeneratorProd_empty, mul_one]
    have hprod : BoxSemialgebraicGeneratorProd ({(0 : Fin 1)} : Finset (Fin 1)) =
        BoxSemialgebraicGenerator 0 := by
      unfold BoxSemialgebraicGeneratorProd; simp
    rw [hprod]

/-! ## Helper lemmas for the main theorem -/

set_option maxHeartbeats 400000 in
-- This lemma closes a long nonlinear arithmetic chain involving `constUpperBound`,
-- `polySupNorm / polyMin`, logarithms, and casts before the final `nlinarith` step.
private theorem two_mul_choose_q_le (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constUpperBound n d * d ^ 2 * (Real.log (n : ℝ) + 1) *
      polySupNorm f / polyMin f ≤ r)
    (hn_pos : 0 < n) (hd_pos : 0 < d) (hd1 : 1 ≤ d) (hn2 : 2 ≤ n)
    (q : ℕ)
    (hq_bound : (q : ℝ) ≤ 4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f *
        Real.log ↑n + 1) :
    2 * q ≤ r := by
  -- Sufficient to show (2 * q : ℝ) ≤ (r : ℝ)
  suffices h : (2 * q : ℝ) ≤ (r : ℝ) by exact_mod_cast h
  have hmin_pos : 0 < polyMin f := polyMin_pos_of_pos f hf_pos
  have hsup_pos : 0 < polySupNorm f := polySupNorm_pos_of_pos f hf_pos
  have hcC_ge1 := one_le_constCChebyshev
  have hconstC_pos := constC_pos n d hn_pos hd_pos
  have hd_cast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hd2_ge1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hlog_n_pos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hSP : polyMin f ≤ polySupNorm f := polyMin_le_polySupNorm f hf_pos
  -- constUpperBound ≥ 4*cC + 2
  have hcub_ge : 8 * constCChebyshev + 2 ≤ constUpperBound n d := by
    unfold constUpperBound; nlinarith
  -- Multiply through by polyMin to avoid division
  have hr' : constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f ≤
      ↑r * polyMin f := by
    rwa [div_le_iff₀ hmin_pos] at hr
  -- From hq_bound, multiply through
  have hq' : (↑q : ℝ) * polyMin f ≤
      4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f := by
    have hqb := hq_bound
    have h1 : (↑q : ℝ) * polyMin f ≤
        (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f *
        Real.log ↑n + 1) * polyMin f :=
      mul_le_mul_of_nonneg_right hqb hmin_pos.le
    have h2 : (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f *
        Real.log ↑n + 1) * polyMin f =
        4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f := by
      field_simp
    linarith
  -- Chain: 2*q ≤ r via multiplied-through form, then cancel polyMin
  have hchain : (2 * ↑q : ℝ) * polyMin f ≤ ↑r * polyMin f := by
    -- 2q*M ≤ 8cC*d²*S*L + 2M ≤ (8cC+2)*d²*(L+1)*S ≤ cub*d²*(L+1)*S ≤ r*M
    have h2q' : 2 * ↑q * polyMin f ≤
        8 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n +
        2 * polyMin f := by
      calc 2 * (↑q : ℝ) * polyMin f
          = ↑q * polyMin f + ↑q * polyMin f := by ring
        _ ≤ (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f) +
            (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f) :=
            add_le_add hq' hq'
        _ = 8 * constCChebyshev * ↑d ^ 2 * polySupNorm f *
            Real.log ↑n + 2 * polyMin f := by ring
        _ ≤ _ := by
          nlinarith [constCChebyshev_pos,
            mul_nonneg (mul_nonneg (mul_nonneg
              (show (0:ℝ) ≤ 4 * constCChebyshev from
                by linarith [constCChebyshev_pos])
              (sq_nonneg (↑d : ℝ)))
              (polySupNorm_nonneg f))
            (show 0 ≤ Real.log ↑n from
              by linarith [hlog_n_pos])]
    have hkey : 8 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n +
        2 * polyMin f ≤
        (8 * constCChebyshev + 2) * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f := by
      -- RHS = 8cC*d²*(L+1)*S + 2*d²*(L+1)*S
      --     = 8cC*d²*L*S + 8cC*d²*S + 2*d²*L*S + 2*d²*S
      -- LHS = 8cC*d²*S*L + 2*M
      -- Diff = 8cC*d²*S + 2*d²*L*S + 2*d²*S - 2*M ≥ 0
      -- since 2*d²*S ≥ 2*M (by h_d2S_ge_M) and rest ≥ 0
      have h_d2S_ge_M : polyMin f ≤ ↑d ^ 2 * polySupNorm f := by nlinarith
      nlinarith [constCChebyshev_pos,
        mul_nonneg (show (0:ℝ) ≤ 8 * constCChebyshev * ↑d ^ 2 by positivity) hsup_pos.le,
        mul_nonneg (show (0:ℝ) ≤ 2 * ↑d ^ 2 * Real.log ↑n by positivity) hsup_pos.le]
    have hcub' : (8 * constCChebyshev + 2) * ↑d ^ 2 * (Real.log ↑n + 1) *
        polySupNorm f ≤ constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) *
        polySupNorm f := by
      apply mul_le_mul_of_nonneg_right _ hsup_pos.le
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_right hcub_ge (by positivity)
    linarith
  exact le_of_mul_le_mul_right hchain hmin_pos

set_option maxHeartbeats 400000 in
-- The proof expands the `constC`/`constUpperBound` inequalities and keeps several casted
-- real and natural bounds live through one large comparison chain.
private theorem schmudgen_hr1_bound (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constUpperBound n d * d ^ 2 * (Real.log (n : ℝ) + 1) *
      polySupNorm f / polyMin f ≤ r)
    (hn_pos : 0 < n) (hd_pos : 0 < d) (hd1 : 1 ≤ d) (hn2 : 2 ≤ n)
    (q : ℕ)
    (hq_bound : (q : ℝ) ≤ 4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f *
        Real.log ↑n + 1)
    (h2q_le_r : 2 * q ≤ r) :
    Real.pi * ↑d * Real.sqrt (2 * ↑n) ≤ ↑(r - 2 * q) := by
  set r_s := r - 2 * q with hr_s_def
  have hr_decomp : r_s + 2 * q = r := by omega
  -- r_s = r - 2*q, so (r_s : ℝ) = (r : ℝ) - 2*(q : ℝ)
  have hr_s_cast : (r_s : ℝ) = (r : ℝ) - 2 * (q : ℝ) := by
    have h := hr_decomp  -- r_s + 2 * q = r in ℕ
    have : (r_s : ℝ) + 2 * (q : ℝ) = (r : ℝ) := by exact_mod_cast h
    linarith
  rw [hr_s_cast]
  -- Need: π*d*√(2n) ≤ r - 2*q (in ℝ)
  -- From hr: r ≥ constUpperBound * d² * (log n+1) * polySupNorm f / polyMin f
  -- From hq_bound: q ≤ 2*cC*d²*(polySupNorm f / polyMin f)*log n + 1
  -- Strategy: show r - 2q ≥ 4*cC*constC*d² * (polySupNorm f / polyMin f)
  --           and 4*cC*constC*d²*R ≥ π*d*√(2n) using constC ≥ 2nπ²d²
  have hmin_pos : 0 < polyMin f := polyMin_pos_of_pos f hf_pos
  have hsup_pos : 0 < polySupNorm f := polySupNorm_pos_of_pos f hf_pos
  have hcC_pos := constCChebyshev_pos
  have hcC_ge1 := one_le_constCChebyshev
  have hconstC_pos := constC_pos n d hn_pos hd_pos
  have hR_ge1 := condition_number_ge_one f hf_pos
  have hd_cast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hd2_ge1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hlog_n_pos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hSP : polyMin f ≤ polySupNorm f := polyMin_le_polySupNorm f hf_pos
  have hR_pos : 0 < polySupNorm f / polyMin f := div_pos hsup_pos hmin_pos
  -- Lower bound on constC
  have hconstC_lb := constC_lower_bound n d hn_pos hd_pos
  -- constC ≥ 2nπ²d², so constC + 1 ≥ 2nπ²d²
  have hconstC1_lb : 2 * ↑n * Real.pi ^ 2 * ↑d ^ 2 ≤ constC n d + 1 := by linarith
  -- constUpperBound = 4*cC*(constC+1) + 4*cC + 2
  -- ≥ 4*cC*(constC+1)
  -- ≥ 4*cC*2nπ²d²
  -- = 8*cC*nπ²d²
  -- Establish: r - 2q ≥ 4*cC*constC*d²*R
  -- From the hypothesis hr (r*M ≥ constUpperBound*d²*(L+1)*S):
  -- r*M ≥ constUpperBound*d²*(L+1)*S
  -- 2q*M ≤ 4cC*d²*S*L + 2*M (from doubled hq')
  -- So (r-2q)*M ≥ constUpperBound*d²*(L+1)*S - 4cC*d²*S*L - 2*M
  -- = [4cC*(constC+1)+4cC+2]*d²*(L+1)*S - 4cC*d²*S*L - 2*M
  -- = 4cC*(constC+1)*d²*(L+1)*S + (4cC+2)*d²*(L+1)*S - 4cC*d²*S*L - 2*M
  -- = 4cC*(constC+1)*d²*(L+1)*S + 4cC*d²*S + 2*d²*(L+1)*S - 2*M
  -- ≥ 4cC*(constC+1)*d²*S  (since 4cC*d²*S ≥ 0, 2*d²*(L+1)*S ≥ 2*M)
  -- = 4cC*(constC+1)*d²*S
  -- where S = polySupNorm f, M = polyMin f
  -- So (r-2q) ≥ 4cC*(constC+1)*d²*S/M = 4cC*(constC+1)*d²*R
  -- ≥ 4cC*2nπ²d²*d²*R = 8cC*nπ²d⁴*R ≥ 8nπ²d⁴ ≥ π*d*√(2n)
  -- For the last step, use √(2n) ≤ 2n for n ≥ 1, hence
  -- πd√(2n) ≤ 2πnd. Meanwhile 8nπ²d⁴ ≥ 2πnd because 4πd³ ≥ 1.
  -- The following proof implements these estimates.

  -- Step A: Lower bound on r - 2q
  -- We'll show (r - 2*q : ℝ) ≥ 4*cC*constC*d²*(polySupNorm f / polyMin f)
  -- Working in the multiplied-through form:
  have hr' : constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f ≤
      ↑r * polyMin f := by
    rwa [div_le_iff₀ hmin_pos] at hr
  have hq' : (↑q : ℝ) * polyMin f ≤
      4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f := by
    have h1 := mul_le_mul_of_nonneg_right hq_bound hmin_pos.le
    have h2 : (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f *
        Real.log ↑n + 1) * polyMin f =
        4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f := by
      field_simp
    linarith
  -- (r-2q)*M ≥ constUpperBound*d²*(L+1)*S - 8cC*d²*S*L - 2*M
  have h_r_minus_2q_M : ((r : ℝ) - 2 * (q : ℝ)) * polyMin f ≥
      constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f -
      8 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n - 2 * polyMin f := by
    have h2q : 2 * (↑q : ℝ) * polyMin f ≤
        8 * constCChebyshev * ↑d ^ 2 * polySupNorm f *
        Real.log ↑n + 2 * polyMin f := by
      nlinarith [hq']
    nlinarith
  -- Simplify the RHS:
  -- constUpperBound*d²*(L+1)*S - 8cC*d²*S*L - 2*M
  -- = [4cC(C+1) + 8cC + 2]*d²*(L+1)*S - 8cC*d²*S*L - 2*M
  -- ≥ 4cC*C*d²*S  (see analysis above)
  have h_rs_lower_M : ((r : ℝ) - 2 * (q : ℝ)) * polyMin f ≥
      4 * constCChebyshev * constC n d * ↑d ^ 2 * polySupNorm f := by
    -- Split constUpperBound into 4cC*C part and (4cC*(C+1) - 4cC*C + 8cC + 2) = (4cC + 8cC + 2)
    -- constUpperBound = 4cC*(C+1) + 8cC + 2
    -- So constUpperBound*d²*(L+1)*S = 4cC*(C+1)*d²*(L+1)*S + (8cC+2)*d²*(L+1)*S
    -- ≥ 4cC*C*d²*S + (8cC+2)*d²*S (using L+1 ≥ 1 and C+1 ≥ C)
    -- And (8cC+2)*d²*S ≥ 8cC*d²*S*L + 2*M by the hkey bound from hr
    -- Step 1: constUpperBound ≥ 4cC*C + 8cC + 2
    have hcub_split : constUpperBound n d ≥
        4 * constCChebyshev * constC n d + (8 * constCChebyshev + 2) := by
      unfold constUpperBound; nlinarith [constCChebyshev_pos]
    -- Step 2: constUpperBound*d²*(L+1)*S ≥ (4cC*C)*d²*(L+1)*S + (8cC+2)*d²*(L+1)*S
    -- ≥ 4cC*C*d²*S + (8cC+2)*d²*(L+1)*S (dropping L from first term)
    have h_split1 : 4 * constCChebyshev * constC n d * ↑d ^ 2 * polySupNorm f ≤
        4 * constCChebyshev * constC n d * ↑d ^ 2 * (Real.log ↑n + 1) *
        polySupNorm f := by
      have : (1 : ℝ) ≤ Real.log ↑n + 1 := by linarith
      calc 4 * constCChebyshev * constC n d * ↑d ^ 2 * polySupNorm f
          = 4 * constCChebyshev * constC n d * ↑d ^ 2 * 1 * polySupNorm f := by ring
        _ ≤ 4 * constCChebyshev * constC n d * ↑d ^ 2 * (Real.log ↑n + 1) *
            polySupNorm f := by
            apply mul_le_mul_of_nonneg_right _ hsup_pos.le
            exact mul_le_mul_of_nonneg_left this (by positivity)
    -- Step 3: (8cC+2)*d²*(L+1)*S ≥ 8cC*d²*S*L + 2*M (from hkey via hr)
    have h_d2S_ge_M : polyMin f ≤ ↑d ^ 2 * polySupNorm f :=
      le_trans hSP (le_mul_of_one_le_left hsup_pos.le hd2_ge1)
    have h_split2 : 8 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n +
        2 * polyMin f ≤
        (8 * constCChebyshev + 2) * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f := by
      -- RHS = 8cC*d²*(L+1)*S + 2*d²*(L+1)*S
      --     = 8cC*d²*L*S + 8cC*d²*S + 2*d²*L*S + 2*d²*S
      -- LHS = 8cC*d²*S*L + 2*M
      -- Diff = 8cC*d²*S + 2*d²*L*S + 2*d²*S - 2*M ≥ 0
      -- since 2*d²*S ≥ 2*M (by h_d2S_ge_M) and rest ≥ 0
      have h1 : (0 : ℝ) ≤ 4 * constCChebyshev * ↑d ^ 2 * polySupNorm f := by positivity
      have h2 : (0 : ℝ) ≤ 2 * ↑d ^ 2 * Real.log ↑n * polySupNorm f := by positivity
      linarith [h_d2S_ge_M]
    -- Step 4: Combine
    -- constUpperBound*d²*(L+1)*S ≥ 4cC*C*d²*(L+1)*S + (8cC+2)*d²*(L+1)*S
    have h_cub_bound : constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f ≥
        4 * constCChebyshev * constC n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f +
        (8 * constCChebyshev + 2) * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f := by
      have : (4 * constCChebyshev * constC n d + (8 * constCChebyshev + 2)) *
          ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f ≤
          constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f := by
        apply mul_le_mul_of_nonneg_right _ hsup_pos.le
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_right hcub_split (by positivity)
      linarith
    -- (r-2q)*M ≥ cub*d²*(L+1)*S - 8cC*d²*S*L - 2M
    --          ≥ [4cC*C*d²*(L+1)*S + (8cC+2)*d²*(L+1)*S] - 8cC*d²*S*L - 2M
    --          ≥ 4cC*C*d²*(L+1)*S + [8cC*d²*S*L + 2M] - 8cC*d²*S*L - 2M (by h_split2)
    --          = 4cC*C*d²*(L+1)*S
    --          ≥ 4cC*C*d²*S (since L+1 ≥ 1)
    linarith
  -- Step B: We already have (r-2q)*M ≥ 4cC*C*d²*S where M = polyMin, S = polySupNorm
  -- π*d*√(2n) ≤ 4cC*C*d²*S/M ≤ r-2q
  -- First bound π*d*√(2n) ≤ 4cC*C*d²*S/M via π*d*√(2n)*M ≤ 4cC*C*d²*S
  -- Since S/M ≥ 1 and 4cC*C*d² ≥ 4*1*2nπ²d²*d² = 8nπ²d⁴:
  -- π*d*√(2n) ≤ 8nπ²d⁴ (proved below) ≤ 4cC*C*d² ≤ 4cC*C*d²*S/M
  -- Step B1: 4cC*C*d² ≥ 8nπ²d⁴
  have h_4cCCd2 : 8 * ↑n * Real.pi ^ 2 * ↑d ^ 4 ≤
      4 * constCChebyshev * constC n d * ↑d ^ 2 := by
    have h1 : (4 : ℝ) * 1 ≤ 4 * constCChebyshev := by linarith
    have h2 := hconstC_lb  -- 2*n*π²*d² ≤ constC n d
    calc 8 * ↑n * Real.pi ^ 2 * ↑d ^ 4
        = (4 * 1) * (2 * ↑n * Real.pi ^ 2 * ↑d ^ 2) * ↑d ^ 2 := by ring
      _ ≤ (4 * constCChebyshev) * constC n d * ↑d ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity : (0:ℝ) ≤ ↑d ^ 2)
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4 * constCChebyshev * constC n d * ↑d ^ 2 := by ring
  -- Step B2: √(2n) ≤ 2n
  have h_sqrt_bound : Real.sqrt (2 * ↑n) ≤ 2 * ↑n := by
    have h2n_nn : (0 : ℝ) ≤ 2 * ↑n := by positivity
    have h2n_ge1 : (1 : ℝ) ≤ 2 * ↑n := by
      have : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn2
      linarith
    calc Real.sqrt (2 * ↑n) ≤ Real.sqrt ((2 * ↑n) ^ 2) := by
          apply Real.sqrt_le_sqrt; nlinarith
      _ = 2 * ↑n := Real.sqrt_sq h2n_nn
  -- Step B3: π*d*√(2n) ≤ 8nπ²d⁴
  have h_pid_sqrt : Real.pi * ↑d * Real.sqrt (2 * ↑n) ≤
      8 * ↑n * Real.pi ^ 2 * ↑d ^ 4 := by
    calc Real.pi * ↑d * Real.sqrt (2 * ↑n)
        ≤ Real.pi * ↑d * (2 * ↑n) :=
          mul_le_mul_of_nonneg_left h_sqrt_bound (by positivity)
      _ = 2 * Real.pi * ↑n * ↑d := by ring
      _ ≤ 8 * ↑n * Real.pi ^ 2 * ↑d ^ 4 := by
          -- 2πnd ≤ 8nπ²d⁴ ⟺ 1 ≤ 4πd³ (divide by 2πnd > 0)
          -- 4πd³ ≥ 4·3·1 = 12 ≥ 1
          have hn_cast : (0 : ℝ) < ↑n := by exact_mod_cast hn_pos
          have hd3 : (1 : ℝ) ≤ ↑d ^ 3 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
          have hpi_gt3 := Real.pi_gt_three
          have hpi_pos := Real.pi_pos
          -- 2πnd ≤ 2πnd·(4πd³) = 8nπ²d⁴ since 1 ≤ 4πd³
          have h4pd3 : (1 : ℝ) ≤ 4 * Real.pi * ↑d ^ 3 := by nlinarith
          have h2pnd : (0 : ℝ) ≤ 2 * Real.pi * ↑n * ↑d := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h4pd3 h2pnd]
  -- Step B4: chain everything
  -- π*d*√(2n) ≤ 8nπ²d⁴ ≤ 4cC*C*d² ≤ 4cC*C*d²*(S/M) ≤ (r-2q)
  -- Chain: π*d*√(2n)*M ≤ 8nπ²d⁴*M ≤ 4cC*C*d²*M ≤ 4cC*C*d²*S ≤ (r-2q)*M
  have key : Real.pi * ↑d * Real.sqrt (2 * ↑n) * polyMin f ≤
      ((r : ℝ) - 2 * (q : ℝ)) * polyMin f := by
    calc Real.pi * ↑d * Real.sqrt (2 * ↑n) * polyMin f
        ≤ (8 * ↑n * Real.pi ^ 2 * ↑d ^ 4) * polyMin f :=
          mul_le_mul_of_nonneg_right h_pid_sqrt hmin_pos.le
      _ ≤ (4 * constCChebyshev * constC n d * ↑d ^ 2) * polyMin f :=
          mul_le_mul_of_nonneg_right h_4cCCd2 hmin_pos.le
      _ ≤ 4 * constCChebyshev * constC n d * ↑d ^ 2 * polySupNorm f :=
          mul_le_mul_of_nonneg_left hSP (by positivity)
      _ ≤ ((r : ℝ) - 2 * (q : ℝ)) * polyMin f := by linarith [h_rs_lower_M]
  exact le_of_mul_le_mul_right key hmin_pos

set_option maxHeartbeats 1600000 in
-- This proof combines Markov perturbation estimates, spread/minimum bounds, and a squaring
-- argument; reducing the budget currently times out elaboration.
private theorem schmudgen_hr2_bound (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constUpperBound n d * d ^ 2 * (Real.log (n : ℝ) + 1) *
      polySupNorm f / polyMin f ≤ r)
    (hn_pos : 0 < n) (hd_pos : 0 < d) (hd1 : 1 ≤ d) (hn2 : 2 ≤ n)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_def : ε = epsilon_threshold f d)
    (q : ℕ) (hq_def : q = choose_q n ε)
    (hq_bound : (q : ℝ) ≤ 4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f *
        Real.log ↑n + 1)
    (h2q_le_r : 2 * q ≤ r) :
    Real.sqrt (constC n d * (polyMax (polyScale (eta n q) f) -
        polyMin (polyScale (eta n q) f)) / polyMin (polyScale (eta n q) f)) ≤
        ↑(r - 2 * q) := by
  set r_s := r - 2 * q with hr_s_def
  have hr_decomp : r_s + 2 * q = r := by omega
  set η := eta n q with hη_def
  set g := polyScale η f with hg_def
  have hη_pos : (0 : ℝ) < η := by
    simp only [hη_def]; unfold eta
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hη_nn : (0 : ℝ) ≤ η := le_of_lt hη_pos
  have hmin_pos : 0 < polyMin f := polyMin_pos_of_pos f hf_pos
  have hsup_pos : 0 < polySupNorm f := polySupNorm_pos_of_pos f hf_pos
  have hconstC_pos := constC_pos n d hn_pos hd_pos
  have hSP : polyMin f ≤ polySupNorm f := polyMin_le_polySupNorm f hf_pos
  have hη_le_eps : η ≤ 1 + ε := by
    rw [hη_def, hq_def]
    exact eta_le_one_add_eps hn2 ε hε_pos
  -- Step 1: polyMin(g) ≥ polyMin f / 2
  have hg_min_bound : polyMin f / 2 ≤ polyMin g := by
    apply le_csInf (Hypercube_image_nonempty g)
    rintro _ ⟨x, hx, rfl⟩
    simp only [hg_def, polyScale_eval]
    have hscaled_in_ext : (fun i => η * x i) ∈ ExtendedHypercube ε n := by
      apply ScaledHypercube_subset_ExtendedHypercube η ε hη_nn hη_le_eps
      rw [ScaledHypercube_mem_abs η hη_nn]
      intro i; have hi := (Hypercube_mem_iff x).mp hx i
      rw [abs_mul, abs_of_pos hη_pos]
      exact mul_le_of_le_one_right hη_pos.le (abs_le.mpr ⟨hi.1, hi.2⟩)
    exact choice_of_epsilon f d ε hd1 hd hf_pos hε_pos (le_of_eq hε_def) _ hscaled_in_ext
  have hg_min_pos : 0 < polyMin g := by linarith
  -- Step 2: Bound spread ≤ 4 * polySupNorm f
  have hg_spread : polyMax g - polyMin g ≤ 4 * polySupNorm f := by
    have hosc := oscillation_le_two_supnorm g
    suffices hg_sup : polySupNorm g ≤ 2 * polySupNorm f by linarith
    -- polySupNorm(polyScale η f) ≤ 2*polySupNorm f
    -- via triangle inequality + Markov perturbation
    -- Strategy: for each x ∈ B^n, |f(η·x)| ≤ |f(clamp(η·x))| + |f(η·x) - f(clamp(η·x))|
    --           ≤ polySupNorm f + polyMin f / 2 ≤ 2 * polySupNorm f
    unfold polySupNorm
    apply csSup_le (Set.image_nonempty.mpr Hypercube_nonempty)
    rintro _ ⟨x, hx, rfl⟩
    simp only [hg_def]
    rw [polyScale_eval]
    -- y = fun i => η * x i is in ExtendedHypercube ε n
    set y := (fun i => η * x i) with hy_def
    have hy_ext : y ∈ ExtendedHypercube ε n := by
      apply ScaledHypercube_subset_ExtendedHypercube η ε hη_nn hη_le_eps
      rw [ScaledHypercube_mem_abs η hη_nn]
      intro i; have hi := (Hypercube_mem_iff x).mp hx i
      rw [abs_mul, abs_of_pos hη_pos]
      exact mul_le_of_le_one_right hη_pos.le (abs_le.mpr ⟨hi.1, hi.2⟩)
    -- Triangle inequality: |f(y)| ≤ |f(clampVec y)| + |f(y) - f(clampVec y)|
    have hclamp_mem : clampVec y ∈ Hypercube n := clampVec_mem_Hypercube y
    have hf_clamp_bound : |MvPolynomial.eval (clampVec y) f| ≤ polySupNorm f :=
      polySupNorm_eval_le f (polySupNorm f) le_rfl (clampVec y) hclamp_mem
    have hε_le : ε ≤ 1 / (d : ℝ) ^ 2 := by
      have hε_bound : ε ≤ polyMin f / (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f) := by
        simp only [hε_def]; exact le_refl _
      calc ε ≤ polyMin f / (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f) := hε_bound
        _ ≤ polySupNorm f / (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f) := by
            have h_denom_pos : (0:ℝ) < 4 * constCChebyshev * ↑d ^ 2 * polySupNorm f := by
              apply mul_pos (mul_pos (mul_pos (by positivity) constCChebyshev_pos)
                (pow_pos (Nat.cast_pos.mpr hd_pos) 2)) hsup_pos
            exact div_le_div_of_nonneg_right (polyMin_le_polySupNorm f hf_pos) h_denom_pos.le
        _ = 1 / (4 * constCChebyshev * (d : ℝ) ^ 2) := by field_simp
        _ ≤ 1 / (d : ℝ) ^ 2 := by
            apply div_le_div_of_nonneg_left (by positivity)
              (by positivity : (0:ℝ) < ↑d ^ 2)
            exact le_mul_of_one_le_left (by positivity) (by nlinarith [one_le_constCChebyshev])
    have hperturb : |MvPolynomial.eval y f - MvPolynomial.eval (clampVec y) f| ≤
        2 * constCChebyshev * ↑d ^ 2 * ε * polySupNorm f :=
      markov_perturbation_bound f d hd y ε hε_pos hε_le hy_ext
    -- 2·cC * d² * ε * polySupNorm f ≤ polyMin f / 2 ≤ polySupNorm f
    have hε_bound : 2 * constCChebyshev * ↑d ^ 2 * ε * polySupNorm f ≤ polyMin f / 2 := by
      have hcd_pos : (0 : ℝ) < 2 * constCChebyshev * (d : ℝ) ^ 2 :=
        mul_pos (mul_pos (by norm_num) constCChebyshev_pos)
          (pow_pos (Nat.cast_pos.mpr hd_pos) 2)
      calc 2 * constCChebyshev * (d : ℝ) ^ 2 * ε * polySupNorm f
          ≤ 2 * constCChebyshev * (d : ℝ) ^ 2 *
            (polyMin f / (4 * constCChebyshev * (d : ℝ) ^ 2 * polySupNorm f)) *
            polySupNorm f := by
            apply mul_le_mul_of_nonneg_right
            · have hε_bound_internal :
                ε ≤ polyMin f / (4 * constCChebyshev *
                  ↑d ^ 2 * polySupNorm f) := by
                simp only [hε_def]; unfold epsilon_threshold; exact le_refl _
              exact mul_le_mul_of_nonneg_left hε_bound_internal (le_of_lt hcd_pos)
            · exact le_of_lt hsup_pos
        _ = polyMin f / 2 := by
            have hcC_ne : constCChebyshev ≠ 0 := ne_of_gt constCChebyshev_pos
            have hsup_ne : polySupNorm f ≠ 0 := ne_of_gt hsup_pos
            have hd2_ne : (d : ℝ) ^ 2 ≠ 0 := ne_of_gt (pow_pos (Nat.cast_pos.mpr hd_pos) 2)
            field_simp; ring
    have hperturb_le : |MvPolynomial.eval y f - MvPolynomial.eval (clampVec y) f| ≤
        polySupNorm f := le_trans hperturb (le_trans hε_bound (by linarith [hSP]))
    calc |MvPolynomial.eval y f|
        ≤ |MvPolynomial.eval (clampVec y) f| +
          |MvPolynomial.eval y f - MvPolynomial.eval (clampVec y) f| := by
            have := abs_sub_abs_le_abs_sub (MvPolynomial.eval y f)
                (MvPolynomial.eval (clampVec y) f)
            linarith
      _ ≤ polySupNorm f + polySupNorm f := add_le_add hf_clamp_bound hperturb_le
      _ = 2 * polySupNorm f := by ring
  -- Step 3: Bound argument ≤ 8*constC*R
  have h_arg : constC n d * (polyMax g - polyMin g) / polyMin g ≤
      8 * constC n d * polySupNorm f / polyMin f := by
    -- constC * spread_g / min_g ≤ constC * 4S / (M/2)
    -- = 8 * constC * S / M
    -- Use: spread_g ≤ 4S (numerator bound), min_g ≥ M/2 (denominator bound)
    have h_num : constC n d * (polyMax g - polyMin g) ≤ constC n d * (4 * polySupNorm f) :=
      mul_le_mul_of_nonneg_left hg_spread hconstC_pos.le
    have h_denom : polyMin f / 2 ≤ polyMin g := hg_min_bound
    have h8 : constC n d * (4 * polySupNorm f) / (polyMin f / 2) =
        8 * constC n d * polySupNorm f / polyMin f := by field_simp; ring
    calc constC n d * (polyMax g - polyMin g) / polyMin g
        ≤ constC n d * (4 * polySupNorm f) / (polyMin f / 2) :=
          div_le_div₀ (mul_nonneg hconstC_pos.le (by linarith [polySupNorm_nonneg f]))
            h_num (by linarith) h_denom
      _ = 8 * constC n d * polySupNorm f / polyMin f := h8
  -- Step 4: √(8*constC*R) ≤ r_s via squaring
  have h_sqrt_mono := Real.sqrt_le_sqrt h_arg
  suffices h : Real.sqrt (8 * constC n d * polySupNorm f / polyMin f) ≤ ↑r_s by linarith
  have hr_s_cast : (r_s : ℝ) = (r : ℝ) - 2 * (q : ℝ) := by
    have : (r_s : ℝ) + 2 * (q : ℝ) = (r : ℝ) := by exact_mod_cast hr_decomp
    linarith
  -- r_s ≥ 4*cC*constC*d²*S/M (re-derive from hr1_s or directly)
  -- Since π*d*√(2n) ≤ r_s and 4*cC*constC*d²*R ≤ 8nπ²d⁴... no, that's weaker
  -- Better: re-derive from hr and hq_bound like in hr1_s
  have hrs_ge : 4 * constCChebyshev * constC n d * ↑d ^ 2 * polySupNorm f / polyMin f ≤
      (r_s : ℝ) := by
    -- From hr1_s: π*d*√(2n) ≤ r_s, and 4*cC*C*d²*S/M ≤ π*d*√(2n)?
    -- No, that's the wrong direction. Let me re-derive properly.
    -- r_s = r - 2q, r ≥ constUpperBound*d²*(L+1)*S/M, 2q ≤ 8cC*d²*S/M*L + 2
    -- r_s ≥ constUpperBound*d²*(L+1)*S/M - 8cC*d²*S/M*L - 2
    -- ≥ 4cC*C*d²*S/M (from the analysis in hr1_s)
    rw [hr_s_cast, div_le_iff₀ hmin_pos]
    -- Need: 4*cC*C*d²*S ≤ (r-2q)*M
    -- From hr: constUpperBound*d²*(L+1)*S ≤ r*M (after div_le_iff)
    have hr' : constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f ≤
        ↑r * polyMin f := by rwa [div_le_iff₀ hmin_pos] at hr
    have hq' : (↑q : ℝ) * polyMin f ≤
        4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f := by
      have h1 := mul_le_mul_of_nonneg_right hq_bound hmin_pos.le
      have h2 : (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f *
          Real.log ↑n + 1) * polyMin f =
          4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f := by
        field_simp
      linarith
    -- Re-derive h_rs_lower_M
    have hlog_n_pos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hd2_ge1 : (1 : ℝ) ≤ (↑d : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (↑d : ℝ) := by exact_mod_cast hd1
      nlinarith [sq_nonneg ((↑d : ℝ) - 1)]
    have h_d2S_ge_M : polyMin f ≤ ↑d ^ 2 * polySupNorm f :=
      le_trans hSP (le_mul_of_one_le_left hsup_pos.le hd2_ge1)
    have hcub_split : constUpperBound n d ≥
        4 * constCChebyshev * constC n d + (8 * constCChebyshev + 2) := by
      unfold constUpperBound; nlinarith [constCChebyshev_pos]
    have h_split1 : 4 * constCChebyshev * constC n d * ↑d ^ 2 * polySupNorm f ≤
        4 * constCChebyshev * constC n d * ↑d ^ 2 * (Real.log ↑n + 1) *
        polySupNorm f := by
      have : (1 : ℝ) ≤ Real.log ↑n + 1 := by linarith
      have h_log_ge1 := this
      have h_prod_nn : (0 : ℝ) ≤ 4 * constCChebyshev * constC n d * (↑d : ℝ) ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith [constCChebyshev_pos]) hconstC_pos.le)
          (pow_nonneg (show (0:ℝ) ≤ ↑d from Nat.cast_nonneg d) 2)
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h_log_ge1 h_prod_nn) hsup_pos.le]
    have h_split2 : 8 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n +
        2 * polyMin f ≤
        (8 * constCChebyshev + 2) * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f := by
      nlinarith [constCChebyshev_pos, (show (0:ℝ) ≤ ↑d from Nat.cast_nonneg d),
        sq_nonneg (↑d : ℝ), h_d2S_ge_M, hlog_n_pos]
    have h_cub_bound : constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f ≥
        4 * constCChebyshev * constC n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f +
        (8 * constCChebyshev + 2) * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f := by
      have : (4 * constCChebyshev * constC n d + (8 * constCChebyshev + 2)) *
          ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f ≤
          constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcub_split
              (pow_nonneg (show (0:ℝ) ≤ ↑d from Nat.cast_nonneg d) 2))
            (by linarith))
          hsup_pos.le
      linarith
    have h2q : 2 * (↑q : ℝ) * polyMin f ≤
        8 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + 2 * polyMin f := by
      calc 2 * (↑q : ℝ) * polyMin f
          = ↑q * polyMin f + ↑q * polyMin f := by ring
        _ ≤ (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f) +
            (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f) :=
            add_le_add hq' hq'
        _ = 8 * constCChebyshev * ↑d ^ 2 * polySupNorm f *
            Real.log ↑n + 2 * polyMin f := by ring
        _ ≤ _ := by
          nlinarith [constCChebyshev_pos,
            mul_nonneg (mul_nonneg (mul_nonneg
              (show (0:ℝ) ≤ 4 * constCChebyshev from
                by linarith [constCChebyshev_pos])
              (sq_nonneg (↑d : ℝ)))
              (polySupNorm_nonneg f))
            (show 0 ≤ Real.log ↑n from
              by linarith [hlog_n_pos])]
    have h_r_minus_2q_M : ((r : ℝ) - 2 * (q : ℝ)) * polyMin f ≥
        constUpperBound n d * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f -
        8 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n - 2 * polyMin f := by
      nlinarith
    nlinarith [h_split1, h_split2]
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ↑r_s)]
  apply Real.sqrt_le_sqrt
  have hrs_nn : (0 : ℝ) ≤ ↑r_s := Nat.cast_nonneg r_s
  have h_expr_nn : (0 : ℝ) ≤ 4 * constCChebyshev * constC n d * ↑d ^ 2 *
      polySupNorm f / polyMin f :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith [constCChebyshev_pos])
      hconstC_pos.le)
      (pow_nonneg (show (0:ℝ) ≤ ↑d from Nat.cast_nonneg d) 2))
      hsup_pos.le) hmin_pos.le
  have hrs_sq : (4 * constCChebyshev * constC n d * ↑d ^ 2 * polySupNorm f / polyMin f) ^ 2 ≤
      (r_s : ℝ) ^ 2 :=
    sq_le_sq' (by linarith) hrs_ge
  have hcC_ge1 := one_le_constCChebyshev
  have hd_cast' : (1 : ℝ) ≤ ↑d := by exact_mod_cast hd1
  have hd4_ge1 : (1 : ℝ) ≤ (↑d : ℝ) ^ 4 := by nlinarith [sq_nonneg ((↑d : ℝ) - 1)]
  have h_coeff : 1 ≤ 2 * constCChebyshev ^ 2 * constC n d * (↑d : ℝ) ^ 4 := by
    have hC_ge1 : (1 : ℝ) ≤ constC n d := by
      have hclb := constC_lower_bound n d (by omega) hd_pos
      have hn_cast : (2 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn2
      have hd_cast : (1 : ℝ) ≤ (↑d : ℝ) := by exact_mod_cast hd1
      -- π² > 9 from π > 3
      have hpi_sq : (9 : ℝ) < Real.pi ^ 2 := by
        nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
      -- constC ≥ 2*n*π²*d² ≥ 2*2*9*1 = 36
      have h1 : (18 : ℝ) < ↑n * Real.pi ^ 2 := by nlinarith
      have h2 : (1 : ℝ) ≤ (↑d : ℝ) ^ 2 := by nlinarith [sq_nonneg ((↑d : ℝ) - 1)]
      linarith [show (36 : ℝ) ≤ 2 * (↑n * Real.pi ^ 2) * ↑d ^ 2 from by nlinarith]
    have hcC2_ge1 : (1 : ℝ) ≤ constCChebyshev ^ 2 := by
      nlinarith [sq_nonneg (constCChebyshev - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hd4_ge1
      (show (0:ℝ) ≤ 2 * constCChebyshev ^ 2 * constC n d from by nlinarith),
      mul_le_mul_of_nonneg_left hC_ge1
      (show (0:ℝ) ≤ 2 * constCChebyshev ^ 2 from by nlinarith)]
  calc 8 * constC n d * polySupNorm f / polyMin f
      ≤ 8 * constC n d * polySupNorm f / polyMin f *
        (2 * constCChebyshev ^ 2 * constC n d * (↑d : ℝ) ^ 4 *
         (polySupNorm f / polyMin f)) := by
          rw [le_mul_iff_one_le_right (by
            apply div_pos (by nlinarith [hconstC_pos]) hmin_pos)]
          calc (1 : ℝ) ≤ 2 * constCChebyshev ^ 2 * constC n d * (↑d : ℝ) ^ 4 := h_coeff
            _ ≤ 2 * constCChebyshev ^ 2 * constC n d * (↑d : ℝ) ^ 4 *
                (polySupNorm f / polyMin f) := by
              rw [le_mul_iff_one_le_right (by
                nlinarith [sq_nonneg (constCChebyshev - 1), sq_nonneg ((↑d : ℝ) - 1)])]
              rw [le_div_iff₀ hmin_pos]; linarith [hSP]
    _ = (4 * constCChebyshev * constC n d * ↑d ^ 2 * polySupNorm f / polyMin f) ^ 2 := by
        field_simp; ring
    _ ≤ (r_s : ℝ) ^ 2 := hrs_sq

/-! ## Simplified upper degree bound (qualitative form of arXiv v3, Theorem 3) -/

-- Upper degree bound proof delegates heavy arithmetic to helper lemmas
/-- Simplified Putinar upper degree bound, giving the qualitative content of
    arXiv v3, Theorem 3. If `f > 0` on B^n and has degree at most d, then
    `f ∈ QM(B^n)_{r·n}` whenever r is at least the displayed threshold. This
    supplies a certificate at the corresponding asymptotic order.

    Proof: (1) Extend positivity to [-1-ε,1+ε]^n via Lemma 28.
    (2) Choose q so η = n^{1/(2q)} ≤ 1+ε. (3) Apply Corollary 22
    (scaled Schmüdgen). (4) Apply Theorem 27 (degree shift). -/
theorem upper_degree_bound_weak (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constUpperBound n d * d ^ 2 * (Real.log (n : ℝ) + 1) *
      polySupNorm f / polyMin f ≤ r) :
    f ∈ BoxQuadraticModule n (r * n) := by
  -- Edge case: n = 0 (f is a constant > 0, trivially in QM)
  by_cases hn0 : n = 0
  · subst hn0
    have hf_const : ∃ c > 0, f = MvPolynomial.C c := by
      set c := legacyMvCoeff 0 f
      have hf_eq : f = MvPolynomial.C c := by
        ext m; rw [show m = 0 from Subsingleton.elim m 0]; simp [c, MvPolynomial.coeff_C]
      obtain ⟨x, hx⟩ := Hypercube_nonempty (n := 0)
      have hc_pos := hf_pos x hx; rw [hf_eq, MvPolynomial.eval_C] at hc_pos
      exact ⟨c, hc_pos, hf_eq⟩
    obtain ⟨c, hc_pos, hf_eq⟩ := hf_const
    rw [hf_eq]
    exact positive_const_in_BoxQuadraticModule hc_pos 0 _
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  -- Edge case: d = 0 (f is constant > 0)
  by_cases hd0 : d = 0
  · subst hd0
    set c := legacyMvCoeff 0 f
    have hf_eq : f = MvPolynomial.C c :=
      MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hd)
    have hc_pos : 0 < c := by
      obtain ⟨x, hx⟩ := Hypercube_nonempty (n := n)
      have := hf_pos x hx; rwa [hf_eq, MvPolynomial.eval_C] at this
    rw [hf_eq]
    exact positive_const_in_BoxQuadraticModule hc_pos n _
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
  have hd1 : 1 ≤ d := hd_pos
  -- Edge case: n = 1 (need n ≥ 2 for choose_q)
  by_cases hn2 : 2 ≤ n
  · -- Main case: n ≥ 2, d ≥ 1
    -- Step 1: Choose ε and get positivity extension
    set ε := epsilon_threshold f d with hε_def
    have ⟨hε_pos, hf_ext_pos⟩ := step1_positivity_extension f d hd1 hd hf_pos
    -- Step 2: Choose q and get scaled positivity
    set q := choose_q n ε with hq_def
    have hq1 : 1 ≤ q := one_le_choose_q hn2 ε hε_pos
    have hf_scaled_pos := step2_scaled_positivity f d ε hn2 hε_pos hf_ext_pos
    -- We need to choose r_schmudgen such that:
    -- (a) r_schmudgen + 2*q ≤ r (so degree fits)
    -- (b) π·d·√(2n) ≤ r_schmudgen
    -- (c) √(constC n d · (polyMax f - polyMin f) / eta n q) ≤ r_schmudgen
    -- The hypothesis hr ensures r is large enough for this decomposition.
    -- Step 3+4+5: Apply scaled_schmudgen, then degree shift
    -- We show r ≥ r_schmudgen + 2*q for r_schmudgen = r - 2*q, and check all bounds.
    -- Derive bounds on q from choose_q_bound
    have hq_bound : (q : ℝ) ≤ 4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f *
        Real.log ↑n + 1 :=
      choose_q_bound f d hd1 hn2 hf_pos
    -- Choose r_schmudgen: we need r ≥ r_schmudgen + 2*q and r_schmudgen large enough
    -- for steps 3's prerequisites (hr1 and hr2)
    -- The hypothesis hr ensures r is large enough.
    -- For the structural proof, we show the chain assuming sufficient bounds.
    -- r_schmudgen = r - 2*q (ensuring r ≥ 2*q from the bound on r)
    have h2q_le_r : 2 * q ≤ r :=
      two_mul_choose_q_le f d r hf_pos hr hn_pos hd_pos hd1 hn2 q hq_bound
    set r_s := r - 2 * q with hr_s_def
    have hr_decomp : r_s + 2 * q = r := by omega
    -- Step 3: Apply scaled_schmudgen
    have hr1_s : Real.pi * ↑d * Real.sqrt (2 * ↑n) ≤ ↑r_s :=
      schmudgen_hr1_bound f d r hf_pos hr hn_pos hd_pos hd1 hn2 q hq_bound h2q_le_r
    have hr2_s : Real.sqrt (constC n d * (polyMax (polyScale (eta n q) f) -
        polyMin (polyScale (eta n q) f)) / polyMin (polyScale (eta n q) f)) ≤ ↑r_s :=
      schmudgen_hr2_bound f d r hd hf_pos hr hn_pos hd_pos hd1 hn2 ε hε_pos hε_def q hq_def
        hq_bound h2q_le_r
    have hf_scaled : f ∈ ScaledBoxPreordering (eta n q) n ((r_s + 1) * n) :=
      step3_scaled_schmudgen f d hn2 hd1 hd q hq1 hf_scaled_pos r_s hr1_s hr2_s
    -- Step 4: Degree shift from ScaledBoxPreordering to BoxQuadraticModule
    have hf_box_qm : f ∈ BoxQuadraticModule n ((r_s + 1) * n + n * (2 * q - 2)) :=
      step4_degree_shift q hq1 hn_pos ((r_s + 1) * n) f hf_scaled
    -- Step 5: Bound total degree
    have h_degree_le : (r_s + 1) * n + n * (2 * q - 2) ≤ (r_s + 2 * q) * n :=
      step5_total_degree r_s q hq1
    -- Combine: (r_s + 2*q) * n = r * n
    have h_eq : (r_s + 2 * q) * n = r * n := by rw [hr_decomp]
    exact BoxQuadraticModule_mono (by omega : (r_s + 1) * n + n * (2 * q - 2) ≤ r * n) hf_box_qm
  · -- n = 1 case: n ≥ 1 (from hn_pos) and n < 2 (from ¬(2 ≤ n))
    push Not at hn2
    have hn1 : n = 1 := by omega
    subst hn1
    -- f > 0 on B^1 = [-1,1], use BoxPreordering ⊆ BoxQuadraticModule for n=1
    -- Since polyMin f > 0, f - C(polyMin f) is nonneg on B^1
    have hmin_pos : 0 < polyMin f := polyMin_pos_of_pos f hf_pos
    have hsup_pos : 0 < polySupNorm f := polySupNorm_pos_of_pos f hf_pos
    have h_nonneg : IsNonnegOn (f - MvPolynomial.C (polyMin f)) (Hypercube 1) := by
      intro x hx; simp only [map_sub, eval_C, sub_nonneg]
      exact polyMin_le_eval f x hx
    -- Ensure r ≥ 1 (from hr and positivity of constants)
    have hr_ge1 : 1 ≤ r := by
      by_contra h; push Not at h
      interval_cases r
      have : 0 < constUpperBound 1 d * ↑d ^ 2 * (Real.log (1 : ℝ) + 1) *
          polySupNorm f / polyMin f := by
        have hlog : Real.log (1 : ℝ) = 0 := Real.log_one
        rw [hlog, zero_add, mul_one]
        exact div_pos (mul_pos (mul_pos (constUpperBound_pos 1 d (by omega) hd_pos)
          (pow_pos (Nat.cast_pos.mpr hd_pos) 2)) hsup_pos) hmin_pos
      simp only [Nat.cast_zero] at hr
      linarith
    set r' := r - 1 with hr'_def
    have hr'_eq : r' + 1 = r := by omega
    -- Apply upperBoundMembershipBoxPreo to get f ∈ BoxPreordering 1 ((r'+1)*1)
    have h_in_box_preo : f ∈ BoxPreordering 1 ((r' + 1) * 1) := by
      -- Apply upperBoundMembershipBoxPreo to g = f - C(polyMin f) with η = polyMin f
      set g := f - MvPolynomial.C (polyMin f) with hg_def
      have hg_deg : g.totalDegree ≤ d :=
        le_trans (MvPolynomial.totalDegree_sub_C_le f _) hd
      -- upperBoundMembershipBoxPreo gives (g + C η) ∈ BoxPreordering, and g + C(polyMin f) = f
      have hg_add : g + MvPolynomial.C (polyMin f) = f := by
        simp [hg_def]
      rw [← hg_add]
      apply upperBoundMembershipBoxPreo g d r' (polyMin f) hg_deg hmin_pos h_nonneg
      · -- hr1: π * d * √(2 * 1) ≤ r'
        rw [Nat.cast_one, Real.log_one, zero_add, mul_one] at hr
        rw [show (2 : ℝ) * (↑(1 : ℕ) : ℝ) = 2 from by simp]
        rw [show (↑r' : ℝ) = ↑r - 1 from by
          rw [hr'_def]; simp [Nat.cast_sub hr_ge1]]
        -- Suffices: π * d * √2 + 1 ≤ r
        suffices h : Real.pi * ↑d * Real.sqrt 2 + 1 ≤ ↑r by linarith
        -- constUpperBound ≥ 26 (since constCChebyshev = exp 5 ≥ 6)
        have hcub_ge : (26 : ℝ) ≤ constUpperBound 1 d := by
          unfold constUpperBound; unfold constCChebyshev
          nlinarith [Real.add_one_le_exp (5 : ℝ), constC_pos 1 d (by omega) hd_pos]
        -- polySupNorm / polyMin ≥ 1
        have hSP := polyMin_le_polySupNorm f hf_pos
        -- r ≥ constUpperBound * d² * S/M ≥ 26 * d² * 1 = 26d²
        have hr_ge : (26 : ℝ) * ↑d ^ 2 ≤ ↑r := by
          have hcub_pos := constUpperBound_pos 1 d (by omega) hd_pos
          have hd2_pos : (0 : ℝ) < ↑d ^ 2 := pow_pos (Nat.cast_pos.mpr hd_pos) 2
          calc (26 : ℝ) * ↑d ^ 2
              ≤ constUpperBound 1 d * ↑d ^ 2 * 1 := by nlinarith
            _ ≤ constUpperBound 1 d * ↑d ^ 2 * (polySupNorm f / polyMin f) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                rw [le_div_iff₀ hmin_pos]; linarith
            _ = constUpperBound 1 d * ↑d ^ 2 * polySupNorm f / polyMin f := by ring
            _ ≤ ↑r := hr
        -- π * √2 < 8
        have hpi_sqrt2 : Real.pi * Real.sqrt 2 < 8 := by
          have : Real.sqrt 2 < 2 := by
            calc Real.sqrt 2 < Real.sqrt 4 :=
                  Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
              _ = 2 := by rw [show (4:ℝ) = 2^2 from by norm_num]; exact Real.sqrt_sq (by norm_num)
          nlinarith [Real.pi_lt_four, Real.pi_pos, Real.sqrt_nonneg (2:ℝ)]
        -- 8d + 1 ≤ 9d² ≤ 26d² ≤ r (for d ≥ 1)
        have hd_cast : (1 : ℝ) ≤ (↑d : ℝ) := by exact_mod_cast hd1
        nlinarith [sq_nonneg ((↑d : ℝ) - 1)]
      · -- hr2: √(constC 1 d * (polyMax g - polyMin g) / polyMin f) ≤ r'
        rw [Nat.cast_one, Real.log_one, zero_add, mul_one] at hr
        rw [hg_def, polyMax_sub_C, polyMin_sub_C]; simp only [sub_self]; rw [sub_zero]
        -- Bound: constC * (polyMax f - polyMin f) / polyMin f ≤ A := constC * supNorm / polyMin
        set A := constC 1 d * polySupNorm f / polyMin f with hA_def
        have hA_pos : 0 < A :=
          div_pos (mul_pos (constC_pos 1 d (by omega) hd_pos) hsup_pos) hmin_pos
        have hbound : constC 1 d * (polyMax f - polyMin f) / polyMin f ≤ A := by
          apply div_le_div_of_nonneg_right _ hmin_pos.le
          apply mul_le_mul_of_nonneg_left _ (constC_pos 1 d (by omega) hd_pos).le
          linarith [polyMax_le_polySupNorm f, polyMin_le_polyMax f]
        -- Suffices: √A ≤ r'
        suffices h : Real.sqrt A ≤ ↑r' from le_trans (Real.sqrt_le_sqrt hbound) h
        -- 4A ≤ r (from constUpperBound ≥ 4 * constC)
        have hcub_bound : 4 * constC 1 d ≤ constUpperBound 1 d := by
          unfold constUpperBound; unfold constCChebyshev
          nlinarith [Real.add_one_le_exp (5 : ℝ), constC_pos 1 d (by omega) hd_pos]
        have hSP := polyMin_le_polySupNorm f hf_pos
        have hcub_4A : 4 * A ≤ ↑r := by
          have hd2 : (1 : ℝ) ≤ (↑d : ℝ) ^ 2 := by
            have : (1 : ℝ) ≤ (↑d : ℝ) := by exact_mod_cast hd1
            nlinarith [sq_nonneg ((↑d : ℝ) - 1)]
          have hR : (1 : ℝ) ≤ polySupNorm f / polyMin f := by
            rw [le_div_iff₀ hmin_pos]; linarith
          have hR_nn : (0 : ℝ) ≤ polySupNorm f / polyMin f := div_nonneg hsup_pos.le hmin_pos.le
          have hd2_nn : (0 : ℝ) ≤ ↑d ^ 2 :=
            pow_nonneg (show (0 : ℝ) ≤ ↑d from Nat.cast_nonneg d) 2
          have hcC_nn : (0 : ℝ) ≤ 4 * constC 1 d :=
            mul_nonneg (by norm_num) (constC_pos 1 d (by omega) hd_pos).le
          calc 4 * A = 4 * constC 1 d * polySupNorm f / polyMin f := by rw [hA_def]; ring
            _ = 4 * constC 1 d * (1 * (polySupNorm f / polyMin f)) := by ring
            _ ≤ 4 * constC 1 d * (↑d ^ 2 * (polySupNorm f / polyMin f)) := by
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd2 hR_nn) hcC_nn
            _ ≤ constUpperBound 1 d * (↑d ^ 2 * (polySupNorm f / polyMin f)) := by
                exact mul_le_mul_of_nonneg_right hcub_bound (mul_nonneg hd2_nn hR_nn)
            _ = constUpperBound 1 d * ↑d ^ 2 * polySupNorm f / polyMin f := by ring
            _ ≤ ↑r := hr
        -- A ≥ 1 (constC ≥ 1 and S/M ≥ 1)
        have hA_ge1 : 1 ≤ A := by
          have hC_lb := constC_lower_bound 1 d (by omega) hd_pos
          -- constC 1 d ≥ 2*1*π²*d² ≥ 2π² > 1
          have hC_ge1 : (1 : ℝ) ≤ constC 1 d := by
            simp only [Nat.cast_one] at hC_lb
            have hd1r : (1 : ℝ) ≤ (↑d : ℝ) := by exact_mod_cast hd1
            nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3),
              sq_nonneg ((↑d : ℝ) - 1)]
          have hR_ge1 : (1 : ℝ) ≤ polySupNorm f / polyMin f := by
            rw [le_div_iff₀ hmin_pos]; linarith
          calc (1 : ℝ) ≤ constC 1 d * (polySupNorm f / polyMin f) := by
                nlinarith
            _ = A := by rw [hA_def]; ring
        -- √A ≤ A (for A ≥ 1): since A² ≥ A
        have hsqrt_le_A : Real.sqrt A ≤ A := by
          have : A ≤ A ^ 2 := by nlinarith
          calc Real.sqrt A ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt this
            _ = |A| := Real.sqrt_sq_eq_abs A
            _ = A := abs_of_pos hA_pos
        -- r' = r - 1 ≥ 4A - 1 ≥ 3A ≥ A ≥ √A
        have hr'_cast : (↑r' : ℝ) = ↑r - 1 := by
          rw [hr'_def]; simp [Nat.cast_sub hr_ge1]
        rw [hr'_cast]; linarith
    -- Convert BoxPreordering → BoxQuadraticModule for n=1
    have h_in_box_qm : f ∈ BoxQuadraticModule 1 ((r' + 1) * 1) :=
      BoxPreordering_subset_BoxQuadraticModule_one _ h_in_box_preo
    rw [hr'_eq] at h_in_box_qm
    exact h_in_box_qm

/-- Existential form of the simplified upper bound, corresponding to the
    qualitative statement in arXiv v3, Theorem 3. -/
theorem upper_degree_bound_weak_exists (f : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hn : 2 ≤ n) (hd1 : 1 ≤ d) :
    ∃ C > 0, ∀ r : ℕ,
      C * d ^ 2 * (Real.log (n : ℝ) + 1) * polySupNorm f / polyMin f ≤ r →
      f ∈ BoxQuadraticModule n (r * n) := by
  refine ⟨constUpperBound n d, constUpperBound_pos n d (by omega) (by omega), ?_⟩
  intro r hr
  exact upper_degree_bound_weak f d r hd hf_pos hr

/-! ## Corollaries -/

/-- The quadratic module certificate gives membership in the BoxPreordering as well,
    by the inclusion QM ⊆ T. -/
theorem upper_degree_bound_weak_box_preordering (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constUpperBound n d * d ^ 2 * (Real.log (n : ℝ) + 1) *
      polySupNorm f / polyMin f ≤ r) :
    f ∈ BoxPreordering n (r * n) :=
  BoxQuadraticModule_subset_BoxPreordering (upper_degree_bound_weak f d r hd hf_pos hr)

/-- Lasserre hierarchy convergence: for large enough r, the Lasserre bound
    on the quadratic module is nonneg (i.e. the feasible set is nonempty). -/
theorem lasserre_box_qm_convergence (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constUpperBound n d * d ^ 2 * (Real.log (n : ℝ) + 1) *
      polySupNorm f / polyMin f ≤ r) :
    (0 : ℝ) ≤ lasserre_bound_box_qm f (r * n) := by
  have hf_box_qm := upper_degree_bound_weak f d r hd hf_pos hr
  -- f - C(0) = f ∈ BoxQuadraticModule, so 0 is feasible
  have hfeas : (f - MvPolynomial.C 0) ∈ BoxQuadraticModule n (r * n) := by
    simp only [C_0, sub_zero]; exact hf_box_qm
  exact lasserre_bound_box_qm_ge_feasible f (r * n) hfeas

/-- The degree bound is polynomial in d, logarithmic in n, and linear in
    the condition number ‖f‖/f_min. This witnesses the qualitative content
    of arXiv v3, Theorem 3. -/
theorem degree_bound_qualitative (f : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hn : 2 ≤ n) (hd1 : 1 ≤ d) :
    ∃ (r : ℕ), f ∈ BoxQuadraticModule n (r * n) := by
  obtain ⟨C, hC, hbound⟩ := upper_degree_bound_weak_exists f d hd hf_pos hn hd1
  exact ⟨Nat.ceil (C * d ^ 2 * (Real.log (n : ℝ) + 1) * polySupNorm f / polyMin f) + 1,
    hbound _ (by
      have := Nat.le_ceil (C * d ^ 2 * (Real.log (n : ℝ) + 1) * polySupNorm f / polyMin f)
      push_cast; linarith)⟩

/-! ## Monotonicity of the degree bound -/

/-- Monotonicity: if the degree bound holds at level r, it holds at any r' ≥ r. -/
theorem upper_degree_bound_weak_mono (f : MvPolynomial (Fin n) ℝ) (d r r' : ℕ)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constUpperBound n d * d ^ 2 * (Real.log (n : ℝ) + 1) *
      polySupNorm f / polyMin f ≤ r)
    (hrr' : r ≤ r') :
    f ∈ BoxQuadraticModule n (r' * n) := by
  have : r * n ≤ r' * n := Nat.mul_le_mul_right n hrr'
  apply BoxQuadraticModule_mono this
  exact upper_degree_bound_weak f d r hd hf_pos hr

/-- For constant polynomials f = C(c) with c > 0, the degree bound is trivially
    satisfied at r = 0 since positive constants are already in QM at any level. -/
theorem upper_degree_bound_weak_const (c : ℝ) (hc : 0 < c) (r : ℕ) :
    MvPolynomial.C c ∈ BoxQuadraticModule n (r * n) :=
  BoxQuadraticModule_mono (Nat.zero_le _) (positive_const_in_BoxQuadraticModule hc n 0)

/-! ## ArXiv v3, Theorem 11: Two-term upper degree bound -/

set_option maxHeartbeats 1600000 in
-- The public upper bound assembles the constant-polynomial, one-variable, and multi-variable
-- cases, then invokes the Schmuedgen certificate and degree-shift machinery.
/-- **ArXiv v3, Theorem 11** (explicit form of Theorem 3):
    If f > 0 on B^n with degree ≤ d, then f ∈ QM(B^n)_{r·n} whenever
    r ≥ constLeading · d² · (log n + 1) · ‖f‖/f_min
        + max(π·d·√(2n), √(constSqrt · C(n,d) · ‖f‖/f_min)).

    The leading term has only the absolute constant constLeading = 8K+2.
    C(n,d) appears only under √ in the lower-order term. -/
theorem upper_degree_bound (f : MvPolynomial (Fin n) ℝ) (d r : ℕ)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x f)
    (hr : constLeading * d ^ 2 * (Real.log (n : ℝ) + 1) *
      polySupNorm f / polyMin f +
      max (Real.pi * d * Real.sqrt (2 * n))
          (Real.sqrt (constSqrt * constC n d * polySupNorm f / polyMin f))
      ≤ r) :
    f ∈ BoxQuadraticModule n (r * n) := by
  -- Edge case: n = 0
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨c, hc_pos, hf_eq⟩ : ∃ c > 0, f = MvPolynomial.C c := by
      set c := legacyMvCoeff 0 f
      have hf_eq : f = MvPolynomial.C c := by
        ext m; rw [show m = 0 from Subsingleton.elim m 0]; simp [c, MvPolynomial.coeff_C]
      obtain ⟨x, hx⟩ := Hypercube_nonempty (n := 0)
      have hc_pos : 0 < c := by
        have : 0 < MvPolynomial.eval x f := hf_pos x hx
        rw [hf_eq, MvPolynomial.eval_C] at this
        exact this
      exact ⟨c, hc_pos, hf_eq⟩
    rw [hf_eq]; exact positive_const_in_BoxQuadraticModule hc_pos 0 _
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  -- Edge case: d = 0
  by_cases hd0 : d = 0
  · subst hd0
    have hf_eq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hd)
    obtain ⟨x, hx⟩ := Hypercube_nonempty (n := n)
    rw [hf_eq]
    have heval := hf_pos x hx
    rw [hf_eq, MvPolynomial.eval_C] at heval
    exact positive_const_in_BoxQuadraticModule heval n _
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
  have hd1 : 1 ≤ d := hd_pos
  -- Common setup
  have hmin_pos := polyMin_pos_of_pos f hf_pos
  have hsup_pos := polySupNorm_pos_of_pos f hf_pos
  have hSP := polyMin_le_polySupNorm f hf_pos
  have hd_cast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hd2_ge1 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hR_ge1 := condition_number_ge_one f hf_pos
  have hconstC_pos := constC_pos n d hn_pos hd_pos
  -- n ≥ 2 vs n = 1
  by_cases hn2 : 2 ≤ n
  · -- Main case: n ≥ 2
    set ε := epsilon_threshold f d
    have ⟨hε_pos, hf_ext_pos⟩ := step1_positivity_extension f d hd1 hd hf_pos
    set q := choose_q n ε
    have hq1 : 1 ≤ q := one_le_choose_q hn2 ε hε_pos
    have hf_scaled_pos := step2_scaled_positivity f d ε hn2 hε_pos hf_ext_pos
    have hq_bound := choose_q_bound f d hd1 hn2 hf_pos
    have hlog_n_pos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    -- Key: 2q ≤ constLeading * d² * (log n + 1) * S/M
    have h2q_le_L : (2 * q : ℝ) ≤ constLeading * ↑d ^ 2 *
        (Real.log ↑n + 1) * polySupNorm f / polyMin f := by
      rw [le_div_iff₀ hmin_pos]
      have hq' : (↑q : ℝ) * polyMin f ≤
          4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f := by
        calc (↑q : ℝ) * polyMin f
            ≤ (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f / polyMin f *
              Real.log ↑n + 1) * polyMin f :=
              mul_le_mul_of_nonneg_right hq_bound hmin_pos.le
          _ = 4 * constCChebyshev * ↑d ^ 2 * polySupNorm f * Real.log ↑n + polyMin f := by
              field_simp
      have h_d2S_ge_M : polyMin f ≤ ↑d ^ 2 * polySupNorm f :=
        le_trans hSP (le_mul_of_one_le_left hsup_pos.le hd2_ge1)
      -- 2q*M ≤ 8K*d²*S*log(n) + 2M ≤ (8K+2)*d²*(log(n)+1)*S = constLeading*d²*(L+1)*S
      change 2 * ↑q * polyMin f ≤ constLeading * ↑d ^ 2 * (Real.log ↑n + 1) * polySupNorm f
      unfold constLeading
      nlinarith [constCChebyshev_pos,
        mul_nonneg
          (mul_nonneg
            (show (0 : ℝ) ≤ 8 * constCChebyshev by
              linarith [constCChebyshev_pos])
            (show (0 : ℝ) ≤ ↑d ^ 2 by positivity))
          hsup_pos.le,
        mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 2 * ↑d ^ 2 by positivity)
          (show (0:ℝ) ≤ Real.log ↑n by linarith)) hsup_pos.le]
    have h2q_le_r : 2 * q ≤ r := by
      suffices h : (2 * q : ℝ) ≤ (r : ℝ) by exact_mod_cast h
      have : 0 ≤ max (Real.pi * ↑d * Real.sqrt (2 * ↑n))
          (Real.sqrt (constSqrt * constC n d * polySupNorm f / polyMin f)) :=
        le_max_of_le_left (by positivity)
      linarith
    set r_s := r - 2 * q
    have hr_decomp : r_s + 2 * q = r := by omega
    have hr_s_cast : (r_s : ℝ) = (r : ℝ) - 2 * (q : ℝ) := by
      have : (r_s : ℝ) + 2 * (q : ℝ) = (r : ℝ) := by exact_mod_cast hr_decomp
      linarith
    -- r_s ≥ max(π·d·√(2n), √(constSqrt·C·S/M))
    have hr_s_ge_max : max (Real.pi * ↑d * Real.sqrt (2 * ↑n))
        (Real.sqrt (constSqrt * constC n d * polySupNorm f / polyMin f)) ≤ (r_s : ℝ) := by
      rw [hr_s_cast]; linarith
    -- hr1_s: trivial from max
    have hr1_s : Real.pi * ↑d * Real.sqrt (2 * ↑n) ≤ ↑r_s :=
      le_trans (le_max_left _ _) hr_s_ge_max
    -- hr2_s: bound the Schmüdgen argument, then use max
    have hr2_s : Real.sqrt (constC n d * (polyMax (polyScale (eta n q) f) -
        polyMin (polyScale (eta n q) f)) / polyMin (polyScale (eta n q) f)) ≤ ↑r_s := by
      set η := eta n q
      set g := polyScale η f
      have hη_pos : (0 : ℝ) < η := by
        change (0 : ℝ) < (n : ℝ).rpow ((1 : ℝ) / (2 * (q : ℝ)))
        exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
      have hη_le_eps : η ≤ 1 + ε := eta_le_one_add_eps hn2 ε hε_pos
      -- polyMin(g) ≥ M/2
      have hg_min_bound : polyMin f / 2 ≤ polyMin g := by
        apply le_csInf (Hypercube_image_nonempty g)
        rintro _ ⟨x, hx, rfl⟩
        change polyMin f / 2 ≤ MvPolynomial.eval x (polyScale η f)
        rw [polyScale_eval]
        have hscaled : (fun i => η * x i) ∈ ExtendedHypercube ε n := by
          apply ScaledHypercube_subset_ExtendedHypercube η ε hη_pos.le hη_le_eps
          rw [ScaledHypercube_mem_abs η hη_pos.le]
          intro i; have hi := (Hypercube_mem_iff x).mp hx i
          rw [abs_mul, abs_of_pos hη_pos]
          exact mul_le_of_le_one_right hη_pos.le (abs_le.mpr ⟨hi.1, hi.2⟩)
        exact choice_of_epsilon f d ε hd1 hd hf_pos hε_pos (le_refl _) _ hscaled
      -- spread(g) ≤ 4S
      have hg_spread : polyMax g - polyMin g ≤ 4 * polySupNorm f := by
        suffices hg_sup : polySupNorm g ≤ 2 * polySupNorm f by
          linarith [oscillation_le_two_supnorm g]
        unfold polySupNorm
        apply csSup_le (Set.image_nonempty.mpr Hypercube_nonempty)
        rintro _ ⟨x, hx, rfl⟩
        change |MvPolynomial.eval x (polyScale η f)| ≤ 2 * polySupNorm f
        rw [polyScale_eval]
        set y := (fun i => η * x i)
        have hy_ext : y ∈ ExtendedHypercube ε n := by
          apply ScaledHypercube_subset_ExtendedHypercube η ε hη_pos.le hη_le_eps
          rw [ScaledHypercube_mem_abs η hη_pos.le]
          intro i; have hi := (Hypercube_mem_iff x).mp hx i
          rw [abs_mul, abs_of_pos hη_pos]
          exact mul_le_of_le_one_right hη_pos.le (abs_le.mpr ⟨hi.1, hi.2⟩)
        have hε_le : ε ≤ 1 / (d : ℝ) ^ 2 := by
          calc ε ≤ polyMin f / (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f) := le_refl _
            _ ≤ polySupNorm f / (4 * constCChebyshev * ↑d ^ 2 * polySupNorm f) := by
                apply div_le_div_of_nonneg_right hSP
                have h4K := mul_pos (by norm_num : (0:ℝ) < 4) constCChebyshev_pos
                exact le_of_lt (mul_pos (mul_pos h4K
                  (pow_pos (Nat.cast_pos.mpr hd_pos) 2)) hsup_pos)
            _ = 1 / (4 * constCChebyshev * (d : ℝ) ^ 2) := by field_simp
            _ ≤ 1 / (d : ℝ) ^ 2 := by
                apply div_le_div_of_nonneg_left (by positivity) (by positivity)
                exact le_mul_of_one_le_left (by positivity) (by nlinarith [one_le_constCChebyshev])
        have hperturb := markov_perturbation_bound f d hd y ε hε_pos hε_le hy_ext
        have hε_bound : 2 * constCChebyshev * ↑d ^ 2 * ε * polySupNorm f ≤ polyMin f / 2 := by
          calc 2 * constCChebyshev * (d : ℝ) ^ 2 * ε * polySupNorm f
              ≤ 2 * constCChebyshev * (d : ℝ) ^ 2 *
                (polyMin f / (4 * constCChebyshev * (d : ℝ) ^ 2 * polySupNorm f)) *
                polySupNorm f := by
                apply mul_le_mul_of_nonneg_right _ hsup_pos.le
                exact mul_le_mul_of_nonneg_left (le_refl _)
                  (le_of_lt (mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) constCChebyshev_pos)
                    (pow_pos (Nat.cast_pos.mpr hd_pos) 2)))
            _ = polyMin f / 2 := by
                have hcC_ne : constCChebyshev ≠ 0 := ne_of_gt constCChebyshev_pos
                have hsup_ne : polySupNorm f ≠ 0 := ne_of_gt hsup_pos
                have hd2_ne : (d : ℝ) ^ 2 ≠ 0 := ne_of_gt (pow_pos (Nat.cast_pos.mpr hd_pos) 2)
                field_simp; ring
        have hperturb_le : |MvPolynomial.eval y f - MvPolynomial.eval (clampVec y) f| ≤
            polySupNorm f := le_trans hperturb (le_trans hε_bound (by linarith [hSP]))
        calc |MvPolynomial.eval y f|
            ≤ |MvPolynomial.eval (clampVec y) f| +
              |MvPolynomial.eval y f - MvPolynomial.eval (clampVec y) f| := by
                linarith [abs_sub_abs_le_abs_sub (MvPolynomial.eval y f)
                    (MvPolynomial.eval (clampVec y) f)]
          _ ≤ polySupNorm f + polySupNorm f :=
              add_le_add (polySupNorm_eval_le f _ le_rfl _ (clampVec_mem_Hypercube y)) hperturb_le
          _ = 2 * polySupNorm f := by ring
      -- arg ≤ constSqrt * constC * S / M
      have h_arg : constC n d * (polyMax g - polyMin g) / polyMin g ≤
          constSqrt * constC n d * polySupNorm f / polyMin f := by
        calc constC n d * (polyMax g - polyMin g) / polyMin g
            ≤ constC n d * (4 * polySupNorm f) / (polyMin f / 2) :=
              div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hg_spread hconstC_pos.le)
                (by linarith) hg_min_bound
          _ = 8 * constC n d * polySupNorm f / polyMin f := by field_simp; ring
          _ = constSqrt * constC n d * polySupNorm f / polyMin f := by unfold constSqrt; ring
      -- Chain: √(arg) ≤ √(constSqrt*C*S/M) ≤ max(...) ≤ r_s
      calc Real.sqrt (constC n d * (polyMax g - polyMin g) / polyMin g)
          ≤ Real.sqrt (constSqrt * constC n d * polySupNorm f / polyMin f) :=
            Real.sqrt_le_sqrt h_arg
        _ ≤ max (Real.pi * ↑d * Real.sqrt (2 * ↑n))
            (Real.sqrt (constSqrt * constC n d * polySupNorm f / polyMin f)) :=
            le_max_right _ _
        _ ≤ ↑r_s := hr_s_ge_max
    -- Combine: scaled_schmudgen + degree_shift
    have h_omega : (r_s + 1) * n + n * (2 * q - 2) ≤ r * n := by
      have h1 : 1 ≤ q := hq1
      have h2 : r_s + 2 * q = r := hr_decomp
      nlinarith [Nat.mul_le_mul_right n (show r_s + 1 + (2 * q - 2) ≤ r_s + 2 * q by omega)]
    exact BoxQuadraticModule_mono h_omega
      (step4_degree_shift q hq1 hn_pos _ f
        (step3_scaled_schmudgen f d hn2 hd1 hd q hq1 hf_scaled_pos r_s hr1_s hr2_s))
  · -- n = 1 case
    have hn1 : n = 1 := by omega
    subst hn1
    have h_nonneg : IsNonnegOn (f - MvPolynomial.C (polyMin f)) (Hypercube 1) := by
      intro x hx; simp only [map_sub, eval_C, sub_nonneg]; exact polyMin_le_eval f x hx
    -- Leading term ≥ 1
    have hL_ge1 : (1 : ℝ) ≤ constLeading * ↑d ^ 2 * (Real.log (1 : ℝ) + 1) *
        polySupNorm f / polyMin f := by
      rw [Real.log_one, zero_add, mul_one]
      calc (1 : ℝ) ≤ constLeading * 1 * 1 := by linarith [one_le_constLeading]
        _ ≤ constLeading * ↑d ^ 2 * (polySupNorm f / polyMin f) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hd2_ge1 constLeading_pos.le)
              hR_ge1 (by linarith [one_le_constLeading])
            exact mul_nonneg constLeading_pos.le (by positivity)
        _ = constLeading * ↑d ^ 2 * polySupNorm f / polyMin f := by ring
    have hr_ge1 : 1 ≤ r := by
      suffices (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast this
      have : 0 ≤ max (Real.pi * ↑d * Real.sqrt (2 * (1:ℝ)))
          (Real.sqrt (constSqrt * constC 1 d * polySupNorm f / polyMin f)) :=
        le_max_of_le_left (by positivity)
      linarith
    set r' := r - 1
    have hr'_eq : r' + 1 = r := by omega
    -- r' ≥ max(...)
    have hr'_cast : (↑r' : ℝ) = ↑r - 1 := by
      have h := hr'_eq  -- r' + 1 = r
      have : (r' : ℝ) + 1 = (r : ℝ) := by exact_mod_cast h
      linarith
    have hr'_ge_max : max (Real.pi * ↑d * Real.sqrt (2 * (1:ℝ)))
        (Real.sqrt (constSqrt * constC 1 d * polySupNorm f / polyMin f)) ≤ (r' : ℝ) := by
      rw [hr'_cast]; linarith [hL_ge1, hr]
    have h_in_box_preo : f ∈ BoxPreordering 1 ((r' + 1) * 1) := by
      set g := f - MvPolynomial.C (polyMin f)
      show f ∈ BoxPreordering 1 ((r' + 1) * 1)
      have : f = g + MvPolynomial.C (polyMin f) := by simp [g]
      rw [this]
      apply upperBoundMembershipBoxPreo g d r' (polyMin f)
        (le_trans (MvPolynomial.totalDegree_sub_C_le f _) hd) hmin_pos h_nonneg
      · -- hr1: π*d*√(2*1) ≤ r'
        show Real.pi * ↑d * Real.sqrt (2 * ↑(1 : ℕ)) ≤ ↑r'
        simp only [Nat.cast_one]
        exact le_trans (le_max_left _ _) hr'_ge_max
      · -- hr2: √(constC * spread / M) ≤ r'
        rw [polyMax_sub_C, polyMin_sub_C]; simp only [sub_self]; rw [sub_zero]
        calc Real.sqrt (constC 1 d * (polyMax f - polyMin f) / polyMin f)
            ≤ Real.sqrt (constSqrt * constC 1 d * polySupNorm f / polyMin f) := by
              apply Real.sqrt_le_sqrt
              apply div_le_div_of_nonneg_right _ hmin_pos.le
              calc constC 1 d * (polyMax f - polyMin f)
                  ≤ constC 1 d * polySupNorm f := by
                    apply mul_le_mul_of_nonneg_left _ hconstC_pos.le
                    linarith [polyMax_le_polySupNorm f, polyMin_le_polyMax f]
                _ ≤ constSqrt * constC 1 d * polySupNorm f := by
                    have : constC 1 d * polySupNorm f ≤
                        constSqrt * (constC 1 d * polySupNorm f) :=
                      le_mul_of_one_le_left (mul_nonneg hconstC_pos.le hsup_pos.le) one_le_constSqrt
                    linarith
          _ ≤ (r' : ℝ) := le_trans (le_max_right _ _) hr'_ge_max
    have : f ∈ BoxQuadraticModule 1 ((r' + 1) * 1) :=
      BoxPreordering_subset_BoxQuadraticModule_one _ h_in_box_preo
    exact BoxQuadraticModule_mono (by omega) this

end OptimalConvergenceRates

end
