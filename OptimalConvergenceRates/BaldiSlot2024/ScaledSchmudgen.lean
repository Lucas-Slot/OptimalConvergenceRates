/-
  OptimalConvergenceRates/BaldiSlot2024/ScaledSchmudgen.lean

  Scaled-box Schmuedgen certificates on [-eta, eta]^n used in the Baldi-Slot upper bound.
-/
import OptimalConvergenceRates.SlotLaurent2022.MainResults
import OptimalConvergenceRates.BasicNotions.SumsOfSquares
import Mathlib.Algebra.MvPolynomial.Monad

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Scaled generators eta^2 - x_i^2 -/

/-- The i-th scaled generator g_i^eta(x) = C(eta^2) - X_i^2 -/
def ScaledBoxGenerator (η : ℝ) (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (η ^ 2) - (X i) ^ 2

/-- Product of scaled generators over a subset J -/
def ScaledBoxGeneratorProd (η : ℝ) (J : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∏ j ∈ J, ScaledBoxGenerator η j

theorem ScaledBoxGenerator_eval (η : ℝ) (i : Fin n) (x : Fin n → ℝ) :
    MvPolynomial.eval x (ScaledBoxGenerator η i) = η ^ 2 - (x i) ^ 2 := by
  simp [ScaledBoxGenerator, map_sub, MvPolynomial.eval_C, map_pow, eval_X]

theorem ScaledBoxGenerator_nonneg_on_ScaledHypercube (η : ℝ) (_hη : 0 ≤ η) (i : Fin n)
    (x : Fin n → ℝ) (hx : x ∈ ScaledHypercube η n) :
    0 ≤ MvPolynomial.eval x (ScaledBoxGenerator η i) := by
  rw [ScaledBoxGenerator_eval]
  have hi := ((ScaledHypercube_mem_iff η x).mp hx i)
  nlinarith [hi.1, hi.2, sq_abs (x i)]

theorem ScaledBoxGeneratorProd_nonneg_on_ScaledHypercube (η : ℝ) (hη : 0 ≤ η)
    (J : Finset (Fin n)) (x : Fin n → ℝ) (hx : x ∈ ScaledHypercube η n) :
    0 ≤ MvPolynomial.eval x (ScaledBoxGeneratorProd η J) := by
  unfold ScaledBoxGeneratorProd
  rw [map_prod]
  exact Finset.prod_nonneg (fun j _ => ScaledBoxGenerator_nonneg_on_ScaledHypercube η hη j x hx)

theorem ScaledBoxGeneratorProd_empty (η : ℝ) :
    ScaledBoxGeneratorProd η (∅ : Finset (Fin n)) = 1 := by
  unfold ScaledBoxGeneratorProd; exact Finset.prod_empty

theorem ScaledBoxGenerator_one (i : Fin n) :
    ScaledBoxGenerator 1 i = BoxSemialgebraicGenerator i := by
  simp [ScaledBoxGenerator, BoxSemialgebraicGenerator, one_pow, MvPolynomial.C_1]

/-! ## The scaled preordering T(eta^2 - x_1^2, ..., eta^2 - x_n^2)_r -/

/-- The truncated preordering with respect to scaled generators {eta^2 - x_i^2}.
    p is in the scaled preordering at level r iff
    p = sum_{J subseteq [n]} sigma_J * prod_{j in J} (C(eta^2) - X_j^2)
    with each sigma_J SOS and deg(sigma_J * g_J^eta) <= r. -/
def ScaledBoxPreordering (η : ℝ) (n : ℕ) (r : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  { p | ∃ (σ : Finset (Fin n) → MvPolynomial (Fin n) ℝ),
    (∀ J, IsSOS (σ J)) ∧
    (∀ J, (σ J * ScaledBoxGeneratorProd η J).totalDegree ≤ r) ∧
    p = ∑ J ∈ Finset.univ.powerset, σ J * ScaledBoxGeneratorProd η J }

private theorem ScaledBoxGeneratorProd_one (J : Finset (Fin n)) :
    ScaledBoxGeneratorProd 1 J = BoxSemialgebraicGeneratorProd J := by
  unfold ScaledBoxGeneratorProd BoxSemialgebraicGeneratorProd
  exact Finset.prod_congr rfl (fun j _ => ScaledBoxGenerator_one j)

theorem ScaledBoxPreordering_one : ScaledBoxPreordering 1 n r = BoxPreordering n r := by
  ext p
  unfold ScaledBoxPreordering BoxPreordering
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨σ, hsos, hdeg, hsum⟩
    refine ⟨σ, hsos, fun J => ?_, ?_⟩
    · rw [← ScaledBoxGeneratorProd_one J]; exact hdeg J
    · rw [hsum]; congr 1; ext J
      rw [ScaledBoxGeneratorProd_one]
  · rintro ⟨σ, hsos, hdeg, hsum⟩
    refine ⟨σ, hsos, fun J => ?_, ?_⟩
    · rw [ScaledBoxGeneratorProd_one]; exact hdeg J
    · rw [hsum]; congr 1; ext J
      rw [ScaledBoxGeneratorProd_one]

theorem ScaledBoxPreordering_subset_nonneg (η : ℝ) (hη : 0 ≤ η) :
    ScaledBoxPreordering η n r ⊆ { p | IsNonnegOn p (ScaledHypercube η n) } := by
  intro p ⟨σ, hsos, _, hsum⟩ x hx
  rw [hsum, map_sum]
  apply Finset.sum_nonneg
  intro J _
  rw [map_mul]
  exact mul_nonneg
    (IsSOS_nonneg _ (hsos J) x (Set.mem_univ _))
    (ScaledBoxGeneratorProd_nonneg_on_ScaledHypercube η hη J x hx)

theorem ScaledBoxPreordering_mono {η : ℝ} {r s : ℕ} (hrs : r ≤ s) :
    ScaledBoxPreordering η n r ⊆ ScaledBoxPreordering η n s := by
  intro p ⟨σ, hsos, hdeg, hsum⟩
  exact ⟨σ, hsos, fun J => le_trans (hdeg J) hrs, hsum⟩

/-! ## Scaling map infrastructure -/

/-- The polynomial scaling map: substitutes X_i ↦ C(c) * X_i.
    This sends a polynomial p(x) to p(c·x). -/
noncomputable def polyScale (c : ℝ) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C c * MvPolynomial.X i)

theorem polyScale_eval (c : ℝ) (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (polyScale c p) = MvPolynomial.eval (fun i => c * x i) p := by
  -- Both sides are AlgHom applications; use extensionality
  have : (MvPolynomial.aeval x).comp (polyScale c) =
      (MvPolynomial.aeval (fun i => c * x i) : MvPolynomial (Fin n) ℝ →ₐ[ℝ] ℝ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [polyScale, MvPolynomial.aeval_X, map_mul]
  have h := AlgHom.congr_fun this p
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] at h
  exact h

theorem polyScale_comp (a b : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    polyScale a (polyScale b p) = polyScale (b * a) p := by
  unfold polyScale
  show (aeval fun i => C a * X i)
         ((aeval fun i => C b * X i) p) =
       (aeval fun i => C (b * a) * X i) p
  have h := @MvPolynomial.bind₁_bind₁ (Fin n) (Fin n) ℝ _ (Fin n)
         (fun i => C b * X i) (fun i => C a * X i) p
  exact h.trans (by congr 1; ext i; simp [MvPolynomial.bind₁_X_right, MvPolynomial.C_mul'])

theorem polyScale_one (p : MvPolynomial (Fin n) ℝ) :
    polyScale 1 p = p := by
  unfold polyScale
  have : (fun i : Fin n => C (1 : ℝ) * X i) =
      (X : Fin n → MvPolynomial (Fin n) ℝ) := by
    ext i; simp [C_1]
  rw [this]
  simp [MvPolynomial.bind₁_X_left]

theorem polyScale_inv (c : ℝ) (hc : c ≠ 0) (p : MvPolynomial (Fin n) ℝ) :
    polyScale c⁻¹ (polyScale c p) = p := by
  rw [polyScale_comp, mul_inv_cancel₀ hc, polyScale_one]

theorem polyScale_inv' (c : ℝ) (hc : c ≠ 0) (p : MvPolynomial (Fin n) ℝ) :
    polyScale c (polyScale c⁻¹ p) = p := by
  rw [polyScale_comp, inv_mul_cancel₀ hc, polyScale_one]

/-- polyScale preserves the sum-of-squares property. -/
theorem polyScale_IsSOS (c : ℝ) {p : MvPolynomial (Fin n) ℝ} (hp : IsSOS p) :
    IsSOS (polyScale c p) := by
  obtain ⟨m, q, rfl⟩ := hp
  exact ⟨m, fun i => polyScale c (q i), by
    simp only [map_sum, map_pow]⟩

/-- polyScale preserves totalDegree (at most). -/
theorem polyScale_totalDegree_le (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    (polyScale c p).totalDegree ≤ p.totalDegree := by
  unfold polyScale
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro v hv
  rw [MvPolynomial.aeval_monomial]
  -- Need: totalDegree (C coeff * ∏ (C c * X i) ^ v i) ≤ totalDegree p
  -- Use smul: C coeff * prod = coeff • prod
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.C_mul']
  -- totalDegree (coeff • prod) ≤ totalDegree (prod) ≤ ∑ v i ≤ totalDegree p
  have hprod_deg : (Finsupp.prod v fun i k =>
      (MvPolynomial.C c * MvPolynomial.X i) ^ k).totalDegree ≤
      ∑ i ∈ v.support, v i := by
    change (∏ i ∈ v.support, (MvPolynomial.C c * MvPolynomial.X i) ^ v i).totalDegree ≤ _
    calc (∏ i ∈ v.support, (MvPolynomial.C c * MvPolynomial.X i) ^ v i).totalDegree
        ≤ ∑ i ∈ v.support, ((MvPolynomial.C c * MvPolynomial.X i) ^ v i).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ i ∈ v.support, v i := by
          apply Finset.sum_le_sum
          intro i _
          calc ((MvPolynomial.C c * MvPolynomial.X i) ^ v i).totalDegree
              ≤ v i * (MvPolynomial.C c * MvPolynomial.X i).totalDegree :=
                MvPolynomial.totalDegree_pow _ _
            _ ≤ v i * ((MvPolynomial.C c).totalDegree +
                  (MvPolynomial.X i : MvPolynomial (Fin n) ℝ).totalDegree) :=
                Nat.mul_le_mul_left _ (MvPolynomial.totalDegree_mul _ _)
            _ = v i * (0 + 1) := by
                rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
            _ = v i := by ring
  have hsum_eq : ∑ i ∈ v.support, v i = v.sum (fun _ e => e) := by simp [Finsupp.sum]
  calc (legacyMvCoeff v p • Finsupp.prod v fun i k =>
          (MvPolynomial.C c * MvPolynomial.X i) ^ k).totalDegree
      ≤ (Finsupp.prod v fun i k =>
          (MvPolynomial.C c * MvPolynomial.X i) ^ k).totalDegree :=
        MvPolynomial.totalDegree_smul_le _ _
    _ ≤ ∑ i ∈ v.support, v i := hprod_deg
    _ = v.sum (fun _ e => e) := hsum_eq
    _ ≤ p.totalDegree := Finset.le_sup (f := fun s => s.sum fun _ e => e) hv

/-- Scaling the standard generator: polyScale c⁻¹ (1 - X_i²) = C(c⁻²) · (C(c²) - X_i²). -/
theorem polyScale_inv_generator (c : ℝ) (hc : c ≠ 0) (i : Fin n) :
    polyScale c⁻¹ (BoxSemialgebraicGenerator i) =
      MvPolynomial.C (c⁻¹ ^ 2) * ScaledBoxGenerator c i := by
  unfold polyScale BoxSemialgebraicGenerator ScaledBoxGenerator
  simp only [map_sub, map_one, map_pow, MvPolynomial.aeval_X]
  -- Goal: 1 - (C c⁻¹ * X i)^2 = C(c⁻¹)^2 * (C(c^2) - X i^2)
  rw [mul_pow, mul_sub, ← MvPolynomial.C_pow, ← MvPolynomial.C_pow]
  -- Goal: 1 - C(c⁻¹^2) * (X i)^2 = C(c⁻¹^2) * C(c^2) - C(c⁻¹^2) * X i^2
  congr 1
  rw [← MvPolynomial.C_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hc), MvPolynomial.C_1]

/-- Scaling the standard generator product. -/
theorem polyScale_inv_generatorProd (c : ℝ) (hc : c ≠ 0) (J : Finset (Fin n)) :
    polyScale c⁻¹ (BoxSemialgebraicGeneratorProd J) =
      MvPolynomial.C (c⁻¹ ^ (2 * J.card)) * ScaledBoxGeneratorProd c J := by
  unfold BoxSemialgebraicGeneratorProd ScaledBoxGeneratorProd
  rw [map_prod]
  -- ∏ j ∈ J, polyScale c⁻¹ (BoxSemialgebraicGenerator j) =
  --   C(c⁻¹^(2*|J|)) * ∏ j ∈ J, ScaledBoxGenerator c j
  simp_rw [polyScale_inv_generator c hc]
  -- The product of the constant factors is C(c⁻¹^(2*|J|)); the remaining
  -- factors give the scaled generator product.
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, ← MvPolynomial.C_pow, ← pow_mul]

/-! ## ArXiv v3, Corollary 22: Scaled Schmüdgen theorem -/

/-- **ArXiv v3, Corollary 22** (scaled Schmüdgen): If f > 0 on [-η,η]^n with
    η > 0, then
    f ∈ T(η²-x₁²,...,η²-xₙ²)_{(r+1)n} for r sufficiently large.
    Proof by change of variables g(x) = f(η·x), applying `upperBoundMembershipBoxPreo`
    on B^n, and scaling back. -/
theorem scaled_schmudgen (f : MvPolynomial (Fin n) ℝ) (η : ℝ) (d r : ℕ)
    (hη : 0 < η)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x, (∀ i, |x i| ≤ η) → 0 < MvPolynomial.eval x f)
    (hr1 : Real.pi * d * Real.sqrt (2 * n) ≤ r)
    (hr2 : Real.sqrt (constC n d * (polyMax (polyScale η f) - polyMin (polyScale η f)) /
      polyMin (polyScale η f)) ≤ r) :
    ∃ (σ : Finset (Fin n) → MvPolynomial (Fin n) ℝ),
      (∀ J, IsSOS (σ J)) ∧
      (∀ J, (σ J * ∏ j ∈ J, (MvPolynomial.C (η ^ 2) - (X j) ^ 2)).totalDegree
        ≤ (r + 1) * n) ∧
      f = ∑ J ∈ Finset.univ.powerset,
        σ J * ∏ j ∈ J, (MvPolynomial.C (η ^ 2) - (X j) ^ 2) := by
  -- Step 0: Useful abbreviations and facts
  have hη_ne : η ≠ 0 := ne_of_gt hη
  have hη_inv_ne : η⁻¹ ≠ 0 := inv_ne_zero hη_ne
  -- Step 1: Define g(x) = f(η·x) via the scaling map
  set g := polyScale η f with hg_def
  -- Step 2: g is nonneg on B^n = [-1,1]^n
  have hg_nonneg : IsNonnegOn g (Hypercube n) := by
    intro x hx
    rw [hg_def, polyScale_eval]
    have hscaled : ∀ i, |η * x i| ≤ η := by
      intro i
      have hi := (Hypercube_mem_iff x).mp hx i
      rw [abs_mul, abs_of_pos hη]
      exact mul_le_of_le_one_right hη.le (abs_le.mpr ⟨hi.1, hi.2⟩)
    exact le_of_lt (hf_pos _ hscaled)
  -- Step 3: g has totalDegree ≤ d
  have hg_deg : g.totalDegree ≤ d :=
    le_trans (polyScale_totalDegree_le η f) hd
  -- Step 4: g is strictly positive on B^n (since f > 0 on [-η,η]^n and g(x) = f(η·x)).
  have hg_pos : ∀ x ∈ Hypercube n, 0 < MvPolynomial.eval x g := by
    intro x hx
    rw [hg_def, polyScale_eval]
    apply hf_pos
    intro i
    have hi := (Hypercube_mem_iff x).mp hx i
    rw [abs_mul, abs_of_pos hη]
    exact mul_le_of_le_one_right hη.le (abs_le.mpr ⟨hi.1, hi.2⟩)
  have hg_min_pos : 0 < polyMin g := by
    obtain ⟨x, hx, heval⟩ := polyMin_mem g
    rw [← heval]
    exact hg_pos x hx
  -- Step 5: Apply upperBoundMembershipBoxPreo to h = g - C(polyMin g) with η = polyMin g.
  -- Since h ≥ 0 on B^n and h + C(polyMin g) = g, this gives g ∈ BoxPreordering.
  -- The spread of h equals the spread of g (shifting by constant preserves spread),
  -- so hr2 (stated in terms of g) provides exactly the bound needed.
  have hg_box_preordering : g ∈ BoxPreordering n ((r + 1) * n) := by
    -- Write g = (g - C(polyMin g)) + C(polyMin g)
    -- Apply upperBoundMembershipBoxPreo to h := g - C(polyMin g), which is nonneg on B^n
    set h := g - MvPolynomial.C (polyMin g)
    have hg_eq : g = h + MvPolynomial.C (polyMin g) := by simp [h]
    rw [hg_eq]
    apply upperBoundMembershipBoxPreo h d r (polyMin g)
    · -- h.totalDegree ≤ d
      exact le_trans (MvPolynomial.totalDegree_sub_C_le g (polyMin g)) hg_deg
    · -- 0 < polyMin g
      exact hg_min_pos
    · -- IsNonnegOn h (Hypercube n)
      intro x hx
      simp only [h, map_sub, MvPolynomial.eval_C]
      exact sub_nonneg.mpr (polyMin_le_eval g x hx)
    · -- hr1: π · d · √(2n) ≤ r
      exact hr1
    · -- hr2 adapted: √(constC n d · (polyMax h - polyMin h) / polyMin g) ≤ r
      -- polyMax h - polyMin h = polyMax g - polyMin g (shifting by constant preserves spread)
      rw [polyMax_sub_polyMin_sub_C g (polyMin g)]
      -- Now the goal is √(constC n d · (polyMax g - polyMin g) / polyMin g) ≤ r
      -- which is exactly hr2 (after unfolding g = polyScale η f)
      exact hr2
  -- Step 6: Extract the BoxPreordering decomposition for g
  obtain ⟨τ, hτ_sos, hτ_deg, hτ_sum⟩ := hg_box_preordering
  -- Step 7: Scale back: apply polyScale η⁻¹ to the identity
  -- g = ∑_J τ_J * BoxSemialgebraicGeneratorProd J
  -- polyScale η⁻¹ g is the sum of the separately scaled certificate terms.
  -- But polyScale η⁻¹ g = polyScale η⁻¹ (polyScale η f) = f
  -- Each scaled generator product contributes C(η⁻²ᴶ) times the
  -- corresponding product at scale η.
  --
  -- So f = ∑_J (polyScale η⁻¹ τ_J) * C(η⁻²ᴶ) * ScaledBoxGeneratorProd η J
  --      = ∑_J [C(η⁻²ᴶ) * polyScale η⁻¹ τ_J] * ScaledBoxGeneratorProd η J
  --
  -- The SOS certificate is σ_J = C(η⁻²ᴶ) * polyScale η⁻¹ τ_J.
  -- This is SOS: polyScale η⁻¹ τ_J is SOS (scaling preserves SOS),
  -- and C(η⁻²ᴶ) * SOS is SOS since η⁻²ᴶ ≥ 0.

  -- Define the scaled SOS certificates
  set σ := fun J : Finset (Fin n) =>
    MvPolynomial.C (η⁻¹ ^ (2 * J.card)) * polyScale η⁻¹ (τ J) with hσ_def
  refine ⟨σ, ?_, ?_, ?_⟩
  · -- σ J is SOS for each J
    intro J
    rw [hσ_def]
    apply IsSOS_nonneg_scale (polyScale_IsSOS η⁻¹ (hτ_sos J))
    positivity
  · -- Degree bounds: (σ J * scaled_gen_prod J).totalDegree ≤ (r+1)*n
    intro J
    -- Bound via polyScale preserving degree
    calc (σ J * ScaledBoxGeneratorProd η J).totalDegree
        = (polyScale η⁻¹ (τ J * BoxSemialgebraicGeneratorProd J)).totalDegree := by
          congr 1
          have hmul : (polyScale η⁻¹) (τ J * BoxSemialgebraicGeneratorProd J) =
              (polyScale η⁻¹) (τ J) * (polyScale η⁻¹) (BoxSemialgebraicGeneratorProd J) :=
            map_mul _ _ _
          have hgen := polyScale_inv_generatorProd η hη_ne J
          rw [hmul, hgen, hσ_def]
          simp only [ScaledBoxGeneratorProd, ScaledBoxGenerator]
          ring
      _ ≤ (τ J * BoxSemialgebraicGeneratorProd J).totalDegree :=
          polyScale_totalDegree_le η⁻¹ _
      _ ≤ (r + 1) * n := hτ_deg J
  · -- f = ∑_J σ_J * ScaledBoxGeneratorProd η J
    -- Apply polyScale η⁻¹ to the equation g = ∑_J τ_J * BoxSemialgebraicGeneratorProd J
    have key : polyScale η⁻¹ g = f := by
      rw [hg_def, polyScale_inv η hη_ne f]
    -- polyScale η⁻¹ is a ring homomorphism, so it distributes over sums and products
    have scaled_eq : polyScale η⁻¹ g =
        ∑ J ∈ Finset.univ.powerset,
          polyScale η⁻¹ (τ J * BoxSemialgebraicGeneratorProd J) := by
      rw [hτ_sum]
      simp only [map_sum]
    rw [← key, scaled_eq]
    congr 1; ext J
    -- polyScale η⁻¹ (τ J * gen J) = (polyScale η⁻¹ τ J) * (polyScale η⁻¹ gen J)
    rw [map_mul]
    -- The scaled generator product contributes its constant factor C(η⁻²ᴶ).
    rw [polyScale_inv_generatorProd η hη_ne J]
    -- Now: polyScale η⁻¹ (τ J) * (C(...) * ScaledBoxGeneratorProd η J)
    --    = (∏ j ∈ J, ...) * σ J
    -- Unfold σ and rearrange
    simp only [hσ_def, ScaledBoxGeneratorProd, ScaledBoxGenerator]
    ring_nf

/-- The scaled Schmudgen theorem expressed as membership in the scaled preordering. -/
theorem scaled_schmudgen' (f : MvPolynomial (Fin n) ℝ) (η : ℝ) (d r : ℕ)
    (hη : 0 < η)
    (hd : f.totalDegree ≤ d)
    (hf_pos : ∀ x, (∀ i, |x i| ≤ η) → 0 < MvPolynomial.eval x f)
    (hr1 : Real.pi * d * Real.sqrt (2 * n) ≤ r)
    (hr2 : Real.sqrt (constC n d * (polyMax (polyScale η f) - polyMin (polyScale η f)) /
      polyMin (polyScale η f)) ≤ r) :
    f ∈ ScaledBoxPreordering η n ((r + 1) * n) := by
  obtain ⟨σ, hsos, hdeg, hsum⟩ := scaled_schmudgen f η d r hη hd hf_pos hr1 hr2
  exact ⟨σ, hsos, hdeg, hsum⟩

end OptimalConvergenceRates

end
