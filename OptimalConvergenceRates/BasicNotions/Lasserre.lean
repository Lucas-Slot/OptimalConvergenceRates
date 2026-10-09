/-
  OptimalConvergenceRates/BasicNotions/Lasserre.lean

  Lasserre lower bounds for the box preordering and quadratic module, including feasibility monotonicity.
-/
import OptimalConvergenceRates.BasicNotions.BoxCones

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n N : ℕ}

/-! ## Lasserre bound -/

open Classical in
/-- The Lasserre lower bound f_{(r)} = sup{λ : f - C λ ∈ BoxPreo(B^n)_r}.
    Values in `WithBot ℝ` (= ℝ ∪ {-∞}) because for small r the feasible set
    {λ | f - C λ ∈ BoxPreo(B^n)_r} may be empty, in which case the supremum is -∞. -/
noncomputable def lasserre_bound_box_preo (f : MvPolynomial (Fin n) ℝ) (r : ℕ) : WithBot ℝ :=
  if _h : { l : ℝ | (f - MvPolynomial.C l) ∈ BoxPreordering n r }.Nonempty then
    ↑(sSup { l : ℝ | (f - MvPolynomial.C l) ∈ BoxPreordering n r })
  else ⊥

/-! ## Lasserre feasibility downward closure -/

/-- The feasible set of the Lasserre relaxation is downward closed.
    Proof idea: add (C(√(l₁-l₂)))² to the σ_∅ SOS component. -/
theorem lasserre_feasible_downward {r : ℕ} {f : MvPolynomial (Fin n) ℝ}
    {l₁ l₂ : ℝ} (hl : l₂ ≤ l₁) (h : (f - MvPolynomial.C l₁) ∈ BoxPreordering n r) :
    (f - MvPolynomial.C l₂) ∈ BoxPreordering n r := by
  -- f - C(l₂) = (f - C(l₁)) + C(l₁ - l₂)
  -- Add C(l₁ - l₂) = (C(√(l₁-l₂)))² (which is SOS) to the σ_∅ component
  obtain ⟨σ, hsos, hdeg, hsum⟩ := h
  set c := l₁ - l₂ with hc_def
  have hc : 0 ≤ c := sub_nonneg.mpr hl
  -- The extra square term: C(√c)²
  set extra := (MvPolynomial.C (Real.sqrt c)) ^ 2 with hextra_def
  -- New SOS certificates: update σ at ∅ by adding the extra square
  set σ' := Function.update σ ∅ (σ ∅ + extra) with hσ'_def
  -- The empty set is in univ.powerset
  have hempty_mem : (∅ : Finset (Fin n)) ∈ (Finset.univ : Finset (Fin n)).powerset :=
    Finset.mem_powerset.mpr (Finset.empty_subset _)
  refine ⟨σ', ?_, ?_, ?_⟩
  · -- Each σ' J is SOS
    intro J
    by_cases hJ : J = ∅
    · subst hJ
      rw [hσ'_def, Function.update_self, hextra_def]
      exact IsSOS_add_sq (hsos ∅) _
    · rw [hσ'_def, Function.update_of_ne hJ]
      exact hsos J
  · -- Degree bounds
    intro J
    by_cases hJ : J = ∅
    · subst hJ
      rw [hσ'_def, Function.update_self, BoxSemialgebraicGeneratorProd_empty]
      -- (σ ∅ + extra) * 1
      rw [mul_one]
      -- Specialize the degree bound at ∅
      have hdeg_empty := hdeg ∅
      rw [BoxSemialgebraicGeneratorProd_empty, mul_one] at hdeg_empty
      -- Need: (σ ∅ + extra).totalDegree ≤ r
      -- extra = C(√c) ^ 2 has degree 0
      calc (σ ∅ + extra).totalDegree
          ≤ max (σ ∅).totalDegree extra.totalDegree := MvPolynomial.totalDegree_add _ _
        _ ≤ max (σ ∅).totalDegree 0 := by
            apply max_le_max_left
            rw [hextra_def, sq, ← MvPolynomial.C_mul]
            exact le_of_eq (MvPolynomial.totalDegree_C _)
        _ = (σ ∅).totalDegree := max_eq_left (Nat.zero_le _)
        _ ≤ r := hdeg_empty
    · rw [hσ'_def, Function.update_of_ne hJ]
      exact hdeg J
  · -- Sum equals f - C(l₂)
    -- Split the sum at ∅ using Finset.add_sum_erase
    have key : ∀ J ∈ (Finset.univ.powerset.erase ∅), σ' J = σ J := by
      intro J hJ
      rw [hσ'_def, Function.update_of_ne (Finset.ne_of_mem_erase hJ)]
    -- f - C(l₂) = (f - C(l₁)) + C(l₁ - l₂) = (f - C(l₁)) + C(c)
    have arith : f - MvPolynomial.C l₂ = (f - MvPolynomial.C l₁) + MvPolynomial.C c := by
      simp only [hc_def, map_sub]; ring
    rw [arith, hsum]
    -- extra * BoxSemialgebraicGeneratorProd ∅ = C(c)
    have extra_eq :
        extra * BoxSemialgebraicGeneratorProd (∅ : Finset (Fin n)) = MvPolynomial.C c := by
      rw [BoxSemialgebraicGeneratorProd_empty, mul_one, hextra_def, sq, ← MvPolynomial.C_mul]
      congr 1
      exact Real.mul_self_sqrt hc
    -- The erased sum for σ' equals the erased sum for σ
    have erase_eq : ∑ x ∈ Finset.univ.powerset.erase ∅,
        σ' x * BoxSemialgebraicGeneratorProd x =
      ∑ x ∈ Finset.univ.powerset.erase ∅,
        σ x * BoxSemialgebraicGeneratorProd x := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [key J hJ]
    -- σ' ∅ = σ ∅ + extra
    have σ'_empty : σ' ∅ = σ ∅ + extra := by
      rw [hσ'_def, Function.update_self]
    -- Rewrite the target sum: split at ∅, substitute, and reassemble
    conv_rhs =>
      rw [← Finset.add_sum_erase _ _ hempty_mem]
    rw [σ'_empty, erase_eq, add_mul, extra_eq]
    conv_lhs => rw [← Finset.add_sum_erase _ _ hempty_mem]
    ring

/-! ## Lasserre bound properties -/

private theorem lasserre_feasible_upper_bound (f : MvPolynomial (Fin n) ℝ) (r : ℕ)
    {l : ℝ} (hl : (f - MvPolynomial.C l) ∈ BoxPreordering n r) :
    l ≤ polyMin f := by
  unfold polyMin
  apply le_csInf (Hypercube_image_nonempty f)
  rintro _ ⟨x, hx, rfl⟩
  have h := box_preordering_subset_nonneg hl x hx
  simp only [map_sub, MvPolynomial.eval_C] at h
  linarith

private theorem lasserre_feasible_bddAbove (f : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    BddAbove { l : ℝ | (f - MvPolynomial.C l) ∈ BoxPreordering n r } :=
  ⟨polyMin f, fun _l hl => lasserre_feasible_upper_bound f r hl⟩

theorem lasserre_bound_box_preo_le_polyMin (f : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    lasserre_bound_box_preo f r ≤ ↑(polyMin f) := by
  unfold lasserre_bound_box_preo
  split_ifs with hne
  · exact WithBot.coe_le_coe.mpr
      (csSup_le hne (fun l hl => lasserre_feasible_upper_bound f r hl))
  · exact bot_le

/-- If λ is feasible (f - C λ ∈ BoxPreo(B^n)_r), then ↑λ ≤ lasserre_bound_box_preo f r -/
theorem lasserre_bound_box_preo_ge_feasible (f : MvPolynomial (Fin n) ℝ) (r : ℕ)
    {l : ℝ} (hl : (f - MvPolynomial.C l) ∈ BoxPreordering n r) :
    ↑l ≤ lasserre_bound_box_preo f r := by
  unfold lasserre_bound_box_preo
  have hne : { l : ℝ | (f - MvPolynomial.C l) ∈ BoxPreordering n r }.Nonempty := ⟨l, hl⟩
  rw [dif_pos hne]
  exact WithBot.coe_le_coe.mpr (le_csSup (lasserre_feasible_bddAbove f r) hl)

theorem lasserre_bound_box_preo_mono (f : MvPolynomial (Fin n) ℝ) {r s : ℕ} (hrs : r ≤ s) :
    lasserre_bound_box_preo f r ≤ lasserre_bound_box_preo f s := by
  unfold lasserre_bound_box_preo
  split_ifs with hr hs
  · exact WithBot.coe_le_coe.mpr
      (csSup_le_csSup (lasserre_feasible_bddAbove f s) hr
        (fun l hl => box_preordering_mono hrs hl))
  · have : { l : ℝ | (f - MvPolynomial.C l) ∈ BoxPreordering n s }.Nonempty := by
      obtain ⟨l, hl⟩ := hr; exact ⟨l, box_preordering_mono hrs hl⟩
    exact absurd this hs
  · exact bot_le
  · exact le_refl _

theorem box_qm_feasible_downward {r : ℕ} {f : MvPolynomial (Fin n) ℝ}
    {l₁ l₂ : ℝ} (hl : l₂ ≤ l₁) (h : (f - MvPolynomial.C l₁) ∈ BoxQuadraticModule n r) :
    (f - MvPolynomial.C l₂) ∈ BoxQuadraticModule n r := by
  obtain ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩ := h
  set c := l₁ - l₂ with hc_def
  have hc : 0 ≤ c := sub_nonneg.mpr hl
  set extra := (MvPolynomial.C (Real.sqrt c)) ^ 2 with hextra_def
  refine ⟨σ₀ + extra, σ, ?_, hsos, ?_, hdeg, ?_⟩
  · exact IsSOS_add_sq hsos₀ _
  · calc (σ₀ + extra).totalDegree
        ≤ max σ₀.totalDegree extra.totalDegree := MvPolynomial.totalDegree_add _ _
      _ ≤ max σ₀.totalDegree 0 := by
          apply max_le_max_left
          rw [hextra_def, sq, ← MvPolynomial.C_mul]
          exact le_of_eq (MvPolynomial.totalDegree_C _)
      _ = σ₀.totalDegree := max_eq_left (Nat.zero_le _)
      _ ≤ r := hdeg₀
  · have arith : f - MvPolynomial.C l₂ = (f - MvPolynomial.C l₁) + MvPolynomial.C c := by
      simp only [hc_def, map_sub]; ring
    have extra_eq : extra = MvPolynomial.C c := by
      rw [hextra_def, sq, ← MvPolynomial.C_mul]; congr 1; exact Real.mul_self_sqrt hc
    rw [arith, hsum, extra_eq]; ring


/-! ## Lasserre bound (quadratic module version) -/

open Classical in
/-- The Lasserre lower bound using the quadratic module:
    f_{(r)}^{QM} = sup{λ : f - C λ ∈ QM(B^n)_r} -/
noncomputable def lasserre_bound_box_qm (f : MvPolynomial (Fin n) ℝ) (r : ℕ) : WithBot ℝ :=
  if _h : { l : ℝ | (f - MvPolynomial.C l) ∈ BoxQuadraticModule n r }.Nonempty then
    ↑(sSup { l : ℝ | (f - MvPolynomial.C l) ∈ BoxQuadraticModule n r })
  else ⊥

theorem lasserre_bound_box_qm_le (f : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    lasserre_bound_box_qm f r ≤ lasserre_bound_box_preo f r := by
  unfold lasserre_bound_box_qm lasserre_bound_box_preo
  split_ifs with hqm hp
  · exact WithBot.coe_le_coe.mpr
      (csSup_le_csSup (lasserre_feasible_bddAbove f r) hqm
        (fun l hl => BoxQuadraticModule_subset_BoxPreordering hl))
  · exfalso; apply hp
    obtain ⟨l, hl⟩ := hqm
    exact ⟨l, BoxQuadraticModule_subset_BoxPreordering hl⟩
  · exact bot_le
  · exact le_refl _

theorem lasserre_bound_box_qm_le_polyMin (f : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    lasserre_bound_box_qm f r ≤ ↑(polyMin f) :=
  le_trans (lasserre_bound_box_qm_le f r) (lasserre_bound_box_preo_le_polyMin f r)

theorem lasserre_bound_box_qm_ge_feasible (f : MvPolynomial (Fin n) ℝ) (r : ℕ)
    {l : ℝ} (hl : (f - MvPolynomial.C l) ∈ BoxQuadraticModule n r) :
    ↑l ≤ lasserre_bound_box_qm f r := by
  unfold lasserre_bound_box_qm
  have hne : { l : ℝ | (f - MvPolynomial.C l) ∈ BoxQuadraticModule n r }.Nonempty := ⟨l, hl⟩
  rw [dif_pos hne]
  exact WithBot.coe_le_coe.mpr
    (le_csSup
      (⟨polyMin f, fun _l hl' =>
        lasserre_feasible_upper_bound f r (BoxQuadraticModule_subset_BoxPreordering hl')⟩)
      hl)

theorem lasserre_bound_box_qm_mono (f : MvPolynomial (Fin n) ℝ) {r s : ℕ} (hrs : r ≤ s) :
    lasserre_bound_box_qm f r ≤ lasserre_bound_box_qm f s := by
  unfold lasserre_bound_box_qm
  split_ifs with hr hs
  · exact WithBot.coe_le_coe.mpr
      (csSup_le_csSup
        (⟨polyMin f, fun _l hl' =>
          lasserre_feasible_upper_bound f s (BoxQuadraticModule_subset_BoxPreordering hl')⟩)
        hr (fun l hl => BoxQuadraticModule_mono hrs hl))
  · exfalso; apply hs
    obtain ⟨l, hl⟩ := hr; exact ⟨l, BoxQuadraticModule_mono hrs hl⟩
  · exact bot_le
  · exact le_refl _

end OptimalConvergenceRates

end
