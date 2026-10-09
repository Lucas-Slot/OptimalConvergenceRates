/-
  Generalized Schmüdgen hierarchy bounds on compact basic closed sets.
-/
import OptimalConvergenceRates.GeneralCompact.UpperBound

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralCompact

variable {n m : ℕ}

/-- Feasibility is downward closed at a fixed preordering truncation. -/
theorem genLasserrePO_feasible_downward
    {g : Fin m → MvPolynomial (Fin n) ℝ} {r : ℕ}
    {f : MvPolynomial (Fin n) ℝ} {l₁ l₂ : ℝ}
    (hl : l₂ ≤ l₁) (h : f - C l₁ ∈ GenPreordering g r) :
    f - C l₂ ∈ GenPreordering g r := by
  have hc : C (l₁ - l₂) ∈ GenPreordering g 0 :=
    KrivineStengle.genPreordering_C_nonneg g (sub_nonneg.mpr hl)
  have hc' : C (l₁ - l₂) ∈ GenPreordering g r :=
    GenPreordering_mono (Nat.zero_le _) hc
  have hadd := KrivineStengle.genPreordering_add h hc'
  have hadd' : f - C l₁ + C (l₁ - l₂) ∈ GenPreordering g r := by
    simpa using hadd
  convert hadd' using 1
  simp only [map_sub]
  ring

/-- A feasible scalar cannot exceed the true compact minimum. -/
theorem genLasserrePO_feasible_upper_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ)
    {l : ℝ} (hl : f - C l ∈ GenPreordering g r) :
    l ≤ GeneralArchimedean.polynomialMinimum g f := by
  obtain ⟨x, hx, hxmin⟩ :=
    polynomialMinimum_mem_of_compact hne hcompact f
  have hnonneg :=
    (show KrivineStengle.PreorderingMem g (f - C l) from ⟨r, hl⟩).nonnegOn x hx
  simp only [eval_sub, eval_C] at hnonneg
  rw [hxmin] at hnonneg
  linarith

/-- The feasible scalar set is bounded above. -/
theorem genLasserrePO_feasible_bddAbove
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    BddAbove {l : ℝ | f - C l ∈ GenPreordering g r} :=
  ⟨GeneralArchimedean.polynomialMinimum g f,
    fun _ hl ↦ genLasserrePO_feasible_upper_bound hne hcompact f r hl⟩

/-- Every feasible scalar lies below the generalized Schmüdgen bound. -/
theorem genLasserreBoundPO_ge_feasible
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ)
    {l : ℝ} (hl : f - C l ∈ GenPreordering g r) :
    (l : WithBot ℝ) ≤ genLasserreBoundPO g f r := by
  unfold genLasserreBoundPO
  have hset : {l : ℝ | f - C l ∈ GenPreordering g r}.Nonempty := ⟨l, hl⟩
  rw [dif_pos hset]
  exact WithBot.coe_le_coe.mpr
    (le_csSup (genLasserrePO_feasible_bddAbove hne hcompact f r) hl)

/-- The generalized Schmüdgen bound never exceeds the true minimum. -/
theorem genLasserreBoundPO_le_polynomialMinimum
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    genLasserreBoundPO g f r ≤
      (GeneralArchimedean.polynomialMinimum g f : WithBot ℝ) := by
  unfold genLasserreBoundPO
  split_ifs with hset
  · exact WithBot.coe_le_coe.mpr
      (csSup_le hset fun l hl ↦
        genLasserrePO_feasible_upper_bound hne hcompact f r hl)
  · exact bot_le

/-- Generalized Schmüdgen bounds are monotone in the truncation order. -/
theorem genLasserreBoundPO_mono
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) {r s : ℕ} (hrs : r ≤ s) :
    genLasserreBoundPO g f r ≤ genLasserreBoundPO g f s := by
  unfold genLasserreBoundPO
  split_ifs with hr hs
  · exact WithBot.coe_le_coe.mpr
      (csSup_le_csSup (genLasserrePO_feasible_bddAbove hne hcompact f s) hr
        fun _ hl ↦ GenPreordering_mono hrs hl)
  · exfalso
    apply hs
    obtain ⟨l, hl⟩ := hr
    exact ⟨l, GenPreordering_mono hrs hl⟩
  · exact bot_le
  · exact le_rfl

/-- A centered certificate yields the expected hierarchy-gap bound. -/
theorem genLasserreBoundPO_ge_of_centered_certificate
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) {epsilon : ℝ}
    (hcert : f - C (GeneralArchimedean.polynomialMinimum g f) + C epsilon ∈
      GenPreordering g r) :
    (GeneralArchimedean.polynomialMinimum g f - epsilon : WithBot ℝ) ≤
      genLasserreBoundPO g f r := by
  apply genLasserreBoundPO_ge_feasible hne hcompact f r
  convert hcert using 1
  simp only [map_sub]
  ring

/-- A uniform centered-certificate rate gives the hierarchy-error rate. -/
theorem lasserrePO_rate_of_centered_certificate
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (hcompact : IsCompact (KrivineStengle.basicClosedSet g))
    (f : MvPolynomial (Fin n) ℝ) (C₀ : ℝ) (r₀ : ℕ)
    (hcert : ∀ r, r₀ ≤ r →
      f - C (GeneralArchimedean.polynomialMinimum g f) +
          C (C₀ * logTwoOverSq r) ∈ GenPreordering g r) :
    ∀ r, r₀ ≤ r →
      (GeneralArchimedean.polynomialMinimum g f - C₀ * logTwoOverSq r :
          WithBot ℝ) ≤ genLasserreBoundPO g f r ∧
        genLasserreBoundPO g f r ≤
          (GeneralArchimedean.polynomialMinimum g f : WithBot ℝ) := by
  intro r hr
  exact ⟨genLasserreBoundPO_ge_of_centered_certificate hne hcompact f r
      (hcert r hr),
    genLasserreBoundPO_le_polynomialMinimum hne hcompact f r⟩

end OptimalConvergenceRates.GeneralCompact

end
