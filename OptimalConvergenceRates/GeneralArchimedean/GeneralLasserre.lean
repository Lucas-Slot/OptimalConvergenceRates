/-
  OptimalConvergenceRates/GeneralArchimedean/GeneralLasserre.lean

  Generalized quadratic-module Lasserre bounds on an Archimedean basic
  closed set.
-/
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanGeometry

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- Feasibility is downward closed at a fixed truncation order. -/
theorem genLasserre_feasible_downward
    {g : Fin m → MvPolynomial (Fin n) ℝ} {r : ℕ}
    {f : MvPolynomial (Fin n) ℝ} {l₁ l₂ : ℝ}
    (hl : l₂ ≤ l₁) (h : f - C l₁ ∈ GenQuadraticModule g r) :
    f - C l₂ ∈ GenQuadraticModule g r := by
  have hc : C (l₁ - l₂) ∈ GenQuadraticModule g 0 :=
    genQuadraticModule_C_nonneg g (sub_nonneg.mpr hl)
  have hadd := genQuadraticModule_add h hc
  simpa [Nat.max_eq_left (Nat.zero_le r), map_sub] using hadd

/-- A feasible scalar cannot exceed the true minimum. -/
theorem genLasserre_feasible_upper_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hK : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ) (r : ℕ)
    {l : ℝ} (hl : f - C l ∈ GenQuadraticModule g r) :
    l ≤ polynomialMinimum g f := by
  unfold polynomialMinimum
  apply le_csInf
  · exact hK.image _
  · rintro _ ⟨x, hx, rfl⟩
    have hnonneg := GenQuadraticModule.eval_nonneg hl x hx
    simp only [eval_sub, eval_C] at hnonneg
    linarith

/-- The feasible set is bounded above whenever the feasible set itself is nonempty. -/
theorem genLasserre_feasible_bddAbove
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hK : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    BddAbove {l : ℝ | f - C l ∈ GenQuadraticModule g r} :=
  ⟨polynomialMinimum g f,
    fun _ hl ↦ genLasserre_feasible_upper_bound hK harch f r hl⟩

/-- Every feasible scalar is below the generalized Lasserre bound. -/
theorem genLasserreBoundQM_ge_feasible
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hK : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ) (r : ℕ)
    {l : ℝ} (hl : f - C l ∈ GenQuadraticModule g r) :
    (l : WithBot ℝ) ≤ genLasserreBoundQM g f r := by
  unfold genLasserreBoundQM
  have hne : {l : ℝ | f - C l ∈ GenQuadraticModule g r}.Nonempty := ⟨l, hl⟩
  rw [dite_eq_left hne]
  exact WithBot.coe_le_coe.mpr
    (le_csSup (genLasserre_feasible_bddAbove hK harch f r) hl)

/-- The generalized Lasserre bound never exceeds the true minimum. -/
theorem genLasserreBoundQM_le_polynomialMinimum
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hK : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    genLasserreBoundQM g f r ≤ (polynomialMinimum g f : WithBot ℝ) := by
  unfold genLasserreBoundQM
  split_ifs with hne
  · exact WithBot.coe_le_coe.mpr
      (csSup_le hne fun l hl ↦ genLasserre_feasible_upper_bound hK harch f r hl)
  · exact bot_le

/-- Generalized Lasserre bounds are monotone in the truncation order. -/
theorem genLasserreBoundQM_mono
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hK : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ)
    {r s : ℕ} (hrs : r ≤ s) :
    genLasserreBoundQM g f r ≤ genLasserreBoundQM g f s := by
  unfold genLasserreBoundQM
  split_ifs with hr hs
  · exact WithBot.coe_le_coe.mpr
      (csSup_le_csSup (genLasserre_feasible_bddAbove hK harch f s) hr
        fun _ hl ↦ GenQuadraticModule_mono hrs hl)
  · exfalso
    apply hs
    obtain ⟨l, hl⟩ := hr
    exact ⟨l, GenQuadraticModule_mono hrs hl⟩
  · exact bot_le
  · exact le_rfl

/-- A certificate for the centered objective plus `ε` yields the expected hierarchy gap. -/
theorem genLasserreBoundQM_ge_of_centered_certificate
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hK : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ)
    (r : ℕ) {ε : ℝ}
    (hcert : f - C (polynomialMinimum g f) + C ε ∈ GenQuadraticModule g r) :
    (polynomialMinimum g f - ε : WithBot ℝ) ≤ genLasserreBoundQM g f r := by
  apply genLasserreBoundQM_ge_feasible hK harch f r
  convert hcert using 1
  simp only [map_sub]
  ring

/-- A uniform centered-certificate rate immediately gives a Lasserre-error rate. -/
theorem lasserre_rate_of_centered_certificate
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hK : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g) (f : MvPolynomial (Fin n) ℝ)
    (C₀ : ℝ) (r₀ : ℕ)
    (hcert : ∀ r, r₀ ≤ r →
      f - C (polynomialMinimum g f) + C (C₀ * logFourOverSq r) ∈
        GenQuadraticModule g r) :
    ∀ r, r₀ ≤ r →
      (polynomialMinimum g f - C₀ * logFourOverSq r : WithBot ℝ) ≤
          genLasserreBoundQM g f r ∧
        genLasserreBoundQM g f r ≤ (polynomialMinimum g f : WithBot ℝ) := by
  intro r hr
  exact ⟨genLasserreBoundQM_ge_of_centered_certificate hK harch f r (hcert r hr),
    genLasserreBoundQM_le_polynomialMinimum hK harch f r⟩

end OptimalConvergenceRates.GeneralArchimedean

end
