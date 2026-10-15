/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Hierarchy.lean

  Feasible sets and lower bounds for the sphere SOS hierarchy.

  Empty feasible sets are represented by `⊥`, matching the repository's other Lasserre
  hierarchies.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Defs

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

variable {n : ℕ}

/-- Feasible lower bounds at sphere SOS root degree `r`. -/
def sphereSOSFeasible (f : MvPolynomial (Fin n) ℝ) (r : ℕ) : Set ℝ :=
  {l | SphereSOSMod (f - MvPolynomial.C l) r}

open Classical in
/-- The sphere SOS lower bound, with `⊥` representing an empty feasible set. -/
def sphereSOSBound (f : MvPolynomial (Fin n) ℝ) (r : ℕ) : WithBot ℝ :=
  if _h : (sphereSOSFeasible f r).Nonempty then ↑(sSup (sphereSOSFeasible f r)) else ⊥

/-- Sphere SOS feasibility is downward closed. -/
theorem sphereSOSFeasible_downward {f : MvPolynomial (Fin n) ℝ} {r : ℕ} {l₁ l₂ : ℝ}
    (hl : l₂ ≤ l₁) (hcert : l₁ ∈ sphereSOSFeasible f r) :
    l₂ ∈ sphereSOSFeasible f r := by
  have hc : 0 ≤ l₁ - l₂ := sub_nonneg.mpr hl
  change SphereSOSMod (f - MvPolynomial.C l₁) r at hcert
  have hconst : SphereSOSMod (MvPolynomial.C (l₁ - l₂) : MvPolynomial (Fin n) ℝ) r :=
    sphereSOSMod_const hc
  have hadd := hcert.add hconst
  change SphereSOSMod (f - MvPolynomial.C l₂) r
  convert hadd using 1
  simp only [map_sub]
  ring

/-- Adding a constant to the objective translates every feasible lower bound by that
constant. -/
theorem sphereSOSFeasible_add_const_iff (f : MvPolynomial (Fin n) ℝ) (r : ℕ)
    (c l : ℝ) :
    l ∈ sphereSOSFeasible (f + MvPolynomial.C c) r ↔
      l - c ∈ sphereSOSFeasible f r := by
  change SphereSOSMod ((f + MvPolynomial.C c) - MvPolynomial.C l) r ↔
    SphereSOSMod (f - MvPolynomial.C (l - c)) r
  simp only [map_sub]
  have heq : f + MvPolynomial.C c - MvPolynomial.C l =
      f - (MvPolynomial.C l - MvPolynomial.C c) := by ring
  rw [heq]

/-- Feasibility is nonempty after adding a constant exactly when it was nonempty before. -/
theorem sphereSOSFeasible_add_const_nonempty_iff (f : MvPolynomial (Fin n) ℝ)
    (r : ℕ) (c : ℝ) :
    (sphereSOSFeasible (f + MvPolynomial.C c) r).Nonempty ↔
      (sphereSOSFeasible f r).Nonempty := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l - c, (sphereSOSFeasible_add_const_iff f r c l).mp hl⟩
  · rintro ⟨l, hl⟩
    refine ⟨l + c, ?_⟩
    rw [sphereSOSFeasible_add_const_iff]
    simpa using hl


/-- Every feasible sphere lower bound lies below the infimum of the sphere values. -/
theorem sphereSOSFeasible_le_spherePolyMin (hne : (sphereSet n).Nonempty)
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) {l : ℝ} (hl : l ∈ sphereSOSFeasible f r) :
    l ≤ spherePolyMin f := by
  unfold spherePolyMin
  apply le_csInf
  · obtain ⟨x, hx⟩ := hne
    exact ⟨MvPolynomial.eval x f, x, hx, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    have hnonneg := hl.nonnegOnSphere hx
    simp only [map_sub, eval_C] at hnonneg
    linarith

/-- The feasible set is bounded above whenever the sphere is nonempty. -/
theorem sphereSOSFeasible_bddAbove (hne : (sphereSet n).Nonempty)
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) : BddAbove (sphereSOSFeasible f r) :=
  ⟨spherePolyMin f, fun _ hl ↦ sphereSOSFeasible_le_spherePolyMin hne f r hl⟩

/-- The real supremum of a nonempty feasible set translates with the objective. -/
theorem sphereSOSFeasible_sSup_add_const (hne : (sphereSet n).Nonempty)
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) (c : ℝ)
    (hfeas : (sphereSOSFeasible f r).Nonempty) :
    sSup (sphereSOSFeasible (f + MvPolynomial.C c) r) =
      sSup (sphereSOSFeasible f r) + c := by
  have hnew : (sphereSOSFeasible (f + MvPolynomial.C c) r).Nonempty :=
    (sphereSOSFeasible_add_const_nonempty_iff f r c).mpr hfeas
  apply le_antisymm
  · apply csSup_le hnew
    intro l hl
    have hle := le_csSup (sphereSOSFeasible_bddAbove hne f r)
      ((sphereSOSFeasible_add_const_iff f r c l).mp hl)
    linarith
  · have haux :
        sSup (sphereSOSFeasible f r) ≤
          sSup (sphereSOSFeasible (f + MvPolynomial.C c) r) - c := by
      apply csSup_le hfeas
      intro l hl
      have hmem : l + c ∈ sphereSOSFeasible (f + MvPolynomial.C c) r := by
        rw [sphereSOSFeasible_add_const_iff]
        simpa using hl
      have hle := le_csSup
        (sphereSOSFeasible_bddAbove hne (f + MvPolynomial.C c) r) hmem
      linarith
    linarith

/-- The hierarchy bound translates exactly when a constant is added to the objective,
including the empty-feasible-set case. -/
theorem sphereSOSBound_add_const (hne : (sphereSet n).Nonempty)
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) (c : ℝ) :
    sphereSOSBound (f + MvPolynomial.C c) r =
      sphereSOSBound f r + (c : WithBot ℝ) := by
  by_cases hold : (sphereSOSFeasible f r).Nonempty
  · have hnew : (sphereSOSFeasible (f + MvPolynomial.C c) r).Nonempty :=
      (sphereSOSFeasible_add_const_nonempty_iff f r c).mpr hold
    rw [sphereSOSBound, dite_eq_left hnew, sphereSOSBound, dite_eq_left hold]
    norm_cast
    exact sphereSOSFeasible_sSup_add_const hne f r c hold
  · have hnew : ¬(sphereSOSFeasible (f + MvPolynomial.C c) r).Nonempty := by
      intro h
      exact hold ((sphereSOSFeasible_add_const_nonempty_iff f r c).mp h)
    rw [sphereSOSBound, dite_eq_right hnew, sphereSOSBound, dite_eq_right hold]
    simp


/-- The sphere SOS hierarchy is a lower bound on the true sphere infimum. -/
theorem sphereSOSBound_le_spherePolyMin (hne : (sphereSet n).Nonempty)
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    sphereSOSBound f r ≤ ↑(spherePolyMin f) := by
  unfold sphereSOSBound
  split_ifs with h
  · exact WithBot.coe_le_coe.mpr
      (csSup_le h fun l hl ↦ sphereSOSFeasible_le_spherePolyMin hne f r hl)
  · exact bot_le

/-- Every feasible value is below the hierarchy bound. -/
theorem sphereSOSBound_ge_feasible (hne : (sphereSet n).Nonempty)
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) {l : ℝ} (hl : l ∈ sphereSOSFeasible f r) :
    (l : WithBot ℝ) ≤ sphereSOSBound f r := by
  unfold sphereSOSBound
  have hnonempty : (sphereSOSFeasible f r).Nonempty := ⟨l, hl⟩
  rw [dite_eq_left hnonempty]
  exact WithBot.coe_le_coe.mpr (le_csSup (sphereSOSFeasible_bddAbove hne f r) hl)

/-- The sphere SOS lower bound is monotone in its root-degree order. -/
theorem sphereSOSBound_mono (hne : (sphereSet n).Nonempty) (f : MvPolynomial (Fin n) ℝ)
    {r s : ℕ} (hrs : r ≤ s) : sphereSOSBound f r ≤ sphereSOSBound f s := by
  unfold sphereSOSBound
  split_ifs with hr hs
  · exact WithBot.coe_le_coe.mpr
      (csSup_le_csSup (sphereSOSFeasible_bddAbove hne f s) hr fun _ hl ↦ hl.mono hrs)
  · exfalso
    apply hs
    obtain ⟨l, hl⟩ := hr
    exact ⟨l, hl.mono hrs⟩
  · exact bot_le
  · exact le_refl _


/-- An exact certificate for a centered polynomial gives an explicit error bound for the
actual feasible-set supremum. -/
theorem sphereSOSBound_error_of_certificate (hne : (sphereSet n).Nonempty)
    (f : MvPolynomial (Fin n) ℝ) (r : ℕ) (epsilon : ℝ)
    (hcert : SphereSOSMod
      (f - MvPolynomial.C (spherePolyMin f) + MvPolynomial.C epsilon) r) :
    ∃ b : ℝ,
      sphereSOSBound f r = (b : WithBot ℝ) ∧
      0 ≤ spherePolyMin f - b ∧ spherePolyMin f - b ≤ epsilon := by
  have hfeasible : spherePolyMin f - epsilon ∈ sphereSOSFeasible f r := by
    change SphereSOSMod (f - MvPolynomial.C (spherePolyMin f - epsilon)) r
    convert hcert using 1
    simp only [map_sub]
    ring
  have hnonempty : (sphereSOSFeasible f r).Nonempty := ⟨_, hfeasible⟩
  let b := sSup (sphereSOSFeasible f r)
  have hbound : sphereSOSBound f r = (b : WithBot ℝ) := by
    simp only [sphereSOSBound, dite_eq_left hnonempty, b]
  have hlower := sphereSOSBound_ge_feasible hne f r hfeasible
  have hupper := sphereSOSBound_le_spherePolyMin hne f r
  rw [hbound, WithBot.coe_le_coe] at hlower hupper
  exact ⟨b, hbound, sub_nonneg.mpr hupper, by linarith⟩
end QuarticConvergence
end OptimalConvergenceRates

end
