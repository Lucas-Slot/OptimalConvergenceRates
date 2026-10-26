import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-!
The equality-constrained hierarchy on the full unit sphere, with explicit
bounds on square-root and equality-multiplier degrees. `Compatibility`
identifies this internal convention with the repository's `SphereSOSMod`.
-/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

abbrev Polynomial (n : ℕ) := MvPolynomial (Fin n) ℝ

def radiusPolynomial (n : ℕ) : Polynomial n :=
  ∑ i : Fin n, MvPolynomial.X i ^ 2

def unitSphere (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∑ i : Fin n, x i ^ 2 = 1}

/-- Order r permits square roots of degree at most r. -/
def Feasible {n : ℕ} (r : ℕ) (p : Polynomial n) (lam : ℝ) : Prop :=
  ∃ (m : ℕ) (h : Fin m → Polynomial n) (g : Polynomial n),
    (∀ j, (h j).totalDegree ≤ r) ∧
    g.totalDegree ≤ 2 * r - 2 ∧
    p - MvPolynomial.C lam =
      (∑ j : Fin m, h j ^ 2) + (1 - radiusPolynomial n) * g

def feasibleValues {n : ℕ} (r : ℕ) (p : Polynomial n) : Set ℝ :=
  {lam | Feasible r p lam}

def sos {n : ℕ} (r : ℕ) (p : Polynomial n) : ℝ :=
  sSup (feasibleValues r p)

def sphereValues {n : ℕ} (p : Polynomial n) : Set ℝ :=
  {v | ∃ x ∈ unitSphere n, MvPolynomial.eval x p = v}

def sphereMinimum {n : ℕ} (p : Polynomial n) : ℝ :=
  sInf (sphereValues p)

def sphereSupNorm {n : ℕ} (p : Polynomial n) : ℝ :=
  sSup {v | ∃ x ∈ unitSphere n, |MvPolynomial.eval x p| = v}

def gap {n : ℕ} (r : ℕ) (p : Polynomial n) : ℝ :=
  sphereMinimum p - sos r p

/-- An attained sphere minimum, used to justify the real infimum. -/
def IsSphereMinimum {n : ℕ} (p : Polynomial n) (μ : ℝ) : Prop :=
  (∀ x ∈ unitSphere n, μ ≤ MvPolynomial.eval x p) ∧
    ∃ x ∈ unitSphere n, MvPolynomial.eval x p = μ

@[simp] theorem radiusPolynomial_eval {n : ℕ} (x : Fin n → ℝ) :
    MvPolynomial.eval x (radiusPolynomial n) = ∑ i : Fin n, x i ^ 2 := by
  simp [radiusPolynomial]

theorem feasible_sound {n r : ℕ} {p : Polynomial n} {lam : ℝ}
    (hlam : Feasible r p lam) {x : Fin n → ℝ} (hx : x ∈ unitSphere n) :
    lam ≤ MvPolynomial.eval x p := by
  classical
  rcases hlam with ⟨m, h, g, _hdeg, _hgdeg, hid⟩
  have hrad : MvPolynomial.eval x (radiusPolynomial n) = 1 := by
    simpa [unitSphere] using hx
  have heval := congrArg (MvPolynomial.eval x) hid
  have hvalue : MvPolynomial.eval x p - lam =
      ∑ j : Fin m, (MvPolynomial.eval x (h j)) ^ 2 := by
    simpa [hrad] using heval
  have hnonneg : 0 ≤ ∑ j : Fin m, (MvPolynomial.eval x (h j)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem feasibleValues_bddAbove {n r : ℕ} {p : Polynomial n}
    {x : Fin n → ℝ} (hx : x ∈ unitSphere n) :
    BddAbove (feasibleValues r p) := by
  exact ⟨MvPolynomial.eval x p, fun _ hlam => feasible_sound hlam hx⟩

theorem feasible_mono {n r t : ℕ} {p : Polynomial n} {lam : ℝ}
    (hrt : r ≤ t) (hlam : Feasible r p lam) : Feasible t p lam := by
  rcases hlam with ⟨m, h, g, hh, hg, hid⟩
  refine ⟨m, h, g, fun j => (hh j).trans hrt, ?_, hid⟩
  exact hg.trans (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hrt) 2)

theorem sphereMinimum_eq {n : ℕ} {p : Polynomial n} {μ : ℝ}
    (hμ : IsSphereMinimum p μ) : sphereMinimum p = μ := by
  rcases hμ with ⟨hlower, x, hx, hvalue⟩
  have hne : (sphereValues p).Nonempty := ⟨μ, x, hx, hvalue⟩
  have hbounded : BddBelow (sphereValues p) := by
    refine ⟨μ, ?_⟩
    rintro v ⟨y, hy, rfl⟩
    exact hlower y hy
  apply le_antisymm
  · exact csInf_le hbounded ⟨x, hx, hvalue⟩
  · exact le_csInf hne (by
      rintro v ⟨y, hy, rfl⟩
      exact hlower y hy)

theorem sos_le_sphereMinimum {n r : ℕ} {p : Polynomial n} {μ : ℝ}
    (hμ : IsSphereMinimum p μ) (hne : (feasibleValues r p).Nonempty) :
    sos r p ≤ sphereMinimum p := by
  rw [sphereMinimum_eq hμ]
  rcases hμ.2 with ⟨x, hx, hvalue⟩
  apply csSup_le hne
  intro lam hlam
  simpa [hvalue] using feasible_sound hlam hx

theorem sos_mono {n r t : ℕ} {p : Polynomial n}
    (hrt : r ≤ t) (hne : (feasibleValues r p).Nonempty)
    {x : Fin n → ℝ} (hx : x ∈ unitSphere n) : sos r p ≤ sos t p := by
  apply csSup_le hne
  intro lam hlam
  exact le_csSup (feasibleValues_bddAbove hx) (feasible_mono hrt hlam)

/-- Certificate obstructions imply a gap without SDP attainment or duality.
Nonemptiness is essential for a real supremum. -/
theorem gap_lower_of_certificates {n r : ℕ} {p : Polynomial n} {η : ℝ}
    (hmin : IsSphereMinimum p 0)
    (hne : (feasibleValues r p).Nonempty)
    (hcert : ∀ lam, Feasible r p lam → lam ≤ -η) : η ≤ gap r p := by
  have hu : sos r p ≤ -η := csSup_le hne (fun lam hlam => hcert lam hlam)
  rw [gap, sphereMinimum_eq hmin]
  linarith

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
