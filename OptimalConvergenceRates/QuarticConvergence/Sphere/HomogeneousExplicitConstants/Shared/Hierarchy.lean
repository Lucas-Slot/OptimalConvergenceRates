import OptimalConvergenceRates.QuarticConvergence.Sphere.CertificateBounds
import Mathlib.Tactic
/-!
Local notation for the repository's sphere hierarchy and extrema. Feasibility is the
canonical `SphereSOSMod` predicate; the lower construction obtains its multiplier
bound from `Sphere/CertificateBounds` when the objective degree is at most `2*r`.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

abbrev Polynomial (n : ℕ) := MvPolynomial (Fin n) ℝ

abbrev radiusPolynomial (n : ℕ) : Polynomial n :=
  SphereBallTransfers.sphereQuadratic n

/-- Coordinate notation for the existing algebraic sphere. -/
def unitSphere (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∑ i : Fin n, x i ^ 2 = 1}

theorem unitSphere_eq_sphereSet (n : ℕ) :
    unitSphere n = SphereBallTransfers.sphereSet n := by
  ext x
  simp [unitSphere, SphereBallTransfers.sphereSet, SphereBallTransfers.sphereQuadratic]

/-- Local argument order for the canonical sphere certificate predicate. -/
abbrev Feasible {n : ℕ} (r : ℕ) (p : Polynomial n) (lam : ℝ) : Prop :=
  SphereBallTransfers.SphereSOSMod (p - MvPolynomial.C lam) r

abbrev feasibleValues {n : ℕ} (r : ℕ) (p : Polynomial n) : Set ℝ :=
  QuarticConvergence.sphereSOSFeasible p r

/-- Real supremum used only with an explicit nonemptiness proof. -/
abbrev sos {n : ℕ} (r : ℕ) (p : Polynomial n) : ℝ :=
  sSup (QuarticConvergence.sphereSOSFeasible p r)

abbrev sphereValues {n : ℕ} (p : Polynomial n) : Set ℝ :=
  QuarticConvergence.sphereValueSet p

abbrev sphereMinimum {n : ℕ} (p : Polynomial n) : ℝ :=
  QuarticConvergence.spherePolyMin p

abbrev sphereSupNorm {n : ℕ} (p : Polynomial n) : ℝ :=
  QuarticConvergence.sphereSupNorm p

def gap {n : ℕ} (r : ℕ) (p : Polynomial n) : ℝ :=
  sphereMinimum p - sos r p

/-- The coordinate presentation of the canonical value set. -/
theorem sphereValues_eq {n : ℕ} (p : Polynomial n) :
    sphereValues p = {v | ∃ x ∈ unitSphere n, MvPolynomial.eval x p = v} := by
  rw [unitSphere_eq_sphereSet]
  rfl

/-- The coordinate presentation of the canonical sphere supremum norm. -/
theorem sphereSupNorm_eq_sSup {n : ℕ} (p : Polynomial n) :
    sphereSupNorm p = sSup {v | ∃ x ∈ unitSphere n, |MvPolynomial.eval x p| = v} := by
  unfold sphereSupNorm QuarticConvergence.sphereSupNorm
  congr 1
  rw [unitSphere_eq_sphereSet]
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨MvPolynomial.eval x p, ⟨x, hx, rfl⟩, rfl⟩

/-- Explicit signed witnesses construct the canonical certificate. -/
theorem feasible_of_squares {n r m : ℕ} {p : Polynomial n} {lam : ℝ}
    (h : Fin m → Polynomial n) (g : Polynomial n)
    (hh : ∀ j, (h j).totalDegree ≤ r) (_hg : g.totalDegree ≤ 2 * r - 2)
    (hid : p - MvPolynomial.C lam =
      (∑ j, h j ^ 2) + (1 - radiusPolynomial n) * g) : Feasible r p lam := by
  refine ⟨m, h, -g, ?_, hh⟩
  rw [hid]
  simp only [SphereBallTransfers.sphereRelation, radiusPolynomial]
  ring

/-- Reading a degree-bounded objective supplies the multiplier bound automatically. -/
theorem feasible_exists_squares {n r : ℕ} {p : Polynomial n} {lam : ℝ}
    (hn : 0 < n) (hp : p.totalDegree ≤ 2 * r) (hcert : Feasible r p lam) :
    ∃ m, ∃ h : Fin m → Polynomial n, ∃ g : Polynomial n,
      (∀ j, (h j).totalDegree ≤ r) ∧ g.totalDegree ≤ 2 * r - 2 ∧
        p - MvPolynomial.C lam = (∑ j, h j ^ 2) + (1 - radiusPolynomial n) * g := by
  obtain ⟨m, h, g, hid, hh⟩ := hcert
  refine ⟨m, h, -g, hh, ?_, ?_⟩
  · simpa using sphere_multiplier_degree hn (p - MvPolynomial.C lam) h g
      ((MvPolynomial.totalDegree_sub _ _).trans (max_le hp (by simp))) hh hid
  · rw [hid]
    simp only [SphereBallTransfers.sphereRelation, radiusPolynomial]
    ring

/-- An attained sphere minimum, used to justify the real infimum. -/
def IsSphereMinimum {n : ℕ} (p : Polynomial n) (μ : ℝ) : Prop :=
  (∀ x ∈ unitSphere n, μ ≤ MvPolynomial.eval x p) ∧
    ∃ x ∈ unitSphere n, MvPolynomial.eval x p = μ

@[simp] theorem radiusPolynomial_eval {n : ℕ} (x : Fin n → ℝ) :
    MvPolynomial.eval x (radiusPolynomial n) = ∑ i : Fin n, x i ^ 2 := by
  simp [radiusPolynomial, SphereBallTransfers.sphereQuadratic]

theorem feasible_sound {n r : ℕ} {p : Polynomial n} {lam : ℝ}
    (hlam : Feasible r p lam) {x : Fin n → ℝ} (hx : x ∈ unitSphere n) :
    lam ≤ MvPolynomial.eval x p := by
  have hx' : x ∈ SphereBallTransfers.sphereSet n := (unitSphere_eq_sphereSet n) ▸ hx
  have h := hlam.nonnegOnSphere hx'
  simpa only [map_sub, MvPolynomial.eval_C, sub_nonneg] using h

theorem feasibleValues_bddAbove {n r : ℕ} {p : Polynomial n}
    {x : Fin n → ℝ} (hx : x ∈ unitSphere n) :
    BddAbove (feasibleValues r p) := by
  exact ⟨MvPolynomial.eval x p, fun _ hlam ↦ feasible_sound hlam hx⟩

theorem feasible_mono {n r t : ℕ} {p : Polynomial n} {lam : ℝ}
    (hrt : r ≤ t) (hlam : Feasible r p lam) : Feasible t p lam := hlam.mono hrt

theorem sphereMinimum_eq {n : ℕ} {p : Polynomial n} {μ : ℝ}
    (hμ : IsSphereMinimum p μ) : sphereMinimum p = μ := by
  rcases hμ with ⟨hlower, x, hx, hvalue⟩
  apply le_antisymm
  · rw [← hvalue]
    exact spherePolyMin_le_eval p x ((unitSphere_eq_sphereSet n) ▸ hx)
  · apply le_csInf
    · exact ⟨μ, x, (unitSphere_eq_sphereSet n) ▸ hx, hvalue⟩
    · rintro v ⟨y, hy, rfl⟩
      exact hlower y ((unitSphere_eq_sphereSet n).symm ▸ hy)

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
  have hu : sos r p ≤ -η := csSup_le hne (fun lam hlam ↦ hcert lam hlam)
  rw [gap, sphereMinimum_eq hmin]
  linarith

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
