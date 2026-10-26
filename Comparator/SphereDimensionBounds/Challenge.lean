import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.WithBot
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Challenge: dimension-dependent sphere SOS bounds

This standalone challenge imports only Mathlib. Its sphere definitions are
the definitions already used by the repository. The three theorem proofs are
intentional challenge holes; all definitions are explicit.
-/

noncomputable section
set_option autoImplicit false

open MvPolynomial
open scoped BigOperators

namespace OptimalConvergenceRates

namespace SphereBallTransfers

/-- The quadratic form defining the sphere. -/
def sphereQuadratic (m : ℕ) : MvPolynomial (Fin m) ℝ :=
  ∑ i : Fin m, (X i) ^ 2

/-- The existing signed sphere relation. -/
def sphereRelation (m : ℕ) : MvPolynomial (Fin m) ℝ :=
  sphereQuadratic m - 1

/-- The unit sphere in coordinate space. -/
def sphereSet (m : ℕ) : Set (Fin m → ℝ) :=
  {x | MvPolynomial.eval x (sphereQuadratic m) = 1}

/-- The repository's sphere SOS convention bounds square-root degrees. -/
def SphereSOSMod {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (k : ℕ) : Prop :=
  ∃ (N : ℕ) (q : Fin N → MvPolynomial (Fin m) ℝ) (h : MvPolynomial (Fin m) ℝ),
    p = (∑ j : Fin N, (q j) ^ 2) + sphereRelation m * h ∧
    ∀ j : Fin N, (q j).totalDegree ≤ k

end SphereBallTransfers

namespace QuarticConvergence

open SphereBallTransfers

/-- Polynomial values on the sphere. -/
def sphereValueSet {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Set ℝ :=
  (fun x ↦ MvPolynomial.eval x p) '' sphereSet n

/-- The existing sphere minimum. -/
def spherePolyMin {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  sInf (sphereValueSet p)

/-- The existing sphere maximum. -/
def spherePolyMax {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  sSup (sphereValueSet p)

/-- Feasible lower values in the existing hierarchy. -/
def sphereSOSFeasible {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (r : ℕ) : Set ℝ :=
  {l | SphereSOSMod (f - MvPolynomial.C l) r}

open Classical in
/-- The hierarchy bound is bottom exactly when its feasible set is empty. -/
def sphereSOSBound {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (r : ℕ) : WithBot ℝ :=
  if _h : (sphereSOSFeasible f r).Nonempty then ↑(sSup (sphereSOSFeasible f r)) else ⊥

end QuarticConvergence

namespace SphereDimensionBounds

open SphereBallTransfers QuarticConvergence

theorem sphereDimensionUpperRate_membership {n d r : ℕ}
    (hn : 3 ≤ n) (hd : 4 ≤ d) (heven : Even d) (hr : 8 * n * d ≤ r)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d) :
    SphereSOSMod
      (p - C (spherePolyMin p) +
        C ((192 * Real.pi ^ 4 * 5476140000) *
          ((d : ℝ) ^ 4 * (n : ℝ) ^ 4 * (1 + (Nat.clog 2 n : ℝ)) ^ 3 /
            (r : ℝ) ^ 4) * (spherePolyMax p - spherePolyMin p))) r := by
  sorry

theorem sphereDimensionUpperRate_gap {n d r : ℕ}
    (hn : 3 ≤ n) (hd : 4 ≤ d) (heven : Even d) (hr : 8 * n * d ≤ r)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d) :
    ∃ b : ℝ, sphereSOSBound p r = (b : WithBot ℝ) ∧
      0 ≤ spherePolyMin p - b ∧
      spherePolyMin p - b ≤
        (192 * Real.pi ^ 4 * 5476140000) *
          ((d : ℝ) ^ 4 * (n : ℝ) ^ 4 * (1 + (Nat.clog 2 n : ℝ)) ^ 3 /
            (r : ℝ) ^ 4) * (spherePolyMax p - spherePolyMin p) := by
  sorry

theorem sphereDimensionLowerRate :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ d : ℕ, 4 ≤ d → Even d →
        ∃ p : MvPolynomial (Fin n) ℝ,
          p.IsHomogeneous d ∧
          (∀ x : Fin n → ℝ, 0 ≤ eval x p) ∧
          spherePolyMin p = 0 ∧ spherePolyMax p = 1 ∧
          ∀ r : ℕ, d / 2 ≤ r →
            ∃ b : ℝ, sphereSOSBound p r = (b : WithBot ℝ) ∧
              c * min (1 / (n : ℝ))
                ((d : ℝ) ^ 4 * (n : ℝ) ^ 3 / (r : ℝ) ^ 4) ≤
                  spherePolyMin p - b := by
  sorry

end SphereDimensionBounds
end OptimalConvergenceRates
