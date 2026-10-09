import Mathlib.Data.Nat.Lattice
import OptimalConvergenceRates.BasicNotions.BoxCones
import OptimalConvergenceRates.BasicNotions.GeneralCones

/-!
# Least certificate orders

These definitions package the natural-number minima used in the statement of
the fixed-instance transfer theorem. They are used only when a certificate is
known to exist; the empty-set value of `sInf` is deliberately irrelevant.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- Least complete-term degree of a certificate in a generalized quadratic
module. -/
def quadraticModuleOrder (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : ℕ :=
  sInf {r : ℕ | p ∈ GenQuadraticModule g r}

/-- Least complete-term degree of a certificate in the canonical cube
quadratic module. -/
def boxQuadraticModuleOrder (p : MvPolynomial (Fin n) ℝ) : ℕ :=
  sInf {r : ℕ | p ∈ BoxQuadraticModule n r}

theorem quadraticModuleOrder_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ} {p : MvPolynomial (Fin n) ℝ}
    (h : ∃ r, p ∈ GenQuadraticModule g r) :
    p ∈ GenQuadraticModule g (quadraticModuleOrder g p) := by
  exact Nat.sInf_mem h

theorem quadraticModuleOrder_le
    {g : Fin m → MvPolynomial (Fin n) ℝ} {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (h : p ∈ GenQuadraticModule g r) :
    quadraticModuleOrder g p ≤ r :=
  Nat.sInf_le h

theorem boxQuadraticModuleOrder_mem
    {p : MvPolynomial (Fin n) ℝ}
    (h : ∃ r, p ∈ BoxQuadraticModule n r) :
    p ∈ BoxQuadraticModule n (boxQuadraticModuleOrder p) := by
  exact Nat.sInf_mem h

theorem boxQuadraticModuleOrder_le
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (h : p ∈ BoxQuadraticModule n r) :
    boxQuadraticModuleOrder p ≤ r :=
  Nat.sInf_le h

/-- Least order of a certificate after adding a positive constant. -/
def perturbationOrder (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (ε : ℝ) : ℕ :=
  quadraticModuleOrder g (p + C ε)

/-- Cube version of `perturbationOrder`. -/
def boxPerturbationOrder (p : MvPolynomial (Fin n) ℝ) (ε : ℝ) : ℕ :=
  boxQuadraticModuleOrder (p + C ε)

end CQCInternal
end OptimalConvergenceRates

end
