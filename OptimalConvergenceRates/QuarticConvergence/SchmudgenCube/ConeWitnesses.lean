/-
  Root-preserving witnesses for the repository's existing box cones.
-/
import OptimalConvergenceRates.BasicNotions.Lasserre

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n r : ℕ} {p : MvPolynomial (Fin n) ℝ}

/-- Every box generator `1 - X i ^ 2` has total degree at most two. -/
theorem boxSemialgebraicGenerator_totalDegree_le_two (i : Fin n) :
    (BoxSemialgebraicGenerator i).totalDegree ≤ 2 := by
  unfold BoxSemialgebraicGenerator
  calc
    ((1 : MvPolynomial (Fin n) ℝ) - X i ^ 2).totalDegree ≤
        max (1 : MvPolynomial (Fin n) ℝ).totalDegree
          ((X i : MvPolynomial (Fin n) ℝ) ^ 2).totalDegree :=
      MvPolynomial.totalDegree_sub _ _
    _ ≤ max 0 2 := max_le_max (by simp) (by simp [MvPolynomial.totalDegree_X_pow])
    _ = 2 := by omega

/-- A product indexed by `J` of box generators has total degree at most
`2 * J.card`. -/
theorem boxSemialgebraicGeneratorProd_totalDegree_le_two_mul_card
    (J : Finset (Fin n)) :
    (BoxSemialgebraicGeneratorProd J).totalDegree ≤ 2 * J.card := by
  unfold BoxSemialgebraicGeneratorProd
  calc
    (∏ j ∈ J, BoxSemialgebraicGenerator j).totalDegree ≤
        ∑ j ∈ J, (BoxSemialgebraicGenerator j).totalDegree :=
      MvPolynomial.totalDegree_finset_prod J _
    _ ≤ ∑ _j ∈ J, 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact boxSemialgebraicGenerator_totalDegree_le_two j
    _ = 2 * J.card := by simp [Nat.mul_comm]

/-- The canonical degree ledger for a weighted square root in the box
preordering: a root budget `deg v + |J| ≤ k` gives certificate degree
`2 * k`. The zero disjunct permits witnesses whose formal total degree is
irrelevant. -/
theorem weightedRootTerm_totalDegree_le_two_mul
    {v : MvPolynomial (Fin n) ℝ} {J : Finset (Fin n)} {k : ℕ}
    (hv : v = 0 ∨ v.totalDegree + J.card ≤ k) :
    ((v ^ 2) * BoxSemialgebraicGeneratorProd J).totalDegree ≤ 2 * k := by
  rcases hv with rfl | hv
  · simp
  · calc
      ((v ^ 2) * BoxSemialgebraicGeneratorProd J).totalDegree ≤
          (v ^ 2).totalDegree + (BoxSemialgebraicGeneratorProd J).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * v.totalDegree + 2 * J.card :=
        Nat.add_le_add (MvPolynomial.totalDegree_pow v 2)
          (boxSemialgebraicGeneratorProd_totalDegree_le_two_mul_card J)
      _ = 2 * (v.totalDegree + J.card) := by omega
      _ ≤ 2 * k := Nat.mul_le_mul_left 2 hv

/-- A box-preordering certificate which retains every square root.  The order
is the repository's total certificate degree, not a square-root degree. -/
structure BoxPreorderingRootWitness (p : MvPolynomial (Fin n) ℝ) (r : ℕ) where
  N : Finset (Fin n) → ℕ
  root : ∀ J, Fin (N J) → MvPolynomial (Fin n) ℝ
  decomp : p = ∑ J ∈ Finset.univ.powerset,
    (∑ j, (root J j) ^ 2) * BoxSemialgebraicGeneratorProd J
  degree : ∀ J j,
    (((root J j) ^ 2) * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r

/-- Build a canonical-order root witness directly from root-degree budgets. -/
def BoxPreorderingRootWitness.ofWeighted
    {k : ℕ}
    (N : Finset (Fin n) → ℕ)
    (root : ∀ J, Fin (N J) → MvPolynomial (Fin n) ℝ)
    (decomp : p = ∑ J ∈ Finset.univ.powerset,
      (∑ j, (root J j) ^ 2) * BoxSemialgebraicGeneratorProd J)
    (degree : ∀ J j, root J j = 0 ∨ (root J j).totalDegree + J.card ≤ k) :
    BoxPreorderingRootWitness p (2 * k) where
  N := N
  root := root
  decomp := decomp
  degree J j := weightedRootTerm_totalDegree_le_two_mul (degree J j)

/-- A root-preserving quadratic-module certificate. -/
structure BoxQuadraticModuleRootWitness (p : MvPolynomial (Fin n) ℝ) (r : ℕ) where
  N₀ : ℕ
  root₀ : Fin N₀ → MvPolynomial (Fin n) ℝ
  N : Fin n → ℕ
  root : ∀ i, Fin (N i) → MvPolynomial (Fin n) ℝ
  decomp : p = (∑ j, (root₀ j) ^ 2) +
    ∑ i, (∑ j, (root i j) ^ 2) * BoxSemialgebraicGenerator i
  degree₀ : ∀ j, ((root₀ j) ^ 2).totalDegree ≤ r
  degree : ∀ i j,
    (((root i j) ^ 2) * BoxSemialgebraicGenerator i).totalDegree ≤ r

/-- Forget the individual roots of a preordering witness. -/
theorem BoxPreorderingRootWitness.toBoxPreordering
    (w : BoxPreorderingRootWitness p r) : p ∈ BoxPreordering n r := by
  let σ : Finset (Fin n) → MvPolynomial (Fin n) ℝ := fun J ↦ ∑ j, (w.root J j) ^ 2
  refine ⟨σ, ?_, ?_, w.decomp⟩
  · intro J
    exact ⟨w.N J, w.root J, rfl⟩
  · intro J
    rw [show σ J * BoxSemialgebraicGeneratorProd J =
      ∑ j, (w.root J j) ^ 2 * BoxSemialgebraicGeneratorProd J by
        simp [σ, Finset.sum_mul]]
    exact MvPolynomial.totalDegree_finsetSum_le fun j _ ↦ w.degree J j

/-- Turn a weighted-root decomposition directly into membership in the
repository's canonical box preordering of order `2 * k`. -/
theorem boxPreordering_of_weightedRoots
    {k : ℕ}
    (N : Finset (Fin n) → ℕ)
    (root : ∀ J, Fin (N J) → MvPolynomial (Fin n) ℝ)
    (decomp : p = ∑ J ∈ Finset.univ.powerset,
      (∑ j, (root J j) ^ 2) * BoxSemialgebraicGeneratorProd J)
    (degree : ∀ J j, root J j = 0 ∨ (root J j).totalDegree + J.card ≤ k) :
    p ∈ BoxPreordering n (2 * k) :=
  (BoxPreorderingRootWitness.ofWeighted N root decomp degree).toBoxPreordering

/-- Forget the individual roots of a quadratic-module witness. -/
theorem BoxQuadraticModuleRootWitness.toBoxQuadraticModule
    (w : BoxQuadraticModuleRootWitness p r) : p ∈ BoxQuadraticModule n r := by
  let σ₀ : MvPolynomial (Fin n) ℝ := ∑ j, (w.root₀ j) ^ 2
  let σ : Fin n → MvPolynomial (Fin n) ℝ := fun i ↦ ∑ j, (w.root i j) ^ 2
  refine ⟨σ₀, σ, ?_, ?_, ?_, ?_, w.decomp⟩
  · exact ⟨w.N₀, w.root₀, rfl⟩
  · intro i
    exact ⟨w.N i, w.root i, rfl⟩
  · exact MvPolynomial.totalDegree_finsetSum_le fun j _ ↦ w.degree₀ j
  · intro i
    rw [show σ i * BoxSemialgebraicGenerator i =
      ∑ j, (w.root i j) ^ 2 * BoxSemialgebraicGenerator i by
        simp [σ, Finset.sum_mul]]
    exact MvPolynomial.totalDegree_finsetSum_le fun j _ ↦ w.degree i j

end QuarticConvergence
end OptimalConvergenceRates

end
