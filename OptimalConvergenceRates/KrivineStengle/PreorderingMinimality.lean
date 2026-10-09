/-
  OptimalConvergenceRates/KrivineStengle/PreorderingMinimality.lean

  Minimality of the repository's untruncated generated preordering.
-/
import OptimalConvergenceRates.KrivineStengle.LocalizedCone
import OptimalConvergenceRates.KrivineStengle.SquareCone

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.KrivineStengle

variable {R : Type*} [CommRing R]

theorem IsSquareCone.sum_mem {C : Set R} (hC : IsSquareCone C)
    {s : Finset α} {f : α → R} (hf : ∀ i ∈ s, f i ∈ C) :
    ∑ i ∈ s, f i ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC.zero_mem
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hC.add_mem (hf a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem IsSquareCone.prod_mem {C : Set R} (hC : IsSquareCone C)
    {s : Finset α} {f : α → R} (hf : ∀ i ∈ s, f i ∈ C) :
    ∏ i ∈ s, f i ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC.one_mem
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact hC.mul_mem (hf a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

variable {n m : ℕ}

private theorem IsSOS.mem_squareCone {C : Set (MvPolynomial (Fin n) ℝ)}
    (hC : IsSquareCone C) {q : MvPolynomial (Fin n) ℝ} (hq : IsSOS q) : q ∈ C := by
  obtain ⟨N, Q, rfl⟩ := hq
  exact hC.sum_mem fun i _ ↦ hC.sq_mem (Q i)

/-- Minimality: every square cone containing the named generators contains their generated
untruncated preordering. -/
theorem PreorderingMem.mem_squareCone {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} (hp : PreorderingMem g p)
    {C : Set (MvPolynomial (Fin n) ℝ)} (hC : IsSquareCone C)
    (hg : ∀ i, g i ∈ C) : p ∈ C := by
  obtain ⟨sigma, hsigma, hsum⟩ := hp.toRep
  rw [hsum]
  apply hC.sum_mem
  intro I _
  exact hC.mul_mem (IsSOS.mem_squareCone hC (hsigma I))
    (hC.prod_mem fun i _ ↦ hg i)

/-- Monotonicity under a pointwise inclusion of finite generator families. -/
theorem PreorderingMem.mono_generators
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} (hp : PreorderingMem g p)
    {m' : ℕ} {g' : Fin m' → MvPolynomial (Fin n) ℝ}
    (hg : ∀ i, PreorderingMem g' (g i)) : PreorderingMem g' p :=
  hp.mem_squareCone (preorderingMem_isSquareCone g') hg

end OptimalConvergenceRates.KrivineStengle

end
