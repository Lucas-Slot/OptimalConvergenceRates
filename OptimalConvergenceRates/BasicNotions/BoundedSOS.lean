import OptimalConvergenceRates.BasicNotions.SOS

/-!
# Degree-bounded sums of squares as a proposition

`BoundedSOS r p` is the existence of the repository's `DegreeBoundedSOS p r` witness.
The root degree convention is shared by all certificate constructions. These operations
are independent of the sphere and of the quantitative homogeneous bounds.
-/

noncomputable section

namespace OptimalConvergenceRates

open MvPolynomial
open scoped BigOperators

/-- Existence of a sum-of-squares witness whose square roots have degree at most `r`. -/
abbrev BoundedSOS {n : ℕ} (r : ℕ) (p : MvPolynomial (Fin n) ℝ) : Prop :=
  Nonempty (DegreeBoundedSOS p r)

namespace BoundedSOS

/-- An explicit family with root-degree bounds presents the canonical SOS witness. -/
theorem of_squares {n r m : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (a : Fin m → MvPolynomial (Fin n) ℝ) (ha : ∀ i, (a i).totalDegree ≤ r)
    (hp : p = ∑ i, a i ^ 2) : BoundedSOS r p :=
  ⟨⟨m, a, hp, ha⟩⟩

/-- Expose square roots when a polynomial identity needs the individual summands. -/
theorem exists_squares {n r : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : BoundedSOS r p) :
    ∃ m, ∃ a : Fin m → MvPolynomial (Fin n) ℝ,
      (∀ i, (a i).totalDegree ≤ r) ∧ p = ∑ i, a i ^ 2 := by
  obtain ⟨h⟩ := hp
  exact ⟨h.N, h.P, h.degree, h.decomp⟩

theorem of_family {n d : ℕ} {I : Type*} [Fintype I]
    (a : I → MvPolynomial (Fin n) ℝ) (ha : ∀ i, (a i).totalDegree ≤ d) :
    BoundedSOS d (∑ i, a i ^ 2) := by
  classical
  let e := Fintype.equivFin I
  exact of_squares (fun j ↦ a (e.symm j)) (fun _ ↦ ha _)
    (e.symm.sum_comp (fun i ↦ a i ^ 2)).symm

theorem zero {n d : ℕ} : BoundedSOS d (0 : MvPolynomial (Fin n) ℝ) :=
  of_squares (m := 0) Fin.elim0 (fun i ↦ Fin.elim0 i) (by simp)

theorem square {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d) :
    BoundedSOS d (p ^ 2) := by
  simpa using of_family (fun _ : Fin 1 ↦ p) (fun _ ↦ hp)

theorem mono {n a b : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : BoundedSOS a p) (hab : a ≤ b) : BoundedSOS b p := by
  obtain ⟨h⟩ := hp
  exact ⟨⟨h.N, h.P, h.decomp, fun i ↦ (h.degree i).trans hab⟩⟩

theorem add {n d : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    (hp : BoundedSOS d p) (hq : BoundedSOS d q) : BoundedSOS d (p + q) := by
  classical
  obtain ⟨m, a, ha, rfl⟩ := hp.exists_squares
  obtain ⟨l, b, hb, rfl⟩ := hq.exists_squares
  apply of_squares (Fin.addCases a b)
  · intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa using ha j
    · simpa using hb j
  · rw [Fin.sum_univ_add]
    simp

theorem mul {n a b : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    (hp : BoundedSOS a p) (hq : BoundedSOS b q) : BoundedSOS (a + b) (p * q) := by
  classical
  obtain ⟨m, v, hv, rfl⟩ := hp.exists_squares
  obtain ⟨l, w, hw, rfl⟩ := hq.exists_squares
  have hid : (∑ i, v i ^ 2) * (∑ j, w j ^ 2) =
      ∑ ij : Fin m × Fin l, (v ij.1 * w ij.2) ^ 2 := by
    simp only [Fintype.sum_prod_type, mul_pow, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hid]
  exact of_family _ (fun ij ↦ (totalDegree_mul _ _).trans
    (Nat.add_le_add (hv ij.1) (hw ij.2)))

theorem scale {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : BoundedSOS d p) (c : ℝ) (hc : 0 ≤ c) : BoundedSOS d (C c * p) := by
  obtain ⟨m, a, ha, rfl⟩ := hp.exists_squares
  apply of_squares (fun i ↦ C (Real.sqrt c) * a i)
  · intro i
    exact (totalDegree_mul _ _).trans (by simpa using ha i)
  · simp only [mul_pow, ← map_pow, Real.sq_sqrt hc, Finset.mul_sum]

theorem sum {n d : ℕ} {I : Type*} (s : Finset I)
    (p : I → MvPolynomial (Fin n) ℝ) (hp : ∀ i ∈ s, BoundedSOS d (p i)) :
    BoundedSOS d (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (n := n) (d := d))
  | @insert i s his ih =>
    rw [Finset.sum_insert his]
    exact (hp i (Finset.mem_insert_self ..)).add
      (ih (fun j hj ↦ hp j (Finset.mem_insert_of_mem hj)))

theorem degree {n d : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : BoundedSOS d p) :
    p.totalDegree ≤ 2 * d := by
  obtain ⟨h⟩ := hp
  exact h.totalDegree_le_two_mul

theorem rename {n m d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : BoundedSOS d p) (f : Fin n → Fin m) :
    BoundedSOS d (MvPolynomial.rename f p) := by
  obtain ⟨l, a, ha, hid⟩ := hp.exists_squares
  rw [hid, map_sum]
  simp only [map_pow]
  exact of_family _ (fun i ↦ (totalDegree_rename_le f (a i)).trans (ha i))

theorem pow {n a : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : BoundedSOS a p) (j : ℕ) : BoundedSOS (a * j) (p ^ j) := by
  induction j with
  | zero => simpa using square (1 : MvPolynomial (Fin n) ℝ) (by simp : totalDegree 1 ≤ 0)
  | succ j ih =>
    rw [pow_succ]
    simpa [Nat.mul_succ] using ih.mul hp

end BoundedSOS
end OptimalConvergenceRates
