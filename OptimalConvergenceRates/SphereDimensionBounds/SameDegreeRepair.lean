import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Hierarchy

/-!
Exact polynomial cross-term completion repairs a structured residual at the
same certificate order. The two auxiliary certificates are hypotheses;
this module does not construct them from pointwise approximation bounds.
-/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds

open OptimalConvergenceRates.SphereDimensionBounds.Foundation
open scoped BigOperators

/-- Addition preserves both the root degree and the sphere multiplier degree. -/
theorem feasible_add_same_order {n r : ℕ} {p q : Polynomial n} {lam mu : ℝ}
    (hp : Feasible r p lam) (hq : Feasible r q mu) :
    Feasible r (p + q) (lam + mu) := by
  classical
  rcases hp with ⟨m, a, g, ha, hg, hidp⟩
  rcases hq with ⟨l, b, h, hb, hh, hidq⟩
  refine ⟨m + l, Fin.addCases a b, g + h, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using ha j
    · intro j
      simpa using hb j
  · exact (MvPolynomial.totalDegree_add _ _).trans (max_le hg hh)
  · have hsum :
        (∑ i : Fin (m + l), (Fin.addCases a b i) ^ 2) =
          (∑ i : Fin m, a i ^ 2) + ∑ j : Fin l, b j ^ 2 := by
      rw [Fin.sum_univ_add]
      simp
    rw [hsum]
    calc
      p + q - MvPolynomial.C (lam + mu) =
          (p - MvPolynomial.C lam) + (q - MvPolynomial.C mu) := by
        rw [MvPolynomial.C_add]
        ring
      _ = _ := by rw [hidp, hidq]; ring

/-- An actual finite sum of polynomial squares is feasible at its root order. -/
theorem feasible_finite_square_sum {n r : ℕ} {I : Type*} [Fintype I]
    (p : I → Polynomial n) (hp : ∀ i, (p i).totalDegree ≤ r) :
    Feasible r (∑ i, p i ^ 2) 0 := by
  classical
  let equiv : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun j => p (equiv.symm j), 0, ?_, by simp, ?_⟩
  · intro j
    exact hp _
  · simpa only [MvPolynomial.C_0, sub_zero, mul_zero, add_zero] using
      (equiv.symm.sum_comp (fun i => p i ^ 2)).symm

/-- The exact completion identity isolates the two SOS-dominated errors. -/
theorem same_degree_repair_identity {n : ℕ} {I : Type*} [Fintype I]
    (F T : Polynomial n) (p b : I → Polynomial n) (eta zeta : ℝ)
    (hid : F - ∑ i, p i ^ 2 = 2 * (∑ i, p i * b i) + T) :
    ((∑ i, (p i + b i) ^ 2) +
        (MvPolynomial.C eta - ∑ i, b i ^ 2)) + (T + MvPolynomial.C zeta) =
      F - MvPolynomial.C (-(eta + zeta)) := by
  have hsum : (∑ i, (p i + b i) ^ 2) =
      (∑ i, p i ^ 2) + 2 * (∑ i, p i * b i) + ∑ i, b i ^ 2 := by
    have hpoint (i : I) : (p i + b i) ^ 2 =
        p i ^ 2 + 2 * (p i * b i) + b i ^ 2 := by ring
    simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hF : F = (∑ i, p i ^ 2) + 2 * (∑ i, p i * b i) + T := by
    linear_combination hid
  rw [hF, hsum]
  simp only [MvPolynomial.C_neg, MvPolynomial.C_add]
  ring

/-- Polynomial cross-term completion preserves the original hierarchy order.
Both input certificates have feasible value zero and explicit multiplier
degree bounds through `Feasible`. -/
theorem same_degree_repair {n r : ℕ} {I : Type*} [Fintype I]
    (F T : Polynomial n) (p b : I → Polynomial n) (eta zeta : ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ r) (hb : ∀ i, (b i).totalDegree ≤ r)
    (hid : F - ∑ i, p i ^ 2 = 2 * (∑ i, p i * b i) + T)
    (herror : Feasible r (MvPolynomial.C eta - ∑ i, b i ^ 2) 0)
    (hremainder : Feasible r (T + MvPolynomial.C zeta) 0) :
    Feasible r F (-(eta + zeta)) := by
  have hroots : Feasible r (∑ i, (p i + b i) ^ 2) 0 := by
    apply feasible_finite_square_sum
    intro i
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hp i) (hb i))
  have hcombined := feasible_add_same_order
    (feasible_add_same_order hroots herror) hremainder
  rw [same_degree_repair_identity F T p b eta zeta hid] at hcombined
  simpa only [Feasible, MvPolynomial.C_0, sub_zero, add_zero] using hcombined

/-- The same-order criterion with the two explicit fourth-order budgets. -/
theorem same_degree_repair_quartic_rate {n r : ℕ} {I : Type*} [Fintype I]
    (F T : Polynomial n) (p b : I → Polynomial n) (E R0 k : ℝ)
    (hp : ∀ i, (p i).totalDegree ≤ r) (hb : ∀ i, (b i).totalDegree ≤ r)
    (hid : F - ∑ i, p i ^ 2 = 2 * (∑ i, p i * b i) + T)
    (herror : Feasible r (MvPolynomial.C (E ^ 2 / k ^ 4) - ∑ i, b i ^ 2) 0)
    (hremainder : Feasible r (T + MvPolynomial.C (R0 / k ^ 4)) 0) :
    Feasible r F (-((E ^ 2 + R0) / k ^ 4)) := by
  convert same_degree_repair F T p b (E ^ 2 / k ^ 4) (R0 / k ^ 4)
    hp hb hid herror hremainder using 1
  ring

end OptimalConvergenceRates.SphereDimensionBounds
