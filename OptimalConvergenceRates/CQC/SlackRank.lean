import OptimalConvergenceRates.CQC.SlackGeometry

/-!
# Full rank of the squared-slack Jacobian

The active-gradient condition is converted here into linear independence of
all rows of the Jacobian of `g_i(x) - y_i^2` along its zero set.
-/

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- The `i`-th row of the squared-slack Jacobian at `z`. -/
def slackGradientAt (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) (i : Fin m) : Fin (n + m) → ℝ :=
  Fin.addCases
    (fun j ↦ MvPolynomial.eval (basePoint z) (MvPolynomial.pderiv j (g i)))
    (fun k ↦ if k = i then -2 * slackPoint z i else 0)

@[simp]
theorem slackGradientAt_base
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) (i : Fin m) (j : Fin n) :
    slackGradientAt g z i (Fin.castAdd m j) =
      MvPolynomial.eval (basePoint z) (MvPolynomial.pderiv j (g i)) := by
  simp [slackGradientAt]

@[simp]
theorem slackGradientAt_slack
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + m) → ℝ) (i k : Fin m) :
    slackGradientAt g z i (Fin.natAdd n k) =
      if k = i then -2 * slackPoint z i else 0 := by
  simp [slackGradientAt]

/-- At a slack zero, a coefficient in a vanishing linear combination of the
slack gradients is zero whenever the corresponding constraint is inactive. -/
theorem coefficient_eq_zero_of_inactive
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackZeroSet g)
    (c : Fin m → ℝ)
    (hc : ∑ i, c i • slackGradientAt g z i = 0)
    {i : Fin m} (hi : MvPolynomial.eval (basePoint z) (g i) ≠ 0) :
    c i = 0 := by
  have hcoord := congrFun hc (Fin.natAdd n i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    slackGradientAt_slack, Pi.zero_apply] at hcoord
  have hislack : slackPoint z i ≠ 0 := by
    intro hzero
    have heq := hz i
    rw [eval_slackPolynomial, hzero] at heq
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero] at heq
    exact hi heq
  have hsingle : c i * (-2 * slackPoint z i) = 0 := by
    simpa using hcoord
  rcases mul_eq_zero.mp hsingle with hci | hfactor
  · exact hci
  · exfalso
    apply hislack
    nlinarith

/-- CQC gives full row rank of the squared-slack Jacobian at every point of
the slack variety. -/
theorem slackGradients_linearIndependent
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcqc : ActiveGradientIndependent g)
    {z : Fin (n + m) → ℝ} (hz : z ∈ slackZeroSet g) :
    LinearIndependent ℝ (slackGradientAt g z) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let x := basePoint z
  have hx : x ∈ KrivineStengle.basicClosedSet g :=
    basePoint_mem_basicClosedSet_of_mem_slackZeroSet hz
  have hinactive : ∀ k : Fin m,
      MvPolynomial.eval x (g k) ≠ 0 → c k = 0 := by
    intro k hk
    exact coefficient_eq_zero_of_inactive hz c hc hk
  let active : Finset (Fin m) :=
    Finset.univ.filter fun k ↦ MvPolynomial.eval x (g k) = 0
  have hsumActive :
      ∑ k : {k : Fin m // MvPolynomial.eval x (g k) = 0},
          c k.1 • (fun j : Fin n ↦
            MvPolynomial.eval x (MvPolynomial.pderiv j (g k.1))) = 0 := by
    apply funext
    intro j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hbase := congrFun hc (Fin.castAdd m j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      slackGradientAt_base, Pi.zero_apply] at hbase
    calc
      (∑ k : {k : Fin m // MvPolynomial.eval x (g k) = 0},
          c k.1 * MvPolynomial.eval x (MvPolynomial.pderiv j (g k.1))) =
          ∑ k ∈ active,
            c k * MvPolynomial.eval x (MvPolynomial.pderiv j (g k)) := by
              symm
              exact Finset.sum_subtype active (fun k ↦ by simp [active]) _
      _ = ∑ k,
          c k * MvPolynomial.eval x (MvPolynomial.pderiv j (g k)) := by
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro k _ hk
            have hkne : MvPolynomial.eval x (g k) ≠ 0 := by
              simpa [active] using hk
            rw [hinactive k hkne, zero_mul]
      _ = 0 := by simpa [x] using hbase
  have hactiveZero :=
    (Fintype.linearIndependent_iff.mp (hcqc x hx))
      (fun k ↦ c k.1) hsumActive
  by_cases hi : MvPolynomial.eval x (g i) = 0
  · exact hactiveZero ⟨i, hi⟩
  · exact hinactive i hi

end CQCInternal
end OptimalConvergenceRates

end
