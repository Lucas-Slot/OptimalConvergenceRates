import OptimalConvergenceRates.CQC.EqualitySlack
import OptimalConvergenceRates.CQC.BoxLiftAlgebra

/-!
# Full rank of the equality-aware slack Jacobian
-/

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates
namespace CQCInternal

variable {n m : ℕ}

/-- CQC with encoded equalities gives independence of the active gradients in
the selected generator family at every point feasible for the original
presentation. -/
theorem selectedActiveGradients_linearIndependent
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcqc : CQCWithEqualities g)
    {x : Fin n → ℝ} (hx : x ∈ KrivineStengle.basicClosedSet g) :
    LinearIndependent ℝ
      (fun i : {i : Fin (selectedConstraintCount g) //
          MvPolynomial.eval x (selectedGenerator g i) = 0} ↦
        fun j : Fin n ↦
          MvPolynomial.eval x (MvPolynomial.pderiv j (selectedGenerator g i))) := by
  let inclusion :
      {i : Fin (selectedConstraintCount g) //
          MvPolynomial.eval x (selectedGenerator g i) = 0} →
        {i : Fin m // IsActiveWithEqualities g x i} :=
    fun i ↦ ⟨selectedRawIndex g i, by
      refine ⟨?_, ?_⟩
      · simpa [selectedGenerator] using i.2
      · exact selectedRawIndex_isSelected g i⟩
  have hinjective : Function.Injective inclusion := by
    intro i j hij
    apply Subtype.ext
    apply selectedRawIndex_injective g
    exact congrArg
      (fun k : {i : Fin m // IsActiveWithEqualities g x i} ↦ k.1) hij
  have hli := (hcqc x hx).comp inclusion hinjective
  rw [show
      (fun i : {i : Fin (selectedConstraintCount g) //
          MvPolynomial.eval x (selectedGenerator g i) = 0} ↦
        fun j : Fin n ↦
          MvPolynomial.eval x (MvPolynomial.pderiv j (selectedGenerator g i))) =
        (fun i : {i : Fin m // IsActiveWithEqualities g x i} ↦
          fun j : Fin n ↦ MvPolynomial.eval x (MvPolynomial.pderiv j (g i))) ∘
            inclusion by
      apply _root_.funext
      intro i
      apply _root_.funext
      intro j
      rfl]
  exact hli

/-- The selected squared-slack rows are independent along the augmented zero
set. -/
theorem selectedSlackGradients_linearIndependent
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcqc : CQCWithEqualities g)
    {z : Fin (n + selectedConstraintCount g) → ℝ}
    (hz : z ∈ equalitySlackZeroSet g) :
    LinearIndependent ℝ (slackGradientAt (selectedGenerator g) z) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let x := basePoint z
  have hx : x ∈ KrivineStengle.basicClosedSet g :=
    basePoint_mem_basicClosedSet_of_mem_equalitySlackZeroSet hz
  have hcore := mem_selected_slackZeroSet_of_mem_equalitySlackZeroSet hz
  have hinactive : ∀ k : Fin (selectedConstraintCount g),
      MvPolynomial.eval x (selectedGenerator g k) ≠ 0 → c k = 0 := by
    intro k hk
    exact coefficient_eq_zero_of_inactive hcore c hc hk
  let active : Finset (Fin (selectedConstraintCount g)) :=
    Finset.univ.filter fun k ↦ MvPolynomial.eval x (selectedGenerator g k) = 0
  have hsumActive :
      ∑ k : {k : Fin (selectedConstraintCount g) //
          MvPolynomial.eval x (selectedGenerator g k) = 0},
          c k.1 • (fun j : Fin n ↦
            MvPolynomial.eval x
              (MvPolynomial.pderiv j (selectedGenerator g k.1))) = 0 := by
    apply _root_.funext
    intro j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hbase := congrFun hc (Fin.castAdd (selectedConstraintCount g) j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      slackGradientAt_base, Pi.zero_apply] at hbase
    calc
      (∑ k : {k : Fin (selectedConstraintCount g) //
          MvPolynomial.eval x (selectedGenerator g k) = 0},
          c k.1 *
            MvPolynomial.eval x
              (MvPolynomial.pderiv j (selectedGenerator g k.1))) =
          ∑ k ∈ active,
            c k * MvPolynomial.eval x
              (MvPolynomial.pderiv j (selectedGenerator g k)) := by
              symm
              exact Finset.sum_subtype active (fun k ↦ by simp [active]) _
      _ = ∑ k,
          c k * MvPolynomial.eval x
            (MvPolynomial.pderiv j (selectedGenerator g k)) := by
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro k _ hk
            have hkne : MvPolynomial.eval x (selectedGenerator g k) ≠ 0 := by
              simpa [active] using hk
            rw [hinactive k hkne, zero_mul]
      _ = 0 := by simpa [x] using hbase
  have hactiveZero :=
    (Fintype.linearIndependent_iff.mp
      (selectedActiveGradients_linearIndependent hcqc hx))
      (fun k ↦ c k.1) hsumActive
  by_cases hi : MvPolynomial.eval x (selectedGenerator g i) = 0
  · exact hactiveZero ⟨i, hi⟩
  · exact hinactive i hi

/-- Evaluated gradient family of the complete equality-aware equation system. -/
def equalitySlackGradientAt
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + selectedConstraintCount g) → ℝ)
    (i : Fin (selectedConstraintCount g + selectedEqualityCount g)) :
    Fin (n + selectedConstraintCount g) → ℝ :=
  polynomialGradientAt (equalitySlackPolynomial g i) z

@[simp]
theorem equalitySlackGradientAt_core
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + selectedConstraintCount g) → ℝ)
    (i : Fin (selectedConstraintCount g)) :
    equalitySlackGradientAt g z
        (Fin.castAdd (selectedEqualityCount g) i) =
      slackGradientAt (selectedGenerator g) z i := by
  simp [equalitySlackGradientAt, equalitySlackPolynomial,
    polynomialGradientAt_slackPolynomial]

@[simp]
theorem equalitySlackGradientAt_equality
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (z : Fin (n + selectedConstraintCount g) → ℝ)
    (e : Fin (selectedEqualityCount g))
    (j : Fin (n + selectedConstraintCount g)) :
    equalitySlackGradientAt g z
        (Fin.natAdd (selectedConstraintCount g) e) j =
      if j = Fin.natAdd n (selectedEqualityIndex g e) then 1 else 0 := by
  classical
  by_cases h : j = Fin.natAdd n (selectedEqualityIndex g e)
  · subst j
    simp [equalitySlackGradientAt, equalitySlackPolynomial, polynomialGradientAt]
  · simp [equalitySlackGradientAt, equalitySlackPolynomial, polynomialGradientAt, h]

/-- All rows of the complete equality-aware slack Jacobian are independent on
its zero set. -/
theorem equalitySlackGradients_linearIndependent
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (hcqc : CQCWithEqualities g)
    {z : Fin (n + selectedConstraintCount g) → ℝ}
    (hz : z ∈ equalitySlackZeroSet g) :
    LinearIndependent ℝ (equalitySlackGradientAt g z) := by
  classical
  let s := selectedConstraintCount g
  let ecount := selectedEqualityCount g
  have hcore :
      LinearIndependent ℝ (slackGradientAt (selectedGenerator g) z) :=
    selectedSlackGradients_linearIndependent hcqc hz
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hextra : ∀ e : Fin (selectedEqualityCount g),
      c (Fin.natAdd (selectedConstraintCount g) e) = 0 := by
    intro e
    have hcoord := congrFun hc (Fin.natAdd n (selectedEqualityIndex g e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
    rw [Fin.sum_univ_add] at hcoord
    have hcoreCoord :
        ∑ k : Fin (selectedConstraintCount g),
            c (Fin.castAdd (selectedEqualityCount g) k) *
              equalitySlackGradientAt g z
                (Fin.castAdd (selectedEqualityCount g) k)
                (Fin.natAdd n (selectedEqualityIndex g e)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [equalitySlackGradientAt_core, slackGradientAt_slack]
      by_cases hk : selectedEqualityIndex g e = k
      · subst k
        have hy :=
          equality_slack_eq_zero_of_mem_equalitySlackZeroSet hz e
        simp [hy]
      · simp [hk]
    rw [hcoreCoord, zero_add] at hcoord
    have hextraCoord :
        (∑ e' : Fin (selectedEqualityCount g),
            c (Fin.natAdd (selectedConstraintCount g) e') *
              equalitySlackGradientAt g z
                (Fin.natAdd (selectedConstraintCount g) e')
                (Fin.natAdd n (selectedEqualityIndex g e))) =
          c (Fin.natAdd (selectedConstraintCount g) e) := by
      rw [Finset.sum_eq_single e]
      · simp
      · intro e' _ he'
        have hne : selectedEqualityIndex g e ≠ selectedEqualityIndex g e' := by
          intro h
          exact he' (selectedEqualityIndex_injective g h).symm
        simp [hne]
      · simp
    rw [hextraCoord] at hcoord
    exact hcoord
  have hcoreSum :
      ∑ k : Fin (selectedConstraintCount g),
          c (Fin.castAdd (selectedEqualityCount g) k) •
            slackGradientAt (selectedGenerator g) z k = 0 := by
    apply _root_.funext
    intro j
    have hj := congrFun hc j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj ⊢
    rw [Fin.sum_univ_add] at hj
    have hextraSum :
        ∑ e : Fin (selectedEqualityCount g),
            c (Fin.natAdd (selectedConstraintCount g) e) *
              equalitySlackGradientAt g z
                (Fin.natAdd (selectedConstraintCount g) e) j = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [hextra e, zero_mul]
    rw [hextraSum, add_zero] at hj
    simpa using hj
  have hcoreZero :=
    (Fintype.linearIndependent_iff.mp hcore)
      (fun k ↦ c (Fin.castAdd (selectedEqualityCount g) k)) hcoreSum
  refine Fin.addCases ?_ ?_ i
  · intro k
    exact hcoreZero k
  · intro e
    exact hextra e

end CQCInternal
end OptimalConvergenceRates

end
