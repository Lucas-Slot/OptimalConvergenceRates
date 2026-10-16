import OptimalConvergenceRates.CQC.Defs
import Mathlib.Data.Fin.VecNotation

/-!
# Regression example for a sphere encoded by opposite inequalities

For every `n`, the unit sphere `S^n` in `ℝⁿ⁺¹` is presented by the inequalities
`1 - ∑ i, x i ^ 2 ≥ 0` and `∑ i, x i ^ 2 - 1 ≥ 0`. The equality-aware CQC
condition retains one of their two opposite gradients and therefore recognizes
this regular equality presentation.
-/

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace CQCExamples

def spherePolynomial (n : ℕ) : MvPolynomial (Fin (n + 1)) ℝ :=
  1 - ∑ i, X i ^ 2

def sphereEqualityGenerators (n : ℕ) :
    Fin 2 → MvPolynomial (Fin (n + 1)) ℝ :=
  ![spherePolynomial n, -spherePolynomial n]

theorem sphere_hasOpposite (n : ℕ) (i : Fin 2) :
    HasOppositeConstraint (sphereEqualityGenerators n) i := by
  fin_cases i
  · refine ⟨1, by decide, ?_⟩
    simp [sphereEqualityGenerators]
  · refine ⟨0, by decide, ?_⟩
    simp [sphereEqualityGenerators]

theorem sphere_zero_isRepresentative (n : ℕ) :
    IsEqualityRepresentative (sphereEqualityGenerators n) 0 := by
  refine ⟨sphere_hasOpposite n 0, ?_⟩
  intro j _
  exact Fin.zero_le j

theorem sphere_one_notRepresentative (n : ℕ) :
    ¬IsEqualityRepresentative (sphereEqualityGenerators n) 1 := by
  intro h
  have hle := h.2 0 (by
    right
    simp [sphereEqualityGenerators])
  omega

theorem sphere_active_index_eq_zero
    {n : ℕ} {x : Fin (n + 1) → ℝ}
    (i : {i : Fin 2 //
      IsActiveWithEqualities (sphereEqualityGenerators n) x i}) :
    i.1 = 0 := by
  by_contra hi
  have hone : i.1 = (1 : Fin 2) := by
    apply Fin.ext
    omega
  have hactive := i.2.2
  rw [hone] at hactive
  rcases hactive with hno | hrep
  · exact hno (sphere_hasOpposite n 1)
  · exact sphere_one_notRepresentative n hrep

theorem sphere_active_subsingleton
    (n : ℕ) (x : Fin (n + 1) → ℝ) :
    Subsingleton {i : Fin 2 //
      IsActiveWithEqualities (sphereEqualityGenerators n) x i} := by
  constructor
  intro i j
  apply Subtype.ext
  rw [sphere_active_index_eq_zero i, sphere_active_index_eq_zero j]

/-- Equality-aware CQC holds for the opposite-inequality presentation of every
unit sphere `S^n` in `ℝⁿ⁺¹`. -/
theorem sphere_cqcWithEqualities (n : ℕ) :
    CQCWithEqualities (sphereEqualityGenerators n) := by
  intro x hx
  let _ : Subsingleton {i : Fin 2 //
      IsActiveWithEqualities (sphereEqualityGenerators n) x i} :=
    sphere_active_subsingleton n x
  rw [linearIndependent_subsingleton_index_iff]
  intro i hzero
  have hqzero : MvPolynomial.eval x (spherePolynomial n) = 0 := by
    simpa [sphereEqualityGenerators] using
      eval_eq_zero_of_hasOppositeConstraint hx (sphere_hasOpposite n 0)
  have hxzero : ∀ j, x j = 0 := by
    intro j
    have hcoord := congrFun hzero j
    have hi : i.1 = 0 := sphere_active_index_eq_zero i
    simpa [sphereEqualityGenerators, spherePolynomial, hi, Pi.single_apply] using
      hcoord
  simp [spherePolynomial, hxzero] at hqzero

/-- Ordinary active-gradient CQC fails for every sphere in the same
presentation because it keeps both opposite active gradients. -/
theorem sphere_not_cqc (n : ℕ) :
    ¬CQC (sphereEqualityGenerators n) := by
  intro hcqc
  let x : Fin (n + 1) → ℝ := fun j ↦ if j = 0 then 1 else 0
  have hx : x ∈ KrivineStengle.basicClosedSet (sphereEqualityGenerators n) := by
    intro i
    fin_cases i <;>
      simp [sphereEqualityGenerators, spherePolynomial, x]
  have hactive :
      ∀ i : Fin 2,
        MvPolynomial.eval x (sphereEqualityGenerators n i) = 0 := by
    intro i
    fin_cases i <;>
      simp [sphereEqualityGenerators, spherePolynomial, x]
  let inclusion :
      Fin 2 →
        {i : Fin 2 //
          MvPolynomial.eval x (sphereEqualityGenerators n i) = 0} :=
    fun i ↦ ⟨i, hactive i⟩
  have hinjective : Function.Injective inclusion := by
    intro i j hij
    exact congrArg Subtype.val hij
  have hli := (hcqc x hx).comp inclusion hinjective
  rw [Fintype.linearIndependent_iff] at hli
  have hsum :
      ∑ i : Fin 2, (1 : ℝ) •
          (fun j : Fin (n + 1) ↦
            MvPolynomial.eval x
              (MvPolynomial.pderiv j
                (sphereEqualityGenerators n (inclusion i)))) = 0 := by
    apply _root_.funext
    intro j
    simp [inclusion, sphereEqualityGenerators]
  have hone := hli (fun _ ↦ 1) hsum 0
  norm_num at hone

end CQCExamples
end OptimalConvergenceRates

end
