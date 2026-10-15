/-
  Cube-polynomial components of the product-circle parity normal form.
-/
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ParityReduction

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-- The set of second coordinates which occur to odd exponent in a monomial. -/
def circleMonomialParity (s : CubeCircleVar n →₀ ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ s (i, true) % 2 = 1

/-- The amount of a monomial exponent retained in its squarefree second-coordinate part. -/
def circleParityWeight (ib : CubeCircleVar n) (e : ℕ) : ℕ :=
  match ib with
  | (_, false) => 0
  | (_, true) => e % 2

/-- The first-coordinate polynomial left after removing the squarefree second-coordinate
factor from a parity-reduced factor. -/
def cubeReducedFactor (ib : CubeCircleVar n) (e : ℕ) : MvPolynomial (Fin n) ℝ :=
  match ib with
  | (i, false) => X i ^ e
  | (i, true) => (1 - X i ^ 2) ^ (e / 2)

/-- The first-coordinate part of a parity-reduced monomial. -/
def cubeReducedMonomial (s : CubeCircleVar n →₀ ℕ) : MvPolynomial (Fin n) ℝ :=
  s.prod cubeReducedFactor

/-- The scalar second-coordinate factor belonging to one original variable power. -/
def circleParityScalar (z : CubeCircleVar n → ℝ) (ib : CubeCircleVar n) (e : ℕ) : ℝ :=
  match ib with
  | (_, false) => 1
  | (i, true) => z (i, true) ^ (e % 2)

private theorem pow_mod_two (a : ℝ) (e : ℕ) :
    a ^ (e % 2) = if e % 2 = 1 then a else 1 := by
  have hmod : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [hmod]

/-- The parity weights sum to the cardinality of the odd second-coordinate set. -/
theorem sum_circleParityWeight (s : CubeCircleVar n →₀ ℕ) :
    ∑ ib : CubeCircleVar n, circleParityWeight ib (s ib) =
      (circleMonomialParity s).card := by
  classical
  simp only [circleParityWeight, Fintype.sum_prod_type, Fintype.sum_bool]
  calc
    (∑ i : Fin n, s (i, true) % 2) =
        ∑ i : Fin n, if s (i, true) % 2 = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have hmod : s (i, true) % 2 = 0 ∨ s (i, true) % 2 = 1 := by omega
      rcases hmod with hmod | hmod <;> simp [hmod]
    _ = (circleMonomialParity s).card := by
      simp [circleMonomialParity]

/-- The scalar factors in a reduced monomial are exactly the product indexed by its parity
set. -/
theorem prod_circleParityScalar (z : CubeCircleVar n → ℝ)
    (s : CubeCircleVar n →₀ ℕ) :
    s.prod (circleParityScalar z) = ∏ i ∈ circleMonomialParity s, z (i, true) := by
  classical
  rw [s.prod_fintype]
  · simp only [circleParityScalar, Fintype.prod_prod_type, Fintype.prod_bool, mul_one,
      pow_mod_two, circleMonomialParity]
    rw [Finset.prod_filter]
  · intro ib
    rcases ib with ⟨i, b⟩
    cases b <;> simp [circleParityScalar]

/-- Removing the parity variable from one reduced factor accounts for its evaluation exactly. -/
theorem eval_circleReducedFactor_eq_cube_mul_parity
    (z : CubeCircleVar n → ℝ) (ib : CubeCircleVar n) (e : ℕ) :
    MvPolynomial.eval z (circleReducedFactor ib e) =
      MvPolynomial.eval (fun i ↦ z (i, false)) (cubeReducedFactor ib e) *
        circleParityScalar z ib e := by
  rcases ib with ⟨i, b⟩
  cases b <;>
    simp [circleReducedFactor, cubeReducedFactor, circleParityScalar, circleGenerator,
      mul_comm]

/-- Pointwise factorization of a reduced monomial into a cube polynomial and its squarefree
second-coordinate monomial. -/
theorem eval_circleReduceMonomial_eq_cube_mul_parity
    (z : CubeCircleVar n → ℝ) (s : CubeCircleVar n →₀ ℕ) :
    MvPolynomial.eval z (circleReduceMonomial s) =
      MvPolynomial.eval (fun i ↦ z (i, false)) (cubeReducedMonomial s) *
        ∏ i ∈ circleMonomialParity s, z (i, true) := by
  classical
  simp only [circleReduceMonomial, cubeReducedMonomial, Finsupp.prod, map_prod]
  calc
    ∏ x ∈ s.support, MvPolynomial.eval z (circleReducedFactor x (s x)) =
        ∏ x ∈ s.support,
          (MvPolynomial.eval (fun i ↦ z (i, false)) (cubeReducedFactor x (s x)) *
            circleParityScalar z x (s x)) := by
      apply Finset.prod_congr rfl
      intro ib _
      exact eval_circleReducedFactor_eq_cube_mul_parity z ib (s ib)
    _ = (∏ x ∈ s.support,
          MvPolynomial.eval (fun i ↦ z (i, false)) (cubeReducedFactor x (s x))) *
        ∏ x ∈ s.support, circleParityScalar z x (s x) := by
      exact Finset.prod_mul_distrib
    _ = (∏ x ∈ s.support,
          MvPolynomial.eval (fun i ↦ z (i, false)) (cubeReducedFactor x (s x))) *
        ∏ i ∈ circleMonomialParity s, z (i, true) := by
      rw [← Finsupp.prod, prod_circleParityScalar]

/-- The weighted degree of the cube part plus the size of its parity set is no larger than
the degree of the original monomial. -/
theorem cubeReducedFactor_totalDegree_add_weight_le
    (ib : CubeCircleVar n) (e : ℕ) :
    (cubeReducedFactor ib e).totalDegree + circleParityWeight ib e ≤ e := by
  rcases ib with ⟨i, b⟩
  cases b with
  | false =>
      simp [cubeReducedFactor, circleParityWeight]
  | true =>
      have hg : ((1 : MvPolynomial (Fin n) ℝ) - X i ^ 2).totalDegree ≤ 2 := by
        exact (MvPolynomial.totalDegree_sub _ _).trans
          (max_le (by simp) (by simp))
      have hp : (((1 : MvPolynomial (Fin n) ℝ) - X i ^ 2) ^ (e / 2)).totalDegree ≤
          (e / 2) * 2 :=
        (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left (e / 2) hg)
      simp only [cubeReducedFactor, circleParityWeight]
      omega

/-- Weighted total-degree ledger for the cube part of a reduced monomial. -/
theorem cubeReducedMonomial_totalDegree_add_card_le
    (s : CubeCircleVar n →₀ ℕ) :
    (cubeReducedMonomial s).totalDegree + (circleMonomialParity s).card ≤
      s.sum fun _ e ↦ e := by
  classical
  have hzero : ∀ ib : CubeCircleVar n, cubeReducedFactor ib 0 = 1 := by
    intro ib
    rcases ib with ⟨i, b⟩
    cases b <;> simp [cubeReducedFactor]
  have hprod : (cubeReducedMonomial s).totalDegree ≤
      ∑ ib : CubeCircleVar n, (cubeReducedFactor ib (s ib)).totalDegree := by
    unfold cubeReducedMonomial
    rw [s.prod_fintype cubeReducedFactor hzero]
    exact MvPolynomial.totalDegree_finsetProd Finset.univ _
  calc
    (cubeReducedMonomial s).totalDegree + (circleMonomialParity s).card ≤
        (∑ ib : CubeCircleVar n, (cubeReducedFactor ib (s ib)).totalDegree) +
          (circleMonomialParity s).card := Nat.add_le_add_right hprod _
    _ = ∑ ib : CubeCircleVar n,
          ((cubeReducedFactor ib (s ib)).totalDegree + circleParityWeight ib (s ib)) := by
      rw [← sum_circleParityWeight s, Finset.sum_add_distrib]
    _ ≤ ∑ ib : CubeCircleVar n, s ib := by
      exact Finset.sum_le_sum fun ib _ ↦
        cubeReducedFactor_totalDegree_add_weight_le ib (s ib)
    _ = s.sum fun _ e ↦ e := by
      rw [s.sum_fintype]
      simp

/-- The cube coefficient of the parity monomial indexed by `J`. -/
def circleParityComponent (P : MvPolynomial (CubeCircleVar n) ℝ) (J : Finset (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ s ∈ P.support.filter (fun s ↦ circleMonomialParity s = J),
    MvPolynomial.C (legacyMvCoeff s P) * cubeReducedMonomial s

/-- Each parity component has the canonical weighted degree inherited from the original
polynomial. -/
theorem circleParityComponent_eq_zero_or_totalDegree_add_card_le
    (P : MvPolynomial (CubeCircleVar n) ℝ) (J : Finset (Fin n)) :
    circleParityComponent P J = 0 ∨
      (circleParityComponent P J).totalDegree + J.card ≤ P.totalDegree := by
  classical
  let T := P.support.filter fun s ↦ circleMonomialParity s = J
  by_cases hT : T = ∅
  · left
    simp [circleParityComponent, T, hT]
  · right
    have hterm (s : CubeCircleVar n →₀ ℕ) (hs : s ∈ T) :
        (MvPolynomial.C (legacyMvCoeff s P) * cubeReducedMonomial s).totalDegree ≤
          P.totalDegree - J.card := by
      have hs' := Finset.mem_filter.mp hs
      have hcoeff :
          (MvPolynomial.C (legacyMvCoeff s P) * cubeReducedMonomial s).totalDegree ≤
            (cubeReducedMonomial s).totalDegree := by
        calc
          (MvPolynomial.C (legacyMvCoeff s P) * cubeReducedMonomial s).totalDegree ≤
              (MvPolynomial.C (legacyMvCoeff s P) :
                MvPolynomial (Fin n) ℝ).totalDegree +
                (cubeReducedMonomial s).totalDegree := MvPolynomial.totalDegree_mul _ _
          _ = (cubeReducedMonomial s).totalDegree := by simp
      have hweighted :
          (cubeReducedMonomial s).totalDegree + J.card ≤ P.totalDegree := by
        calc
          (cubeReducedMonomial s).totalDegree + J.card =
              (cubeReducedMonomial s).totalDegree + (circleMonomialParity s).card := by
            rw [hs'.2]
          _ ≤ s.sum (fun _ e ↦ e) := cubeReducedMonomial_totalDegree_add_card_le s
          _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hs'.1
      omega
    have hcomponent : (circleParityComponent P J).totalDegree ≤
        P.totalDegree - J.card := by
      unfold circleParityComponent
      exact MvPolynomial.totalDegree_finsetSum_le fun s hs ↦ hterm s hs
    obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hT
    have hs' := Finset.mem_filter.mp hs
    have hJ : J.card ≤ P.totalDegree := by
      have := cubeReducedMonomial_totalDegree_add_card_le s
      rw [hs'.2] at this
      exact (Nat.le_add_left J.card (cubeReducedMonomial s).totalDegree).trans
        (this.trans (MvPolynomial.le_totalDegree hs'.1))
    omega

/-- Evaluation of the parity normal form grouped into cube-polynomial components. This identity
is pointwise on all paired coordinates, hence in particular on `ProductCircle n`. -/
theorem eval_circleParityReduce_eq_sum_components
    (P : MvPolynomial (CubeCircleVar n) ℝ) (z : CubeCircleVar n → ℝ) :
    MvPolynomial.eval z (circleParityReduce P) =
      ∑ J ∈ Finset.univ.powerset,
        MvPolynomial.eval (fun i ↦ z (i, false)) (circleParityComponent P J) *
          ∏ i ∈ J, z (i, true) := by
  classical
  let parity : (CubeCircleVar n →₀ ℕ) → Finset (Fin n) := circleMonomialParity
  have hmaps : ∀ s ∈ P.support,
      parity s ∈ (Finset.univ : Finset (Fin n)).powerset := by
    intro s _
    simp [parity]
  calc
    MvPolynomial.eval z (circleParityReduce P) =
        ∑ s ∈ P.support,
          legacyMvCoeff s P *
            (MvPolynomial.eval (fun i ↦ z (i, false)) (cubeReducedMonomial s) *
              ∏ i ∈ circleMonomialParity s, z (i, true)) := by
      change MvPolynomial.eval z
        (∑ s ∈ P.support,
          MvPolynomial.C (legacyMvCoeff s P) * circleReduceMonomial s) = _
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [map_mul, eval_C, eval_circleReduceMonomial_eq_cube_mul_parity]
    _ = ∑ J ∈ Finset.univ.powerset,
        ∑ s ∈ P.support.filter (fun s ↦ parity s = J),
          legacyMvCoeff s P *
            (MvPolynomial.eval (fun i ↦ z (i, false)) (cubeReducedMonomial s) *
              ∏ i ∈ J, z (i, true)) := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      apply Finset.sum_congr rfl
      intro J _
      apply Finset.sum_congr rfl
      intro s hs
      have hparity : parity s = J := (Finset.mem_filter.mp hs).2
      rw [← hparity]
    _ = ∑ J ∈ Finset.univ.powerset,
        MvPolynomial.eval (fun i ↦ z (i, false)) (circleParityComponent P J) *
          ∏ i ∈ J, z (i, true) := by
      apply Finset.sum_congr rfl
      intro J _
      simp only [circleParityComponent, map_sum, map_mul, eval_C, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- On the product of circles, the component expansion evaluates the original polynomial. -/
theorem eval_eq_sum_circleParityComponents {z : CubeCircleVar n → ℝ}
    (hz : z ∈ ProductCircle n) (P : MvPolynomial (CubeCircleVar n) ℝ) :
    MvPolynomial.eval z P =
      ∑ J ∈ Finset.univ.powerset,
        MvPolynomial.eval (fun i ↦ z (i, false)) (circleParityComponent P J) *
          ∏ i ∈ J, z (i, true) := by
  rw [← eval_circleParityReduce hz]
  exact eval_circleParityReduce_eq_sum_components P z

end QuarticConvergence
end OptimalConvergenceRates

end
