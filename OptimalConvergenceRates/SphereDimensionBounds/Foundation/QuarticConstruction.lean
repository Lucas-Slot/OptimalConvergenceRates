import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Rounding

/-!
# The nonnegative quartic associated with sound three-variable clauses

This module proves the occurrence-count identities and the nonnegativity
argument for the actual quartic. Clause soundness is an explicit hypothesis;
the combinatorial existence theorem is a separate dependency.
-/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

section Quartic

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

/-- Occurrences count positions, so this definition also handles repeated
coordinates in an individual clause. -/
def clauseOccurrenceCount (i j k : E → V) (v : V) : ℕ :=
  ∑ e : E, ((if i e = v then 1 else 0) +
    (if j e = v then 1 else 0) + (if k e = v then 1 else 0))

/-- Summing a quantity with occurrence weights equals summing it in all three
positions of every clause. -/
theorem clauseOccurrenceCount_sum (i j k : E → V) (f : V → ℝ) :
    (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * f v) =
      ∑ e : E, (f (i e) + f (j e) + f (k e)) := by
  classical
  simp only [clauseOccurrenceCount, Nat.cast_sum, Nat.cast_add,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp [add_mul, Finset.sum_add_distrib, ite_mul]

theorem clauseOccurrenceCount_total (i j k : E → V) :
    (∑ v : V, (clauseOccurrenceCount i j k v : ℝ)) =
      3 * (Fintype.card E : ℝ) := by
  have ht := clauseOccurrenceCount_sum i j k (fun _ => (1 : ℝ))
  simp at ht
  linarith

def clauseSquareSum (i j k : E → V) (b : E → ℝ) (x : V → ℝ) (t : ℝ) : ℝ :=
  ∑ e : E, (x (i e) * x (j e) - b e * x (k e) * t) ^ 2

def occurrencePenalty (i j k : E → V) (x : V → ℝ) (t : ℝ) : ℝ :=
  ∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * (x v ^ 2 - t ^ 2) ^ 2

/-- The unnormalized homogeneous quartic in the supplied construction. -/
def xorQuartic (i j k : E → V) (b : E → ℝ) (x : V → ℝ) (t : ℝ) : ℝ :=
  clauseSquareSum i j k b x t + 6 * occurrencePenalty i j k x t -
    (Fintype.card E : ℝ) / 4 * t ^ 4

omit [Fintype V] [DecidableEq V] in
theorem clauseSquareSum_nonneg (i j k : E → V) (b : E → ℝ)
    (x : V → ℝ) (t : ℝ) : 0 ≤ clauseSquareSum i j k b x t := by
  exact Finset.sum_nonneg fun e he => sq_nonneg _

theorem occurrencePenalty_nonneg (i j k : E → V) (x : V → ℝ) (t : ℝ) :
    0 ≤ occurrencePenalty i j k x t := by
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- Aggregate rounding keeps exactly the occurrence weights in the quartic. -/
theorem rounded_clause_sum_bound (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (x : V → ℝ) :
    clauseSquareSum i j k b (fun v => roundSign (x v)) 1 ≤
      2 * clauseSquareSum i j k b x 1 + 6 * occurrencePenalty i j k x 1 := by
  have hpoint :
      (∑ e : E, (roundSign (x (i e)) * roundSign (x (j e)) -
          b e * roundSign (x (k e))) ^ 2) ≤
        ∑ e : E, (2 * (x (i e) * x (j e) - b e * x (k e)) ^ 2 +
          6 * ((x (i e) ^ 2 - 1) ^ 2 + (x (j e) ^ 2 - 1) ^ 2 +
            (x (k e) ^ 2 - 1) ^ 2)) := by
    apply Finset.sum_le_sum
    intro e he
    exact rounded_clause_bound (x (i e)) (x (j e)) (x (k e)) (b e) (hb e)
  have herrors := clauseOccurrenceCount_sum i j k (fun v => (x v ^ 2 - 1) ^ 2)
  simpa only [clauseSquareSum, occurrencePenalty, one_pow, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← herrors] using hpoint

/-- The precise margin obtained from sign soundness at `t=1`. -/
theorem xorQuartic_at_one_lower (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hsound : ∀ σ : V → ℝ, (∀ v, σ v ^ 2 = 1) →
      (Fintype.card E : ℝ) ≤ clauseSquareSum i j k b σ 1)
    (x : V → ℝ) :
    (Fintype.card E : ℝ) / 4 ≤ xorQuartic i j k b x 1 := by
  have hsign := hsound (fun v => roundSign (x v)) (fun v => roundSign_sq (x v))
  have hround : (Fintype.card E : ℝ) ≤
      2 * clauseSquareSum i j k b x 1 + 6 * occurrencePenalty i j k x 1 :=
    hsign.trans (rounded_clause_sum_bound i j k b hb x)
  simpa only [xorQuartic, one_pow, mul_one] using
    rounding_margin (clauseSquareSum i j k b x 1) (occurrencePenalty i j k x 1)
      (Fintype.card E : ℝ) (occurrencePenalty_nonneg i j k x 1) hround

omit [Fintype V] [DecidableEq V] in
theorem clauseSquareSum_homogeneous (i j k : E → V) (b : E → ℝ)
    (a : ℝ) (x : V → ℝ) (t : ℝ) :
    clauseSquareSum i j k b (fun v => a * x v) (a * t) =
      a ^ 4 * clauseSquareSum i j k b x t := by
  unfold clauseSquareSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem occurrencePenalty_homogeneous (i j k : E → V)
    (a : ℝ) (x : V → ℝ) (t : ℝ) :
    occurrencePenalty i j k (fun v => a * x v) (a * t) =
      a ^ 4 * occurrencePenalty i j k x t := by
  unfold occurrencePenalty
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- The construction has genuine quartic homogeneity in the original variables. -/
theorem xorQuartic_homogeneous (i j k : E → V) (b : E → ℝ)
    (a : ℝ) (x : V → ℝ) (t : ℝ) :
    xorQuartic i j k b (fun v => a * x v) (a * t) =
      a ^ 4 * xorQuartic i j k b x t := by
  unfold xorQuartic
  rw [clauseSquareSum_homogeneous, occurrencePenalty_homogeneous]
  ring

/-- Sound sign clauses give a globally nonnegative homogeneous quartic.
This statement applies to every real point, including `t=0`. -/
theorem xorQuartic_nonneg (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hsound : ∀ σ : V → ℝ, (∀ v, σ v ^ 2 = 1) →
      (Fintype.card E : ℝ) ≤ clauseSquareSum i j k b σ 1)
    (x : V → ℝ) (t : ℝ) : 0 ≤ xorQuartic i j k b x t := by
  by_cases ht : t = 0
  · subst t
    have hclause := clauseSquareSum_nonneg i j k b x 0
    have hpenalty := occurrencePenalty_nonneg i j k x 0
    simp only [xorQuartic, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, sub_zero]
    linarith
  · have hrescale : (fun v => t * (x v / t)) = x := by
      funext v
      field_simp
    have hscale := xorQuartic_homogeneous i j k b t (fun v => x v / t) 1
    rw [hrescale, mul_one] at hscale
    rw [hscale]
    apply mul_nonneg (by positivity)
    exact (by positivity : (0 : ℝ) ≤ (Fintype.card E : ℝ) / 4).trans
      (xorQuartic_at_one_lower i j k b hb hsound (fun v => x v / t))

/-- The quadratic clause root, with `none` representing the coordinate `t`. -/
def clauseRootPolynomial (i j k : E → V) (b : E → ℝ) (e : E) :
    MvPolynomial (Option V) ℝ :=
  MvPolynomial.X (some (i e)) * MvPolynomial.X (some (j e)) -
    MvPolynomial.C (b e) * MvPolynomial.X (some (k e)) * MvPolynomial.X none

def deviationRootPolynomial (v : V) : MvPolynomial (Option V) ℝ :=
  MvPolynomial.X (some v) ^ 2 - MvPolynomial.X none ^ 2

/-- A polynomial-ring realization of the same quartic, in `|V|+1` variables. -/
def xorQuarticPolynomial (i j k : E → V) (b : E → ℝ) :
    MvPolynomial (Option V) ℝ :=
  (∑ e : E, clauseRootPolynomial i j k b e ^ 2) +
    MvPolynomial.C 6 *
      (∑ v : V, MvPolynomial.C (clauseOccurrenceCount i j k v : ℝ) *
        deviationRootPolynomial v ^ 2) -
    MvPolynomial.C ((Fintype.card E : ℝ) / 4) * MvPolynomial.X none ^ 4

theorem xorQuarticPolynomial_eval (i j k : E → V) (b : E → ℝ)
    (w : Option V → ℝ) :
    MvPolynomial.eval w (xorQuarticPolynomial i j k b) =
      xorQuartic i j k b (fun v => w (some v)) (w none) := by
  simp [xorQuarticPolynomial, clauseRootPolynomial, deviationRootPolynomial,
    xorQuartic, clauseSquareSum, occurrencePenalty]

omit [Fintype E] [Fintype V] [DecidableEq V] in
theorem clauseRootPolynomial_isHomogeneous (i j k : E → V) (b : E → ℝ) (e : E) :
    (clauseRootPolynomial i j k b e).IsHomogeneous 2 := by
  unfold clauseRootPolynomial
  exact ((MvPolynomial.isHomogeneous_X ℝ _).mul
    (MvPolynomial.isHomogeneous_X ℝ _)).sub
      (((MvPolynomial.isHomogeneous_X ℝ _).C_mul (b e)).mul
        (MvPolynomial.isHomogeneous_X ℝ _))

omit [Fintype E] [Fintype V] [DecidableEq V] in
theorem deviationRootPolynomial_isHomogeneous (v : V) :
    (deviationRootPolynomial v).IsHomogeneous 2 := by
  exact (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (some v) 2).sub
    (MvPolynomial.isHomogeneous_X_pow (R := ℝ) none 2)

theorem xorQuarticPolynomial_isHomogeneous (i j k : E → V) (b : E → ℝ) :
    (xorQuarticPolynomial i j k b).IsHomogeneous 4 := by
  classical
  have hclauses :
      (∑ e : E, clauseRootPolynomial i j k b e ^ 2).IsHomogeneous 4 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro e he
    exact (clauseRootPolynomial_isHomogeneous i j k b e).pow 2
  have hpenalty :
      (∑ v : V, MvPolynomial.C (clauseOccurrenceCount i j k v : ℝ) *
        deviationRootPolynomial v ^ 2).IsHomogeneous 4 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro v hv
    exact ((deviationRootPolynomial_isHomogeneous v).pow 2).C_mul _
  exact (hclauses.add (hpenalty.C_mul 6)).sub
    ((MvPolynomial.isHomogeneous_X_pow (R := ℝ) none 4).C_mul _)

theorem xorQuarticPolynomial_totalDegree_le (i j k : E → V) (b : E → ℝ) :
    (xorQuarticPolynomial i j k b).totalDegree ≤ 4 :=
  (xorQuarticPolynomial_isHomogeneous i j k b).totalDegree_le

theorem xorQuarticPolynomial_nonneg (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hsound : ∀ σ : V → ℝ, (∀ v, σ v ^ 2 = 1) →
      (Fintype.card E : ℝ) ≤ clauseSquareSum i j k b σ 1)
    (w : Option V → ℝ) :
    0 ≤ MvPolynomial.eval w (xorQuarticPolynomial i j k b) := by
  rw [xorQuarticPolynomial_eval]
  exact xorQuartic_nonneg i j k b hb hsound _ _

end Quartic

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
