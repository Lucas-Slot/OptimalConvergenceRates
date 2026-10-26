import OptimalConvergenceRates.SphereDimensionBounds.Foundation.XorPseudoexpectation

/-!
# Polynomial evaluation on Boolean maps of degree one

Every polynomial root in an order-`r` certificate becomes a Boolean function
of degree at most `r` under a coordinate map of Boolean degree one.
-/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

section DegreeCalculus

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem hasBooleanDegree_mono {d t : ℕ} {f : (V → Bool) → ℝ}
    (hdt : d ≤ t) (hf : HasBooleanDegree d f) : HasBooleanDegree t f := by
  intro S hS
  exact hf S (lt_of_le_of_lt hdt hS)

theorem hasBooleanDegree_const (d : ℕ) (c : ℝ) :
    HasBooleanDegree d (fun _ : V → Bool => c) := by
  have h := (booleanDegreeSpace (I := V) d).smul_mem c (hasBooleanDegree_one d)
  change HasBooleanDegree d (c • (fun _ : V → Bool => (1 : ℝ))) at h
  simpa only [Pi.smul_def, smul_eq_mul, mul_one] using h

theorem hasBooleanDegree_smul (d : ℕ) (c : ℝ) (f : (V → Bool) → ℝ)
    (hf : HasBooleanDegree d f) : HasBooleanDegree d (fun z => c * f z) :=
  (booleanDegreeSpace (I := V) d).smul_mem c hf

theorem hasBooleanDegree_add (d : ℕ) (f g : (V → Bool) → ℝ)
    (hf : HasBooleanDegree d f) (hg : HasBooleanDegree d g) :
    HasBooleanDegree d (fun z => f z + g z) :=
  (booleanDegreeSpace (I := V) d).add_mem hf hg

theorem hasBooleanDegree_sub (d : ℕ) (f g : (V → Bool) → ℝ)
    (hf : HasBooleanDegree d f) (hg : HasBooleanDegree d g) :
    HasBooleanDegree d (fun z => f z - g z) :=
  (booleanDegreeSpace (I := V) d).sub_mem hf hg

theorem hasBooleanDegree_finset_sum {J : Type*} (s : Finset J)
    (f : J → (V → Bool) → ℝ) (d : ℕ)
    (hf : ∀ j ∈ s, HasBooleanDegree d (f j)) :
    HasBooleanDegree d (fun z => ∑ j ∈ s, f j z) := by
  have hsum : (∑ j ∈ s, f j) ∈ booleanDegreeSpace (I := V) d :=
    (booleanDegreeSpace (I := V) d).sum_mem hf
  change (fun z => ∑ j ∈ s, f j z) ∈ booleanDegreeSpace (I := V) d
  convert hsum using 1
  funext z
  simp only [Finset.sum_apply]

theorem hasBooleanDegree_pow (d : ℕ) (f : (V → Bool) → ℝ)
    (hf : HasBooleanDegree d f) (n : ℕ) :
    HasBooleanDegree (d * n) (fun z => f z ^ n) := by
  induction n with
  | zero => simpa only [Nat.mul_zero, pow_zero] using hasBooleanDegree_one (I := V) 0
  | succ n ih =>
      have hmul := hasBooleanDegree_mul (d * n) d (fun z => f z ^ n) f ih hf
      simpa only [Nat.mul_succ, pow_succ] using hmul

theorem hasBooleanDegree_finset_prod {J : Type*} (s : Finset J)
    (d : J → ℕ) (f : J → (V → Bool) → ℝ)
    (hf : ∀ j ∈ s, HasBooleanDegree (d j) (f j)) :
    HasBooleanDegree (∑ j ∈ s, d j) (fun z => ∏ j ∈ s, f j z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasBooleanDegree_one (I := V) 0
  | @insert j s hjs ih =>
      have hj := hf j (Finset.mem_insert_self j s)
      have hs := ih (fun l hl => hf l (Finset.mem_insert_of_mem hl))
      have hmul := hasBooleanDegree_mul (d j) (∑ l ∈ s, d l)
        (f j) (fun z => ∏ l ∈ s, f l z) hj hs
      simpa only [Finset.sum_insert hjs, Finset.prod_insert hjs] using hmul

/-- No finiteness assumption on the polynomial variable type is needed. -/
theorem hasBooleanDegree_eval {σ : Type*} (p : MvPolynomial σ ℝ)
    (a : σ → (V → Bool) → ℝ) (ha : ∀ i, HasBooleanDegree 1 (a i)) :
    HasBooleanDegree p.totalDegree (fun z => MvPolynomial.eval (fun i => a i z) p) := by
  classical
  have heval : (fun z => MvPolynomial.eval (fun i => a i z) p) =
      fun z => ∑ d ∈ p.support, p.coeff d *
        ∏ i ∈ d.support, a i z ^ d i := by
    funext z
    exact MvPolynomial.eval_eq _ _
  rw [heval]
  apply hasBooleanDegree_finset_sum
  intro d hd
  have hprod : HasBooleanDegree (∑ i ∈ d.support, d i)
      (fun z => ∏ i ∈ d.support, a i z ^ d i) := by
    apply hasBooleanDegree_finset_prod
    intro i hi
    simpa only [one_mul] using hasBooleanDegree_pow 1 (a i) (ha i) (d i)
  have hdegree : (∑ i ∈ d.support, d i) ≤ p.totalDegree :=
    MvPolynomial.le_totalDegree hd
  exact hasBooleanDegree_smul p.totalDegree (p.coeff d) _
    (hasBooleanDegree_mono hdegree hprod)

theorem hasBooleanDegree_eval_of_totalDegree_le {σ : Type*} (p : MvPolynomial σ ℝ)
    (a : σ → (V → Bool) → ℝ) (ha : ∀ i, HasBooleanDegree 1 (a i))
    (D : ℕ) (hp : p.totalDegree ≤ D) :
    HasBooleanDegree D (fun z => MvPolynomial.eval (fun i => a i z) p) :=
  hasBooleanDegree_mono hp (hasBooleanDegree_eval p a ha)

theorem hasBooleanDegree_booleanSign (v : V) :
    HasBooleanDegree 1 (fun z : V → Bool => booleanSign (z v)) := by
  have h := hasBooleanDegree_character (I := V) 1 {v} (by simp)
  convert h using 1
  funext z
  simp [cubeCharacter, booleanCharacter]

/-- Arbitrary affine coordinates on the real sign cube have Boolean degree one. -/
theorem hasBooleanDegree_affine (c : ℝ) (A : V → ℝ) :
    HasBooleanDegree 1 (fun z : V → Bool => c + ∑ v : V, A v * booleanSign (z v)) := by
  apply hasBooleanDegree_add
  · exact hasBooleanDegree_const 1 c
  · apply hasBooleanDegree_finset_sum
    intro v hv
    exact hasBooleanDegree_smul 1 (A v) _ (hasBooleanDegree_booleanSign v)

end DegreeCalculus

section ActualMap

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

theorem normalizedXorBooleanPoint_coordinate_degree (i j k : E → V) (v : Option V) :
    HasBooleanDegree 1 (fun z : V → Bool => normalizedXorBooleanPoint i j k z v) := by
  cases v with
  | none => exact hasBooleanDegree_const 1 _
  | some v =>
      have h := hasBooleanDegree_smul 1
        (Real.sqrt ((clauseOccurrenceCount i j k v : ℝ) + 1) /
          Real.sqrt (booleanMapDenominator (E := E) (V := V)))
        (fun z : V → Bool => booleanSign (z v)) (hasBooleanDegree_booleanSign v)
      convert h using 1
      funext z
      simp only [normalizedXorBooleanPoint, normalizedBooleanCoordinates]
      ring

theorem hasBooleanDegree_eval_normalizedXorBooleanPoint (i j k : E → V)
    (p : MvPolynomial (Option V) ℝ) :
    HasBooleanDegree p.totalDegree
      (fun z : V → Bool => MvPolynomial.eval (normalizedXorBooleanPoint i j k z) p) := by
  exact hasBooleanDegree_eval p (fun v z => normalizedXorBooleanPoint i j k z v)
    (normalizedXorBooleanPoint_coordinate_degree i j k)

theorem hasBooleanDegree_eval_normalizedXorBooleanPoint_of_totalDegree_le
    (i j k : E → V) (p : MvPolynomial (Option V) ℝ) (D : ℕ) (hp : p.totalDegree ≤ D) :
    HasBooleanDegree D
      (fun z : V → Bool => MvPolynomial.eval (normalizedXorBooleanPoint i j k z) p) :=
  hasBooleanDegree_mono hp (hasBooleanDegree_eval_normalizedXorBooleanPoint i j k p)

end ActualMap

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
