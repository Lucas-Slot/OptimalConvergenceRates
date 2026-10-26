import OptimalConvergenceRates.SphereDimensionBounds.Foundation.QuarticNormalization
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.BoundaryMoments

/-!
# The exact negative Boolean value of the normalized quartic

The moment functional below is the checked Fourier functional. Its negative
value is derived from its normalization and individual clause moments.
-/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

section XorMoments

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

def xorClauseEdge (i j k : E → V) (e : E) : Finset V := {i e, j e, k e}

omit [Fintype E] [Fintype V] in
theorem xorClauseEdge_card_le (i j k : E → V) (e : E) :
    (xorClauseEdge i j k e).card ≤ 3 := by
  unfold xorClauseEdge
  calc
    ({i e, j e, k e} : Finset V).card ≤ ({j e, k e} : Finset V).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (({k e} : Finset V).card + 1) + 1 :=
      Nat.add_le_add_right (Finset.card_insert_le _ _) 1
    _ = 3 := by simp

omit [Fintype E] [Fintype V] in
theorem cubeCharacter_xorClauseEdge (i j k : E → V) (e : E)
    (hij : i e ≠ j e) (hik : i e ≠ k e) (hjk : j e ≠ k e) (z : V → Bool) :
    cubeCharacter (xorClauseEdge i j k e) z =
      booleanSign (z (i e)) * booleanSign (z (j e)) * booleanSign (z (k e)) := by
  simp [cubeCharacter, booleanCharacter, xorClauseEdge, hij, hik, hjk, mul_assoc]

theorem sign_clause_square_expansion (a b c label : ℝ)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1) (hlabel : label ^ 2 = 1) :
    (a * b - label * c) ^ 2 = 2 - 2 * label * (a * b * c) := by
  calc
    (a * b - label * c) ^ 2 =
        a ^ 2 * b ^ 2 + label ^ 2 * c ^ 2 - 2 * label * (a * b * c) := by ring
    _ = 2 - 2 * label * (a * b * c) := by rw [ha, hb, hc, hlabel]; ring

omit [Fintype E] [Fintype V] in
theorem boolean_xor_clause_expansion (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (e : E)
    (hij : i e ≠ j e) (hik : i e ≠ k e) (hjk : j e ≠ k e) :
    (fun z : V → Bool =>
      (booleanSign (z (i e)) * booleanSign (z (j e)) - b e * booleanSign (z (k e))) ^ 2) =
      fun z => 2 - (2 * b e) * cubeCharacter (xorClauseEdge i j k e) z := by
  funext z
  have hbsq : b e ^ 2 = 1 := by rw [← sq_abs, hb e]; norm_num
  rw [sign_clause_square_expansion _ _ _ _ (booleanSign_sq _) (booleanSign_sq _)
    (booleanSign_sq _) hbsq, cubeCharacter_xorClauseEdge i j k e hij hik hjk]

omit [Fintype E] in
theorem xor_booleanMomentFunctional_const (moment : Finset V → ℝ) (c : ℝ) :
    booleanMomentFunctional moment (fun _ : V → Bool => c) = c * moment ∅ := by
  simpa only [mul_one, booleanMomentFunctional_one] using
    booleanMomentFunctional_smul moment c (fun _ : V → Bool => 1)

omit [Fintype E] in
theorem booleanMomentFunctional_clause_square_zero (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (moment : Finset V → ℝ) (hnorm : moment ∅ = 1)
    (e : E) (hmoment : moment (xorClauseEdge i j k e) = b e)
    (hij : i e ≠ j e) (hik : i e ≠ k e) (hjk : j e ≠ k e) :
    booleanMomentFunctional moment (fun z : V → Bool =>
      (booleanSign (z (i e)) * booleanSign (z (j e)) - b e * booleanSign (z (k e))) ^ 2) = 0 := by
  rw [boolean_xor_clause_expansion i j k b hb e hij hik hjk]
  change booleanMomentFunctional moment
    ((fun _ : V → Bool => (2 : ℝ)) - (2 * b e) • cubeCharacter (xorClauseEdge i j k e)) = 0
  rw [map_sub, map_smul, xor_booleanMomentFunctional_const,
    booleanMomentFunctional_character, hnorm, hmoment]
  have hbsq : b e ^ 2 = 1 := by rw [← sq_abs, hb e]; norm_num
  change 2 * 1 - (2 * b e) * b e = 0
  nlinarith

theorem booleanMomentFunctional_clauseSquareSum_zero (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (moment : Finset V → ℝ) (hnorm : moment ∅ = 1)
    (hmoment : ∀ e, moment (xorClauseEdge i j k e) = b e)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e) :
    booleanMomentFunctional moment
      (fun z : V → Bool => clauseSquareSum i j k b (fun v => booleanSign (z v)) 1) = 0 := by
  simp only [clauseSquareSum, mul_one]
  rw [booleanMomentFunctional_sum]
  apply Finset.sum_eq_zero
  intro e he
  exact booleanMomentFunctional_clause_square_zero i j k b hb moment hnorm e
    (hmoment e) (hij e) (hik e) (hjk e)

def normalizedXorBooleanFunction (i j k : E → V) (b : E → ℝ) : (V → Bool) → ℝ :=
  fun z => normalizedQuartic i j k b
    (normalizedBooleanCoordinates i j k (fun v => booleanSign (z v)))
    (normalizedBooleanLastCoordinate (E := E) (V := V))

theorem normalizedXorBooleanFunction_formula (i j k : E → V) (b : E → ℝ)
    (hm : 0 < Fintype.card E) :
    normalizedXorBooleanFunction i j k b = fun z : V → Bool =>
      (clauseSquareSum i j k b (fun v => booleanSign (z v)) 1 - (Fintype.card E : ℝ) / 4) /
        (16 * booleanMapDenominator (E := E) (V := V) ^ 2) := by
  funext z
  exact normalizedBooleanMap_eval i j k b (fun v => booleanSign (z v))
    (fun v => booleanSign_sq _) hm

theorem booleanMomentFunctional_normalizedXor (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (moment : Finset V → ℝ) (hnorm : moment ∅ = 1)
    (hmoment : ∀ e, moment (xorClauseEdge i j k e) = b e)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e)
    (hm : 0 < Fintype.card E) :
    booleanMomentFunctional moment (normalizedXorBooleanFunction i j k b) =
      -(Fintype.card E : ℝ) /
        (64 * booleanMapDenominator (E := E) (V := V) ^ 2) := by
  rw [normalizedXorBooleanFunction_formula i j k b hm]
  have hfun :
      (fun z : V → Bool =>
        (clauseSquareSum i j k b (fun v => booleanSign (z v)) 1 - (Fintype.card E : ℝ) / 4) /
          (16 * booleanMapDenominator (E := E) (V := V) ^ 2)) =
        (1 / (16 * booleanMapDenominator (E := E) (V := V) ^ 2)) •
          ((fun z : V → Bool => clauseSquareSum i j k b (fun v => booleanSign (z v)) 1) -
            (fun _ : V → Bool => (Fintype.card E : ℝ) / 4)) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring
  rw [hfun, map_smul, map_sub,
    booleanMomentFunctional_clauseSquareSum_zero i j k b hb moment hnorm hmoment hij hik hjk,
    xor_booleanMomentFunctional_const, hnorm]
  simp only [smul_eq_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem booleanMomentFunctional_normalizedXor_density (N : ℕ) (hN : 0 < N)
    (i j k : Fin (8 * N) → Fin N) (b : Fin (8 * N) → ℝ)
    (hb : ∀ e, |b e| = 1) (moment : Finset (Fin N) → ℝ) (hnorm : moment ∅ = 1)
    (hmoment : ∀ e, moment (xorClauseEdge i j k e) = b e)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e) :
    booleanMomentFunctional moment (normalizedXorBooleanFunction i j k b) =
      -(1 / (8712 * (N : ℝ))) := by
  have hm : 0 < Fintype.card (Fin (8 * N)) := by simpa using (by omega : 0 < 8 * N)
  rw [booleanMomentFunctional_normalizedXor i j k b hb moment hnorm hmoment hij hik hjk hm]
  simp only [booleanMapDenominator, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  exact positive_weight_gap_density_arithmetic (N : ℝ) (by exact_mod_cast Nat.ne_of_gt hN)

omit [Fintype E] in
theorem xor_hasBooleanDegree_const (d : ℕ) (c : ℝ) :
    HasBooleanDegree d (fun _ : V → Bool => c) := by
  have h := (booleanDegreeSpace (I := V) d).smul_mem c (hasBooleanDegree_one d)
  change HasBooleanDegree d (c • (fun _ : V → Bool => (1 : ℝ))) at h
  simpa only [Pi.smul_def, smul_eq_mul, mul_one] using h

omit [Fintype E] in
theorem xor_hasBooleanDegree_mono {d t : ℕ} {f : (V → Bool) → ℝ}
    (hdt : d ≤ t) (hf : HasBooleanDegree d f) : HasBooleanDegree t f := by
  intro S hS
  exact hf S (lt_of_le_of_lt hdt hS)

omit [Fintype E] in
theorem boolean_xor_clause_degree (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (e : E)
    (hij : i e ≠ j e) (hik : i e ≠ k e) (hjk : j e ≠ k e) :
    HasBooleanDegree 3 (fun z : V → Bool =>
      (booleanSign (z (i e)) * booleanSign (z (j e)) - b e * booleanSign (z (k e))) ^ 2) := by
  rw [boolean_xor_clause_expansion i j k b hb e hij hik hjk]
  exact (booleanDegreeSpace (I := V) 3).sub_mem (xor_hasBooleanDegree_const 3 2)
    ((booleanDegreeSpace (I := V) 3).smul_mem (2 * b e)
      (hasBooleanDegree_character 3 (xorClauseEdge i j k e) (xorClauseEdge_card_le i j k e)))

theorem boolean_clauseSquareSum_degree (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e) :
    HasBooleanDegree 3
      (fun z : V → Bool => clauseSquareSum i j k b (fun v => booleanSign (z v)) 1) := by
  have hsum : (∑ e : E, (fun z : V → Bool =>
      (booleanSign (z (i e)) * booleanSign (z (j e)) - b e * booleanSign (z (k e))) ^ 2)) ∈
        booleanDegreeSpace (I := V) 3 := by
    exact (booleanDegreeSpace (I := V) 3).sum_mem
      (fun e he => boolean_xor_clause_degree i j k b hb e (hij e) (hik e) (hjk e))
  change (fun z : V → Bool => clauseSquareSum i j k b (fun v => booleanSign (z v)) 1) ∈
    booleanDegreeSpace (I := V) 3
  convert hsum using 1
  funext z
  simp only [Finset.sum_apply, clauseSquareSum, mul_one]

theorem normalizedXorBooleanFunction_degree (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e)
    (hm : 0 < Fintype.card E) : HasBooleanDegree 3 (normalizedXorBooleanFunction i j k b) := by
  rw [normalizedXorBooleanFunction_formula i j k b hm]
  have hsub := (booleanDegreeSpace (I := V) 3).sub_mem
    (boolean_clauseSquareSum_degree i j k b hb hij hik hjk)
    (xor_hasBooleanDegree_const 3 ((Fintype.card E : ℝ) / 4))
  have hscale := (booleanDegreeSpace (I := V) 3).smul_mem
    (1 / (16 * booleanMapDenominator (E := E) (V := V) ^ 2)) hsub
  change (fun z : V → Bool =>
    (clauseSquareSum i j k b (fun v => booleanSign (z v)) 1 - (Fintype.card E : ℝ) / 4) /
      (16 * booleanMapDenominator (E := E) (V := V) ^ 2)) ∈ booleanDegreeSpace (I := V) 3
  convert hscale using 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

def normalizedXorBooleanPoint (i j k : E → V) (z : V → Bool) : Option V → ℝ
  | some v => normalizedBooleanCoordinates i j k (fun w => booleanSign (z w)) v
  | none => normalizedBooleanLastCoordinate (E := E) (V := V)

/-- The Boolean function is evaluation of the actual normalized polynomial. -/
theorem normalizedXorBooleanFunction_eq_eval (i j k : E → V) (b : E → ℝ) :
    normalizedXorBooleanFunction i j k b = fun z : V → Bool =>
      MvPolynomial.eval (normalizedXorBooleanPoint i j k z) (normalizedQuarticPolynomial i j k b) := by
  funext z
  rw [normalizedQuarticPolynomial_eval]
  rfl

theorem normalizedXorBooleanPoint_unit (i j k : E → V) (z : V → Bool)
    (hm : 0 < Fintype.card E) :
    coordinateSquareSum (fun v => normalizedXorBooleanPoint i j k z (some v)) +
      normalizedXorBooleanPoint i j k z none ^ 2 = 1 := by
  exact normalizedBooleanMap_unit i j k (fun v => booleanSign (z v))
    (fun v => booleanSign_sq _) hm

theorem normalizedXorBooleanFunction_degree_truncated (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e)
    (hm : 0 < Fintype.card E) (K : ℕ) (hK : 2 ≤ K) :
    HasBooleanDegree (2 * K) (normalizedXorBooleanFunction i j k b) := by
  exact xor_hasBooleanDegree_mono (by omega : 3 ≤ 2 * K)
    (normalizedXorBooleanFunction_degree i j k b hb hij hik hjk hm)

variable [DecidableEq E]

theorem boundaryMoment_normalizedXor (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e)
    (hm : 0 < Fintype.card E) (K : ℕ) (hK : 0 < K)
    (expand : BoundaryExpansion (parityBoundary (xorClauseEdge i j k)) K) :
    booleanMomentFunctional (boundaryMoment (parityBoundary (xorClauseEdge i j k)) K b)
        (normalizedXorBooleanFunction i j k b) =
      -(Fintype.card E : ℝ) /
        (64 * booleanMapDenominator (E := E) (V := V) ^ 2) := by
  apply booleanMomentFunctional_normalizedXor i j k b hb _ _ _ hij hik hjk hm
  · exact boundaryMoment_empty (parityBoundary (xorClauseEdge i j k)) K b
      (parityBoundary_empty _) (parityBoundary_symmDiff _) expand
  · intro e
    exact parityBoundaryMoment_clause (xorClauseEdge i j k) K hK b expand e

/-- This is the actual positive functional obtained from the boundary Gram
construction; its negative value is proved below rather than assumed. -/
def xorHypergraphPseudoexpectation (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (K : ℕ)
    (expand : BoundaryExpansion (parityBoundary (xorClauseEdge i j k)) K) :
    TruncatedBooleanPseudoexpectation V K :=
  hypergraphPseudoexpectation (xorClauseEdge i j k) K b
    (fun e => by rw [← sq_abs, hb e]; norm_num) expand

theorem xorHypergraphPseudoexpectation_normalizedXor (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e)
    (hm : 0 < Fintype.card E) (K : ℕ) (hK : 2 ≤ K)
    (expand : BoundaryExpansion (parityBoundary (xorClauseEdge i j k)) K) :
    (xorHypergraphPseudoexpectation i j k b hb K expand).functional
      ⟨normalizedXorBooleanFunction i j k b,
        normalizedXorBooleanFunction_degree_truncated i j k b hb hij hik hjk hm K hK⟩ =
      -(Fintype.card E : ℝ) /
        (64 * booleanMapDenominator (E := E) (V := V) ^ 2) := by
  change booleanMomentFunctional (boundaryMoment (parityBoundary (xorClauseEdge i j k)) K b)
    (normalizedXorBooleanFunction i j k b) = _
  exact boundaryMoment_normalizedXor i j k b hb hij hik hjk hm K (by omega) expand

theorem xorHypergraphPseudoexpectation_normalizedXor_density (N : ℕ) (hN : 0 < N)
    (i j k : Fin (8 * N) → Fin N) (b : Fin (8 * N) → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hij : ∀ e, i e ≠ j e) (hik : ∀ e, i e ≠ k e) (hjk : ∀ e, j e ≠ k e)
    (K : ℕ) (hK : 2 ≤ K)
    (expand : BoundaryExpansion (parityBoundary (xorClauseEdge i j k)) K) :
    (xorHypergraphPseudoexpectation i j k b hb K expand).functional
      ⟨normalizedXorBooleanFunction i j k b,
        normalizedXorBooleanFunction_degree_truncated i j k b hb hij hik hjk
          (by simpa using (by omega : 0 < 8 * N)) K hK⟩ =
      -(1 / (8712 * (N : ℝ))) := by
  have hm : 0 < Fintype.card (Fin (8 * N)) := by simpa using (by omega : 0 < 8 * N)
  rw [xorHypergraphPseudoexpectation_normalizedXor i j k b hb hij hik hjk hm K hK expand]
  simp only [booleanMapDenominator, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  exact positive_weight_gap_density_arithmetic (N : ℝ) (by exact_mod_cast Nat.ne_of_gt hN)

end XorMoments

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
