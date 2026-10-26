import OptimalConvergenceRates.SphereDimensionBounds.Foundation.ExpandingHypergraph
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.HypergraphBounds
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.TripleProbability
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.BoundaryMoments

/-! Unconditional finite existence of linearly expanding triple systems. -/

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators

theorem finite_half_sum_lt_one (s : ℕ) :
    (∑ a : Fin s, (1 / 2 : ℝ) ^ (a.val + 1)) < 1 := by
  have hsum : (∑ a ∈ Finset.range s, (1 / 2 : ℝ) ^ (a + 1)) =
      1 - (1 / 2 : ℝ) ^ s := by
    induction s with
    | zero => simp
    | succ s ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => (1 / 2 : ℝ) ^ (a + 1)) s, hsum]
  have hpos : 0 < (1 / 2 : ℝ) ^ s := by positivity
  linarith

/-- The exact finite union-bound budget is strictly smaller than the
sample space throughout the stated absolute small-set regime. -/
theorem tripleSystemCountingBudget_lt (N s : ℕ) (hN : 3 ≤ N)
    (hs : s * 2 ^ 48 ≤ N) :
    tripleSystemCountingBudget N s < N.choose 3 ^ (8 * N) := by
  have hden : 0 < (N.choose 3 : ℝ) ^ (8 * N) :=
    pow_pos (real_choose_three_pos N hN) _
  have hratio : (tripleSystemCountingBudget N s : ℝ) /
      (N.choose 3 : ℝ) ^ (8 * N) ≤
        ∑ a : Fin s, (1 / 2 : ℝ) ^ (a.val + 1) := by
    unfold tripleSystemCountingBudget
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_le_sum
    intro a ha
    have haS : a.val + 1 ≤ s := by omega
    have hsmall : (a.val + 1) * 2 ^ 48 ≤ N :=
      (Nat.mul_le_mul_right _ haS).trans hs
    have hav : a.val + 1 ≤ 7 * (a.val + 1) / 4 := by omega
    have hv : 7 * (a.val + 1) / 4 ≤ 2 * (a.val + 1) := by omega
    have hvfour : 4 * (7 * (a.val + 1) / 4) ≤ 7 * (a.val + 1) := by omega
    have hvN : 7 * (a.val + 1) / 4 ≤ N := by
      norm_num at hsmall
      omega
    have haN : a.val + 1 ≤ 8 * N := by
      norm_num at hsmall
      omega
    rw [normalized_triple_count N (a.val + 1) (7 * (a.val + 1) / 4) hN haN]
    exact small_support_union_bound N (a.val + 1) (7 * (a.val + 1) / 4)
      (by omega) hav hv hvfour hsmall
      ((7 * (a.val + 1) / 4).choose 3 / (N.choose 3 : ℝ))
      (by positivity) (choose_three_ratio_le_cube _ N hN hvN)
  have hlt : (tripleSystemCountingBudget N s : ℝ) /
      (N.choose 3 : ℝ) ^ (8 * N) < 1 :=
    hratio.trans_lt (finite_half_sum_lt_one s)
  have hreal : (tripleSystemCountingBudget N s : ℝ) <
      (N.choose 3 : ℝ) ^ (8 * N) := by
    simpa only [one_mul] using (div_lt_iff₀ hden).mp hlt
  exact_mod_cast hreal

theorem exists_tripleSystem_support_growth (N s : ℕ) (hN : 3 ≤ N)
    (hs : s * 2 ^ 48 ≤ N) :
    ∃ edge : Fin (8 * N) → Finset (Fin N),
      (∀ e, (edge e).card = 3) ∧
      ∀ A : Finset (Fin (8 * N)), A.Nonempty → A.card ≤ s →
        7 * A.card < 4 * (A.biUnion edge).card := by
  apply exists_tripleSystem_support_growth_of_budget N s
  · intro a
    have haS : a.val + 1 ≤ s := by omega
    have hsmall : (a.val + 1) * 2 ^ 48 ≤ N :=
      (Nat.mul_le_mul_right _ haS).trans hs
    norm_num at hsmall
    omega
  · exact tripleSystemCountingBudget_lt N s hN hs

theorem linear_boolean_level_ge_four (N : ℕ) (hN : 2 ^ 53 ≤ N) :
    4 ≤ N / 2 ^ 51 := by
  norm_num at hN ⊢
  omega

/-- This theorem has no unproved graph or probabilistic input. The number
of usable Boolean levels is a fixed positive fraction of the dimension. -/
theorem exists_linearLevel_expanding_triples (N : ℕ) (hN : 2 ^ 53 ≤ N) :
    ∃ edge : Fin (8 * N) → Finset (Fin N),
      (∀ e, (edge e).card = 3) ∧
        BoundaryExpansion (parityBoundary edge) (N / 2 ^ 51) := by
  have hN3 : 3 ≤ N := by norm_num at hN; omega
  have hs : (8 * (N / 2 ^ 51)) * 2 ^ 48 ≤ N := by
    calc
      (8 * (N / 2 ^ 51)) * 2 ^ 48 = (N / 2 ^ 51) * (8 * 2 ^ 48) := by ac_rfl
      _ = (N / 2 ^ 51) * 2 ^ 51 := by rw [show (8 : ℕ) * 2 ^ 48 = 2 ^ 51 by norm_num]
      _ ≤ N := Nat.div_mul_le_self N (2 ^ 51)
  obtain ⟨edge, htriple, hgrowth⟩ :=
    exists_tripleSystem_support_growth N (8 * (N / 2 ^ 51)) hN3 hs
  exact ⟨edge, htriple,
    boundaryExpansion_of_support_growth edge htriple (N / 2 ^ 51) hgrowth⟩

/-- One expanding triple system supports the required truncated functional
for every choice of square-one clause signs. Sound signs may be chosen after
the graph; the graph and level are independent of the sphere order. -/
theorem exists_linearLevel_hypergraphPseudoexpectations (N : ℕ) (hN : 2 ^ 53 ≤ N) :
    ∃ edge : Fin (8 * N) → Finset (Fin N),
      ∃ htriple : ∀ e, (edge e).card = 3,
      ∀ sign : Fin (8 * N) → ℝ, (∀ e, sign e ^ 2 = 1) →
        ∃ P : TruncatedBooleanPseudoexpectation (Fin N) (N / 2 ^ 51),
          (∀ e, P.functional
            ⟨cubeCharacter (edge e), hasBooleanDegree_character (2 * (N / 2 ^ 51)) _
              (by rw [htriple e]
                  have hK := linear_boolean_level_ge_four N hN
                  omega)⟩ = sign e) ∧
          ∀ (f : booleanDegreeSpace (I := Fin N) (2 * (N / 2 ^ 51))) (B : ℝ),
            (∀ x, |f.val x| ≤ B) → |P.functional f| ≤ cubeSize (Fin N) * B := by
  obtain ⟨edge, htriple, hexpand⟩ := exists_linearLevel_expanding_triples N hN
  refine ⟨edge, htriple, ?_⟩
  intro sign hsign
  have hK : 0 < N / 2 ^ 51 := by have h := linear_boolean_level_ge_four N hN; omega
  have hdegree (e : Fin (8 * N)) : (edge e).card ≤ 2 * (N / 2 ^ 51) := by
    rw [htriple]
    have h := linear_boolean_level_ge_four N hN
    omega
  exact exists_hypergraphPseudoexpectation edge (N / 2 ^ 51) hK sign hsign hexpand hdegree

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
