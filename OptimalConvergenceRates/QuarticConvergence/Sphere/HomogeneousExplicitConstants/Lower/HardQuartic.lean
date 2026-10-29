import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.HypergraphExistence
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.XorSoundness
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.BooleanPolynomial

/-!
# An unconditional hard quartic input at a linear Boolean level

The data selected here depend only on the dimension. Expansion is supplied
by the checked finite counting theorem, and sound labels are selected after
the graph. The polynomial and positive functional are explicit derived data.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

/-- Every indexed family of three-element sets admits consistent ordered,
pairwise distinct coordinate maps. -/
theorem exists_ordered_triple_maps {E V : Type*} [DecidableEq V]
    (edge : E → Finset V) (htriple : ∀ e, (edge e).card = 3) :
    ∃ i j k : E → V, (∀ e, i e ≠ j e) ∧ (∀ e, i e ≠ k e) ∧
      (∀ e, j e ≠ k e) ∧ edge = xorClauseEdge i j k := by
  classical
  have h : ∀ e : E, ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ edge e = {a, b, c} :=
    fun e ↦ Finset.card_eq_three.mp (htriple e)
  choose i j k hij hik hjk hedge using h
  refine ⟨i, j, k, hij, hik, hjk, ?_⟩
  funext e
  exact hedge e

/-- Pure finite input data. No polynomial nonnegativity, positive-functional
property, or negative-expectation conclusion is assumed in this structure. -/
structure HardQuarticData (N K : ℕ) where
  dimension_pos : 0 < N
  level_ge_two : 2 ≤ K
  first : Fin (8 * N) → Fin N
  second : Fin (8 * N) → Fin N
  third : Fin (8 * N) → Fin N
  first_ne_second : ∀ e, first e ≠ second e
  first_ne_third : ∀ e, first e ≠ third e
  second_ne_third : ∀ e, second e ≠ third e
  label : Fin (8 * N) → ℝ
  label_abs : ∀ e, |label e| = 1
  expansion : BoundaryExpansion (parityBoundary (xorClauseEdge first second third)) K
  soundness : ∀ σ : Fin N → ℝ, (∀ v, σ v ^ 2 = 1) →
    (Fintype.card (Fin (8 * N)) : ℝ) ≤ clauseSquareSum first second third label σ 1

/-- The hard finite input exists at every sufficiently large dimension, with
an absolute explicit Boolean level and no external lower-bound theorem. -/
theorem exists_hardQuarticData (N : ℕ) (hN : 2 ^ 53 ≤ N) :
    Nonempty (HardQuarticData N (N / 2 ^ 51)) := by
  obtain ⟨edge, htriple, hexpand⟩ := exists_linearLevel_expanding_triples N hN
  obtain ⟨i, j, k, hij, hik, hjk, hedge⟩ := exists_ordered_triple_maps edge htriple
  rw [hedge] at hexpand
  have hNpos : 0 < N := by norm_num at hN; omega
  have hK : 2 ≤ N / 2 ^ 51 := (by omega : 2 ≤ 4).trans (linear_boolean_level_ge_four N hN)
  obtain ⟨b, hb, hsound⟩ := exists_real_sound_xor_labels N hNpos i j k
  exact ⟨{
    dimension_pos := hNpos
    level_ge_two := hK
    first := i
    second := j
    third := k
    first_ne_second := hij
    first_ne_third := hik
    second_ne_third := hjk
    label := b
    label_abs := hb
    expansion := hexpand
    soundness := hsound
  }⟩

namespace HardQuarticData

variable {N K : ℕ} (D : HardQuarticData N K)

def polynomial : MvPolynomial (Option (Fin N)) ℝ :=
  normalizedQuarticPolynomial D.first D.second D.third D.label

def point (z : Fin N → Bool) : Option (Fin N) → ℝ :=
  normalizedXorBooleanPoint D.first D.second D.third z

def booleanFunction : (Fin N → Bool) → ℝ :=
  normalizedXorBooleanFunction D.first D.second D.third D.label

def pseudoexpectation : TruncatedBooleanPseudoexpectation (Fin N) K :=
  xorHypergraphPseudoexpectation D.first D.second D.third D.label D.label_abs K D.expansion

include D in
theorem edge_count_pos : 0 < Fintype.card (Fin (8 * N)) := by
  have hN := D.dimension_pos
  simpa only [Fintype.card_fin] using (by omega : 0 < 8 * N)

theorem polynomial_isHomogeneous : D.polynomial.IsHomogeneous 4 :=
  normalizedQuarticPolynomial_isHomogeneous D.first D.second D.third D.label

theorem polynomial_totalDegree_le : D.polynomial.totalDegree ≤ 4 :=
  normalizedQuarticPolynomial_totalDegree_le D.first D.second D.third D.label

theorem polynomial_nonneg (w : Option (Fin N) → ℝ) :
    0 ≤ MvPolynomial.eval w D.polynomial :=
  normalizedQuarticPolynomial_nonneg D.first D.second D.third D.label D.label_abs D.soundness w

theorem polynomial_le_one_on_ball (w : Option (Fin N) → ℝ)
    (hw : (∑ v : Option (Fin N), w v ^ 2) ≤ 1) :
    MvPolynomial.eval w D.polynomial ≤ 1 := by
  have hsplit : coordinateSquareSum (fun v ↦ w (some v)) + w none ^ 2 ≤ 1 := by
    simpa only [point, Fintype.sum_option, coordinateSquareSum, add_comm] using hw
  have hm : 8 ≤ Fintype.card (Fin (8 * N)) := by
    have hN := D.dimension_pos
    simp only [Fintype.card_fin]
    omega
  exact normalizedQuarticPolynomial_le_one D.first D.second D.third D.label
    D.label_abs hm w hsplit

theorem point_unit (z : Fin N → Bool) :
    (∑ v : Option (Fin N), D.point z v ^ 2) = 1 := by
  have h := normalizedXorBooleanPoint_unit D.first D.second D.third z D.edge_count_pos
  simpa only [point, Fintype.sum_option, coordinateSquareSum, add_comm] using h

theorem point_coordinate_degree (v : Option (Fin N)) :
    HasBooleanDegree 1 (fun z : Fin N → Bool ↦ D.point z v) :=
  normalizedXorBooleanPoint_coordinate_degree D.first D.second D.third v

theorem booleanFunction_eq_eval :
    D.booleanFunction = fun z : Fin N → Bool ↦ MvPolynomial.eval (D.point z) D.polynomial :=
  normalizedXorBooleanFunction_eq_eval D.first D.second D.third D.label

theorem booleanFunction_degree : HasBooleanDegree 3 D.booleanFunction :=
  normalizedXorBooleanFunction_degree D.first D.second D.third D.label D.label_abs
    D.first_ne_second D.first_ne_third D.second_ne_third D.edge_count_pos

theorem booleanFunction_degree_truncated : HasBooleanDegree (2 * K) D.booleanFunction :=
  hasBooleanDegree_mono (by have hK := D.level_ge_two; omega : 3 ≤ 2 * K) D.booleanFunction_degree

def booleanElement : booleanDegreeSpace (I := Fin N) (2 * K) :=
  ⟨D.booleanFunction, D.booleanFunction_degree_truncated⟩

/-- The actual positive functional evaluates the actual polynomial at a
unit Boolean affine map to an explicit negative value. -/
theorem negative_value : D.pseudoexpectation.functional D.booleanElement =
    -(1 / (8712 * (N : ℝ))) := by
  exact xorHypergraphPseudoexpectation_normalizedXor_density N D.dimension_pos
    D.first D.second D.third D.label D.label_abs D.first_ne_second D.first_ne_third
    D.second_ne_third K D.level_ge_two D.expansion

end HardQuarticData

/-- The complete hard quartic input exists unconditionally. The same
polynomial, map, and functional are selected independently of any sphere
relaxation order. The remaining sphere transfer is a separate theorem. -/
theorem exists_hard_quartic_input (N : ℕ) (hN : 2 ^ 53 ≤ N) :
    ∃ D : HardQuarticData N (N / 2 ^ 51),
      D.polynomial.IsHomogeneous 4 ∧
      (∀ w : Option (Fin N) → ℝ, 0 ≤ MvPolynomial.eval w D.polynomial) ∧
      (∀ w : Option (Fin N) → ℝ, (∑ v : Option (Fin N), w v ^ 2) ≤ 1 →
        MvPolynomial.eval w D.polynomial ≤ 1) ∧
      (∀ z : Fin N → Bool, (∑ v : Option (Fin N), D.point z v ^ 2) = 1) ∧
      HasBooleanDegree 3 D.booleanFunction ∧
      D.pseudoexpectation.functional D.booleanElement = -(1 / (8712 * (N : ℝ))) := by
  obtain ⟨D⟩ := exists_hardQuarticData N hN
  exact ⟨D, D.polynomial_isHomogeneous, D.polynomial_nonneg, D.polynomial_le_one_on_ball,
    D.point_unit, D.booleanFunction_degree, D.negative_value⟩

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
