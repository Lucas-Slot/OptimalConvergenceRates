import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.QuarticConstruction

/-!
# Positive occurrence weights for the quartic construction

We use the weights `d_v + 1`, scale the last coordinate by `sqrt |E|`,
and divide the quartic by `16`. This preserves unused coordinates and
avoids any case split on zero occurrence counts.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

section Normalization

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

def coordinateSquareSum (X : V → ℝ) : ℝ := ∑ v : V, X v ^ 2

omit [Fintype E] [DecidableEq V] in
theorem coordinateSquareSum_nonneg (X : V → ℝ) : 0 ≤ coordinateSquareSum X := by
  exact Finset.sum_nonneg fun v hv ↦ sq_nonneg _

omit [Fintype E] [DecidableEq V] in
theorem coordinate_sq_le_squareSum (X : V → ℝ) (v : V) :
    X v ^ 2 ≤ coordinateSquareSum X := by
  exact Finset.single_le_sum (fun w hw ↦ sq_nonneg (X w)) (Finset.mem_univ v)

def positiveWeightCoordinate (i j k : E → V) (X : V → ℝ) (v : V) : ℝ :=
  X v / Real.sqrt ((clauseOccurrenceCount i j k v : ℝ) + 1)

omit [Fintype V] in
theorem positiveWeightCoordinate_sq_identity (i j k : E → V) (X : V → ℝ) (v : V) :
    ((clauseOccurrenceCount i j k v : ℝ) + 1) *
      positiveWeightCoordinate i j k X v ^ 2 = X v ^ 2 := by
  have hd : 0 < (clauseOccurrenceCount i j k v : ℝ) + 1 := by positivity
  simp only [positiveWeightCoordinate, div_pow, Real.sq_sqrt hd.le]
  field_simp

omit [Fintype V] in
theorem positiveWeightCoordinate_sq_le (i j k : E → V) (X : V → ℝ) (v : V) :
    positiveWeightCoordinate i j k X v ^ 2 ≤ X v ^ 2 := by
  have hid := positiveWeightCoordinate_sq_identity i j k X v
  have hw := mul_nonneg (Nat.cast_nonneg (clauseOccurrenceCount i j k v) :
      (0 : ℝ) ≤ (clauseOccurrenceCount i j k v : ℝ))
    (sq_nonneg (positiveWeightCoordinate i j k X v))
  nlinarith

omit [Fintype V] in
theorem positiveWeightCoordinate_weighted_sq_le (i j k : E → V)
    (X : V → ℝ) (v : V) :
    (clauseOccurrenceCount i j k v : ℝ) *
      positiveWeightCoordinate i j k X v ^ 2 ≤ X v ^ 2 := by
  have hid := positiveWeightCoordinate_sq_identity i j k X v
  nlinarith [sq_nonneg (positiveWeightCoordinate i j k X v)]

theorem positiveWeightCoordinate_sum_sq_le (i j k : E → V) (X : V → ℝ) :
    (∑ v : V, positiveWeightCoordinate i j k X v ^ 2) ≤ coordinateSquareSum X := by
  exact Finset.sum_le_sum fun v hv ↦ positiveWeightCoordinate_sq_le i j k X v

theorem positiveWeightCoordinate_weighted_sum_sq_le (i j k : E → V) (X : V → ℝ) :
    (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) *
      positiveWeightCoordinate i j k X v ^ 2) ≤ coordinateSquareSum X := by
  exact Finset.sum_le_sum fun v hv ↦ positiveWeightCoordinate_weighted_sq_le i j k X v

theorem first_position_sum_le_occurrences (i j k : E → V) (f : V → ℝ)
    (hf : ∀ v, 0 ≤ f v) :
    (∑ e : E, f (i e)) ≤ ∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * f v := by
  rw [clauseOccurrenceCount_sum]
  apply Finset.sum_le_sum
  intro e he
  linarith [hf (j e), hf (k e)]

theorem third_position_sum_le_occurrences (i j k : E → V) (f : V → ℝ)
    (hf : ∀ v, 0 ≤ f v) :
    (∑ e : E, f (k e)) ≤ ∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * f v := by
  rw [clauseOccurrenceCount_sum]
  apply Finset.sum_le_sum
  intro e he
  linarith [hf (i e), hf (j e)]

/-- A generic clause upper estimate using a bound on coordinates and the
occurrence-weighted squared norm. -/
theorem clauseSquareSum_upper (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (x : V → ℝ) (t S : ℝ) (hS : 0 ≤ S)
    (hcoord : ∀ v, x v ^ 2 ≤ S)
    (hweighted : (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * x v ^ 2) ≤ S) :
    clauseSquareSum i j k b x t ≤ 2 * S ^ 2 + 2 * t ^ 2 * S := by
  have hfirst : (∑ e : E, x (i e) ^ 2) ≤ S :=
    (first_position_sum_le_occurrences i j k (fun v ↦ x v ^ 2)
      (fun v ↦ sq_nonneg _)).trans hweighted
  have hthird : (∑ e : E, x (k e) ^ 2) ≤ S :=
    (third_position_sum_le_occurrences i j k (fun v ↦ x v ^ 2)
      (fun v ↦ sq_nonneg _)).trans hweighted
  calc
    clauseSquareSum i j k b x t ≤
        ∑ e : E, (2 * S * x (i e) ^ 2 + 2 * t ^ 2 * x (k e) ^ 2) := by
      apply Finset.sum_le_sum
      intro e he
      have hbsq : b e ^ 2 = 1 := by
        rw [← sq_abs, hb e]
        norm_num
      have hpoint : (x (i e) * x (j e) - b e * x (k e) * t) ^ 2 ≤
          2 * (x (i e) * x (j e)) ^ 2 + 2 * (b e * x (k e) * t) ^ 2 := by
        nlinarith [sq_nonneg (x (i e) * x (j e) + b e * x (k e) * t)]
      have hprod := mul_le_mul_of_nonneg_left (hcoord (j e)) (sq_nonneg (x (i e)))
      simp only [mul_pow, hbsq, one_mul] at hpoint
      nlinarith
    _ = 2 * S * (∑ e : E, x (i e) ^ 2) +
        2 * t ^ 2 * (∑ e : E, x (k e) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * S ^ 2 + 2 * t ^ 2 * S := by
      have h₁ := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 2 * S)
      have h₃ := mul_le_mul_of_nonneg_left hthird (by positivity : 0 ≤ 2 * t ^ 2)
      nlinarith

theorem weighted_fourth_sum_upper (i j k : E → V) (x : V → ℝ) (S : ℝ)
    (hS : 0 ≤ S) (hcoord : ∀ v, x v ^ 2 ≤ S)
    (hweighted : (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * x v ^ 2) ≤ S) :
    (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * x v ^ 4) ≤ S ^ 2 := by
  calc
    (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * x v ^ 4) ≤
        ∑ v : V, S * ((clauseOccurrenceCount i j k v : ℝ) * x v ^ 2) := by
      apply Finset.sum_le_sum
      intro v hv
      have hh := mul_le_mul_of_nonneg_left (hcoord v)
        (mul_nonneg (Nat.cast_nonneg (clauseOccurrenceCount i j k v) :
          (0 : ℝ) ≤ (clauseOccurrenceCount i j k v : ℝ)) (sq_nonneg (x v)))
      nlinarith
    _ = S * (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * x v ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ S ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hweighted hS]

theorem occurrencePenalty_upper (i j k : E → V) (x : V → ℝ) (t S : ℝ)
    (hS : 0 ≤ S) (hcoord : ∀ v, x v ^ 2 ≤ S)
    (hweighted : (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * x v ^ 2) ≤ S) :
    occurrencePenalty i j k x t ≤
      2 * S ^ 2 + 6 * (Fintype.card E : ℝ) * t ^ 4 := by
  calc
    occurrencePenalty i j k x t ≤
        ∑ v : V, (2 * ((clauseOccurrenceCount i j k v : ℝ) * x v ^ 4) +
          2 * t ^ 4 * (clauseOccurrenceCount i j k v : ℝ)) := by
      apply Finset.sum_le_sum
      intro v hv
      have hh : (x v ^ 2 - t ^ 2) ^ 2 ≤ 2 * x v ^ 4 + 2 * t ^ 4 := by
        nlinarith [sq_nonneg (x v ^ 2 + t ^ 2)]
      have hmul := mul_le_mul_of_nonneg_left hh
        (Nat.cast_nonneg (clauseOccurrenceCount i j k v) :
          (0 : ℝ) ≤ (clauseOccurrenceCount i j k v : ℝ))
      nlinarith
    _ = 2 * (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * x v ^ 4) +
        6 * (Fintype.card E : ℝ) * t ^ 4 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        clauseOccurrenceCount_total]
      ring
    _ ≤ 2 * S ^ 2 + 6 * (Fintype.card E : ℝ) * t ^ 4 := by
      linarith [weighted_fourth_sum_upper i j k x S hS hcoord hweighted]

theorem xorQuartic_upper (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (x : V → ℝ) (t S : ℝ) (hS : 0 ≤ S)
    (hcoord : ∀ v, x v ^ 2 ≤ S)
    (hweighted : (∑ v : V, (clauseOccurrenceCount i j k v : ℝ) * x v ^ 2) ≤ S) :
    xorQuartic i j k b x t ≤
      14 * S ^ 2 + 2 * t ^ 2 * S + 36 * (Fintype.card E : ℝ) * t ^ 4 := by
  have hclause := clauseSquareSum_upper i j k b hb x t S hS hcoord hweighted
  have hpenalty := occurrencePenalty_upper i j k x t S hS hcoord hweighted
  have hnegative : 0 ≤ (Fintype.card E : ℝ) / 4 * t ^ 4 := by positivity
  unfold xorQuartic
  linarith

theorem normalization_scalar_absorption (F S u t m : ℝ)
    (hS : 0 ≤ S) (hu : 0 ≤ u) (hm : 8 ≤ m) (ht : m * t ^ 2 = u)
    (hF : F ≤ 14 * S ^ 2 + 2 * t ^ 2 * S + 36 * m * t ^ 4) :
    F ≤ 16 * (S + u) ^ 2 := by
  have hm₀ : 0 ≤ m := by linarith
  have ht₀ := sq_nonneg t
  have ht₄ : 0 ≤ t ^ 4 := by positivity
  have htu : t ^ 2 ≤ u := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ m - 1) ht₀]
  have htuS := mul_le_mul_of_nonneg_right htu hS
  have hpower : (m * t ^ 2) ^ 2 = u ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) ht
  have hfourth := mul_le_mul_of_nonneg_right hm (mul_nonneg hm₀ ht₄)
  nlinarith [sq_nonneg S, sq_nonneg u, mul_nonneg hS hu]

def normalizedQuartic (i j k : E → V) (b : E → ℝ) (X : V → ℝ) (T : ℝ) : ℝ :=
  xorQuartic i j k b (positiveWeightCoordinate i j k X)
    (T / Real.sqrt (Fintype.card E : ℝ)) / 16

theorem normalized_last_sq_identity (T m : ℝ) (hm : 0 < m) :
    m * (T / Real.sqrt m) ^ 2 = T ^ 2 := by
  rw [div_pow, Real.sq_sqrt hm.le]
  field_simp

theorem normalizedQuartic_le_one (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (hm : 8 ≤ Fintype.card E)
    (X : V → ℝ) (T : ℝ) (hnorm : coordinateSquareSum X + T ^ 2 ≤ 1) :
    normalizedQuartic i j k b X T ≤ 1 := by
  have hmreal : (8 : ℝ) ≤ (Fintype.card E : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (Fintype.card E : ℝ) := by linarith
  have hS := coordinateSquareSum_nonneg X
  have hcoord : ∀ v, positiveWeightCoordinate i j k X v ^ 2 ≤ coordinateSquareSum X :=
    fun v ↦ (positiveWeightCoordinate_sq_le i j k X v).trans
      (coordinate_sq_le_squareSum X v)
  have hupper := xorQuartic_upper i j k b hb (positiveWeightCoordinate i j k X)
    (T / Real.sqrt (Fintype.card E : ℝ)) (coordinateSquareSum X) hS hcoord
    (positiveWeightCoordinate_weighted_sum_sq_le i j k X)
  have habsorb := normalization_scalar_absorption _ (coordinateSquareSum X) (T ^ 2)
    (T / Real.sqrt (Fintype.card E : ℝ)) (Fintype.card E : ℝ) hS (sq_nonneg T)
    hmreal (normalized_last_sq_identity T _ hmpos) hupper
  have htotal : 0 ≤ coordinateSquareSum X + T ^ 2 := add_nonneg hS (sq_nonneg T)
  unfold normalizedQuartic
  nlinarith

theorem normalizedQuartic_nonneg (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hsound : ∀ σ : V → ℝ, (∀ v, σ v ^ 2 = 1) →
      (Fintype.card E : ℝ) ≤ clauseSquareSum i j k b σ 1)
    (X : V → ℝ) (T : ℝ) : 0 ≤ normalizedQuartic i j k b X T := by
  exact div_nonneg (xorQuartic_nonneg i j k b hb hsound _ _) (by norm_num)

def booleanMapDenominator : ℝ := 4 * (Fintype.card E : ℝ) + (Fintype.card V : ℝ)

def normalizedBooleanCoordinates (i j k : E → V) (z : V → ℝ) (v : V) : ℝ :=
  Real.sqrt ((clauseOccurrenceCount i j k v : ℝ) + 1) * z v /
    Real.sqrt (booleanMapDenominator (E := E) (V := V))

def normalizedBooleanLastCoordinate : ℝ :=
  Real.sqrt (Fintype.card E : ℝ) /
    Real.sqrt (booleanMapDenominator (E := E) (V := V))

omit [DecidableEq V] in
theorem booleanMapDenominator_pos (hm : 0 < Fintype.card E) :
    0 < booleanMapDenominator (E := E) (V := V) := by
  unfold booleanMapDenominator
  positivity

/-- The new Boolean affine map has exactly unit norm, even with unused variables. -/
theorem normalizedBooleanMap_unit (i j k : E → V) (z : V → ℝ)
    (hz : ∀ v, z v ^ 2 = 1) (hm : 0 < Fintype.card E) :
    coordinateSquareSum (normalizedBooleanCoordinates i j k z) +
      normalizedBooleanLastCoordinate (E := E) (V := V) ^ 2 = 1 := by
  have hD := booleanMapDenominator_pos (V := V) hm
  have hcoords : ∀ v, normalizedBooleanCoordinates i j k z v ^ 2 =
      ((clauseOccurrenceCount i j k v : ℝ) + 1) /
        booleanMapDenominator (E := E) (V := V) := by
    intro v
    simp only [normalizedBooleanCoordinates, div_pow, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ (clauseOccurrenceCount i j k v : ℝ) + 1),
      Real.sq_sqrt hD.le, hz v, mul_one]
  have hlast : normalizedBooleanLastCoordinate (E := E) (V := V) ^ 2 =
      (Fintype.card E : ℝ) / booleanMapDenominator (E := E) (V := V) := by
    simp only [normalizedBooleanLastCoordinate, div_pow,
      Real.sq_sqrt (Nat.cast_nonneg (Fintype.card E)), Real.sq_sqrt hD.le]
  unfold coordinateSquareSum
  simp_rw [hcoords]
  rw [← Finset.sum_div, hlast, Finset.sum_add_distrib, clauseOccurrenceCount_total]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  unfold booleanMapDenominator
  field_simp; ring

theorem positiveWeightCoordinate_booleanMap (i j k : E → V) (z : V → ℝ)
    (v : V) (hm : 0 < Fintype.card E) :
    positiveWeightCoordinate i j k (normalizedBooleanCoordinates i j k z) v =
      z v / Real.sqrt (booleanMapDenominator (E := E) (V := V)) := by
  have hw : 0 < (clauseOccurrenceCount i j k v : ℝ) + 1 := by positivity
  have hD := booleanMapDenominator_pos (V := V) hm
  unfold positiveWeightCoordinate normalizedBooleanCoordinates
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hw), ne_of_gt (Real.sqrt_pos.mpr hD)] <;> ring

omit [DecidableEq V] in
theorem normalizedBooleanLastCoordinate_div_sqrt (hm : 0 < Fintype.card E) :
    normalizedBooleanLastCoordinate (E := E) (V := V) /
        Real.sqrt (Fintype.card E : ℝ) =
      1 / Real.sqrt (booleanMapDenominator (E := E) (V := V)) := by
  have hmreal : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast hm
  have hD := booleanMapDenominator_pos (V := V) hm
  unfold normalizedBooleanLastCoordinate
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hmreal), ne_of_gt (Real.sqrt_pos.mpr hD)] <;> ring

/-- At a sign vector the positive-weight map returns the same original
coordinate in every position, with denominator `sqrt (4m+|V|)`. -/
theorem normalizedBooleanMap_eval (i j k : E → V) (b : E → ℝ) (z : V → ℝ)
    (hz : ∀ v, z v ^ 2 = 1) (hm : 0 < Fintype.card E) :
    normalizedQuartic i j k b (normalizedBooleanCoordinates i j k z)
        (normalizedBooleanLastCoordinate (E := E) (V := V)) =
      (clauseSquareSum i j k b z 1 - (Fintype.card E : ℝ) / 4) /
        (16 * booleanMapDenominator (E := E) (V := V) ^ 2) := by
  have hD := booleanMapDenominator_pos (V := V) hm
  let a : ℝ := 1 / Real.sqrt (booleanMapDenominator (E := E) (V := V))
  have hcoordinates : positiveWeightCoordinate i j k
      (normalizedBooleanCoordinates i j k z) = (fun v ↦ a * z v) := by
    funext v
    rw [positiveWeightCoordinate_booleanMap i j k z v hm]
    dsimp [a]
    ring
  have hlast : normalizedBooleanLastCoordinate (E := E) (V := V) /
      Real.sqrt (Fintype.card E : ℝ) = a :=
    normalizedBooleanLastCoordinate_div_sqrt hm
  have hpenalty : occurrencePenalty i j k z 1 = 0 := by
    simp [occurrencePenalty, hz]
  have hscale := xorQuartic_homogeneous i j k b a z 1
  rw [mul_one] at hscale
  have hfourth : a ^ 4 = 1 / booleanMapDenominator (E := E) (V := V) ^ 2 := by
    dsimp [a]
    rw [div_pow, one_pow]
    have hroot : Real.sqrt (booleanMapDenominator (E := E) (V := V)) ^ 4 =
        booleanMapDenominator (E := E) (V := V) ^ 2 := by
      calc
        Real.sqrt (booleanMapDenominator (E := E) (V := V)) ^ 4 =
            (Real.sqrt (booleanMapDenominator (E := E) (V := V)) ^ 2) ^ 2 := by ring
        _ = booleanMapDenominator (E := E) (V := V) ^ 2 := by rw [Real.sq_sqrt hD.le]
    rw [hroot]
  unfold normalizedQuartic
  rw [hcoordinates, hlast, hscale, hfourth]
  simp only [xorQuartic, hpenalty, mul_zero, add_zero, one_pow, mul_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The exact negative value after applying a normalized functional that kills
all the clause squares. This is the density-eight arithmetic identity. -/
theorem positive_weight_gap_density_arithmetic (N : ℝ) (hN : N ≠ 0) :
    -(8 * N) / (64 * (4 * (8 * N) + N) ^ 2) = -(1 / (8712 * N)) := by
  rw [show 4 * (8 * N) + N = 33 * N by ring]
  field_simp [hN] <;> ring

/-- Linear coordinate substitution implementing the positive occurrence weights. -/
def normalizedVariablePolynomial (i j k : E → V) :
    Option V → MvPolynomial (Option V) ℝ
  | some v => MvPolynomial.C (1 / Real.sqrt ((clauseOccurrenceCount i j k v : ℝ) + 1)) *
      MvPolynomial.X (some v)
  | none => MvPolynomial.C (1 / Real.sqrt (Fintype.card E : ℝ)) * MvPolynomial.X none

def normalizedQuarticPolynomial (i j k : E → V) (b : E → ℝ) :
    MvPolynomial (Option V) ℝ :=
  MvPolynomial.C (1 / 16 : ℝ) *
    MvPolynomial.eval₂ MvPolynomial.C (normalizedVariablePolynomial i j k)
      (xorQuarticPolynomial i j k b)

theorem normalizedQuarticPolynomial_eval (i j k : E → V) (b : E → ℝ)
    (w : Option V → ℝ) :
    MvPolynomial.eval w (normalizedQuarticPolynomial i j k b) =
      normalizedQuartic i j k b (fun v ↦ w (some v)) (w none) := by
  unfold normalizedQuarticPolynomial
  rw [map_mul, MvPolynomial.eval_C, ← MvPolynomial.eval_assoc,
    xorQuarticPolynomial_eval]
  simp only [Function.comp_apply, normalizedVariablePolynomial, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  have hcoords : (fun v ↦ 1 / Real.sqrt ((clauseOccurrenceCount i j k v : ℝ) + 1) *
      w (some v)) = positiveWeightCoordinate i j k (fun v ↦ w (some v)) := by
    funext v
    unfold positiveWeightCoordinate
    ring
  rw [hcoords]
  have hlast : 1 / Real.sqrt (Fintype.card E : ℝ) * w none =
      w none / Real.sqrt (Fintype.card E : ℝ) := by ring
  rw [hlast]
  unfold normalizedQuartic
  ring

omit [Fintype V] in
theorem normalizedVariablePolynomial_isHomogeneous (i j k : E → V) (v : Option V) :
    (normalizedVariablePolynomial i j k v).IsHomogeneous 1 := by
  cases v with
  | none => exact (MvPolynomial.isHomogeneous_X ℝ _).C_mul _
  | some v => exact (MvPolynomial.isHomogeneous_X ℝ _).C_mul _

theorem normalizedQuarticPolynomial_isHomogeneous (i j k : E → V) (b : E → ℝ) :
    (normalizedQuarticPolynomial i j k b).IsHomogeneous 4 := by
  have hcomp := (xorQuarticPolynomial_isHomogeneous i j k b).eval₂ MvPolynomial.C
    (normalizedVariablePolynomial i j k) (fun r ↦ MvPolynomial.isHomogeneous_C _ r)
    (normalizedVariablePolynomial_isHomogeneous i j k)
  exact hcomp.C_mul _

theorem normalizedQuarticPolynomial_totalDegree_le (i j k : E → V) (b : E → ℝ) :
    (normalizedQuarticPolynomial i j k b).totalDegree ≤ 4 :=
  (normalizedQuarticPolynomial_isHomogeneous i j k b).totalDegree_le

theorem normalizedQuarticPolynomial_nonneg (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1)
    (hsound : ∀ σ : V → ℝ, (∀ v, σ v ^ 2 = 1) →
      (Fintype.card E : ℝ) ≤ clauseSquareSum i j k b σ 1)
    (w : Option V → ℝ) :
    0 ≤ MvPolynomial.eval w (normalizedQuarticPolynomial i j k b) := by
  rw [normalizedQuarticPolynomial_eval]
  exact normalizedQuartic_nonneg i j k b hb hsound _ _

theorem normalizedQuarticPolynomial_le_one (i j k : E → V) (b : E → ℝ)
    (hb : ∀ e, |b e| = 1) (hm : 8 ≤ Fintype.card E)
    (w : Option V → ℝ)
    (hnorm : coordinateSquareSum (fun v ↦ w (some v)) + w none ^ 2 ≤ 1) :
    MvPolynomial.eval w (normalizedQuarticPolynomial i j k b) ≤ 1 := by
  rw [normalizedQuarticPolynomial_eval]
  exact normalizedQuartic_le_one i j k b hb hm _ _ hnorm

end Normalization

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
