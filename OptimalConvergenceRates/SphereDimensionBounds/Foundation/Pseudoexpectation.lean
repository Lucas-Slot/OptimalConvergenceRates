import OptimalConvergenceRates.SphereDimensionBounds.Foundation.BooleanFourier
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.BoundaryWitness

/-!
# Precisely truncated Boolean functionals

Fourier degree is the cardinality of the supporting character subset.
The final structure below is a linear functional on the degree-`2*K`
submodule, normalized on one and positive on squares of degree-`K`
functions. Its constructor obtains positivity from an explicit finite
Gram representation of the moment matrix.
-/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators symmDiff

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hasBooleanDegree_character (d : ℕ) (S : Finset I) (hS : S.card ≤ d) :
    HasBooleanDegree d (cubeCharacter S) := by
  intro T hT
  rw [cubeFourierCoeff_character]
  have hne : T ≠ S := by
    intro h
    subst T
    omega
  simp [hne]

theorem hasBooleanDegree_one (d : ℕ) :
    HasBooleanDegree d (fun _ : I → Bool => (1 : ℝ)) := by
  exact hasBooleanDegree_character d ∅ (by simp)

/-- Product expansion before any application of the pseudoexpectation. -/
theorem boolean_product_expansion (d e : ℕ) (f g : (I → Bool) → ℝ)
    (hf : HasBooleanDegree d f) (hg : HasBooleanDegree e g) :
    (fun x => f x * g x) = fun x =>
      ∑ S : BooleanIndex I d, ∑ T : BooleanIndex I e,
        (cubeFourierCoeff f S.val * cubeFourierCoeff g T.val) *
          cubeCharacter (S.val ∆ T.val) x := by
  funext x
  rw [← cubeFourier_inversion_truncated d f hf x,
    ← cubeFourier_inversion_truncated e g hg x, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  rw [← cubeCharacter_mul]
  ring

/-- Products have at most the sum of their actual Fourier degrees. -/
theorem hasBooleanDegree_mul (d e : ℕ) (f g : (I → Bool) → ℝ)
    (hf : HasBooleanDegree d f) (hg : HasBooleanDegree e g) :
    HasBooleanDegree (d + e) (fun x => f x * g x) := by
  intro U hU
  rw [boolean_product_expansion d e f g hf hg, cubeFourierCoeff_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [cubeFourierCoeff_sum]
  apply Finset.sum_eq_zero
  intro T hT
  rw [cubeFourierCoeff_smul]
  have hcard : (S.val ∆ T.val).card ≤ d + e := by
    have h := symmDiff_card_le S.val T.val
    have hSbound := S.property
    have hTbound := T.property
    omega
  rw [hasBooleanDegree_character (d + e) _ hcard U hU, mul_zero]

theorem hasBooleanDegree_square (K : ℕ) (f : (I → Bool) → ℝ)
    (hf : HasBooleanDegree K f) :
    HasBooleanDegree (2 * K) (fun x => f x ^ 2) := by
  simpa only [pow_two, two_mul] using hasBooleanDegree_mul K K f f hf hf

/-- The full Fourier extension is convenient for algebra. Its restriction
below has precisely the required degree-`2*K` domain. -/
def booleanMomentFunctional (moment : Finset I → ℝ) :
    ((I → Bool) → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ S, cubeFourierCoeff f S * moment S
  map_add' f g := by
    change (∑ S, cubeFourierCoeff (fun x => f x + g x) S * moment S) = _
    simp_rw [cubeFourierCoeff_add, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    change (∑ S, cubeFourierCoeff (fun x => c * f x) S * moment S) =
      c * ∑ S, cubeFourierCoeff f S * moment S
    simp_rw [cubeFourierCoeff_smul, mul_assoc, Finset.mul_sum]

@[simp] theorem booleanMomentFunctional_character (moment : Finset I → ℝ)
    (S : Finset I) : booleanMomentFunctional moment (cubeCharacter S) = moment S := by
  simp [booleanMomentFunctional, cubeFourierCoeff_character, ite_mul]

@[simp] theorem booleanMomentFunctional_one (moment : Finset I → ℝ) :
    booleanMomentFunctional moment (fun _ : I → Bool => 1) = moment ∅ := by
  exact booleanMomentFunctional_character moment ∅

theorem booleanMomentFunctional_sum {J : Type*} [Fintype J]
    (moment : Finset I → ℝ) (f : J → (I → Bool) → ℝ) :
    booleanMomentFunctional moment (fun x => ∑ j, f j x) =
      ∑ j, booleanMomentFunctional moment (f j) := by
  change (∑ S, cubeFourierCoeff (fun x => ∑ j, f j x) S * moment S) = _
  simp_rw [cubeFourierCoeff_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem booleanMomentFunctional_smul (moment : Finset I → ℝ)
    (c : ℝ) (f : (I → Bool) → ℝ) :
    booleanMomentFunctional moment (fun x => c * f x) =
      c * booleanMomentFunctional moment f := by
  exact (booleanMomentFunctional moment).map_smul c f

/-- Squared low-degree functions evaluate to the ordinary truncated
moment-matrix quadratic form. -/
theorem booleanMomentFunctional_square_eq (moment : Finset I → ℝ)
    (K : ℕ) (f : (I → Bool) → ℝ) (hf : HasBooleanDegree K f) :
    booleanMomentFunctional moment (fun x => f x ^ 2) =
      ∑ S : BooleanIndex I K, ∑ T : BooleanIndex I K,
        cubeFourierCoeff f S.val * cubeFourierCoeff f T.val *
          moment (S.val ∆ T.val) := by
  have hfun : (fun x => f x ^ 2) = (fun x => f x * f x) := by
    funext x
    exact pow_two _
  rw [hfun, boolean_product_expansion K K f f hf hf, booleanMomentFunctional_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [booleanMomentFunctional_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [booleanMomentFunctional_smul, booleanMomentFunctional_character]

theorem booleanMomentFunctional_square_nonneg_of_gram {C : Type*} [Fintype C]
    (moment : Finset I → ℝ) (K : ℕ) (u : BooleanIndex I K → C → ℝ)
    (hgram : ∀ S T, moment (S.val ∆ T.val) = finiteGramKernel u S T)
    (f : (I → Bool) → ℝ) (hf : HasBooleanDegree K f) :
    0 ≤ booleanMomentFunctional moment (fun x => f x ^ 2) := by
  rw [booleanMomentFunctional_square_eq moment K f hf]
  simp_rw [hgram]
  exact finiteGram_quadratic_nonneg u (fun S => cubeFourierCoeff f S.val)

theorem booleanMomentFunctional_square_nonneg_of_signed_blocks
    {C : Type*} [Fintype C] [DecidableEq C]
    (moment : Finset I → ℝ) (K : ℕ)
    (classOf : BooleanIndex I K → C) (sign : BooleanIndex I K → ℝ)
    (hblocks : ∀ S T, moment (S.val ∆ T.val) = signedBlockKernel classOf sign S T)
    (f : (I → Bool) → ℝ) (hf : HasBooleanDegree K f) :
    0 ≤ booleanMomentFunctional moment (fun x => f x ^ 2) := by
  apply booleanMomentFunctional_square_nonneg_of_gram moment K
    (signedBlockFeature classOf sign)
  · intro S T
    rw [hblocks, signedBlockKernel_eq_gram]
  · exact hf

/-- The quantitative evaluation bound needed to carry a uniform error
through a truncated Boolean functional. Only moments in its domain are bounded. -/
theorem booleanMomentFunctional_abs_le (moment : Finset I → ℝ)
    (d : ℕ) (hmoment : ∀ S, S.card ≤ d → |moment S| ≤ 1)
    (f : (I → Bool) → ℝ) (hf : HasBooleanDegree d f)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    |booleanMomentFunctional moment f| ≤ cubeSize I * B := by
  calc
    |booleanMomentFunctional moment f| ≤
        ∑ S : Finset I, |cubeFourierCoeff f S * moment S| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S : Finset I, |cubeFourierCoeff f S| := by
      apply Finset.sum_le_sum
      intro S hS
      by_cases hcard : S.card ≤ d
      · rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hmoment S hcard)
      · rw [hf S (Nat.lt_of_not_ge hcard)]
        simp
    _ ≤ cubeSize I * B := cubeFourier_sum_abs_le f B hB

/-- A normalized positive functional on exactly the truncated Boolean space.
Every square argument carries its proved degree bound. -/
structure TruncatedBooleanPseudoexpectation (I : Type*) [Fintype I] [DecidableEq I]
    (K : ℕ) where
  functional : booleanDegreeSpace (I := I) (2 * K) →ₗ[ℝ] ℝ
  normalized : functional ⟨fun _ => 1, hasBooleanDegree_one (2 * K)⟩ = 1
  square_nonneg : ∀ (f : (I → Bool) → ℝ) (hf : HasBooleanDegree K f),
    0 ≤ functional ⟨fun x => f x ^ 2, hasBooleanDegree_square K f hf⟩

/-- A finite Gram moment matrix constructs a genuine truncated
pseudoexpectation. The hypothesis describes a matrix, not the target polynomial. -/
def truncatedPseudoexpectationOfGram {C : Type*} [Fintype C]
    (moment : Finset I → ℝ) (K : ℕ) (hnorm : moment ∅ = 1)
    (u : BooleanIndex I K → C → ℝ)
    (hgram : ∀ S T, moment (S.val ∆ T.val) = finiteGramKernel u S T) :
    TruncatedBooleanPseudoexpectation I K where
  functional := (booleanMomentFunctional moment).comp (booleanDegreeSpace (2 * K)).subtype
  normalized := by
    change booleanMomentFunctional moment (fun _ => 1) = 1
    rw [booleanMomentFunctional_one, hnorm]
  square_nonneg f hf :=
    booleanMomentFunctional_square_nonneg_of_gram moment K u hgram f hf

/-- Every character in degree at most `2*K` is a product of two characters
of degree at most `K`. -/
theorem exists_booleanIndex_split (K : ℕ) (D : Finset I) (hD : D.card ≤ 2 * K) :
    ∃ S T : BooleanIndex I K, S.val ∆ T.val = D := by
  by_cases hsmall : D.card ≤ K
  · refine ⟨⟨D, hsmall⟩, ⟨∅, by simp⟩, ?_⟩
    simp
  · have hK : K ≤ D.card := by omega
    obtain ⟨S, hSD, hScard⟩ := Finset.exists_subset_card_eq hK
    have hTcard : (D \ S).card ≤ K := by
      rw [Finset.card_sdiff_of_subset hSD, hScard]
      omega
    refine ⟨⟨S, hScard.le⟩, ⟨D \ S, hTcard⟩, ?_⟩
    simpa only [Finset.sup_eq_union, Finset.union_eq_right.mpr hSD] using
      (symmDiff_sdiff_eq_sup S D)

/-- Unit diagonal Gram matrices have entries of absolute value at most one.
The proof uses only the nonnegativity of two explicit sums of squares. -/
theorem finiteGram_abs_le_one {J C : Type*} [Fintype C]
    (u : J → C → ℝ) (S T : J)
    (hS : finiteGramKernel u S S = 1) (hT : finiteGramKernel u T T = 1) :
    |finiteGramKernel u S T| ≤ 1 := by
  have hplus : 0 ≤ 1 + 2 * finiteGramKernel u S T + 1 := by
    calc
      0 ≤ ∑ a : C, (u S a + u T a) ^ 2 :=
        Finset.sum_nonneg fun a ha => sq_nonneg _
      _ = finiteGramKernel u S S + 2 * finiteGramKernel u S T +
          finiteGramKernel u T T := by
        unfold finiteGramKernel
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = 1 + 2 * finiteGramKernel u S T + 1 := by rw [hS, hT]
  have hminus : 0 ≤ 1 + (-2) * finiteGramKernel u S T + 1 := by
    calc
      0 ≤ ∑ a : C, (u S a - u T a) ^ 2 :=
        Finset.sum_nonneg fun a ha => sq_nonneg _
      _ = finiteGramKernel u S S + (-2) * finiteGramKernel u S T +
          finiteGramKernel u T T := by
        unfold finiteGramKernel
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = 1 + (-2) * finiteGramKernel u S T + 1 := by rw [hS, hT]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Normalization and a Gram moment kernel imply the needed bound on every
moment in the degree-`2*K` domain. It is not an extra hypothesis on the instance. -/
theorem booleanMoment_abs_le_one_of_gram {C : Type*} [Fintype C]
    (moment : Finset I → ℝ) (K : ℕ) (hnorm : moment ∅ = 1)
    (u : BooleanIndex I K → C → ℝ)
    (hgram : ∀ S T, moment (S.val ∆ T.val) = finiteGramKernel u S T)
    (D : Finset I) (hD : D.card ≤ 2 * K) : |moment D| ≤ 1 := by
  obtain ⟨S, T, hST⟩ := exists_booleanIndex_split K D hD
  have hdiag (U : BooleanIndex I K) : finiteGramKernel u U U = 1 := by
    rw [← hgram]
    simpa using hnorm
  rw [← hST, hgram]
  exact finiteGram_abs_le_one u S T (hdiag S) (hdiag T)

theorem booleanMomentFunctional_abs_le_of_gram {C : Type*} [Fintype C]
    (moment : Finset I → ℝ) (K : ℕ) (hnorm : moment ∅ = 1)
    (u : BooleanIndex I K → C → ℝ)
    (hgram : ∀ S T, moment (S.val ∆ T.val) = finiteGramKernel u S T)
    (f : (I → Bool) → ℝ) (hf : HasBooleanDegree (2 * K) f)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    |booleanMomentFunctional moment f| ≤ cubeSize I * B :=
  booleanMomentFunctional_abs_le moment (2 * K)
    (booleanMoment_abs_le_one_of_gram moment K hnorm u hgram) f hf B hB

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
