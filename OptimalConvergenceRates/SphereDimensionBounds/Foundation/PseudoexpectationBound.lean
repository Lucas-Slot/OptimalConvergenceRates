import OptimalConvergenceRates.SphereDimensionBounds.Foundation.Pseudoexpectation

/-! Quantitative bounds for every normalized truncated positive functional. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.Foundation

open scoped BigOperators symmDiff

variable {I : Type*} [Fintype I] [DecidableEq I]

def booleanCharacterElement (d : ℕ) (S : Finset I) (hS : S.card ≤ d) :
    booleanDegreeSpace (I := I) d :=
  ⟨cubeCharacter S, hasBooleanDegree_character d S hS⟩

def booleanOneElement (d : ℕ) : booleanDegreeSpace (I := I) d :=
  ⟨fun _ => 1, hasBooleanDegree_one d⟩

omit [Fintype I] [DecidableEq I] in
theorem cubeCharacter_sq (S : Finset I) (x : I → Bool) : cubeCharacter S x ^ 2 = 1 :=
  booleanCharacter_sq _ (fun _ => booleanSign_sq _) S

/-- Positivity of the two squares `(chi_A+chi_B)^2` and `(chi_A-chi_B)^2`
bounds every character moment of degree at most `2*K`. No Gram representation
or special construction of the functional is required. -/
theorem pseudoexpectation_character_abs_le (K : ℕ)
    (P : TruncatedBooleanPseudoexpectation I K) (D : Finset I) (hD : D.card ≤ 2 * K) :
    |P.functional (booleanCharacterElement (2 * K) D hD)| ≤ 1 := by
  obtain ⟨A, B, hAB⟩ := exists_booleanIndex_split K D hD
  have hA : HasBooleanDegree K (cubeCharacter A.val) :=
    hasBooleanDegree_character K A.val A.property
  have hB : HasBooleanDegree K (cubeCharacter B.val) :=
    hasBooleanDegree_character K B.val B.property
  have hplusDegree : HasBooleanDegree K (fun x => cubeCharacter A.val x + cubeCharacter B.val x) :=
    (booleanDegreeSpace K).add_mem hA hB
  have hminusDegree : HasBooleanDegree K (fun x => cubeCharacter A.val x - cubeCharacter B.val x) :=
    (booleanDegreeSpace K).sub_mem hA hB
  have hplusPoint (x : I → Bool) :
      (cubeCharacter A.val x + cubeCharacter B.val x) ^ 2 = 2 + 2 * cubeCharacter D x := by
    rw [← hAB, ← cubeCharacter_mul]
    nlinarith [cubeCharacter_sq A.val x, cubeCharacter_sq B.val x]
  have hminusPoint (x : I → Bool) :
      (cubeCharacter A.val x - cubeCharacter B.val x) ^ 2 = 2 + (-2) * cubeCharacter D x := by
    rw [← hAB, ← cubeCharacter_mul]
    nlinarith [cubeCharacter_sq A.val x, cubeCharacter_sq B.val x]
  have hplusElement :
      (⟨fun x => (cubeCharacter A.val x + cubeCharacter B.val x) ^ 2,
          hasBooleanDegree_square K _ hplusDegree⟩ : booleanDegreeSpace (2 * K)) =
        (2 : ℝ) • booleanOneElement (2 * K) +
          (2 : ℝ) • booleanCharacterElement (2 * K) D hD := by
    apply Subtype.ext
    funext x
    change (cubeCharacter A.val x + cubeCharacter B.val x) ^ 2 =
      2 * 1 + 2 * cubeCharacter D x
    simpa only [mul_one] using hplusPoint x
  have hminusElement :
      (⟨fun x => (cubeCharacter A.val x - cubeCharacter B.val x) ^ 2,
          hasBooleanDegree_square K _ hminusDegree⟩ : booleanDegreeSpace (2 * K)) =
        (2 : ℝ) • booleanOneElement (2 * K) +
          (-2 : ℝ) • booleanCharacterElement (2 * K) D hD := by
    apply Subtype.ext
    funext x
    change (cubeCharacter A.val x - cubeCharacter B.val x) ^ 2 =
      2 * 1 + (-2) * cubeCharacter D x
    simpa only [mul_one] using hminusPoint x
  have hnorm : P.functional (booleanOneElement (2 * K)) = 1 := P.normalized
  have hp := P.square_nonneg _ hplusDegree
  have hm := P.square_nonneg _ hminusDegree
  rw [hplusElement, map_add, map_smul, map_smul, hnorm] at hp
  rw [hminusElement, map_add, map_smul, map_smul, hnorm] at hm
  simp only [smul_eq_mul, mul_one] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The actual truncated space is spanned by its low-support characters. -/
theorem booleanDegreeElement_fourier (d : ℕ)
    (f : booleanDegreeSpace (I := I) d) :
    f = ∑ S : BooleanIndex I d,
      cubeFourierCoeff f.val S.val • booleanCharacterElement d S.val S.property := by
  apply Subtype.ext
  funext x
  simpa [booleanCharacterElement] using
    (cubeFourier_inversion_truncated d f.val f.property x).symm

theorem pseudoexpectation_fourier_sum (K : ℕ)
    (P : TruncatedBooleanPseudoexpectation I K)
    (f : booleanDegreeSpace (I := I) (2 * K)) :
    P.functional f = ∑ S : BooleanIndex I (2 * K),
      cubeFourierCoeff f.val S.val *
        P.functional (booleanCharacterElement (2 * K) S.val S.property) := by
  conv_lhs => rw [booleanDegreeElement_fourier (2 * K) f]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Every normalized degree-`2*K` positive functional has the same uniform
error amplification bound. In particular uniform transfer does not need to
remember the Gram representation used to construct the hard instance. -/
theorem pseudoexpectation_abs_le (K : ℕ)
    (P : TruncatedBooleanPseudoexpectation I K)
    (f : booleanDegreeSpace (I := I) (2 * K)) (B : ℝ)
    (hB : ∀ x, |f.val x| ≤ B) : |P.functional f| ≤ cubeSize I * B := by
  classical
  rw [pseudoexpectation_fourier_sum]
  calc
    |∑ S : BooleanIndex I (2 * K), cubeFourierCoeff f.val S.val *
        P.functional (booleanCharacterElement (2 * K) S.val S.property)| ≤
        ∑ S : BooleanIndex I (2 * K),
          |cubeFourierCoeff f.val S.val *
            P.functional (booleanCharacterElement (2 * K) S.val S.property)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S : BooleanIndex I (2 * K), |cubeFourierCoeff f.val S.val| := by
      apply Finset.sum_le_sum
      intro S hS
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (pseudoexpectation_character_abs_le K P S.val S.property)
    _ = ∑ S ∈ Finset.univ.filter (fun S : Finset I => S.card ≤ 2 * K),
        |cubeFourierCoeff f.val S| :=
      (Finset.sum_subtype
        (Finset.univ.filter (fun S : Finset I => S.card ≤ 2 * K))
        (by intro S; simp) (fun S => |cubeFourierCoeff f.val S|)).symm
    _ ≤ ∑ S : Finset I, |cubeFourierCoeff f.val S| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun S hS hnot => abs_nonneg _)
    _ ≤ cubeSize I * B := cubeFourier_sum_abs_le f.val B hB

end OptimalConvergenceRates.SphereDimensionBounds.Foundation
