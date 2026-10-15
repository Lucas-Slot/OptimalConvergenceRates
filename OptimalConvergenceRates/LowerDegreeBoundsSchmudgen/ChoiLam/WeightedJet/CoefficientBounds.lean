/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/WeightedJet/CoefficientBounds.lean

  Homogeneous Choi-Lam identities and coefficient-distance estimates for quadratic jets.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.WeightedJet.WeightedRestriction
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.WeightedJet.CertificateExtraction

open MvPolynomial Finset
open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates

lemma homogeneousPart4_eq_self_of_isHomogeneous {m : ℕ} {p : MvPolynomial (Fin 4) ℝ}
    (hp : p.IsHomogeneous m) : homogeneousPart4 m p = p := by
  ext α
  rw [coeff_homogeneousPart4]
  by_cases hdeg : α.sum (fun _ e => e) = m
  · simp [hdeg]
  · have hdegree : Finsupp.degree α ≠ m := by
      intro hdegree
      apply hdeg
      rw [← hdegree]
      simp [Finsupp.degree_apply, Finsupp.sum]
    rw [hp.coeff_eq_zero hdegree]
    simp [hdeg]

lemma homogeneousPart4_choiLamQuartic : homogeneousPart4 4 choiLamQuartic = choiLamQuartic := by
  apply homogeneousPart4_eq_self_of_isHomogeneous
  unfold choiLamQuartic
  have hX0 : ((MvPolynomial.X (0 : Fin 4) : MvPolynomial (Fin 4) ℝ) ^ 4).IsHomogeneous 4 := by
    simpa using (MvPolynomial.isHomogeneous_X ℝ (0 : Fin 4)).pow 4
  have hX12 : (((MvPolynomial.X (1 : Fin 4) : MvPolynomial (Fin 4) ℝ) ^ 2) *
      ((MvPolynomial.X (2 : Fin 4) : MvPolynomial (Fin 4) ℝ) ^ 2)).IsHomogeneous 4 := by
    have h1 := (MvPolynomial.isHomogeneous_X ℝ (1 : Fin 4)).pow 2
    have h2 := (MvPolynomial.isHomogeneous_X ℝ (2 : Fin 4)).pow 2
    simpa using h1.mul h2
  have hX23 : (((MvPolynomial.X (2 : Fin 4) : MvPolynomial (Fin 4) ℝ) ^ 2) *
      ((MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ) ^ 2)).IsHomogeneous 4 := by
    have h2 := (MvPolynomial.isHomogeneous_X ℝ (2 : Fin 4)).pow 2
    have h3 := (MvPolynomial.isHomogeneous_X ℝ (3 : Fin 4)).pow 2
    simpa using h2.mul h3
  have hX31 : (((MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) ℝ) ^ 2) *
      ((MvPolynomial.X (1 : Fin 4) : MvPolynomial (Fin 4) ℝ) ^ 2)).IsHomogeneous 4 := by
    have h3 := (MvPolynomial.isHomogeneous_X ℝ (3 : Fin 4)).pow 2
    have h1 := (MvPolynomial.isHomogeneous_X ℝ (1 : Fin 4)).pow 2
    simpa using h3.mul h1
  have hmix0 : (((MvPolynomial.C (4 : ℝ) : MvPolynomial (Fin 4) ℝ) *
      MvPolynomial.X (0 : Fin 4)) * MvPolynomial.X (1 : Fin 4) *
      MvPolynomial.X (2 : Fin 4) * MvPolynomial.X (3 : Fin 4)).IsHomogeneous 4 := by
    have h0 := (MvPolynomial.isHomogeneous_X ℝ (0 : Fin 4)).C_mul (4 : ℝ)
    have h1 := MvPolynomial.isHomogeneous_X ℝ (1 : Fin 4)
    have h2 := MvPolynomial.isHomogeneous_X ℝ (2 : Fin 4)
    have h3 := MvPolynomial.isHomogeneous_X ℝ (3 : Fin 4)
    simpa [add_assoc] using (((h0.mul h1).mul h2).mul h3)
  have hmix : ((4 : MvPolynomial (Fin 4) ℝ) * X (0 : Fin 4) * X (1 : Fin 4) *
      X (2 : Fin 4) * X (3 : Fin 4)).IsHomogeneous 4 := by
    rw [show (4 : MvPolynomial (Fin 4) ℝ) = MvPolynomial.C (4 : ℝ) from
      (MvPolynomial.C_eq_coe_nat 4).symm]
    exact hmix0
  exact (((hX0.add hX12).add hX23).add hX31).sub hmix

lemma homogeneousPart4_C_four (epsilon : ℝ) :
    homogeneousPart4 4 (MvPolynomial.C epsilon : MvPolynomial (Fin 4) ℝ) = 0 := by
  ext α
  rw [coeff_homogeneousPart4]
  by_cases hα : α = 0
  · subst α
    simp
  · have h0α : (0 : Fin 4 →₀ ℕ) ≠ α := fun h => hα h.symm
    simp [MvPolynomial.coeff_C, h0α]

lemma homogeneousPart4_choiLamPerturbed (epsilon : ℝ) :
    homogeneousPart4 4 (choiLamQuartic + MvPolynomial.C epsilon) = choiLamQuartic := by
  rw [homogeneousPart4_add, homogeneousPart4_choiLamQuartic, homogeneousPart4_C_four]
  simp

theorem homogeneousPart4_totalDegree_le (m : ℕ)
    (p : MvPolynomial (Fin 4) ℝ) :
    (homogeneousPart4 m p).totalDegree ≤ m := by
  rw [homogeneousPart4_eq_homogeneousComponent]
  exact (MvPolynomial.homogeneousComponent_isHomogeneous m p).totalDegree_le

theorem sosVectorSq4_homogeneousPartVec4_two_totalDegree_le_four
    {N : ℕ} (Q : Fin N → MvPolynomial (Fin 4) ℝ) :
    (sosVectorSq4 (homogeneousPartVec4 2 Q)).totalDegree ≤ 4 := by
  unfold sosVectorSq4
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _hi
  calc
    ((homogeneousPartVec4 2 Q i) ^ 2).totalDegree
        ≤ 2 * (homogeneousPartVec4 2 Q i).totalDegree :=
          MvPolynomial.totalDegree_pow _ 2
    _ ≤ 4 := by
      have hdeg := homogeneousPart4_totalDegree_le 2 (Q i)
      dsimp [homogeneousPartVec4] at hdeg ⊢
      omega

theorem finite_sum_quadratic_jet_totalDegree_le_four
    {N : Finset (Fin 4) → ℕ}
    (Q : ∀ J : Finset (Fin 4), Fin (N J) → MvPolynomial (Fin 4) ℝ) :
    (∑ J ∈ Finset.univ.powerset,
      sosVectorSq4 (homogeneousPartVec4 2 (Q J))).totalDegree ≤ 4 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro J _hJ
  exact sosVectorSq4_homogeneousPartVec4_two_totalDegree_le_four (Q J)

theorem finite_sum_quadratic_jet_degreeBoundedSOS
    {N : Finset (Fin 4) → ℕ}
    (Q : ∀ J : Finset (Fin 4), Fin (N J) → MvPolynomial (Fin 4) ℝ) :
    Nonempty (DegreeBoundedSOS
      (∑ J ∈ Finset.univ.powerset, sosVectorSq4 (homogeneousPartVec4 2 (Q J))) 2) := by
  exact degreeBoundedSOS_of_isSOS_totalDegree_le_four
    (finite_sum_quadratic_jet_sos Q) (finite_sum_quadratic_jet_totalDegree_le_four Q)

theorem choiLamCoeffDistanceToSOS_eq_coeffNorm4 (S : MvPolynomial (Fin 4) ℝ) :
    choiLamCoeffDistanceToSOS S = coeffNorm4 (choiLamQuartic - S) := by
  rfl

theorem choiLam_sos_contradiction_of_coeffNorm_lt
    {S E : MvPolynomial (Fin 4) ℝ}
    (hS : Nonempty (DegreeBoundedSOS S 2))
    (hdecomp : choiLamQuartic = S + E)
    (herr : coeffNorm4 E < choiLamSosDistance) :
    False := by
  rcases hS with ⟨hS⟩
  have hdeg : S.totalDegree ≤ 4 := by
    simpa using hS.totalDegree_le_two_mul
  have hdist := choiLamSosDistance_le_distance_to_sos hS.toIsSOS hdeg
  have hdist_eq : choiLamCoeffDistanceToSOS S = coeffNorm4 E := by
    rw [choiLamCoeffDistanceToSOS_eq_coeffNorm4]
    congr 1
    rw [hdecomp]
    ring
  rw [hdist_eq] at hdist
  linarith

lemma coeff_eq_zero_of_totalDegree_lt_n4
    {p : MvPolynomial (Fin 4) ℝ} {m : Fin 4 →₀ ℕ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hm : d < m.sum fun _ e => e) :
    legacyMvCoeff m p = 0 := by
  by_contra hcoeff
  have hmem : m ∈ p.support := by
    rw [MvPolynomial.mem_support_iff]
    exact hcoeff
  have hmle := MvPolynomial.le_totalDegree hmem
  omega

lemma X_pow_eq_monomial_weightedJet (i : Fin 4) (k : ℕ) :
    ((X i : MvPolynomial (Fin 4) ℝ) ^ k) = MvPolynomial.monomial (Finsupp.single i k) 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih]
      change MvPolynomial.monomial (Finsupp.single i k) (1 : ℝ) *
          MvPolynomial.monomial (Finsupp.single i 1) (1 : ℝ) = _
      rw [MvPolynomial.monomial_mul_monomial]
      congr
      · ext j
        by_cases h : j = i <;> simp [h]
      · norm_num

lemma X_pow_mul_X_pow_eq_monomial_weightedJet (i j : Fin 4) (a b : ℕ) :
    ((X i : MvPolynomial (Fin 4) ℝ) ^ a * X j ^ b) =
      MvPolynomial.monomial (Finsupp.single i a + Finsupp.single j b) 1 := by
  rw [X_pow_eq_monomial_weightedJet, X_pow_eq_monomial_weightedJet,
    MvPolynomial.monomial_mul_monomial]
  norm_num

lemma four_X_prod_eq_monomial_weightedJet :
    (4 * X (0 : Fin 4) * X (1 : Fin 4) * X (2 : Fin 4) * X (3 : Fin 4) :
      MvPolynomial (Fin 4) ℝ) =
      MvPolynomial.monomial (Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1) 4 := by
  change MvPolynomial.monomial 0 (4 : ℝ) * MvPolynomial.monomial (Finsupp.single (0 : Fin 4) 1) 1 *
      MvPolynomial.monomial (Finsupp.single (1 : Fin 4) 1) 1 *
      MvPolynomial.monomial (Finsupp.single (2 : Fin 4) 1) 1 *
      MvPolynomial.monomial (Finsupp.single (3 : Fin 4) 1) 1 = _
  repeat rw [MvPolynomial.monomial_mul_monomial]
  congr
  · ext j; fin_cases j <;> norm_num
  · norm_num

lemma choiLamQuartic_coeff_single_zero_four_weightedJet :
    legacyMvCoeff (Finsupp.single (0 : Fin 4) 4) choiLamQuartic = 1 := by
  unfold choiLamQuartic
  rw [X_pow_eq_monomial_weightedJet]
  rw [X_pow_mul_X_pow_eq_monomial_weightedJet, X_pow_mul_X_pow_eq_monomial_weightedJet,
    X_pow_mul_X_pow_eq_monomial_weightedJet, four_X_prod_eq_monomial_weightedJet]
  have h2 : Finsupp.single (1 : Fin 4) 2 + Finsupp.single (2 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (1 : Fin 4); simp at this
  have h3 : Finsupp.single (2 : Fin 4) 2 + Finsupp.single (3 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (2 : Fin 4); simp at this
  have h4 : Finsupp.single (3 : Fin 4) 2 + Finsupp.single (1 : Fin 4) 2 ≠
      Finsupp.single (0 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (3 : Fin 4); simp at this
  have h5 : Finsupp.single (0 : Fin 4) 1 + Finsupp.single (1 : Fin 4) 1 +
        Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) 1 ≠
      Finsupp.single (0 : Fin 4) 4 := by
    intro h; have := Finsupp.ext_iff.mp h (1 : Fin 4); simp at this
  simp [MvPolynomial.coeff_monomial, h2, h3, h4, h5]

/-! ## Quarter-exponent interface

A symmetric-hole Remez/Bernstein estimate gives the higher-jet bounds
`Q₂ = O(1)`, `Q₃ = O(r)`, and `Q₄ = O(r²)`. The certificate extraction,
degree-four comparison, and final constant arithmetic below are specialized to
that quarter-exponent estimate. -/

noncomputable def weightedJetTailConst : ℝ :=
  2 * Real.exp 6 * (2 + jetErrorConst + 64)


def orderedCubicAlpha (ijk : Fin 4 × Fin 4 × Fin 4) : Fin 4 →₀ ℕ :=
  Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 + Finsupp.single ijk.2.2 1

def orderedQuarticAlpha (ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4) :
    Fin 4 →₀ ℕ :=
  Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
    Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1

def orderedCubicWeight (ijk : Fin 4 × Fin 4 × Fin 4) : ℝ :=
  (500 : ℝ) ^ (2 * weightedDegree4 (orderedCubicAlpha ijk))

def orderedQuarticWeight (ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4) : ℝ :=
  (500 : ℝ) ^ (2 * weightedDegree4 (orderedQuarticAlpha ijkl))

theorem orderedCubicWeight_nonneg (ijk : Fin 4 × Fin 4 × Fin 4) :
    0 ≤ orderedCubicWeight ijk := by
  unfold orderedCubicWeight
  exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 500) _

theorem orderedQuarticWeight_nonneg (ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4) :
    0 ≤ orderedQuarticWeight ijkl := by
  unfold orderedQuarticWeight
  exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 500) _

noncomputable def weightedJetTailCubicWeightSum : ℝ :=
  ∑ ijk : Fin 4 × Fin 4 × Fin 4, orderedCubicWeight ijk

noncomputable def weightedJetTailQuarticWeightSum : ℝ :=
  ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, orderedQuarticWeight ijkl

noncomputable def weightedJetTailCoeffConst : ℝ :=
  1000 * weightedJetTailConst +
    4096 * (weightedJetTailCubicWeightSum + 1) * weightedJetTailConst +
    262144 * (weightedJetTailQuarticWeightSum + 1) * weightedJetTailConst + 1

noncomputable def weightedJetQuarterConst : ℝ :=
  weightedJetHigherConst + weightedJetTailCoeffConst + 1

theorem weightedJetTailConst_pos : 0 < weightedJetTailConst := by
  unfold weightedJetTailConst
  have hinner : 0 < 2 + jetErrorConst + 64 := by nlinarith [jetErrorConst_pos]
  positivity

theorem weightedJetTailConst_nonneg : 0 ≤ weightedJetTailConst :=
  weightedJetTailConst_pos.le


theorem weightedJetTailCubicWeightSum_nonneg :
    0 ≤ weightedJetTailCubicWeightSum := by
  unfold weightedJetTailCubicWeightSum
  exact Finset.sum_nonneg (fun ijk _ ↦ orderedCubicWeight_nonneg ijk)

theorem weightedJetTailQuarticWeightSum_nonneg :
    0 ≤ weightedJetTailQuarticWeightSum := by
  unfold weightedJetTailQuarticWeightSum
  exact Finset.sum_nonneg (fun ijkl _ ↦ orderedQuarticWeight_nonneg ijkl)

theorem weightedJetTailCoeffConst_nonneg : 0 ≤ weightedJetTailCoeffConst := by
  unfold weightedJetTailCoeffConst
  nlinarith [weightedJetTailConst_nonneg, weightedJetTailCubicWeightSum_nonneg,
    weightedJetTailQuarticWeightSum_nonneg]

theorem weightedJetQuarterConst_pos : 0 < weightedJetQuarterConst := by
  unfold weightedJetQuarterConst
  nlinarith [weightedJetHigherConst_pos, weightedJetTailCoeffConst_nonneg]

theorem weightedJetQuarterConst_nonneg : 0 ≤ weightedJetQuarterConst :=
  weightedJetQuarterConst_pos.le


theorem weightedJetQuarterConst_absorbs_tail_1000 :
    1000 * weightedJetTailConst ≤ weightedJetQuarterConst := by
  unfold weightedJetQuarterConst weightedJetTailCoeffConst
  have hhigh : 0 ≤ weightedJetHigherConst := weightedJetHigherConst_pos.le
  have h3 : 0 ≤ 4096 * (weightedJetTailCubicWeightSum + 1) * weightedJetTailConst := by
    nlinarith [weightedJetTailCubicWeightSum_nonneg, weightedJetTailConst_nonneg]
  have h4 : 0 ≤ 262144 * (weightedJetTailQuarticWeightSum + 1) * weightedJetTailConst := by
    nlinarith [weightedJetTailQuarticWeightSum_nonneg, weightedJetTailConst_nonneg]
  nlinarith

theorem weightedJetQuarterConst_absorbs_tail_cubic
    (ijk : Fin 4 × Fin 4 × Fin 4) :
    4096 * orderedCubicWeight ijk * weightedJetTailConst ≤ weightedJetQuarterConst := by
  let weight : ℝ := orderedCubicWeight ijk
  have htail : 0 ≤ weightedJetTailConst := weightedJetTailConst_nonneg
  have hweight_le : weight ≤ weightedJetTailCubicWeightSum + 1 := by
    have hle : weight ≤ weightedJetTailCubicWeightSum := by
      dsimp [weight]
      unfold weightedJetTailCubicWeightSum
      exact Finset.single_le_sum (f := orderedCubicWeight)
        (fun x _ ↦ orderedCubicWeight_nonneg x) (Finset.mem_univ ijk)
    linarith
  have hmain : 4096 * weight * weightedJetTailConst ≤
      4096 * (weightedJetTailCubicWeightSum + 1) * weightedJetTailConst := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hweight_le (by norm_num)) htail
  have habs : 4096 * (weightedJetTailCubicWeightSum + 1) * weightedJetTailConst ≤
      weightedJetQuarterConst := by
    unfold weightedJetQuarterConst weightedJetTailCoeffConst
    have hhigh : 0 ≤ weightedJetHigherConst := weightedJetHigherConst_pos.le
    have h1000 : 0 ≤ 1000 * weightedJetTailConst := by positivity
    have h4 : 0 ≤ 262144 * (weightedJetTailQuarticWeightSum + 1) *
        weightedJetTailConst := by
      nlinarith [weightedJetTailQuarticWeightSum_nonneg, weightedJetTailConst_nonneg]
    nlinarith
  calc
    4096 * orderedCubicWeight ijk * weightedJetTailConst
        = 4096 * weight * weightedJetTailConst := by rfl
    _ ≤ 4096 * (weightedJetTailCubicWeightSum + 1) * weightedJetTailConst := hmain
    _ ≤ weightedJetQuarterConst := habs

theorem weightedJetQuarterConst_absorbs_tail_quartic
    (ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4) :
    262144 * orderedQuarticWeight ijkl * weightedJetTailConst ≤ weightedJetQuarterConst := by
  let weight : ℝ := orderedQuarticWeight ijkl
  have htail : 0 ≤ weightedJetTailConst := weightedJetTailConst_nonneg
  have hweight_le : weight ≤ weightedJetTailQuarticWeightSum + 1 := by
    have hle : weight ≤ weightedJetTailQuarticWeightSum := by
      dsimp [weight]
      unfold weightedJetTailQuarticWeightSum
      -- Recursion-depth budget: unfolding the quartic ordered-weight sum exposes a
      -- deeply nested finite product index before `single_le_sum` closes the goal.
      set_option maxRecDepth 5000 in
      exact Finset.single_le_sum (f := orderedQuarticWeight)
        (fun x _ ↦ orderedQuarticWeight_nonneg x) (Finset.mem_univ ijkl)
    linarith
  have hmain : 262144 * weight * weightedJetTailConst ≤
      262144 * (weightedJetTailQuarticWeightSum + 1) * weightedJetTailConst := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hweight_le (by norm_num)) htail
  have habs : 262144 * (weightedJetTailQuarticWeightSum + 1) * weightedJetTailConst ≤
      weightedJetQuarterConst := by
    unfold weightedJetQuarterConst weightedJetTailCoeffConst
    have hhigh : 0 ≤ weightedJetHigherConst := weightedJetHigherConst_pos.le
    have h1000 : 0 ≤ 1000 * weightedJetTailConst := by positivity
    have h3 : 0 ≤ 4096 * (weightedJetTailCubicWeightSum + 1) *
        weightedJetTailConst := by
      nlinarith [weightedJetTailCubicWeightSum_nonneg, weightedJetTailConst_nonneg]
    nlinarith
  calc
    262144 * orderedQuarticWeight ijkl * weightedJetTailConst
        = 262144 * weight * weightedJetTailConst := by rfl
    _ ≤ 262144 * (weightedJetTailQuarticWeightSum + 1) * weightedJetTailConst := hmain
    _ ≤ weightedJetQuarterConst := habs

/-- Linear-jet estimate from the Bernstein bound, improving the Markov loss from
`r^2` to `r`. -/
theorem sixty_four_le_weightedJetQuarterConst :
    (64 : ℝ) ≤ weightedJetQuarterConst := by
  have hC0 : (1 / 16 : ℝ) ≤ Real.sqrt schmInteriorEpsilon0 + schmInteriorS ^ 2 := by
    have hs : schmInteriorS ^ 2 = (1 / 16 : ℝ) := by
      unfold schmInteriorS
      norm_num
    rw [← hs]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hmain : (64 : ℝ) ≤
      8000 * (Real.sqrt schmInteriorEpsilon0 + schmInteriorS ^ 2) + 1 := by
    nlinarith
  unfold weightedJetQuarterConst weightedJetHigherConst
  nlinarith [hmain, weightedJetCubicConst_nonneg, weightedJetQuarticConst_nonneg,
    weightedJetTailCoeffConst_nonneg]

/-- Linear jet bound assembled from the uniform Bernstein estimate on zero
lines and the finite-dimensional Choi-Lam basis conversion, with the explicit
constant used in the punctured-line tail estimate. -/
theorem weightedJetLemma_linear_bound_sixty_four
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon) :
    vecCoeffNorm4 (homogeneousPartVec4 1 Q) ≤
      64 * (A * (k : ℝ) * Real.sqrt epsilon) := by
  let B : ℝ := 8 * (k : ℝ) * (A * Real.sqrt epsilon)
  have hBnon : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbasis : ∀ zi : Fin 4,
      interiorVecNorm
          (fun i : Fin N => MvPolynomial.eval (choiLamZeroDirection zi)
            (homogeneousPartVec4 1 Q i)) ≤ B := by
    intro zi
    let P : Fin N → Polynomial ℝ := fun i =>
      univariateRestriction (Q i) (0 : Fin 4 → ℝ) (choiLamZeroDirection zi)
    have hMnon : 0 ≤ A * Real.sqrt epsilon :=
      mul_nonneg (le_trans zero_le_one hA) (Real.sqrt_nonneg epsilon)
    have hdegP : ∀ i, (P i).natDegree ≤ k := by
      intro i
      exact (univariateRestriction_natDegree_le (Q i) (0 : Fin 4 → ℝ)
        (choiLamZeroDirection zi)).trans (hdeg i)
    have hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ A * Real.sqrt epsilon := by
      intro t ht
      have hline := hzeroLines zi t ht
      have heval : (fun i : Fin N => (P i).eval t) =
          fun i : Fin N => MvPolynomial.eval
            (fun j => t * choiLamZeroDirection zi j) (Q i) := by
        funext i
        dsimp [P]
        rw [univariateRestriction_eval]
        apply congrArg (fun w : Fin 4 → ℝ => MvPolynomial.eval w (Q i))
        funext j
        simp [Pi.smul_apply, smul_eq_mul]
      rw [heval]
      exact hline
    have hbern := interior_bernstein_vector_first_derivative_schm P hMnon hdegP hbound
    let V : Fin N → ℝ := fun i =>
      MvPolynomial.eval (choiLamZeroDirection zi) (homogeneousPartVec4 1 Q i)
    have hderiv : (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) = V := by
      funext i
      dsimp [P, V, homogeneousPartVec4]
      change directionalDeriv (Q i) (0 : Fin 4 → ℝ) (choiLamZeroDirection zi) =
        MvPolynomial.eval (choiLamZeroDirection zi) (homogeneousPart4 1 (Q i))
      rw [directionalDeriv_zero_eq_eval_homogeneousPart_one]
    calc
      interiorVecNorm
          (fun i : Fin N => MvPolynomial.eval (choiLamZeroDirection zi)
            (homogeneousPartVec4 1 Q i)) = interiorVecNorm V := rfl
      _ ≤ 8 * (k : ℝ) * (A * Real.sqrt epsilon) := by
        simpa [hderiv] using hbern
      _ = B := by ring
  have hlin := linear_coeff_bound_from_choiLam_basis (homogeneousPartVec4 1 Q)
    (B := B)
    (fun i => by
      unfold homogeneousPartVec4
      exact homogeneousPart4_idem 1 (Q i))
    hBnon hbasis
  calc
    vecCoeffNorm4 (homogeneousPartVec4 1 Q) ≤ 8 * B := hlin
    _ = 64 * (A * (k : ℝ) * Real.sqrt epsilon) := by
      dsimp [B]
      ring

/-- Linear jet bound assembled from the uniform Bernstein estimate on zero
lines and the finite-dimensional Choi-Lam basis conversion. -/
theorem weightedJetLemma_linear_bound_quarter
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon) :
    vecCoeffNorm4 (homogeneousPartVec4 1 Q) ≤
      weightedJetQuarterConst * A * (k : ℝ) * Real.sqrt epsilon := by
  have h64 := weightedJetLemma_linear_bound_sixty_four heps hk hA Q hdeg hzeroLines
  have hTnon : 0 ≤ A * (k : ℝ) * Real.sqrt epsilon := by positivity
  calc
    vecCoeffNorm4 (homogeneousPartVec4 1 Q)
        ≤ 64 * (A * (k : ℝ) * Real.sqrt epsilon) := h64
    _ ≤ weightedJetQuarterConst * (A * (k : ℝ) * Real.sqrt epsilon) := by
      exact mul_le_mul_of_nonneg_right sixty_four_le_weightedJetQuarterConst hTnon
    _ = weightedJetQuarterConst * A * (k : ℝ) * Real.sqrt epsilon := by ring

/-- Directional form of the revised linear-jet estimate with constant `64`. -/
theorem weightedJetLemma_linear_eval_bound_sixty_four
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) :
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 1 Q i)) ≤
      64 * (A * (k : ℝ) * Real.sqrt epsilon) := by
  exact (interiorVecNorm_eval_le_vecCoeffNorm4_of_localSqNorm_eq_one
    (homogeneousPartVec4 1 Q) hv).trans
      (weightedJetLemma_linear_bound_sixty_four heps hk hA Q hdeg hzeroLines)

/-- Directional form of the revised linear-jet estimate.  This is the formal
piece used when bounding the divided residual outside the central hole. -/
theorem weightedJetLemma_linear_eval_bound_quarter
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) :
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 1 Q i)) ≤
      weightedJetQuarterConst * A * (k : ℝ) * Real.sqrt epsilon := by
  exact (interiorVecNorm_eval_le_vecCoeffNorm4_of_localSqNorm_eq_one
    (homogeneousPartVec4 1 Q) hv).trans
      (weightedJetLemma_linear_bound_quarter heps hk hA Q hdeg hzeroLines)

lemma interiorVecNorm_sub_sub_le_add3 {N : ℕ} (u v w : Fin N → ℝ) :
    interiorVecNorm (fun i : Fin N => u i - v i - w i) ≤
      interiorVecNorm u + interiorVecNorm v + interiorVecNorm w := by
  change vecNorm (fun i : Fin N => (u i - v i) - w i) ≤
    vecNorm u + vecNorm v + vecNorm w
  have h1 := vecNorm_sub_le (fun i : Fin N => u i - v i) w
  have h2 := vecNorm_sub_le u v
  linarith

theorem univariateRestriction_coeff_zero_eq_homogeneousPart_zero
    (p : MvPolynomial (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    (univariateRestriction p (0 : Fin 4 → ℝ) v).coeff 0 =
      MvPolynomial.eval v (homogeneousPart4 0 p) := by
  exact coeff_univariateRestriction_zero_eq_eval_homogeneousPart p v 0

theorem univariateRestriction_coeff_one_eq_homogeneousPart_one
    (p : MvPolynomial (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    (univariateRestriction p (0 : Fin 4 → ℝ) v).coeff 1 =
      MvPolynomial.eval v (homogeneousPart4 1 p) := by
  exact coeff_univariateRestriction_zero_eq_eval_homogeneousPart p v 1

/-- Residual bound before division by `t^2` in
`W(t) = (Q(tv) - Q_0 - t Q_1(v)) / t^2`. -/
theorem weightedJet_residual_norm_bound_sixty_four
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) {t : ℝ} (ht : |t| ≤ schmInteriorS) :
    interiorVecNorm
        (fun i : Fin N =>
          (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v).eval t -
            (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v).coeff 0 -
              (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v).coeff 1 * t) ≤
      A * (Real.sqrt epsilon + t ^ 2) +
        jetErrorConst * A * Real.sqrt epsilon +
          64 * (A * (k : ℝ) * Real.sqrt epsilon) * |t| := by
  let P : Fin N → Polynomial ℝ := fun i =>
    univariateRestriction (Q i) (0 : Fin 4 → ℝ) v
  let U : Fin N → ℝ := fun i => (P i).eval t
  let C0 : Fin N → ℝ := fun i => (P i).coeff 0
  let L1 : Fin N → ℝ := fun i => (P i).coeff 1 * t
  have htri : interiorVecNorm (fun i : Fin N => U i - C0 i - L1 i) ≤
      interiorVecNorm U + interiorVecNorm C0 + interiorVecNorm L1 :=
    interiorVecNorm_sub_sub_le_add3 U C0 L1
  have hU : interiorVecNorm U ≤ A * (Real.sqrt epsilon + t ^ 2) := by
    have hbox : boxSmall (fun j => t * v j) := boxSmall_smul_of_localSqNorm_eq_one hv ht
    have hloc := hlocal (fun j => t * v j) hbox
    have heqU : U = fun i : Fin N => MvPolynomial.eval (fun j => t * v j) (Q i) := by
      funext i
      dsimp [U, P]
      rw [univariateRestriction_eval]
      congr
      funext j
      simp [Pi.smul_apply, smul_eq_mul]
    have hsq : localSqNorm (fun j => t * v j) = t ^ 2 :=
      localSqNorm_smul_of_localSqNorm_eq_one hv t
    simpa [heqU, hsq] using hloc
  have hC0eq : C0 = fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 0 Q i) := by
    funext i
    dsimp [C0, P, homogeneousPartVec4]
    exact univariateRestriction_coeff_zero_eq_homogeneousPart_zero (Q i) v
  have hC0 : interiorVecNorm C0 ≤ jetErrorConst * A * Real.sqrt epsilon := by
    rw [hC0eq]
    exact (interiorVecNorm_eval_le_vecCoeffNorm4_of_localSqNorm_eq_one
      (homogeneousPartVec4 0 Q) hv).trans
        (weightedJetLemma_constant_bound heps hA Q hzeroLines)
  have hL1eq : L1 = fun i : Fin N => t *
      MvPolynomial.eval v (homogeneousPartVec4 1 Q i) := by
    funext i
    dsimp [L1, P, homogeneousPartVec4]
    rw [univariateRestriction_coeff_one_eq_homogeneousPart_one]
    ring
  have hLscale : interiorVecNorm L1 = |t| *
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 1 Q i)) := by
    rw [hL1eq]
    by_cases ht0 : 0 ≤ t
    · have habs : |t| = t := abs_of_nonneg ht0
      simpa [habs, interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
        vecNorm_smul_nonneg (N := N) (c := t) ht0
          (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 1 Q i))
    · have ht_nonpos : t ≤ 0 := le_of_not_ge ht0
      have habs : |t| = -t := abs_of_nonpos ht_nonpos
      have hfun : (fun i : Fin N => t *
          MvPolynomial.eval v (homogeneousPartVec4 1 Q i)) =
          fun i : Fin N => (-t) *
            (-MvPolynomial.eval v (homogeneousPartVec4 1 Q i)) := by
        funext i
        ring
      rw [hfun]
      simpa [habs, interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
        vecNorm_smul_nonneg (N := N) (c := -t) (neg_nonneg.mpr ht_nonpos)
          (fun i : Fin N => -MvPolynomial.eval v (homogeneousPartVec4 1 Q i))
  have hL1 : interiorVecNorm L1 ≤
      64 * (A * (k : ℝ) * Real.sqrt epsilon) * |t| := by
    rw [hLscale]
    have hlin := weightedJetLemma_linear_eval_bound_sixty_four heps hk hA Q hdeg hzeroLines hv
    have ht_abs_nonneg : 0 ≤ |t| := abs_nonneg t
    calc
      |t| * interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 1 Q i))
          ≤ |t| * (64 * (A * (k : ℝ) * Real.sqrt epsilon)) := by
            exact mul_le_mul_of_nonneg_left hlin ht_abs_nonneg
      _ = 64 * (A * (k : ℝ) * Real.sqrt epsilon) * |t| := by ring
  have hsum := htri.trans (add_le_add (add_le_add hU hC0) hL1)
  simpa [P, U, C0, L1, add_assoc] using hsum

/-- Residual bound before division by `t^2` in
`W(t) = (Q(tv) - Q_0 - t Q_1(v)) / t^2`. -/
theorem weightedJet_residual_norm_bound_quarter
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) {t : ℝ} (ht : |t| ≤ schmInteriorS) :
    interiorVecNorm
        (fun i : Fin N =>
          (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v).eval t -
            (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v).coeff 0 -
              (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v).coeff 1 * t) ≤
      A * (Real.sqrt epsilon + t ^ 2) +
        jetErrorConst * A * Real.sqrt epsilon +
          weightedJetQuarterConst * A * (k : ℝ) * Real.sqrt epsilon * |t| := by
  let P : Fin N → Polynomial ℝ := fun i =>
    univariateRestriction (Q i) (0 : Fin 4 → ℝ) v
  let U : Fin N → ℝ := fun i => (P i).eval t
  let C0 : Fin N → ℝ := fun i => (P i).coeff 0
  let L1 : Fin N → ℝ := fun i => (P i).coeff 1 * t
  have htri : interiorVecNorm (fun i : Fin N => U i - C0 i - L1 i) ≤
      interiorVecNorm U + interiorVecNorm C0 + interiorVecNorm L1 :=
    interiorVecNorm_sub_sub_le_add3 U C0 L1
  have hU : interiorVecNorm U ≤ A * (Real.sqrt epsilon + t ^ 2) := by
    have hbox : boxSmall (fun j => t * v j) := boxSmall_smul_of_localSqNorm_eq_one hv ht
    have hloc := hlocal (fun j => t * v j) hbox
    have heqU : U = fun i : Fin N => MvPolynomial.eval (fun j => t * v j) (Q i) := by
      funext i
      dsimp [U, P]
      rw [univariateRestriction_eval]
      congr
      funext j
      simp [Pi.smul_apply, smul_eq_mul]
    have hsq : localSqNorm (fun j => t * v j) = t ^ 2 :=
      localSqNorm_smul_of_localSqNorm_eq_one hv t
    simpa [heqU, hsq] using hloc
  have hC0eq : C0 = fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 0 Q i) := by
    funext i
    dsimp [C0, P, homogeneousPartVec4]
    exact univariateRestriction_coeff_zero_eq_homogeneousPart_zero (Q i) v
  have hC0 : interiorVecNorm C0 ≤ jetErrorConst * A * Real.sqrt epsilon := by
    rw [hC0eq]
    exact (interiorVecNorm_eval_le_vecCoeffNorm4_of_localSqNorm_eq_one
      (homogeneousPartVec4 0 Q) hv).trans
        (weightedJetLemma_constant_bound heps hA Q hzeroLines)
  have hL1eq : L1 = fun i : Fin N => t *
      MvPolynomial.eval v (homogeneousPartVec4 1 Q i) := by
    funext i
    dsimp [L1, P, homogeneousPartVec4]
    rw [univariateRestriction_coeff_one_eq_homogeneousPart_one]
    ring
  have hLscale : interiorVecNorm L1 = |t| *
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 1 Q i)) := by
    rw [hL1eq]
    by_cases ht0 : 0 ≤ t
    · have habs : |t| = t := abs_of_nonneg ht0
      simpa [habs, interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
        vecNorm_smul_nonneg (N := N) (c := t) ht0
          (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 1 Q i))
    · have ht_nonpos : t ≤ 0 := le_of_not_ge ht0
      have habs : |t| = -t := abs_of_nonpos ht_nonpos
      have hfun : (fun i : Fin N => t *
          MvPolynomial.eval v (homogeneousPartVec4 1 Q i)) =
          fun i : Fin N => (-t) *
            (-MvPolynomial.eval v (homogeneousPartVec4 1 Q i)) := by
        funext i
        ring
      rw [hfun]
      simpa [habs, interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
        vecNorm_smul_nonneg (N := N) (c := -t) (neg_nonneg.mpr ht_nonpos)
          (fun i : Fin N => -MvPolynomial.eval v (homogeneousPartVec4 1 Q i))
  have hL1 : interiorVecNorm L1 ≤
      weightedJetQuarterConst * A * (k : ℝ) * Real.sqrt epsilon * |t| := by
    rw [hLscale]
    have hlin := weightedJetLemma_linear_eval_bound_quarter heps hk hA Q hdeg hzeroLines hv
    have ht_abs_nonneg : 0 ≤ |t| := abs_nonneg t
    calc
      |t| * interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 1 Q i))
          ≤ |t| * (weightedJetQuarterConst * A * (k : ℝ) * Real.sqrt epsilon) := by
            exact mul_le_mul_of_nonneg_left hlin ht_abs_nonneg
      _ = weightedJetQuarterConst * A * (k : ℝ) * Real.sqrt epsilon * |t| := by ring
  have hsum := htri.trans (add_le_add (add_le_add hU hC0) hL1)
  simpa [P, U, C0, L1, add_assoc] using hsum

/-- Divided-tail bound on the outer part of the punctured line. The hypotheses
`hsqrt` and `hlinear` are the algebraic consequences of the hole choice. -/
theorem weightedJet_tail_outer_bound_sixty_four
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) {t : ℝ}
    (ht : |t| ≤ schmInteriorS) (ht0 : t ≠ 0)
    (hsqrt : Real.sqrt epsilon ≤ t ^ 2)
    (hlinear : (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2) :
    interiorVecNorm
        (fun i : Fin N =>
          (polynomialTailDivX2 (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v)).eval t) ≤
      2 * A + jetErrorConst * A + 64 * A := by
  let P : Fin N → Polynomial ℝ := fun i =>
    univariateRestriction (Q i) (0 : Fin 4 → ℝ) v
  let M : ℝ := 2 * A + jetErrorConst * A + 64 * A
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hJ0 : 0 ≤ jetErrorConst := jetErrorConst_pos.le
  have ht2non : 0 ≤ t ^ 2 := sq_nonneg t
  have hres0 := weightedJet_residual_norm_bound_sixty_four heps hk hA Q hdeg hlocal
    hzeroLines hv ht
  have hlocalTerm : A * (Real.sqrt epsilon + t ^ 2) ≤ 2 * A * t ^ 2 := by
    nlinarith
  have hconstTerm : jetErrorConst * A * Real.sqrt epsilon ≤ jetErrorConst * A * t ^ 2 := by
    have hcoef : 0 ≤ jetErrorConst * A := mul_nonneg hJ0 hA0
    exact mul_le_mul_of_nonneg_left hsqrt hcoef
  have hlinearTerm : 64 * (A * (k : ℝ) * Real.sqrt epsilon) * |t| ≤
      64 * A * t ^ 2 := by
    have hcoef : 0 ≤ 64 * A := mul_nonneg (by norm_num) hA0
    calc
      64 * (A * (k : ℝ) * Real.sqrt epsilon) * |t|
          = (64 * A) * ((k : ℝ) * Real.sqrt epsilon * |t|) := by ring
      _ ≤ (64 * A) * t ^ 2 :=
        mul_le_mul_of_nonneg_left hlinear hcoef
      _ = 64 * A * t ^ 2 := by ring
  have hres : interiorVecNorm
        (fun i : Fin N => (P i).eval t - (P i).coeff 0 - (P i).coeff 1 * t) ≤
      M * t ^ 2 := by
    have hsum := hres0.trans (add_le_add (add_le_add hlocalTerm hconstTerm) hlinearTerm)
    dsimp [P, M] at hsum ⊢
    nlinarith
  exact interiorVecNorm_polynomialTailDivX2_eval_le_of_residual_bound P ht0 hres

/-- Divided-tail bound on the outer part of the punctured line. The hypotheses
`hsqrt` and `hlinear` are the algebraic consequences of the hole choice. -/
theorem weightedJet_tail_outer_bound_quarter
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) {t : ℝ}
    (ht : |t| ≤ schmInteriorS) (ht0 : t ≠ 0)
    (hsqrt : Real.sqrt epsilon ≤ t ^ 2)
    (hlinear : (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2) :
    interiorVecNorm
        (fun i : Fin N =>
          (polynomialTailDivX2 (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v)).eval t) ≤
      2 * A + jetErrorConst * A + weightedJetQuarterConst * A := by
  let P : Fin N → Polynomial ℝ := fun i =>
    univariateRestriction (Q i) (0 : Fin 4 → ℝ) v
  let M : ℝ := 2 * A + jetErrorConst * A + weightedJetQuarterConst * A
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hJ0 : 0 ≤ jetErrorConst := jetErrorConst_pos.le
  have hW0 : 0 ≤ weightedJetQuarterConst := weightedJetQuarterConst_nonneg
  have ht2non : 0 ≤ t ^ 2 := sq_nonneg t
  have hres0 := weightedJet_residual_norm_bound_quarter heps hk hA Q hdeg hlocal
    hzeroLines hv ht
  have hlocalTerm : A * (Real.sqrt epsilon + t ^ 2) ≤ 2 * A * t ^ 2 := by
    nlinarith
  have hconstTerm : jetErrorConst * A * Real.sqrt epsilon ≤ jetErrorConst * A * t ^ 2 := by
    have hcoef : 0 ≤ jetErrorConst * A := mul_nonneg hJ0 hA0
    exact mul_le_mul_of_nonneg_left hsqrt hcoef
  have hlinearTerm : weightedJetQuarterConst * A * (k : ℝ) * Real.sqrt epsilon * |t| ≤
      weightedJetQuarterConst * A * t ^ 2 := by
    have hcoef : 0 ≤ weightedJetQuarterConst * A := mul_nonneg hW0 hA0
    calc
      weightedJetQuarterConst * A * (k : ℝ) * Real.sqrt epsilon * |t|
          = (weightedJetQuarterConst * A) * ((k : ℝ) * Real.sqrt epsilon * |t|) := by ring
      _ ≤ (weightedJetQuarterConst * A) * t ^ 2 :=
        mul_le_mul_of_nonneg_left hlinear hcoef
  have hres : interiorVecNorm
        (fun i : Fin N => (P i).eval t - (P i).coeff 0 - (P i).coeff 1 * t) ≤
      M * t ^ 2 := by
    have hsum := hres0.trans (add_le_add (add_le_add hlocalTerm hconstTerm) hlinearTerm)
    dsimp [P, M] at hsum ⊢
    nlinarith
  exact interiorVecNorm_polynomialTailDivX2_eval_le_of_residual_bound P ht0 hres

/-- From the outer divided-tail estimate and the symmetric-gap Remez interface,
obtain a derivative bound for the divided tail at the origin.  The explicit
coefficient constants are assembled later in
`symmetricHole_weightedJet_ordered_coeff_bounds`. -/
theorem weightedJet_tail_derivative_bound_from_outer_quarter
    {N k ell : ℕ} {epsilon A rho : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (hrho : 0 < rho)
    (hrhoSmall : rho < schmInteriorS / 2)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1)
    (hsqrtOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      Real.sqrt epsilon ≤ t ^ 2)
    (hlinearOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2) :
    ∃ C : ℝ, 0 < C ∧
      interiorVecNorm
          (fun i : Fin N =>
            ((Polynomial.derivative^[ell])
              (polynomialTailDivX2
                (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v))).eval 0) ≤
        C * (k : ℝ) ^ ell *
          (2 * A + jetErrorConst * A + weightedJetQuarterConst * A) := by
  let P : Fin N → Polynomial ℝ := fun i =>
    polynomialTailDivX2 (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v)
  let M : ℝ := 2 * A + jetErrorConst * A + weightedJetQuarterConst * A
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hM : 0 ≤ M := by
    dsimp [M]
    nlinarith [jetErrorConst_pos.le, weightedJetQuarterConst_nonneg, hA0]
  have hdegP : ∀ i, (P i).natDegree ≤ k := by
    intro i
    dsimp [P]
    exact (polynomialTailDivX2_natDegree_le _).trans
      ((univariateRestriction_natDegree_le (Q i) (0 : Fin 4 → ℝ) v).trans (hdeg i))
  have houter : ∀ t : ℝ,
      (rho ≤ |t| ∧ |t| ≤ schmInteriorS) →
        interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M := by
    intro t ht
    have ht0 : t ≠ 0 := by
      intro htz
      subst t
      simp at ht
      linarith
    dsimp [P, M]
    exact weightedJet_tail_outer_bound_quarter heps hk hA Q hdeg hlocal hzeroLines hv
      ht.2 ht0 (hsqrtOuter t ht) (hlinearOuter t ht)
  obtain ⟨R, c, hRpos, hcpos, hfull⟩ :=
    symmetric_gap_remez_vector P hrho hrhoSmall hM hdegP houter
  let Mfull : ℝ := R * Real.exp (c * (k : ℝ) * rho / schmInteriorS) * M
  have hMfull : 0 ≤ Mfull := by
    dsimp [Mfull]
    positivity
  have hfull' : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ Mfull := by
    intro t ht
    simpa [Mfull] using hfull t ht
  obtain ⟨B, hBpos, hbern⟩ := interior_bernstein_vector (ell := ell) P hMfull hdegP hfull'
  refine ⟨B * R * Real.exp (c * (k : ℝ) * rho / schmInteriorS), ?_, ?_⟩
  · positivity
  · calc
      interiorVecNorm
          (fun i : Fin N =>
            ((Polynomial.derivative^[ell])
              (polynomialTailDivX2
                (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v))).eval 0)
          = interiorVecNorm
              (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) := rfl
      _ ≤ B * (k : ℝ) ^ ell * Mfull := hbern
      _ = (B * R * Real.exp (c * (k : ℝ) * rho / schmInteriorS)) *
          (k : ℝ) ^ ell * M := by
            dsimp [Mfull]
            ring

/-- Unit-direction homogeneous-jet bound obtained from the divided-tail
Remez/Bernstein derivative estimate. -/
theorem weightedJet_higher_eval_bound_from_outer_quarter
    {N k ell : ℕ} {epsilon A rho : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (hrho : 0 < rho)
    (hrhoSmall : rho < schmInteriorS / 2)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1)
    (hsqrtOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      Real.sqrt epsilon ≤ t ^ 2)
    (hlinearOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2) :
    ∃ C : ℝ, 0 < C ∧
      interiorVecNorm
          (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 (ell + 2) Q i)) ≤
        C * (k : ℝ) ^ ell *
          (2 * A + jetErrorConst * A + weightedJetQuarterConst * A) := by
  obtain ⟨C, hCpos, hderiv⟩ :=
    weightedJet_tail_derivative_bound_from_outer_quarter (ell := ell) heps hk hA
      hrho hrhoSmall Q hdeg hlocal hzeroLines hv hsqrtOuter hlinearOuter
  refine ⟨C, hCpos, ?_⟩
  exact homogeneousPart_eval_norm_le_of_tail_derivative_norm_le Q v hderiv

end OptimalConvergenceRates
