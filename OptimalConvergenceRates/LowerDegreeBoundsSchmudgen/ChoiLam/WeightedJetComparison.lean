/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/WeightedJetComparison.lean

  Degree-four comparison turning weighted-jet estimates into the Choi-Lam lower-bound constant.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.WeightedJet.Analytic
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.WeightedJet.CertificateExtraction

open MvPolynomial Finset
open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates

private def degreeFourQuarterErrorSummandConst (J : Finset (Fin 4)) : ℝ :=
  let K0 : ℝ := jetErrorConst * schmInteriorLocalControlConst
  let KQ : ℝ := weightedJetQuarterConst * schmInteriorLocalControlConst
  2 * K0 * KQ + 2 * KQ * KQ +
    coeffNorm4 (homogeneousPart4 1
        (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
      (2 * K0 * KQ + 2 * KQ * KQ) +
    coeffNorm4 (homogeneousPart4 2
        (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
      (2 * K0 * KQ + KQ ^ 2) +
    coeffNorm4 (homogeneousPart4 3
        (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
      (2 * K0 * KQ) +
    coeffNorm4 (homogeneousPart4 4
        (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
      (K0 ^ 2)

private noncomputable def degreeFourQuarterErrorConst : ℝ :=
  1 + ∑ J ∈ Finset.univ.powerset, degreeFourQuarterErrorSummandConst J

private theorem degreeFourQuarterErrorConst_pos : 0 < degreeFourQuarterErrorConst := by
  unfold degreeFourQuarterErrorConst
  have hsum_nonneg : 0 ≤ ∑ J ∈ Finset.univ.powerset,
      degreeFourQuarterErrorSummandConst J := by
    apply Finset.sum_nonneg
    intro J _hJ
    unfold degreeFourQuarterErrorSummandConst
    let K0 : ℝ := jetErrorConst * schmInteriorLocalControlConst
    let KQ : ℝ := weightedJetQuarterConst * schmInteriorLocalControlConst
    have hK0 : 0 ≤ K0 := by
      dsimp [K0]
      exact mul_nonneg jetErrorConst_pos.le schmInteriorLocalControlConst_pos.le
    have hKQ : 0 ≤ KQ := by
      dsimp [KQ]
      exact mul_nonneg weightedJetQuarterConst_pos.le schmInteriorLocalControlConst_pos.le
    have hg1 : 0 ≤ coeffNorm4 (homogeneousPart4 1
        (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) := coeffNorm4_nonneg _
    have hg2 : 0 ≤ coeffNorm4 (homogeneousPart4 2
        (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) := coeffNorm4_nonneg _
    have hg3 : 0 ≤ coeffNorm4 (homogeneousPart4 3
        (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) := coeffNorm4_nonneg _
    have hg4 : 0 ≤ coeffNorm4 (homogeneousPart4 4
        (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) := coeffNorm4_nonneg _
    positivity
  linarith

private theorem schmInteriorEpsilon0_le_one_quarter : schmInteriorEpsilon0 ≤ 1 := by
  unfold schmInteriorEpsilon0
  have hnon : 0 ≤ schmInteriorLowerBoundConst / 4 := by
    exact div_nonneg schmInteriorLowerBoundConst_pos.le (by norm_num)
  have hle : schmInteriorLowerBoundConst / 4 ≤ 1 := by
    have hgamma := schmInteriorLowerBoundConst_le_gamma
    have hgam : weightedJetGamma0 ≤ 1 := by
      unfold weightedJetGamma0
      norm_num
    nlinarith
  exact pow_le_one₀ hnon hle

theorem box_preordering_certificate_degree_four_explicit_error_bound_quarter
    {epsilon : ℝ} {r : ℕ}
    (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0)
    (hr : 1 ≤ r)
    (hrSmall : (r : ℝ) ≤ weightedJetGamma0 * epsilon ^ (-(1 : ℝ) / 4))
    (hcert : choiLamQuartic + MvPolynomial.C epsilon ∈ BoxPreordering 4 r) :
    ∃ (N : Finset (Fin 4) → ℕ)
      (Q : ∀ J : Finset (Fin 4), Fin (N J) → MvPolynomial (Fin 4) ℝ),
      Nonempty (DegreeBoundedSOS
        (∑ J ∈ Finset.univ.powerset, sosVectorSq4 (homogeneousPartVec4 2 (Q J))) 2) ∧
      choiLamQuartic =
        (∑ J ∈ Finset.univ.powerset, sosVectorSq4 (homogeneousPartVec4 2 (Q J))) +
          ∑ J ∈ Finset.univ.powerset, degreeFourWeightedSOSError J (Q J) ∧
      coeffNorm4 (∑ J ∈ Finset.univ.powerset, degreeFourWeightedSOSError J (Q J)) ≤
        degreeFourQuarterErrorConst * Real.sqrt epsilon * (r : ℝ) ^ 2 := by
  classical
  obtain ⟨σ, hσ, _hdeg, hsum⟩ :=
    box_preordering_certificate_sos_vectors_local_control_with_degree heps.le hcert
  let N : Finset (Fin 4) → ℕ := fun J => Classical.choose (hσ J)
  let Q : ∀ J : Finset (Fin 4), Fin (N J) → MvPolynomial (Fin 4) ℝ :=
    fun J => Classical.choose (Classical.choose_spec (hσ J))
  have hspec : ∀ J,
      σ J = sosVectorSq4 (Q J) ∧
      (∀ i, (Q J i).totalDegree ≤ r) ∧
      (∀ x, boxSmall x →
        interiorVecNorm (fun i : Fin (N J) => MvPolynomial.eval x (Q J i)) ≤
          schmInteriorLocalControlConst * (Real.sqrt epsilon + localSqNorm x)) ∧
      (∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
        interiorVecNorm
            (fun i : Fin (N J) =>
              MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q J i)) ≤
          schmInteriorLocalControlConst * Real.sqrt epsilon) := by
    intro J
    dsimp [N, Q]
    exact Classical.choose_spec (Classical.choose_spec (hσ J))
  have hQdeg : ∀ J, ∀ i, (Q J i).totalDegree ≤ r := fun J => (hspec J).2.1
  have hQ0 : ∀ J, vecCoeffNorm4 (homogeneousPartVec4 0 (Q J)) ≤
      jetErrorConst * schmInteriorLocalControlConst * Real.sqrt epsilon := by
    intro J
    exact weightedJetLemma_constant_bound heps one_le_schmInteriorLocalControlConst (Q J)
      (hspec J).2.2.2
  have hQ1 : ∀ J, vecCoeffNorm4 (homogeneousPartVec4 1 (Q J)) ≤
      weightedJetQuarterConst * schmInteriorLocalControlConst * (r : ℝ) *
        Real.sqrt epsilon := by
    intro J
    exact weightedJetLemma_linear_bound_quarter heps hr one_le_schmInteriorLocalControlConst
      (Q J) (hQdeg J) (hspec J).2.2.2
  have hQhigher : ∀ J,
      vecCoeffNorm4 (homogeneousPartVec4 2 (Q J)) ≤
          weightedJetQuarterConst * schmInteriorLocalControlConst ∧
      vecCoeffNorm4 (homogeneousPartVec4 3 (Q J)) ≤
          weightedJetQuarterConst * schmInteriorLocalControlConst * (r : ℝ) ∧
      vecCoeffNorm4 (homogeneousPartVec4 4 (Q J)) ≤
          weightedJetQuarterConst * schmInteriorLocalControlConst * (r : ℝ) ^ 2 := by
    intro J
    exact weightedJetLemma_higher_bounds_quarter heps heps0 hr
      one_le_schmInteriorLocalControlConst hrSmall (Q J) (hQdeg J)
      (hspec J).2.2.1 (hspec J).2.2.2
  have hdecomp : choiLamQuartic =
      (∑ J ∈ Finset.univ.powerset, sosVectorSq4 (homogeneousPartVec4 2 (Q J))) +
        ∑ J ∈ Finset.univ.powerset, degreeFourWeightedSOSError J (Q J) := by
    calc
      choiLamQuartic = homogeneousPart4 4 (choiLamQuartic + MvPolynomial.C epsilon) := by
        rw [homogeneousPart4_choiLamPerturbed]
      _ = homogeneousPart4 4 (∑ J ∈ Finset.univ.powerset,
            σ J * BoxSemialgebraicGeneratorProd J) := by rw [hsum]
      _ = ∑ J ∈ Finset.univ.powerset,
            homogeneousPart4 4 (σ J * BoxSemialgebraicGeneratorProd J) := by
        rw [homogeneousPart4_sum]
      _ = ∑ J ∈ Finset.univ.powerset,
            homogeneousPart4 4 (BoxSemialgebraicGeneratorProd J * sosVectorSq4 (Q J)) := by
        apply Finset.sum_congr rfl
        intro J _hJ
        rw [(hspec J).1]
        ring_nf
      _ = ∑ J ∈ Finset.univ.powerset,
          (sosVectorSq4 (homogeneousPartVec4 2 (Q J)) +
            degreeFourWeightedSOSError J (Q J)) := by
        apply Finset.sum_congr rfl
        intro J _hJ
        rw [degree_four_part_weighted_sos_term (J := J) (Q := Q J) (_r := r) (_epsilon := epsilon)]
      _ = (∑ J ∈ Finset.univ.powerset, sosVectorSq4 (homogeneousPartVec4 2 (Q J))) +
          ∑ J ∈ Finset.univ.powerset, degreeFourWeightedSOSError J (Q J) := by
        rw [← Finset.sum_add_distrib]
  let K0 : ℝ := jetErrorConst * schmInteriorLocalControlConst
  let KQ : ℝ := weightedJetQuarterConst * schmInteriorLocalControlConst
  let S : ℝ := Real.sqrt epsilon * (r : ℝ) ^ 2
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    exact mul_nonneg jetErrorConst_pos.le schmInteriorLocalControlConst_pos.le
  have hKQ : 0 ≤ KQ := by
    dsimp [KQ]
    exact mul_nonneg weightedJetQuarterConst_pos.le schmInteriorLocalControlConst_pos.le
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  have hcoeff_expr :
      coeffNorm4 (∑ J ∈ Finset.univ.powerset, degreeFourWeightedSOSError J (Q J)) ≤
        ∑ J ∈ Finset.univ.powerset,
          (2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ) ^ 2) +
            2 * (KQ * (r : ℝ) * Real.sqrt epsilon) * (KQ * (r : ℝ)) +
            coeffNorm4 (homogeneousPart4 1
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              (2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ)) +
                2 * (KQ * (r : ℝ) * Real.sqrt epsilon) * KQ) +
            coeffNorm4 (homogeneousPart4 2
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              (2 * (K0 * Real.sqrt epsilon) * KQ +
                (KQ * (r : ℝ) * Real.sqrt epsilon) ^ 2) +
            coeffNorm4 (homogeneousPart4 3
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              (2 * (K0 * Real.sqrt epsilon) *
                (KQ * (r : ℝ) * Real.sqrt epsilon)) +
            coeffNorm4 (homogeneousPart4 4
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              ((K0 * Real.sqrt epsilon) ^ 2)) := by
    dsimp [K0, KQ]
    apply degreeFourWeightedSOSError_sum_coeffNorm4_le_of_separate_jet_bounds
    · exact mul_nonneg (mul_nonneg jetErrorConst_pos.le schmInteriorLocalControlConst_pos.le)
        (Real.sqrt_nonneg epsilon)
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg weightedJetQuarterConst_pos.le schmInteriorLocalControlConst_pos.le)
          (Nat.cast_nonneg r)) (Real.sqrt_nonneg epsilon)
    · exact mul_nonneg weightedJetQuarterConst_pos.le schmInteriorLocalControlConst_pos.le
    · exact mul_nonneg
        (mul_nonneg weightedJetQuarterConst_pos.le schmInteriorLocalControlConst_pos.le)
        (Nat.cast_nonneg r)
    · exact mul_nonneg
        (mul_nonneg weightedJetQuarterConst_pos.le schmInteriorLocalControlConst_pos.le)
        (sq_nonneg (r : ℝ))
    · exact hQ0
    · exact hQ1
    · intro J; exact (hQhigher J).1
    · intro J; exact (hQhigher J).2.1
    · intro J; exact (hQhigher J).2.2
  have hsum_bound :
      ∑ J ∈ Finset.univ.powerset,
          (2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ) ^ 2) +
            2 * (KQ * (r : ℝ) * Real.sqrt epsilon) * (KQ * (r : ℝ)) +
            coeffNorm4 (homogeneousPart4 1
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              (2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ)) +
                2 * (KQ * (r : ℝ) * Real.sqrt epsilon) * KQ) +
            coeffNorm4 (homogeneousPart4 2
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              (2 * (K0 * Real.sqrt epsilon) * KQ +
                (KQ * (r : ℝ) * Real.sqrt epsilon) ^ 2) +
            coeffNorm4 (homogeneousPart4 3
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              (2 * (K0 * Real.sqrt epsilon) *
                (KQ * (r : ℝ) * Real.sqrt epsilon)) +
            coeffNorm4 (homogeneousPart4 4
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              ((K0 * Real.sqrt epsilon) ^ 2)) ≤
        degreeFourQuarterErrorConst * S := by
    have heps_le_one : epsilon ≤ 1 := le_trans heps0 schmInteriorEpsilon0_le_one_quarter
    have hsqrt_nonneg : 0 ≤ Real.sqrt epsilon := Real.sqrt_nonneg _
    have heps_le_sqrt : epsilon ≤ Real.sqrt epsilon := by
      have hsqrt_le_one : Real.sqrt epsilon ≤ 1 := by
        have h := Real.sqrt_le_sqrt heps_le_one
        simpa using h
      have heps_eq : epsilon = Real.sqrt epsilon * Real.sqrt epsilon := by
        symm
        rw [show Real.sqrt epsilon * Real.sqrt epsilon = (Real.sqrt epsilon) ^ 2 by ring]
        exact Real.sq_sqrt heps.le
      calc
        epsilon = Real.sqrt epsilon * Real.sqrt epsilon := heps_eq
        _ ≤ Real.sqrt epsilon := mul_le_of_le_one_right hsqrt_nonneg hsqrt_le_one
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    have hr_le_r2 : (r : ℝ) ≤ (r : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (r : ℝ) := hrR
      nlinarith [mul_le_mul_of_nonneg_left h1 hr0]
    have hone_le_r2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [hrR]
    have hsqrt_le_S : Real.sqrt epsilon ≤ S := by
      dsimp [S]
      exact calc
        Real.sqrt epsilon = Real.sqrt epsilon * 1 := by ring
        _ ≤ Real.sqrt epsilon * (r : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hone_le_r2 hsqrt_nonneg
    have hsqrt_r_le_S : Real.sqrt epsilon * (r : ℝ) ≤ S := by
      dsimp [S]
      exact mul_le_mul_of_nonneg_left hr_le_r2 hsqrt_nonneg
    have heps_r2_le_S : epsilon * (r : ℝ) ^ 2 ≤ S := by
      dsimp [S]
      exact mul_le_mul_of_nonneg_right heps_le_sqrt (sq_nonneg (r : ℝ))
    have heps_r_le_S : epsilon * (r : ℝ) ≤ S := by
      have h := mul_le_mul_of_nonneg_left hr_le_r2 heps.le
      exact le_trans h (by
        dsimp [S]
        exact mul_le_mul_of_nonneg_right heps_le_sqrt (sq_nonneg (r : ℝ)))
    have heps_le_S : epsilon ≤ S := le_trans heps_le_sqrt hsqrt_le_S
    have hsum_le :
        ∑ J ∈ Finset.univ.powerset,
          (2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ) ^ 2) +
            2 * (KQ * (r : ℝ) * Real.sqrt epsilon) * (KQ * (r : ℝ)) +
            coeffNorm4 (homogeneousPart4 1
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              (2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ)) +
                2 * (KQ * (r : ℝ) * Real.sqrt epsilon) * KQ) +
            coeffNorm4 (homogeneousPart4 2
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              (2 * (K0 * Real.sqrt epsilon) * KQ +
                (KQ * (r : ℝ) * Real.sqrt epsilon) ^ 2) +
            coeffNorm4 (homogeneousPart4 3
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              (2 * (K0 * Real.sqrt epsilon) *
                (KQ * (r : ℝ) * Real.sqrt epsilon)) +
            coeffNorm4 (homogeneousPart4 4
                (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) *
              ((K0 * Real.sqrt epsilon) ^ 2)) ≤
          (∑ J ∈ Finset.univ.powerset, degreeFourQuarterErrorSummandConst J) * S := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro J _hJ
      have hg1 : 0 ≤ coeffNorm4 (homogeneousPart4 1
          (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) := coeffNorm4_nonneg _
      have hg2 : 0 ≤ coeffNorm4 (homogeneousPart4 2
          (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) := coeffNorm4_nonneg _
      have hg3 : 0 ≤ coeffNorm4 (homogeneousPart4 3
          (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) := coeffNorm4_nonneg _
      have hg4 : 0 ≤ coeffNorm4 (homogeneousPart4 4
          (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 4) ℝ)) := coeffNorm4_nonneg _
      have h04 : 2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ) ^ 2) ≤
          (2 * K0 * KQ) * S := by
        dsimp [S]
        ring_nf
        exact le_rfl
      have h13 : 2 * (KQ * (r : ℝ) * Real.sqrt epsilon) * (KQ * (r : ℝ)) ≤
          (2 * KQ * KQ) * S := by
        dsimp [S]
        ring_nf
        exact le_rfl
      have h03 : 2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ)) ≤
          (2 * K0 * KQ) * S := by
        have hcoef : 0 ≤ 2 * K0 * KQ := by positivity
        have hmul := mul_le_mul_of_nonneg_left hsqrt_r_le_S hcoef
        calc
          2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ)) =
              (2 * K0 * KQ) * (Real.sqrt epsilon * (r : ℝ)) := by ring
          _ ≤ (2 * K0 * KQ) * S := hmul
      have h12 : 2 * (KQ * (r : ℝ) * Real.sqrt epsilon) * KQ ≤
          (2 * KQ * KQ) * S := by
        have hcoef : 0 ≤ 2 * KQ * KQ := by positivity
        have hmul := mul_le_mul_of_nonneg_left hsqrt_r_le_S hcoef
        calc
          2 * (KQ * (r : ℝ) * Real.sqrt epsilon) * KQ =
              (2 * KQ * KQ) * (Real.sqrt epsilon * (r : ℝ)) := by ring
          _ ≤ (2 * KQ * KQ) * S := hmul
      have h02 : 2 * (K0 * Real.sqrt epsilon) * KQ ≤
          (2 * K0 * KQ) * S := by
        have hcoef : 0 ≤ 2 * K0 * KQ := by positivity
        have hmul := mul_le_mul_of_nonneg_left hsqrt_le_S hcoef
        calc
          2 * (K0 * Real.sqrt epsilon) * KQ =
              (2 * K0 * KQ) * Real.sqrt epsilon := by ring
          _ ≤ (2 * K0 * KQ) * S := hmul
      have h11 : (KQ * (r : ℝ) * Real.sqrt epsilon) ^ 2 ≤
          (KQ ^ 2) * S := by
        have hmul := mul_le_mul_of_nonneg_left heps_r2_le_S (sq_nonneg KQ)
        calc
          (KQ * (r : ℝ) * Real.sqrt epsilon) ^ 2 =
              KQ ^ 2 * (epsilon * (r : ℝ) ^ 2) := by
            rw [show (KQ * (r : ℝ) * Real.sqrt epsilon) ^ 2 =
                KQ ^ 2 * ((Real.sqrt epsilon) ^ 2 * (r : ℝ) ^ 2) by ring]
            rw [Real.sq_sqrt heps.le]
          _ ≤ KQ ^ 2 * S := hmul
      have h01 : 2 * (K0 * Real.sqrt epsilon) *
            (KQ * (r : ℝ) * Real.sqrt epsilon) ≤
          (2 * K0 * KQ) * S := by
        have hcoef : 0 ≤ 2 * K0 * KQ := by positivity
        have hmul := mul_le_mul_of_nonneg_left heps_r_le_S hcoef
        calc
          2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ) * Real.sqrt epsilon) =
              (2 * K0 * KQ) * (epsilon * (r : ℝ)) := by
            rw [show 2 * (K0 * Real.sqrt epsilon) * (KQ * (r : ℝ) * Real.sqrt epsilon) =
                (2 * K0 * KQ) * ((Real.sqrt epsilon) ^ 2 * (r : ℝ)) by ring]
            rw [Real.sq_sqrt heps.le]
          _ ≤ (2 * K0 * KQ) * S := hmul
      have h00 : (K0 * Real.sqrt epsilon) ^ 2 ≤ (K0 ^ 2) * S := by
        have hmul := mul_le_mul_of_nonneg_left heps_le_S (sq_nonneg K0)
        calc
          (K0 * Real.sqrt epsilon) ^ 2 = K0 ^ 2 * epsilon := by
            rw [show (K0 * Real.sqrt epsilon) ^ 2 = K0 ^ 2 * (Real.sqrt epsilon) ^ 2 by ring]
            rw [Real.sq_sqrt heps.le]
          _ ≤ K0 ^ 2 * S := hmul
      have hg1b := mul_le_mul_of_nonneg_left (add_le_add h03 h12) hg1
      have hg2b := mul_le_mul_of_nonneg_left (add_le_add h02 h11) hg2
      have hg3b := mul_le_mul_of_nonneg_left h01 hg3
      have hg4b := mul_le_mul_of_nonneg_left h00 hg4
      unfold degreeFourQuarterErrorSummandConst
      dsimp [K0, KQ]
      nlinarith [h04, h13, hg1b, hg2b, hg3b, hg4b]
    have hconst_le :
        (∑ J ∈ Finset.univ.powerset, degreeFourQuarterErrorSummandConst J) * S ≤
          degreeFourQuarterErrorConst * S := by
      unfold degreeFourQuarterErrorConst
      nlinarith [hS_nonneg]
    exact le_trans hsum_le hconst_le
  refine ⟨N, Q, finite_sum_quadratic_jet_degreeBoundedSOS Q, hdecomp, ?_⟩
  simpa [S, mul_assoc] using le_trans hcoeff_expr hsum_bound

noncomputable def schmInteriorLowerBoundConst4 : ℝ :=
  min weightedJetGamma0
    (min 1 (Real.sqrt (choiLamSosDistance / (2 * degreeFourQuarterErrorConst))))

theorem schmInteriorLowerBoundConst4_pos : 0 < schmInteriorLowerBoundConst4 := by
  unfold schmInteriorLowerBoundConst4
  apply lt_min
  · exact weightedJetGamma0_pos
  · apply lt_min
    · norm_num
    · apply Real.sqrt_pos_of_pos
      exact div_pos choiLamSosDistance_pos
        (mul_pos (by norm_num) degreeFourQuarterErrorConst_pos)

theorem schmInteriorLowerBoundConst4_nonneg : 0 ≤ schmInteriorLowerBoundConst4 :=
  schmInteriorLowerBoundConst4_pos.le

theorem schmInteriorLowerBoundConst4_le_gamma :
    schmInteriorLowerBoundConst4 ≤ weightedJetGamma0 := by
  unfold schmInteriorLowerBoundConst4
  exact min_le_left _ _

private theorem schmInteriorLowerBoundConst4_sq_le_distance :
    schmInteriorLowerBoundConst4 ^ 2 ≤
      choiLamSosDistance / (2 * degreeFourQuarterErrorConst) := by
  have hle : schmInteriorLowerBoundConst4 ≤
      Real.sqrt (choiLamSosDistance / (2 * degreeFourQuarterErrorConst)) := by
    unfold schmInteriorLowerBoundConst4
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hnon : 0 ≤ schmInteriorLowerBoundConst4 := schmInteriorLowerBoundConst4_nonneg
  have harg_non : 0 ≤ choiLamSosDistance / (2 * degreeFourQuarterErrorConst) := by
    exact div_nonneg choiLamSosDistance_pos.le
      (mul_nonneg (by norm_num) degreeFourQuarterErrorConst_pos.le)
  have hsqrt_sq :
      (Real.sqrt (choiLamSosDistance / (2 * degreeFourQuarterErrorConst))) ^ 2 =
        choiLamSosDistance / (2 * degreeFourQuarterErrorConst) :=
    Real.sq_sqrt harg_non
  calc
    schmInteriorLowerBoundConst4 ^ 2
        ≤ (Real.sqrt (choiLamSosDistance / (2 * degreeFourQuarterErrorConst))) ^ 2 :=
          pow_le_pow_left₀ hnon hle 2
    _ = choiLamSosDistance / (2 * degreeFourQuarterErrorConst) := hsqrt_sq

private theorem sqrt_mul_pow_two_le_of_quarter
    {epsilon c : ℝ} {r : ℕ}
    (heps : 0 < epsilon)
    (hsmall : (r : ℝ) ≤ c * epsilon ^ (-(1 : ℝ) / 4)) :
    Real.sqrt epsilon * (r : ℝ) ^ 2 ≤ c ^ 2 := by
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hpow := Real.rpow_le_rpow hr0 hsmall (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
  have hpow' : (r : ℝ) ^ 2 ≤ (c * epsilon ^ (-(1 : ℝ) / 4)) ^ 2 := by
    simpa using hpow
  have hright : (c * epsilon ^ (-(1 : ℝ) / 4)) ^ 2 =
      c ^ 2 * epsilon ^ (-(1 : ℝ) / 2) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (le_of_lt heps)]
    norm_num
  rw [hright] at hpow'
  have hsqrt : Real.sqrt epsilon = epsilon ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow epsilon
  rw [hsqrt]
  calc
    epsilon ^ ((1 : ℝ) / 2) * (r : ℝ) ^ 2
        ≤ epsilon ^ ((1 : ℝ) / 2) * (c ^ 2 * epsilon ^ (-(1 : ℝ) / 2)) := by
          exact mul_le_mul_of_nonneg_left hpow' (Real.rpow_nonneg heps.le _)
    _ = c ^ 2 := by
      rw [show epsilon ^ ((1 : ℝ) / 2) * (c ^ 2 * epsilon ^ (-(1 : ℝ) / 2)) =
          c ^ 2 * (epsilon ^ ((1 : ℝ) / 2) * epsilon ^ (-(1 : ℝ) / 2)) by ring]
      rw [← Real.rpow_add heps]
      norm_num

private theorem degreeFourWeightedSOSError_explicit_bound_lt_distance_of_quarter
    {epsilon : ℝ} {r : ℕ}
    (heps : 0 < epsilon)
    (hsmall : (r : ℝ) ≤ schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4)) :
    degreeFourQuarterErrorConst * Real.sqrt epsilon * (r : ℝ) ^ 2 <
      choiLamSosDistance := by
  let c : ℝ := schmInteriorLowerBoundConst4
  have hS_le : Real.sqrt epsilon * (r : ℝ) ^ 2 ≤ c ^ 2 := by
    dsimp [c]
    exact sqrt_mul_pow_two_le_of_quarter heps hsmall
  have hD_nonneg : 0 ≤ degreeFourQuarterErrorConst := degreeFourQuarterErrorConst_pos.le
  have hD_le :
      degreeFourQuarterErrorConst * (Real.sqrt epsilon * (r : ℝ) ^ 2) ≤
        degreeFourQuarterErrorConst * c ^ 2 :=
    mul_le_mul_of_nonneg_left hS_le hD_nonneg
  have hD_c_le_half :
      degreeFourQuarterErrorConst * c ^ 2 ≤ choiLamSosDistance / 2 := by
    have hc_sq : c ^ 2 ≤ choiLamSosDistance / (2 * degreeFourQuarterErrorConst) := by
      dsimp [c]
      exact schmInteriorLowerBoundConst4_sq_le_distance
    calc
      degreeFourQuarterErrorConst * c ^ 2 ≤
          degreeFourQuarterErrorConst *
            (choiLamSosDistance / (2 * degreeFourQuarterErrorConst)) := by
        exact mul_le_mul_of_nonneg_left hc_sq hD_nonneg
      _ = choiLamSosDistance / 2 := by
        field_simp [degreeFourQuarterErrorConst_pos.ne']
  have hhalf_lt : choiLamSosDistance / 2 < choiLamSosDistance := by
    nlinarith [choiLamSosDistance_pos]
  calc
    degreeFourQuarterErrorConst * Real.sqrt epsilon * (r : ℝ) ^ 2
        = degreeFourQuarterErrorConst * (Real.sqrt epsilon * (r : ℝ) ^ 2) := by ring
    _ ≤ degreeFourQuarterErrorConst * c ^ 2 := hD_le
    _ ≤ choiLamSosDistance / 2 := hD_c_le_half
    _ < choiLamSosDistance := hhalf_lt

theorem box_preordering_degree_four_sos_too_close_quarter
    {epsilon : ℝ} {r : ℕ}
    (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0)
    (hsmall : (r : ℝ) ≤ schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4))
    (hmem : choiLamQuartic + MvPolynomial.C epsilon ∈ BoxPreordering 4 r) :
    False := by
  classical
  have hr : 1 ≤ r := by
    by_contra hr0
    have hreq : r = 0 := by omega
    obtain ⟨σ, _hsos, hdeg, hsum⟩ := hmem
    let m : Fin 4 →₀ ℕ := Finsupp.single (0 : Fin 4) 4
    have hmdeg : m.sum (fun _ e => e) = 4 := by
      dsimp [m]
      simp
    have hsum_coeff_zero :
        legacyMvCoeff m
          (∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J) = 0 := by
      rw [MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro J _hJ
      apply coeff_eq_zero_of_totalDegree_lt_n4
      · have hj := hdeg J
        omega
      · rw [hmdeg]
        omega
    have hleft_coeff : legacyMvCoeff m (choiLamQuartic + MvPolynomial.C epsilon) = 1 := by
      dsimp [m]
      rw [choiLamQuartic_coeff_single_zero_four_weightedJet]
      have hC : (0 : Fin 4 →₀ ℕ) ≠ Finsupp.single (0 : Fin 4) 4 := by
        intro h
        have := Finsupp.ext_iff.mp h (0 : Fin 4)
        simp at this
      simp [MvPolynomial.coeff_C, hC]
    rw [hsum] at hleft_coeff
    rw [hsum_coeff_zero] at hleft_coeff
    norm_num at hleft_coeff
  have hrSmallGamma : (r : ℝ) ≤ weightedJetGamma0 * epsilon ^ (-(1 : ℝ) / 4) := by
    calc
      (r : ℝ) ≤ schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4) := hsmall
      _ ≤ weightedJetGamma0 * epsilon ^ (-(1 : ℝ) / 4) := by
        exact mul_le_mul_of_nonneg_right schmInteriorLowerBoundConst4_le_gamma
          (Real.rpow_nonneg heps.le _)
  obtain ⟨N, Q, hS, hdecomp, hcoeff⟩ :=
    box_preordering_certificate_degree_four_explicit_error_bound_quarter heps heps0 hr
      hrSmallGamma hmem
  exact choiLam_sos_contradiction_of_coeffNorm_lt hS hdecomp
    (lt_of_le_of_lt hcoeff
      (degreeFourWeightedSOSError_explicit_bound_lt_distance_of_quarter heps hsmall))

theorem degree_four_comparison_error_bound_quarter
    {epsilon : ℝ} {r : ℕ}
    (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0)
    (hsmall : (r : ℝ) ≤ schmInteriorLowerBoundConst4 * epsilon ^ (-(1 : ℝ) / 4))
    (hmem : choiLamQuartic + MvPolynomial.C epsilon ∈ BoxPreordering 4 r) :
    False := by
  exact box_preordering_degree_four_sos_too_close_quarter heps heps0 hsmall hmem

end OptimalConvergenceRates

end
