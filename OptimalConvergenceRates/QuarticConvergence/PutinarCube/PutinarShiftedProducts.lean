/-
  Exact elimination of the temporarily shifted cube generators.

  The proof follows the manuscript's Chebyshev split.  It uses the explicit
  localized-product certificates and the explicit SOS residuals; in
  particular, it never invokes a nonnegative-polynomial-to-SOS principle.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarSplit
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarLocalizedProducts
import OptimalConvergenceRates.BaldiSlot2024.ScaledSchmudgen
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

open MvPolynomial Finset Polynomial
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n : ℕ}

/-! ## The leading scalar in the localized expansion -/

/-- The normalized correction contributed by localized products of
cardinality at least two. -/
def putinarShiftCorrectionRatio (t : ℝ) (I : Finset (Fin n)) : ℝ :=
  ∑ J ∈ I.powerset, if 2 ≤ J.card then t ^ J.card else 0

/-- The unnormalized correction in the expansion of
`∏ i∈I, (η + a_i)`. -/
def putinarShiftCorrection (k : ℕ) (η : ℝ) (I : Finset (Fin n)) : ℝ :=
  ∑ J ∈ I.powerset, if 2 ≤ J.card then
    η ^ (I.card - J.card) * putinarPairMu k ^ J.card
  else 0

/-- Grouping the normalized correction by subset cardinality. -/
theorem putinarShiftCorrectionRatio_eq_card_sum
    (t : ℝ) (I : Finset (Fin n)) :
    putinarShiftCorrectionRatio t I =
      ∑ j ∈ Finset.range (I.card + 1),
        (I.card.choose j : ℝ) * (if 2 ≤ j then t ^ j else 0) := by
  unfold putinarShiftCorrectionRatio
  simpa only [nsmul_eq_mul] using
    (Finset.sum_powerset_apply_card
      (α := ℝ) (fun j ↦ if 2 ≤ j then t ^ j else 0) (x := I))

/-- The finite binomial/geometric estimate used for the leading constant.
There is no appeal to an infinite-series value in the certificate proof. -/
theorem putinarShiftCorrectionRatio_le_half
    (I : Finset (Fin n)) {t : ℝ}
    (ht : 0 ≤ t) (hnt : (n : ℝ) * t ≤ 1 / 2) :
    putinarShiftCorrectionRatio t I ≤ 1 / 2 := by
  rw [putinarShiftCorrectionRatio_eq_card_sum]
  calc
    (∑ j ∈ Finset.range (I.card + 1),
        (I.card.choose j : ℝ) * (if 2 ≤ j then t ^ j else 0)) ≤
        ∑ j ∈ Finset.range (I.card + 1),
          if 2 ≤ j then (1 / 2 : ℝ) ^ j else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases htwo : 2 ≤ j
      · simp only [htwo, if_pos]
        have hchooseNat : I.card.choose j ≤ I.card ^ j :=
          Nat.choose_le_pow I.card j
        have hchoose : (I.card.choose j : ℝ) ≤ (I.card : ℝ) ^ j := by
          exact_mod_cast hchooseNat
        have hcardNat : I.card ≤ n := by
          simpa using Finset.card_le_univ I
        have hcard : (I.card : ℝ) ≤ n := by exact_mod_cast hcardNat
        have hcardt : (I.card : ℝ) * t ≤ (n : ℝ) * t :=
          mul_le_mul_of_nonneg_right hcard ht
        calc
          (I.card.choose j : ℝ) * t ^ j ≤
              (I.card : ℝ) ^ j * t ^ j :=
            mul_le_mul_of_nonneg_right hchoose (pow_nonneg ht j)
          _ = ((I.card : ℝ) * t) ^ j := by rw [mul_pow]
          _ ≤ ((n : ℝ) * t) ^ j :=
            pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) ht) hcardt j
          _ ≤ (1 / 2 : ℝ) ^ j :=
            pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) ht) hnt j
      · simp only [htwo, if_false, mul_zero]
        exact le_rfl
    _ = ∑ j ∈ Finset.Ico 2 (I.card + 1), (1 / 2 : ℝ) ^ j := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp [Finset.mem_Ico, and_comm]
    _ ≤ (1 / 2 : ℝ) ^ 2 / (1 - 1 / 2) :=
      geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = 1 / 2 := by norm_num

/-- Factoring out `η^|I|` identifies the raw correction with its
dimensionless ratio. -/
theorem putinarShiftCorrection_eq_pow_mul_ratio
    (k : ℕ) {η : ℝ} (hη : η ≠ 0) (I : Finset (Fin n)) :
    putinarShiftCorrection k η I =
      η ^ I.card * putinarShiftCorrectionRatio (putinarPairMu k / η) I := by
  unfold putinarShiftCorrection putinarShiftCorrectionRatio
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJI : J ⊆ I := Finset.mem_powerset.mp hJ
  have hcard : J.card ≤ I.card := Finset.card_le_card hJI
  by_cases htwo : 2 ≤ J.card
  · simp only [htwo, if_pos]
    rw [pow_sub₀ η hη hcard, div_pow]
    simp only [div_eq_mul_inv]
    ring
  · simp only [htwo, if_false, mul_zero]

/-- Under the manuscript hypothesis `η ≥ 2nμ`, the leading scalar in
the shifted localized-factor expansion is nonnegative. -/
theorem putinarShiftLeadingConstant_nonneg
    (hn : 0 < n) (k : ℕ) (hk : 1 ≤ k) (η : ℝ)
    (hη : 2 * (n : ℝ) * putinarPairMu k ≤ η)
    (I : Finset (Fin n)) :
    0 ≤ η ^ I.card - putinarShiftCorrection k η I := by
  have hμ : 0 < putinarPairMu k := by
    unfold putinarPairMu delta
    positivity
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hηpos : 0 < η :=
    (mul_pos (mul_pos (by norm_num) hnreal) hμ).trans_le hη
  have ht : 0 ≤ putinarPairMu k / η := div_nonneg hμ.le hηpos.le
  have hnt : (n : ℝ) * (putinarPairMu k / η) ≤ 1 / 2 := by
    rw [show (n : ℝ) * (putinarPairMu k / η) =
      ((n : ℝ) * putinarPairMu k) / η by ring]
    rw [div_le_iff₀ hηpos]
    nlinarith
  have hratio := putinarShiftCorrectionRatio_le_half I ht hnt
  rw [putinarShiftCorrection_eq_pow_mul_ratio k hηpos.ne' I]
  have hpow : 0 ≤ η ^ I.card := pow_nonneg hηpos.le _
  apply sub_nonneg.mpr
  calc
    η ^ I.card *
        putinarShiftCorrectionRatio (putinarPairMu k / η) I ≤
        η ^ I.card * (1 / 2) :=
      mul_le_mul_of_nonneg_left hratio hpow
    _ ≤ η ^ I.card := by nlinarith

/-! ## The shifted localized-factor product -/

/-- The localized product `A_J`. This local name avoids importing the
larger preordering-conversion module. -/
def putinarShiftFactorSetProduct (k : ℕ) (J : Finset (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ J, putinarPairFactor k i

/-- The product of the localized factors after adding the common shift. -/
def putinarShiftedFactorProduct (k : ℕ) (η : ℝ)
    (I : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ I, (MvPolynomial.C η + putinarPairFactor k i)

/-- Ordinary subset expansion of the shifted localized-factor product. -/
theorem putinarShiftedFactorProduct_eq_sum
    (k : ℕ) (η : ℝ) (I : Finset (Fin n)) :
    putinarShiftedFactorProduct k η I =
      ∑ J ∈ I.powerset,
        MvPolynomial.C (η ^ (I.card - J.card)) *
          putinarShiftFactorSetProduct k J := by
  unfold putinarShiftedFactorProduct
  simp_rw [add_comm]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJI : J ⊆ I := Finset.mem_powerset.mp hJ
  have hcard : (I \ J).card = I.card - J.card :=
    Finset.card_sdiff_of_subset hJI
  unfold putinarShiftFactorSetProduct
  rw [Finset.prod_const, hcard, MvPolynomial.C_pow]
  ring


/-- The augmented term packages the localized certificate
`A_J + μ^|J|` when `|J| ≥ 2`; singleton sets retain `A_J` itself. -/
def putinarShiftAugmentedTerm (k : ℕ) (η : ℝ)
    (I J : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (η ^ (I.card - J.card)) *
    (putinarShiftFactorSetProduct k J +
      if 2 ≤ J.card then MvPolynomial.C (putinarPairMu k ^ J.card) else 0)

/-- Exact manuscript expansion: the shifted localized-factor product is the
nonnegative leading constant plus the augmented terms over nonempty subsets. -/
theorem putinarShiftedFactorProduct_eq_leading_add_sum
    (k : ℕ) (η : ℝ) (I : Finset (Fin n)) :
    putinarShiftedFactorProduct k η I =
      MvPolynomial.C (η ^ I.card - putinarShiftCorrection k η I) +
        ∑ J ∈ I.powerset.erase ∅, putinarShiftAugmentedTerm k η I J := by
  have hempty : (∅ : Finset (Fin n)) ∈ I.powerset := by simp
  have haugmented :
      (∑ J ∈ I.powerset, putinarShiftAugmentedTerm k η I J) =
        putinarShiftedFactorProduct k η I +
          MvPolynomial.C (putinarShiftCorrection k η I) := by
    rw [putinarShiftedFactorProduct_eq_sum]
    unfold putinarShiftAugmentedTerm putinarShiftCorrection
    rw [map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases htwo : 2 ≤ J.card
    · simp only [htwo, if_pos]
      rw [map_mul]
      ring
    · simp only [htwo, if_false, map_zero, add_zero]
  have hemptyTerm :
      putinarShiftAugmentedTerm k η I ∅ = MvPolynomial.C (η ^ I.card) := by
    simp [putinarShiftAugmentedTerm, putinarShiftFactorSetProduct]
  have hsplit := Finset.sum_eq_add_sum_diff_singleton hempty
    (f := putinarShiftAugmentedTerm k η I)
  rw [hemptyTerm] at hsplit
  have hsplitErase :
      (∑ J ∈ I.powerset, putinarShiftAugmentedTerm k η I J) =
        MvPolynomial.C (η ^ I.card) +
          ∑ J ∈ I.powerset.erase ∅, putinarShiftAugmentedTerm k η I J := by
    simpa only [Finset.sdiff_singleton_eq_erase] using hsplit
  calc
    putinarShiftedFactorProduct k η I =
        (putinarShiftedFactorProduct k η I +
            MvPolynomial.C (putinarShiftCorrection k η I)) -
          MvPolynomial.C (putinarShiftCorrection k η I) := by ring
    _ = (∑ J ∈ I.powerset, putinarShiftAugmentedTerm k η I J) -
          MvPolynomial.C (putinarShiftCorrection k η I) := by rw [haugmented]
    _ = (MvPolynomial.C (η ^ I.card) +
          ∑ J ∈ I.powerset.erase ∅, putinarShiftAugmentedTerm k η I J) -
          MvPolynomial.C (putinarShiftCorrection k η I) := by rw [hsplitErase]
    _ = MvPolynomial.C (η ^ I.card - putinarShiftCorrection k η I) +
          ∑ J ∈ I.powerset.erase ∅, putinarShiftAugmentedTerm k η I J := by
      rw [map_sub]
      ring

/-! ## Canonical certificates for the localized core -/

/-- A finite sum of certificates at a common canonical order. -/
theorem boxQuadraticModule_sum_finset {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hf : ∀ i ∈ s, f i ∈ BoxQuadraticModule n r) :
    ∑ i ∈ s, f i ∈ BoxQuadraticModule n r := by
  classical
  induction s using Finset.induction with
  | empty => simp [zero_mem_BoxQuadraticModule]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact BoxQuadraticModule_add
        (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

/-- Each localized factor `a_i` is already one explicit generator times a
square, at canonical order `2k`. -/
theorem putinarPairFactor_mem_BoxQuadraticModule
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    putinarPairFactor k i ∈ BoxQuadraticModule n (2 * k) := by
  have hdegree :
      (putinarPairQ k i ^ 2 * BoxSemialgebraicGenerator i).totalDegree ≤
        2 * k := by
    rw [mul_comm, ← putinarPairFactor_eq_generator_mul_q_sq k hk i]
    exact putinarPairFactor_totalDegree_le k hk i
  have hmem := sos_mul_boxSemialgebraicGenerator_mem_BoxQuadraticModule i
    (putinarPairQ k i ^ 2) (IsSOS_sq _) hdegree
  rw [putinarPairFactor_eq_generator_mul_q_sq k hk i]
  simpa only [mul_comm] using hmem


/-- Every nonempty augmented term has a certificate whose order is governed
by the ambient set `I`. -/
theorem putinarShiftAugmentedTerm_mem_BoxQuadraticModule
    (k : ℕ) (hk : 1 ≤ k) {η : ℝ} (hη : 0 ≤ η)
    (I J : Finset (Fin n)) (hJI : J ⊆ I) (hJne : J.Nonempty) :
    putinarShiftAugmentedTerm k η I J ∈
      BoxQuadraticModule n (4 * I.card * k) := by
  have hcard : J.card ≤ I.card := Finset.card_le_card hJI
  have hinner :
      putinarShiftFactorSetProduct k J +
          (if 2 ≤ J.card then MvPolynomial.C (putinarPairMu k ^ J.card) else 0) ∈
        BoxQuadraticModule n (4 * J.card * k) := by
    by_cases htwo : 2 ≤ J.card
    · simp only [htwo, if_pos]
      exact putinarLocalizedProduct_finset_mem_BoxQuadraticModule k hk J htwo
    · have hcardOne : J.card = 1 := by
        have hone : 1 ≤ J.card := Finset.one_le_card.mpr hJne
        omega
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcardOne
      have hmono := BoxQuadraticModule_mono
        (show 2 * k ≤ 4 * 1 * k by omega)
        (putinarPairFactor_mem_BoxQuadraticModule k hk i)
      simpa only [putinarShiftFactorSetProduct, Finset.prod_singleton,
        Finset.card_singleton, mul_one, Nat.not_ofNat_le_one, if_false,
        add_zero] using hmono
  have hinnerMono := BoxQuadraticModule_mono
    (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 4 hcard)) hinner
  unfold putinarShiftAugmentedTerm
  exact BoxQuadraticModule_nonneg_scale _ (pow_nonneg hη _) hinnerMono

/-- The core shifted product `∏(η+a_i)` belongs to the canonical quadratic
module at order `4|I|k`. -/
theorem putinarShiftedFactorProduct_mem_BoxQuadraticModule
    (hn : 0 < n) (k : ℕ) (hk : 1 ≤ k) (η : ℝ)
    (hη : 2 * (n : ℝ) * putinarPairMu k ≤ η)
    (I : Finset (Fin n)) :
    putinarShiftedFactorProduct k η I ∈
      BoxQuadraticModule n (4 * I.card * k) := by
  have hμ : 0 < putinarPairMu k := by
    unfold putinarPairMu delta
    positivity
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hηpos : 0 < η :=
    (mul_pos (mul_pos (by norm_num) hnreal) hμ).trans_le hη
  have hleading :
      MvPolynomial.C (η ^ I.card - putinarShiftCorrection k η I) ∈
        BoxQuadraticModule n (4 * I.card * k) :=
    nonneg_const_mem_BoxQuadraticModule
      (putinarShiftLeadingConstant_nonneg hn k hk η hη I) n _
  have hsum :
      (∑ J ∈ I.powerset.erase ∅, putinarShiftAugmentedTerm k η I J) ∈
        BoxQuadraticModule n (4 * I.card * k) := by
    apply boxQuadraticModule_sum_finset
    intro J hJ
    have hmem := Finset.mem_erase.mp hJ
    exact putinarShiftAugmentedTerm_mem_BoxQuadraticModule k hk hηpos.le I J
      (Finset.mem_powerset.mp hmem.2) (Finset.nonempty_iff_ne_empty.mpr hmem.1)
  have hadd := BoxQuadraticModule_add hleading hsum
  rw [← putinarShiftedFactorProduct_eq_leading_add_sum k η I] at hadd
  exact hadd

/-! ## Restoring the SOS residuals -/

/-- Product of the SOS residuals in the Chebyshev split. -/
def putinarShiftResidualProduct (k : ℕ) (L : Finset (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ L, putinarSplitS k i

/-- A finite product of the residuals is SOS. -/
theorem putinarShiftResidualProduct_isSOS
    (k : ℕ) (hk : 1 ≤ k) (L : Finset (Fin n)) :
    IsSOS (putinarShiftResidualProduct k L) := by
  unfold putinarShiftResidualProduct
  apply IsSOS_finset_prod
  intro i hi
  exact putinarSplitS_isSOS k hk i

/-- The residual product has the expected additive degree bound. -/
theorem putinarShiftResidualProduct_totalDegree_le
    (k : ℕ) (hk : 1 ≤ k) (L : Finset (Fin n)) :
    (putinarShiftResidualProduct k L).totalDegree ≤ 2 * k * L.card := by
  unfold putinarShiftResidualProduct
  calc
    (∏ i ∈ L, putinarSplitS k i).totalDegree ≤
        ∑ i ∈ L, (putinarSplitS k i).totalDegree :=
      MvPolynomial.totalDegree_finset_prod L _
    _ ≤ ∑ _i ∈ L, 2 * k := by
      apply Finset.sum_le_sum
      intro i hi
      exact putinarSplitS_totalDegree_le k hk i
    _ = 2 * k * L.card := by simp [Nat.mul_comm]

/-- Expanding the shifted cube generators using `g_i = a_i + s_i`. -/
theorem shiftedBoxGeneratorProduct_eq_sum_split
    (k : ℕ) (η : ℝ) (I : Finset (Fin n)) :
    (∏ i ∈ I, (BoxSemialgebraicGenerator i + MvPolynomial.C η)) =
      ∑ J ∈ I.powerset,
        putinarShiftedFactorProduct k η J *
          putinarShiftResidualProduct k (I \ J) := by
  have hsplit (i : Fin n) :
      BoxSemialgebraicGenerator i + MvPolynomial.C η =
        (MvPolynomial.C η + putinarPairFactor k i) + putinarSplitS k i := by
    rw [boxGenerator_eq_putinarSplitS_add_factor k i]
    ring
  simp_rw [hsplit]
  rw [Finset.prod_add]
  rfl

/-- The shifted product of any subset of cube generators has an explicit
canonical Putinar certificate.  Its order is linear in the dimension and in
the localization parameter. -/
theorem shiftedBoxGeneratorProduct_mem_BoxQuadraticModule
    (hn : 0 < n) (k : ℕ) (hk : 1 ≤ k) (η : ℝ)
    (hη : 2 * (n : ℝ) * putinarPairMu k ≤ η)
    (I : Finset (Fin n)) :
    (∏ i ∈ I, (BoxSemialgebraicGenerator i + MvPolynomial.C η)) ∈
      BoxQuadraticModule n (4 * n * k) := by
  have hAtCard :
      (∏ i ∈ I, (BoxSemialgebraicGenerator i + MvPolynomial.C η)) ∈
        BoxQuadraticModule n (4 * I.card * k) := by
    rw [shiftedBoxGeneratorProduct_eq_sum_split k η I]
    apply boxQuadraticModule_sum_finset
    intro J hJ
    have hJI : J ⊆ I := Finset.mem_powerset.mp hJ
    have hcore := putinarShiftedFactorProduct_mem_BoxQuadraticModule
      hn k hk η hη J
    have hresSOS := putinarShiftResidualProduct_isSOS k hk (I \ J)
    have hmul := BoxQuadraticModule_sos_mul hresSOS hcore
    have hresDegree := putinarShiftResidualProduct_totalDegree_le
      k hk (I \ J)
    have hcards : (I \ J).card + J.card = I.card :=
      Finset.card_sdiff_add_card_eq_card hJI
    have hcoeff : 4 * J.card + 2 * (I \ J).card ≤ 4 * I.card := by
      omega
    have hcoarse :
        4 * J.card * k + 2 * k * (I \ J).card ≤ 4 * I.card * k := by
      calc
        4 * J.card * k + 2 * k * (I \ J).card =
            (4 * J.card + 2 * (I \ J).card) * k := by ring
        _ ≤ (4 * I.card) * k := Nat.mul_le_mul_right k hcoeff
        _ = 4 * I.card * k := by ring
    have horder :
        4 * J.card * k + (putinarShiftResidualProduct k (I \ J)).totalDegree ≤
          4 * I.card * k :=
      (Nat.add_le_add_left hresDegree (4 * J.card * k)).trans hcoarse
    have hout := BoxQuadraticModule_mono horder hmul
    simpa only [mul_comm] using hout
  have hcard : I.card ≤ n := by simpa using Finset.card_le_univ I
  exact BoxQuadraticModule_mono
    (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 4 hcard)) hAtCard

/-! ## Transfer of a complete scaled preordering witness -/

/-- A scaled generator is a cube generator shifted by `b² - 1`. -/
theorem scaledBoxGenerator_eq_shifted (b : ℝ) (i : Fin n) :
    ScaledBoxGenerator b i =
      BoxSemialgebraicGenerator i + MvPolynomial.C (b ^ 2 - 1) := by
  unfold ScaledBoxGenerator BoxSemialgebraicGenerator
  simp only [map_sub, map_one]
  ring

/-- Scaled box generators are nonzero polynomials, for every real scale. -/
theorem scaledBoxGenerator_ne_zero (b : ℝ) (i : Fin n) :
    ScaledBoxGenerator b i ≠ (0 : MvPolynomial (Fin n) ℝ) := by
  intro hzero
  have hzeroEval := congrArg
    (MvPolynomial.eval (fun _ : Fin n ↦ (0 : ℝ))) hzero
  have honeEval := congrArg
    (MvPolynomial.eval (fun j : Fin n ↦ if j = i then (1 : ℝ) else 0)) hzero
  simp [ScaledBoxGenerator] at hzeroEval honeEval
  subst b
  norm_num at honeEval

/-- Consequently, every finite product of scaled generators is nonzero. -/
theorem scaledBoxGeneratorProd_ne_zero (b : ℝ) (J : Finset (Fin n)) :
    ScaledBoxGeneratorProd b J ≠ (0 : MvPolynomial (Fin n) ℝ) := by
  unfold ScaledBoxGeneratorProd
  exact Finset.prod_ne_zero_iff.mpr fun i hi ↦ scaledBoxGenerator_ne_zero b i

/-- The scaled generator product is exactly the shifted product certified
above. -/
theorem scaledBoxGeneratorProd_eq_shifted (b : ℝ) (J : Finset (Fin n)) :
    ScaledBoxGeneratorProd b J =
      ∏ i ∈ J,
        (BoxSemialgebraicGenerator i + MvPolynomial.C (b ^ 2 - 1)) := by
  unfold ScaledBoxGeneratorProd
  apply Finset.prod_congr rfl
  intro i hi
  exact scaledBoxGenerator_eq_shifted b i

/-- If the right factor is nonzero, the degree of the left factor is bounded
by any bound on the degree of the complete product. -/
theorem totalDegree_left_le_of_mul_right_ne_zero
    {p q : MvPolynomial (Fin n) ℝ} {R : ℕ} (hq : q ≠ 0)
    (hdegree : (p * q).totalDegree ≤ R) :
    p.totalDegree ≤ R := by
  by_cases hp : p = 0
  · simp [hp]
  · have hmul := MvPolynomial.totalDegree_mul_of_isDomain hp hq
    rw [hmul] at hdegree
    omega

/-- Witness-level shifted-product transfer.  A certificate in the
`b`-scaled box preordering becomes a certificate in the ordinary box
quadratic module, with exactly the additive order loss `4 n k`. -/
theorem scaledBoxPreordering_mem_BoxQuadraticModule
    (hn : 0 < n) (k : ℕ) (hk : 1 ≤ k) (b : ℝ)
    (hshift : 2 * (n : ℝ) * putinarPairMu k ≤ b ^ 2 - 1)
    {p : MvPolynomial (Fin n) ℝ} {R : ℕ}
    (hp : p ∈ ScaledBoxPreordering b n R) :
    p ∈ BoxQuadraticModule n (R + 4 * n * k) := by
  obtain ⟨σ, hσSOS, hdegree, hpEq⟩ := hp
  rw [hpEq]
  apply boxQuadraticModule_sum_finset
  intro J hJ
  have hprod : ScaledBoxGeneratorProd b J ∈
      BoxQuadraticModule n (4 * n * k) := by
    rw [scaledBoxGeneratorProd_eq_shifted b J]
    exact shiftedBoxGeneratorProduct_mem_BoxQuadraticModule
      hn k hk (b ^ 2 - 1) hshift J
  have hmul := BoxQuadraticModule_sos_mul (hσSOS J) hprod
  have hσdegree : (σ J).totalDegree ≤ R :=
    totalDegree_left_le_of_mul_right_ne_zero
      (scaledBoxGeneratorProd_ne_zero b J) (hdegree J)
  exact BoxQuadraticModule_mono (by omega) hmul

end QuarticConvergence
end OptimalConvergenceRates

end
