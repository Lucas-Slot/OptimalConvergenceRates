/-
  Conversion of a root-preserving box-preordering certificate to the box
  quadratic module, retaining the polynomial correction from the manuscript.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarSplit
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarLocalizedProducts
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ConeWitnesses

open MvPolynomial Finset Polynomial
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n R r : ℕ}

/-! ## Algebraic pieces of the conversion -/

/-- The residual product `S_L = ∏_{i∈L} s_i`. -/
def putinarSplitSetProduct (k : ℕ) (L : Finset (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ L, putinarSplitS k i

/-- The localized product `A_L = ∏_{i∈L} a_i`. -/
def putinarFactorSetProduct (k : ℕ) (L : Finset (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i ∈ L, putinarPairFactor k i

/-- The correction attached to one generator set `I`.  The conditional sum
is exactly the finite sum over `J ⊆ I` with `2 ≤ |J|`. -/
def putinarCorrectionInner (k : ℕ) (I : Finset (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ J ∈ I.powerset, if 2 ≤ J.card then
    MvPolynomial.C (putinarPairMu k ^ J.card) *
      putinarSplitSetProduct k (I \ J)
  else 0

/-- Correction weighted by an SOS multiplier `τ`. -/
def putinarCorrectionForMultiplier (k : ℕ) (I : Finset (Fin n))
    (τ : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  τ * putinarCorrectionInner k I

/-- The converted summand indexed by `J ⊆ I`. -/
def putinarConvertedSubsetTerm (k : ℕ) (I J : Finset (Fin n))
    (τ : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  τ * putinarSplitSetProduct k (I \ J) *
    (putinarFactorSetProduct k J +
      if 2 ≤ J.card then MvPolynomial.C (putinarPairMu k ^ J.card) else 0)

/-- Every residual product is SOS. -/
theorem putinarSplitSetProduct_isSOS
    (k : ℕ) (hk : 1 ≤ k) (L : Finset (Fin n)) :
    IsSOS (putinarSplitSetProduct k L) := by
  unfold putinarSplitSetProduct
  apply IsSOS_finset_prod
  intro i hi
  exact putinarSplitS_isSOS k hk i

/-- Degree of a residual product. -/
theorem putinarSplitSetProduct_totalDegree_le
    (k : ℕ) (hk : 1 ≤ k) (L : Finset (Fin n)) :
    (putinarSplitSetProduct k L).totalDegree ≤ 2 * k * L.card := by
  unfold putinarSplitSetProduct
  calc
    (∏ i ∈ L, putinarSplitS k i).totalDegree ≤
        ∑ i ∈ L, (putinarSplitS k i).totalDegree :=
      MvPolynomial.totalDegree_finset_prod L _
    _ ≤ ∑ _i ∈ L, 2 * k := by
      apply Finset.sum_le_sum
      intro i hi
      exact putinarSplitS_totalDegree_le k hk i
    _ = 2 * k * L.card := by simp [Nat.mul_comm]

/-- The inner correction is SOS. -/
theorem putinarCorrectionInner_isSOS
    (k : ℕ) (hk : 1 ≤ k) (I : Finset (Fin n)) :
    IsSOS (putinarCorrectionInner k I) := by
  unfold putinarCorrectionInner
  apply IsSOS_sum_finset
  intro J hJ
  by_cases hcard : 2 ≤ J.card
  · simp only [hcard, ↓reduceIte]
    apply IsSOS_nonneg_scale (putinarSplitSetProduct_isSOS k hk (I \ J))
    unfold putinarPairMu delta
    positivity
  · simp only [hcard, ↓reduceIte]
    exact IsSOS_zero

/-- A correction weighted by an SOS multiplier is SOS. -/
theorem putinarCorrectionForMultiplier_isSOS
    (k : ℕ) (hk : 1 ≤ k) (I : Finset (Fin n))
    {τ : MvPolynomial (Fin n) ℝ} (hτ : IsSOS τ) :
    IsSOS (putinarCorrectionForMultiplier k I τ) := by
  exact IsSOS_mul hτ (putinarCorrectionInner_isSOS k hk I)

/-- Degree of the inner correction, uniformly over all `I ⊆ Fin n`. -/
theorem putinarCorrectionInner_totalDegree_le
    (k : ℕ) (hk : 1 ≤ k) (I : Finset (Fin n)) :
    (putinarCorrectionInner k I).totalDegree ≤ 2 * n * k := by
  unfold putinarCorrectionInner
  apply MvPolynomial.totalDegree_finsetSum_le
  intro J hJ
  have hJI : J ⊆ I := Finset.mem_powerset.mp hJ
  have hdiff : (I \ J).card ≤ n := by
    simpa using Finset.card_le_univ (I \ J)
  by_cases hcard : 2 ≤ J.card
  · simp only [hcard, ↓reduceIte]
    calc
      (MvPolynomial.C (putinarPairMu k ^ J.card) *
          putinarSplitSetProduct k (I \ J)).totalDegree ≤
          (MvPolynomial.C (putinarPairMu k ^ J.card)).totalDegree +
            (putinarSplitSetProduct k (I \ J)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 2 * k * (I \ J).card := by
        exact Nat.add_le_add (by rw [MvPolynomial.totalDegree_C])
          (putinarSplitSetProduct_totalDegree_le k hk (I \ J))
      _ ≤ 2 * n * k := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          Nat.mul_le_mul_left (2 * k) hdiff
  · simp [hcard]

/-- Expanding `g_i = a_i + s_i` over a finite generator set. -/
theorem boxSemialgebraicGeneratorProd_eq_sum_factor_split
    (k : ℕ) (I : Finset (Fin n)) :
    BoxSemialgebraicGeneratorProd I =
      ∑ J ∈ I.powerset,
        putinarFactorSetProduct k J * putinarSplitSetProduct k (I \ J) := by
  unfold BoxSemialgebraicGeneratorProd
  simp_rw [boxGenerator_eq_putinarSplitS_add_factor k, add_comm]
  rw [Finset.prod_add]
  rfl

/-- Polynomial identity underlying the conversion: expansion plus the
retained correction is the sum of the converted subset terms. -/
theorem mul_generatorProd_add_correction_eq_sum_converted
    (k : ℕ) (I : Finset (Fin n)) (τ : MvPolynomial (Fin n) ℝ) :
    τ * BoxSemialgebraicGeneratorProd I +
        putinarCorrectionForMultiplier k I τ =
      ∑ J ∈ I.powerset, putinarConvertedSubsetTerm k I J τ := by
  rw [boxSemialgebraicGeneratorProd_eq_sum_factor_split k I]
  unfold putinarCorrectionForMultiplier putinarCorrectionInner
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  unfold putinarConvertedSubsetTerm
  by_cases hcard : 2 ≤ J.card
  · simp only [hcard, ↓reduceIte]
    ring
  · simp only [hcard, ↓reduceIte, add_zero]
    ring


/-- A single localized factor belongs to the canonical quadratic module at
total certificate degree `2k`. -/
theorem putinarPairFactor_mem_BoxQuadraticModule
    (k : ℕ) (hk : 1 ≤ k) (i : Fin n) :
    putinarPairFactor k i ∈ BoxQuadraticModule n (2 * k) := by
  have hdegree := putinarPairFactor_totalDegree_le k hk i
  rw [putinarPairFactor_eq_generator_mul_q_sq k hk i] at hdegree
  have hcert := sos_mul_boxSemialgebraicGenerator_mem_BoxQuadraticModule
    i (putinarPairQ k i ^ 2) (IsSOS_sq _) (by simpa [mul_comm] using hdegree)
  simpa [putinarPairFactor_eq_generator_mul_q_sq k hk i, mul_comm] using hcert

/-- A finite sum of same-order quadratic-module certificates. -/
theorem BoxQuadraticModule_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℝ) {d : ℕ}
    (hf : ∀ i ∈ s, f i ∈ BoxQuadraticModule n d) :
    ∑ i ∈ s, f i ∈ BoxQuadraticModule n d := by
  classical
  induction s using Finset.induction with
  | empty => simpa using zero_mem_BoxQuadraticModule n d
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact BoxQuadraticModule_add (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

/-- One converted subset term has the uniform canonical total-degree order
`2R + 4nk` when `τ` is SOS of degree at most `2R`. -/
theorem putinarConvertedSubsetTerm_mem_BoxQuadraticModule
    (k : ℕ) (hk : 1 ≤ k) (I J : Finset (Fin n)) (hJI : J ⊆ I)
    (τ : MvPolynomial (Fin n) ℝ) (hτ : IsSOS τ) (hτdegree : τ.totalDegree ≤ 2 * R) :
    putinarConvertedSubsetTerm k I J τ ∈
      BoxQuadraticModule n (2 * R + 4 * n * k) := by
  let p := τ * putinarSplitSetProduct k (I \ J)
  have hpSOS : IsSOS p :=
    IsSOS_mul hτ (putinarSplitSetProduct_isSOS k hk (I \ J))
  have hpdegree : p.totalDegree ≤ 2 * R + 2 * k * (I \ J).card := by
    dsimp [p]
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add hτdegree
        (putinarSplitSetProduct_totalDegree_le k hk (I \ J)))
  have hcards : (I \ J).card + J.card = I.card :=
    Finset.card_sdiff_add_card_eq_card hJI
  have hIcard : I.card ≤ n := by simpa using Finset.card_le_univ I
  have hdouble : 2 * k * (I \ J).card ≤ 4 * k * (I \ J).card := by
    exact Nat.mul_le_mul_right (I \ J).card
      (Nat.mul_le_mul_right k (by omega))
  have horder :
      4 * J.card * k + (2 * R + 2 * k * (I \ J).card) ≤
        2 * R + 4 * n * k := by
    calc
      4 * J.card * k + (2 * R + 2 * k * (I \ J).card) =
          2 * R + 4 * k * J.card + 2 * k * (I \ J).card := by ring
      _ ≤ 2 * R + 4 * k * J.card + 4 * k * (I \ J).card :=
        Nat.add_le_add_left hdouble (2 * R + 4 * k * J.card)
      _ = 2 * R + 4 * k * ((I \ J).card + J.card) := by ring
      _ = 2 * R + 4 * k * I.card := by rw [hcards]
      _ ≤ 2 * R + 4 * k * n :=
        Nat.add_le_add_left (Nat.mul_le_mul_left (4 * k) hIcard) (2 * R)
      _ = 2 * R + 4 * n * k := by ring
  by_cases hlarge : 2 ≤ J.card
  · have hloc := putinarLocalizedProduct_finset_mem_BoxQuadraticModule
      k hk J hlarge
    have hmul := BoxQuadraticModule_sos_mul hpSOS hloc
    have hmono : 4 * J.card * k + p.totalDegree ≤ 2 * R + 4 * n * k :=
      (Nat.add_le_add_left hpdegree (4 * J.card * k)).trans horder
    have hout := BoxQuadraticModule_mono hmono hmul
    simpa [putinarConvertedSubsetTerm, p, hlarge] using hout
  · have hcard : J.card ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hzero | hone
    · have hJ : J = ∅ := Finset.card_eq_zero.mp hzero
      have hpdegreeTarget : p.totalDegree ≤ 2 * R + 4 * n * k := by
        apply hpdegree.trans
        calc
          2 * R + 2 * k * (I \ J).card ≤
              4 * J.card * k + (2 * R + 2 * k * (I \ J).card) := by omega
          _ ≤ 2 * R + 4 * n * k := horder
      have hfree := isSOS_mem_BoxQuadraticModule hpSOS hpdegreeTarget
      simpa [putinarConvertedSubsetTerm, putinarFactorSetProduct, p, hlarge, hJ] using hfree
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
      have hfactor := putinarPairFactor_mem_BoxQuadraticModule k hk i
      have hmul := BoxQuadraticModule_sos_mul hpSOS hfactor
      have hmono : 2 * k + p.totalDegree ≤ 2 * R + 4 * n * k := by
        calc
          2 * k + p.totalDegree ≤
              2 * k + (2 * R + 2 * k * (I \ {i}).card) :=
            Nat.add_le_add_left hpdegree (2 * k)
          _ ≤ 4 * ({i} : Finset (Fin n)).card * k +
              (2 * R + 2 * k * (I \ {i}).card) := by simp; omega
          _ ≤ 2 * R + 4 * n * k := horder
      have hout := BoxQuadraticModule_mono hmono hmul
      simpa [putinarConvertedSubsetTerm, putinarFactorSetProduct, p, hlarge] using hout


/-! ## One preordering summand -/

/-- Conversion of one preordering summand, retaining its explicit correction. -/
theorem mul_generatorProd_add_correction_mem_BoxQuadraticModule
    (k : ℕ) (hk : 1 ≤ k) (I : Finset (Fin n))
    (τ : MvPolynomial (Fin n) ℝ) (hτ : IsSOS τ)
    (hτdegree : τ.totalDegree ≤ 2 * R) :
    τ * BoxSemialgebraicGeneratorProd I +
        putinarCorrectionForMultiplier k I τ ∈
      BoxQuadraticModule n (2 * R + 4 * n * k) := by
  rw [mul_generatorProd_add_correction_eq_sum_converted]
  apply BoxQuadraticModule_finset_sum
  intro J hJ
  exact putinarConvertedSubsetTerm_mem_BoxQuadraticModule k hk I J
    (Finset.mem_powerset.mp hJ) τ hτ hτdegree

/-! ## Root-preserving conversion -/

/-- The SOS multiplier represented by the roots over one generator set. -/
def boxPreorderingRootMultiplier
    {q : MvPolynomial (Fin n) ℝ}
    (w : BoxPreorderingRootWitness q r) (I : Finset (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ j, (w.root I j) ^ 2

/-- The root multiplier is SOS by construction. -/
theorem boxPreorderingRootMultiplier_isSOS
    {q : MvPolynomial (Fin n) ℝ}
    (w : BoxPreorderingRootWitness q r) (I : Finset (Fin n)) :
    IsSOS (boxPreorderingRootMultiplier w I) := by
  exact ⟨w.N I, w.root I, rfl⟩

/-- A uniform bound on root degree gives twice that bound for the multiplier. -/
theorem boxPreorderingRootMultiplier_totalDegree_le
    {q : MvPolynomial (Fin n) ℝ}
    (w : BoxPreorderingRootWitness q r)
    (hroot : ∀ I j, (w.root I j).totalDegree ≤ R)
    (I : Finset (Fin n)) :
    (boxPreorderingRootMultiplier w I).totalDegree ≤ 2 * R := by
  unfold boxPreorderingRootMultiplier
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (MvPolynomial.totalDegree_pow (w.root I j) 2).trans
    (Nat.mul_le_mul_left 2 (hroot I j))

/-- The manuscript correction
E_k = sum_I tau_I sum_(J subset I, 2 <= |J|) mu_k^|J| S_(I minus J). -/
def putinarConversionCorrection
    {q : MvPolynomial (Fin n) ℝ}
    (k : ℕ) (w : BoxPreorderingRootWitness q r) :
    MvPolynomial (Fin n) ℝ :=
  ∑ I ∈ Finset.univ.powerset,
    putinarCorrectionForMultiplier k I
      (boxPreorderingRootMultiplier w I)

/-- The retained correction is SOS. -/
theorem putinarConversionCorrection_isSOS
    {q : MvPolynomial (Fin n) ℝ}
    (k : ℕ) (hk : 1 ≤ k) (w : BoxPreorderingRootWitness q r) :
    IsSOS (putinarConversionCorrection k w) := by
  unfold putinarConversionCorrection
  apply IsSOS_sum_finset
  intro I hI
  exact putinarCorrectionForMultiplier_isSOS k hk I
    (boxPreorderingRootMultiplier_isSOS w I)

/-- The retained correction has total degree at most 2R + 2nk. -/
theorem putinarConversionCorrection_totalDegree_le
    {q : MvPolynomial (Fin n) ℝ}
    (k : ℕ) (hk : 1 ≤ k) (w : BoxPreorderingRootWitness q r)
    (hroot : ∀ I j, (w.root I j).totalDegree ≤ R) :
    (putinarConversionCorrection k w).totalDegree ≤
      2 * R + 2 * n * k := by
  unfold putinarConversionCorrection
  apply MvPolynomial.totalDegree_finsetSum_le
  intro I hI
  unfold putinarCorrectionForMultiplier
  calc
    (boxPreorderingRootMultiplier w I *
        putinarCorrectionInner k I).totalDegree ≤
        (boxPreorderingRootMultiplier w I).totalDegree +
          (putinarCorrectionInner k I).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 2 * R + 2 * n * k :=
      Nat.add_le_add
        (boxPreorderingRootMultiplier_totalDegree_le w hroot I)
        (putinarCorrectionInner_totalDegree_le k hk I)

/-- Root-preserving preordering conversion with the polynomial correction
retained. If every stored root has degree at most R, then q + E_k
belongs to the canonical box quadratic module at repository total-degree
order 2R + 4nk. -/
theorem BoxPreorderingRootWitness.add_putinarConversionCorrection_mem
    {q : MvPolynomial (Fin n) ℝ}
    (w : BoxPreorderingRootWitness q r)
    (hroot : ∀ I j, (w.root I j).totalDegree ≤ R)
    (k : ℕ) (hk : 1 ≤ k) :
    q + putinarConversionCorrection k w ∈
      BoxQuadraticModule n (2 * R + 4 * n * k) := by
  simp only [w.decomp]
  unfold putinarConversionCorrection
  rw [← Finset.sum_add_distrib]
  apply BoxQuadraticModule_finset_sum
  intro I hI
  exact mul_generatorProd_add_correction_mem_BoxQuadraticModule k hk I
    (boxPreorderingRootMultiplier w I)
    (boxPreorderingRootMultiplier_isSOS w I)
    (boxPreorderingRootMultiplier_totalDegree_le w hroot I)

/-- Existential form of the conversion proposition. The witness is the
explicit correction above, not an abstract nonnegative-univariate SOS. -/
theorem BoxPreorderingRootWitness.exists_sos_correction_putinar
    {q : MvPolynomial (Fin n) ℝ}
    (w : BoxPreorderingRootWitness q r)
    (hroot : ∀ I j, (w.root I j).totalDegree ≤ R)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ E : MvPolynomial (Fin n) ℝ,
      IsSOS E ∧
      E.totalDegree ≤ 2 * R + 2 * n * k ∧
      q + E ∈ BoxQuadraticModule n (2 * R + 4 * n * k) := by
  refine ⟨putinarConversionCorrection k w,
    putinarConversionCorrection_isSOS k hk w,
    putinarConversionCorrection_totalDegree_le k hk w hroot, ?_⟩
  exact w.add_putinarConversionCorrection_mem hroot k hk

end QuarticConvergence
end OptimalConvergenceRates

end
