/- Homogeneous jets for ternary Motzkin certificates. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.CoefficientNorms
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

open MvPolynomial Finset
open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

/-- Squared Euclidean norm on ternary vectors. -/
def motzkinSqNorm (x : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, x i ^ 2

theorem motzkinSqNorm_nonneg (x : Fin 3 → ℝ) : 0 ≤ motzkinSqNorm x := by
  exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg (x i))
theorem sq_coord_le_motzkinSqNorm (x : Fin 3 → ℝ) (i : Fin 3) :
    x i ^ 2 ≤ motzkinSqNorm x := by
  unfold motzkinSqNorm
  exact Finset.single_le_sum (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)

/-- The Motzkin sextic is bounded above by three times the cube of the
squared Euclidean norm. -/
theorem motzkinSextic_eval_le_three_sqNorm_cube (x : Fin 3 → ℝ) :
    eval x motzkinSextic ≤ 3 * motzkinSqNorm x ^ 3 := by
  have hx : x 0 ^ 2 ≤ motzkinSqNorm x := sq_coord_le_motzkinSqNorm x 0
  have hy : x 1 ^ 2 ≤ motzkinSqNorm x := sq_coord_le_motzkinSqNorm x 1
  have hz : x 2 ^ 2 ≤ motzkinSqNorm x := sq_coord_le_motzkinSqNorm x 2
  have hxy : x 0 ^ 4 * x 1 ^ 2 ≤ motzkinSqNorm x ^ 3 := by
    calc
      x 0 ^ 4 * x 1 ^ 2 = (x 0 ^ 2) ^ 2 * x 1 ^ 2 := by ring
      _ ≤ motzkinSqNorm x ^ 2 * motzkinSqNorm x := by
        gcongr
      _ = motzkinSqNorm x ^ 3 := by ring
  have hyx : x 0 ^ 2 * x 1 ^ 4 ≤ motzkinSqNorm x ^ 3 := by
    calc
      x 0 ^ 2 * x 1 ^ 4 = x 0 ^ 2 * (x 1 ^ 2) ^ 2 := by ring
      _ ≤ motzkinSqNorm x * motzkinSqNorm x ^ 2 := by
        gcongr
        exact motzkinSqNorm_nonneg x
      _ = motzkinSqNorm x ^ 3 := by ring
  have hz6 : x 2 ^ 6 ≤ motzkinSqNorm x ^ 3 := by
    calc
      x 2 ^ 6 = (x 2 ^ 2) ^ 3 := by ring
      _ ≤ motzkinSqNorm x ^ 3 := pow_le_pow_left₀ (sq_nonneg (x 2)) hz 3
  rw [motzkinSextic_eval]
  have hcross : 0 ≤ 3 * x 0 ^ 2 * x 1 ^ 2 * x 2 ^ 2 := by positivity
  nlinarith




/-- Degree-`m` homogeneous part of a four-variable polynomial.

This keeps exactly the monomials whose exponent sum is `m`. -/
def homogeneousPart3 (m : ℕ) (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ α ∈ p.support.filter (fun α => (α.sum fun _ e => e) = m),
    MvPolynomial.monomial α (MvPolynomial.coeff α p)

/-- Degree-`m` homogeneous part of each component of a polynomial vector. -/
def homogeneousPartVec3 {N : ℕ} (m : ℕ)
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) : Fin N → MvPolynomial (Fin 3) ℝ :=
  fun i => homogeneousPart3 m (Q i)

/-- The squared norm polynomial `sum_i Q_i^2`. -/
def sosVectorSq3 {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  ∑ i : Fin N, (Q i) ^ 2

theorem sosVectorSq3_isSOS {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    IsSOS (sosVectorSq3 Q) := by
  exact ⟨N, Q, rfl⟩

theorem motzkinCoeffNorm_sosVectorSq3_le_sq {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (sosVectorSq3 Q) ≤ motzkinVecCoeffNorm Q ^ 2 := by
  unfold sosVectorSq3
  calc
    motzkinCoeffNorm (∑ i : Fin N, (Q i) ^ 2)
        ≤ ∑ i : Fin N, motzkinCoeffNorm ((Q i) ^ 2) := by
          simpa using motzkinCoeffNorm_sum_le (Finset.univ : Finset (Fin N)) fun i => (Q i) ^ 2
    _ ≤ ∑ i : Fin N, motzkinCoeffNorm (Q i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa [pow_two] using motzkinCoeffNorm_mul_le (Q i) (Q i)
    _ = motzkinVecCoeffNorm Q ^ 2 := by
      unfold motzkinVecCoeffNorm
      rw [Real.sq_sqrt]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The main degree-four Taylor term `||Q_2||^2` is an SOS quartic candidate. -/
theorem degree_four_main_sos_term_isSOS {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    IsSOS (sosVectorSq3 (homogeneousPartVec3 2 Q)) := by
  exact sosVectorSq3_isSOS (homogeneousPartVec3 2 Q)

/-- The local homogeneous-part definition agrees with mathlib's homogeneous component. -/
lemma homogeneousPart3_eq_homogeneousComponent (m : ℕ) (p : MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 m p = MvPolynomial.homogeneousComponent m p := by
  simp [homogeneousPart3, MvPolynomial.homogeneousComponent_apply, Finsupp.degree_apply,
    Finsupp.sum]

lemma motzkinCoeffNorm_homogeneousPart3_zero (p : MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (homogeneousPart3 0 p) = |MvPolynomial.eval 0 p| := by
  rw [MvPolynomial.eval_zero]
  rw [congrFun MvPolynomial.constantCoeff_eq p]
  rw [homogeneousPart3_eq_homogeneousComponent, MvPolynomial.homogeneousComponent_zero]
  by_cases h : MvPolynomial.coeff 0 p = 0
  · simp [motzkinCoeffNorm, h]
  · unfold motzkinCoeffNorm
    rw [MvPolynomial.support_C]
    rw [if_neg h]
    simp [MvPolynomial.coeff_C]

lemma coeff_homogeneousPart3 (m : ℕ) (p : MvPolynomial (Fin 3) ℝ) (α : Fin 3 →₀ ℕ) :
    MvPolynomial.coeff α (homogeneousPart3 m p) =
      if α.sum (fun _ e => e) = m then MvPolynomial.coeff α p else 0 := by
  unfold homogeneousPart3
  rw [MvPolynomial.coeff_sum]
  by_cases hα : α ∈ p.support.filter (fun α => α.sum (fun _ e => e) = m)
  · have hdeg : α.sum (fun _ e => e) = m := (Finset.mem_filter.mp hα).2
    rw [Finset.sum_eq_single α]
    · simp [MvPolynomial.coeff_monomial, hdeg]
    · intro β hβ hβα
      rw [MvPolynomial.coeff_monomial]
      simp [hβα]
    · intro hnot
      exact (hnot hα).elim
  · have hif : ¬ α.sum (fun _ e => e) = m ∨ MvPolynomial.coeff α p = 0 := by
      by_cases hdeg : α.sum (fun _ e => e) = m
      · right
        by_contra hcoeff
        exact hα (by simp [hdeg, MvPolynomial.mem_support_iff.mpr hcoeff])
      · exact Or.inl hdeg
    rw [Finset.sum_eq_zero]
    · rcases hif with hdeg | hcoeff
      · simp [hdeg]
      · simp [hcoeff]
    · intro β hβ
      rw [MvPolynomial.coeff_monomial]
      by_cases hβα : β = α
      · subst β
        exact (hα hβ).elim
      · simp [hβα]

theorem motzkinCoeffNorm_homogeneousPart3_le (m : ℕ) (p : MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (homogeneousPart3 m p) ≤ motzkinCoeffNorm p := by
  classical
  unfold motzkinCoeffNorm
  have hsupp : (homogeneousPart3 m p).support ⊆ p.support := by
    intro α hα
    rw [MvPolynomial.mem_support_iff] at hα ⊢
    rw [coeff_homogeneousPart3] at hα
    by_cases hdeg : α.sum (fun _ e => e) = m
    · simpa [hdeg] using hα
    · simp [hdeg] at hα
  calc
    ∑ α ∈ (homogeneousPart3 m p).support, |MvPolynomial.coeff α (homogeneousPart3 m p)|
        ≤ ∑ α ∈ p.support, |MvPolynomial.coeff α (homogeneousPart3 m p)| := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ α ∈ p.support, |MvPolynomial.coeff α p| := by
      apply Finset.sum_le_sum
      intro α _hα
      rw [coeff_homogeneousPart3]
      by_cases hdeg : α.sum (fun _ e => e) = m
      · simp [hdeg]
      · simp [hdeg]

lemma homogeneousPart3_idem (m : ℕ) (p : MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 m (homogeneousPart3 m p) = homogeneousPart3 m p := by
  ext α
  rw [coeff_homogeneousPart3]
  by_cases h : α.sum (fun _ e => e) = m
  · rw [if_pos h, coeff_homogeneousPart3, if_pos h]
  · rw [if_neg h, coeff_homogeneousPart3, if_neg h]

lemma homogeneousPart3_add (m : ℕ) (p q : MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 m (p + q) = homogeneousPart3 m p + homogeneousPart3 m q := by
  ext α
  simp [coeff_homogeneousPart3, MvPolynomial.coeff_add]
  split_ifs <;> ring

lemma homogeneousPart3_sum {ι : Type*} (m : ℕ) (s : Finset ι)
    (f : ι → MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 m (∑ i ∈ s, f i) = ∑ i ∈ s, homogeneousPart3 m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext α
      simp [coeff_homogeneousPart3]
  | insert a s has ih =>
      simp [has, homogeneousPart3_add, ih]

/-! ## Fixed-degree product rules -/
lemma homogeneousPart3_zero_mul (p q : MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 0 (p * q) = homogeneousPart3 0 p * homogeneousPart3 0 q := by
  ext α
  rw [coeff_homogeneousPart3]
  by_cases hα : α.sum (fun _ e => e) = 0
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro x hx
    have hsum : x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = 0 := by
      have hadd :
          x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) =
            α.sum (fun _ e => e) := by
        rw [Finset.mem_antidiagonal] at hx
        rw [← hx]
        simp [Finsupp.sum_add_index]
      simpa [hα] using hadd
    have h1 : x.1.sum (fun _ e => e) = 0 := by omega
    have h2 : x.2.sum (fun _ e => e) = 0 := by omega
    simp [h1, h2]
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_mul]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    have hsum :
        x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = α.sum (fun _ e => e) := by
      rw [Finset.mem_antidiagonal] at hx
      rw [← hx]
      simp [Finsupp.sum_add_index]
    by_cases h1 : x.1.sum (fun _ e => e) = 0
    · have h2 : x.2.sum (fun _ e => e) ≠ 0 := by omega
      simp [h2]
    · simp [h1]

lemma homogeneousPart3_sosVectorSq3_zero {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 0 (sosVectorSq3 Q) = sosVectorSq3 (homogeneousPartVec3 0 Q) := by
  unfold sosVectorSq3 homogeneousPartVec3
  rw [homogeneousPart3_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simpa [pow_two] using homogeneousPart3_zero_mul (Q i) (Q i)

lemma homogeneousPart3_one_mul (p q : MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 1 (p * q) =
      homogeneousPart3 0 p * homogeneousPart3 1 q +
      homogeneousPart3 1 p * homogeneousPart3 0 q := by
  ext α
  rw [coeff_homogeneousPart3]
  by_cases hα : α.sum (fun _ e => e) = 1
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    symm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hsum : x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = 1 := by
      have hadd :
          x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) =
            α.sum (fun _ e => e) := by
        rw [Finset.mem_antidiagonal] at hx
        rw [← hx]
        simp [Finsupp.sum_add_index]
      simpa [hα] using hadd
    have hle : x.1.sum (fun _ e => e) ≤ 1 := by omega
    interval_cases h1 : x.1.sum (fun _ e => e)
    · have h2 : x.2.sum (fun _ e => e) = 1 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 0 := by omega
      simp [h2]
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    rw [← Finset.sum_add_distrib]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    have hsum :
        x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = α.sum (fun _ e => e) := by
      rw [Finset.mem_antidiagonal] at hx
      rw [← hx]
      simp [Finsupp.sum_add_index]
    by_cases h01 : x.2.sum (fun _ e => e) = 1
    · have h10 : x.1.sum (fun _ e => e) ≠ 0 := by omega
      simp [h01, h10]
    · by_cases h10 : x.2.sum (fun _ e => e) = 0
      · have h11 : x.1.sum (fun _ e => e) ≠ 1 := by omega
        simp [h10, h11]
      · simp [h01, h10]

lemma homogeneousPart3_sosVectorSq3_one {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 1 (sosVectorSq3 Q) =
      ∑ i : Fin N,
        (homogeneousPart3 0 (Q i) * homogeneousPart3 1 (Q i) +
          homogeneousPart3 1 (Q i) * homogeneousPart3 0 (Q i)) := by
  unfold sosVectorSq3
  rw [homogeneousPart3_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simpa [pow_two] using homogeneousPart3_one_mul (Q i) (Q i)

lemma homogeneousPart3_two_mul (p q : MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 2 (p * q) =
      homogeneousPart3 0 p * homogeneousPart3 2 q +
      homogeneousPart3 1 p * homogeneousPart3 1 q +
      homogeneousPart3 2 p * homogeneousPart3 0 q := by
  ext α
  rw [coeff_homogeneousPart3]
  by_cases hα : α.sum (fun _ e => e) = 2
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    symm
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hsum : x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = 2 := by
      have hadd :
          x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) =
            α.sum (fun _ e => e) := by
        rw [Finset.mem_antidiagonal] at hx
        rw [← hx]
        simp [Finsupp.sum_add_index]
      simpa [hα] using hadd
    have hle : x.1.sum (fun _ e => e) ≤ 2 := by omega
    interval_cases h1 : x.1.sum (fun _ e => e)
    · have h2 : x.2.sum (fun _ e => e) = 2 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 1 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 0 := by omega
      simp [h2]
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    have hsum :
        x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = α.sum (fun _ e => e) := by
      rw [Finset.mem_antidiagonal] at hx
      rw [← hx]
      simp [Finsupp.sum_add_index]
    by_cases h02 : x.2.sum (fun _ e => e) = 2
    · have h10 : x.1.sum (fun _ e => e) ≠ 0 := by omega
      simp [h02, h10]
    · by_cases h11 : x.2.sum (fun _ e => e) = 1
      · have h11' : x.1.sum (fun _ e => e) ≠ 1 := by omega
        simp [h11, h11']
      · by_cases h20 : x.2.sum (fun _ e => e) = 0
        · have h12 : x.1.sum (fun _ e => e) ≠ 2 := by omega
          simp [h20, h12]
        · simp [h02, h11, h20]

lemma homogeneousPart3_sosVectorSq3_two {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 2 (sosVectorSq3 Q) =
      ∑ i : Fin N,
        (homogeneousPart3 0 (Q i) * homogeneousPart3 2 (Q i) +
          homogeneousPart3 1 (Q i) * homogeneousPart3 1 (Q i) +
          homogeneousPart3 2 (Q i) * homogeneousPart3 0 (Q i)) := by
  unfold sosVectorSq3
  rw [homogeneousPart3_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simpa [pow_two] using homogeneousPart3_two_mul (Q i) (Q i)

lemma homogeneousPart3_three_mul (p q : MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 3 (p * q) =
      homogeneousPart3 0 p * homogeneousPart3 3 q +
      homogeneousPart3 1 p * homogeneousPart3 2 q +
      homogeneousPart3 2 p * homogeneousPart3 1 q +
      homogeneousPart3 3 p * homogeneousPart3 0 q := by
  ext α
  rw [coeff_homogeneousPart3]
  by_cases hα : α.sum (fun _ e => e) = 3
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    symm
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hsum : x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = 3 := by
      have hadd :
          x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) =
            α.sum (fun _ e => e) := by
        rw [Finset.mem_antidiagonal] at hx
        rw [← hx]
        simp [Finsupp.sum_add_index]
      simpa [hα] using hadd
    have hle : x.1.sum (fun _ e => e) ≤ 3 := by omega
    interval_cases h1 : x.1.sum (fun _ e => e)
    · have h2 : x.2.sum (fun _ e => e) = 3 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 2 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 1 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 0 := by omega
      simp [h2]
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    have hsum :
        x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = α.sum (fun _ e => e) := by
      rw [Finset.mem_antidiagonal] at hx
      rw [← hx]
      simp [Finsupp.sum_add_index]
    by_cases h03 : x.2.sum (fun _ e => e) = 3
    · have h10 : x.1.sum (fun _ e => e) ≠ 0 := by omega
      simp [h03, h10]
    · by_cases h12 : x.2.sum (fun _ e => e) = 2
      · have h11 : x.1.sum (fun _ e => e) ≠ 1 := by omega
        simp [h12, h11]
      · by_cases h21 : x.2.sum (fun _ e => e) = 1
        · have h12' : x.1.sum (fun _ e => e) ≠ 2 := by omega
          simp [h21, h12']
        · by_cases h30 : x.2.sum (fun _ e => e) = 0
          · have h13 : x.1.sum (fun _ e => e) ≠ 3 := by omega
            simp [h30, h13]
          · simp [h03, h12, h21, h30]

lemma homogeneousPart3_sosVectorSq3_three {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 3 (sosVectorSq3 Q) =
      ∑ i : Fin N,
        (homogeneousPart3 0 (Q i) * homogeneousPart3 3 (Q i) +
          homogeneousPart3 1 (Q i) * homogeneousPart3 2 (Q i) +
          homogeneousPart3 2 (Q i) * homogeneousPart3 1 (Q i) +
          homogeneousPart3 3 (Q i) * homogeneousPart3 0 (Q i)) := by
  unfold sosVectorSq3
  rw [homogeneousPart3_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simpa [pow_two] using homogeneousPart3_three_mul (Q i) (Q i)

lemma homogeneousPart3_four_mul (p q : MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 4 (p * q) =
      homogeneousPart3 0 p * homogeneousPart3 4 q +
      homogeneousPart3 1 p * homogeneousPart3 3 q +
      homogeneousPart3 2 p * homogeneousPart3 2 q +
      homogeneousPart3 3 p * homogeneousPart3 1 q +
      homogeneousPart3 4 p * homogeneousPart3 0 q := by
  ext α
  rw [coeff_homogeneousPart3]
  by_cases hα : α.sum (fun _ e => e) = 4
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    symm
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hsum : x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = 4 := by
      have hadd :
          x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) =
            α.sum (fun _ e => e) := by
        rw [Finset.mem_antidiagonal] at hx
        rw [← hx]
        simp [Finsupp.sum_add_index]
      simpa [hα] using hadd
    have hle : x.1.sum (fun _ e => e) ≤ 4 := by omega
    interval_cases h1 : x.1.sum (fun _ e => e)
    · have h2 : x.2.sum (fun _ e => e) = 4 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 3 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 2 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 1 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 0 := by omega
      simp [h2]
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    have hsum :
        x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = α.sum (fun _ e => e) := by
      rw [Finset.mem_antidiagonal] at hx
      rw [← hx]
      simp [Finsupp.sum_add_index]
    by_cases h04 : x.2.sum (fun _ e => e) = 4
    · have h10 : x.1.sum (fun _ e => e) ≠ 0 := by omega
      simp [h04, h10]
    · by_cases h13 : x.2.sum (fun _ e => e) = 3
      · have h11 : x.1.sum (fun _ e => e) ≠ 1 := by omega
        simp [h13, h11]
      · by_cases h22 : x.2.sum (fun _ e => e) = 2
        · have h12 : x.1.sum (fun _ e => e) ≠ 2 := by omega
          simp [h22, h12]
        · by_cases h31 : x.2.sum (fun _ e => e) = 1
          · have h13' : x.1.sum (fun _ e => e) ≠ 3 := by omega
            simp [h31, h13']
          · by_cases h40 : x.2.sum (fun _ e => e) = 0
            · have h14 : x.1.sum (fun _ e => e) ≠ 4 := by omega
              simp [h40, h14]
            · simp [h04, h13, h22, h31, h40]

lemma homogeneousPart3_sosVectorSq3_four {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 4 (sosVectorSq3 Q) =
      ∑ i : Fin N,
        (homogeneousPart3 0 (Q i) * homogeneousPart3 4 (Q i) +
          homogeneousPart3 1 (Q i) * homogeneousPart3 3 (Q i) +
          homogeneousPart3 2 (Q i) * homogeneousPart3 2 (Q i) +
          homogeneousPart3 3 (Q i) * homogeneousPart3 1 (Q i) +
          homogeneousPart3 4 (Q i) * homogeneousPart3 0 (Q i)) := by
  unfold sosVectorSq3
  rw [homogeneousPart3_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simpa [pow_two] using homogeneousPart3_four_mul (Q i) (Q i)

lemma homogeneousPart3_sosVectorSq3_four_error {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 4 (sosVectorSq3 Q) =
      sosVectorSq3 (homogeneousPartVec3 2 Q) +
        ∑ i : Fin N,
          (homogeneousPart3 0 (Q i) * homogeneousPart3 4 (Q i) +
            homogeneousPart3 1 (Q i) * homogeneousPart3 3 (Q i) +
            homogeneousPart3 3 (Q i) * homogeneousPart3 1 (Q i) +
            homogeneousPart3 4 (Q i) * homogeneousPart3 0 (Q i)) := by
  rw [homogeneousPart3_sosVectorSq3_four]
  unfold sosVectorSq3 homogeneousPartVec3
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  simp only [pow_two]
  conv_rhs =>
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
  abel

theorem motzkinCoeffNorm_homogeneousPart3_sosVectorSq3_zero_le {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (homogeneousPart3 0 (sosVectorSq3 Q)) ≤
      motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) ^ 2 := by
  rw [homogeneousPart3_sosVectorSq3_zero]
  exact motzkinCoeffNorm_sosVectorSq3_le_sq _

theorem motzkinCoeffNorm_homogeneousPart3_sosVectorSq3_one_le {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (homogeneousPart3 1 (sosVectorSq3 Q)) ≤
      2 * motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) *
        motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) := by
  rw [homogeneousPart3_sosVectorSq3_one]
  have hsum : motzkinCoeffNorm
      (∑ i : Fin N,
        (homogeneousPart3 0 (Q i) * homogeneousPart3 1 (Q i) +
          homogeneousPart3 1 (Q i) * homogeneousPart3 0 (Q i))) ≤
      ∑ i : Fin N,
        (motzkinCoeffNorm (homogeneousPart3 0 (Q i)) * motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
          motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 0 (Q i))) := by
    calc
      motzkinCoeffNorm (∑ i : Fin N,
          (homogeneousPart3 0 (Q i) * homogeneousPart3 1 (Q i) +
            homogeneousPart3 1 (Q i) * homogeneousPart3 0 (Q i)))
          ≤ ∑ i : Fin N, motzkinCoeffNorm
            (homogeneousPart3 0 (Q i) * homogeneousPart3 1 (Q i) +
              homogeneousPart3 1 (Q i) * homogeneousPart3 0 (Q i)) := by
            simpa using motzkinCoeffNorm_sum_le (Finset.univ : Finset (Fin N)) fun i =>
              homogeneousPart3 0 (Q i) * homogeneousPart3 1 (Q i) +
              homogeneousPart3 1 (Q i) * homogeneousPart3 0 (Q i)
      _ ≤ ∑ i : Fin N,
          (motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 0 (Q i))) := by
            apply Finset.sum_le_sum
            intro i _hi
            calc
              motzkinCoeffNorm
                (homogeneousPart3 0 (Q i) * homogeneousPart3 1 (Q i) +
                  homogeneousPart3 1 (Q i) * homogeneousPart3 0 (Q i))
                  ≤ motzkinCoeffNorm (homogeneousPart3 0 (Q i) * homogeneousPart3 1 (Q i)) +
                    motzkinCoeffNorm (homogeneousPart3 1 (Q i) * homogeneousPart3 0 (Q i)) :=
                    motzkinCoeffNorm_add_le _ _
              _ ≤
                  motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
                      motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
                    motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
                      motzkinCoeffNorm (homogeneousPart3 0 (Q i)) := by
                    gcongr <;> apply motzkinCoeffNorm_mul_le
  have hdot :
      (∑ i : Fin N,
        motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 1 (Q i))) ≤
        motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) *
          motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) := by
    simpa [homogeneousPartVec3] using motzkinCoeffNorm_dot_le_motzkinVecCoeffNorm_mul
      (homogeneousPartVec3 0 Q) (homogeneousPartVec3 1 Q)
  calc
    motzkinCoeffNorm (∑ i : Fin N,
        (homogeneousPart3 0 (Q i) * homogeneousPart3 1 (Q i) +
          homogeneousPart3 1 (Q i) * homogeneousPart3 0 (Q i)))
        ≤ ∑ i : Fin N,
          (motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 0 (Q i))) := hsum
    _ = 2 * ∑ i : Fin N,
          motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ ≤ 2 * motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) *
        motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) := by
          nlinarith

theorem motzkinCoeffNorm_homogeneousPart3_sosVectorSq3_two_le {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (homogeneousPart3 2 (sosVectorSq3 Q)) ≤
      2 * motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) *
          motzkinVecCoeffNorm (homogeneousPartVec3 2 Q) +
        motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) ^ 2 := by
  rw [homogeneousPart3_sosVectorSq3_two]
  calc
    motzkinCoeffNorm (∑ i : Fin N,
        (homogeneousPart3 0 (Q i) * homogeneousPart3 2 (Q i) +
          homogeneousPart3 1 (Q i) * homogeneousPart3 1 (Q i) +
          homogeneousPart3 2 (Q i) * homogeneousPart3 0 (Q i)))
        ≤ ∑ i : Fin N,
          (motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 2 (Q i)) +
            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
            motzkinCoeffNorm (homogeneousPart3 2 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 0 (Q i))) := by
          calc
            motzkinCoeffNorm (∑ i : Fin N,
                (homogeneousPart3 0 (Q i) * homogeneousPart3 2 (Q i) +
                  homogeneousPart3 1 (Q i) * homogeneousPart3 1 (Q i) +
                  homogeneousPart3 2 (Q i) * homogeneousPart3 0 (Q i)))
                ≤ ∑ i : Fin N, motzkinCoeffNorm
                  (homogeneousPart3 0 (Q i) * homogeneousPart3 2 (Q i) +
                    homogeneousPart3 1 (Q i) * homogeneousPart3 1 (Q i) +
                    homogeneousPart3 2 (Q i) * homogeneousPart3 0 (Q i)) := by
                  simpa using motzkinCoeffNorm_sum_le (Finset.univ : Finset (Fin N)) fun i =>
                    homogeneousPart3 0 (Q i) * homogeneousPart3 2 (Q i) +
                    homogeneousPart3 1 (Q i) * homogeneousPart3 1 (Q i) +
                    homogeneousPart3 2 (Q i) * homogeneousPart3 0 (Q i)
            _ ≤ ∑ i : Fin N,
                (motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 2 (Q i)) +
                  motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
                  motzkinCoeffNorm (homogeneousPart3 2 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 0 (Q i))) := by
                  apply Finset.sum_le_sum
                  intro i _hi
                  calc
                    motzkinCoeffNorm
                      (homogeneousPart3 0 (Q i) * homogeneousPart3 2 (Q i) +
                        homogeneousPart3 1 (Q i) * homogeneousPart3 1 (Q i) +
                        homogeneousPart3 2 (Q i) * homogeneousPart3 0 (Q i))
                        ≤ motzkinCoeffNorm (homogeneousPart3 0 (Q i) * homogeneousPart3 2 (Q i)) +
                          motzkinCoeffNorm (homogeneousPart3 1 (Q i) * homogeneousPart3 1 (Q i)) +
                          motzkinCoeffNorm
                            (homogeneousPart3 2 (Q i) * homogeneousPart3 0 (Q i)) := by
                          simpa [add_assoc] using
                            motzkinCoeffNorm_add_le
                              (homogeneousPart3 0 (Q i) * homogeneousPart3 2 (Q i) +
                                homogeneousPart3 1 (Q i) * homogeneousPart3 1 (Q i))
                              (homogeneousPart3 2 (Q i) * homogeneousPart3 0 (Q i)) |>.trans
                              (by
                                nlinarith [motzkinCoeffNorm_add_le
                                  (homogeneousPart3 0 (Q i) * homogeneousPart3 2 (Q i))
                                  (homogeneousPart3 1 (Q i) * homogeneousPart3 1 (Q i))])
                    _ ≤
                        motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
                            motzkinCoeffNorm (homogeneousPart3 2 (Q i)) +
                          motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
                            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
                          motzkinCoeffNorm (homogeneousPart3 2 (Q i)) *
                            motzkinCoeffNorm (homogeneousPart3 0 (Q i)) := by
                          gcongr <;> apply motzkinCoeffNorm_mul_le
    _ = 2 * (∑ i : Fin N,
          motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 2 (Q i))) +
        ∑ i : Fin N, motzkinCoeffNorm (homogeneousPart3 1 (Q i)) ^ 2 := by
          have hcomm :
              (∑ i : Fin N,
                motzkinCoeffNorm (homogeneousPart3 2 (Q i)) *
                  motzkinCoeffNorm (homogeneousPart3 0 (Q i))) =
                ∑ i : Fin N,
                  motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 2 (Q i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcomm]
          ring_nf
    _ ≤ 2 * motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) *
          motzkinVecCoeffNorm (homogeneousPartVec3 2 Q) +
        motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) ^ 2 := by
          have h02 :
              (∑ i : Fin N,
                motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
                  motzkinCoeffNorm (homogeneousPart3 2 (Q i))) ≤
                motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) *
                  motzkinVecCoeffNorm (homogeneousPartVec3 2 Q) := by
            simpa [homogeneousPartVec3] using motzkinCoeffNorm_dot_le_motzkinVecCoeffNorm_mul
              (homogeneousPartVec3 0 Q) (homogeneousPartVec3 2 Q)
          have h1sq :
              (∑ i : Fin N, motzkinCoeffNorm (homogeneousPart3 1 (Q i)) ^ 2) =
                motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) ^ 2 := by
            unfold motzkinVecCoeffNorm homogeneousPartVec3
            rw [Real.sq_sqrt]
            exact Finset.sum_nonneg fun _ _ => sq_nonneg _
          nlinarith

theorem motzkinCoeffNorm_homogeneousPart3_sosVectorSq3_three_le {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (homogeneousPart3 3 (sosVectorSq3 Q)) ≤
      2 * motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) *
          motzkinVecCoeffNorm (homogeneousPartVec3 3 Q) +
        2 * motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) *
          motzkinVecCoeffNorm (homogeneousPartVec3 2 Q) := by
  rw [homogeneousPart3_sosVectorSq3_three]
  -- The degree-three estimate is the same four-product calculation as the unweighted error.
  calc
    motzkinCoeffNorm (∑ i : Fin N,
        (homogeneousPart3 0 (Q i) * homogeneousPart3 3 (Q i) +
          homogeneousPart3 1 (Q i) * homogeneousPart3 2 (Q i) +
          homogeneousPart3 2 (Q i) * homogeneousPart3 1 (Q i) +
          homogeneousPart3 3 (Q i) * homogeneousPart3 0 (Q i)))
        ≤ ∑ i : Fin N,
          (motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 3 (Q i)) +
            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 2 (Q i)) +
            motzkinCoeffNorm (homogeneousPart3 2 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
            motzkinCoeffNorm (homogeneousPart3 3 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 0 (Q i))) := by
          calc
            motzkinCoeffNorm (∑ i : Fin N,
                (homogeneousPart3 0 (Q i) * homogeneousPart3 3 (Q i) +
                  homogeneousPart3 1 (Q i) * homogeneousPart3 2 (Q i) +
                  homogeneousPart3 2 (Q i) * homogeneousPart3 1 (Q i) +
                  homogeneousPart3 3 (Q i) * homogeneousPart3 0 (Q i)))
                ≤ ∑ i : Fin N, motzkinCoeffNorm
                  (homogeneousPart3 0 (Q i) * homogeneousPart3 3 (Q i) +
                    homogeneousPart3 1 (Q i) * homogeneousPart3 2 (Q i) +
                    homogeneousPart3 2 (Q i) * homogeneousPart3 1 (Q i) +
                    homogeneousPart3 3 (Q i) * homogeneousPart3 0 (Q i)) := by
                  simpa using motzkinCoeffNorm_sum_le (Finset.univ : Finset (Fin N)) fun i =>
                    homogeneousPart3 0 (Q i) * homogeneousPart3 3 (Q i) +
                    homogeneousPart3 1 (Q i) * homogeneousPart3 2 (Q i) +
                    homogeneousPart3 2 (Q i) * homogeneousPart3 1 (Q i) +
                    homogeneousPart3 3 (Q i) * homogeneousPart3 0 (Q i)
            _ ≤ ∑ i : Fin N,
                (motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 3 (Q i)) +
                  motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 2 (Q i)) +
                  motzkinCoeffNorm (homogeneousPart3 2 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
                  motzkinCoeffNorm (homogeneousPart3 3 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 0 (Q i))) := by
                  apply Finset.sum_le_sum
                  intro i _hi
                  calc
                    motzkinCoeffNorm
                      (homogeneousPart3 0 (Q i) * homogeneousPart3 3 (Q i) +
                        homogeneousPart3 1 (Q i) * homogeneousPart3 2 (Q i) +
                        homogeneousPart3 2 (Q i) * homogeneousPart3 1 (Q i) +
                        homogeneousPart3 3 (Q i) * homogeneousPart3 0 (Q i))
                        ≤ motzkinCoeffNorm (homogeneousPart3 0 (Q i) * homogeneousPart3 3 (Q i)) +
                          motzkinCoeffNorm (homogeneousPart3 1 (Q i) * homogeneousPart3 2 (Q i)) +
                          motzkinCoeffNorm (homogeneousPart3 2 (Q i) * homogeneousPart3 1 (Q i)) +
                          motzkinCoeffNorm (homogeneousPart3 3 (Q i) * homogeneousPart3 0 (Q i)) :=
                          motzkinCoeffNorm_add4_le _ _ _ _
                    _ ≤
                        motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
                            motzkinCoeffNorm (homogeneousPart3 3 (Q i)) +
                          motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
                            motzkinCoeffNorm (homogeneousPart3 2 (Q i)) +
                          motzkinCoeffNorm (homogeneousPart3 2 (Q i)) *
                            motzkinCoeffNorm (homogeneousPart3 1 (Q i)) +
                          motzkinCoeffNorm (homogeneousPart3 3 (Q i)) *
                            motzkinCoeffNorm (homogeneousPart3 0 (Q i)) := by
                          gcongr <;> apply motzkinCoeffNorm_mul_le
    _ = 2 * (∑ i : Fin N,
          motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 3 (Q i))) +
        2 * (∑ i : Fin N,
          motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
            motzkinCoeffNorm (homogeneousPart3 2 (Q i))) := by
          have h30 :
              (∑ i : Fin N,
                motzkinCoeffNorm (homogeneousPart3 3 (Q i)) *
                  motzkinCoeffNorm (homogeneousPart3 0 (Q i))) =
                ∑ i : Fin N,
                  motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 3 (Q i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          have h21 :
              (∑ i : Fin N,
                motzkinCoeffNorm (homogeneousPart3 2 (Q i)) *
                  motzkinCoeffNorm (homogeneousPart3 1 (Q i))) =
                ∑ i : Fin N,
                  motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
                    motzkinCoeffNorm (homogeneousPart3 2 (Q i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [h30, h21]
          ring_nf
    _ ≤ 2 * motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) *
          motzkinVecCoeffNorm (homogeneousPartVec3 3 Q) +
        2 * motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) *
          motzkinVecCoeffNorm (homogeneousPartVec3 2 Q) := by
          have h03 :
              (∑ i : Fin N,
                motzkinCoeffNorm (homogeneousPart3 0 (Q i)) *
                  motzkinCoeffNorm (homogeneousPart3 3 (Q i))) ≤
                motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) *
                  motzkinVecCoeffNorm (homogeneousPartVec3 3 Q) := by
            simpa [homogeneousPartVec3] using motzkinCoeffNorm_dot_le_motzkinVecCoeffNorm_mul
              (homogeneousPartVec3 0 Q) (homogeneousPartVec3 3 Q)
          have h12 :
              (∑ i : Fin N,
                motzkinCoeffNorm (homogeneousPart3 1 (Q i)) *
                  motzkinCoeffNorm (homogeneousPart3 2 (Q i))) ≤
                motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) *
                  motzkinVecCoeffNorm (homogeneousPartVec3 2 Q) := by
            simpa [homogeneousPartVec3] using motzkinCoeffNorm_dot_le_motzkinVecCoeffNorm_mul
              (homogeneousPartVec3 1 Q) (homogeneousPartVec3 2 Q)
          nlinarith

lemma isHomogeneous_of_homogeneousPart3_eq {m : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (h : homogeneousPart3 m p = p) : p.IsHomogeneous m := by
  rw [← h, homogeneousPart3_eq_homogeneousComponent]
  exact MvPolynomial.homogeneousComponent_isHomogeneous m p

lemma isHomogeneous_eval_smul {m : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous m) (c : ℝ) (x : Fin 3 → ℝ) :
    MvPolynomial.eval (fun i => c * x i) p = c ^ m * MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg_weight : Finsupp.weight (fun _ : Fin 3 => (1 : ℕ)) d = m :=
    hp (Finsupp.mem_support_iff.mp hd)
  have hdeg : Finsupp.degree d = m := by
    simpa [Finsupp.degree_eq_weight_one] using hdeg_weight
  calc
    MvPolynomial.coeff d p * ∏ i ∈ d.support, (c * x i) ^ d i
        = MvPolynomial.coeff d p * (c ^ m * ∏ i ∈ d.support, x i ^ d i) := by
          rw [← hdeg]
          simp_rw [mul_pow]
          rw [Finset.prod_mul_distrib]
          simp_rw [Finset.prod_pow_eq_pow_sum]
          simp [Finsupp.degree_apply]
    _ = c ^ m * (MvPolynomial.coeff d p * ∏ i ∈ d.support, x i ^ d i) := by
      ring

lemma abs_eval_le_motzkinCoeffNorm_of_motzkinSqNorm_eq_one (p : MvPolynomial (Fin 3) ℝ)
    {x : Fin 3 → ℝ} (hx : motzkinSqNorm x = 1) :
    |MvPolynomial.eval x p| ≤ motzkinCoeffNorm p := by
  rw [MvPolynomial.eval_eq]
  calc
    |∑ d ∈ p.support, MvPolynomial.coeff d p * ∏ i ∈ d.support, x i ^ d i|
        ≤ ∑ d ∈ p.support,
            |MvPolynomial.coeff d p * ∏ i ∈ d.support, x i ^ d i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ p.support, |MvPolynomial.coeff d p| := by
      apply Finset.sum_le_sum
      intro d _hd
      rw [abs_mul]
      have hprod_le : |∏ i ∈ d.support, x i ^ d i| ≤ 1 := by
        rw [Finset.abs_prod]
        apply Finset.prod_le_one
        · intro i _hi
          exact abs_nonneg _
        · intro i _hi
          rw [abs_pow]
          have hxi : |x i| ≤ 1 := by
            rw [← sq_le_one_iff_abs_le_one]
            have hsq := sq_coord_le_motzkinSqNorm x i
            simpa [hx] using hsq
          exact pow_le_one₀ (abs_nonneg _) hxi
      exact mul_le_of_le_one_right (abs_nonneg _) hprod_le
    _ = motzkinCoeffNorm p := rfl

lemma interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one {N : ℕ}
    (H : Fin N → MvPolynomial (Fin 3) ℝ) {x : Fin 3 → ℝ} (hx : motzkinSqNorm x = 1) :
    interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (H i)) ≤ motzkinVecCoeffNorm H := by
  unfold interiorVecNorm motzkinVecCoeffNorm
  apply Real.sqrt_le_sqrt
  unfold interiorVecSqNorm
  calc
    ∑ i : Fin N, MvPolynomial.eval x (H i) ^ 2
        = ∑ i : Fin N, |MvPolynomial.eval x (H i)| ^ 2 := by
          simp [sq_abs]
    _ ≤ ∑ i : Fin N, motzkinCoeffNorm (H i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [sq_le_sq]
      rw [abs_of_nonneg (motzkinCoeffNorm_nonneg _), abs_abs]
      exact abs_eval_le_motzkinCoeffNorm_of_motzkinSqNorm_eq_one (H i) hx

lemma motzkinSqNorm_eq_zero_iff (x : Fin 3 → ℝ) : motzkinSqNorm x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have hsq0 : x i ^ 2 = 0 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun j _ => sq_nonneg (x j))).mp ?_ i (Finset.mem_univ i)
      · exact hall
      · simpa [motzkinSqNorm] using hx
    exact sq_eq_zero_iff.mp hsq0
  · intro hx
    simp [hx, motzkinSqNorm]

lemma motzkinSqNorm_pos_of_ne_zero {x : Fin 3 → ℝ} (hx : x ≠ 0) :
    0 < motzkinSqNorm x := by
  exact lt_of_le_of_ne (motzkinSqNorm_nonneg x)
    (fun h => hx ((motzkinSqNorm_eq_zero_iff x).mp h.symm))

lemma motzkinSqNorm_smul (c : ℝ) (x : Fin 3 → ℝ) :
    motzkinSqNorm (fun i => c * x i) = c ^ 2 * motzkinSqNorm x := by
  simp [motzkinSqNorm, mul_pow, Finset.mul_sum]

lemma motzkinSqNorm_normalize_eq_one {x : Fin 3 → ℝ} (hx : 0 < motzkinSqNorm x) :
    motzkinSqNorm (fun i => (Real.sqrt (motzkinSqNorm x))⁻¹ * x i) = 1 := by
  rw [motzkinSqNorm_smul]
  have hs : Real.sqrt (motzkinSqNorm x) ^ 2 = motzkinSqNorm x := Real.sq_sqrt hx.le
  have hsne : Real.sqrt (motzkinSqNorm x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  field_simp [hsne]
  exact hs.symm

lemma eval_eq_zero_of_unit_eq_zero {m : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p.IsHomogeneous m)
    (hunit : ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 → MvPolynomial.eval v p = 0) :
    ∀ x : Fin 3 → ℝ, MvPolynomial.eval x p = 0 := by
  intro x
  by_cases hx0 : x = 0
  · subst x
    let e : Fin 3 → ℝ := fun i => if i = 0 then 1 else 0
    have he : motzkinSqNorm e = 1 := by
      simp [e, motzkinSqNorm]
    have hscale := isHomogeneous_eval_smul hp 0 e
    simpa [e, hunit e he] using hscale
  · have hxpos : 0 < motzkinSqNorm x := motzkinSqNorm_pos_of_ne_zero hx0
    let c := Real.sqrt (motzkinSqNorm x)
    let u : Fin 3 → ℝ := fun i => c⁻¹ * x i
    have hu : motzkinSqNorm u = 1 := by
      dsimp [u, c]
      exact motzkinSqNorm_normalize_eq_one hxpos
    have hcu : (fun i => c * u i) = x := by
      funext i
      dsimp [u, c]
      have hcne : Real.sqrt (motzkinSqNorm x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hxpos)
      field_simp [hcne]
    have hscale := isHomogeneous_eval_smul hp c u
    rw [hcu] at hscale
    rw [hscale, hunit u hu, mul_zero]


private def unit3 (j : Fin 3) : Fin 3 → ℝ := fun i => if i = j then 1 else 0

private def pair4 (i j : Fin 3) : Fin 3 → ℝ :=
  fun k => if k = i ∨ k = j then 1 else 0

private lemma motzkinSqNorm_unit3 (j : Fin 3) : motzkinSqNorm (unit3 j) = 1 := by
  fin_cases j <;> simp [unit3, motzkinSqNorm]

private lemma finsupp_degree_one_cases {a : Fin 3 →₀ ℕ}
    (ha : a.sum (fun _ e => e) = 1) :
    ∃ j : Fin 3, a = Finsupp.single j 1 := by
  exact (Finsupp.sum_eq_one_iff a).mp ha

private lemma single_one_injective :
    Function.Injective (fun j : Fin 3 => Finsupp.single j 1) := by
  intro i j hij
  by_contra hne
  have hi := Finsupp.ext_iff.mp hij i
  simp [hne] at hi

private lemma motzkinCoeffNorm_linear_le_sum_coeff {p : MvPolynomial (Fin 3) ℝ}
    (hp : homogeneousPart3 1 p = p) :
    motzkinCoeffNorm p ≤ ∑ j : Fin 3, |MvPolynomial.coeff (Finsupp.single j 1) p| := by
  unfold motzkinCoeffNorm
  have hsubset : p.support ⊆ (Finset.univ.image fun j : Fin 3 => Finsupp.single j 1) := by
    intro a ha
    have hhom := isHomogeneous_of_homogeneousPart3_eq hp
    have hweight := hhom (MvPolynomial.mem_support_iff.mp ha)
    have hsum : a.sum (fun _ e => e) = 1 := by
      have hdeg : Finsupp.degree a = 1 := by
        simpa [Finsupp.degree_eq_weight_one] using hweight
      simpa [Finsupp.degree_apply] using hdeg
    obtain ⟨j, rfl⟩ := finsupp_degree_one_cases hsum
    simp
  calc
    ∑ α ∈ p.support, |MvPolynomial.coeff α p|
        ≤ ∑ α ∈ (Finset.univ.image fun j : Fin 3 => Finsupp.single j 1),
            |MvPolynomial.coeff α p| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro x _hx _hnot
          exact abs_nonneg _
    _ = ∑ j : Fin 3, |MvPolynomial.coeff (Finsupp.single j 1) p| := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij => single_one_injective hij

private lemma linear_eq_sum_monomial {p : MvPolynomial (Fin 3) ℝ}
    (hp : homogeneousPart3 1 p = p) :
    p = ∑ j : Fin 3, MvPolynomial.monomial (Finsupp.single j 1)
      (MvPolynomial.coeff (Finsupp.single j 1) p) := by
  ext α
  rw [MvPolynomial.coeff_sum]
  by_cases hα : α ∈ p.support
  · have hhom := isHomogeneous_of_homogeneousPart3_eq hp
    have hweight := hhom (MvPolynomial.mem_support_iff.mp hα)
    have hsum : α.sum (fun _ e => e) = 1 := by
      have hdeg : Finsupp.degree α = 1 := by
        simpa [Finsupp.degree_eq_weight_one] using hweight
      simpa [Finsupp.degree_apply] using hdeg
    obtain ⟨j, rfl⟩ := finsupp_degree_one_cases hsum
    rw [Finset.sum_eq_single j]
    · simp [MvPolynomial.coeff_monomial]
    · intro k _ hk
      have hne : Finsupp.single k 1 ≠ Finsupp.single j 1 := by
        intro h
        exact hk (single_one_injective h)
      simp [MvPolynomial.coeff_monomial, hne]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · have hcoeff : MvPolynomial.coeff α p = 0 := by
      by_contra hc
      exact hα (MvPolynomial.mem_support_iff.mpr hc)
    rw [hcoeff]
    symm
    apply Finset.sum_eq_zero
    intro j _
    by_cases hαj : Finsupp.single j 1 = α
    · rw [← hαj]
      have hcoeffj : MvPolynomial.coeff (Finsupp.single j 1) p = 0 := by
        by_contra hc
        exact hα (by simpa [hαj] using MvPolynomial.mem_support_iff.mpr hc)
      simp [hcoeffj]
    · simp [MvPolynomial.coeff_monomial, hαj]

lemma eval_linear_eq_sum_coeff {p : MvPolynomial (Fin 3) ℝ}
    (hp : homogeneousPart3 1 p = p) (x : Fin 3 → ℝ) :
    MvPolynomial.eval x p = ∑ j : Fin 3, MvPolynomial.coeff (Finsupp.single j 1) p * x j := by
  calc
    MvPolynomial.eval x p =
        MvPolynomial.eval x (∑ j : Fin 3, MvPolynomial.monomial (Finsupp.single j 1)
          (MvPolynomial.coeff (Finsupp.single j 1) p)) := by
          exact congrArg (MvPolynomial.eval x) (linear_eq_sum_monomial hp)
    _ = ∑ j : Fin 3, MvPolynomial.coeff (Finsupp.single j 1) p * x j := by
      simp [MvPolynomial.eval_monomial]

lemma coeff_single_one_eq_eval_unit {p : MvPolynomial (Fin 3) ℝ}
    (hp : homogeneousPart3 1 p = p) (j : Fin 3) :
    MvPolynomial.coeff (Finsupp.single j 1) p = MvPolynomial.eval (unit3 j) p := by
  have h := eval_linear_eq_sum_coeff hp (unit3 j)
  fin_cases j <;> simp [unit3] at h ⊢ <;> linarith

lemma interiorVecNorm_abs {N : ℕ} (v : Fin N → ℝ) :
    interiorVecNorm (fun i => |v i|) = interiorVecNorm v := by
  unfold interiorVecNorm interiorVecSqNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [sq_abs]

lemma interiorVecNorm_add_le {N : ℕ} (u v : Fin N → ℝ) :
    interiorVecNorm (fun i => u i + v i) ≤ interiorVecNorm u + interiorVecNorm v := by
  change vecNorm (fun i => u i + v i) ≤ vecNorm u + vecNorm v
  exact vecNorm_add_le u v

lemma interiorVecNorm_neg {N : ℕ} (u : Fin N → ℝ) :
    interiorVecNorm (fun i => -u i) = interiorVecNorm u := by
  unfold interiorVecNorm interiorVecSqNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma interiorVecNorm_smul_abs {N : ℕ} (c : ℝ) (u : Fin N → ℝ) :
    interiorVecNorm (fun i => c * u i) = |c| * interiorVecNorm u := by
  by_cases hc : 0 ≤ c
  · simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm, abs_of_nonneg hc] using
      vecNorm_smul_nonneg (N := N) c hc u
  · have hneg : 0 ≤ -c := neg_nonneg.mpr (le_of_not_ge hc)
    calc
      interiorVecNorm (fun i => c * u i) =
          interiorVecNorm (fun i => (-c) * (-u i)) := by
        congr 1
        funext i
        ring
      _ = (-c) * interiorVecNorm (fun i => -u i) := by
        simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
          vecNorm_smul_nonneg (N := N) (-c) hneg (fun i => -u i)
      _ = |c| * interiorVecNorm u := by
        rw [interiorVecNorm_neg, abs_of_neg (lt_of_not_ge hc)]

lemma interiorVecNorm_sub_le {N : ℕ} (u v : Fin N → ℝ) :
    interiorVecNorm (fun i => u i - v i) ≤ interiorVecNorm u + interiorVecNorm v := by
  calc
    interiorVecNorm (fun i => u i - v i) = interiorVecNorm (fun i => u i + -v i) := by rfl
    _ ≤ interiorVecNorm u + interiorVecNorm (fun i => -v i) :=
      interiorVecNorm_add_le u (fun i => -v i)
    _ = interiorVecNorm u + interiorVecNorm v := by rw [interiorVecNorm_neg]

private lemma interiorVecNorm_finset_sum_le_sum_norm {N : ℕ} {ι : Type*}
    (s : Finset ι) (V : ι → Fin N → ℝ) :
    interiorVecNorm (fun i => ∑ z ∈ s, V z i) ≤ ∑ z ∈ s, interiorVecNorm (V z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [interiorVecNorm, interiorVecSqNorm]
  | insert a s has ih =>
      conv_lhs =>
        arg 1
        ext i
        rw [Finset.sum_insert has]
      rw [Finset.sum_insert has]
      calc
        interiorVecNorm (fun i => V a i + ∑ z ∈ s, V z i)
            ≤ interiorVecNorm (V a) + interiorVecNorm (fun i => ∑ z ∈ s, V z i) :=
              interiorVecNorm_add_le (V a) (fun i => ∑ z ∈ s, V z i)
        _ ≤ interiorVecNorm (V a) + ∑ z ∈ s, interiorVecNorm (V z) := by
          linarith


private lemma finsupp_degree_two_as_sum_single {a : Fin 3 →₀ ℕ} (ha : a.degree = 2) :
    ∃ i j : Fin 3, a = Finsupp.single i 1 + Finsupp.single j 1 := by
  have hmem : a ∈ (2 : ℕ) • ((fun i : Fin 3 => Finsupp.single i 1) '' Set.univ) := by
    rw [Finsupp.nsmul_single_one_image]
    exact ⟨ha, by simp⟩
  have hmem2 : a ∈ ((fun i : Fin 3 => Finsupp.single i 1) '' Set.univ) +
      ((fun i : Fin 3 => Finsupp.single i 1) '' Set.univ) := by
    simpa [two_nsmul] using hmem
  rcases hmem2 with ⟨x, hx, y, hy, hxy⟩
  rcases hx with ⟨i, _, rfl⟩
  rcases hy with ⟨j, _, rfl⟩
  exact ⟨i, j, hxy.symm⟩


private lemma single_one_add_self (a : Fin 3) :
    Finsupp.single a 1 + Finsupp.single a 1 = Finsupp.single a 2 := by
  ext k
  by_cases h : k = a <;> simp [h]

private lemma single_two_ne_single_two {i j : Fin 3} (hij : i ≠ j) :
    Finsupp.single i 2 ≠ Finsupp.single j 2 := by
  intro h
  have hi := Finsupp.ext_iff.mp h i
  simp [hij] at hi

private lemma single_two_ne_pair {i j : Fin 3} (hij : i ≠ j) :
    Finsupp.single i 2 ≠ Finsupp.single i 1 + Finsupp.single j 1 := by
  intro h
  have hj := Finsupp.ext_iff.mp h j
  simp [hij.symm] at hj

private lemma pair_ne_single_two {i j : Fin 3} (hij : i ≠ j) :
    Finsupp.single i 1 + Finsupp.single j 1 ≠ Finsupp.single j 2 := by
  intro h
  have hi := Finsupp.ext_iff.mp h i
  simp [hij] at hi

private lemma single_two_right_ne_pair {i j : Fin 3} (hij : i ≠ j) :
    Finsupp.single j 2 ≠ Finsupp.single i 1 + Finsupp.single j 1 := by
  exact (pair_ne_single_two hij).symm

private lemma degree_two_eq_single_of_other_coords_zero (d : Fin 3 →₀ ℕ) (j : Fin 3)
    (hd : d.degree = 2) (hzero : ∀ k : Fin 3, k ≠ j → d k = 0) :
    d = Finsupp.single j 2 := by
  ext k
  by_cases hkj : k = j
  · subst k
    rw [Finsupp.single_eq_same]
    have hsum : d.sum (fun _ e => e) = 2 := by
      simpa [Finsupp.degree_apply] using hd
    rw [Finsupp.sum_fintype] at hsum
    · fin_cases j <;> simp [hzero, Fin.sum_univ_three] at hsum ⊢ <;> omega
    · intro i
      rfl
  · rw [Finsupp.single_eq_of_ne hkj]
    exact hzero k hkj

private lemma exists_other_support_of_degree_two_ne_single (d : Fin 3 →₀ ℕ) (j : Fin 3)
    (hd : d.degree = 2) (hneq : d ≠ Finsupp.single j 2) :
    ∃ k : Fin 3, k ≠ j ∧ k ∈ d.support := by
  by_contra hnot
  have hzero : ∀ k : Fin 3, k ≠ j → d k = 0 := by
    intro k hkj
    by_contra hk
    have hksupp : k ∈ d.support := by simpa [Finsupp.mem_support_iff] using hk
    exact hnot ⟨k, hkj, hksupp⟩
  exact hneq (degree_two_eq_single_of_other_coords_zero d j hd hzero)

private lemma degree_two_unit_support_prod_eq_zero_of_ne_single (d : Fin 3 →₀ ℕ) (j : Fin 3)
    (hd : d.degree = 2) (hneq : d ≠ Finsupp.single j 2) :
    ∏ i ∈ d.support, unit3 j i ^ d i = 0 := by
  obtain ⟨k, hkj, hksupp⟩ := exists_other_support_of_degree_two_ne_single d j hd hneq
  apply Finset.prod_eq_zero hksupp
  have hkne : d k ≠ 0 := Finsupp.mem_support_iff.mp hksupp
  simp [unit3, hkj, hkne]

private lemma unit_single_two_support_prod_eq_one (j : Fin 3) :
    ∏ i ∈ (Finsupp.single j 2 : Fin 3 →₀ ℕ).support,
      unit3 j i ^ (Finsupp.single j 2 : Fin 3 →₀ ℕ) i = 1 := by
  rw [Finset.prod_eq_single j]
  · simp [unit3]
  · intro b hb hbj
    simp [Finsupp.mem_support_iff] at hb
    simp [Finsupp.single_eq_of_ne hbj] at hb
  · intro hj
    exact (hj (by simp [Finsupp.mem_support_iff])).elim

private lemma pair_single_two_support_prod_eq_one (i j : Fin 3) :
    ∏ k ∈ (Finsupp.single i 2 : Fin 3 →₀ ℕ).support,
      pair4 i j k ^ (Finsupp.single i 2 : Fin 3 →₀ ℕ) k = 1 := by
  rw [Finset.prod_eq_single i]
  · simp [pair4]
  · intro b hb hbi
    simp [Finsupp.mem_support_iff] at hb
    simp [Finsupp.single_eq_of_ne hbi] at hb
  · intro hi
    exact (hi (by simp [Finsupp.mem_support_iff])).elim

private lemma pair_single_two_support_prod_eq_one_right (i j : Fin 3) :
    ∏ k ∈ (Finsupp.single j 2 : Fin 3 →₀ ℕ).support,
      pair4 i j k ^ (Finsupp.single j 2 : Fin 3 →₀ ℕ) k = 1 := by
  rw [Finset.prod_eq_single j]
  · simp [pair4]
  · intro b hb hbj
    simp [Finsupp.mem_support_iff] at hb
    simp [Finsupp.single_eq_of_ne hbj] at hb
  · intro hj
    exact (hj (by simp [Finsupp.mem_support_iff])).elim

private lemma pair_mixed_support_prod_eq_one (i j : Fin 3) :
    ∏ k ∈ (Finsupp.single i 1 + Finsupp.single j 1 : Fin 3 →₀ ℕ).support,
      pair4 i j k ^ (Finsupp.single i 1 + Finsupp.single j 1 : Fin 3 →₀ ℕ) k = 1 := by
  apply Finset.prod_eq_one
  intro k hk
  have hkij : k = i ∨ k = j := by
    by_contra hnot
    simp only [not_or] at hnot
    have hkzero : (Finsupp.single i 1 + Finsupp.single j 1 : Fin 3 →₀ ℕ) k = 0 := by
      simp [hnot.1, hnot.2]
    exact (Finsupp.mem_support_iff.mp hk) hkzero
  simp [pair4, hkij]

private lemma degree_two_pair_support_prod_eq_zero_of_ne_terms (d : Fin 3 →₀ ℕ)
    (i j : Fin 3) (hd : d.degree = 2) (hne_i : d ≠ Finsupp.single i 2)
    (hne_j : d ≠ Finsupp.single j 2)
    (hne_ij : d ≠ Finsupp.single i 1 + Finsupp.single j 1) :
    ∏ k ∈ d.support, pair4 i j k ^ d k = 0 := by
  rcases finsupp_degree_two_as_sum_single hd with ⟨a, b, rfl⟩
  by_cases ha : a = i ∨ a = j
  · by_cases hb : b = i ∨ b = j
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact (hne_i (single_one_add_self _)).elim
      · exact (hne_ij rfl).elim
      · exact (hne_ij (by rw [add_comm])).elim
      · exact (hne_j (single_one_add_self _)).elim
    · have hbsupp : b ∈
          (Finsupp.single a 1 + Finsupp.single b 1 : Fin 3 →₀ ℕ).support := by
        simp [Finsupp.mem_support_iff]
      apply Finset.prod_eq_zero hbsupp
      have hbne : pair4 i j b = 0 := by simp [pair4, hb]
      simp [hbne]
  · have hasupp : a ∈
        (Finsupp.single a 1 + Finsupp.single b 1 : Fin 3 →₀ ℕ).support := by
      simp [Finsupp.mem_support_iff]
    apply Finset.prod_eq_zero hasupp
    have hane : pair4 i j a = 0 := by simp [pair4, ha]
    simp [hane]

private lemma sum_eq_sum_target_of_zero {α : Type*} {s T : Finset α} {f : α → ℝ}
    (hs : ∀ x ∈ s, x ∉ T → f x = 0) (hT : ∀ x ∈ T, x ∉ s → f x = 0) :
    ∑ x ∈ s, f x = ∑ x ∈ T, f x := by
  classical
  have hsunion : ∑ x ∈ s, f x = ∑ x ∈ s ∪ T, f x := by
    apply Finset.sum_subset (Finset.subset_union_left)
    intro x hx hxs
    exact hT x (Finset.mem_union.mp hx |>.elim (fun hsx => (hxs hsx).elim) id) hxs
  have hTunion : ∑ x ∈ T, f x = ∑ x ∈ s ∪ T, f x := by
    apply Finset.sum_subset (Finset.subset_union_right)
    intro x hx hxT
    exact hs x (Finset.mem_union.mp hx |>.elim id (fun htx => (hxT htx).elim)) hxT
  exact hsunion.trans hTunion.symm

lemma eval_unit_quadratic_eq_coeff_single_two {p : MvPolynomial (Fin 3) ℝ}
    (hp : homogeneousPart3 2 p = p) (j : Fin 3) :
    MvPolynomial.eval (unit3 j) p = MvPolynomial.coeff (Finsupp.single j 2) p := by
  rw [MvPolynomial.eval_eq]
  rw [Finset.sum_eq_single (Finsupp.single j 2)]
  · rw [unit_single_two_support_prod_eq_one]
    ring
  · intro d hdmem hneq
    have hhom := isHomogeneous_of_homogeneousPart3_eq hp
    have hweight := hhom (MvPolynomial.mem_support_iff.mp hdmem)
    have hddeg : d.degree = 2 := by simpa [Finsupp.degree_eq_weight_one] using hweight
    rw [degree_two_unit_support_prod_eq_zero_of_ne_single d j hddeg hneq]
    ring
  · intro hnot
    have hcoeff : MvPolynomial.coeff (Finsupp.single j 2) p = 0 := by
      exact MvPolynomial.notMem_support_iff.mp hnot
    simp [hcoeff]

lemma eval_pair_quadratic_eq_coeffs {p : MvPolynomial (Fin 3) ℝ}
    (hp : homogeneousPart3 2 p = p) {i j : Fin 3} (hij : i ≠ j) :
    MvPolynomial.eval (pair4 i j) p =
      MvPolynomial.coeff (Finsupp.single i 2) p +
      MvPolynomial.coeff (Finsupp.single j 2) p +
      MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) p := by
  let T : Finset (Fin 3 →₀ ℕ) :=
    {Finsupp.single i 2, Finsupp.single j 2, Finsupp.single i 1 + Finsupp.single j 1}
  rw [MvPolynomial.eval_eq]
  have hsum :
      (∑ d ∈ p.support,
        MvPolynomial.coeff d p * ∏ k ∈ d.support, pair4 i j k ^ d k) =
      ∑ d ∈ T, MvPolynomial.coeff d p * ∏ k ∈ d.support, pair4 i j k ^ d k := by
    apply sum_eq_sum_target_of_zero
    · intro d hdmem hdT
      have hhom := isHomogeneous_of_homogeneousPart3_eq hp
      have hweight := hhom (MvPolynomial.mem_support_iff.mp hdmem)
      have hddeg : d.degree = 2 := by simpa [Finsupp.degree_eq_weight_one] using hweight
      have hne_i : d ≠ Finsupp.single i 2 := by
        intro h; exact hdT (by simp [T, h])
      have hne_j : d ≠ Finsupp.single j 2 := by
        intro h; exact hdT (by simp [T, h])
      have hne_ij : d ≠ Finsupp.single i 1 + Finsupp.single j 1 := by
        intro h; exact hdT (by simp [T, h])
      rw [degree_two_pair_support_prod_eq_zero_of_ne_terms d i j hddeg hne_i hne_j hne_ij]
      ring
    · intro d hdT hdnot
      have hcoeff : MvPolynomial.coeff d p = 0 := MvPolynomial.notMem_support_iff.mp hdnot
      simp [hcoeff]
  rw [hsum]
  dsimp [T]
  rw [Finset.sum_insert]
  swap
  · simp [single_two_ne_single_two hij, single_two_ne_pair hij]
  rw [Finset.sum_insert]
  swap
  · simp [single_two_right_ne_pair hij]
  rw [pair_single_two_support_prod_eq_one i j]
  rw [pair_single_two_support_prod_eq_one_right i j]
  rw [Finset.sum_singleton]
  rw [pair_mixed_support_prod_eq_one i j]
  ring_nf

private lemma motzkinSqNorm_pair4_of_ne {i j : Fin 3} (hij : i ≠ j) :
    motzkinSqNorm (pair4 i j) = 2 := by
  unfold motzkinSqNorm
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [pair4, Fin.ext_iff] at hij ⊢ <;> norm_num

private lemma finset_sum_image_le_sum_of_nonneg {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (g : β → ℝ)
    (hg : ∀ x ∈ s, 0 ≤ g (f x)) :
    ∑ y ∈ s.image f, g y ≤ ∑ x ∈ s, g (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ih' : ∑ y ∈ s.image f, g y ≤ ∑ x ∈ s, g (f x) := by
        exact ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
      by_cases hfa : f a ∈ s.image f
      · have himage : (insert a s).image f = s.image f := by
          ext y
          constructor
          · intro hy
            rw [Finset.mem_image] at hy ⊢
            rcases hy with ⟨x, hx, rfl⟩
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact Finset.mem_image.mp hfa
            · exact ⟨x, hx, rfl⟩
          · intro hy
            rw [Finset.mem_image] at hy ⊢
            rcases hy with ⟨x, hx, rfl⟩
            exact ⟨x, Finset.mem_insert_of_mem hx, rfl⟩
        rw [himage, Finset.sum_insert ha]
        exact le_trans ih' (by
          exact le_add_of_nonneg_left (hg a (Finset.mem_insert_self a s)))
      · rw [Finset.image_insert, Finset.sum_insert hfa, Finset.sum_insert ha]
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left ih' (g (f a))

private lemma motzkinCoeffNorm_quadratic_le_ordered_sum_coeff {p : MvPolynomial (Fin 3) ℝ}
    (hp : homogeneousPart3 2 p = p) :
    motzkinCoeffNorm p ≤ ∑ ij : Fin 3 × Fin 3,
      |MvPolynomial.coeff (Finsupp.single ij.1 1 + Finsupp.single ij.2 1) p| := by
  classical
  unfold motzkinCoeffNorm
  let f : Fin 3 × Fin 3 → Fin 3 →₀ ℕ := fun ij =>
    Finsupp.single ij.1 1 + Finsupp.single ij.2 1
  have hsubset : p.support ⊆ (Finset.univ.image f) := by
    intro α hα
    have hhom := isHomogeneous_of_homogeneousPart3_eq hp
    have hweight := hhom (MvPolynomial.mem_support_iff.mp hα)
    have hdeg : Finsupp.degree α = 2 := by
      simpa [Finsupp.degree_eq_weight_one] using hweight
    rcases finsupp_degree_two_as_sum_single hdeg with ⟨i, j, rfl⟩
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
  calc
    ∑ α ∈ p.support, |MvPolynomial.coeff α p|
        ≤ ∑ α ∈ Finset.univ.image f, |MvPolynomial.coeff α p| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro x _ _
          exact abs_nonneg _
    _ ≤ ∑ ij : Fin 3 × Fin 3, |MvPolynomial.coeff (f ij) p| := by
      exact finset_sum_image_le_sum_of_nonneg Finset.univ f
        (fun α => |MvPolynomial.coeff α p|) (fun _ _ => abs_nonneg _)

lemma motzkinVecCoeffNorm_quadratic_le_ordered_sum_coeff_vectors {N : ℕ}
    (H : Fin N → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ i, homogeneousPart3 2 (H i) = H i) :
    motzkinVecCoeffNorm H ≤ ∑ ij : Fin 3 × Fin 3, interiorVecNorm
      (fun i : Fin N =>
        MvPolynomial.coeff (Finsupp.single ij.1 1 + Finsupp.single ij.2 1) (H i)) := by
  let f : Fin 3 × Fin 3 → Fin 3 →₀ ℕ := fun ij =>
    Finsupp.single ij.1 1 + Finsupp.single ij.2 1
  have hpoint : ∀ i : Fin N, motzkinCoeffNorm (H i) ≤
      ∑ ij : Fin 3 × Fin 3, |MvPolynomial.coeff (f ij) (H i)| := by
    intro i
    exact motzkinCoeffNorm_quadratic_le_ordered_sum_coeff (hhom i)
  have hnorm_point : motzkinVecCoeffNorm H ≤
      interiorVecNorm (fun i : Fin N => ∑ ij : Fin 3 × Fin 3,
        |MvPolynomial.coeff (f ij) (H i)|) := by
    unfold motzkinVecCoeffNorm interiorVecNorm interiorVecSqNorm
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    rw [sq_le_sq]
    rw [abs_of_nonneg (motzkinCoeffNorm_nonneg _)]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
    exact hpoint i
  calc
    motzkinVecCoeffNorm H ≤ interiorVecNorm (fun i : Fin N => ∑ ij : Fin 3 × Fin 3,
        |MvPolynomial.coeff (f ij) (H i)|) := hnorm_point
    _ ≤ ∑ ij : Fin 3 × Fin 3, interiorVecNorm
        (fun i : Fin N => |MvPolynomial.coeff (f ij) (H i)|) := by
          simpa using interiorVecNorm_finset_sum_le_sum_norm
            (Finset.univ : Finset (Fin 3 × Fin 3))
            (fun ij i => |MvPolynomial.coeff (f ij) (H i)|)
    _ = ∑ ij : Fin 3 × Fin 3, interiorVecNorm
        (fun i : Fin N => MvPolynomial.coeff (f ij) (H i)) := by
          apply Finset.sum_congr rfl
          intro ij _
          exact interiorVecNorm_abs _

lemma motzkinVecCoeffNorm_linear_le_sum_coeff_vectors {N : ℕ}
    (H : Fin N → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ i, homogeneousPart3 1 (H i) = H i) :
    motzkinVecCoeffNorm H ≤
      ∑ j : Fin 3, interiorVecNorm
        (fun i : Fin N => MvPolynomial.coeff (Finsupp.single j 1) (H i)) := by
  have hpoint : ∀ i : Fin N, motzkinCoeffNorm (H i) ≤
      ∑ j : Fin 3, |MvPolynomial.coeff (Finsupp.single j 1) (H i)| := by
    intro i
    exact motzkinCoeffNorm_linear_le_sum_coeff (hhom i)
  have hnorm_point : motzkinVecCoeffNorm H ≤
      interiorVecNorm (fun i : Fin N => ∑ j : Fin 3,
        |MvPolynomial.coeff (Finsupp.single j 1) (H i)|) := by
    unfold motzkinVecCoeffNorm interiorVecNorm interiorVecSqNorm
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    rw [sq_le_sq]
    rw [abs_of_nonneg (motzkinCoeffNorm_nonneg _)]
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
    exact hpoint i
  calc
    motzkinVecCoeffNorm H ≤ interiorVecNorm (fun i : Fin N => ∑ j : Fin 3,
        |MvPolynomial.coeff (Finsupp.single j 1) (H i)|) := hnorm_point
    _ ≤ ∑ j : Fin 3, interiorVecNorm
        (fun i : Fin N => |MvPolynomial.coeff (Finsupp.single j 1) (H i)|) := by
          simpa using interiorVecNorm_finset_sum_le_sum_norm
            (Finset.univ : Finset (Fin 3))
            (fun j i => |MvPolynomial.coeff (Finsupp.single j 1) (H i)|)
    _ = ∑ j : Fin 3, interiorVecNorm
        (fun i : Fin N => MvPolynomial.coeff (Finsupp.single j 1) (H i)) := by
          apply Finset.sum_congr rfl
          intro j _
          exact interiorVecNorm_abs _

/-- Uniform degree-one coefficient/spherical-sup estimate.

Unlike `coeff_norm_from_spherical_sup_norm`, the constant here is fixed (`3`) and does not
inspect the polynomial vector or the target dimension. -/
theorem coeff_norm_from_spherical_sup_norm_degree_one_uniform
    {N : ℕ} (H : Fin N → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ i, homogeneousPart3 1 (H i) = H i) :
    motzkinVecCoeffNorm H ≤
      3 * sSup { y : ℝ |
        ∃ v : Fin 3 → ℝ, motzkinSqNorm v = 1 ∧
          y = interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) } := by
  let S : Set ℝ := { y : ℝ |
    ∃ v : Fin 3 → ℝ, motzkinSqNorm v = 1 ∧
      y = interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) }
  have hbdd : BddAbove S := by
    refine ⟨motzkinVecCoeffNorm H, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    exact interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one H hv
  have hcoeff := motzkinVecCoeffNorm_linear_le_sum_coeff_vectors H hhom
  have hunit_le : ∀ j : Fin 3,
      interiorVecNorm (fun i : Fin N => MvPolynomial.coeff (Finsupp.single j 1) (H i)) ≤
        sSup S := by
    intro j
    have hmem : interiorVecNorm (fun i : Fin N => MvPolynomial.eval (unit3 j) (H i)) ∈ S :=
      ⟨unit3 j, motzkinSqNorm_unit3 j, rfl⟩
    calc
      interiorVecNorm (fun i : Fin N => MvPolynomial.coeff (Finsupp.single j 1) (H i)) =
          interiorVecNorm (fun i : Fin N => MvPolynomial.eval (unit3 j) (H i)) := by
            congr 1
            funext i
            exact coeff_single_one_eq_eval_unit (hhom i) j
      _ ≤ sSup S := le_csSup hbdd hmem
  calc
    motzkinVecCoeffNorm H ≤
        ∑ j : Fin 3, interiorVecNorm
          (fun i : Fin N => MvPolynomial.coeff (Finsupp.single j 1) (H i)) := hcoeff
    _ ≤ ∑ _j : Fin 3, sSup S := by
      exact Finset.sum_le_sum (fun j _ => hunit_le j)
    _ = 3 * sSup S := by
      simp


/-- Uniform degree-two coefficient/spherical-sup estimate with a deliberately slack constant. -/
theorem coeff_norm_from_spherical_sup_norm_degree_two_uniform
    {N : ℕ} (H : Fin N → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ i, homogeneousPart3 2 (H i) = H i) :
    motzkinVecCoeffNorm H ≤
      1000 * sSup { y : ℝ |
        ∃ v : Fin 3 → ℝ, motzkinSqNorm v = 1 ∧
          y = interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) } := by
  let S : Set ℝ := { y : ℝ |
    ∃ v : Fin 3 → ℝ, motzkinSqNorm v = 1 ∧
      y = interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) }
  have hbdd : BddAbove S := by
    refine ⟨motzkinVecCoeffNorm H, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    exact interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one H hv
  have hsup_nonneg : 0 ≤ sSup S := by
    have hmem : interiorVecNorm (fun i : Fin N => MvPolynomial.eval (unit3 0) (H i)) ∈ S :=
      ⟨unit3 0, motzkinSqNorm_unit3 0, rfl⟩
    exact (interiorVecNorm_nonneg _).trans (le_csSup hbdd hmem)
  have hcoeff := motzkinVecCoeffNorm_quadratic_le_ordered_sum_coeff_vectors H hhom
  have hdiag_le : ∀ j : Fin 3,
      interiorVecNorm (fun i : Fin N => MvPolynomial.coeff (Finsupp.single j 2) (H i)) ≤
        sSup S := by
    intro j
    have hmem : interiorVecNorm (fun i : Fin N => MvPolynomial.eval (unit3 j) (H i)) ∈ S :=
      ⟨unit3 j, motzkinSqNorm_unit3 j, rfl⟩
    calc
      interiorVecNorm (fun i : Fin N => MvPolynomial.coeff (Finsupp.single j 2) (H i)) =
          interiorVecNorm (fun i : Fin N => MvPolynomial.eval (unit3 j) (H i)) := by
            congr 1
            funext i
            exact (eval_unit_quadratic_eq_coeff_single_two (hhom i) j).symm
      _ ≤ sSup S := le_csSup hbdd hmem
  have hpair_eval_le : ∀ i j : Fin 3, i ≠ j →
      interiorVecNorm (fun n : Fin N => MvPolynomial.eval (pair4 i j) (H n)) ≤
        2 * sSup S := by
    intro i j hij
    let c : ℝ := (Real.sqrt 2)⁻¹
    let v : Fin 3 → ℝ := fun k => c * pair4 i j k
    have hv : motzkinSqNorm v = 1 := by
      dsimp [v, c]
      rw [motzkinSqNorm_smul, motzkinSqNorm_pair4_of_ne hij]
      have hsqrt_ne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hmem : interiorVecNorm (fun n : Fin N => MvPolynomial.eval v (H n)) ∈ S :=
      ⟨v, hv, rfl⟩
    have hscale : interiorVecNorm (fun n : Fin N => MvPolynomial.eval v (H n)) =
        c ^ 2 * interiorVecNorm (fun n : Fin N => MvPolynomial.eval (pair4 i j) (H n)) := by
      have heq : (fun n : Fin N => MvPolynomial.eval v (H n)) =
          fun n : Fin N => c ^ 2 * MvPolynomial.eval (pair4 i j) (H n) := by
        funext n
        have hscale_eval := isHomogeneous_eval_smul
          (isHomogeneous_of_homogeneousPart3_eq (hhom n)) c (pair4 i j)
        change MvPolynomial.eval (fun k => c * pair4 i j k) (H n) =
          c ^ 2 * MvPolynomial.eval (pair4 i j) (H n)
        exact hscale_eval
      rw [heq]
      change vecNorm (fun n : Fin N => c ^ 2 * MvPolynomial.eval (pair4 i j) (H n)) =
        c ^ 2 * vecNorm (fun n : Fin N => MvPolynomial.eval (pair4 i j) (H n))
      exact vecNorm_smul_nonneg (c ^ 2) (sq_nonneg c)
        (fun n : Fin N => MvPolynomial.eval (pair4 i j) (H n))
    have hc2 : c ^ 2 = (2 : ℝ)⁻¹ := by
      dsimp [c]
      rw [inv_pow]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hle := le_csSup hbdd hmem
    rw [hscale, hc2] at hle
    have hnorm_nonneg :
        0 ≤ interiorVecNorm (fun n : Fin N => MvPolynomial.eval (pair4 i j) (H n)) :=
      interiorVecNorm_nonneg _
    nlinarith
  have hordered_le : ∀ ij : Fin 3 × Fin 3,
      interiorVecNorm
        (fun i : Fin N =>
          MvPolynomial.coeff (Finsupp.single ij.1 1 + Finsupp.single ij.2 1) (H i)) ≤
        4 * sSup S := by
    intro ij
    rcases ij with ⟨a, b⟩
    by_cases hij : a = b
    · subst b
      calc
        interiorVecNorm
            (fun i : Fin N => MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single a 1) (H i)) =
            interiorVecNorm (fun i : Fin N => MvPolynomial.coeff (Finsupp.single a 2) (H i)) := by
              congr 1
              funext i
              rw [single_one_add_self]
        _ ≤ sSup S := hdiag_le a
        _ ≤ 4 * sSup S := by nlinarith
    · have hcoeff_eq :
        (fun n : Fin N =>
          MvPolynomial.coeff (Finsupp.single a 1 + Finsupp.single b 1) (H n)) =
        fun n : Fin N =>
          MvPolynomial.eval (pair4 a b) (H n) -
            MvPolynomial.coeff (Finsupp.single a 2) (H n) -
            MvPolynomial.coeff (Finsupp.single b 2) (H n) := by
        funext n
        have h := eval_pair_quadratic_eq_coeffs (hhom n) hij
        linarith
      rw [hcoeff_eq]
      calc
        interiorVecNorm
            (fun n : Fin N =>
              MvPolynomial.eval (pair4 a b) (H n) -
                MvPolynomial.coeff (Finsupp.single a 2) (H n) -
                MvPolynomial.coeff (Finsupp.single b 2) (H n)) ≤
            interiorVecNorm (fun n : Fin N =>
              MvPolynomial.eval (pair4 a b) (H n) -
                MvPolynomial.coeff (Finsupp.single a 2) (H n)) +
            interiorVecNorm (fun n : Fin N =>
              MvPolynomial.coeff (Finsupp.single b 2) (H n)) := by
              simpa [sub_eq_add_neg] using interiorVecNorm_sub_le
                (fun n : Fin N =>
                  MvPolynomial.eval (pair4 a b) (H n) -
                    MvPolynomial.coeff (Finsupp.single a 2) (H n))
                (fun n : Fin N => MvPolynomial.coeff (Finsupp.single b 2) (H n))
        _ ≤ (interiorVecNorm (fun n : Fin N => MvPolynomial.eval (pair4 a b) (H n)) +
              interiorVecNorm (fun n : Fin N =>
                MvPolynomial.coeff (Finsupp.single a 2) (H n))) +
            interiorVecNorm (fun n : Fin N =>
              MvPolynomial.coeff (Finsupp.single b 2) (H n)) := by
              gcongr
              simpa [sub_eq_add_neg] using interiorVecNorm_sub_le
                (fun n : Fin N => MvPolynomial.eval (pair4 a b) (H n))
                (fun n : Fin N => MvPolynomial.coeff (Finsupp.single a 2) (H n))
        _ ≤ 4 * sSup S := by
              have hp := hpair_eval_le a b hij
              have hdi := hdiag_le a
              have hdj := hdiag_le b
              nlinarith
  calc
    motzkinVecCoeffNorm H ≤ ∑ ij : Fin 3 × Fin 3, interiorVecNorm
        (fun i : Fin N =>
          MvPolynomial.coeff (Finsupp.single ij.1 1 + Finsupp.single ij.2 1) (H i)) :=
      hcoeff
    _ ≤ ∑ _ij : Fin 3 × Fin 3, 4 * sSup S := by
      exact Finset.sum_le_sum (fun ij _ => hordered_le ij)
    _ = 36 * sSup S := by
      simp
      ring
    _ ≤ 1000 * sSup S := by
      nlinarith


/-- Finite-dimensional norm equivalence from spherical sup norm to coefficient norm.

The statement applies to homogeneous vector-valued forms. -/
theorem coeff_norm_from_spherical_sup_norm
    {N m : ℕ} (H : Fin N → MvPolynomial (Fin 3) ℝ)
    (hhom : ∀ i, homogeneousPart3 m (H i) = H i) :
    ∃ L : ℝ, 0 < L ∧
      motzkinVecCoeffNorm H ≤
        L * sSup { y : ℝ |
          ∃ v : Fin 3 → ℝ, motzkinSqNorm v = 1 ∧
            y = interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) } := by
  let S : Set ℝ := { y : ℝ |
    ∃ v : Fin 3 → ℝ, motzkinSqNorm v = 1 ∧
      y = interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H i)) }
  have hbdd : BddAbove S := by
    refine ⟨motzkinVecCoeffNorm H, ?_⟩
    rintro y ⟨v, hv, rfl⟩
    exact interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one H hv
  have hsup_nonneg : 0 ≤ sSup S := by
    let e : Fin 3 → ℝ := fun i => if i = 0 then 1 else 0
    have he : motzkinSqNorm e = 1 := by
      simp [e, motzkinSqNorm]
    have hy_mem : interiorVecNorm (fun i : Fin N => MvPolynomial.eval e (H i)) ∈ S := by
      exact ⟨e, he, rfl⟩
    exact (interiorVecNorm_nonneg _).trans (le_csSup hbdd hy_mem)
  by_cases hcoeff0 : motzkinVecCoeffNorm H = 0
  · refine ⟨1, by norm_num, ?_⟩
    rw [hcoeff0]
    simpa using hsup_nonneg
  · have hcoeff_pos : 0 < motzkinVecCoeffNorm H :=
      lt_of_le_of_ne (motzkinVecCoeffNorm_nonneg H) (Ne.symm hcoeff0)
    have hsup_pos : 0 < sSup S := by
      by_contra hnot
      have hsup_nonpos : sSup S ≤ 0 := le_of_not_gt hnot
      have hpoly_zero : ∀ i, H i = 0 := by
        intro i
        apply MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero
        · exact isHomogeneous_of_homogeneousPart3_eq (hhom i)
        · intro x
          apply eval_eq_zero_of_unit_eq_zero (isHomogeneous_of_homogeneousPart3_eq (hhom i))
          intro v hv
          have hy_mem :
              interiorVecNorm (fun j : Fin N => MvPolynomial.eval v (H j)) ∈ S := by
            exact ⟨v, hv, rfl⟩
          have hnorm_le_zero :
              interiorVecNorm (fun j : Fin N => MvPolynomial.eval v (H j)) ≤ 0 :=
            (le_csSup hbdd hy_mem).trans hsup_nonpos
          exact component_eq_zero_of_interiorVecNorm_le_zero hnorm_le_zero i
      have hcoeff_zero' : motzkinVecCoeffNorm H = 0 := by
        simp [motzkinVecCoeffNorm, motzkinCoeffNorm, hpoly_zero]
      exact (ne_of_gt hcoeff_pos) hcoeff_zero'
    refine ⟨(motzkinVecCoeffNorm H + 1) / sSup S, div_pos ?_ hsup_pos, ?_⟩
    · nlinarith
    · field_simp [ne_of_gt hsup_pos]
      nlinarith


lemma homogeneousPart3_six_mul (p q : MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 6 (p * q) =
      homogeneousPart3 0 p * homogeneousPart3 6 q +
      homogeneousPart3 1 p * homogeneousPart3 5 q +
      homogeneousPart3 2 p * homogeneousPart3 4 q +
      homogeneousPart3 3 p * homogeneousPart3 3 q +
      homogeneousPart3 4 p * homogeneousPart3 2 q +
      homogeneousPart3 5 p * homogeneousPart3 1 q +
      homogeneousPart3 6 p * homogeneousPart3 0 q := by
  ext α
  rw [coeff_homogeneousPart3]
  by_cases hα : α.sum (fun _ e => e) = 6
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    symm
    repeat' rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    have hsum : x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) = 6 := by
      have hadd : x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) =
          α.sum (fun _ e => e) := by
        rw [Finset.mem_antidiagonal] at hx
        rw [← hx]
        simp [Finsupp.sum_add_index]
      simpa [hα] using hadd
    have hle : x.1.sum (fun _ e => e) ≤ 6 := by omega
    interval_cases h1 : x.1.sum (fun _ e => e)
    · have h2 : x.2.sum (fun _ e => e) = 6 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 5 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 4 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 3 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 2 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 1 := by omega
      simp [h2]
    · have h2 : x.2.sum (fun _ e => e) = 0 := by omega
      simp [h2]
  · simp only [hα, coeff_homogeneousPart3, ↓reduceIte, MvPolynomial.coeff_add,
      MvPolynomial.coeff_mul]
    repeat' rw [← Finset.sum_add_distrib]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    have hsum : x.1.sum (fun _ e => e) + x.2.sum (fun _ e => e) =
        α.sum (fun _ e => e) := by
      rw [Finset.mem_antidiagonal] at hx
      rw [← hx]
      simp [Finsupp.sum_add_index]
    by_cases h0 : x.2.sum (fun _ e => e) = 6
    · have : x.1.sum (fun _ e => e) ≠ 0 := by omega
      simp [h0, this]
    · by_cases h1 : x.2.sum (fun _ e => e) = 5
      · have : x.1.sum (fun _ e => e) ≠ 1 := by omega
        simp [h1, this]
      · by_cases h2 : x.2.sum (fun _ e => e) = 4
        · have : x.1.sum (fun _ e => e) ≠ 2 := by omega
          simp [h2, this]
        · by_cases h3 : x.2.sum (fun _ e => e) = 3
          · have : x.1.sum (fun _ e => e) ≠ 3 := by omega
            simp [h3, this]
          · by_cases h4 : x.2.sum (fun _ e => e) = 2
            · have : x.1.sum (fun _ e => e) ≠ 4 := by omega
              simp [h4, this]
            · by_cases h5 : x.2.sum (fun _ e => e) = 1
              · have : x.1.sum (fun _ e => e) ≠ 5 := by omega
                simp [h5, this]
              · by_cases h6 : x.2.sum (fun _ e => e) = 0
                · have : x.1.sum (fun _ e => e) ≠ 6 := by omega
                  simp [h6, this]
                · simp [h0, h1, h2, h3, h4, h5, h6]

lemma homogeneousPart3_sosVectorSq3_six {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 6 (sosVectorSq3 Q) =
      ∑ i : Fin N,
        (homogeneousPart3 0 (Q i) * homogeneousPart3 6 (Q i) +
          homogeneousPart3 1 (Q i) * homogeneousPart3 5 (Q i) +
          homogeneousPart3 2 (Q i) * homogeneousPart3 4 (Q i) +
          homogeneousPart3 3 (Q i) * homogeneousPart3 3 (Q i) +
          homogeneousPart3 4 (Q i) * homogeneousPart3 2 (Q i) +
          homogeneousPart3 5 (Q i) * homogeneousPart3 1 (Q i) +
          homogeneousPart3 6 (Q i) * homogeneousPart3 0 (Q i)) := by
  unfold sosVectorSq3
  rw [homogeneousPart3_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simpa [pow_two] using homogeneousPart3_six_mul (Q i) (Q i)


end Motzkin

end OptimalConvergenceRates

end
