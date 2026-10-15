/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/WeightedJet/DirectionalDerivatives.lean

  Linear and low-order directional-derivative estimates for weighted jets.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.SOSJets
import OptimalConvergenceRates.BasicNotions.SOSVector
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityCorollaries
import OptimalConvergenceRates.MarkovInequality.ChebyshevEndpoint
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

open MvPolynomial Finset
open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates

lemma vecCoeffNorm4_homogeneousPartVec4_zero {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 4) ℝ) :
    vecCoeffNorm4 (homogeneousPartVec4 0 Q) =
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval 0 (Q i)) := by
  unfold vecCoeffNorm4 interiorVecNorm interiorVecSqNorm homogeneousPartVec4
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [coeffNorm4_homogeneousPart4_zero]
  exact sq_abs _

lemma homogeneousPart4_idem (m : ℕ) (p : MvPolynomial (Fin 4) ℝ) :
    homogeneousPart4 m (homogeneousPart4 m p) = homogeneousPart4 m p := by
  rw [homogeneousPart4_eq_homogeneousComponent]
  rw [MvPolynomial.homogeneousComponent_of_mem (m := m) (n := m)]
  · simp
  · rw [homogeneousPart4_eq_homogeneousComponent]
    exact MvPolynomial.homogeneousComponent_mem m p

lemma weightedJetLemma_constant_bound
    {N : ℕ} {epsilon A : ℝ}
    (_heps : 0 < epsilon)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon) :
    vecCoeffNorm4 (homogeneousPartVec4 0 Q) ≤ jetErrorConst * A * Real.sqrt epsilon := by
  rw [vecCoeffNorm4_homogeneousPartVec4_zero]
  have hline := hzeroLines 0 0 (by simpa using schmInteriorS_pos.le)
  have hzero_eval :
      (fun i : Fin N =>
        MvPolynomial.eval (fun j => (0 : ℝ) * choiLamZeroDirection 0 j) (Q i)) =
        fun i : Fin N => MvPolynomial.eval 0 (Q i) := by
    funext i
    congr
    funext j
    simp
  rw [hzero_eval] at hline
  have hjet : (1 : ℝ) ≤ jetErrorConst := by
    unfold jetErrorConst
    norm_num
  calc
    interiorVecNorm (fun i : Fin N => MvPolynomial.eval 0 (Q i))
        ≤ A * Real.sqrt epsilon := hline
    _ = 1 * (A * Real.sqrt epsilon) := by ring
    _ ≤ jetErrorConst * (A * Real.sqrt epsilon) := by
      exact mul_le_mul_of_nonneg_right hjet
        (mul_nonneg (le_trans zero_le_one hA) (Real.sqrt_nonneg epsilon))
    _ = jetErrorConst * A * Real.sqrt epsilon := by ring


lemma finsupp_coord_le_sum_linear (a : Fin 4 →₀ ℕ) (j : Fin 4) :
    a j ≤ a.sum (fun _ e => e) := by
  by_cases hj : a j = 0
  · simp [hj]
  · have hmem : j ∈ a.support := by
      rw [Finsupp.mem_support_iff]
      exact hj
    calc
      a j = ∑ x ∈ ({j} : Finset (Fin 4)), a x := by simp
      _ ≤ ∑ x ∈ a.support, a x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          have hxj : x = j := by simpa using hx
          subst x
          exact hmem
        · intro x _hx _hnot
          exact Nat.zero_le _
      _ = a.sum (fun _ e => e) := rfl

lemma finsupp_sum_fintype4_linear (a : Fin 4 →₀ ℕ) :
    a.sum (fun _ e => e) = ∑ i : Fin 4, a i := by
  rw [Finsupp.sum_fintype]
  intro i
  rfl

lemma finsupp_degree_one_cases_linear {a : Fin 4 →₀ ℕ}
    (ha : a.sum (fun _ e => e) = 1) :
    ∃ j : Fin 4, a = Finsupp.single j 1 := by
  have h0le : a 0 ≤ 1 := by simpa [ha] using finsupp_coord_le_sum_linear a 0
  interval_cases h0 : a 0
  · have h1le : a 1 ≤ 1 := by simpa [ha] using finsupp_coord_le_sum_linear a 1
    interval_cases h1 : a 1
    · have h2le : a 2 ≤ 1 := by simpa [ha] using finsupp_coord_le_sum_linear a 2
      interval_cases h2 : a 2
      · refine ⟨3, ?_⟩
        ext j
        fin_cases j <;> simp [h0, h1, h2]
        rw [finsupp_sum_fintype4_linear] at ha
        simp [Fin.sum_univ_four, h0, h1, h2] at ha
        omega
      · refine ⟨2, ?_⟩
        ext j
        fin_cases j <;> simp [h0, h1, h2]
        rw [finsupp_sum_fintype4_linear] at ha
        simp [Fin.sum_univ_four, h0, h1, h2] at ha
        omega
    · refine ⟨1, ?_⟩
      ext j
      fin_cases j <;> simp [h0, h1]
      all_goals
        rw [finsupp_sum_fintype4_linear] at ha
        simp [Fin.sum_univ_four, h0, h1] at ha
        omega
  · refine ⟨0, ?_⟩
    ext j
    fin_cases j <;> simp [h0]
    all_goals
      rw [finsupp_sum_fintype4_linear] at ha
      simp [Fin.sum_univ_four, h0] at ha
      omega

lemma single_one_injective_linear :
    Function.Injective (fun j : Fin 4 => Finsupp.single j 1) := by
  intro i j hij
  by_contra hne
  have hi := Finsupp.ext_iff.mp hij i
  simp [hne] at hi

lemma coeffNorm4_linear_le_sum_coeff {p : MvPolynomial (Fin 4) ℝ}
    (hp : homogeneousPart4 1 p = p) :
    coeffNorm4 p ≤ ∑ j : Fin 4, |legacyMvCoeff (Finsupp.single j 1) p| := by
  unfold coeffNorm4
  have hsubset : p.support ⊆ (Finset.univ.image fun j : Fin 4 => Finsupp.single j 1) := by
    intro a ha
    have hhom := isHomogeneous_of_homogeneousPart4_eq hp
    have hweight := hhom (MvPolynomial.mem_support_iff.mp ha)
    have hsum : a.sum (fun _ e => e) = 1 := by
      have hdeg : Finsupp.degree a = 1 := by
        rw [Finsupp.degree_eq_weight_one]
        exact hweight
      rw [finsupp_sum_fintype4_linear]
      simpa only [Finsupp.degree_eq_sum] using hdeg
    obtain ⟨j, rfl⟩ := finsupp_degree_one_cases_linear hsum
    simp
  calc
    ∑ α ∈ p.support, |legacyMvCoeff α p|
        ≤ ∑ α ∈ (Finset.univ.image fun j : Fin 4 => Finsupp.single j 1),
            |legacyMvCoeff α p| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro x _hx _hnot
          exact abs_nonneg _
    _ = ∑ j : Fin 4, |legacyMvCoeff (Finsupp.single j 1) p| := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij => single_one_injective_linear hij


lemma linear_eq_sum_monomial {p : MvPolynomial (Fin 4) ℝ}
    (hp : homogeneousPart4 1 p = p) :
    p = ∑ j : Fin 4, MvPolynomial.monomial (Finsupp.single j 1)
      (legacyMvCoeff (Finsupp.single j 1) p) := by
  ext α
  rw [MvPolynomial.coeff_sum]
  by_cases hα : α ∈ p.support
  · have hhom := isHomogeneous_of_homogeneousPart4_eq hp
    have hweight := hhom (MvPolynomial.mem_support_iff.mp hα)
    have hsum : α.sum (fun _ e => e) = 1 := by
      have hdeg : Finsupp.degree α = 1 := by
        rw [Finsupp.degree_eq_weight_one]
        exact hweight
      rw [finsupp_sum_fintype4_linear]
      simpa only [Finsupp.degree_eq_sum] using hdeg
    obtain ⟨j, rfl⟩ := finsupp_degree_one_cases_linear hsum
    rw [Finset.sum_eq_single j]
    · simp [MvPolynomial.coeff_monomial]
    · intro k _ hk
      have hne : Finsupp.single k 1 ≠ Finsupp.single j 1 := by
        intro h
        exact hk (single_one_injective_linear h)
      simp [MvPolynomial.coeff_monomial, hne]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · have hcoeff : legacyMvCoeff α p = 0 := by
      by_contra hc
      exact hα (MvPolynomial.mem_support_iff.mpr hc)
    rw [hcoeff]
    symm
    apply Finset.sum_eq_zero
    intro j _
    by_cases hαj : Finsupp.single j 1 = α
    · rw [← hαj]
      have hcoeffj : legacyMvCoeff (Finsupp.single j 1) p = 0 := by
        by_contra hc
        exact hα (by simpa [hαj] using MvPolynomial.mem_support_iff.mpr hc)
      simp [hcoeffj]
    · simp [MvPolynomial.coeff_monomial, hαj]

lemma eval_linear_eq_sum_coeff {p : MvPolynomial (Fin 4) ℝ}
    (hp : homogeneousPart4 1 p = p) (x : Fin 4 → ℝ) :
    MvPolynomial.eval x p = ∑ j : Fin 4, legacyMvCoeff (Finsupp.single j 1) p * x j := by
  calc
    MvPolynomial.eval x p =
        MvPolynomial.eval x (∑ j : Fin 4, MvPolynomial.monomial (Finsupp.single j 1)
          (legacyMvCoeff (Finsupp.single j 1) p)) := by
          exact congrArg (MvPolynomial.eval x) (linear_eq_sum_monomial hp)
    _ = ∑ j : Fin 4, legacyMvCoeff (Finsupp.single j 1) p * x j := by
      simp [MvPolynomial.eval_monomial]


lemma linear_coeff_eq_choiLam_basis_sum {p : MvPolynomial (Fin 4) ℝ}
    (hp : homogeneousPart4 1 p = p) (j : Fin 4) :
    legacyMvCoeff (Finsupp.single j 1) p =
      ∑ z : Fin 4, MvPolynomial.eval (choiLamZeroDirection z) p * choiLamZeroDirection z j := by
  have h0 := eval_linear_eq_sum_coeff hp (choiLamZeroDirection 0)
  have h1 := eval_linear_eq_sum_coeff hp (choiLamZeroDirection 1)
  have h2 := eval_linear_eq_sum_coeff hp (choiLamZeroDirection 2)
  have h3 := eval_linear_eq_sum_coeff hp (choiLamZeroDirection 3)
  fin_cases j <;>
    simp [choiLamZeroDirection, choiLamZeroDirection0, choiLamZeroDirection1,
      choiLamZeroDirection2, choiLamZeroDirection3, Fin.sum_univ_four] at h0 h1 h2 h3 ⊢ <;>
    linarith


lemma interiorVecNorm_sum_abs_le_sum_norm {N : ℕ} (V : Fin 4 → Fin N → ℝ) :
    interiorVecNorm (fun i => ∑ z : Fin 4, |V z i|) ≤
      ∑ z : Fin 4, interiorVecNorm (V z) := by
  calc
    interiorVecNorm (fun i => ∑ z : Fin 4, |V z i|)
        ≤ ∑ z : Fin 4, interiorVecNorm (fun i => |V z i|) := by
          simpa using interiorVecNorm_finset_sum_le_sum_norm
            (Finset.univ : Finset (Fin 4)) (fun z i => |V z i|)
    _ = ∑ z : Fin 4, interiorVecNorm (V z) := by
      apply Finset.sum_congr rfl
      intro z _
      exact interiorVecNorm_abs (V z)



lemma choiLamZeroDirection_abs_sum (z : Fin 4) :
    ∑ j : Fin 4, |choiLamZeroDirection z j| = 2 := by
  fin_cases z <;>
    simp [choiLamZeroDirection, choiLamZeroDirection0, choiLamZeroDirection1,
      choiLamZeroDirection2, choiLamZeroDirection3, Fin.sum_univ_four] <;>
    norm_num

lemma coeffNorm4_linear_le_two_sum_abs_basis_eval {p : MvPolynomial (Fin 4) ℝ}
    (hp : homogeneousPart4 1 p = p) :
    coeffNorm4 p ≤ 2 * ∑ z : Fin 4, |MvPolynomial.eval (choiLamZeroDirection z) p| := by
  calc
    coeffNorm4 p ≤ ∑ j : Fin 4, |legacyMvCoeff (Finsupp.single j 1) p| :=
      coeffNorm4_linear_le_sum_coeff hp
    _ = ∑ j : Fin 4,
        |∑ z : Fin 4, MvPolynomial.eval (choiLamZeroDirection z) p *
          choiLamZeroDirection z j| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [linear_coeff_eq_choiLam_basis_sum hp j]
    _ ≤ ∑ j : Fin 4, ∑ z : Fin 4,
        |MvPolynomial.eval (choiLamZeroDirection z) p * choiLamZeroDirection z j| := by
          apply Finset.sum_le_sum
          intro j _
          exact Finset.abs_sum_le_sum_abs _ _
    _ = 2 * ∑ z : Fin 4, |MvPolynomial.eval (choiLamZeroDirection z) p| := by
      rw [Finset.sum_comm]
      calc
        ∑ x : Fin 4, ∑ x_1 : Fin 4,
            |MvPolynomial.eval (choiLamZeroDirection x) p * choiLamZeroDirection x x_1|
            = ∑ z : Fin 4,
                |MvPolynomial.eval (choiLamZeroDirection z) p| *
                  ∑ j : Fin 4, |choiLamZeroDirection z j| := by
              apply Finset.sum_congr rfl
              intro z _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_mul]
        _ = ∑ z : Fin 4, |MvPolynomial.eval (choiLamZeroDirection z) p| * 2 := by
          apply Finset.sum_congr rfl
          intro z _
          rw [choiLamZeroDirection_abs_sum]
        _ = 2 * ∑ z : Fin 4, |MvPolynomial.eval (choiLamZeroDirection z) p| := by
          rw [← Finset.sum_mul]
          ring


/-- Finite-dimensional conversion from bounds on the orthonormal Choi-Lam basis
into the componentwise `L^1` coefficient norm used in this development.

The constant is deliberately coarse: coefficient inversion gives a factor `2`,
and the triangle inequality over the four basis directions gives another factor
`4`. -/
theorem linear_coeff_bound_from_choiLam_basis
    {N : ℕ} {B : ℝ} (H : Fin N → MvPolynomial (Fin 4) ℝ)
    (hhom : ∀ i, homogeneousPart4 1 (H i) = H i)
    (_hB : 0 ≤ B)
    (hbasis : ∀ zi : Fin 4,
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval (choiLamZeroDirection zi) (H i))
        ≤ B) :
    vecCoeffNorm4 H ≤ 8 * B := by
  let V : Fin 4 → Fin N → ℝ :=
    fun z i => MvPolynomial.eval (choiLamZeroDirection z) (H i)
  have hpoint : ∀ i : Fin N, coeffNorm4 (H i) ≤ 2 * ∑ z : Fin 4, |V z i| := by
    intro i
    simpa [V] using coeffNorm4_linear_le_two_sum_abs_basis_eval (hhom i)
  have hnorm : vecCoeffNorm4 H ≤ interiorVecNorm (fun i : Fin N => 2 * ∑ z : Fin 4, |V z i|) := by
    unfold vecCoeffNorm4 interiorVecNorm interiorVecSqNorm
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    rw [sq_le_sq]
    rw [abs_of_nonneg (coeffNorm4_nonneg (H i))]
    rw [abs_of_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
      (Finset.sum_nonneg fun z _ => abs_nonneg (V z i)))]
    exact hpoint i
  have hscale :
      interiorVecNorm (fun i : Fin N => 2 * ∑ z : Fin 4, |V z i|) =
        2 * interiorVecNorm (fun i : Fin N => ∑ z : Fin 4, |V z i|) := by
    simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
      vecNorm_smul_nonneg (N := N) (c := 2) (by norm_num : 0 ≤ (2 : ℝ))
        (fun i : Fin N => ∑ z : Fin 4, |V z i|)
  have htri :
      interiorVecNorm (fun i : Fin N => ∑ z : Fin 4, |V z i|) ≤
        ∑ z : Fin 4, interiorVecNorm (V z) :=
    interiorVecNorm_sum_abs_le_sum_norm V
  have hsumB : ∑ z : Fin 4, interiorVecNorm (V z) ≤ ∑ _z : Fin 4, B := by
    apply Finset.sum_le_sum
    intro z _
    simpa [V] using hbasis z
  calc
    vecCoeffNorm4 H ≤ interiorVecNorm (fun i : Fin N => 2 * ∑ z : Fin 4, |V z i|) := hnorm
    _ = 2 * interiorVecNorm (fun i : Fin N => ∑ z : Fin 4, |V z i|) := hscale
    _ ≤ 2 * (∑ z : Fin 4, interiorVecNorm (V z)) := by nlinarith
    _ ≤ 2 * (∑ _z : Fin 4, B) := by nlinarith
    _ = 8 * B := by simp; ring

theorem directionalDeriv_zero_eq_sum_linear_coeff
    (p : MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ) :
    directionalDeriv p 0 z =
      ∑ j : Fin 4, legacyMvCoeff (Finsupp.single j 1) p * z j := by
  unfold directionalDeriv univariateRestriction
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.aeval_C, Polynomial.algebraMap_eq, Polynomial.derivative_C,
        Polynomial.eval_zero, MvPolynomial.coeff_C]
      symm
      apply Finset.sum_eq_zero
      intro j _
      have h : (0 : Fin 4 →₀ ℕ) ≠ Finsupp.single j 1 := by
        intro h
        have := congrArg (fun f : Fin 4 →₀ ℕ => f j) h
        simp at this
      simp [h]
  | add p q ihp ihq =>
      simp only [map_add, Polynomial.eval_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      rw [ihp, ihq, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
  | mul_X p j _ihp =>
      simp only [map_mul, MvPolynomial.aeval_X]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_X, zero_mul, zero_add, mul_one]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        mul_zero, add_zero]
      have heval0 :
          Polynomial.eval 0
              ((MvPolynomial.aeval fun i =>
                Polynomial.C ((0 : Fin 4 → ℝ) i) + Polynomial.C (z i) * Polynomial.X) p) =
            legacyMvCoeff 0 p := by
        change (univariateRestriction p (0 : Fin 4 → ℝ) z).eval 0 =
          legacyMvCoeff 0 p
        rw [univariateRestriction_eval]
        have hcoeff : MvPolynomial.eval (0 : Fin 4 → ℝ) p = legacyMvCoeff 0 p := by
          rw [MvPolynomial.eval_zero]
          rw [MvPolynomial.constantCoeff_eq p]
        simpa using hcoeff
      rw [heval0]
      rw [Finset.sum_eq_single j]
      · simp [MvPolynomial.coeff_mul_X']
      · intro b _ hb
        have hjb : j ≠ b := Ne.symm hb
        have hnot : j ∉ (Finsupp.single b 1).support := by
          simp [hjb]
        simp [MvPolynomial.coeff_mul_X', hnot, hjb]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim

lemma coeff_homogeneousPart4_one_single
    (p : MvPolynomial (Fin 4) ℝ) (j : Fin 4) :
    legacyMvCoeff (Finsupp.single j 1) (homogeneousPart4 1 p) =
      legacyMvCoeff (Finsupp.single j 1) p := by
  by_cases hcoeff : legacyMvCoeff (Finsupp.single j 1) p = 0
  · rw [hcoeff]
    unfold homogeneousPart4
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro α hα
    rw [MvPolynomial.coeff_monomial]
    by_cases hαj : α = Finsupp.single j 1
    · subst α
      simp [hcoeff]
    · simp [hαj]
  · unfold homogeneousPart4
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single (Finsupp.single j 1)]
    · simp [MvPolynomial.coeff_monomial]
    · intro α _hα hne
      rw [MvPolynomial.coeff_monomial]
      have hne' : α ≠ Finsupp.single j 1 := hne
      simp [hne']
    · intro hnot
      exfalso
      apply hnot
      rw [Finset.mem_filter]
      constructor
      · exact MvPolynomial.mem_support_iff.mpr hcoeff
      · simp

theorem directionalDeriv_zero_eq_eval_homogeneousPart_one
    (p : MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ) :
    directionalDeriv p 0 z = MvPolynomial.eval z (homogeneousPart4 1 p) := by
  rw [directionalDeriv_zero_eq_sum_linear_coeff]
  rw [eval_linear_eq_sum_coeff (homogeneousPart4_idem 1 p)]
  apply Finset.sum_congr rfl
  intro j _
  rw [coeff_homogeneousPart4_one_single]


lemma sum_sub_single_one_zero (α : Fin 4 →₀ ℕ) (hj : (0 : Fin 4) ∈ α.support) :
    (α - Finsupp.single (0 : Fin 4) 1).sum (fun _ e => e) =
      α.sum (fun _ e => e) - 1 := by
  rw [Finsupp.sum_fintype]
  · rw [Finsupp.sum_fintype]
    · have hjpos : 1 ≤ α 0 := by
        have hjne : α 0 ≠ 0 := Finsupp.mem_support_iff.mp hj
        omega
      simp [Fin.sum_univ_four]
      omega
    · intro i
      rfl
  · intro i
    rfl

lemma sum_sub_single_one_of_mem (α : Fin 4 →₀ ℕ) {j : Fin 4}
    (hj : j ∈ α.support) :
    (α - Finsupp.single j 1).sum (fun _ e => e) = α.sum (fun _ e => e) - 1 := by
  fin_cases j
  · exact sum_sub_single_one_zero α hj
  · rw [Finsupp.sum_fintype]
    · rw [Finsupp.sum_fintype]
      · have hjpos : 1 ≤ α 1 := by
          have hjne : α 1 ≠ 0 := Finsupp.mem_support_iff.mp hj
          omega
        simp [Fin.sum_univ_four]
        omega
      · intro i
        rfl
    · intro i
      rfl
  · rw [Finsupp.sum_fintype]
    · rw [Finsupp.sum_fintype]
      · have hjpos : 1 ≤ α 2 := by
          have hjne : α 2 ≠ 0 := Finsupp.mem_support_iff.mp hj
          omega
        simp [Fin.sum_univ_four]
        omega
      · intro i
        rfl
    · intro i
      rfl
  · rw [Finsupp.sum_fintype]
    · rw [Finsupp.sum_fintype]
      · have hjpos : 1 ≤ α 3 := by
          have hjne : α 3 ≠ 0 := Finsupp.mem_support_iff.mp hj
          omega
        simp [Fin.sum_univ_four]
        omega
      · intro i
        rfl
    · intro i
      rfl

lemma homogeneousPart4_succ_mul_X (m : ℕ) (p : MvPolynomial (Fin 4) ℝ) (j : Fin 4) :
    homogeneousPart4 (m + 1) (p * MvPolynomial.X j) =
      homogeneousPart4 m p * MvPolynomial.X j := by
  ext α
  rw [coeff_homogeneousPart4]
  rw [MvPolynomial.coeff_mul_X']
  rw [MvPolynomial.coeff_mul_X']
  by_cases hj : j ∈ α.support
  · simp [hj]
    have hsumsub := sum_sub_single_one_of_mem α hj
    have hsumpos : 1 ≤ α.sum (fun _ e => e) := by
      have hjpos : 1 ≤ α j := by
        have hjne : α j ≠ 0 := Finsupp.mem_support_iff.mp hj
        omega
      rw [Finsupp.sum_fintype]
      · exact hjpos.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
      · intro i
        rfl
    by_cases hdeg : α.sum (fun _ e => e) = m + 1
    · have hpred : (α - Finsupp.single j 1).sum (fun _ e => e) = m := by omega
      simp [hdeg, coeff_homogeneousPart4, hpred]
    · have hpred : ¬ (α - Finsupp.single j 1).sum (fun _ e => e) = m := by omega
      simp [hdeg, coeff_homogeneousPart4, hpred]
  · simp [hj]

lemma homogeneousPart4_two_mul_X (p : MvPolynomial (Fin 4) ℝ) (j : Fin 4) :
    homogeneousPart4 2 (p * MvPolynomial.X j) = homogeneousPart4 1 p * MvPolynomial.X j := by
  ext α
  rw [coeff_homogeneousPart4]
  rw [MvPolynomial.coeff_mul_X']
  rw [MvPolynomial.coeff_mul_X']
  by_cases hj : j ∈ α.support
  · simp [hj]
    have hsumsub := sum_sub_single_one_of_mem α hj
    by_cases hdeg : α.sum (fun _ e => e) = 2
    · have hpred : (α - Finsupp.single j 1).sum (fun _ e => e) = 1 := by omega
      simp [hdeg, coeff_homogeneousPart4, hpred]
    · have hpred : ¬ (α - Finsupp.single j 1).sum (fun _ e => e) = 1 := by omega
      simp [hdeg, coeff_homogeneousPart4, hpred]
  · simp [hj]

lemma univariateRestriction_mul_X_zero
    (p : MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ) (j : Fin 4) :
    univariateRestriction (p * MvPolynomial.X j) (0 : Fin 4 → ℝ) z =
      univariateRestriction p (0 : Fin 4 → ℝ) z * (Polynomial.C (z j) * Polynomial.X) := by
  unfold univariateRestriction
  simp

lemma polynomial_second_derivative_mul_CX_eval_zero (P : Polynomial ℝ) (a : ℝ) :
    (Polynomial.derivative (Polynomial.derivative (P * (Polynomial.C a * Polynomial.X)))).eval 0 =
      2 * a * (Polynomial.derivative P).eval 0 := by
  rw [Polynomial.derivative_mul]
  simp [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.eval_mul, Polynomial.eval_add]
  ring

lemma polynomial_iterate_derivative_eval_zero (P : Polynomial ℝ) (m : ℕ) :
    ((Polynomial.derivative^[m]) P).eval 0 = (Nat.factorial m : ℝ) * P.coeff m := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

lemma polynomial_coeff_mul_CX_succ (P : Polynomial ℝ) (a : ℝ) (m : ℕ) :
    (P * (Polynomial.C a * Polynomial.X)).coeff (m + 1) = a * P.coeff m := by
  rw [mul_comm (Polynomial.C a) Polynomial.X]
  rw [show P * (Polynomial.X * Polynomial.C a) = Polynomial.X * (Polynomial.C a * P) by ring]
  rw [Polynomial.coeff_X_mul]
  simp [mul_comm]

lemma polynomial_coeff_mul_CX_zero (P : Polynomial ℝ) (a : ℝ) :
    (P * (Polynomial.C a * Polynomial.X)).coeff 0 = 0 := by
  rw [mul_comm (Polynomial.C a) Polynomial.X]
  rw [show P * (Polynomial.X * Polynomial.C a) = Polynomial.X * (Polynomial.C a * P) by ring]
  simp

theorem coeff_univariateRestriction_zero_eq_eval_homogeneousPart
    (p : MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ) (m : ℕ) :
    (univariateRestriction p (0 : Fin 4 → ℝ) z).coeff m =
      MvPolynomial.eval z (homogeneousPart4 m p) := by
  induction p using MvPolynomial.induction_on generalizing m with
  | C a =>
      cases m with
      | zero =>
          have hC : homogeneousPart4 0 (MvPolynomial.C a : MvPolynomial (Fin 4) ℝ) =
              MvPolynomial.C a := by
            ext α
            rw [coeff_homogeneousPart4]
            by_cases hα : α = 0
            · subst α
              simp
            · have h0α : (0 : Fin 4 →₀ ℕ) ≠ α := fun h => hα h.symm
              simp [MvPolynomial.coeff_C, h0α]
          unfold univariateRestriction
          rw [hC]
          simp
      | succ m =>
          have hC : homogeneousPart4 (m + 1)
                (MvPolynomial.C a : MvPolynomial (Fin 4) ℝ) = 0 := by
            ext α
            rw [coeff_homogeneousPart4]
            by_cases hα : α = 0
            · subst α
              simp
            · have h0α : (0 : Fin 4 →₀ ℕ) ≠ α := fun h => hα h.symm
              simp [MvPolynomial.coeff_C, h0α]
          unfold univariateRestriction
          rw [hC]
          simp
  | add p q ihp ihq =>
      unfold univariateRestriction at ihp ihq ⊢
      rw [map_add, Polynomial.coeff_add, homogeneousPart4_add, MvPolynomial.eval_add]
      rw [ihp m, ihq m]
  | mul_X p j ihp =>
      cases m with
      | zero =>
          rw [univariateRestriction_mul_X_zero]
          rw [polynomial_coeff_mul_CX_zero]
          have hzero : homogeneousPart4 0 (p * MvPolynomial.X j) = 0 := by
            ext α
            rw [coeff_homogeneousPart4]
            rw [MvPolynomial.coeff_mul_X']
            by_cases hdeg : α.sum (fun _ e => e) = 0
            · have hnot : j ∉ α.support := by
                intro hj
                have hjpos : 1 ≤ α j := by
                  have hjne : α j ≠ 0 := Finsupp.mem_support_iff.mp hj
                  omega
                have hsumpos : 1 ≤ α.sum (fun _ e => e) := by
                  rw [Finsupp.sum_fintype]
                  · exact hjpos.trans
                      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
                  · intro i
                    rfl
                omega
              simp [hdeg, hnot]
            · simp [hdeg]
          rw [hzero]
          simp
      | succ m =>
          rw [univariateRestriction_mul_X_zero]
          rw [polynomial_coeff_mul_CX_succ]
          rw [homogeneousPart4_succ_mul_X]
          rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
          rw [ihp m]
          ring

theorem iterateDirectionalDeriv_zero_eq_eval_homogeneousPart
    (p : MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ) (m : ℕ) :
    ((Polynomial.derivative^[m]) (univariateRestriction p (0 : Fin 4 → ℝ) z)).eval 0 =
      (Nat.factorial m : ℝ) * MvPolynomial.eval z (homogeneousPart4 m p) := by
  rw [polynomial_iterate_derivative_eval_zero]
  rw [coeff_univariateRestriction_zero_eq_eval_homogeneousPart]

theorem polynomialTailDivX2_univariateRestriction_coeff_eq_eval_homogeneousPart
    (p : MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ) (n : ℕ) :
    (polynomialTailDivX2 (univariateRestriction p (0 : Fin 4 → ℝ) z)).coeff n =
      MvPolynomial.eval z (homogeneousPart4 (n + 2) p) := by
  rw [polynomialTailDivX2_coeff]
  exact coeff_univariateRestriction_zero_eq_eval_homogeneousPart p z (n + 2)

theorem iterateDerivative_tail_univariateRestriction_eval_zero_eq_homogeneousPart
    (p : MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ) (ell : ℕ) :
    ((Polynomial.derivative^[ell])
        (polynomialTailDivX2 (univariateRestriction p (0 : Fin 4 → ℝ) z))).eval 0 =
      (Nat.factorial ell : ℝ) * MvPolynomial.eval z (homogeneousPart4 (ell + 2) p) := by
  rw [polynomial_iterate_derivative_eval_zero]
  rw [polynomialTailDivX2_univariateRestriction_coeff_eq_eval_homogeneousPart]

theorem homogeneousPart_eval_norm_le_of_tail_derivative_norm_le
    {N ell : ℕ} {C : ℝ}
    (Q : Fin N → MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ)
    (hderiv : interiorVecNorm
        (fun i : Fin N =>
          ((Polynomial.derivative^[ell])
            (polynomialTailDivX2 (univariateRestriction (Q i) (0 : Fin 4 → ℝ) z))).eval 0) ≤ C) :
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval z (homogeneousPartVec4 (ell + 2) Q i)) ≤ C := by
  let V : Fin N → ℝ := fun i => MvPolynomial.eval z (homogeneousPartVec4 (ell + 2) Q i)
  have hderiv_eq :
      (fun i : Fin N =>
          ((Polynomial.derivative^[ell])
            (polynomialTailDivX2 (univariateRestriction (Q i) (0 : Fin 4 → ℝ) z))).eval 0) =
        fun i : Fin N => (Nat.factorial ell : ℝ) * V i := by
    funext i
    dsimp [V, homogeneousPartVec4]
    exact iterateDerivative_tail_univariateRestriction_eval_zero_eq_homogeneousPart (Q i) z ell
  have hscale : interiorVecNorm (fun i : Fin N => (Nat.factorial ell : ℝ) * V i) =
      (Nat.factorial ell : ℝ) * interiorVecNorm V := by
    simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
      vecNorm_smul_nonneg (N := N) (c := (Nat.factorial ell : ℝ))
        (by positivity : 0 ≤ (Nat.factorial ell : ℝ)) V
  have hfact : (1 : ℝ) ≤ (Nat.factorial ell : ℝ) := by
    exact_mod_cast Nat.factorial_pos ell
  have hVnon : 0 ≤ interiorVecNorm V := interiorVecNorm_nonneg V
  have hscaled : (Nat.factorial ell : ℝ) * interiorVecNorm V ≤ C := by
    simpa [hderiv_eq, hscale] using hderiv
  have hV_le_scaled : interiorVecNorm V ≤ (Nat.factorial ell : ℝ) * interiorVecNorm V := by
    calc
      interiorVecNorm V = 1 * interiorVecNorm V := by ring
      _ ≤ (Nat.factorial ell : ℝ) * interiorVecNorm V :=
        mul_le_mul_of_nonneg_right hfact hVnon
  exact hV_le_scaled.trans hscaled

theorem directionalDeriv2_zero_eq_eval_homogeneousPart_two
    (p : MvPolynomial (Fin 4) ℝ) (z : Fin 4 → ℝ) :
    directionalDeriv2 p 0 z = 2 * MvPolynomial.eval z (homogeneousPart4 2 p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hC : homogeneousPart4 2 (MvPolynomial.C a : MvPolynomial (Fin 4) ℝ) = 0 := by
        ext α
        rw [coeff_homogeneousPart4]
        by_cases hα : α = 0
        · subst α
          simp
        · have h0α : (0 : Fin 4 →₀ ℕ) ≠ α := fun h => hα h.symm
          simp [MvPolynomial.coeff_C, h0α]
      unfold directionalDeriv2 univariateRestriction
      rw [hC]
      simp
  | add p q ihp ihq =>
      unfold directionalDeriv2 at ihp ihq ⊢
      have hadd : univariateRestriction (p + q) (0 : Fin 4 → ℝ) z =
          univariateRestriction p (0 : Fin 4 → ℝ) z +
            univariateRestriction q (0 : Fin 4 → ℝ) z := by
        unfold univariateRestriction
        simp
      rw [hadd, Polynomial.derivative_add, Polynomial.derivative_add, Polynomial.eval_add]
      rw [ihp, ihq, homogeneousPart4_add, MvPolynomial.eval_add]
      ring
  | mul_X p j ihp =>
      unfold directionalDeriv2 at ihp ⊢
      rw [univariateRestriction_mul_X_zero]
      rw [polynomial_second_derivative_mul_CX_eval_zero]
      rw [homogeneousPart4_two_mul_X]
      have hlin := directionalDeriv_zero_eq_eval_homogeneousPart_one p z
      unfold directionalDeriv at hlin
      rw [hlin]
      simp [MvPolynomial.eval_mul]
      ring

/-- Zero-line Markov input for the linear jet.

For each Choi-Lam zero direction `z`, the univariate vector polynomial
`t ↦ Q(t z)` is bounded by `A sqrt epsilon`; the formalized Markov estimate gives
the corresponding linear homogeneous part evaluated at `z` with an `O(k^2)` loss. -/
theorem weightedJetLemma_linear_zero_direction_bound
    {N k : ℕ} {epsilon A : ℝ}
    (_heps : 0 < epsilon)
    (_hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon) :
    ∀ zi : Fin 4,
      interiorVecNorm
          (fun i : Fin N => MvPolynomial.eval (choiLamZeroDirection zi)
            (homogeneousPartVec4 1 Q i))
        ≤ jetErrorConst * A * (k : ℝ) ^ 2 * Real.sqrt epsilon := by
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
    simp only [P, univariateRestriction_eval, zero_add]
    have hdir :
        t • choiLamZeroDirection zi =
          (fun j => t * choiLamZeroDirection zi j) := by
      rfl
    rw [hdir]
    exact hline
  have hmark := interior_markov_vector_first_derivative_schm P hMnon hdegP hbound
  let V : Fin N → ℝ := fun i =>
    MvPolynomial.eval (choiLamZeroDirection zi) (homogeneousPartVec4 1 Q i)
  have hderiv : (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) = V := by
    funext i
    dsimp [P, V, homogeneousPartVec4]
    change directionalDeriv (Q i) (0 : Fin 4 → ℝ) (choiLamZeroDirection zi) =
      MvPolynomial.eval (choiLamZeroDirection zi) (homogeneousPart4 1 (Q i))
    rw [directionalDeriv_zero_eq_eval_homogeneousPart_one]
  have hV : interiorVecNorm V ≤ 4 * ((k : ℝ) ^ 2 * (A * Real.sqrt epsilon)) := by
    calc
      interiorVecNorm V ≤ 4 * (k : ℝ) ^ 2 * (A * Real.sqrt epsilon) := by
        simpa [hderiv] using hmark
      _ = 4 * ((k : ℝ) ^ 2 * (A * Real.sqrt epsilon)) := by ring
  have hconst : (4 : ℝ) ≤ jetErrorConst := by
    unfold jetErrorConst
    norm_num
  have hTnon : 0 ≤ A * (k : ℝ) ^ 2 * Real.sqrt epsilon := by
    positivity
  calc
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval (choiLamZeroDirection zi)
          (homogeneousPartVec4 1 Q i)) = interiorVecNorm V := rfl
    _ ≤ 4 * ((k : ℝ) ^ 2 * (A * Real.sqrt epsilon)) := hV
    _ = 4 * (A * (k : ℝ) ^ 2 * Real.sqrt epsilon) := by ring
    _ ≤ jetErrorConst * (A * (k : ℝ) ^ 2 * Real.sqrt epsilon) := by
      exact mul_le_mul_of_nonneg_right hconst hTnon
    _ = jetErrorConst * A * (k : ℝ) ^ 2 * Real.sqrt epsilon := by ring

/-- Linear jet bound assembled from the zero-line Markov estimate and the
finite-dimensional basis conversion. -/
theorem weightedJetLemma_linear_bound
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
      8 * jetErrorConst * A * (k : ℝ) ^ 2 * Real.sqrt epsilon := by
  have hlin := linear_coeff_bound_from_choiLam_basis (homogeneousPartVec4 1 Q)
    (B := jetErrorConst * A * (k : ℝ) ^ 2 * Real.sqrt epsilon)
    (fun i => by
      unfold homogeneousPartVec4
      exact homogeneousPart4_idem 1 (Q i))
    (mul_nonneg (mul_nonneg (mul_nonneg jetErrorConst_pos.le (le_trans zero_le_one hA))
      (sq_nonneg (k : ℝ))) (Real.sqrt_nonneg epsilon))
    (weightedJetLemma_linear_zero_direction_bound heps hk hA Q hdeg hzeroLines)
  simpa [mul_assoc] using hlin

lemma boxSmall_smul_of_localSqNorm_eq_one
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) {t : ℝ} (ht : |t| ≤ schmInteriorS) :
    boxSmall (fun j => t * v j) := by
  intro j
  have hvj_sq : v j ^ 2 ≤ 1 := by
    simpa [hv] using sq_coord_le_localSqNorm v j
  have hvj_abs : |v j| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    exact hvj_sq
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg t) hvj_abs).trans ht

lemma localSqNorm_smul_of_localSqNorm_eq_one
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) (t : ℝ) :
    localSqNorm (fun j => t * v j) = t ^ 2 := by
  rw [localSqNorm_smul, hv, mul_one]

lemma sq_le_schmInteriorS_sq_of_abs_le {t : ℝ} (ht : |t| ≤ schmInteriorS) :
    t ^ 2 ≤ schmInteriorS ^ 2 := by
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg t) ht 2

lemma local_quadratic_line_bound
    {N : ℕ} {epsilon A : ℝ}
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) :
    ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N => (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v).eval t)
        ≤ A * (Real.sqrt epsilon + schmInteriorS ^ 2) := by
  intro t ht
  have hbox : boxSmall (fun j => t * v j) := boxSmall_smul_of_localSqNorm_eq_one hv ht
  have hloc := hlocal (fun j => t * v j) hbox
  have hsq : localSqNorm (fun j => t * v j) ≤ schmInteriorS ^ 2 := by
    rw [localSqNorm_smul_of_localSqNorm_eq_one hv t]
    exact sq_le_schmInteriorS_sq_of_abs_le ht
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  calc
    interiorVecNorm
          (fun i : Fin N => (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v).eval t)
        = interiorVecNorm (fun i : Fin N => MvPolynomial.eval (fun j => t * v j) (Q i)) := by
          congr 1
          funext i
          rw [univariateRestriction_eval]
          have hx : (0 + t • v : Fin 4 → ℝ) = fun j => t * v j := by
            ext j
            simp [Pi.smul_apply, smul_eq_mul]
          rw [hx]
    _ ≤ A * (Real.sqrt epsilon + localSqNorm (fun j => t * v j)) := hloc
    _ ≤ A * (Real.sqrt epsilon + schmInteriorS ^ 2) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl (Real.sqrt epsilon)) hsq) hA0

end OptimalConvergenceRates
