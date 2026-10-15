/- The degree-six comparison between a Motzkin certificate and cubic SOS forms. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.NormEquivalence

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

/-- Evaluation of a homogeneous SOS component is the finite convolution of
its root jets after restriction to a line. -/
lemma eval_homogeneousPart3_sosVectorSq3 {N d : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    MvPolynomial.eval v (homogeneousPart3 d (sosVectorSq3 Q)) =
      ∑ i : Fin N, ∑ x ∈ Finset.antidiagonal d,
        MvPolynomial.eval v (homogeneousPart3 x.1 (Q i)) *
          MvPolynomial.eval v (homogeneousPart3 x.2 (Q i)) := by
  rw [← coeff_univariateRestriction_zero_eq_eval_homogeneousPart]
  unfold sosVectorSq3
  rw [show univariateRestriction (∑ i : Fin N, (Q i) ^ 2) 0 v =
      ∑ i : Fin N, (univariateRestriction (Q i) 0 v) ^ 2 by
    unfold univariateRestriction
    simp]
  let cf : Polynomial ℝ →+ ℝ :=
    { toFun := fun P => P.coeff d
      map_zero' := Polynomial.coeff_zero d
      map_add' := fun P R => Polynomial.coeff_add P R d }
  change cf (∑ i : Fin N, _ ^ 2) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (_ ^ 2 : Polynomial ℝ).coeff d = _
  rw [pow_two, Polynomial.coeff_mul]
  change (∑ x ∈ Finset.antidiagonal d,
    (univariateRestriction (Q i) 0 v).coeff x.1 *
      (univariateRestriction (Q i) 0 v).coeff x.2) = _
  simp_rw [coeff_univariateRestriction_zero_eq_eval_homogeneousPart]

/-- The cubic-jet SOS extracted from every multiplier of a certificate. -/
def motzkinCubicJetSOS
    {N : Finset (Fin 3) → ℕ}
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ J ∈ Finset.univ.powerset, sosVectorSq3 (homogeneousPartVec3 3 (Q J))

/-- Difference between the Motzkin sextic and the cubic-jet SOS. -/
def motzkinDegreeSixError
    {N : Finset (Fin 3) → ℕ}
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  motzkinSextic - motzkinCubicJetSOS Q

lemma motzkinCubicJetSOS_isSOS
    {N : Finset (Fin 3) → ℕ}
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ) :
    IsSOS (motzkinCubicJetSOS Q) := by
  unfold motzkinCubicJetSOS
  apply IsSOS_sum_finset
  intro J _
  exact sosVectorSq3_isSOS _

lemma motzkinCubicJetSOS_totalDegree_le_six
    {N : Finset (Fin 3) → ℕ}
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ) :
    (motzkinCubicJetSOS Q).totalDegree ≤ 6 := by
  unfold motzkinCubicJetSOS
  apply MvPolynomial.totalDegree_finsetSum_le
  intro J _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  calc
    ((homogeneousPartVec3 3 (Q J) i) ^ 2).totalDegree ≤
        2 * (homogeneousPartVec3 3 (Q J) i).totalDegree :=
      MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 * 3 := Nat.mul_le_mul_left 2
      (isHomogeneous_of_homogeneousPart3_eq
        (homogeneousPart3_idem 3 (Q J i))).totalDegree_le
    _ = 6 := by norm_num

lemma motzkinCubicJetSOS_degreeBounded
    {N : Finset (Fin 3) → ℕ}
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ) :
    Nonempty (DegreeBoundedSOS (motzkinCubicJetSOS Q) 3) := by
  rcases motzkinCubicJetSOS_isSOS Q with ⟨M, P, hP⟩
  refine ⟨⟨M, P, hP, ?_⟩⟩
  apply sos_summand_totalDegree_le_of_sum_sq_totalDegree hP
  simpa using motzkinCubicJetSOS_totalDegree_le_six Q


lemma motzkinCoeffNorm_boxGenerator_le_two (i : Fin 3) :
    motzkinCoeffNorm (BoxSemialgebraicGenerator i) ≤ 2 := by
  unfold BoxSemialgebraicGenerator
  calc
    motzkinCoeffNorm (1 - X i ^ 2) ≤ motzkinCoeffNorm 1 + motzkinCoeffNorm (X i ^ 2) := by
      simpa [sub_eq_add_neg, motzkinCoeffNorm_neg] using
        motzkinCoeffNorm_add_le (1 : MvPolynomial (Fin 3) ℝ) (-(X i ^ 2))
    _ ≤ 2 := by
      have hOne : motzkinCoeffNorm (1 : MvPolynomial (Fin 3) ℝ) ≤ 1 := by
        rw [← MvPolynomial.C_1]
        simpa only [MvPolynomial.monomial_zero', abs_one] using
          motzkinCoeffNorm_monomial_le (0 : Fin 3 →₀ ℕ) (1 : ℝ)
      have hX : motzkinCoeffNorm (X i ^ 2 : MvPolynomial (Fin 3) ℝ) ≤ 1 := by
        rw [MvPolynomial.X_pow_eq_monomial]
        simpa using motzkinCoeffNorm_monomial_le (Finsupp.single i 2) (1 : ℝ)
      linarith

lemma motzkinCoeffNorm_boxGeneratorProd_le_eight (J : Finset (Fin 3)) :
    motzkinCoeffNorm (BoxSemialgebraicGeneratorProd J) ≤ 8 := by
  unfold BoxSemialgebraicGeneratorProd
  calc
    motzkinCoeffNorm (∏ j ∈ J, BoxSemialgebraicGenerator j) ≤
        ∏ j ∈ J, motzkinCoeffNorm (BoxSemialgebraicGenerator j) := by
      induction J using Finset.induction_on with
      | empty =>
          simp only [Finset.prod_empty]
          rw [← MvPolynomial.C_1]
          simpa only [MvPolynomial.monomial_zero', abs_one] using
            motzkinCoeffNorm_monomial_le (0 : Fin 3 →₀ ℕ) (1 : ℝ)
      | @insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.prod_insert ha]
          exact (motzkinCoeffNorm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left ih (motzkinCoeffNorm_nonneg _))
    _ ≤ ∏ _j ∈ J, (2 : ℝ) := by
      exact Finset.prod_le_prod₀ (fun _ _ => motzkinCoeffNorm_nonneg _)
        (fun j _ => motzkinCoeffNorm_boxGenerator_le_two j)
    _ = (2 : ℝ) ^ J.card := by simp
    _ ≤ 2 ^ 3 := by
      exact pow_le_pow_right₀ (by norm_num) (by simpa using Finset.card_le_univ J)
    _ = 8 := by norm_num

lemma abs_eval_homogeneousPart3_boxGeneratorProd_le_eight
    (J : Finset (Fin 3)) (d : ℕ) (v : Fin 3 → ℝ)
    (hv : motzkinSqNorm v = 1) :
    |MvPolynomial.eval v
      (homogeneousPart3 d (BoxSemialgebraicGeneratorProd J))| ≤ 8 := by
  exact (abs_eval_le_motzkinCoeffNorm_of_motzkinSqNorm_eq_one _ hv).trans
    ((motzkinCoeffNorm_homogeneousPart3_le d _).trans
      (motzkinCoeffNorm_boxGeneratorProd_le_eight J))


lemma abs_eval_homogeneousPart3_sosVectorSq3_le {N d : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    |MvPolynomial.eval v (homogeneousPart3 d (sosVectorSq3 Q))| ≤
      ∑ x ∈ Finset.antidiagonal d,
        interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPart3 x.1 (Q i))) *
        interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPart3 x.2 (Q i))) := by
  rw [eval_homogeneousPart3_sosVectorSq3]
  rw [Finset.sum_comm]
  calc
    |∑ x ∈ Finset.antidiagonal d, ∑ i : Fin N,
        MvPolynomial.eval v (homogeneousPart3 x.1 (Q i)) *
          MvPolynomial.eval v (homogeneousPart3 x.2 (Q i))| ≤
        ∑ x ∈ Finset.antidiagonal d, |∑ i : Fin N,
          MvPolynomial.eval v (homogeneousPart3 x.1 (Q i)) *
            MvPolynomial.eval v (homogeneousPart3 x.2 (Q i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x _
      change |vecDot (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPart3 x.1 (Q i)))
        (fun i : Fin N => MvPolynomial.eval v
          (homogeneousPart3 x.2 (Q i)))| ≤ _
      exact OptimalConvergenceRates.abs_vecDot_le_vecNorm_mul _ _


lemma abs_eval_homogeneousPart3_sosVectorSq3_le_jet_bounds {N d : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ)
    (A : ℕ → ℝ) (hA : ∀ m, m ≤ d → 0 ≤ A m)
    (hjet : ∀ m, m ≤ d →
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPart3 m (Q i))) ≤ A m) :
    |MvPolynomial.eval v (homogeneousPart3 d (sosVectorSq3 Q))| ≤
      ∑ x ∈ Finset.antidiagonal d, A x.1 * A x.2 := by
  refine (abs_eval_homogeneousPart3_sosVectorSq3_le Q v).trans ?_
  apply Finset.sum_le_sum
  intro x hx
  have hsum : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
  exact mul_le_mul (hjet x.1 (by omega)) (hjet x.2 (by omega))
    (interiorVecNorm_nonneg _) (hA x.1 (by omega))


/-- Common high-jet constant after the cubic-tail and symmetric-hole estimates. -/
def motzkinHighJetConst : ℝ :=
  2 * Real.exp 6 * (4 * motzkinLowJetConst + 2 * schmInteriorLocalControlConst)

theorem motzkinHighJetConst_pos : 0 < motzkinHighJetConst := by
  unfold motzkinHighJetConst
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos 6))
    (add_pos (mul_pos (by norm_num) motzkinLowJetConst_pos)
      (mul_pos (by norm_num) schmInteriorLocalControlConst_pos))

/-- All seven homogeneous root jets of one certificate multiplier, evaluated
on the unit sphere, with their low/high scalings made explicit. -/
theorem motzkin_certificate_root_jet_eval_bounds
    {N r : ℕ} {epsilon rho : ℝ}
    (heps : 0 < epsilon) (hrho : 0 < rho)
    (hsqrt : Real.sqrt epsilon = rho ^ 3)
    (hr2 : 2 ≤ r) (hrhoSmall : rho < schmInteriorS / 2)
    (hsmall : (r : ℝ) * rho ≤ 1 / 8)
    (Q : Fin N → MvPolynomial (Fin 3) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ r)
    (hlocal : ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      ∀ t : ℝ, |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval (fun j => t * v j) (Q i)) ≤
          schmInteriorLocalControlConst * (Real.sqrt epsilon + |t| ^ 3))
    (hzero : ∀ zi : Fin 6, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval (fun j => t * motzkinZeroDirection zi j) (Q i)) ≤
        schmInteriorLocalControlConst * Real.sqrt epsilon) :
    ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      let H := fun m : ℕ => interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPart3 m (Q i)))
      H 0 ≤ motzkinLowJetConst * Real.sqrt epsilon ∧
      H 1 ≤ motzkinLowJetConst * (r : ℝ) * Real.sqrt epsilon ∧
      H 2 ≤ motzkinLowJetConst * (r : ℝ) ^ 2 * Real.sqrt epsilon ∧
      H 3 ≤ motzkinHighJetConst ∧
      H 4 ≤ 8 * (r : ℝ) * motzkinHighJetConst ∧
      H 5 ≤ 32 * (r : ℝ) ^ 2 * motzkinHighJetConst ∧
      H 6 ≤ 700 * (r : ℝ) ^ 3 * motzkinHighJetConst := by
  have hlow := motzkin_low_jet_bounds heps (by omega) Q hdeg hzero
  have houter := motzkin_cubic_tail_outer_bound hrho hsqrt hsmall Q hlocal hlow
  have hdegree : (((2 * r : ℕ) : ℝ) * rho) ≤ schmInteriorS := by
    norm_num [schmInteriorS] at hsmall ⊢
    nlinarith
  have hhigh := motzkin_high_jet_eval_bounds_of_tail_bound hrho hrhoSmall hr2
    hdegree (add_nonneg
      (mul_nonneg (by norm_num) motzkinLowJetConst_pos.le)
      (mul_nonneg (by norm_num) schmInteriorLocalControlConst_pos.le))
    Q hdeg houter
  intro v hv
  have hh := hhigh v hv
  dsimp only at hh ⊢
  refine ⟨(interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one
      (homogeneousPartVec3 0 Q) hv).trans hlow.1, ?_⟩
  refine ⟨(interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one
      (homogeneousPartVec3 1 Q) hv).trans hlow.2.1, ?_⟩
  refine ⟨(interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one
      (homogeneousPartVec3 2 Q) hv).trans hlow.2.2, ?_⟩
  simpa [motzkinHighJetConst, homogeneousPartVec3] using hh


lemma homogeneousPart3_zero_boxGeneratorProd (J : Finset (Fin 3)) :
    homogeneousPart3 0 (BoxSemialgebraicGeneratorProd J) = 1 := by
  rw [homogeneousPart3_eq_homogeneousComponent, MvPolynomial.homogeneousComponent_zero]
  rw [← MvPolynomial.C_1]
  congr 1
  rw [← MvPolynomial.constantCoeff_eq
    (BoxSemialgebraicGeneratorProd J : MvPolynomial (Fin 3) ℝ)]
  rw [← MvPolynomial.eval_zero]
  unfold BoxSemialgebraicGeneratorProd
  rw [map_prod]
  apply Finset.prod_eq_one
  intro i _
  rw [BoxSemialgebraicGenerator_eval]
  simp

/-- The non-cubic-square part of the sextic jet of one SOS multiplier. -/
def motzkinSosSixError {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  homogeneousPart3 6 (sosVectorSq3 Q) -
    sosVectorSq3 (homogeneousPartVec3 3 Q)

lemma motzkinSosSixError_expansion {N : ℕ}
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    motzkinSosSixError Q = ∑ i : Fin N,
      (homogeneousPart3 0 (Q i) * homogeneousPart3 6 (Q i) +
       homogeneousPart3 1 (Q i) * homogeneousPart3 5 (Q i) +
       homogeneousPart3 2 (Q i) * homogeneousPart3 4 (Q i) +
       homogeneousPart3 4 (Q i) * homogeneousPart3 2 (Q i) +
       homogeneousPart3 5 (Q i) * homogeneousPart3 1 (Q i) +
       homogeneousPart3 6 (Q i) * homogeneousPart3 0 (Q i)) := by
  unfold motzkinSosSixError
  rw [homogeneousPart3_sosVectorSq3_six]
  unfold sosVectorSq3 homogeneousPartVec3
  simp only [pow_two]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Sextic error in one generator-weighted SOS summand. -/
def motzkinWeightedSixError {N : ℕ} (J : Finset (Fin 3))
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  homogeneousPart3 6 (BoxSemialgebraicGeneratorProd J * sosVectorSq3 Q) -
    sosVectorSq3 (homogeneousPartVec3 3 Q)

lemma motzkinWeightedSixError_expansion {N : ℕ} (J : Finset (Fin 3))
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    motzkinWeightedSixError J Q =
      motzkinSosSixError Q +
      homogeneousPart3 1 (BoxSemialgebraicGeneratorProd J) *
        homogeneousPart3 5 (sosVectorSq3 Q) +
      homogeneousPart3 2 (BoxSemialgebraicGeneratorProd J) *
        homogeneousPart3 4 (sosVectorSq3 Q) +
      homogeneousPart3 3 (BoxSemialgebraicGeneratorProd J) *
        homogeneousPart3 3 (sosVectorSq3 Q) +
      homogeneousPart3 4 (BoxSemialgebraicGeneratorProd J) *
        homogeneousPart3 2 (sosVectorSq3 Q) +
      homogeneousPart3 5 (BoxSemialgebraicGeneratorProd J) *
        homogeneousPart3 1 (sosVectorSq3 Q) +
      homogeneousPart3 6 (BoxSemialgebraicGeneratorProd J) *
        homogeneousPart3 0 (sosVectorSq3 Q) := by
  unfold motzkinWeightedSixError
  rw [homogeneousPart3_six_mul, homogeneousPart3_zero_boxGeneratorProd]
  rw [one_mul]
  unfold motzkinSosSixError
  abel


/-- A common majorant for the seven evaluated root jets. -/
def motzkinJetMajorant (r : ℕ) (s : ℝ) : ℕ → ℝ
  | 0 => (motzkinLowJetConst + motzkinHighJetConst) * s
  | 1 => (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) * s
  | 2 => (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ 2 * s
  | 3 => 700 * (motzkinLowJetConst + motzkinHighJetConst)
  | 4 => 700 * (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ)
  | 5 => 700 * (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ 2
  | _ => 700 * (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ 3

lemma motzkinJetMajorant_nonneg (r : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (m : ℕ) (hm : m ≤ 6) : 0 ≤ motzkinJetMajorant r s m := by
  have hK : 0 ≤ motzkinLowJetConst + motzkinHighJetConst :=
    (add_pos motzkinLowJetConst_pos motzkinHighJetConst_pos).le
  interval_cases m
  all_goals simp only [motzkinJetMajorant]
  all_goals positivity

lemma motzkin_root_jets_le_majorant
    {N r : ℕ} {epsilon : ℝ} (hr2 : 2 ≤ r) (heps : 0 < epsilon)
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ)
    (hjets :
      let H := fun m : ℕ => interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPart3 m (Q i)))
      H 0 ≤ motzkinLowJetConst * Real.sqrt epsilon ∧
      H 1 ≤ motzkinLowJetConst * (r : ℝ) * Real.sqrt epsilon ∧
      H 2 ≤ motzkinLowJetConst * (r : ℝ) ^ 2 * Real.sqrt epsilon ∧
      H 3 ≤ motzkinHighJetConst ∧
      H 4 ≤ 8 * (r : ℝ) * motzkinHighJetConst ∧
      H 5 ≤ 32 * (r : ℝ) ^ 2 * motzkinHighJetConst ∧
      H 6 ≤ 700 * (r : ℝ) ^ 3 * motzkinHighJetConst) :
    ∀ m, m ≤ 6 →
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPart3 m (Q i))) ≤
        motzkinJetMajorant r (Real.sqrt epsilon) m := by
  dsimp only at hjets
  intro m hm
  have hs : 0 ≤ Real.sqrt epsilon := Real.sqrt_nonneg epsilon
  have hL : 0 ≤ motzkinLowJetConst := motzkinLowJetConst_pos.le
  have hH : 0 ≤ motzkinHighJetConst := motzkinHighJetConst_pos.le
  interval_cases m
  · simpa only [motzkinJetMajorant] using hjets.1.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hH) hs)
  · refine hjets.2.1.trans ?_
    simp only [motzkinJetMajorant]
    gcongr
    exact le_add_of_nonneg_right hH
  · refine hjets.2.2.1.trans ?_
    simp only [motzkinJetMajorant]
    gcongr
    exact le_add_of_nonneg_right hH
  · simpa only [motzkinJetMajorant] using
      hjets.2.2.2.1.trans (by nlinarith : motzkinHighJetConst ≤
        700 * (motzkinLowJetConst + motzkinHighJetConst))
  · refine hjets.2.2.2.2.1.trans ?_
    simp only [motzkinJetMajorant]
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith [mul_nonneg hr hH, mul_nonneg hr hL]
  · refine hjets.2.2.2.2.2.1.trans ?_
    simp only [motzkinJetMajorant]
    have hr : 0 ≤ (r : ℝ) ^ 2 := sq_nonneg (r : ℝ)
    have hcoef : 32 * motzkinHighJetConst ≤
        700 * (motzkinLowJetConst + motzkinHighJetConst) := by nlinarith
    calc
      32 * (r : ℝ) ^ 2 * motzkinHighJetConst =
          (32 * motzkinHighJetConst) * (r : ℝ) ^ 2 := by ring
      _ ≤ (700 * (motzkinLowJetConst + motzkinHighJetConst)) * (r : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hr
      _ = 700 * (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ 2 := by ring
  · refine hjets.2.2.2.2.2.2.trans ?_
    simp only [motzkinJetMajorant]
    have hr : 0 ≤ (r : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg r) 3
    have hcoef : motzkinHighJetConst ≤
        motzkinLowJetConst + motzkinHighJetConst := le_add_of_nonneg_left hL
    calc
      700 * (r : ℝ) ^ 3 * motzkinHighJetConst =
          700 * motzkinHighJetConst * (r : ℝ) ^ 3 := by ring
      _ ≤ 700 * (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcoef (by norm_num)) hr

lemma motzkinJetMajorant_of_le_two
    (r : ℕ) (s : ℝ) {m : ℕ} (hm : m ≤ 2) :
    motzkinJetMajorant r s m =
      (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ m * s := by
  interval_cases m <;> simp [motzkinJetMajorant]

lemma motzkinJetMajorant_of_three_le
    (r : ℕ) (s : ℝ) {m : ℕ} (hm3 : 3 ≤ m) (hm6 : m ≤ 6) :
    motzkinJetMajorant r s m =
      700 * (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ (m - 3) := by
  interval_cases m <;> simp [motzkinJetMajorant]

lemma pow_mul_sqrt_le_cube
    {r d : ℕ} {epsilon : ℝ}
    (hr : (1 : ℝ) ≤ r) (hs : 0 ≤ Real.sqrt epsilon)
    (hsOne : Real.sqrt epsilon ≤ 1)
    (hrs : (r : ℝ) * Real.sqrt epsilon ≤ 1) (hd : d ≤ 4) :
    (r : ℝ) ^ d * Real.sqrt epsilon ≤ (r : ℝ) ^ 3 := by
  by_cases hd3 : d ≤ 3
  · calc
      (r : ℝ) ^ d * Real.sqrt epsilon ≤ (r : ℝ) ^ 3 * Real.sqrt epsilon :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hr hd3) hs
      _ ≤ (r : ℝ) ^ 3 * 1 := by gcongr
      _ = (r : ℝ) ^ 3 := mul_one _
  · have hd4 : d = 4 := by omega
    subst d
    calc
      (r : ℝ) ^ 4 * Real.sqrt epsilon = (r : ℝ) ^ 3 *
          ((r : ℝ) * Real.sqrt epsilon) := by ring
      _ ≤ (r : ℝ) ^ 3 * 1 := by gcongr
      _ = (r : ℝ) ^ 3 := mul_one _


lemma motzkinJetMajorant_pair_le_of_left_low
    {r : ℕ} {epsilon : ℝ}
    (hr : (1 : ℝ) ≤ r) (hs : 0 ≤ Real.sqrt epsilon)
    (hsOne : Real.sqrt epsilon ≤ 1)
    (hrs : (r : ℝ) * Real.sqrt epsilon ≤ 1)
    {m n : ℕ} (hm2 : m ≤ 2) (hn : n ≤ 6) (hsum : m + n ≤ 6) :
    motzkinJetMajorant r (Real.sqrt epsilon) m *
        motzkinJetMajorant r (Real.sqrt epsilon) n ≤
      700 * (motzkinLowJetConst + motzkinHighJetConst) ^ 2 *
        (r : ℝ) ^ 3 * Real.sqrt epsilon := by
  rw [motzkinJetMajorant_of_le_two r (Real.sqrt epsilon) hm2]
  by_cases hnlow : n ≤ 2
  · rw [motzkinJetMajorant_of_le_two r (Real.sqrt epsilon) hnlow]
    have hpow := pow_mul_sqrt_le_cube hr hs hsOne hrs (show m + n ≤ 4 by omega)
    have hscalar : (r : ℝ) ^ (m + n) * Real.sqrt epsilon ^ 2 ≤
        (r : ℝ) ^ 3 * Real.sqrt epsilon := by
      calc
        (r : ℝ) ^ (m + n) * Real.sqrt epsilon ^ 2 =
            ((r : ℝ) ^ (m + n) * Real.sqrt epsilon) * Real.sqrt epsilon := by ring
        _ ≤ (r : ℝ) ^ 3 * Real.sqrt epsilon :=
          mul_le_mul_of_nonneg_right hpow hs
    calc
      (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ m *
          Real.sqrt epsilon *
          ((motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ n *
            Real.sqrt epsilon) =
          (motzkinLowJetConst + motzkinHighJetConst) ^ 2 *
            ((r : ℝ) ^ (m + n) * Real.sqrt epsilon ^ 2) := by
              rw [pow_add]
              ring
      _ ≤ (motzkinLowJetConst + motzkinHighJetConst) ^ 2 *
          ((r : ℝ) ^ 3 * Real.sqrt epsilon) :=
        mul_le_mul_of_nonneg_left hscalar (sq_nonneg _)
      _ ≤ 700 * (motzkinLowJetConst + motzkinHighJetConst) ^ 2 *
          (r : ℝ) ^ 3 * Real.sqrt epsilon := by
        have hfac : 0 ≤ (motzkinLowJetConst + motzkinHighJetConst) ^ 2 *
            ((r : ℝ) ^ 3 * Real.sqrt epsilon) := by positivity
        nlinarith
  · have hn3 : 3 ≤ n := by omega
    rw [motzkinJetMajorant_of_three_le r (Real.sqrt epsilon) hn3 hn]
    have hexp : m + (n - 3) ≤ 3 := by omega
    have hp : (r : ℝ) ^ (m + (n - 3)) ≤ (r : ℝ) ^ 3 :=
      pow_le_pow_right₀ hr hexp
    rw [pow_add] at hp
    calc
      (motzkinLowJetConst + motzkinHighJetConst) * (r : ℝ) ^ m *
          Real.sqrt epsilon *
          (700 * (motzkinLowJetConst + motzkinHighJetConst) *
            (r : ℝ) ^ (n - 3)) =
          700 * (motzkinLowJetConst + motzkinHighJetConst) ^ 2 *
            ((r : ℝ) ^ m * (r : ℝ) ^ (n - 3)) * Real.sqrt epsilon := by ring
      _ ≤ 700 * (motzkinLowJetConst + motzkinHighJetConst) ^ 2 *
          (r : ℝ) ^ 3 * Real.sqrt epsilon := by gcongr

lemma motzkinJetMajorant_pair_le
    {r : ℕ} {epsilon rho : ℝ}
    (hr2 : 2 ≤ r) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hsqrt : Real.sqrt epsilon = rho ^ 3)
    (hsmall : (r : ℝ) * rho ≤ 1 / 8)
    {m n : ℕ} (hm : m ≤ 6) (hn : n ≤ 6)
    (hpair : m + n ≤ 5 ∨ (m + n = 6 ∧ (m ≠ 3 ∨ n ≠ 3))) :
    motzkinJetMajorant r (Real.sqrt epsilon) m *
        motzkinJetMajorant r (Real.sqrt epsilon) n ≤
      700 * (motzkinLowJetConst + motzkinHighJetConst) ^ 2 *
        (r : ℝ) ^ 3 * Real.sqrt epsilon := by
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hs : 0 ≤ Real.sqrt epsilon := Real.sqrt_nonneg epsilon
  have hsOne : Real.sqrt epsilon ≤ 1 := by
    rw [hsqrt]
    nlinarith [sq_nonneg rho, mul_self_nonneg rho]
  have hrs : (r : ℝ) * Real.sqrt epsilon ≤ 1 := by
    rw [hsqrt]
    calc
      (r : ℝ) * rho ^ 3 = ((r : ℝ) * rho) * rho ^ 2 := by ring
      _ ≤ (1 / 8) * rho ^ 2 := by gcongr
      _ ≤ 1 := by nlinarith [sq_nonneg rho]
  have hsum : m + n ≤ 6 := by omega
  have hlow : m ≤ 2 ∨ n ≤ 2 := by omega
  rcases hlow with hm2 | hn2
  · exact motzkinJetMajorant_pair_le_of_left_low hr hs hsOne hrs hm2 hn hsum
  · rw [mul_comm]
    exact motzkinJetMajorant_pair_le_of_left_low hr hs hsOne hrs hn2 hm (by omega)


/-- One unit in the directional sextic error estimate. -/
def motzkinPairErrorBound (r : ℕ) (epsilon : ℝ) : ℝ :=
  700 * (motzkinLowJetConst + motzkinHighJetConst) ^ 2 *
    (r : ℝ) ^ 3 * Real.sqrt epsilon

lemma motzkinPairErrorBound_nonneg (r : ℕ) (epsilon : ℝ) :
    0 ≤ motzkinPairErrorBound r epsilon := by
  unfold motzkinPairErrorBound
  positivity

lemma abs_eval_jet_pair_le
    {N r : ℕ} {epsilon rho : ℝ}
    (hr2 : 2 ≤ r) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hsqrt : Real.sqrt epsilon = rho ^ 3) (hsmall : (r : ℝ) * rho ≤ 1 / 8)
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ)
    (hjets : ∀ m, m ≤ 6 →
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPart3 m (Q i))) ≤
        motzkinJetMajorant r (Real.sqrt epsilon) m)
    {m n : ℕ} (hm : m ≤ 6) (hn : n ≤ 6)
    (hpair : m + n ≤ 5 ∨ (m + n = 6 ∧ (m ≠ 3 ∨ n ≠ 3))) :
    |∑ i : Fin N, MvPolynomial.eval v (homogeneousPart3 m (Q i)) *
        MvPolynomial.eval v (homogeneousPart3 n (Q i))| ≤
      motzkinPairErrorBound r epsilon := by
  change |vecDot (fun i : Fin N => MvPolynomial.eval v (homogeneousPart3 m (Q i)))
    (fun i : Fin N => MvPolynomial.eval v (homogeneousPart3 n (Q i)))| ≤ _
  calc
    _ ≤ interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPart3 m (Q i))) *
        interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPart3 n (Q i))) :=
      OptimalConvergenceRates.abs_vecDot_le_vecNorm_mul _ _
    _ ≤ motzkinJetMajorant r (Real.sqrt epsilon) m *
        motzkinJetMajorant r (Real.sqrt epsilon) n := by
      exact mul_le_mul (hjets m hm) (hjets n hn) (interiorVecNorm_nonneg _)
        (motzkinJetMajorant_nonneg r (Real.sqrt_nonneg epsilon) m hm)
    _ ≤ _ := motzkinJetMajorant_pair_le hr2 hrho hrhoOne hsqrt hsmall hm hn hpair

lemma abs_eval_sos_component_below_six_le
    {N r d : ℕ} {epsilon rho : ℝ}
    (hr2 : 2 ≤ r) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hsqrt : Real.sqrt epsilon = rho ^ 3) (hsmall : (r : ℝ) * rho ≤ 1 / 8)
    (hd : d ≤ 5) (Q : Fin N → MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ)
    (hjets : ∀ m, m ≤ 6 →
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPart3 m (Q i))) ≤
        motzkinJetMajorant r (Real.sqrt epsilon) m) :
    |MvPolynomial.eval v (homogeneousPart3 d (sosVectorSq3 Q))| ≤
      6 * motzkinPairErrorBound r epsilon := by
  calc
    |MvPolynomial.eval v (homogeneousPart3 d (sosVectorSq3 Q))| ≤
        ∑ x ∈ Finset.antidiagonal d,
          motzkinJetMajorant r (Real.sqrt epsilon) x.1 *
            motzkinJetMajorant r (Real.sqrt epsilon) x.2 :=
      abs_eval_homogeneousPart3_sosVectorSq3_le_jet_bounds Q v _
        (fun m hm ↦ motzkinJetMajorant_nonneg r (Real.sqrt_nonneg epsilon) m
          (hm.trans (hd.trans (by omega))))
        (fun m hm ↦ hjets m (hm.trans (hd.trans (by omega))))
    _ ≤ ∑ _x ∈ Finset.antidiagonal d, motzkinPairErrorBound r epsilon := by
      apply Finset.sum_le_sum
      intro x hx
      have hsum := Finset.mem_antidiagonal.mp hx
      exact motzkinJetMajorant_pair_le hr2 hrho hrhoOne hsqrt hsmall
        (by omega) (by omega) (by left; omega)
    _ ≤ 6 * motzkinPairErrorBound r epsilon := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.antidiagonal d).card = d + 1 := by simp
      rw [hcard]
      have hc : ((d + 1 : ℕ) : ℝ) ≤ 6 := by
        exact_mod_cast (show d + 1 ≤ 6 by omega)
      exact mul_le_mul_of_nonneg_right hc (motzkinPairErrorBound_nonneg r epsilon)

lemma abs_add6_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  calc
    |a + b + c + d + e + f| ≤ |a + b + c + d + e| + |f| := abs_add_le _ _
    _ ≤ (|a + b + c + d| + |e|) + |f| := by gcongr; exact abs_add_le _ _
    _ ≤ ((|a + b + c| + |d|) + |e|) + |f| := by gcongr; exact abs_add_le _ _
    _ ≤ (((|a + b| + |c|) + |d|) + |e|) + |f| := by gcongr; exact abs_add_le _ _
    _ ≤ ((((|a| + |b|) + |c|) + |d|) + |e|) + |f| := by gcongr; exact abs_add_le _ _

lemma abs_eval_motzkinSosSixError_le
    {N r : ℕ} {epsilon rho : ℝ}
    (hr2 : 2 ≤ r) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hsqrt : Real.sqrt epsilon = rho ^ 3) (hsmall : (r : ℝ) * rho ≤ 1 / 8)
    (Q : Fin N → MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ)
    (hjets : ∀ m, m ≤ 6 →
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPart3 m (Q i))) ≤
        motzkinJetMajorant r (Real.sqrt epsilon) m) :
    |MvPolynomial.eval v (motzkinSosSixError Q)| ≤
      6 * motzkinPairErrorBound r epsilon := by
  have hp (m n : ℕ) (hm : m ≤ 6) (hn : n ≤ 6)
      (hne : m ≠ 3 ∨ n ≠ 3) (hsum : m + n = 6) :
      |∑ i : Fin N, MvPolynomial.eval v (homogeneousPart3 m (Q i)) *
          MvPolynomial.eval v (homogeneousPart3 n (Q i))| ≤
        motzkinPairErrorBound r epsilon :=
    abs_eval_jet_pair_le hr2 hrho hrhoOne hsqrt hsmall Q v hjets hm hn
      (Or.inr ⟨hsum, hne⟩)
  rw [motzkinSosSixError_expansion, map_sum]
  simp_rw [map_add, map_mul]
  repeat' rw [Finset.sum_add_distrib]
  let a := ∑ i : Fin N, MvPolynomial.eval v (homogeneousPart3 0 (Q i)) *
    MvPolynomial.eval v (homogeneousPart3 6 (Q i))
  let b := ∑ i : Fin N, MvPolynomial.eval v (homogeneousPart3 1 (Q i)) *
    MvPolynomial.eval v (homogeneousPart3 5 (Q i))
  let c := ∑ i : Fin N, MvPolynomial.eval v (homogeneousPart3 2 (Q i)) *
    MvPolynomial.eval v (homogeneousPart3 4 (Q i))
  let d := ∑ i : Fin N, MvPolynomial.eval v (homogeneousPart3 4 (Q i)) *
    MvPolynomial.eval v (homogeneousPart3 2 (Q i))
  let e := ∑ i : Fin N, MvPolynomial.eval v (homogeneousPart3 5 (Q i)) *
    MvPolynomial.eval v (homogeneousPart3 1 (Q i))
  let f := ∑ i : Fin N, MvPolynomial.eval v (homogeneousPart3 6 (Q i)) *
    MvPolynomial.eval v (homogeneousPart3 0 (Q i))
  change |a + b + c + d + e + f| ≤ _
  have ha : |a| ≤ motzkinPairErrorBound r epsilon :=
    hp 0 6 (by omega) (by omega) (Or.inl (by omega)) (by omega)
  have hb : |b| ≤ motzkinPairErrorBound r epsilon :=
    hp 1 5 (by omega) (by omega) (Or.inl (by omega)) (by omega)
  have hc : |c| ≤ motzkinPairErrorBound r epsilon :=
    hp 2 4 (by omega) (by omega) (Or.inl (by omega)) (by omega)
  have hd : |d| ≤ motzkinPairErrorBound r epsilon :=
    hp 4 2 (by omega) (by omega) (Or.inl (by omega)) (by omega)
  have he : |e| ≤ motzkinPairErrorBound r epsilon :=
    hp 5 1 (by omega) (by omega) (Or.inl (by omega)) (by omega)
  have hf : |f| ≤ motzkinPairErrorBound r epsilon :=
    hp 6 0 (by omega) (by omega) (Or.inl (by omega)) (by omega)
  exact (abs_add6_le a b c d e f).trans (by linarith)

lemma abs_add7_le (a b c d e f g : ℝ) :
    |a + b + c + d + e + f + g| ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
  calc
    |a + b + c + d + e + f + g| ≤ |a + b + c + d + e + f| + |g| := abs_add_le _ _
    _ ≤ (|a| + |b| + |c| + |d| + |e| + |f|) + |g| := by
      gcongr
      exact abs_add6_le a b c d e f

lemma abs_eval_motzkinWeightedSixError_le
    {N r : ℕ} {epsilon rho : ℝ}
    (hr2 : 2 ≤ r) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hsqrt : Real.sqrt epsilon = rho ^ 3) (hsmall : (r : ℝ) * rho ≤ 1 / 8)
    (J : Finset (Fin 3)) (Q : Fin N → MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ)
    (hv : motzkinSqNorm v = 1)
    (hjets : ∀ m, m ≤ 6 →
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPart3 m (Q i))) ≤
        motzkinJetMajorant r (Real.sqrt epsilon) m) :
    |MvPolynomial.eval v (motzkinWeightedSixError J Q)| ≤
      294 * motzkinPairErrorBound r epsilon := by
  have hsos (d : ℕ) (hd : d ≤ 5) :
      |MvPolynomial.eval v (homogeneousPart3 d (sosVectorSq3 Q))| ≤
        6 * motzkinPairErrorBound r epsilon :=
    abs_eval_sos_component_below_six_le hr2 hrho hrhoOne hsqrt hsmall hd Q v hjets
  have hterm (d e : ℕ) (he : e ≤ 5) :
      |MvPolynomial.eval v (homogeneousPart3 d (BoxSemialgebraicGeneratorProd J) *
        homogeneousPart3 e (sosVectorSq3 Q))| ≤
        48 * motzkinPairErrorBound r epsilon := by
    rw [MvPolynomial.eval_mul, abs_mul]
    exact (mul_le_mul (abs_eval_homogeneousPart3_boxGeneratorProd_le_eight J d v hv)
      (hsos e he) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  rw [motzkinWeightedSixError_expansion]
  simp only [map_add, map_mul]
  let a := MvPolynomial.eval v (motzkinSosSixError Q)
  let b := MvPolynomial.eval v (homogeneousPart3 1 (BoxSemialgebraicGeneratorProd J)) *
    MvPolynomial.eval v (homogeneousPart3 5 (sosVectorSq3 Q))
  let c := MvPolynomial.eval v (homogeneousPart3 2 (BoxSemialgebraicGeneratorProd J)) *
    MvPolynomial.eval v (homogeneousPart3 4 (sosVectorSq3 Q))
  let d := MvPolynomial.eval v (homogeneousPart3 3 (BoxSemialgebraicGeneratorProd J)) *
    MvPolynomial.eval v (homogeneousPart3 3 (sosVectorSq3 Q))
  let e := MvPolynomial.eval v (homogeneousPart3 4 (BoxSemialgebraicGeneratorProd J)) *
    MvPolynomial.eval v (homogeneousPart3 2 (sosVectorSq3 Q))
  let f := MvPolynomial.eval v (homogeneousPart3 5 (BoxSemialgebraicGeneratorProd J)) *
    MvPolynomial.eval v (homogeneousPart3 1 (sosVectorSq3 Q))
  let g := MvPolynomial.eval v (homogeneousPart3 6 (BoxSemialgebraicGeneratorProd J)) *
    MvPolynomial.eval v (homogeneousPart3 0 (sosVectorSq3 Q))
  change |a + b + c + d + e + f + g| ≤ _
  have ha : |a| ≤ 6 * motzkinPairErrorBound r epsilon :=
    abs_eval_motzkinSosSixError_le hr2 hrho hrhoOne hsqrt hsmall Q v hjets
  have hb : |b| ≤ 48 * motzkinPairErrorBound r epsilon := by
    simpa [b, MvPolynomial.eval_mul] using hterm 1 5 (by omega)
  have hc : |c| ≤ 48 * motzkinPairErrorBound r epsilon := by
    simpa [c, MvPolynomial.eval_mul] using hterm 2 4 (by omega)
  have hd : |d| ≤ 48 * motzkinPairErrorBound r epsilon := by
    simpa [d, MvPolynomial.eval_mul] using hterm 3 3 (by omega)
  have he : |e| ≤ 48 * motzkinPairErrorBound r epsilon := by
    simpa [e, MvPolynomial.eval_mul] using hterm 4 2 (by omega)
  have hf : |f| ≤ 48 * motzkinPairErrorBound r epsilon := by
    simpa [f, MvPolynomial.eval_mul] using hterm 5 1 (by omega)
  have hg : |g| ≤ 48 * motzkinPairErrorBound r epsilon := by
    simpa [g, MvPolynomial.eval_mul] using hterm 6 0 (by omega)
  exact (abs_add7_le a b c d e f g).trans (by linarith)

/-- The Motzkin target is homogeneous of degree six. -/
theorem motzkinSextic_isHomogeneous : motzkinSextic.IsHomogeneous 6 := by
  have hx2 : (X (0 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 :=
    MvPolynomial.isHomogeneous_X_pow _ _
  have hx4 : (X (0 : Fin 3) ^ 4 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 4 :=
    MvPolynomial.isHomogeneous_X_pow _ _
  have hy2 : (X (1 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 :=
    MvPolynomial.isHomogeneous_X_pow _ _
  have hy4 : (X (1 : Fin 3) ^ 4 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 4 :=
    MvPolynomial.isHomogeneous_X_pow _ _
  have hz2 : (X (2 : Fin 3) ^ 2 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 2 :=
    MvPolynomial.isHomogeneous_X_pow _ _
  have hz6 : (X (2 : Fin 3) ^ 6 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 6 :=
    MvPolynomial.isHomogeneous_X_pow _ _
  have hcross :
      (3 * X (0 : Fin 3) ^ 2 * X (1 : Fin 3) ^ 2 * X (2 : Fin 3) ^ 2 :
        MvPolynomial (Fin 3) ℝ).IsHomogeneous 6 := by
    rw [show (3 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (3 : ℝ) from
      (MvPolynomial.C_eq_coe_nat 3).symm]
    simpa [Nat.add_assoc] using (((hx2.C_mul 3).mul hy2).mul hz2)
  simpa [motzkinSextic, Nat.add_assoc] using
    (((hx4.mul hy2).add (hx2.mul hy4)).add hz6).sub hcross

@[simp] lemma homogeneousPart3_motzkinSextic :
    homogeneousPart3 6 motzkinSextic = motzkinSextic := by
  rw [homogeneousPart3_eq_homogeneousComponent]
  exact MvPolynomial.homogeneousComponent_eq_self motzkinSextic_isHomogeneous

lemma homogeneousPart3_C_six (epsilon : ℝ) :
    homogeneousPart3 6 (MvPolynomial.C epsilon : MvPolynomial (Fin 3) ℝ) = 0 := by
  ext α
  rw [coeff_homogeneousPart3]
  by_cases hα : α = 0
  · subst α
    simp
  · have h0α : (0 : Fin 3 →₀ ℕ) ≠ α := fun h ↦ hα h.symm
    simp [MvPolynomial.coeff_C, h0α]

lemma homogeneousPart3_motzkinPerturbed (epsilon : ℝ) :
    homogeneousPart3 6 (motzkinPerturbed epsilon) = motzkinSextic := by
  rw [motzkinPerturbed, homogeneousPart3_add, homogeneousPart3_motzkinSextic,
    homogeneousPart3_C_six, add_zero]

lemma motzkinDegreeSixError_eq_sum_weighted
    {N : Finset (Fin 3) → ℕ}
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ)
    (sigma : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ)
    (epsilon : ℝ)
    (hsigma : ∀ J, sigma J = sosVectorSq3 (Q J))
    (hsum : motzkinPerturbed epsilon =
      ∑ J ∈ Finset.univ.powerset, sigma J * BoxSemialgebraicGeneratorProd J) :
    motzkinDegreeSixError Q =
      ∑ J ∈ Finset.univ.powerset, motzkinWeightedSixError J (Q J) := by
  have hdegree :
      motzkinSextic = ∑ J ∈ Finset.univ.powerset,
        homogeneousPart3 6
          (BoxSemialgebraicGeneratorProd J * sosVectorSq3 (Q J)) := by
    calc
      motzkinSextic = homogeneousPart3 6 (motzkinPerturbed epsilon) :=
        (homogeneousPart3_motzkinPerturbed epsilon).symm
      _ = homogeneousPart3 6
          (∑ J ∈ Finset.univ.powerset,
            sigma J * BoxSemialgebraicGeneratorProd J) := by rw [hsum]
      _ = ∑ J ∈ Finset.univ.powerset,
          homogeneousPart3 6 (sigma J * BoxSemialgebraicGeneratorProd J) := by
        exact homogeneousPart3_sum 6 Finset.univ.powerset
          (fun J ↦ sigma J * BoxSemialgebraicGeneratorProd J)
      _ = ∑ J ∈ Finset.univ.powerset,
          homogeneousPart3 6
            (BoxSemialgebraicGeneratorProd J * sosVectorSq3 (Q J)) := by
        apply Finset.sum_congr rfl
        intro J _
        rw [hsigma J, mul_comm]
  unfold motzkinDegreeSixError motzkinCubicJetSOS motzkinWeightedSixError
  rw [Finset.sum_sub_distrib]
  rw [hdegree]

theorem motzkinDegreeSixError_unit_eval_le
    {N : Finset (Fin 3) → ℕ} {r : ℕ} {epsilon rho : ℝ}
    (hr2 : 2 ≤ r) (heps : 0 < epsilon) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) (hsqrt : Real.sqrt epsilon = rho ^ 3)
    (hrhoSmall : rho < schmInteriorS / 2)
    (hsmall : (r : ℝ) * rho ≤ 1 / 8)
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ)
    (hdeg : ∀ J i, (Q J i).totalDegree ≤ r)
    (hlocal : ∀ J, ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      ∀ t : ℝ, |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin (N J) =>
          MvPolynomial.eval (fun j ↦ t * v j) (Q J i)) ≤
          schmInteriorLocalControlConst * (Real.sqrt epsilon + |t| ^ 3))
    (hzero : ∀ J, ∀ zi : Fin 6, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin (N J) =>
        MvPolynomial.eval (fun j ↦ t * motzkinZeroDirection zi j) (Q J i)) ≤
        schmInteriorLocalControlConst * Real.sqrt epsilon)
    (v : Fin 3 → ℝ) (hv : motzkinSqNorm v = 1) :
    |MvPolynomial.eval v
      (∑ J ∈ Finset.univ.powerset, motzkinWeightedSixError J (Q J))| ≤
      2352 * motzkinPairErrorBound r epsilon := by
  have hterm (J : Finset (Fin 3)) :
      |MvPolynomial.eval v (motzkinWeightedSixError J (Q J))| ≤
        294 * motzkinPairErrorBound r epsilon := by
    have hjets := motzkin_certificate_root_jet_eval_bounds heps hrho hsqrt hr2
      hrhoSmall hsmall (Q J) (hdeg J) (hlocal J) (hzero J) v hv
    exact abs_eval_motzkinWeightedSixError_le hr2 hrho hrhoOne hsqrt hsmall
      J (Q J) v hv (motzkin_root_jets_le_majorant hr2 heps (Q J) v hjets)
  rw [map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    ∑ J ∈ Finset.univ.powerset,
        |MvPolynomial.eval v (motzkinWeightedSixError J (Q J))| ≤
      ∑ _J ∈ Finset.univ.powerset, 294 * motzkinPairErrorBound r epsilon := by
        exact Finset.sum_le_sum fun J _ ↦ hterm J
    _ = 2352 * motzkinPairErrorBound r epsilon := by
      simp
      ring

lemma motzkinSqNorm_le_three_of_mem_cube
    (x : Fin 3 → ℝ) (hx : x ∈ Hypercube 3) :
    motzkinSqNorm x ≤ 3 := by
  rw [Hypercube_mem_iff] at hx
  have ha0 : |x 0| ≤ 1 := by rw [abs_le]; exact hx 0
  have ha1 : |x 1| ≤ 1 := by rw [abs_le]; exact hx 1
  have ha2 : |x 2| ≤ 1 := by rw [abs_le]; exact hx 2
  have hs0 : x 0 ^ 2 ≤ 1 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg (x 0)) (by norm_num : (0 : ℝ) ≤ 1)).2 ha0
  have hs1 : x 1 ^ 2 ≤ 1 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg (x 1)) (by norm_num : (0 : ℝ) ≤ 1)).2 ha1
  have hs2 : x 2 ^ 2 ≤ 1 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg (x 2)) (by norm_num : (0 : ℝ) ≤ 1)).2 ha2
  have hnorm : motzkinSqNorm x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    simp [motzkinSqNorm, Fin.sum_univ_succ]
    ring
  rw [hnorm]
  linarith

lemma homogeneous_six_cube_eval_le_of_unit
    (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous 6)
    {B : ℝ} (hB : 0 ≤ B)
    (hunit : ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      |MvPolynomial.eval v p| ≤ B)
    (x : Fin 3 → ℝ) (hx : x ∈ Hypercube 3) :
    |MvPolynomial.eval x p| ≤ 27 * B := by
  by_cases hx0 : x = 0
  · subst x
    let e : Fin 3 → ℝ := fun i ↦ if i = 0 then 1 else 0
    have hscale := isHomogeneous_eval_smul hp 0 e
    have heval : MvPolynomial.eval 0 p = 0 := by
      simpa [e] using hscale
    rw [heval, abs_zero]
    positivity
  · have hxpos : 0 < motzkinSqNorm x := motzkinSqNorm_pos_of_ne_zero hx0
    let c := Real.sqrt (motzkinSqNorm x)
    let u : Fin 3 → ℝ := fun i ↦ c⁻¹ * x i
    have hu : motzkinSqNorm u = 1 := by
      dsimp [u, c]
      exact motzkinSqNorm_normalize_eq_one hxpos
    have hcpos : 0 < c := Real.sqrt_pos.mpr hxpos
    have hcu : (fun i ↦ c * u i) = x := by
      funext i
      dsimp [u, c]
      field_simp [ne_of_gt hcpos]
    have hc2 : c ^ 2 = motzkinSqNorm x := Real.sq_sqrt hxpos.le
    have hc6 : c ^ 6 ≤ 27 := by
      calc
        c ^ 6 = (c ^ 2) ^ 3 := by ring
        _ = motzkinSqNorm x ^ 3 := by rw [hc2]
        _ ≤ (3 : ℝ) ^ 3 := pow_le_pow_left₀
          (motzkinSqNorm_nonneg x) (motzkinSqNorm_le_three_of_mem_cube x hx) 3
        _ = 27 := by norm_num
    have hscale := isHomogeneous_eval_smul hp c u
    rw [hcu] at hscale
    rw [hscale, abs_mul, abs_of_nonneg (pow_nonneg hcpos.le 6)]
    exact (mul_le_mul_of_nonneg_left (hunit u hu) (pow_nonneg hcpos.le 6)).trans
      (mul_le_mul_of_nonneg_right hc6 hB)

lemma motzkinCubicJetSOS_isHomogeneous
    {N : Finset (Fin 3) → ℕ}
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ) :
    (motzkinCubicJetSOS Q).IsHomogeneous 6 := by
  unfold motzkinCubicJetSOS sosVectorSq3 homogeneousPartVec3
  apply MvPolynomial.IsHomogeneous.sum
  intro J _
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  rw [homogeneousPart3_eq_homogeneousComponent]
  simpa using
    (MvPolynomial.homogeneousComponent_isHomogeneous 3 (Q J i)).pow 2

lemma motzkinDegreeSixError_isHomogeneous
    {N : Finset (Fin 3) → ℕ}
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ) :
    (motzkinDegreeSixError Q).IsHomogeneous 6 := by
  exact motzkinSextic_isHomogeneous.sub (motzkinCubicJetSOS_isHomogeneous Q)

@[simp] lemma homogeneousPart3_motzkinDegreeSixError
    {N : Finset (Fin 3) → ℕ}
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ) :
    homogeneousPart3 6 (motzkinDegreeSixError Q) = motzkinDegreeSixError Q := by
  rw [homogeneousPart3_eq_homogeneousComponent]
  exact MvPolynomial.homogeneousComponent_eq_self
    (motzkinDegreeSixError_isHomogeneous Q)

theorem motzkinDegreeSixError_coeffNorm_le
    {N : Finset (Fin 3) → ℕ} {r : ℕ} {epsilon rho : ℝ}
    (hr2 : 2 ≤ r) (heps : 0 < epsilon) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1) (hsqrt : Real.sqrt epsilon = rho ^ 3)
    (hrhoSmall : rho < schmInteriorS / 2)
    (hsmall : (r : ℝ) * rho ≤ 1 / 8)
    (Q : ∀ J, Fin (N J) → MvPolynomial (Fin 3) ℝ)
    (sigma : Finset (Fin 3) → MvPolynomial (Fin 3) ℝ)
    (hsigma : ∀ J, sigma J = sosVectorSq3 (Q J))
    (hsum : motzkinPerturbed epsilon =
      ∑ J ∈ Finset.univ.powerset, sigma J * BoxSemialgebraicGeneratorProd J)
    (hdeg : ∀ J i, (Q J i).totalDegree ≤ r)
    (hlocal : ∀ J, ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      ∀ t : ℝ, |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin (N J) =>
          MvPolynomial.eval (fun j ↦ t * v j) (Q J i)) ≤
          schmInteriorLocalControlConst * (Real.sqrt epsilon + |t| ^ 3))
    (hzero : ∀ J, ∀ zi : Fin 6, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin (N J) =>
        MvPolynomial.eval (fun j ↦ t * motzkinZeroDirection zi j) (Q J i)) ≤
        schmInteriorLocalControlConst * Real.sqrt epsilon) :
    motzkinCoeffNorm (motzkinDegreeSixError Q) ≤
      motzkinDegreeSixNormConst *
        (27 * (2352 * motzkinPairErrorBound r epsilon)) := by
  have hpair : 0 ≤ motzkinPairErrorBound r epsilon :=
    motzkinPairErrorBound_nonneg r epsilon
  apply motzkinCoeffNorm_homogeneous_six_le_cube_bound
    (motzkinDegreeSixError Q) (homogeneousPart3_motzkinDegreeSixError Q)
  · positivity
  intro x hx
  apply homogeneous_six_cube_eval_le_of_unit
    (motzkinDegreeSixError Q) (motzkinDegreeSixError_isHomogeneous Q) (by positivity)
  · intro v hv
    rw [motzkinDegreeSixError_eq_sum_weighted Q sigma epsilon hsigma hsum]
    exact motzkinDegreeSixError_unit_eval_le hr2 heps hrho hrhoOne hsqrt hrhoSmall
      hsmall Q hdeg hlocal hzero v hv
  · exact hx

end Motzkin

end OptimalConvergenceRates

end
