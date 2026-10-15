/- The matching lower bound for the fixed bivariate Schmüdgen example. -/
import OptimalConvergenceRates.GeneralCompact.SharpBivariate.Geometry
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.LowerBound
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Common.VectorPolynomialEstimates

noncomputable section

open Finset MvPolynomial Filter Asymptotics

namespace OptimalConvergenceRates.GeneralCompact

/-- The SOS multipliers in a bivariate preordering certificate. -/
def SharpPreorderingCertificate (epsilon : ℝ) (r : ℕ) : Prop :=
  ∃ sigma : Finset (Fin 2) → MvPolynomial (Fin 2) ℝ,
    (∀ J, IsSOS (sigma J)) ∧
    (∀ J, (sigma J * ∏ j ∈ J, sharpGenerators j).totalDegree ≤ r) ∧
    sharpObjective + C epsilon =
      ∑ J ∈ Finset.univ.powerset,
        sigma J * ∏ j ∈ J, sharpGenerators j

/-- Expose the witnesses in a truncated preordering certificate. -/
theorem sharpPreorderingCertificate_of_mem
    {epsilon : ℝ} {r : ℕ}
    (hcert : sharpObjective + C epsilon ∈
      GenPreordering sharpGenerators r) :
    SharpPreorderingCertificate epsilon r := by
  exact hcert

/-- Restrict a bivariate polynomial to the `a`-line at fixed `z`. -/
def sharpRestrictA (z : ℝ) (p : MvPolynomial (Fin 2) ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C z] p

@[simp] theorem sharpRestrictA_eval (a z : ℝ)
    (p : MvPolynomial (Fin 2) ℝ) :
    (sharpRestrictA z p).eval a = MvPolynomial.eval ![a, z] p := by
  rw [sharpRestrictA]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
        Polynomial.eval_mul]
      rw [hp]
      congr 1
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem sharpRestrictA_natDegree_le (z : ℝ)
    (p : MvPolynomial (Fin 2) ℝ) :
    (sharpRestrictA z p).natDegree ≤ p.totalDegree := by
  have h := MvPolynomial.aeval_natDegree_le p (le_refl p.totalDegree)
    ![Polynomial.X, Polynomial.C z] (n := 1) (by
      intro i
      fin_cases i <;> simp)
  simpa [sharpRestrictA] using h

/-- Restrict a bivariate polynomial to the `z`-line at fixed `a`. -/
def sharpRestrictZAt (a : ℝ) (p : MvPolynomial (Fin 2) ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval ![Polynomial.C a, Polynomial.X] p

@[simp] theorem sharpRestrictZAt_eval (a z : ℝ)
    (p : MvPolynomial (Fin 2) ℝ) :
    (sharpRestrictZAt a p).eval z = MvPolynomial.eval ![a, z] p := by
  rw [sharpRestrictZAt]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
        Polynomial.eval_mul]
      rw [hp]
      congr 1
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem sharpRestrictZAt_natDegree_le (a : ℝ)
    (p : MvPolynomial (Fin 2) ℝ) :
    (sharpRestrictZAt a p).natDegree ≤ p.totalDegree := by
  have h := MvPolynomial.aeval_natDegree_le p (le_refl p.totalDegree)
    ![Polynomial.C a, Polynomial.X] (n := 1) (by
      intro i
      fin_cases i <;> simp)
  simpa [sharpRestrictZAt] using h

@[simp] theorem eval_sharpH (a z : ℝ) :
    MvPolynomial.eval ![a, z] sharpH = z * (a ^ 2 + z ^ 2) := by
  simp [sharpH, sharpA, sharpZ]

@[simp] theorem eval_sharpBall (a z : ℝ) :
    MvPolynomial.eval ![a, z] sharpBall = 1 - a ^ 2 - z ^ 2 := by
  simp [sharpBall, sharpA, sharpZ]

theorem sharpH_ne_zero : sharpH ≠ (0 : MvPolynomial (Fin 2) ℝ) := by
  intro h
  have h' := congr_arg (MvPolynomial.eval ![(0 : ℝ), (1 : ℝ)]) h
  norm_num at h'

theorem sharpBall_ne_zero : sharpBall ≠ (0 : MvPolynomial (Fin 2) ℝ) := by
  intro h
  have h' := congr_arg (MvPolynomial.eval ![(0 : ℝ), (0 : ℝ)]) h
  norm_num at h'

private theorem sharpGeneratorProd_ne_zero (J : Finset (Fin 2)) :
    (∏ j ∈ J, sharpGenerators j) ≠
      (0 : MvPolynomial (Fin 2) ℝ) := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  fin_cases i
  · simpa [sharpGenerators] using sharpH_ne_zero
  · simpa [sharpGenerators] using sharpBall_ne_zero

private theorem sharpMultiplier_totalDegree_le
    {sigma : Finset (Fin 2) → MvPolynomial (Fin 2) ℝ} {r : ℕ}
    (hdegree : ∀ J,
      (sigma J * ∏ j ∈ J, sharpGenerators j).totalDegree ≤ r) (J) :
    (sigma J).totalDegree ≤ r := by
  by_cases hsigma : sigma J = 0
  · simp [hsigma]
  · have hmul := MvPolynomial.totalDegree_mul_of_isDomain hsigma
      (sharpGeneratorProd_ne_zero J)
    have hw := hdegree J
    omega

private theorem sharpGenerator_nonneg_on_rectangle
    {a z : ℝ} (ha : |a| ≤ 1 / 4) (hz0 : 0 ≤ z) (hz4 : z ≤ 1 / 4)
    (i : Fin 2) :
    0 ≤ MvPolynomial.eval ![a, z] (sharpGenerators i) := by
  fin_cases i
  · change 0 ≤ MvPolynomial.eval ![a, z] sharpH
    rw [eval_sharpH]
    exact mul_nonneg hz0 (add_nonneg (sq_nonneg _) (sq_nonneg _))
  · change 0 ≤ MvPolynomial.eval ![a, z] sharpBall
    rw [eval_sharpBall]
    have ha4 : -(1 / 4 : ℝ) ≤ a ∧ a ≤ 1 / 4 := abs_le.mp ha
    nlinarith [sq_nonneg (a + 1 / 4), sq_nonneg (a - 1 / 4),
      sq_nonneg z]

private theorem sharpCertificate_term_nonneg
    {sigma : Finset (Fin 2) → MvPolynomial (Fin 2) ℝ}
    (hsos : ∀ J, IsSOS (sigma J))
    {a z : ℝ} (ha : |a| ≤ 1 / 4) (hz0 : 0 ≤ z) (hz4 : z ≤ 1 / 4)
    (J : Finset (Fin 2)) :
    0 ≤ MvPolynomial.eval ![a, z]
      (sigma J * ∏ j ∈ J, sharpGenerators j) := by
  rw [map_mul, map_prod]
  apply mul_nonneg
  · exact IsSOS_nonneg (sigma J) (hsos J) _ (Set.mem_univ _)
  · apply Finset.prod_nonneg
    intro i hi
    exact sharpGenerator_nonneg_on_rectangle ha hz0 hz4 i

/-- On the positive slab, each of the two terms containing the cubic
generator gives a uniform weighted bound for its SOS multiplier. -/
theorem sharpCertificate_weighted_multiplier_bounds
    {epsilon t : ℝ}
    (hepsilon : 0 < epsilon) (ht : t = 2 * epsilon)
    {sigma : Finset (Fin 2) → MvPolynomial (Fin 2) ℝ}
    (hsos : ∀ J, IsSOS (sigma J))
    (hidentity : sharpObjective + C epsilon =
      ∑ J ∈ Finset.univ.powerset,
        sigma J * ∏ j ∈ J, sharpGenerators j)
    {a z : ℝ} (ha : |a| ≤ 1 / 4) (hz : t ≤ z) (hz4 : z ≤ 1 / 4) :
    a ^ 2 * MvPolynomial.eval ![a, z] (sigma {0}) ≤ 2 ∧
    a ^ 2 * MvPolynomial.eval ![a, z] (sigma {0, 1}) ≤ 2 := by
  have ht0 : 0 < t := by rw [ht]; positivity
  have hz0 : 0 ≤ z := ht0.le.trans hz
  have hsigma0 : 0 ≤ MvPolynomial.eval ![a, z] (sigma {0}) :=
    IsSOS_nonneg _ (hsos {0}) _ (Set.mem_univ _)
  have hsigma01 : 0 ≤ MvPolynomial.eval ![a, z] (sigma {0, 1}) :=
    IsSOS_nonneg _ (hsos {0, 1}) _ (Set.mem_univ _)
  have hball : (7 / 8 : ℝ) ≤ 1 - a ^ 2 - z ^ 2 := by
    have ha' := abs_le.mp ha
    nlinarith [sq_nonneg (a + 1 / 4), sq_nonneg (a - 1 / 4),
      sq_nonneg z, sq_nonneg (z - 1 / 4)]
  have hwhole :
      MvPolynomial.eval ![a, z]
          (∑ J ∈ Finset.univ.powerset,
            sigma J * ∏ j ∈ J, sharpGenerators j) = z + epsilon := by
    rw [← hidentity]
    simp [sharpObjective, sharpZ]
  have hterm (J : Finset (Fin 2))
      (hJ : J ∈ (Finset.univ : Finset (Fin 2)).powerset) :
      MvPolynomial.eval ![a, z]
          (sigma J * ∏ j ∈ J, sharpGenerators j) ≤ z + epsilon := by
    rw [← hwhole, map_sum]
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 2)).powerset)
      (f := fun K => MvPolynomial.eval ![a, z]
        (sigma K * ∏ j ∈ K, sharpGenerators j))
      (fun K hK =>
        sharpCertificate_term_nonneg hsos ha hz0 hz4 K) hJ
  have hH := hterm {0} (by simp)
  have hHB := hterm {0, 1} (by simp)
  simp only [map_mul, map_prod] at hH hHB
  norm_num [sharpGenerators] at hH hHB
  have hepsz : epsilon ≤ z / 2 := by rw [ht] at hz; linarith
  constructor
  · have hfac : z * a ^ 2 ≤ z * (a ^ 2 + z ^ 2) := by
      nlinarith [sq_nonneg z]
    nlinarith [mul_le_mul_of_nonneg_left hfac hsigma0]
  · have hfac :
        z * a ^ 2 * (7 / 8 : ℝ) ≤
          z * (a ^ 2 + z ^ 2) * (1 - a ^ 2 - z ^ 2) := by
      have hleft := mul_le_mul_of_nonneg_left hball
        (mul_nonneg hz0 (add_nonneg (sq_nonneg a) (sq_nonneg z)))
      have hquad : z * a ^ 2 ≤ z * (a ^ 2 + z ^ 2) := by
        nlinarith [sq_nonneg z]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hfac hsigma01]

/-- Vector Bernstein turns a bound for a squared weighted multiplier into
a quadratic degree bound for its face value. -/
theorem sharpSOS_face_bound
    {sigma : MvPolynomial (Fin 2) ℝ} {r : ℕ} {z : ℝ}
    (hsos : IsSOS sigma) (hdegree : sigma.totalDegree ≤ r)
    (hweighted : ∀ a : ℝ, |a| ≤ 1 / 4 →
      a ^ 2 * MvPolynomial.eval ![a, z] sigma ≤ 2) :
    MvPolynomial.eval ![(0 : ℝ), z] sigma ≤
      (16 * ((r : ℝ) + 1)) ^ 2 := by
  obtain ⟨N, P, hP⟩ := hsos
  have hPdegree : ∀ i : Fin N, (P i).totalDegree ≤ r := by
    apply sos_summand_totalDegree_le_of_sum_sq_totalDegree hP
    omega
  let Q : Fin N → Polynomial ℝ :=
    fun i => Polynomial.X * sharpRestrictA z (P i)
  have hQdegree : ∀ i : Fin N, (Q i).natDegree ≤ r + 1 := by
    intro i
    dsimp [Q]
    calc
      (Polynomial.X * sharpRestrictA z (P i)).natDegree ≤
          Polynomial.X.natDegree +
            (sharpRestrictA z (P i)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 + (P i).totalDegree := by
        rw [Polynomial.natDegree_X]
        exact Nat.add_le_add_left
          (sharpRestrictA_natDegree_le z (P i)) 1
      _ ≤ 1 + r := Nat.add_le_add_left (hPdegree i) 1
      _ = r + 1 := by omega
  have hQbound : ∀ a : ℝ, |a| ≤ 1 / 4 →
      interiorVecNorm (fun i : Fin N => (Q i).eval a) ≤ 2 := by
    intro a ha
    have hsq : interiorVecSqNorm (fun i : Fin N => (Q i).eval a) =
        a ^ 2 * MvPolynomial.eval ![a, z] sigma := by
      unfold interiorVecSqNorm
      dsimp [Q]
      rw [hP, map_sum]
      simp only [map_pow, Polynomial.eval_mul, Polynomial.eval_X,
        sharpRestrictA_eval]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hsqle : interiorVecSqNorm (fun i : Fin N => (Q i).eval a) ≤
        (2 : ℝ) ^ 2 := by
      rw [hsq]
      have hw := hweighted a ha
      norm_num at hw ⊢
      linarith
    simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
      (vecNorm_le_of_vecSqNorm_le (v := fun i : Fin N => (Q i).eval a)
        (by norm_num : (0 : ℝ) ≤ 2) (by
          simpa [interiorVecSqNorm, vecSqNorm] using hsqle))
  have hbern := interior_bernstein_vector_first_derivative_radius Q
    (s := (1 / 4 : ℝ)) (M := (2 : ℝ)) (k := r + 1)
    (by norm_num) (by norm_num) hQdegree hQbound
  have hderivative :
      (fun i : Fin N => (Polynomial.derivative (Q i)).eval 0) =
        fun i : Fin N => (sharpRestrictA z (P i)).eval 0 := by
    funext i
    dsimp [Q]
    simp [Polynomial.derivative_mul]
  rw [hderivative] at hbern
  have hnorm :
      interiorVecNorm
          (fun i : Fin N => (sharpRestrictA z (P i)).eval 0) ≤
        16 * ((r : ℝ) + 1) := by
    convert hbern using 1
    all_goals push_cast
    all_goals ring
  simp only [sharpRestrictA_eval] at hnorm
  rw [hP, map_sum]
  simp only [map_pow]
  have hnonneg :
      0 ≤ ∑ i : Fin N, MvPolynomial.eval ![(0 : ℝ), z] (P i) ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  unfold interiorVecNorm at hnorm
  unfold interiorVecSqNorm at hnorm
  have hsqrt := Real.sqrt_nonneg
    (∑ i : Fin N, MvPolynomial.eval ![(0 : ℝ), z] (P i) ^ 2)
  have hright : 0 ≤ 16 * ((r : ℝ) + 1) := by positivity
  nlinarith [Real.sq_sqrt hnonneg]

/-- Expand the preordering sum for the two fixed generators. -/
theorem sharpPreordering_sum_expand
    (sigma : Finset (Fin 2) → MvPolynomial (Fin 2) ℝ) :
    (∑ J ∈ (Finset.univ : Finset (Fin 2)).powerset,
        sigma J * ∏ j ∈ J, sharpGenerators j) =
      sigma ∅ + sigma {0} * sharpH + sigma {1} * sharpBall +
        sigma {0, 1} * (sharpH * sharpBall) := by
  classical
  have hpowerset : (Finset.univ : Finset (Fin 2)).powerset =
      {∅, {0}, {1}, {0, 1}} := by decide
  rw [hpowerset]
  rw [Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [sharpGenerators]
  ring_nf

/-- Common envelope for the two critical multipliers at the negative face. -/
def sharpNegativeFaceEnvelope (t : ℝ) (r : ℕ) : ℝ :=
  Real.exp (100 * (r : ℝ) * Real.sqrt t) *
    (16 * ((r : ℝ) + 1)) ^ 2

/-- Bernstein on the transverse variable followed by Chebyshev
extrapolation in the objective variable. -/
theorem sharpCertificate_negative_face_bounds
    {epsilon t : ℝ} {r : ℕ}
    (hr : 2 ≤ r) (hepsilon : 0 < epsilon) (ht : t = 2 * epsilon)
    (htsmall : t ≤ (1 : ℝ) / 64)
    {sigma : Finset (Fin 2) → MvPolynomial (Fin 2) ℝ}
    (hsos : ∀ J, IsSOS (sigma J))
    (hdegree : ∀ J,
      (sigma J * ∏ j ∈ J, sharpGenerators j).totalDegree ≤ r)
    (hidentity : sharpObjective + C epsilon =
      ∑ J ∈ Finset.univ.powerset,
        sigma J * ∏ j ∈ J, sharpGenerators j) :
    MvPolynomial.eval ![(0 : ℝ), -t] (sigma {0}) ≤
        sharpNegativeFaceEnvelope t r ∧
      MvPolynomial.eval ![(0 : ℝ), -t] (sigma {0, 1}) ≤
        sharpNegativeFaceEnvelope t r := by
  have ht0 : 0 < t := by rw [ht]; positivity
  have hface (J : Finset (Fin 2))
      (hselect : ∀ {a z : ℝ}, |a| ≤ 1 / 4 → t ≤ z → z ≤ 1 / 4 →
        a ^ 2 * MvPolynomial.eval ![a, z] (sigma J) ≤ 2) :
      ∀ z : ℝ, t ≤ z → z ≤ 1 / 4 →
        MvPolynomial.eval ![(0 : ℝ), z] (sigma J) ≤
          (16 * ((r : ℝ) + 1)) ^ 2 := by
    intro z hz hz4
    exact sharpSOS_face_bound (hsos J)
      (sharpMultiplier_totalDegree_le hdegree J)
      (fun a ha => hselect ha hz hz4)
  have hextrapolate (J : Finset (Fin 2))
      (hfaceJ : ∀ z : ℝ, t ≤ z → z ≤ 1 / 4 →
        MvPolynomial.eval ![(0 : ℝ), z] (sigma J) ≤
          (16 * ((r : ℝ) + 1)) ^ 2) :
      MvPolynomial.eval ![(0 : ℝ), -t] (sigma J) ≤
        sharpNegativeFaceEnvelope t r := by
    let p := sharpRestrictZAt 0 (sigma J)
    have hpdeg : p.natDegree ≤ r :=
      (sharpRestrictZAt_natDegree_le 0 (sigma J)).trans
        (sharpMultiplier_totalDegree_le hdegree J)
    have hpbound : ∀ z : ℝ, t ≤ z → z ≤ 1 / 4 →
        |p.eval z| ≤ (16 * ((r : ℝ) + 1)) ^ 2 := by
      intro z hz hz4
      rw [sharpRestrictZAt_eval]
      rw [abs_of_nonneg
        (IsSOS_nonneg _ (hsos J) _ (Set.mem_univ _))]
      exact hfaceJ z hz hz4
    have hext :=
      GeneralArchimedean.polynomial_extrapolate_negative_slab
        hr ht0 htsmall p hpdeg hpbound
    rw [sharpRestrictZAt_eval] at hext
    exact (le_abs_self _).trans (by
      simpa [sharpNegativeFaceEnvelope] using hext)
  have hweighted := fun {a z : ℝ} (ha : |a| ≤ 1 / 4)
      (hz : t ≤ z) (hz4 : z ≤ 1 / 4) =>
    sharpCertificate_weighted_multiplier_bounds hepsilon ht hsos
      hidentity ha hz hz4
  exact ⟨hextrapolate {0} (hface {0} (fun ha hz hz4 =>
      (hweighted ha hz hz4).1)),
    hextrapolate {0, 1} (hface {0, 1} (fun ha hz hz4 =>
      (hweighted ha hz hz4).2))⟩

/-- Evaluation at the reflected point forces the quantitative obstruction
that will be inverted asymptotically. -/
theorem sharpCertificate_forces_growth
    {epsilon t : ℝ} {r : ℕ}
    (hr : 2 ≤ r) (hepsilon : 0 < epsilon) (ht : t = 2 * epsilon)
    (htsmall : t ≤ (1 : ℝ) / 64)
    (hcert : sharpObjective + C epsilon ∈
      GenPreordering sharpGenerators r) :
    1 ≤ 4 * t ^ 2 * sharpNegativeFaceEnvelope t r := by
  obtain ⟨sigma, hsos, hdegree, hidentity⟩ :=
    sharpPreorderingCertificate_of_mem hcert
  have hnegative := sharpCertificate_negative_face_bounds hr hepsilon ht
    htsmall hsos hdegree hidentity
  have ht0 : 0 < t := by rw [ht]; positivity
  have htSq : t ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg t]
  have hball0 : 0 ≤ 1 - t ^ 2 := by linarith
  have hball1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  let sigmaZero := MvPolynomial.eval ![(0 : ℝ), -t] (sigma ∅)
  let sigmaH := MvPolynomial.eval ![(0 : ℝ), -t] (sigma {0})
  let sigmaBall := MvPolynomial.eval ![(0 : ℝ), -t] (sigma {1})
  let sigmaHBall := MvPolynomial.eval ![(0 : ℝ), -t] (sigma {0, 1})
  have hsigmaZero : 0 ≤ sigmaZero :=
    IsSOS_nonneg _ (hsos ∅) _ (Set.mem_univ _)
  have hsigmaH : 0 ≤ sigmaH :=
    IsSOS_nonneg _ (hsos {0}) _ (Set.mem_univ _)
  have hsigmaBall : 0 ≤ sigmaBall :=
    IsSOS_nonneg _ (hsos {1}) _ (Set.mem_univ _)
  have hsigmaHBall : 0 ≤ sigmaHBall :=
    IsSOS_nonneg _ (hsos {0, 1}) _ (Set.mem_univ _)
  have hHbound : sigmaH ≤ sharpNegativeFaceEnvelope t r := by
    exact hnegative.1
  have hHBallBound : sigmaHBall ≤ sharpNegativeFaceEnvelope t r := by
    exact hnegative.2
  rw [sharpPreordering_sum_expand] at hidentity
  have heval := congr_arg
    (MvPolynomial.eval ![(0 : ℝ), -t]) hidentity
  simp only [map_add, map_mul] at heval
  norm_num [sharpObjective, sharpZ] at heval
  change -t + epsilon =
    sigmaZero + -(sigmaH * (t * t ^ 2)) +
      sigmaBall * (1 - t ^ 2) +
        -(sigmaHBall * (t * t ^ 2 * (1 - t ^ 2))) at heval
  have hepsilonEq : epsilon = t / 2 := by rw [ht]; ring
  rw [hepsilonEq] at heval
  have henvelope0 : 0 ≤ sharpNegativeFaceEnvelope t r := by
    unfold sharpNegativeFaceEnvelope
    positivity
  have hcritical :
      t / 2 ≤ t ^ 3 * (sigmaH + (1 - t ^ 2) * sigmaHBall) := by
    nlinarith [mul_nonneg hsigmaBall hball0]
  have hcriticalUpper :
      t ^ 3 * (sigmaH + (1 - t ^ 2) * sigmaHBall) ≤
        2 * t ^ 3 * sharpNegativeFaceEnvelope t r := by
    have ht3 : 0 ≤ t ^ 3 := by positivity
    have hweighted :
        sigmaH + (1 - t ^ 2) * sigmaHBall ≤
          2 * sharpNegativeFaceEnvelope t r := by
      nlinarith [mul_le_mul_of_nonneg_right hHBallBound hball0,
        mul_le_mul_of_nonneg_right hball1 hsigmaHBall]
    nlinarith [mul_le_mul_of_nonneg_left hweighted ht3]
  nlinarith [mul_nonneg (sq_nonneg t) henvelope0]

/-- A fixed positive constant for the bivariate preordering lower bound. -/
def sharpCompactLowerConstant : ℝ :=
  1 / (2 * (10 : ℝ) ^ 20)

theorem sharpCompact_logTwo_over_sq_lower_pos :
    ∃ r0 : ℕ, 0 < r0 ∧
      ∀ r, r0 ≤ r → ∀ epsilon : ℝ, 0 < epsilon →
        sharpObjective + C epsilon ∈ GenPreordering sharpGenerators r →
          sharpCompactLowerConstant * logTwoOverSq r ≤ epsilon := by
  obtain ⟨r0, hr0⟩ := eventually_atTop.mp
    GeneralArchimedean.eventually_sharpLowerConditions
  refine ⟨max r0 1, by omega, ?_⟩
  intro r hrr epsilon hepsilon hcert
  have hcond := hr0 r (le_trans (le_max_left r0 1) hrr)
  rcases hcond with ⟨hr, hlogLarge, hdom, hrateFour⟩
  by_contra hnot
  have hepsilonLt :
      epsilon < sharpCompactLowerConstant * logTwoOverSq r :=
    lt_of_not_ge hnot
  have hmax : max r 2 = r := max_eq_left (by omega)
  have hrR : (0 : ℝ) < (r : ℝ) := by positivity
  have hlogPos : 0 < Real.log (r : ℝ) := by linarith
  have hrateEq : logTwoOverSq r =
      Real.log (r : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
    simp [logTwoOverSq, hmax]
  have hrateNonneg : 0 ≤ logTwoOverSq r := by
    rw [hrateEq]
    positivity
  have hrateOne : logTwoOverSq r ≤ 1 := by
    have hfourEq : GeneralArchimedean.logFourOverSq r =
        Real.log (r : ℝ) ^ 4 / (r : ℝ) ^ 2 := by
      simp [GeneralArchimedean.logFourOverSq, hmax]
    rw [hfourEq] at hrateFour
    rw [hrateEq]
    have hpow : Real.log (r : ℝ) ^ 2 ≤
        Real.log (r : ℝ) ^ 4 := by
      nlinarith [sq_nonneg (Real.log (r : ℝ) ^ 2 - 1)]
    exact (div_le_div_of_nonneg_right hpow (sq_nonneg _)).trans hrateFour
  let t : ℝ := 2 * epsilon
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htRate : t <
      Real.log (r : ℝ) ^ 2 /
        ((10 : ℝ) ^ 20 * (r : ℝ) ^ 2) := by
    calc
      t < 2 * (sharpCompactLowerConstant * logTwoOverSq r) := by
        dsimp [t]
        linarith
      _ = Real.log (r : ℝ) ^ 2 /
          ((10 : ℝ) ^ 20 * (r : ℝ) ^ 2) := by
        rw [hrateEq]
        unfold sharpCompactLowerConstant
        field_simp
  have htsmall : t ≤ (1 : ℝ) / 64 := by
    have hc : (2 : ℝ) * sharpCompactLowerConstant ≤ 1 / 64 := by
      unfold sharpCompactLowerConstant
      norm_num
    calc
      t ≤ 2 * sharpCompactLowerConstant * logTwoOverSq r := by
        dsimp [t]
        nlinarith [hepsilonLt]
      _ ≤ ((1 : ℝ) / 64) * logTwoOverSq r :=
        mul_le_mul_of_nonneg_right hc hrateNonneg
      _ ≤ (1 : ℝ) / 64 := by nlinarith
  have hY0 : 0 ≤ Real.log (r : ℝ) /
      ((10 : ℝ) ^ 10 * (r : ℝ)) := by positivity
  have htY : t ≤
      (Real.log (r : ℝ) / ((10 : ℝ) ^ 10 * (r : ℝ))) ^ 2 := by
    calc
      t ≤ Real.log (r : ℝ) ^ 2 /
          ((10 : ℝ) ^ 20 * (r : ℝ) ^ 2) := htRate.le
      _ = (Real.log (r : ℝ) /
          ((10 : ℝ) ^ 10 * (r : ℝ))) ^ 2 := by field_simp
  have hsqrt : Real.sqrt t ≤
      Real.log (r : ℝ) / ((10 : ℝ) ^ 10 * (r : ℝ)) := by
    calc
      Real.sqrt t ≤ Real.sqrt
          ((Real.log (r : ℝ) / ((10 : ℝ) ^ 10 * (r : ℝ))) ^ 2) :=
        Real.sqrt_le_sqrt htY
      _ = _ := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hY0]
  have hexponent :
      100 * (r : ℝ) * Real.sqrt t ≤ Real.log (r : ℝ) := by
    calc
      100 * (r : ℝ) * Real.sqrt t ≤
          100 * (r : ℝ) *
            (Real.log (r : ℝ) / ((10 : ℝ) ^ 10 * (r : ℝ))) := by
        gcongr
      _ ≤ Real.log (r : ℝ) := by
        field_simp
        nlinarith [hlogPos]
  have hexp :
      Real.exp (100 * (r : ℝ) * Real.sqrt t) ≤ (r : ℝ) := by
    calc
      Real.exp (100 * (r : ℝ) * Real.sqrt t) ≤
          Real.exp (Real.log (r : ℝ)) := Real.exp_le_exp.mpr hexponent
      _ = (r : ℝ) := Real.exp_log hrR
  have hquadratic :
      (16 * ((r : ℝ) + 1)) ^ 2 ≤ 1024 * (r : ℝ) ^ 2 := by
    have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hforce := sharpCertificate_forces_growth (r := r) (by omega) hepsilon
    (by rfl : t = 2 * epsilon) htsmall hcert
  unfold sharpNegativeFaceEnvelope at hforce
  have hforceUpper : 1 ≤ 4096 * t ^ 2 * (r : ℝ) ^ 3 := by
    calc
      1 ≤ 4 * t ^ 2 *
          (Real.exp (100 * (r : ℝ) * Real.sqrt t) *
            (16 * ((r : ℝ) + 1)) ^ 2) := hforce
      _ ≤ 4 * t ^ 2 * ((r : ℝ) * (1024 * (r : ℝ) ^ 2)) := by
        gcongr
      _ = 4096 * t ^ 2 * (r : ℝ) ^ 3 := by ring
  have hlogPow : Real.log (r : ℝ) ^ 4 ≤ Real.log (r : ℝ) ^ 8 := by
    have hlogOne : (1 : ℝ) ≤ Real.log (r : ℝ) := by linarith
    have hpowOne : (1 : ℝ) ≤ Real.log (r : ℝ) ^ 4 :=
      one_le_pow₀ hlogOne
    rw [show Real.log (r : ℝ) ^ 8 =
      (Real.log (r : ℝ) ^ 4) ^ 2 by ring]
    nlinarith [sq_nonneg (Real.log (r : ℝ) ^ 4 - 1)]
  have hdominates :
      4096 * Real.log (r : ℝ) ^ 4 <
        (10 : ℝ) ^ 40 * (r : ℝ) := by
    calc
      4096 * Real.log (r : ℝ) ^ 4 ≤
          512 * (8 * Real.log (r : ℝ) ^ 8) := by nlinarith
      _ ≤ 512 * ((10 : ℝ) ^ 32 * (r : ℝ)) := by gcongr
      _ < (10 : ℝ) ^ 40 * (r : ℝ) := by
        have : (512 : ℝ) * 10 ^ 32 < 10 ^ 40 := by norm_num
        nlinarith
  have hupper :
      4096 * t ^ 2 * (r : ℝ) ^ 3 < 1 := by
    calc
      4096 * t ^ 2 * (r : ℝ) ^ 3 <
          4096 * (Real.log (r : ℝ) ^ 2 /
            ((10 : ℝ) ^ 20 * (r : ℝ) ^ 2)) ^ 2 *
              (r : ℝ) ^ 3 := by gcongr
      _ = (4096 * Real.log (r : ℝ) ^ 4) /
          ((10 : ℝ) ^ 40 * (r : ℝ)) := by field_simp
      _ < 1 := (div_lt_one (by positivity)).mpr hdominates
  linarith

/-- Matching lower certificate bound, including the zero endpoint. -/
theorem sharpCompact_logTwo_over_sq_lower :
    ∃ c r0, 0 < c ∧ 0 < r0 ∧
      ∀ r, r0 ≤ r → ∀ epsilon : ℝ, 0 ≤ epsilon →
        sharpObjective + C epsilon ∈ GenPreordering sharpGenerators r →
          c * logTwoOverSq r ≤ epsilon := by
  obtain ⟨r0, hr0, hlower⟩ :=
    sharpCompact_logTwo_over_sq_lower_pos
  refine ⟨sharpCompactLowerConstant, max r0 3, ?_, by omega, ?_⟩
  · unfold sharpCompactLowerConstant
    positivity
  · intro r hrr epsilon hepsilon hcert
    have hrr0 : r0 ≤ r := le_trans (le_max_left r0 3) hrr
    rcases hepsilon.eq_or_lt with rfl | hepsilonPos
    · have hr3 : 3 ≤ r := le_trans (le_max_right r0 3) hrr
      have hmax : max r 2 = r := max_eq_left (by omega)
      have hlog : 0 < Real.log (r : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (show 1 < r by omega)
      have hratePos : 0 < logTwoOverSq r := by
        rw [logTwoOverSq, hmax]
        positivity
      let delta : ℝ :=
        sharpCompactLowerConstant * logTwoOverSq r / 2
      have hdelta : 0 < delta := by
        dsimp [delta]
        exact div_pos (mul_pos (by
          unfold sharpCompactLowerConstant
          positivity) hratePos) (by norm_num)
      have hconst : C delta ∈ GenPreordering sharpGenerators 0 :=
        KrivineStengle.genPreordering_C_nonneg sharpGenerators hdelta.le
      have hconstR : C delta ∈ GenPreordering sharpGenerators r :=
        GenPreordering_mono (Nat.zero_le r) hconst
      have hcertDelta :
          sharpObjective + C delta ∈ GenPreordering sharpGenerators r := by
        have hsum := KrivineStengle.genPreordering_add hcert hconstR
        simpa using hsum
      have hcontra := hlower r hrr0 delta hdelta hcertDelta
      dsimp [delta] at hcontra
      nlinarith
    · exact hlower r hrr0 epsilon hepsilonPos hcert

end OptimalConvergenceRates.GeneralCompact

end
