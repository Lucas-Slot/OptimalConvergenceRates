/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/TrigDerivative.lean

  Degree-quadratic control of symmetric great-circle differences.
-/
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityCorollaries
import OptimalConvergenceRates.QuarticConvergence.Sphere.FiniteDegree
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Localization
import OptimalConvergenceRates.ScaledRobinson.HomogenizationCore
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Reflection

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open ScaledRobinson

open SphereBallTransfers

/-- Markov's first-derivative inequality gives a Lipschitz estimate from any
point of the unit interval to its right endpoint. -/
theorem polynomial_eval_sub_eval_one_abs_le_markov
    (q : Polynomial ℝ) (D : ℕ) (hdeg : q.natDegree ≤ D)
    (M : ℝ)
    (hbound : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → |q.eval t| ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |q.eval t - q.eval 1| ≤ (D : ℝ) ^ 2 * M * (1 - t) := by
  have hsup : polySupNormUni q ≤ M :=
    polySupNormUni_le_of_bound q M hbound
  have hderiv :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        ‖deriv q.eval z‖ ≤ (D : ℝ) ^ 2 * M := by
    intro z hz
    have hderivEval :
        deriv q.eval z = (Polynomial.derivative q).eval z := by
      have h := Polynomial.deriv_aeval (𝕜 := ℝ) q (x := z)
      simpa only [Polynomial.coe_aeval_eq_eval] using h
    rw [hderivEval, Real.norm_eq_abs]
    exact (univariate_markov_first_derivative_inside q D hdeg z
      (abs_le.mpr hz)).trans
        (mul_le_mul_of_nonneg_left hsup (sq_nonneg (D : ℝ)))
  have hmean :
      ‖q.eval t - q.eval 1‖ ≤
        ((D : ℝ) ^ 2 * M) * ‖t - 1‖ := by
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.Icc (-1 : ℝ) 1)
      (f := q.eval)
      (fun _z _hz ↦ q.differentiableAt)
      hderiv (convex_Icc (-1 : ℝ) 1)
      (by norm_num) ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr ht.2)] at hmean
  nlinarith

/-- A polynomial of degree at most one is its affine interpolation between
the endpoints `-1` and `1`. -/
theorem polynomial_two_mul_eval_eq_endpoint_interpolation
    (q : Polynomial ℝ) (hdeg : q.natDegree ≤ 1) (t : ℝ) :
    2 * q.eval t = (1 + t) * q.eval 1 + (1 - t) * q.eval (-1) := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

/-- Evaluation of an affine multivariate polynomial at two endpoints averages
to evaluation at their midpoint. -/
theorem mvPolynomial_eval_add_eval_eq_two_mul_eval_midpoint
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hdeg : P.totalDegree ≤ 1)
    (z w : Fin n → ℝ) :
    MvPolynomial.eval z P + MvPolynomial.eval w P =
      2 * MvPolynomial.eval ((1 / 2 : ℝ) • (z + w)) P := by
  let q := univariateRestriction P z (w - z)
  have hqdeg : q.natDegree ≤ 1 :=
    (univariateRestriction_natDegree_le P z (w - z)).trans hdeg
  have hz : z + (1 / 2 : ℝ) • (w - z) = (1 / 2 : ℝ) • (z + w) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hone : z + (1 : ℝ) • (w - z) = w := by
    ext i
    simp
  have hqzero : q.eval 0 = MvPolynomial.eval z P := by
    rw [univariateRestriction_eval]
    simp
  have hqone : q.eval 1 = MvPolynomial.eval w P := by
    rw [univariateRestriction_eval, hone]
  have hqmid : q.eval (1 / 2) =
      MvPolynomial.eval ((1 / 2 : ℝ) • (z + w)) P := by
    rw [univariateRestriction_eval, hz]
  have qlin := Polynomial.eq_X_add_C_of_natDegree_le_one hqdeg
  rw [qlin] at hqzero hqone hqmid
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hqzero hqone hqmid
  rw [← hqzero, ← hqone, ← hqmid]
  ring

/-- Unit vectors with dot product one agree. -/
theorem sphereSet_eq_of_dot_eq_one {n : ℕ} (y x : sphereSet n)
    (hdot : ∑ i, y.1 i * x.1 i = 1) :
    y = x := by
  have hzero : sphereChordalSq y.1 x.1 = 0 := by
    rw [sphereChordalSq_eq_two_mul_one_sub_dot y.2 x.2, hdot]
    ring
  change ∑ i, (y.1 i - x.1 i) ^ 2 = 0 at hzero
  apply Subtype.ext
  funext i
  have hi :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _hj ↦ sq_nonneg (y.1 j - x.1 j))).1
      hzero i (Finset.mem_univ i)
  nlinarith

/-- Unit vectors with dot product minus one are antipodal. -/
theorem sphereSet_coe_eq_neg_of_dot_eq_neg_one {n : ℕ} (y x : sphereSet n)
    (hdot : ∑ i, y.1 i * x.1 i = -1) :
    y.1 = -x.1 := by
  let xneg : sphereSet n := ⟨-x.1, by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2⟩
  have hdotneg : ∑ i, y.1 i * xneg.1 i = 1 := by
    calc
      (∑ i, y.1 i * xneg.1 i) = -(∑ i, y.1 i * x.1 i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [xneg]
      _ = 1 := by rw [hdot]; ring
  have hyneg := sphereSet_eq_of_dot_eq_one y xneg hdotneg
  exact congrArg Subtype.val hyneg

/-- Axial reflection fixes its unit axis. -/
@[simp] theorem sphereAxialReflection_self {n : ℕ} (x : sphereSet n) :
    sphereAxialReflection x x = x := by
  apply Subtype.ext
  funext i
  change 2 * (∑ j, x.1 j * x.1 j) * x.1 i - x.1 i = x.1 i
  have hxsum : ∑ j, x.1 j * x.1 j = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2
  rw [hxsum]
  ring

/-- Axial reflection also fixes the antipode of its axis. -/
theorem sphereAxialReflection_neg_self {n : ℕ} (x : sphereSet n) :
    sphereAxialReflection x
      ⟨-x.1, by simpa [sphereSet, sphereQuadratic, pow_two] using x.2⟩ =
        ⟨-x.1, by simpa [sphereSet, sphereQuadratic, pow_two] using x.2⟩ := by
  apply Subtype.ext
  funext i
  change 2 * (∑ j, (-x.1 j) * x.1 j) * x.1 i - (-x.1 i) = -x.1 i
  have hxsum : ∑ j, x.1 j * x.1 j = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2
  have hneg : ∑ j, (-x.1 j) * x.1 j = -1 := by
    calc
      (∑ j, (-x.1 j) * x.1 j) = -(∑ j, x.1 j * x.1 j) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = -1 := by rw [hxsum]
  rw [hneg]
  ring

/-- The standard cosine-sine parametrization of two orthonormal ambient
directions lies on the algebraic unit sphere. -/
theorem sphereGreatCirclePoint_mem {n : ℕ} (x u : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) (hu : ∑ i, u i ^ 2 = 1)
    (horth : ∑ i, x i * u i = 0)
    (t : ℝ) (htLower : -1 ≤ t) (htUpper : t ≤ 1) :
    (fun i ↦ t * x i + Real.sqrt (1 - t ^ 2) * u i) ∈ sphereSet n := by
  have hsnonneg : 0 ≤ 1 - t ^ 2 := by
    nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
  have hsqrt : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 :=
    Real.sq_sqrt hsnonneg
  simp only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X,
    Set.mem_setOf_eq]
  calc
    (∑ i, (t * x i + Real.sqrt (1 - t ^ 2) * u i) ^ 2) =
        t ^ 2 * (∑ i, x i ^ 2) +
          2 * t * Real.sqrt (1 - t ^ 2) * (∑ i, x i * u i) +
          (Real.sqrt (1 - t ^ 2)) ^ 2 * (∑ i, u i ^ 2) := by
      simp_rw [add_sq, Finset.sum_add_distrib]
      rw [show (∑ i, (t * x i) ^ 2) = t ^ 2 * ∑ i, x i ^ 2 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring]
      rw [show (∑ i, 2 * (t * x i) *
          (Real.sqrt (1 - t ^ 2) * u i)) =
          2 * t * Real.sqrt (1 - t ^ 2) * ∑ i, x i * u i by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring]
      rw [show (∑ i, (Real.sqrt (1 - t ^ 2) * u i) ^ 2) =
          (Real.sqrt (1 - t ^ 2)) ^ 2 * ∑ i, u i ^ 2 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring]
    _ = 1 := by rw [hx, hu, horth, hsqrt]; ring

/-- Restrict an ambient polynomial to the formal two-coordinate plane
`(t,s) ↦ t x + s u`. We use the repository's ternary square-substitution
infrastructure, leaving its middle variable unused. -/
noncomputable def greatCircleTernaryRestriction {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (x u : Fin n → ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval
    (fun i => MvPolynomial.C (x i) * MvPolynomial.X 0 +
      MvPolynomial.C (u i) * MvPolynomial.X 2) P

/-- Evaluation of the formal great-circle restriction is the expected
ambient evaluation. -/
theorem greatCircleTernaryRestriction_eval {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (x u : Fin n → ℝ) (t s w : ℝ) :
    MvPolynomial.eval ![t, w, s] (greatCircleTernaryRestriction P x u) =
      MvPolynomial.eval (fun i => t * x i + s * u i) P := by
  have h :
      (MvPolynomial.aeval ![t, w, s]).comp
          (MvPolynomial.aeval
            (fun i => MvPolynomial.C (x i) * MvPolynomial.X 0 +
              MvPolynomial.C (u i) * MvPolynomial.X 2)) =
        (MvPolynomial.aeval (fun i => t * x i + s * u i) :
          MvPolynomial (Fin n) ℝ →ₐ[ℝ] ℝ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [mul_comm]
  simpa [greatCircleTernaryRestriction, MvPolynomial.aeval_eq_eval] using
    AlgHom.congr_fun h P

/-- Linear substitution into the two-coordinate plane preserves the ambient
total-degree bound. -/
theorem greatCircleTernaryRestriction_totalDegree_le {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (x u : Fin n → ℝ) :
    (greatCircleTernaryRestriction P x u).totalDegree ≤ P.totalDegree := by
  let f : Fin n → MvPolynomial (Fin 3) ℝ := fun i =>
    MvPolynomial.C (x i) * MvPolynomial.X 0 +
      MvPolynomial.C (u i) * MvPolynomial.X 2
  change (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree
  apply ScaledRobinson.totalDegree_aeval_le_of_linear
  intro i
  let a : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.C (x i) * MvPolynomial.X 0
  let b : MvPolynomial (Fin 3) ℝ :=
    MvPolynomial.C (u i) * MvPolynomial.X 2
  change (a + b).totalDegree ≤ 1
  calc
    (a + b).totalDegree ≤ max a.totalDegree b.totalDegree :=
      MvPolynomial.totalDegree_add _ _
    _ ≤ max 1 1 := max_le_max
      ((ScaledRobinson.totalDegree_C_mul_le _ _).trans
        (by simp [MvPolynomial.totalDegree_X]))
      ((ScaledRobinson.totalDegree_C_mul_le _ _).trans
        (by simp [MvPolynomial.totalDegree_X]))
    _ = 1 := by simp

/-- Reflecting the formal sine coordinate negates the transverse direction. -/
theorem zReflect3_greatCircleTernaryRestriction {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (x u : Fin n → ℝ) :
    zReflect3 (greatCircleTernaryRestriction P x u) =
      greatCircleTernaryRestriction P x (-u) := by
  unfold greatCircleTernaryRestriction
  have h :
      zReflect3.comp
          (MvPolynomial.aeval
            (fun i => MvPolynomial.C (x i) * MvPolynomial.X 0 +
              MvPolynomial.C (u i) * MvPolynomial.X 2)) =
        MvPolynomial.aeval
          (fun i => MvPolynomial.C (x i) * MvPolynomial.X 0 +
            MvPolynomial.C ((-u) i) * MvPolynomial.X 2) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [zReflect3]
  exact AlgHom.congr_fun h P

/-- Evaluating the repository's square-substitution map squares only the
third coordinate. -/
theorem zSquareSubst3_eval (A : MvPolynomial (Fin 3) ℝ) (t w s : ℝ) :
    MvPolynomial.eval ![t, w, s] (zSquareSubst3 A) =
      MvPolynomial.eval ![t, w, s ^ 2] A := by
  change (MvPolynomial.aeval ![t, w, s])
      (MvPolynomial.aeval
        ![(MvPolynomial.X 0 : MvPolynomial (Fin 3) ℝ), MvPolynomial.X 1,
          (MvPolynomial.X 2) ^ 2] A) =
    MvPolynomial.aeval ![t, w, s ^ 2] A
  rw [MvPolynomial.comp_aeval_apply]
  apply AlgHom.congr_fun ?_ A
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp

/-- At the affine slice `(t,0,1)`, the homogeneous unit-ball substitution
replaces its source square variable by `1 - t²`. -/
theorem homBallSourceSubst_one_eval (A : MvPolynomial (Fin 3) ℝ) (t : ℝ) :
    MvPolynomial.eval ![t, 0, 1] (homBallSourceSubst 1 A) =
      MvPolynomial.eval ![t, 0, 1 - t ^ 2] A := by
  change (MvPolynomial.aeval ![t, 0, 1])
      (MvPolynomial.aeval
        ![(MvPolynomial.X 0 : MvPolynomial (Fin 3) ℝ), MvPolynomial.X 1,
          HomBallGenerator 1] A) =
    MvPolynomial.aeval ![t, 0, 1 - t ^ 2] A
  rw [MvPolynomial.comp_aeval_apply]
  apply AlgHom.congr_fun ?_ A
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [HomBallGenerator]

/-- Contracting the even exponents of a polynomial whose coefficients are
themselves real polynomials does not increase its outer degree. -/
theorem coefficientPolynomial_contract_two_natDegree_le
    (P : Polynomial (Polynomial ℝ)) :
    (Polynomial.contract 2 P).natDegree ≤ P.natDegree := by
  by_cases hP : P = 0
  · subst P
    rw [show (0 : Polynomial (Polynomial ℝ)) = Polynomial.C 0 by simp]
    rw [Polynomial.contract_C]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_lt_of_le hk (by omega : k ≤ k * 2))

/-- The unscaled even part in the outer variable of a polynomial with
polynomial coefficients. The missing factor `1 / 2` is intentional: the
great-circle theorem needs the sum of the two reflected evaluations. -/
noncomputable def coefficientPolynomialSymmetricPart
    (P : Polynomial (Polynomial ℝ)) : Polynomial (Polynomial ℝ) :=
  P + P.comp (-Polynomial.X)

theorem coefficientPolynomial_coeff_comp_neg_X
    (P : Polynomial (Polynomial ℝ)) (k : ℕ) :
    (P.comp (-Polynomial.X)).coeff k =
      P.coeff k * (-1 : Polynomial ℝ) ^ k := by
  rw [show (-Polynomial.X : Polynomial (Polynomial ℝ)) =
    Polynomial.C (-1 : Polynomial ℝ) * Polynomial.X by simp]
  exact Polynomial.comp_C_mul_X_coeff

/-- Odd outer coefficients vanish after reflection in the outer variable. -/
theorem coefficientPolynomialSymmetricPart_odd_coeff_eq_zero
    (P : Polynomial (Polynomial ℝ)) {k : ℕ} (hk : ¬2 ∣ k) :
    (coefficientPolynomialSymmetricPart P).coeff k = 0 := by
  have hkNotEven : ¬Even k := by
    rw [even_iff_two_dvd]
    exact hk
  have hkOdd : Odd k := Nat.not_even_iff_odd.mp hkNotEven
  have hpow : (-1 : Polynomial ℝ) ^ k = -1 := by
    exact (neg_one_pow_eq_neg_one_iff_odd
      (by norm_num : (-1 : Polynomial ℝ) ≠ 1)).mpr hkOdd
  simp only [coefficientPolynomialSymmetricPart, Polynomial.coeff_add,
    coefficientPolynomial_coeff_comp_neg_X, hpow]
  ring

/-- Expanding after contracting recovers the symmetric polynomial, since all
of its odd outer coefficients vanish. -/
theorem coefficientPolynomialSymmetricPart_expand_contract
    (P : Polynomial (Polynomial ℝ)) :
    Polynomial.expand (Polynomial ℝ) 2
        (Polynomial.contract 2 (coefficientPolynomialSymmetricPart P)) =
      coefficientPolynomialSymmetricPart P := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hk : 2 ∣ k
  · rw [if_pos hk, Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0),
      Nat.div_mul_cancel hk]
  · rw [if_neg hk]
    exact (coefficientPolynomialSymmetricPart_odd_coeff_eq_zero P hk).symm

/-- Evaluating the contracted symmetric polynomial at a square is the sum of
the original evaluations at the two square roots. -/
theorem coefficientPolynomialSymmetricPart_contract_eval_sq
    (P : Polynomial (Polynomial ℝ)) (r : Polynomial ℝ) :
    (Polynomial.contract 2 (coefficientPolynomialSymmetricPart P)).eval (r ^ 2) =
      P.eval r + P.eval (-r) := by
  have h := congrArg (fun Q : Polynomial (Polynomial ℝ) ↦ Q.eval r)
    (coefficientPolynomialSymmetricPart_expand_contract P)
  simpa [coefficientPolynomialSymmetricPart, Polynomial.eval_add,
    Polynomial.eval_comp] using h

/-- Reflection in the outer variable does not increase outer degree. -/
theorem coefficientPolynomialSymmetricPart_natDegree_le
    (P : Polynomial (Polynomial ℝ)) :
    (coefficientPolynomialSymmetricPart P).natDegree ≤ P.natDegree := by
  apply (Polynomial.natDegree_add_le _ _).trans
  rw [max_le_iff]
  constructor
  · exact le_rfl
  · calc
      (P.comp (-Polynomial.X)).natDegree ≤
          P.natDegree *
            (-Polynomial.X : Polynomial (Polynomial ℝ)).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _
        (Polynomial.natDegree_neg_le_of_le Polynomial.natDegree_X_le)
      _ = P.natDegree := Nat.mul_one _

/-- Contracting the symmetric outer variable does not increase the original
outer degree. -/
theorem coefficientPolynomialSymmetricPart_contract_natDegree_le
    (P : Polynomial (Polynomial ℝ)) :
    (Polynomial.contract 2 (coefficientPolynomialSymmetricPart P)).natDegree ≤
      P.natDegree :=
  (coefficientPolynomial_contract_two_natDegree_le _).trans
    (coefficientPolynomialSymmetricPart_natDegree_le P)

/-- On the unit cosine interval, symmetrizing the formal sine coordinate
and replacing its square by `1 - t²` produces a univariate polynomial
without increasing total degree. -/
theorem exists_evenGreatCirclePolynomial_on_Icc
    {n D : ℕ} (P : MvPolynomial (Fin n) ℝ) (hPdeg : P.totalDegree ≤ D)
    (x u : Fin n → ℝ) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ D ∧
      ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
        q.eval t =
          MvPolynomial.eval
              (fun i ↦ t * x i + Real.sqrt (1 - t ^ 2) * u i) P +
            MvPolynomial.eval
              (fun i ↦ t * x i - Real.sqrt (1 - t ^ 2) * u i) P := by
  let B : MvPolynomial (Fin 3) ℝ := greatCircleTernaryRestriction P x u
  let S : MvPolynomial (Fin 3) ℝ := B + zReflect3 B
  have hSinv : zReflect3 S = S := by
    dsimp only [S]
    rw [map_add, zReflect3_involutive]
    ac_rfl
  obtain ⟨A, hA⟩ :=
    exists_zSquareSubst3_of_zReflect3_eq_self hSinv
  have hBdeg : B.totalDegree ≤ D := by
    exact (greatCircleTernaryRestriction_totalDegree_le P x u).trans hPdeg
  have hSdeg : S.totalDegree ≤ D := by
    calc
      S.totalDegree ≤ max B.totalDegree (zReflect3 B).totalDegree := by
        dsimp only [S]
        exact MvPolynomial.totalDegree_add _ _
      _ ≤ D := max_le hBdeg ((zReflect3_totalDegree_le B).trans hBdeg)
  have hAweighted : sourceWeightedDegree3 A ≤ D := by
    calc
      sourceWeightedDegree3 A ≤ (zSquareSubst3 A).totalDegree :=
        sourceWeightedDegree3_le_zSquareSubst3_totalDegree A
      _ = S.totalDegree := by rw [← hA]
      _ ≤ D := hSdeg
  let base : Fin 3 → ℝ := ![0, 0, 1]
  let direction : Fin 3 → ℝ := ![1, 0, 0]
  let q : Polynomial ℝ :=
    univariateRestriction (homBallSourceSubst 1 A) base direction
  have hqdeg : q.natDegree ≤ D := by
    calc
      q.natDegree ≤ (homBallSourceSubst 1 A).totalDegree := by
        exact univariateRestriction_natDegree_le
          (homBallSourceSubst 1 A) base direction
      _ ≤ sourceWeightedDegree3 A :=
        homBallSourceSubst_totalDegree_le_weighted 1 A
      _ ≤ D := hAweighted
  refine ⟨q, hqdeg, ?_⟩
  intro t htLower htUpper
  have htSq : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
  have hline : base + t • direction = ![t, 0, 1] := by
    ext i
    fin_cases i <;> simp [base, direction]
  calc
    q.eval t =
        MvPolynomial.eval ![t, 0, 1] (homBallSourceSubst 1 A) := by
      dsimp only [q]
      rw [univariateRestriction_eval, hline]
    _ = MvPolynomial.eval ![t, 0, 1 - t ^ 2] A :=
      homBallSourceSubst_one_eval A t
    _ = MvPolynomial.eval ![t, 0, (Real.sqrt (1 - t ^ 2)) ^ 2] A := by
      rw [htSq]
    _ = MvPolynomial.eval ![t, 0, Real.sqrt (1 - t ^ 2)]
          (zSquareSubst3 A) := by
      symm
      exact zSquareSubst3_eval A t 0 (Real.sqrt (1 - t ^ 2))
    _ = MvPolynomial.eval ![t, 0, Real.sqrt (1 - t ^ 2)] S := by
      rw [hA]
    _ = MvPolynomial.eval ![t, 0, Real.sqrt (1 - t ^ 2)] B +
          MvPolynomial.eval ![t, 0, Real.sqrt (1 - t ^ 2)]
            (zReflect3 B) := by
      simp only [S, MvPolynomial.eval_add]
    _ =
        MvPolynomial.eval
            (fun i ↦ t * x i + Real.sqrt (1 - t ^ 2) * u i) P +
          MvPolynomial.eval
            (fun i ↦ t * x i - Real.sqrt (1 - t ^ 2) * u i) P := by
      dsimp only [B]
      rw [zReflect3_greatCircleTernaryRestriction]
      rw [greatCircleTernaryRestriction_eval,
        greatCircleTernaryRestriction_eval]
      simp only [Pi.neg_apply, mul_neg, sub_eq_add_neg]

/-- The even great-circle restriction is constant in filtration degree zero. -/
theorem exists_axialReflection_evenRestrictionPolynomial_zero
    {n : ℕ} (v : spherePolynomialSpace n 0) (x y : sphereSet n) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ 0 ∧
      (∀ t : ℝ, -1 ≤ t → t ≤ 1 → |q.eval t| ≤ 2 * ‖v‖) ∧
      q.eval (∑ i, y.1 i * x.1 i) =
        v.1 y + v.1 (sphereAxialReflection x y) ∧
      q.eval 1 = 2 * v.1 x := by
  obtain ⟨P, hPdeg, hPv⟩ :=
    (mem_spherePolynomialSpace_iff v.1).1 v.2
  have hPzero : P.totalDegree = 0 := Nat.eq_zero_of_le_zero hPdeg
  have hPconst := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).1 hPzero
  let c := MvPolynomial.coeff 0 P
  have hvconst : v = spherePolynomialConst n 0 c := by
    apply Subtype.ext
    change v.1 = (spherePolynomialConst n 0 c).1
    rw [← hPv, hPconst]
    ext z
    simp [c]
  rw [hvconst]
  refine ⟨Polynomial.C (2 * c),
    by simpa only [Polynomial.natDegree_C] using (Nat.le_refl 0),
    ?_, ?_, ?_⟩
  · intro _t _htLower _htUpper
    have hcabs : |c| ≤ ‖spherePolynomialConst n 0 c‖ := by
      simpa only [spherePolynomialConst_apply, Real.norm_eq_abs] using
        ContinuousMap.norm_coe_le_norm
          (spherePolynomialConst n 0 c).1 x
    rw [Polynomial.eval_C, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hcabs (by norm_num)
  · simp only [Polynomial.eval_C, spherePolynomialConst_apply]
    ring
  · simp

/-- For an affine ambient polynomial, the even axial-reflection restriction is
the affine line restriction through the origin, multiplied by two. -/
theorem exists_axialReflection_evenRestrictionPolynomial_one
    {n : ℕ} (v : spherePolynomialSpace n 1) (x y : sphereSet n) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ 1 ∧
      (∀ t : ℝ, -1 ≤ t → t ≤ 1 → |q.eval t| ≤ 2 * ‖v‖) ∧
      q.eval (∑ i, y.1 i * x.1 i) =
        v.1 y + v.1 (sphereAxialReflection x y) ∧
      q.eval 1 = 2 * v.1 x := by
  obtain ⟨P, hPdeg, hPv⟩ :=
    (mem_spherePolynomialSpace_iff v.1).1 v.2
  let xneg : sphereSet n := ⟨-x.1, by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2⟩
  let r := univariateRestriction P 0 x.1
  let q : Polynomial ℝ := (2 : ℝ) • r
  have hrdeg : r.natDegree ≤ 1 :=
    (univariateRestriction_natDegree_le P 0 x.1).trans hPdeg
  have hqdeg : q.natDegree ≤ 1 :=
    (Polynomial.natDegree_smul_le (2 : ℝ) r).trans hrdeg
  have hPval (z : sphereSet n) : MvPolynomial.eval z.1 P = v.1 z := by
    have hz := congrArg (fun f : C(sphereSet n, ℝ) ↦ f z) hPv
    simpa using hz
  have hrone : r.eval 1 = v.1 x := by
    rw [univariateRestriction_eval]
    simpa only [zero_add, one_smul] using hPval x
  have hrnegone : r.eval (-1) = v.1 xneg := by
    rw [univariateRestriction_eval]
    have hxneg : (0 : Fin n → ℝ) + (-1 : ℝ) • x.1 = xneg.1 := by
      ext i
      simp [xneg]
    rw [hxneg]
    exact hPval xneg
  have hxbound : |v.1 x| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm v.1 x
  have hxnegbound : |v.1 xneg| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm v.1 xneg
  refine ⟨q, hqdeg, ?_, ?_, ?_⟩
  · intro t htLower htUpper
    have hinterp := polynomial_two_mul_eval_eq_endpoint_interpolation r hrdeg t
    rw [hrone, hrnegone] at hinterp
    have hnonnegLeft : 0 ≤ 1 + t := by linarith
    have hnonnegRight : 0 ≤ 1 - t := by linarith
    rw [show q.eval t = 2 * r.eval t by simp [q]]
    rw [hinterp]
    calc
      |(1 + t) * v.1 x + (1 - t) * v.1 xneg| ≤
          |(1 + t) * v.1 x| + |(1 - t) * v.1 xneg| := abs_add_le _ _
      _ = (1 + t) * |v.1 x| + (1 - t) * |v.1 xneg| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hnonnegLeft,
          abs_of_nonneg hnonnegRight]
      _ ≤ (1 + t) * ‖v‖ + (1 - t) * ‖v‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left hxbound hnonnegLeft)
          (mul_le_mul_of_nonneg_left hxnegbound hnonnegRight)
      _ = 2 * ‖v‖ := by ring
  · let a : ℝ := ∑ i, y.1 i * x.1 i
    have hmidpoint :
        (1 / 2 : ℝ) • (y.1 + (sphereAxialReflection x y).1) = a • x.1 := by
      ext i
      simp only [sphereAxialReflection_coe, sphereAxialReflectionRaw,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      dsimp only [a]
      ring
    have hmid := mvPolynomial_eval_add_eval_eq_two_mul_eval_midpoint
      P hPdeg y.1 (sphereAxialReflection x y).1
    rw [hmidpoint] at hmid
    change q.eval a = v.1 y + v.1 (sphereAxialReflection x y)
    calc
      q.eval a = 2 * MvPolynomial.eval (a • x.1) P := by
        simp [q, r, univariateRestriction_eval]
      _ = MvPolynomial.eval y.1 P +
          MvPolynomial.eval (sphereAxialReflection x y).1 P := hmid.symm
      _ = v.1 y + v.1 (sphereAxialReflection x y) := by
        rw [hPval y, hPval (sphereAxialReflection x y)]
  · calc
      q.eval 1 = 2 * r.eval 1 := by simp [q]
      _ = 2 * v.1 x := by rw [hrone]

/-- If the two sphere points are parallel, endpoint interpolation supplies the
required bounded restriction polynomial in every positive filtration degree. -/
theorem exists_axialReflection_evenRestrictionPolynomial_endpoint
    {n D : ℕ} (hD : 1 ≤ D) (v : spherePolynomialSpace n D)
    (x y : sphereSet n)
    (hend : (∑ i, y.1 i * x.1 i) ^ 2 = 1) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ D ∧
      (∀ t : ℝ, -1 ≤ t → t ≤ 1 → |q.eval t| ≤ 2 * ‖v‖) ∧
      q.eval (∑ i, y.1 i * x.1 i) =
        v.1 y + v.1 (sphereAxialReflection x y) ∧
      q.eval 1 = 2 * v.1 x := by
  let xneg : sphereSet n := ⟨-x.1, by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2⟩
  let q : Polynomial ℝ :=
    Polynomial.C (v.1 x + v.1 xneg) +
      Polynomial.C (v.1 x - v.1 xneg) * Polynomial.X
  have hqdegOne : q.natDegree ≤ 1 := by
    dsimp only [q]
    calc
      (Polynomial.C (v.1 x + v.1 xneg) +
          Polynomial.C (v.1 x - v.1 xneg) * Polynomial.X).natDegree ≤
          max (Polynomial.C (v.1 x + v.1 xneg)).natDegree
            (Polynomial.C (v.1 x - v.1 xneg) * Polynomial.X).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 1 := by
        apply max_le
        · simp [Polynomial.natDegree_C]
        · calc
            (Polynomial.C (v.1 x - v.1 xneg) * Polynomial.X :
                Polynomial ℝ).natDegree ≤
                (Polynomial.C (v.1 x - v.1 xneg)).natDegree +
                  Polynomial.X.natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ 0 + 1 := by
              apply Nat.add_le_add
              · simp [Polynomial.natDegree_C]
              · exact Polynomial.natDegree_X_le (R := ℝ)
            _ = 1 := by omega
  have hqeval (t : ℝ) :
      q.eval t = (1 + t) * v.1 x + (1 - t) * v.1 xneg := by
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hxbound : |v.1 x| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm v.1 x
  have hxnegbound : |v.1 xneg| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm v.1 xneg
  refine ⟨q, hqdegOne.trans hD, ?_, ?_, ?_⟩
  · intro t htLower htUpper
    have hnonnegLeft : 0 ≤ 1 + t := by linarith
    have hnonnegRight : 0 ≤ 1 - t := by linarith
    rw [hqeval]
    calc
      |(1 + t) * v.1 x + (1 - t) * v.1 xneg| ≤
          |(1 + t) * v.1 x| + |(1 - t) * v.1 xneg| := abs_add_le _ _
      _ = (1 + t) * |v.1 x| + (1 - t) * |v.1 xneg| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hnonnegLeft,
          abs_of_nonneg hnonnegRight]
      _ ≤ (1 + t) * ‖v‖ + (1 - t) * ‖v‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_left hxbound hnonnegLeft)
          (mul_le_mul_of_nonneg_left hxnegbound hnonnegRight)
      _ = 2 * ‖v‖ := by ring
  · rcases sq_eq_one_iff.mp hend with hdot | hdot
    · have hy : y = x := sphereSet_eq_of_dot_eq_one y x hdot
      rw [hy, sphereAxialReflection_self, hqeval]
      have hxsum : ∑ i, x.1 i * x.1 i = 1 := by
        simpa [sphereSet, sphereQuadratic, pow_two] using x.2
      rw [hxsum]
      ring
    · have hycoe : y.1 = -x.1 :=
        sphereSet_coe_eq_neg_of_dot_eq_neg_one y x hdot
      have hy : y = xneg := by
        apply Subtype.ext
        exact hycoe
      have hrefl : sphereAxialReflection x xneg = xneg := by
        simpa [xneg] using sphereAxialReflection_neg_self x
      rw [hy, hrefl, hqeval]
      have hxsum : ∑ i, xneg.1 i * x.1 i = -1 := by
        calc
          (∑ i, xneg.1 i * x.1 i) = -(∑ i, x.1 i * x.1 i) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i _hi
            simp [xneg]
          _ = -1 := by
            have hnorm : ∑ i, x.1 i * x.1 i = 1 := by
              simpa [sphereSet, sphereQuadratic, pow_two] using x.2
            rw [hnorm]
      rw [hxsum]
      ring
  · rw [hqeval]
    ring

/-- Away from parallel endpoints, normalization of the transverse component
reduces the public reflection bridge to the even great-circle polynomial lemma. -/
theorem exists_axialReflection_evenRestrictionPolynomial_nonendpoint
    {n D : ℕ} (v : spherePolynomialSpace n D) (x y : sphereSet n)
    (hend : (∑ i, y.1 i * x.1 i) ^ 2 ≠ 1) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ D ∧
      (∀ t : ℝ, -1 ≤ t → t ≤ 1 → |q.eval t| ≤ 2 * ‖v‖) ∧
      q.eval (∑ i, y.1 i * x.1 i) =
        v.1 y + v.1 (sphereAxialReflection x y) ∧
      q.eval 1 = 2 * v.1 x := by
  obtain ⟨P, hPdeg, hPv⟩ :=
    (mem_spherePolynomialSpace_iff v.1).1 v.2
  let a : ℝ := ∑ i, y.1 i * x.1 i
  let s : ℝ := 1 - a ^ 2
  have ha : a ∈ Set.Icc (-1 : ℝ) 1 :=
    sphereDot_mem_Icc y.2 x.2
  have hsnonneg : 0 ≤ s := by
    rw [show s = (1 - a) * (1 + a) by dsimp only [s]; ring]
    exact mul_nonneg (sub_nonneg.mpr ha.2) (by linarith [ha.1])
  have hsne : s ≠ 0 := by
    intro hs
    apply hend
    have hasq : a ^ 2 = 1 := by
      dsimp only [s] at hs
      linarith
    simpa only [a] using hasq
  have hspos : 0 < s := lt_of_le_of_ne hsnonneg (Ne.symm hsne)
  have hsqrtne : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hspos)
  have hsqrtsq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hsnonneg
  let u : Fin n → ℝ := fun i ↦ (y.1 i - a * x.1 i) / Real.sqrt s
  have hxnorm : ∑ i, x.1 i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using x.2
  have hynorm : ∑ i, y.1 i ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic, pow_two] using y.2
  have hxy : ∑ i, x.1 i * y.1 i = a := by
    dsimp only [a]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have htrans : ∑ i, (y.1 i - a * x.1 i) ^ 2 = s := by
    have hcross :
        (∑ i, 2 * a * (y.1 i * x.1 i)) =
          2 * a * (∑ i, y.1 i * x.1 i) := by
      simpa using (Finset.mul_sum Finset.univ
        (fun i ↦ y.1 i * x.1 i) (2 * a)).symm
    have hsquare :
        (∑ i, a ^ 2 * x.1 i ^ 2) = a ^ 2 * (∑ i, x.1 i ^ 2) := by
      simpa using (Finset.mul_sum Finset.univ
        (fun i ↦ x.1 i ^ 2) (a ^ 2)).symm
    calc
      (∑ i, (y.1 i - a * x.1 i) ^ 2) =
          ∑ i, (y.1 i ^ 2 - 2 * a * (y.1 i * x.1 i) +
            a ^ 2 * x.1 i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i, y.1 i ^ 2) -
          2 * a * (∑ i, y.1 i * x.1 i) +
          a ^ 2 * (∑ i, x.1 i ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross, hsquare]
      _ = s := by
        rw [hynorm, hxnorm, show (∑ i, y.1 i * x.1 i) = a by rfl]
        dsimp only [s]
        ring
  have horthNum : ∑ i, x.1 i * (y.1 i - a * x.1 i) = 0 := by
    calc
      (∑ i, x.1 i * (y.1 i - a * x.1 i)) =
          ∑ i, (x.1 i * y.1 i - a * x.1 i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i, x.1 i * y.1 i) -
          (∑ i, a * x.1 i ^ 2) := by rw [Finset.sum_sub_distrib]
      _ = (∑ i, x.1 i * y.1 i) - a * (∑ i, x.1 i ^ 2) := by
        simpa using (Finset.mul_sum Finset.univ
          (fun i ↦ x.1 i ^ 2) a).symm
      _ = 0 := by rw [hxy, hxnorm]; ring
  have horth : ∑ i, x.1 i * u i = 0 := by
    calc
      (∑ i, x.1 i * u i) =
          ∑ i, (x.1 i * (y.1 i - a * x.1 i)) / Real.sqrt s := by
        apply Finset.sum_congr rfl
        intro i _hi
        dsimp only [u]
        ring
      _ = (∑ i, x.1 i * (y.1 i - a * x.1 i)) / Real.sqrt s :=
        by rw [Finset.sum_div]
      _ = 0 := by rw [horthNum, zero_div]
  have hunorm : ∑ i, u i ^ 2 = 1 := by
    calc
      (∑ i, u i ^ 2) =
          ∑ i, (y.1 i - a * x.1 i) ^ 2 / (Real.sqrt s) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        dsimp only [u]
        ring
      _ = (∑ i, (y.1 i - a * x.1 i) ^ 2) / (Real.sqrt s) ^ 2 :=
        by rw [Finset.sum_div]
      _ = 1 := by rw [htrans, hsqrtsq, div_self hsne]
  have hPval (z : sphereSet n) : MvPolynomial.eval z.1 P = v.1 z := by
    have hz := congrArg (fun f : C(sphereSet n, ℝ) ↦ f z) hPv
    simpa using hz
  obtain ⟨q, hqdeg, hqeval⟩ :=
    exists_evenGreatCirclePolynomial_on_Icc P hPdeg x.1 u
  refine ⟨q, hqdeg, ?_, ?_, ?_⟩
  · intro t htLower htUpper
    let zplus : Fin n → ℝ :=
      fun i ↦ t * x.1 i + Real.sqrt (1 - t ^ 2) * u i
    let zminus : Fin n → ℝ :=
      fun i ↦ t * x.1 i - Real.sqrt (1 - t ^ 2) * u i
    have hzplus : zplus ∈ sphereSet n :=
      sphereGreatCirclePoint_mem x.1 u hxnorm hunorm horth
        t htLower htUpper
    have hunormNeg : ∑ i, (-u i) ^ 2 = 1 := by
      simpa only [neg_sq] using hunorm
    have horthNeg : ∑ i, x.1 i * (-u i) = 0 := by
      calc
        (∑ i, x.1 i * (-u i)) = -(∑ i, x.1 i * u i) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
        _ = 0 := by rw [horth, neg_zero]
    have hzminus : zminus ∈ sphereSet n := by
      have hz := sphereGreatCirclePoint_mem x.1 (-u) hxnorm hunormNeg
        horthNeg t htLower htUpper
      simpa only [zminus, Pi.neg_apply, mul_neg, sub_eq_add_neg] using hz
    rw [hqeval t htLower htUpper]
    change |MvPolynomial.eval zplus P + MvPolynomial.eval zminus P| ≤ 2 * ‖v‖
    rw [hPval ⟨zplus, hzplus⟩, hPval ⟨zminus, hzminus⟩]
    calc
      |v.1 ⟨zplus, hzplus⟩ + v.1 ⟨zminus, hzminus⟩| ≤
          |v.1 ⟨zplus, hzplus⟩| + |v.1 ⟨zminus, hzminus⟩| :=
        abs_add_le _ _
      _ ≤ ‖v‖ + ‖v‖ := add_le_add
        (by simpa only [Real.norm_eq_abs] using
          ContinuousMap.norm_coe_le_norm v.1 ⟨zplus, hzplus⟩)
        (by simpa only [Real.norm_eq_abs] using
          ContinuousMap.norm_coe_le_norm v.1 ⟨zminus, hzminus⟩)
      _ = 2 * ‖v‖ := by ring
  · have hplus :
        (fun i ↦ a * x.1 i + Real.sqrt (1 - a ^ 2) * u i) = y.1 := by
      funext i
      dsimp only [u]
      change a * x.1 i + Real.sqrt s *
          ((y.1 i - a * x.1 i) / Real.sqrt s) = y.1 i
      rw [mul_div_cancel₀ _ hsqrtne]
      ring
    have hminus :
        (fun i ↦ a * x.1 i - Real.sqrt (1 - a ^ 2) * u i) =
          (sphereAxialReflection x y).1 := by
      rw [sphereAxialReflection_coe]
      funext i
      unfold sphereAxialReflectionRaw
      dsimp only [u]
      change a * x.1 i - Real.sqrt s *
          ((y.1 i - a * x.1 i) / Real.sqrt s) = 2 * a * x.1 i - y.1 i
      rw [mul_div_cancel₀ _ hsqrtne]
      ring
    change q.eval a = v.1 y + v.1 (sphereAxialReflection x y)
    rw [hqeval a ha.1 ha.2, hplus, hminus, hPval y, hPval (sphereAxialReflection x y)]
  · rw [hqeval 1 (by norm_num) (by norm_num)]
    norm_num
    rw [hPval x]
    ring

/-- Algebraic great-circle restriction needed to apply the repository's
univariate Markov inequality to a symmetric axial-reflection difference.
The construction expands an ambient representative into even and odd powers
of the transverse great-circle coordinate; the odd powers cancel. -/
theorem exists_axialReflection_evenRestrictionPolynomial
    {n D : ℕ} (v : spherePolynomialSpace n D) (x y : sphereSet n) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ D ∧
      (∀ t : ℝ, -1 ≤ t → t ≤ 1 → |q.eval t| ≤ 2 * ‖v‖) ∧
      q.eval (∑ i, y.1 i * x.1 i) =
        v.1 y + v.1 (sphereAxialReflection x y) ∧
      q.eval 1 = 2 * v.1 x := by
  by_cases hD : D = 0
  · subst D
    exact exists_axialReflection_evenRestrictionPolynomial_zero v x y
  · by_cases hDone : D = 1
    · subst D
      exact exists_axialReflection_evenRestrictionPolynomial_one v x y
    · by_cases hend : (∑ i, y.1 i * x.1 i) ^ 2 = 1
      · exact exists_axialReflection_evenRestrictionPolynomial_endpoint
          (Nat.one_le_iff_ne_zero.mpr hD) v x y hend
      · exact exists_axialReflection_evenRestrictionPolynomial_nonendpoint v x y hend

/-- The repository's univariate Markov inequality yields the natural sharp
constant after the even great-circle restriction is constructed. -/
theorem spherePolynomial_axialReflection_secondDifference_le_markov
    {n D : ℕ} (v : spherePolynomialSpace n D) (x y : sphereSet n) :
    |v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x| ≤
      (((D : ℝ) ^ 2) * ‖v‖) * sphereChordalSq y.1 x.1 := by
  obtain ⟨q, hqdeg, hqbound, hqeval, hqone⟩ :=
    exists_axialReflection_evenRestrictionPolynomial v x y
  let a : ℝ := ∑ i, y.1 i * x.1 i
  have ha : a ∈ Set.Icc (-1 : ℝ) 1 :=
    sphereDot_mem_Icc y.2 x.2
  have hmarkov :=
    polynomial_eval_sub_eval_one_abs_le_markov q D hqdeg
      (2 * ‖v‖) hqbound a ha
  calc
    |v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x| =
        |q.eval a - q.eval 1| := by
      rw [hqeval, hqone]
    _ ≤ (D : ℝ) ^ 2 * (2 * ‖v‖) * (1 - a) := hmarkov
    _ = (((D : ℝ) ^ 2) * ‖v‖) * sphereChordalSq y.1 x.1 := by
      rw [sphereChordalSq_eq_two_mul_one_sub_dot y.2 x.2]
      change (D : ℝ) ^ 2 * (2 * ‖v‖) * (1 - a) =
        (D : ℝ) ^ 2 * ‖v‖ * (2 * (1 - a))
      ring

/-- The spherical Bernstein estimate in the exact axial-reflection form used
by the cancellation module. -/
theorem spherePolynomial_axialReflection_secondDifference_le
    {n D : ℕ} (_hn : 3 ≤ n) (_hD : 1 ≤ D)
    (v : spherePolynomialSpace n D) (x y : sphereSet n) :
    |v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x| ≤
      (2 * (((D : ℝ) ^ 2) * ‖v‖)) * sphereChordalSq y.1 x.1 := by
  calc
    |v.1 y + v.1 (sphereAxialReflection x y) - 2 * v.1 x| ≤
        (((D : ℝ) ^ 2) * ‖v‖) * sphereChordalSq y.1 x.1 :=
      spherePolynomial_axialReflection_secondDifference_le_markov v x y
    _ ≤ (2 * (((D : ℝ) ^ 2) * ‖v‖)) * sphereChordalSq y.1 x.1 := by
      have hnonneg :
          0 ≤ (((D : ℝ) ^ 2) * ‖v‖) * sphereChordalSq y.1 x.1 :=
        mul_nonneg
          (mul_nonneg (sq_nonneg (D : ℝ)) (norm_nonneg v))
          (sphereChordalSq_nonneg y.1 x.1)
      nlinarith

end QuarticConvergence
end OptimalConvergenceRates

end

