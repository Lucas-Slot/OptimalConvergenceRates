/-
  Explicit degree propagation for the rotational C6 norm of the cube lift.

  The analytic core below derives a first-rotation Bernstein estimate on the
  sphere.  The recursive `sphereRotNorm` definition then gives the required
  degree-six comparison with an explicit dimension-only constant.
-/
import OptimalConvergenceRates.MarkovInequality.BernsteinInequality
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.Radial
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.CenteredBounds
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.LiftCertificate
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.TrigDerivative

open MvPolynomial Finset
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence
open SphereBallTransfers
open ScaledRobinson

/-- The odd-in-sine part of a great-circle restriction, after dividing by
the sine coordinate, is a genuine univariate polynomial of no larger degree.
This complements `exists_evenGreatCirclePolynomial_on_Icc`. -/
theorem exists_oddGreatCirclePolynomial_on_Icc
    {n D : ℕ} (P : MvPolynomial (Fin n) ℝ) (hPdeg : P.totalDegree ≤ D)
    (x u : Fin n → ℝ) :
    ∃ q : Polynomial ℝ,
      q.natDegree ≤ D ∧
      ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
        Real.sqrt (1 - t ^ 2) * q.eval t =
          MvPolynomial.eval
              (fun i ↦ t * x i + Real.sqrt (1 - t ^ 2) * u i) P -
            MvPolynomial.eval
              (fun i ↦ t * x i - Real.sqrt (1 - t ^ 2) * u i) P := by
  let G : MvPolynomial (Fin 3) ℝ := greatCircleTernaryRestriction P x u
  let A : MvPolynomial (Fin 3) ℝ := G - zReflect3 G
  have hAanti : zReflect3 A = -A := by
    dsimp only [A]
    rw [map_sub, zReflect3_involutive]
    ring
  obtain ⟨B, hB⟩ := exists_X_two_mul_zSquareSubst3_of_zReflect3_eq_neg hAanti
  have hGdeg : G.totalDegree ≤ D :=
    (greatCircleTernaryRestriction_totalDegree_le P x u).trans hPdeg
  have hAdeg : A.totalDegree ≤ D := by
    calc
      A.totalDegree ≤ max G.totalDegree (zReflect3 G).totalDegree := by
        dsimp only [A]
        exact MvPolynomial.totalDegree_sub _ _
      _ ≤ D := max_le hGdeg ((zReflect3_totalDegree_le G).trans hGdeg)
  have hBweighted : sourceWeightedDegree3 B ≤ D := by
    apply sourceWeightedDegree3_le_of_X_two_mul_zSquareSubst3_totalDegree_le
    rw [← hB]
    exact hAdeg.trans (by omega)
  let base : Fin 3 → ℝ := ![0, 0, 1]
  let direction : Fin 3 → ℝ := ![1, 0, 0]
  let q : Polynomial ℝ :=
    univariateRestriction (homBallSourceSubst 1 B) base direction
  have hqdeg : q.natDegree ≤ D := by
    calc
      q.natDegree ≤ (homBallSourceSubst 1 B).totalDegree := by
        exact univariateRestriction_natDegree_le
          (homBallSourceSubst 1 B) base direction
      _ ≤ sourceWeightedDegree3 B :=
        homBallSourceSubst_totalDegree_le_weighted 1 B
      _ ≤ D := hBweighted
  refine ⟨q, hqdeg, ?_⟩
  intro t htLower htUpper
  have htSq : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [sq_nonneg (t - 1), sq_nonneg (t + 1)]
  have hline : base + t • direction = ![t, 0, 1] := by
    ext i
    fin_cases i <;> simp [base, direction]
  calc
    Real.sqrt (1 - t ^ 2) * q.eval t =
        Real.sqrt (1 - t ^ 2) *
          MvPolynomial.eval ![t, 0, 1] (homBallSourceSubst 1 B) := by
      dsimp only [q]
      rw [univariateRestriction_eval, hline]
    _ = Real.sqrt (1 - t ^ 2) *
          MvPolynomial.eval ![t, 0, 1 - t ^ 2] B := by
      rw [homBallSourceSubst_one_eval]
    _ = MvPolynomial.eval ![t, 0, Real.sqrt (1 - t ^ 2)]
          ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 B) := by
      simp only [map_mul, eval_X]
      rw [zSquareSubst3_eval, htSq]
      simp
    _ = MvPolynomial.eval ![t, 0, Real.sqrt (1 - t ^ 2)] A := by
      rw [hB]
    _ = MvPolynomial.eval ![t, 0, Real.sqrt (1 - t ^ 2)] G -
          MvPolynomial.eval ![t, 0, Real.sqrt (1 - t ^ 2)] (zReflect3 G) := by
      simp only [A, MvPolynomial.eval_sub]
    _ =
        MvPolynomial.eval
            (fun i ↦ t * x i + Real.sqrt (1 - t ^ 2) * u i) P -
          MvPolynomial.eval
            (fun i ↦ t * x i - Real.sqrt (1 - t ^ 2) * u i) P := by
      dsimp only [G]
      rw [zReflect3_greatCircleTernaryRestriction]
      rw [greatCircleTernaryRestriction_eval,
        greatCircleTernaryRestriction_eval]
      simp only [Pi.neg_apply, mul_neg, sub_eq_add_neg]

/-- The coordinate-gradient differential agrees with the repository's
line-restriction definition of directional derivative. -/
theorem mvPolynomialEvalFDeriv_eq_directionalDeriv
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x u : Fin n → ℝ) :
    mvPolynomialEvalFDeriv P x u = directionalDeriv P x u := by
  have hline : HasDerivAt
      (fun t : ℝ ↦ MvPolynomial.eval (x + t • u) P)
      (directionalDeriv P x u) 0 := by
    simpa only [directionalDeriv, univariateRestriction_eval] using
      (univariateRestriction P x u).hasDerivAt 0
  have hpath : HasDerivAt (fun t : ℝ ↦ x + t • u) u 0 := by
    rw [hasDerivAt_pi]
    intro i
    convert (hasDerivAt_const (x := (0 : ℝ)) (x i)).add
      ((hasDerivAt_id (x := (0 : ℝ))).mul_const (u i)) using 1; simp
  have hchain := (hasFDerivAt_mvPolynomial_eval P x).comp_hasDerivAt_of_eq
    0 hpath (by simp)
  have hchain' : HasDerivAt
      (fun t : ℝ ↦ MvPolynomial.eval (x + t • u) P)
      (mvPolynomialEvalFDeriv P x u) 0 := by
    simpa only [Function.comp_apply] using hchain
  exact hchain'.unique hline

/-- The square-root coordinate of the standard circle chart has zero
derivative at the center. -/
theorem hasDerivAt_sqrt_one_sub_sq_zero :
    HasDerivAt (fun t : ℝ ↦ Real.sqrt (1 - t ^ 2)) 0 0 := by
  have hinner : HasDerivAt (fun t : ℝ ↦ 1 - t ^ 2) 0 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
      ((hasDerivAt_id (x := (0 : ℝ))).pow 2) using 1; norm_num
  convert hinner.sqrt (by norm_num) using 1; norm_num

/-- The standard great-circle chart through `x` in direction `u` has
velocity `u` at its center. -/
theorem hasDerivAt_greatCirclePath_zero
    {n : ℕ} (x u : Fin n → ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ fun i ↦ t * u i + Real.sqrt (1 - t ^ 2) * x i)
      u 0 := by
  rw [hasDerivAt_pi]
  intro i
  convert ((hasDerivAt_id (x := (0 : ℝ))).mul_const (u i)).add
    (hasDerivAt_sqrt_one_sub_sq_zero.mul_const (x i)) using 1; simp

/-- Differentiating polynomial evaluation along the great-circle chart gives
the algebraic directional derivative. -/
theorem hasDerivAt_eval_greatCirclePath_zero
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x u : Fin n → ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ MvPolynomial.eval
        (fun i ↦ t * u i + Real.sqrt (1 - t ^ 2) * x i) P)
      (directionalDeriv P x u) 0 := by
  have hchain := (hasFDerivAt_mvPolynomial_eval P x).comp_hasDerivAt_of_eq 0
    (hasDerivAt_greatCirclePath_zero x u) (by simp)
  have hchain' : HasDerivAt
      (fun t : ℝ ↦ MvPolynomial.eval
        (fun i ↦ t * u i + Real.sqrt (1 - t ^ 2) * x i) P)
      (mvPolynomialEvalFDeriv P x u) 0 := by
    simpa only [Function.comp_apply] using hchain
  rw [mvPolynomialEvalFDeriv_eq_directionalDeriv] at hchain'
  exact hchain'

/-- Bernstein's inequality at the center, applied to the even and odd
great-circle parts, controls every unit tangential derivative. -/
theorem sphere_directionalDeriv_le_bernstein
    {n D : ℕ} (hn : 0 < n) (P : MvPolynomial (Fin n) ℝ)
    (hPdeg : P.totalDegree ≤ D) (x u : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) (hu : ∑ i, u i ^ 2 = 1)
    (horth : ∑ i, x i * u i = 0) :
    |directionalDeriv P x u| ≤ 10 * (D : ℝ) * sphereSupNorm P := by
  let M := sphereSupNorm P
  have hM : 0 ≤ M := sphereSupNorm_nonneg hn P
  have horth' : ∑ i, u i * x i = 0 := by
    calc
      (∑ i, u i * x i) = ∑ i, x i * u i := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = 0 := horth
  obtain ⟨E, hEdeg, hEeval⟩ :=
    exists_evenGreatCirclePolynomial_on_Icc P hPdeg u x
  obtain ⟨O, hOdeg, hOeval⟩ :=
    exists_oddGreatCirclePolynomial_on_Icc P hPdeg u x
  have hEbound : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → |E.eval t| ≤ 2 * M := by
    intro t htLower htUpper
    let zplus : Fin n → ℝ :=
      fun i ↦ t * u i + Real.sqrt (1 - t ^ 2) * x i
    let zminus : Fin n → ℝ :=
      fun i ↦ t * u i - Real.sqrt (1 - t ^ 2) * x i
    have hzplus : zplus ∈ sphereSet n :=
      sphereGreatCirclePoint_mem u x hu hx horth' t htLower htUpper
    have hxneg : ∑ i, (-x i) ^ 2 = 1 := by simpa only [neg_sq] using hx
    have horthneg : ∑ i, u i * (-x i) = 0 := by
      calc
        (∑ i, u i * (-x i)) = -(∑ i, u i * x i) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
        _ = 0 := by rw [horth', neg_zero]
    have hzminus : zminus ∈ sphereSet n := by
      have hz := sphereGreatCirclePoint_mem u (-x) hu hxneg horthneg
        t htLower htUpper
      simpa only [zminus, Pi.neg_apply, mul_neg, sub_eq_add_neg] using hz
    rw [hEeval t htLower htUpper]
    change |MvPolynomial.eval zplus P + MvPolynomial.eval zminus P| ≤ 2 * M
    calc
      |MvPolynomial.eval zplus P + MvPolynomial.eval zminus P| ≤
          |MvPolynomial.eval zplus P| + |MvPolynomial.eval zminus P| := abs_add_le _ _
      _ ≤ M + M := add_le_add (sphereSupNorm_eval_le P zplus hzplus)
        (sphereSupNorm_eval_le P zminus hzminus)
      _ = 2 * M := by ring
  have hOboundHalf : ∀ t : ℝ, -(1 / 2 : ℝ) ≤ t → t ≤ 1 / 2 →
      |O.eval t| ≤ 4 * M := by
    intro t htLower htUpper
    have htIcc : -1 ≤ t ∧ t ≤ 1 := by constructor <;> linarith
    let zplus : Fin n → ℝ :=
      fun i ↦ t * u i + Real.sqrt (1 - t ^ 2) * x i
    let zminus : Fin n → ℝ :=
      fun i ↦ t * u i - Real.sqrt (1 - t ^ 2) * x i
    have hzplus : zplus ∈ sphereSet n :=
      sphereGreatCirclePoint_mem u x hu hx horth' t htIcc.1 htIcc.2
    have hxneg : ∑ i, (-x i) ^ 2 = 1 := by simpa only [neg_sq] using hx
    have horthneg : ∑ i, u i * (-x i) = 0 := by
      calc
        (∑ i, u i * (-x i)) = -(∑ i, u i * x i) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
        _ = 0 := by rw [horth', neg_zero]
    have hzminus : zminus ∈ sphereSet n := by
      have hz := sphereGreatCirclePoint_mem u (-x) hu hxneg horthneg
        t htIcc.1 htIcc.2
      simpa only [zminus, Pi.neg_apply, mul_neg, sub_eq_add_neg] using hz
    have htSq : t ^ 2 ≤ 1 / 4 := by
      nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg (t + 1 / 2)]
    have hsnonneg : 0 ≤ 1 - t ^ 2 := by linarith
    have hsqrtSq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 :=
      Real.sq_sqrt hsnonneg
    have hsqrtLower : (1 / 2 : ℝ) ≤ Real.sqrt (1 - t ^ 2) := by
      nlinarith [Real.sqrt_nonneg (1 - t ^ 2)]
    have hdiff :
        |MvPolynomial.eval zplus P - MvPolynomial.eval zminus P| ≤ 2 * M := by
      calc
        |MvPolynomial.eval zplus P - MvPolynomial.eval zminus P| ≤
            |MvPolynomial.eval zplus P| + |MvPolynomial.eval zminus P| :=
          abs_sub _ _
        _ ≤ M + M := add_le_add (sphereSupNorm_eval_le P zplus hzplus)
          (sphereSupNorm_eval_le P zminus hzminus)
        _ = 2 * M := by ring
    have hprod : Real.sqrt (1 - t ^ 2) * |O.eval t| ≤ 2 * M := by
      rw [← abs_of_nonneg (Real.sqrt_nonneg (1 - t ^ 2)), ← abs_mul]
      rw [hOeval t htIcc.1 htIcc.2]
      exact hdiff
    nlinarith [abs_nonneg (O.eval t)]
  let Ohalf : Polynomial ℝ := O.comp (Polynomial.C (1 / 2 : ℝ) * Polynomial.X)
  have hOhalfdeg : Ohalf.natDegree ≤ D := by
    calc
      Ohalf.natDegree ≤ O.natDegree *
          (Polynomial.C (1 / 2 : ℝ) * Polynomial.X).natDegree := by
        exact Polynomial.natDegree_comp_le
      _ ≤ D * 1 := Nat.mul_le_mul hOdeg (by simp)
      _ = D := Nat.mul_one D
  have hOhalfEval (t : ℝ) : Ohalf.eval t = O.eval (t / 2) := by
    dsimp only [Ohalf]
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring_nf
  have hOhalfbound : ∀ t : ℝ, -1 ≤ t → t ≤ 1 →
      |Ohalf.eval t| ≤ 4 * M := by
    intro t htLower htUpper
    rw [hOhalfEval]
    exact hOboundHalf (t / 2) (by linarith) (by linarith)
  have hEderiv := univariate_bernstein_first_derivative_zero_bound
    E D hEdeg (2 * M) (by positivity) hEbound
  have hOhalfDeriv := univariate_bernstein_first_derivative_zero_bound
    Ohalf D hOhalfdeg (4 * M) (by positivity) hOhalfbound
  have hOhalfDerivEq : (Polynomial.derivative Ohalf).eval 0 =
      (1 / 2 : ℝ) * (Polynomial.derivative O).eval 0 := by
    dsimp only [Ohalf]
    rw [Polynomial.derivative_comp]
    simp [Polynomial.derivative_mul]
  have hOderiv : |(Polynomial.derivative O).eval 0| ≤ 16 * (D : ℝ) * M := by
    rw [hOhalfDerivEq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      at hOhalfDeriv
    nlinarith [abs_nonneg ((Polynomial.derivative O).eval 0)]
  have hEderiv' : |(Polynomial.derivative E).eval 0| ≤ 4 * (D : ℝ) * M := by
    nlinarith
  let fplus : ℝ → ℝ := fun t ↦ MvPolynomial.eval
    (fun i ↦ t * u i + Real.sqrt (1 - t ^ 2) * x i) P
  have heq : fplus =ᶠ[𝓝 0]
      fun t ↦ (E.eval t + Real.sqrt (1 - t ^ 2) * O.eval t) / 2 := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t ht
    have hEven := hEeval t ht.1.le ht.2.le
    have hOdd := hOeval t ht.1.le ht.2.le
    dsimp only [fplus]
    linarith
  have hright : HasDerivAt
      (fun t ↦ (E.eval t + Real.sqrt (1 - t ^ 2) * O.eval t) / 2)
      (((Polynomial.derivative E).eval 0 + (Polynomial.derivative O).eval 0) / 2) 0 := by
    convert ((E.hasDerivAt 0).add
      (hasDerivAt_sqrt_one_sub_sq_zero.mul (O.hasDerivAt 0))).div_const 2 using 1;
        norm_num
  have hfromEq : HasDerivAt fplus
      (((Polynomial.derivative E).eval 0 + (Polynomial.derivative O).eval 0) / 2) 0 :=
    hright.congr_of_eventuallyEq heq
  have hcircle : HasDerivAt fplus (directionalDeriv P x u) 0 := by
    exact hasDerivAt_eval_greatCirclePath_zero P x u
  have hderivEq : directionalDeriv P x u =
      ((Polynomial.derivative E).eval 0 + (Polynomial.derivative O).eval 0) / 2 :=
    hcircle.unique hfromEq
  rw [hderivEq]
  calc
    |((Polynomial.derivative E).eval 0 + (Polynomial.derivative O).eval 0) / 2| ≤
        (|(Polynomial.derivative E).eval 0| + |(Polynomial.derivative O).eval 0|) / 2 := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ ≤ (4 * (D : ℝ) * M + 16 * (D : ℝ) * M) / 2 := by
      exact div_le_div_of_nonneg_right (add_le_add hEderiv' hOderiv) (by norm_num)
    _ = 10 * (D : ℝ) * M := by ring

/-- The same estimate for every tangent vector of Euclidean norm at most one. -/
theorem sphere_tangent_directionalDeriv_le_bernstein
    {n D : ℕ} (hn : 0 < n) (P : MvPolynomial (Fin n) ℝ)
    (hPdeg : P.totalDegree ≤ D) (x v : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) (hv : ∑ i, v i ^ 2 ≤ 1)
    (horth : ∑ i, x i * v i = 0) :
    |directionalDeriv P x v| ≤ 10 * (D : ℝ) * sphereSupNorm P := by
  let s : ℝ := ∑ i, v i ^ 2
  have hsnonneg : 0 ≤ s := Finset.sum_nonneg fun i _hi ↦ sq_nonneg (v i)
  by_cases hs : s = 0
  · have hvzero : v = 0 := by
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _hj ↦ sq_nonneg (v j))).mp hs i (Finset.mem_univ i)
      simp only [Pi.zero_apply]
      nlinarith
    rw [hvzero]
    have hz := directionalDeriv_smul P x (0 : Fin n → ℝ) 0
    simp only [zero_smul, zero_mul] at hz
    rw [hz, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg D))
      (sphereSupNorm_nonneg hn P)
  · have hspos : 0 < s := lt_of_le_of_ne hsnonneg (Ne.symm hs)
    let r : ℝ := Real.sqrt s
    let u : Fin n → ℝ := fun i ↦ v i / r
    have hrpos : 0 < r := Real.sqrt_pos.2 hspos
    have hrsq : r ^ 2 = s := Real.sq_sqrt hsnonneg
    have hunorm : ∑ i, u i ^ 2 = 1 := by
      calc
        (∑ i, u i ^ 2) = (∑ i, v i ^ 2) / r ^ 2 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _hi
          dsimp only [u]
          ring
        _ = s / s := by rw [show (∑ i, v i ^ 2) = s by rfl, hrsq]
        _ = 1 := div_self hs
    have huorth : ∑ i, x i * u i = 0 := by
      calc
        (∑ i, x i * u i) = (∑ i, x i * v i) / r := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _hi
          dsimp only [u]
          ring
        _ = 0 := by rw [horth, zero_div]
    have hvscale : v = r • u := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      dsimp only [u]
      field_simp
    have hrle : r ≤ 1 := by
      dsimp only [r]
      nlinarith [Real.sqrt_nonneg s, Real.sq_sqrt hsnonneg]
    have hunit := sphere_directionalDeriv_le_bernstein
      hn P hPdeg x u hx hunorm huorth
    rw [hvscale, directionalDeriv_smul, abs_mul, abs_of_nonneg hrpos.le]
    calc
      r * |directionalDeriv P x u| ≤
          r * (10 * (D : ℝ) * sphereSupNorm P) :=
        mul_le_mul_of_nonneg_left hunit hrpos.le
      _ ≤ 1 * (10 * (D : ℝ) * sphereSupNorm P) := by
        apply mul_le_mul_of_nonneg_right hrle
        exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg D))
          (sphereSupNorm_nonneg hn P)
      _ = 10 * (D : ℝ) * sphereSupNorm P := one_mul _

/-- The coordinate rotation field is the corresponding algebraic directional
derivative. -/
theorem directionalDeriv_coordinateRotation
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (i j : Fin n) :
    directionalDeriv P x (Pi.single j (x i) - Pi.single i (x j)) =
      MvPolynomial.eval x (rotationDeriv i j P) := by
  rw [← mvPolynomialEvalFDeriv_eq_directionalDeriv]
  rw [eval_rotationDeriv_eq]
  simp [mvPolynomialEvalFDeriv, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Explicit spherical Bernstein estimate for one coordinate rotation. -/
theorem sphereSupNorm_rotationDeriv_le_bernstein
    {n D : ℕ} (hn : 0 < n) (P : MvPolynomial (Fin n) ℝ)
    (hPdeg : P.totalDegree ≤ D) (i j : Fin n) :
    sphereSupNorm (rotationDeriv i j P) ≤
      10 * (D : ℝ) * sphereSupNorm P := by
  apply sphereSupNorm_le_of_bound hn
  intro x hx
  let v : Fin n → ℝ := Pi.single j (x i) - Pi.single i (x j)
  have hxnorm : ∑ k, x k ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic] using hx
  have hvnorm : ∑ k, v k ^ 2 ≤ 1 := by
    by_cases hij : i = j
    · subst j
      simp [v]
    · have hsum : ∑ k, v k ^ 2 = x i ^ 2 + x j ^ 2 := by
        dsimp only [v, Pi.sub_apply, Pi.single_apply]
        simp_rw [sub_sq]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp [Pi.single_apply, hij]
      rw [hsum, ← hxnorm]
      have hpairsum : ∑ k ∈ ({i, j} : Finset (Fin n)), x k ^ 2 =
          x i ^ 2 + x j ^ 2 := by simp [hij]
      rw [← hpairsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (show {i, j} ⊆ (Finset.univ : Finset (Fin n)) by simp)
        (fun k _hk _hnot ↦ sq_nonneg (x k))
  have hvorth : ∑ k, x k * v k = 0 := by
    dsimp only [v, Pi.sub_apply, Pi.single_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp [Pi.single_apply]
    ring
  have hbound := sphere_tangent_directionalDeriv_le_bernstein
    hn P hPdeg x v hxnorm hvnorm hvorth
  rw [show v = Pi.single j (x i) - Pi.single i (x j) by rfl,
    directionalDeriv_coordinateRotation] at hbound
  exact hbound


/-- A uniform first-rotation estimate for sphere polynomials of ambient degree
at most `D`.  This is the precise analytic input needed to unfold the
recursive rotational norm. -/
def SphereFirstRotationBound (n D : ℕ) (K : ℝ) : Prop :=
  ∀ (P : MvPolynomial (Fin n) ℝ), P.totalDegree ≤ D →
    ∀ i j : Fin n,
      sphereSupNorm (rotationDeriv i j P) ≤ K * sphereSupNorm P

/-- A convenient name for the explicit coarse constant obtained from the repository’s center
Bernstein inequality after splitting the great-circle restriction into its even and odd parts. -/
def SphereBernsteinRotationBound (n D : ℕ) : Prop :=
  SphereFirstRotationBound n D (10 * (D : ℝ))

/-- The even/odd great-circle argument proves the uniform first-rotation
bound required by the recursive C6 estimate. -/
theorem sphereBernsteinRotationBound {n D : ℕ} (hn : 0 < n) :
    SphereBernsteinRotationBound n D := by
  intro P hPdeg i j
  exact sphereSupNorm_rotationDeriv_le_bernstein hn P hPdeg i j


/-- A first-rotation estimate propagates through every level of the recursive
rotational norm.  The factor `n²` is exactly the number of ordered coordinate
rotation pairs occurring at each recursive step. -/
theorem sphereRotNorm_le_pow_of_firstRotationBound
    {n D : ℕ} (hn : 0 < n) {K : ℝ} (hK : 0 ≤ K)
    (hrotation : SphereFirstRotationBound n D K)
    (k : ℕ) (P : MvPolynomial (Fin n) ℝ) (hPdeg : P.totalDegree ≤ D) :
    sphereRotNorm k P ≤
      (1 + (n : ℝ) ^ 2 * K) ^ k * sphereSupNorm P := by
  have hfactor : 0 ≤ 1 + (n : ℝ) ^ 2 * K := by positivity
  induction k generalizing P with
  | zero =>
      simp [sphereRotNorm]
  | succ k ih =>
      rw [sphereRotNorm]
      calc
        sphereRotNorm k P +
              ∑ i : Fin n, ∑ j : Fin n, sphereRotNorm k (rotationDeriv i j P)
            ≤ (1 + (n : ℝ) ^ 2 * K) ^ k * sphereSupNorm P +
              ∑ i : Fin n, ∑ j : Fin n,
                (1 + (n : ℝ) ^ 2 * K) ^ k *
                  sphereSupNorm (rotationDeriv i j P) := by
            apply add_le_add (ih P hPdeg)
            apply Finset.sum_le_sum
            intro i _hi
            apply Finset.sum_le_sum
            intro j _hj
            exact ih (rotationDeriv i j P)
              ((rotationDeriv_totalDegree_le i j P).trans hPdeg)
        _ ≤ (1 + (n : ℝ) ^ 2 * K) ^ k * sphereSupNorm P +
              ∑ _i : Fin n, ∑ _j : Fin n,
                (1 + (n : ℝ) ^ 2 * K) ^ k *
                  (K * sphereSupNorm P) := by
            apply add_le_add (le_refl _)
            apply Finset.sum_le_sum
            intro i _hi
            apply Finset.sum_le_sum
            intro j _hj
            exact mul_le_mul_of_nonneg_left (hrotation P hPdeg i j)
              (pow_nonneg hfactor k)
        _ = (1 + (n : ℝ) ^ 2 * K) ^ (k + 1) * sphereSupNorm P := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            rw [pow_succ]
            ring

/-- Six recursive rotations cost the sixth power of the one-step factor. -/
theorem sphereC6Norm_le_of_firstRotationBound
    {n D : ℕ} (hn : 0 < n) {K : ℝ} (hK : 0 ≤ K)
    (hrotation : SphereFirstRotationBound n D K)
    (P : MvPolynomial (Fin n) ℝ) (hPdeg : P.totalDegree ≤ D) :
    sphereC6Norm P ≤
      (1 + (n : ℝ) ^ 2 * K) ^ 6 * sphereSupNorm P := by
  exact sphereRotNorm_le_pow_of_firstRotationBound hn hK hrotation 6 P hPdeg

/-- The proved first-rotation Bernstein factor `10D` yields an explicit
degree-six bound. -/
theorem sphereC6Norm_le_of_bernsteinRotationBound
    {n D : ℕ} (hn : 0 < n) (hD : 1 ≤ D)
    (hrotation : SphereBernsteinRotationBound n D)
    (P : MvPolynomial (Fin n) ℝ) (hPdeg : P.totalDegree ≤ D) :
    sphereC6Norm P ≤
      (1 + 10 * (n : ℝ) ^ 2) ^ 6 * (D : ℝ) ^ 6 * sphereSupNorm P := by
  have hraw := sphereC6Norm_le_of_firstRotationBound hn
    (K := 10 * (D : ℝ)) (by positivity) hrotation P hPdeg
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hbase : 1 + (n : ℝ) ^ 2 * (10 * (D : ℝ)) ≤
      (1 + 10 * (n : ℝ) ^ 2) * (D : ℝ) := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hpow :
      (1 + (n : ℝ) ^ 2 * (10 * (D : ℝ))) ^ 6 ≤
        ((1 + 10 * (n : ℝ) ^ 2) * (D : ℝ)) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hbase 6
  calc
    sphereC6Norm P ≤
        (1 + (n : ℝ) ^ 2 * (10 * (D : ℝ))) ^ 6 * sphereSupNorm P := hraw
    _ ≤ ((1 + 10 * (n : ℝ) ^ 2) * (D : ℝ)) ^ 6 * sphereSupNorm P :=
      mul_le_mul_of_nonneg_right hpow (sphereSupNorm_nonneg hn P)
    _ = (1 + 10 * (n : ℝ) ^ 2) ^ 6 * (D : ℝ) ^ 6 * sphereSupNorm P := by
      rw [mul_pow]

/-- The explicit dimension-only constant obtained after substituting the
degree-`2n+1` polynomial cube map into six rotational derivatives. -/
def cubeSphereC6DimensionConstant (n : ℕ) : ℝ :=
  (1 + 10 * ((2 * n + 1 : ℕ) : ℝ) ^ 2) ^ 6 *
    ((2 * n + 1 : ℕ) : ℝ) ^ 6

theorem cubeSphereC6DimensionConstant_pos (n : ℕ) :
    0 < cubeSphereC6DimensionConstant n := by
  unfold cubeSphereC6DimensionConstant
  positivity

/-- Conditional explicit lift comparison.  All algebraic and degree
propagation is discharged here; the remaining input is exactly the spherical
first-rotation Bernstein inequality in ambient dimension `2n+1`. -/
theorem cubeSphereC6Norm_le_of_bernsteinRotationBound
    {n : ℕ} (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ)
    (hrotation : SphereBernsteinRotationBound (2 * n + 1)
      ((2 * n + 1) * max p.totalDegree 1)) :
    cubeSphereC6Norm n p ≤
      cubeSphereC6DimensionConstant n *
        ((max p.totalDegree 1 : ℕ) : ℝ) ^ 6 *
          sphereSupNorm (cubeSphereLift n p) := by
  let e : ℕ := max p.totalDegree 1
  let D : ℕ := (2 * n + 1) * e
  have he : 1 ≤ e := by exact le_max_right _ _
  have hD : 1 ≤ D := by
    calc
      1 = 1 * 1 := by omega
      _ ≤ (2 * n + 1) * e := Nat.mul_le_mul (by omega) he
      _ = D := by rfl
  have hdeg : (cubeSphereLift n p).totalDegree ≤ D := by
    exact (cubeSphereLift_totalDegree_le n p).trans
      (Nat.mul_le_mul_left (2 * n + 1) (le_max_left _ _))
  have hmain := sphereC6Norm_le_of_bernsteinRotationBound
    (n := 2 * n + 1) (D := D) (by omega) hD hrotation
    (cubeSphereLift n p) hdeg
  change sphereC6Norm (cubeSphereLift n p) ≤ _
  calc
    sphereC6Norm (cubeSphereLift n p) ≤
        (1 + 10 * ((2 * n + 1 : ℕ) : ℝ) ^ 2) ^ 6 *
          (D : ℝ) ^ 6 * sphereSupNorm (cubeSphereLift n p) := hmain
    _ = cubeSphereC6DimensionConstant n * (e : ℝ) ^ 6 *
          sphereSupNorm (cubeSphereLift n p) := by
      simp only [D, cubeSphereC6DimensionConstant, Nat.cast_mul]
      rw [mul_pow]
      ring
    _ = cubeSphereC6DimensionConstant n *
          ((max p.totalDegree 1 : ℕ) : ℝ) ^ 6 *
            sphereSupNorm (cubeSphereLift n p) := by rfl

/-- Centered, bounded-degree consequence of the conditional lift comparison.
It already has the exact public cube oscillation and degree-six interface
needed by the general hierarchy theorem. -/
theorem cubeSphereC6Norm_centered_le_of_bernsteinRotationBound
    {n d : ℕ} (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ)
    (hpdeg : p.totalDegree ≤ d)
    (hrotation : SphereBernsteinRotationBound (2 * n + 1)
      ((2 * n + 1) * max d 1)) :
    cubeSphereC6Norm n (p - MvPolynomial.C (polyMin p)) ≤
      cubeSphereC6DimensionConstant n *
        ((max d 1 : ℕ) : ℝ) ^ 6 * (polyMax p - polyMin p) := by
  let q := p - MvPolynomial.C (polyMin p)
  let D : ℕ := (2 * n + 1) * max d 1
  have hqdeg : q.totalDegree ≤ d := centerAtPolyMin_totalDegree_le_of_le hpdeg
  have hD : 1 ≤ D := by
    calc
      1 = 1 * 1 := by omega
      _ ≤ (2 * n + 1) * max d 1 :=
        Nat.mul_le_mul (by omega) (le_max_right _ _)
      _ = D := by rfl
  have hliftdeg : (cubeSphereLift n q).totalDegree ≤ D := by
    exact (cubeSphereLift_totalDegree_le n q).trans
      (Nat.mul_le_mul_left (2 * n + 1) (hqdeg.trans (le_max_left _ _)))
  have hmain := sphereC6Norm_le_of_bernsteinRotationBound
    (n := 2 * n + 1) (D := D) (by omega) hD hrotation
    (cubeSphereLift n q) hliftdeg
  change sphereC6Norm (cubeSphereLift n q) ≤ _
  calc
    sphereC6Norm (cubeSphereLift n q) ≤
        (1 + 10 * ((2 * n + 1 : ℕ) : ℝ) ^ 2) ^ 6 *
          (D : ℝ) ^ 6 * sphereSupNorm (cubeSphereLift n q) := hmain
    _ = cubeSphereC6DimensionConstant n * ((max d 1 : ℕ) : ℝ) ^ 6 *
          polySupNorm q := by
      rw [sphereSupNorm_cubeSphereLift hn q]
      simp only [D, cubeSphereC6DimensionConstant, Nat.cast_mul]
      rw [mul_pow]
      ring
    _ = cubeSphereC6DimensionConstant n * ((max d 1 : ℕ) : ℝ) ^ 6 *
          (polyMax p - polyMin p) := by
      rw [show q = p - MvPolynomial.C (polyMin p) by rfl,
        polySupNorm_centerAtPolyMin_eq]



/-- Explicit degree-six comparison between the rotational C6 norm and the
sphere restriction sup norm. -/
theorem sphereC6Norm_le_degree_six
    {n D : ℕ} (hn : 0 < n) (hD : 1 ≤ D)
    (P : MvPolynomial (Fin n) ℝ) (hPdeg : P.totalDegree ≤ D) :
    sphereC6Norm P ≤
      (1 + 10 * (n : ℝ) ^ 2) ^ 6 * (D : ℝ) ^ 6 * sphereSupNorm P := by
  exact sphereC6Norm_le_of_bernsteinRotationBound hn hD
    (sphereBernsteinRotationBound hn) P hPdeg

/-- Uniform explicit degree-six regularity estimate for every lifted cube
polynomial.  The constant depends only on the cube dimension. -/
theorem cubeSphereC6Norm_le
    {n : ℕ} (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    cubeSphereC6Norm n p ≤
      cubeSphereC6DimensionConstant n *
        ((max p.totalDegree 1 : ℕ) : ℝ) ^ 6 *
          sphereSupNorm (cubeSphereLift n p) := by
  exact cubeSphereC6Norm_le_of_bernsteinRotationBound hn p
    (sphereBernsteinRotationBound (by omega : 0 < 2 * n + 1))

/-- Centering at the cube minimum converts the explicit lift estimate into
the oscillation form used by the general Schmüdgen and Putinar rates. -/
theorem cubeSphereC6Norm_centered_le
    {n d : ℕ} (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ)
    (hpdeg : p.totalDegree ≤ d) :
    cubeSphereC6Norm n (p - MvPolynomial.C (polyMin p)) ≤
      cubeSphereC6DimensionConstant n *
        ((max d 1 : ℕ) : ℝ) ^ 6 * (polyMax p - polyMin p) := by
  exact cubeSphereC6Norm_centered_le_of_bernsteinRotationBound hn p hpdeg
    (sphereBernsteinRotationBound (by omega : 0 < 2 * n + 1))


end QuarticConvergence
end OptimalConvergenceRates

end
