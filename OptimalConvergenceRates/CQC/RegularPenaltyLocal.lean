import OptimalConvergenceRates.CQC.RegularPenaltyUniform

/-!
# The local equation-to-distance estimate
-/

noncomputable section

open MvPolynomial Finset Set Matrix

namespace OptimalConvergenceRates
namespace CQCInternal

variable {N m : ℕ}

/-- Values of a finite polynomial equation family. -/
def equationValuesAt (h : Fin m → MvPolynomial (Fin N) ℝ)
    (z : Fin N → ℝ) : Fin m → ℝ :=
  fun i ↦ MvPolynomial.eval z (h i)

theorem jacobian_mulVec_eq_evalFDeriv
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (v w : Fin N → ℝ) :
    (polynomialJacobianAt h v) *ᵥ w =
      fun i ↦ QuarticConvergence.mvPolynomialEvalFDeriv (h i) v w := by
  funext i
  simp [polynomialJacobianAt, Matrix.mulVec, dotProduct,
    mvPolynomialEvalFDeriv_apply]

/-- The sup norm of the equation values is controlled by their polynomial
sum of squares. -/
theorem norm_equationValuesAt_sq_le
    (h : Fin m → MvPolynomial (Fin N) ℝ) (z : Fin N → ℝ) :
    ‖equationValuesAt h z‖ ^ 2 ≤
      MvPolynomial.eval z (equationSquareSum h) := by
  let S := MvPolynomial.eval z (equationSquareSum h)
  have hS : 0 ≤ S := eval_equationSquareSum_nonneg h z
  have hcoord : ∀ i, ‖equationValuesAt h z i‖ ≤ Real.sqrt S := by
    intro i
    have hi : (MvPolynomial.eval z (h i)) ^ 2 ≤ S := by
      dsimp [S]
      rw [eval_equationSquareSum]
      exact Finset.single_le_sum
        (fun j _ ↦ sq_nonneg (MvPolynomial.eval z (h j)))
        (Finset.mem_univ i)
    have hsqrt := Real.sq_sqrt hS
    rw [Real.norm_eq_abs]
    change |MvPolynomial.eval z (h i)| ≤ Real.sqrt S
    nlinarith [sq_abs (MvPolynomial.eval z (h i)),
      abs_nonneg (MvPolynomial.eval z (h i)), Real.sqrt_nonneg S]
  have hnorm : ‖equationValuesAt h z‖ ≤ Real.sqrt S :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2 hcoord
  have hsqrt := Real.sq_sqrt hS
  nlinarith [norm_nonneg (equationValuesAt h z), Real.sqrt_nonneg S]

/-- A finite polynomial family has a uniform vector-valued quadratic Taylor
remainder on a compact convex set. -/
theorem exists_equationFamily_taylor_bound
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (A : Set (Fin N → ℝ))
    (hAcompact : IsCompact A) (hAconvex : Convex ℝ A) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v ∈ A, ∀ z ∈ A,
      ‖equationValuesAt h z - equationValuesAt h v -
          (polynomialJacobianAt h v) *ᵥ (z - v)‖ ≤
        L * ‖z - v‖ ^ 2 := by
  have hexists : ∀ i : Fin m, ∃ L : ℝ, 0 ≤ L ∧
      ∀ v ∈ A, ∀ z ∈ A,
        |MvPolynomial.eval z (h i) - MvPolynomial.eval v (h i) -
            QuarticConvergence.mvPolynomialEvalFDeriv (h i) v (z - v)| ≤
          L * ‖z - v‖ ^ 2 := fun i ↦
    exists_eval_taylor_bound (h i) A hAcompact hAconvex
  choose L hL hTaylor using hexists
  let Ltotal := ∑ i, L i
  have hLtotal : 0 ≤ Ltotal := Finset.sum_nonneg fun i _ ↦ hL i
  refine ⟨Ltotal, hLtotal, ?_⟩
  intro v hv z hz
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hLtotal (sq_nonneg _))).2
  intro i
  rw [Real.norm_eq_abs]
  have hLi : L i ≤ Ltotal := by
    exact Finset.single_le_sum (fun j _ ↦ hL j) (Finset.mem_univ i)
  have hi := hTaylor i v hv z hz
  rw [jacobian_mulVec_eq_evalFDeriv]
  exact hi.trans (mul_le_mul_of_nonneg_right hLi (sq_nonneg _))

/-- Near a compact regular zero set, squared distance of a nearest normal
point is controlled by the sum of squared equation values. -/
theorem exists_local_regular_error_bound
    (h : Fin m → MvPolynomial (Fin N) ℝ)
    (A : Set (Fin N → ℝ))
    (hAcompact : IsCompact A) (hAconvex : Convex ℝ A)
    (hVsub : polynomialZeroSet h ⊆ A)
    (hne : (polynomialZeroSet h).Nonempty)
    (hcompact : IsCompact (polynomialZeroSet h))
    (hregular : ∀ v ∈ polynomialZeroSet h,
      LinearIndependent ℝ (fun i ↦ polynomialGradientAt (h i) v)) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧
      ∀ z ∈ A, ∀ v ∈ polynomialZeroSet h,
        ∀ coeff : Fin m → ℝ,
        z - v = ∑ i, coeff i • polynomialGradientAt (h i) v →
        ‖z - v‖ ≤ rho →
        ‖z - v‖ ^ 2 ≤
          C * MvPolynomial.eval z (equationSquareSum h) := by
  obtain ⟨sigma, hsigma, hlower⟩ :=
    exists_uniform_normal_lower_bound h hne hcompact hregular
  obtain ⟨L, hL, hTaylor⟩ :=
    exists_equationFamily_taylor_bound h A hAcompact hAconvex
  let rho := sigma / (2 * (L + 1))
  let C := 4 / sigma ^ 2
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨rho, C, hrho, hC, ?_⟩
  intro z hz v hv coeff hw hsmall
  have hvA : v ∈ A := hVsub hv
  let w := z - v
  have hlower' : sigma * ‖w‖ ≤
      ‖(polynomialJacobianAt h v) *ᵥ w‖ :=
    hlower v hv w ⟨coeff, hw⟩
  have hrem := hTaylor v hvA z hz
  have hvzero : equationValuesAt h v = 0 := by
    funext i
    exact hv i
  have hrem' :
      ‖equationValuesAt h z - (polynomialJacobianAt h v) *ᵥ w‖ ≤
        L * ‖w‖ ^ 2 := by
    simpa [w, hvzero] using hrem
  have htriangle : ‖(polynomialJacobianAt h v) *ᵥ w‖ ≤
      ‖equationValuesAt h z‖ +
        ‖equationValuesAt h z - (polynomialJacobianAt h v) *ᵥ w‖ := by
    calc
      ‖(polynomialJacobianAt h v) *ᵥ w‖ =
          ‖equationValuesAt h z -
            (equationValuesAt h z - (polynomialJacobianAt h v) *ᵥ w)‖ := by
              congr 1
              abel
      _ ≤ _ := norm_sub_le _ _
  have hLrho : L * rho ≤ sigma / 2 := by
    dsimp [rho]
    have hLp : 0 < L + 1 := by linarith
    field_simp
    nlinarith
  have hLw : L * ‖w‖ ≤ sigma / 2 :=
    (mul_le_mul_of_nonneg_left hsmall hL).trans hLrho
  have hquad : L * ‖w‖ ^ 2 ≤ sigma / 2 * ‖w‖ := by
    calc
      L * ‖w‖ ^ 2 = (L * ‖w‖) * ‖w‖ := by ring
      _ ≤ (sigma / 2) * ‖w‖ :=
        mul_le_mul_of_nonneg_right hLw (norm_nonneg _)
  have htriangle' : ‖(polynomialJacobianAt h v) *ᵥ w‖ ≤
      ‖equationValuesAt h z‖ + L * ‖w‖ ^ 2 :=
    htriangle.trans (by gcongr)
  have hhalf : sigma / 2 * ‖w‖ ≤ ‖equationValuesAt h z‖ := by
    nlinarith
  have hvalues := norm_equationValuesAt_sq_le h z
  have hsigmaSq : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have hsquare : (sigma / 2 * ‖w‖) ^ 2 ≤
      ‖equationValuesAt h z‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (div_nonneg hsigma.le (by norm_num)) (norm_nonneg _))
      (norm_nonneg _)).2 hhalf
  have hcross : sigma ^ 2 * ‖w‖ ^ 2 ≤
      4 * MvPolynomial.eval z (equationSquareSum h) := by
    nlinarith
  dsimp [C]
  rw [show 4 / sigma ^ 2 * MvPolynomial.eval z (equationSquareSum h) =
      (4 * MvPolynomial.eval z (equationSquareSum h)) / sigma ^ 2 by ring]
  apply (le_div_iff₀ hsigmaSq).2
  simpa [w, mul_comm, mul_left_comm, mul_assoc] using hcross

end CQCInternal
end OptimalConvergenceRates

end
