/-
  Dimension-free coefficient bounds for polynomial vectors on the
  quarter interval used in the sharp-example moment argument.
-/
import OptimalConvergenceRates.GeneralArchimedean.UnivariateSupNorm
import OptimalConvergenceRates.BasicNotions.SOSVector

noncomputable section

open Finset Polynomial

namespace OptimalConvergenceRates.GeneralArchimedean

private theorem weightedPolynomial_natDegree_le {N d : Nat}
    (P : Fin N -> Polynomial Real) (u : Fin N -> Real)
    (hdeg : forall i, (P i).natDegree <= d) :
    (∑ i : Fin N, C (u i) * P i).natDegree <= d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _hi
  calc
    (C (u i) * P i).natDegree <= (C (u i)).natDegree + (P i).natDegree :=
      Polynomial.natDegree_mul_le
    _ <= 0 + d := by
      rw [Polynomial.natDegree_C]
      exact Nat.add_le_add_left (hdeg i) 0
    _ = d := by omega

private theorem weightedPolynomial_eval {N : Nat}
    (P : Fin N -> Polynomial Real) (u : Fin N -> Real) (x : Real) :
    (∑ i : Fin N, C (u i) * P i).eval x =
      OptimalConvergenceRates.vecDot u (fun i => (P i).eval x) := by
  unfold OptimalConvergenceRates.vecDot
  simp_rw [<- Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp

private theorem weightedPolynomial_iterateDerivative_eval {N ell : Nat}
    (P : Fin N -> Polynomial Real) (u : Fin N -> Real) (x : Real) :
    ((Polynomial.derivative^[ell])
        (∑ i : Fin N, C (u i) * P i)).eval x =
      ∑ i : Fin N, u i *
        ((Polynomial.derivative^[ell]) (P i)).eval x := by
  rw [Polynomial.iterate_derivative_sum]
  simp_rw [<- Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Polynomial.iterate_derivative_C_mul]
  simp

private theorem iterateDerivative_comp_affine
    (ell : Nat) (p : Polynomial Real) (s c : Real) :
    (Polynomial.derivative^[ell])
        (p.comp (C s * Polynomial.X + C c)) =
      C (s ^ ell) *
        ((Polynomial.derivative^[ell]) p).comp
          (C s * Polynomial.X + C c) := by
  induction ell generalizing p with
  | zero => simp
  | succ ell ih =>
      rw [Function.iterate_succ']
      simp only [Function.comp_apply]
      rw [ih p]
      rw [Polynomial.derivative_mul]
      have hconst : Polynomial.derivative (C (s ^ ell)) =
          (0 : Polynomial Real) := Polynomial.derivative_C
      rw [hconst, zero_mul, zero_add, Polynomial.derivative_comp]
      simp [Polynomial.derivative_add, Polynomial.derivative_mul,
        Polynomial.derivative_C, Polynomial.derivative_X, pow_succ]
      ring

/-- General-order vector Markov inequality at the left endpoint of
`[0,1/4]`.  The constant is independent of the vector dimension. -/
theorem quarterInterval_vector_iterateDerivative_zero
    {N d ell : Nat} {M : Real} (P : Fin N -> Polynomial Real)
    (hM : 0 <= M) (hdeg : forall i, (P i).natDegree <= d)
    (hbound : forall x : Real, 0 <= x -> x <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm (fun i => (P i).eval x) <= M) :
    OptimalConvergenceRates.interiorVecNorm
        (fun i => ((Polynomial.derivative^[ell]) (P i)).eval 0) <=
      (8 : Real) ^ ell * (d : Real) ^ (2 * ell) * M := by
  let D : Fin N -> Real :=
    fun i => ((Polynomial.derivative^[ell]) (P i)).eval 0
  by_cases hDzero : OptimalConvergenceRates.interiorVecNorm D = 0
  · simpa [D, hDzero] using
      mul_nonneg (mul_nonneg (by positivity : 0 <= (8 : Real) ^ ell)
        (by positivity : 0 <= (d : Real) ^ (2 * ell))) hM
  · let u : Fin N -> Real :=
      fun i => D i / OptimalConvergenceRates.interiorVecNorm D
    let R : Polynomial Real := ∑ i : Fin N, C (u i) * P i
    let phi : Polynomial Real := C ((1 : Real) / 8) * Polynomial.X + C (1 / 8)
    let S : Polynomial Real := R.comp phi
    have hRdeg : R.natDegree <= d := by
      dsimp [R]
      exact weightedPolynomial_natDegree_le P u hdeg
    have hphiDeg : phi.natDegree <= 1 := by
      dsimp [phi]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (Polynomial.natDegree_mul_le.trans (by simp)) (by simp))
    have hSdeg : S.natDegree <= d := by
      dsimp [S]
      calc
        (R.comp phi).natDegree <= R.natDegree * phi.natDegree :=
          Polynomial.natDegree_comp_le
        _ <= d * 1 := Nat.mul_le_mul hRdeg hphiDeg
        _ = d := by omega
    have hSsup : polySupNormUni S <= M := by
      apply polySupNormUni_le_of_bound
      intro t htleft htright
      have ht : |t| <= 1 := abs_le.mpr <| And.intro htleft htright
      let x : Real := (t + 1) / 8
      have hx0 : 0 <= x := by dsimp [x]; linarith
      have hx4 : x <= (1 : Real) / 4 := by dsimp [x]; linarith
      have hdot := OptimalConvergenceRates.abs_vecDot_unit_le (v := D)
        (by simpa [OptimalConvergenceRates.vecNorm, OptimalConvergenceRates.vecSqNorm,
          OptimalConvergenceRates.interiorVecNorm, OptimalConvergenceRates.interiorVecSqNorm]
          using hDzero)
        (fun i => (P i).eval x)
      have hnorm : OptimalConvergenceRates.vecNorm (fun i => (P i).eval x) <= M := by
        simpa [OptimalConvergenceRates.vecNorm, OptimalConvergenceRates.vecSqNorm,
          OptimalConvergenceRates.interiorVecNorm, OptimalConvergenceRates.interiorVecSqNorm]
          using hbound x hx0 hx4
      have heval : S.eval t = OptimalConvergenceRates.vecDot u
          (fun i => (P i).eval x) := by
        dsimp [S]
        rw [Polynomial.eval_comp]
        have hphi : phi.eval t = x := by
          dsimp [phi, x]
          simp
          ring
        rw [hphi]
        dsimp [R]
        exact weightedPolynomial_eval P u x
      rw [heval]
      exact hdot.trans hnorm
    have hmarkov := OptimalConvergenceRates.univariate_markov_general_inside
      S d ell hSdeg (-1) (by norm_num : |(-1 : Real)| <= 1)
    rw [OptimalConvergenceRates.GeneralArchimedean.iteratedDeriv_polynomial_eval_eq]
      at hmarkov
    have hRderiv : ((Polynomial.derivative^[ell]) R).eval 0 =
        OptimalConvergenceRates.interiorVecNorm D := by
      dsimp [R]
      rw [weightedPolynomial_iterateDerivative_eval]
      change OptimalConvergenceRates.vecDot
          (fun i => D i / OptimalConvergenceRates.interiorVecNorm D) D =
        OptimalConvergenceRates.interiorVecNorm D
      exact OptimalConvergenceRates.vecDot_unit_self (v := D)
        (by simpa [OptimalConvergenceRates.vecNorm, OptimalConvergenceRates.vecSqNorm,
          OptimalConvergenceRates.interiorVecNorm, OptimalConvergenceRates.interiorVecSqNorm]
          using hDzero)
    have hSderiv : ((Polynomial.derivative^[ell]) S).eval (-1) =
        ((1 : Real) / 8) ^ ell * OptimalConvergenceRates.interiorVecNorm D := by
      dsimp [S]
      rw [iterateDerivative_comp_affine]
      simp [hRderiv]
    change |((Polynomial.derivative^[ell]) S).eval (-1)| <= _ at hmarkov
    rw [hSderiv, abs_mul, abs_of_nonneg (by positivity :
      0 <= ((1 : Real) / 8) ^ ell),
      abs_of_nonneg (OptimalConvergenceRates.interiorVecNorm_nonneg D)] at hmarkov
    have hscaled : ((1 : Real) / 8) ^ ell *
        OptimalConvergenceRates.interiorVecNorm D <=
      (d : Real) ^ (2 * ell) * M :=
      hmarkov.trans (mul_le_mul_of_nonneg_left hSsup (by positivity))
    have hscalePos : 0 < ((1 : Real) / 8) ^ ell := by positivity
    have hdivide : OptimalConvergenceRates.interiorVecNorm D <=
        ((d : Real) ^ (2 * ell) * M) / ((1 : Real) / 8) ^ ell := by
      apply (le_div_iff₀ hscalePos).2
      simpa [mul_comm] using hscaled
    have hinv : (((1 : Real) / 8) ^ ell)⁻¹ = (8 : Real) ^ ell := by
      rw [<- inv_pow]
      norm_num
    change OptimalConvergenceRates.interiorVecNorm D <=
      (8 : Real) ^ ell * (d : Real) ^ (2 * ell) * M
    calc
      OptimalConvergenceRates.interiorVecNorm D <= _ := hdivide
      _ = _ := by rw [div_eq_mul_inv, hinv]; ring

/-- Coefficient-vector form of the quarter-interval Markov estimate. -/
theorem quarterInterval_vector_coeff
    {N d k : Nat} {M : Real} (P : Fin N -> Polynomial Real)
    (hM : 0 <= M) (hdeg : forall i, (P i).natDegree <= d)
    (hbound : forall x : Real, 0 <= x -> x <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm (fun i => (P i).eval x) <= M) :
    OptimalConvergenceRates.interiorVecNorm (fun i => (P i).coeff k) <=
      (8 : Real) ^ k * (d : Real) ^ (2 * k) * M := by
  have hderiv := quarterInterval_vector_iterateDerivative_zero
    P hM hdeg hbound (ell := k)
  have hfactorial : (1 : Real) <= Nat.factorial k := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos k)
  have hscale : OptimalConvergenceRates.interiorVecNorm
      (fun i => ((Polynomial.derivative^[k]) (P i)).eval 0) =
      (Nat.factorial k : Real) *
        OptimalConvergenceRates.interiorVecNorm (fun i => (P i).coeff k) := by
    simp_rw [iterate_derivative_eval_zero]
    exact OptimalConvergenceRates.interiorVecNorm_smul_abs
      (Nat.factorial k : Real) (fun i => (P i).coeff k) |>.trans <| by
        rw [abs_of_nonneg]
        positivity
  rw [hscale] at hderiv
  exact (le_mul_of_one_le_left
    (OptimalConvergenceRates.interiorVecNorm_nonneg _) hfactorial).trans hderiv

end OptimalConvergenceRates.GeneralArchimedean

end
