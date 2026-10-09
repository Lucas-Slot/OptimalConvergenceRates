/-
  Dimension-independent coefficient estimates for the high-degree tail of
  a vector sum of squares.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.TailSplit

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

private theorem abs_interiorVecDot_le {N : Nat} (u v : Fin N -> Real) :
    |OptimalConvergenceRates.vecDot u v| <=
      OptimalConvergenceRates.interiorVecNorm u *
        OptimalConvergenceRates.interiorVecNorm v := by
  simpa [OptimalConvergenceRates.vecNorm, OptimalConvergenceRates.vecSqNorm,
    OptimalConvergenceRates.interiorVecNorm, OptimalConvergenceRates.interiorVecSqNorm] using
    OptimalConvergenceRates.abs_vecDot_le_vecNorm_mul u v

/-- Exact convolution formula for a coefficient of the SOS tail. -/
theorem sharpTailPolynomial_coeff_eq {N D : Nat}
    (q : Fin N -> MvPolynomial (Fin 2) Real) (gamma : Fin 2 →₀ Nat) :
    (sharpTailPolynomial D q).coeff gamma =
      ∑ x ∈ Finset.antidiagonal gamma,
        (2 * OptimalConvergenceRates.vecDot
            (fun k => (sharpLowPart D (q k)).coeff x.1)
            (fun k => (sharpHighPart D (q k)).coeff x.2) +
          OptimalConvergenceRates.vecDot
            (fun k => (sharpHighPart D (q k)).coeff x.1)
            (fun k => (sharpHighPart D (q k)).coeff x.2)) := by
  classical
  rw [sharpTailPolynomial, MvPolynomial.coeff_sum]
  simp_rw [pow_two, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_mul]
  calc
    ∑ k : Fin N,
        (2 * (∑ x ∈ Finset.antidiagonal gamma,
              (sharpLowPart D (q k)).coeff x.1 *
                (sharpHighPart D (q k)).coeff x.2) +
          (∑ x ∈ Finset.antidiagonal gamma,
              (sharpHighPart D (q k)).coeff x.1 *
                (sharpHighPart D (q k)).coeff x.2)) =
      ∑ k : Fin N, ∑ x ∈ Finset.antidiagonal gamma,
        (2 * ((sharpLowPart D (q k)).coeff x.1 *
              (sharpHighPart D (q k)).coeff x.2) +
          (sharpHighPart D (q k)).coeff x.1 *
            (sharpHighPart D (q k)).coeff x.2) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum, Finset.sum_add_distrib]
    _ = ∑ x ∈ Finset.antidiagonal gamma, ∑ k : Fin N,
        (2 * ((sharpLowPart D (q k)).coeff x.1 *
              (sharpHighPart D (q k)).coeff x.2) +
          (sharpHighPart D (q k)).coeff x.1 *
            (sharpHighPart D (q k)).coeff x.2) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_add_distrib, <- Finset.mul_sum]
      rfl

theorem sharpLowPart_coeffVecNorm_le {N D d : Nat} {M : Real}
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hM : 0 <= M) (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M)
    (alpha : Fin 2 →₀ Nat) :
    OptimalConvergenceRates.interiorVecNorm
        (fun k => (sharpLowPart D (q k)).coeff alpha) <=
      (8 : Real) ^ (alpha 0 + alpha 1) *
        (d : Real) ^ (2 * (alpha 0 + alpha 1)) * M := by
  by_cases halpha : alpha.sum (fun _ e => e) < D
  · have hcoeff : (fun k => (sharpLowPart D (q k)).coeff alpha) =
        fun k => (q k).coeff alpha := by
      funext k
      rw [sharpLowPart_coeff, if_pos halpha]
    rw [hcoeff]
    have hmark := bivariate_vector_coeff_bound q hM hdeg hbound
      (i := alpha 0) (j := alpha 1)
    rw [bivarExponent_of_exponents alpha] at hmark
    exact hmark
  · have hzero : (fun k => (sharpLowPart D (q k)).coeff alpha) =
        fun _ => 0 := by
      funext k
      rw [sharpLowPart_coeff, if_neg halpha]
    rw [hzero]
    calc
      OptimalConvergenceRates.interiorVecNorm (fun _ : Fin N => (0 : Real)) = 0 := by
        simp [OptimalConvergenceRates.interiorVecNorm, OptimalConvergenceRates.interiorVecSqNorm]
      _ <= _ := by positivity

theorem sharpHighPart_coeffVecNorm_le {N D d : Nat} {M : Real}
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hM : 0 <= M) (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M)
    (alpha : Fin 2 →₀ Nat) :
    OptimalConvergenceRates.interiorVecNorm
        (fun k => (sharpHighPart D (q k)).coeff alpha) <=
      (8 : Real) ^ (alpha 0 + alpha 1) *
        (d : Real) ^ (2 * (alpha 0 + alpha 1)) * M := by
  by_cases halpha : D <= alpha.sum (fun _ e => e)
  · have hcoeff : (fun k => (sharpHighPart D (q k)).coeff alpha) =
        fun k => (q k).coeff alpha := by
      funext k
      rw [sharpHighPart_coeff, if_pos halpha]
    rw [hcoeff]
    have hmark := bivariate_vector_coeff_bound q hM hdeg hbound
      (i := alpha 0) (j := alpha 1)
    rw [bivarExponent_of_exponents alpha] at hmark
    exact hmark
  · have hzero : (fun k => (sharpHighPart D (q k)).coeff alpha) =
        fun _ => 0 := by
      funext k
      rw [sharpHighPart_coeff, if_neg halpha]
    rw [hzero]
    calc
      OptimalConvergenceRates.interiorVecNorm (fun _ : Fin N => (0 : Real)) = 0 := by
        simp [OptimalConvergenceRates.interiorVecNorm, OptimalConvergenceRates.interiorVecSqNorm]
      _ <= _ := by positivity

/-- Each tail coefficient is controlled by a convolution of the
dimension-free coefficient-vector envelopes. -/
theorem abs_sharpTailPolynomial_coeff_le {N D d : Nat} {M : Real}
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hM : 0 <= M) (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M)
    (gamma : Fin 2 →₀ Nat) :
    |(sharpTailPolynomial D q).coeff gamma| <=
      ∑ _x ∈ Finset.antidiagonal gamma,
        3 * (8 : Real) ^ (gamma 0 + gamma 1) *
          (d : Real) ^ (2 * (gamma 0 + gamma 1)) * M ^ 2 := by
  rw [sharpTailPolynomial_coeff_eq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  have hxadd : x.1 + x.2 = gamma := Finset.mem_antidiagonal.mp hx
  have hxzero : x.1 0 + x.2 0 = gamma 0 := by
    simpa using (Finsupp.ext_iff.mp hxadd 0)
  have hxone : x.1 1 + x.2 1 = gamma 1 := by
    simpa using (Finsupp.ext_iff.mp hxadd 1)
  have hlow := sharpLowPart_coeffVecNorm_le (D := D) q hM hdeg hbound x.1
  have hhighOne := sharpHighPart_coeffVecNorm_le (D := D) q hM hdeg hbound x.1
  have hhighTwo := sharpHighPart_coeffVecNorm_le (D := D) q hM hdeg hbound x.2
  have hdotLow := abs_interiorVecDot_le
    (fun k => (sharpLowPart D (q k)).coeff x.1)
    (fun k => (sharpHighPart D (q k)).coeff x.2)
  have hdotHigh := abs_interiorVecDot_le
    (fun k => (sharpHighPart D (q k)).coeff x.1)
    (fun k => (sharpHighPart D (q k)).coeff x.2)
  calc
    |2 * OptimalConvergenceRates.vecDot
          (fun k => (sharpLowPart D (q k)).coeff x.1)
          (fun k => (sharpHighPart D (q k)).coeff x.2) +
        OptimalConvergenceRates.vecDot
          (fun k => (sharpHighPart D (q k)).coeff x.1)
          (fun k => (sharpHighPart D (q k)).coeff x.2)|
        <= 2 * (OptimalConvergenceRates.interiorVecNorm
              (fun k => (sharpLowPart D (q k)).coeff x.1) *
            OptimalConvergenceRates.interiorVecNorm
              (fun k => (sharpHighPart D (q k)).coeff x.2)) +
          OptimalConvergenceRates.interiorVecNorm
              (fun k => (sharpHighPart D (q k)).coeff x.1) *
            OptimalConvergenceRates.interiorVecNorm
              (fun k => (sharpHighPart D (q k)).coeff x.2) := by
          calc
            |_ + _| <= |2 * OptimalConvergenceRates.vecDot
                (fun k => (sharpLowPart D (q k)).coeff x.1)
                (fun k => (sharpHighPart D (q k)).coeff x.2)| +
              |OptimalConvergenceRates.vecDot
                (fun k => (sharpHighPart D (q k)).coeff x.1)
                (fun k => (sharpHighPart D (q k)).coeff x.2)| := abs_add_le _ _
            _ <= _ := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
              exact add_le_add (mul_le_mul_of_nonneg_left hdotLow (by norm_num))
                hdotHigh
    _ <= 3 * (8 : Real) ^ (gamma 0 + gamma 1) *
          (d : Real) ^ (2 * (gamma 0 + gamma 1)) * M ^ 2 := by
      rw [<- hxzero, <- hxone]
      have hdegree : x.1 0 + x.2 0 + (x.1 1 + x.2 1) =
          (x.1 0 + x.1 1) + (x.2 0 + x.2 1) := by omega
      rw [hdegree]
      have htwoDegree : 2 * ((x.1 0 + x.1 1) + (x.2 0 + x.2 1)) =
          2 * (x.1 0 + x.1 1) + 2 * (x.2 0 + x.2 1) := by omega
      rw [show (8 : Real) ^ ((x.1 0 + x.1 1) + (x.2 0 + x.2 1)) =
          8 ^ (x.1 0 + x.1 1) * 8 ^ (x.2 0 + x.2 1) by rw [pow_add],
        htwoDegree,
        show (d : Real) ^ (2 * (x.1 0 + x.1 1) + 2 * (x.2 0 + x.2 1)) =
          d ^ (2 * (x.1 0 + x.1 1)) * d ^ (2 * (x.2 0 + x.2 1)) by rw [pow_add]]
      have hnonOne : 0 <= (8 : Real) ^ (x.1 0 + x.1 1) *
          (d : Real) ^ (2 * (x.1 0 + x.1 1)) * M := by positivity
      have hnonTwo : 0 <= (8 : Real) ^ (x.2 0 + x.2 1) *
          (d : Real) ^ (2 * (x.2 0 + x.2 1)) * M := by positivity
      have hlprod := mul_le_mul hlow hhighTwo
        (OptimalConvergenceRates.interiorVecNorm_nonneg _)
        hnonOne
      have hhprod := mul_le_mul hhighOne hhighTwo
        (OptimalConvergenceRates.interiorVecNorm_nonneg _)
        hnonOne
      calc
        2 * (OptimalConvergenceRates.interiorVecNorm
              (fun k => (sharpLowPart D (q k)).coeff x.1) *
            OptimalConvergenceRates.interiorVecNorm
              (fun k => (sharpHighPart D (q k)).coeff x.2)) +
          OptimalConvergenceRates.interiorVecNorm
              (fun k => (sharpHighPart D (q k)).coeff x.1) *
            OptimalConvergenceRates.interiorVecNorm
              (fun k => (sharpHighPart D (q k)).coeff x.2)
            <= 2 *
                ((8 : Real) ^ (x.1 0 + x.1 1) *
                  (d : Real) ^ (2 * (x.1 0 + x.1 1)) * M *
                ((8 : Real) ^ (x.2 0 + x.2 1) *
                  (d : Real) ^ (2 * (x.2 0 + x.2 1)) * M)) +
              ((8 : Real) ^ (x.1 0 + x.1 1) *
                  (d : Real) ^ (2 * (x.1 0 + x.1 1)) * M *
                ((8 : Real) ^ (x.2 0 + x.2 1) *
                  (d : Real) ^ (2 * (x.2 0 + x.2 1)) * M)) := by
              linarith
        _ = _ := by ring

end OptimalConvergenceRates.GeneralArchimedean

end
