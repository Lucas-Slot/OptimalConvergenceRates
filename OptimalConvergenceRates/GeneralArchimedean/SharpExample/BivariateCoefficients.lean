/-
  Bivariate coefficient-vector bounds obtained by applying the
  quarter-interval vector Markov estimate in each coordinate.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.VectorMarkov
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.TruncatedMoment

noncomputable section

open Finset MvPolynomial Polynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Regard a bivariate polynomial as a polynomial in its first coordinate
after fixing the second coordinate. -/
def restrictSecond (b : Real) (p : MvPolynomial (Fin 2) Real) :
    Polynomial Real :=
  (AddMonoidAlgebra.coeff p).sum fun alpha c => Polynomial.monomial (alpha 0) (c * b ^ alpha 1)

/-- The polynomial in the second coordinate formed by the coefficients of
a fixed power of the first coordinate. -/
def firstCoefficientPolynomial (i : Nat)
    (p : MvPolynomial (Fin 2) Real) : Polynomial Real :=
  (AddMonoidAlgebra.coeff p).sum fun alpha c =>
    if alpha 0 = i then Polynomial.monomial (alpha 1) c else 0

theorem restrictSecond_eval (a b : Real)
    (p : MvPolynomial (Fin 2) Real) :
    (restrictSecond b p).eval a = MvPolynomial.eval ![a, b] p := by
  rw [restrictSecond, MvPolynomial.sum_def, MvPolynomial.eval_eq]
  simp_rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro alpha _halpha
  simp only [Polynomial.eval_monomial]
  have hexponents :
      (Finset.prod alpha.support fun x => ![a, b] x ^ alpha x) =
        a ^ alpha 0 * b ^ alpha 1 := by
    change alpha.prod (fun x e => ![a, b] x ^ e) = _
    rw [Finsupp.prod_fintype]
    all_goals simp [Fin.prod_univ_two]
  rw [hexponents]
  ring

theorem firstCoefficientPolynomial_eval (i : Nat) (b : Real)
    (p : MvPolynomial (Fin 2) Real) :
    (firstCoefficientPolynomial i p).eval b =
      (restrictSecond b p).coeff i := by
  rw [firstCoefficientPolynomial, restrictSecond, MvPolynomial.sum_def, MvPolynomial.sum_def]
  rw [Polynomial.eval_finsetSum]
  rw [<- Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  apply Finset.sum_congr rfl
  intro alpha _halpha
  by_cases hi : alpha 0 = i
  · subst i
    simp
  · simp [hi, Polynomial.coeff_monomial]

theorem restrictSecond_natDegree_le (b : Real)
    (p : MvPolynomial (Fin 2) Real) :
    (restrictSecond b p).natDegree <= p.totalDegree := by
  rw [restrictSecond, MvPolynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro alpha halpha
  exact (Polynomial.natDegree_monomial_le _).trans
    (support_coordinate_le_totalDegree p halpha 0)

theorem firstCoefficientPolynomial_natDegree_le (i : Nat)
    (p : MvPolynomial (Fin 2) Real) :
    (firstCoefficientPolynomial i p).natDegree <= p.totalDegree := by
  rw [firstCoefficientPolynomial, MvPolynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro alpha halpha
  by_cases hi : alpha 0 = i
  · rw [ite_eq_left hi]
    exact (Polynomial.natDegree_monomial_le _).trans
      (support_coordinate_le_totalDegree p halpha 1)
  · rw [ite_eq_right hi]
    simp

theorem firstCoefficientPolynomial_coeff (i j : Nat)
    (p : MvPolynomial (Fin 2) Real) :
    (firstCoefficientPolynomial i p).coeff j =
      p.coeff (bivarExponent i j) := by
  classical
  rw [firstCoefficientPolynomial, MvPolynomial.sum_def]
  rw [<- Polynomial.lcoeff_apply, map_sum]
  simp only [Polynomial.lcoeff_apply]
  let e := bivarExponent i j
  by_cases he : e ∈ p.support
  · rw [Finset.sum_eq_single e]
    · simp [e]
    · intro alpha halpha hne
      by_cases hi : alpha 0 = i
      · have hj : alpha 1 ≠ j := by
          intro hjEq
          apply hne
          rw [<- bivarExponent_of_exponents alpha, hi, hjEq]
        simp [hi, hj, Polynomial.coeff_monomial]
      · simp [hi]
    · simp [he]
  · rw [Finset.sum_eq_zero]
    · exact (MvPolynomial.notMem_support_iff.mp he).symm
    · intro alpha halpha
      by_cases hi : alpha 0 = i
      · have hj : alpha 1 ≠ j := by
          intro hjEq
          have : alpha = e := by
            rw [<- bivarExponent_of_exponents alpha, hi, hjEq]
          exact he (this ▸ halpha)
        simp [hi, hj, Polynomial.coeff_monomial]
      · simp [hi]

/-- Coefficient-vector Markov bound for bivariate polynomial vectors on
`[0,1/4]^2`. -/
theorem bivariate_vector_coeff_bound
    {N d i j : Nat} {M : Real}
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hM : 0 <= M) (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M) :
    OptimalConvergenceRates.interiorVecNorm
        (fun k => (q k).coeff (bivarExponent i j)) <=
      (8 : Real) ^ (i + j) * (d : Real) ^ (2 * (i + j)) * M := by
  let Pi : Fin N -> Polynomial Real :=
    fun k => firstCoefficientPolynomial i (q k)
  have hPiDeg : forall k, (Pi k).natDegree <= d := by
    intro k
    exact (firstCoefficientPolynomial_natDegree_le i (q k)).trans (hdeg k)
  have hFirst (b : Real) (hb0 : 0 <= b) (hb4 : b <= (1 : Real) / 4) :
      OptimalConvergenceRates.interiorVecNorm (fun k => (Pi k).eval b) <=
        (8 : Real) ^ i * (d : Real) ^ (2 * i) * M := by
    let P : Fin N -> Polynomial Real := fun k => restrictSecond b (q k)
    have hPDeg : forall k, (P k).natDegree <= d := by
      intro k
      exact (restrictSecond_natDegree_le b (q k)).trans (hdeg k)
    have hPBound : forall a : Real, 0 <= a -> a <= (1 : Real) / 4 ->
        OptimalConvergenceRates.interiorVecNorm (fun k => (P k).eval a) <= M := by
      intro a ha0 ha4
      simpa [P, restrictSecond_eval] using hbound a b ha0 ha4 hb0 hb4
    have hcoeff := quarterInterval_vector_coeff P hM hPDeg hPBound (k := i)
    simpa [Pi, P, firstCoefficientPolynomial_eval] using hcoeff
  have hsecond := quarterInterval_vector_coeff Pi
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hM)
    hPiDeg hFirst (k := j)
  simp only [Pi, firstCoefficientPolynomial_coeff] at hsecond
  calc
    OptimalConvergenceRates.interiorVecNorm
        (fun k => (q k).coeff (bivarExponent i j)) <=
      (8 : Real) ^ j * (d : Real) ^ (2 * j) *
        ((8 : Real) ^ i * (d : Real) ^ (2 * i) * M) := hsecond
    _ = (8 : Real) ^ (i + j) * (d : Real) ^ (2 * (i + j)) * M := by
      rw [pow_add, show 2 * (i + j) = 2 * i + 2 * j by omega, pow_add]
      ring

end OptimalConvergenceRates.GeneralArchimedean

end
