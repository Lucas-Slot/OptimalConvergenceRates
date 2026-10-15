/-
  Pointwise multiplier estimates and Chebyshev extrapolation from the
  positive slab to the negative face in the sharp Archimedean example.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.SlabRestriction
import OptimalConvergenceRates.MarkovInequality.ChebyshevEndpoint

noncomputable section
open Finset MvPolynomial Polynomial
open OptimalConvergenceRates

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Restrict a trivariate polynomial to the `z` line through `(a,b)`. -/
def sharpRestrictAB (a b : Real) (p : MvPolynomial (Fin 3) Real) :
    Polynomial Real :=
  MvPolynomial.aeval ![Polynomial.C a, Polynomial.C b, Polynomial.X] p

/-- Evaluation of the `z`-line restriction. -/
@[simp] theorem sharpRestrictAB_eval (a b z : Real) (p : MvPolynomial (Fin 3) Real) :
    (sharpRestrictAB a b p).eval z = MvPolynomial.eval ![a, b, z] p := by
  rw [sharpRestrictAB]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
        Polynomial.eval_mul]
      rw [hp]
      congr 1
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]

/-- Restriction to a coordinate line does not increase total degree. -/
theorem sharpRestrictAB_natDegree_le (a b : Real) (p : MvPolynomial (Fin 3) Real) :
    (sharpRestrictAB a b p).natDegree <= p.totalDegree := by
  have h := MvPolynomial.aeval_natDegree_le p (le_refl p.totalDegree)
    ![Polynomial.C a, Polynomial.C b, Polynomial.X] (n := 1) (by
      intro i
      fin_cases i <;> simp)
  simpa [sharpRestrictAB] using h

/-- Coarse Chebyshev growth at distance `O(t)` outside `[-1,1]`.  The
constant is deliberately generous so later algebra stays simple. -/
theorem chebyshevT_abs_le_exp_slab
    (d : Nat) (hd : 1 <= d) {t y : Real}
    (ht0 : 0 <= t) (ht : t <= (1 : Real) / 64)
    (hy : |y| <= 1 + 32 * t) :
    |(chebyshevT d).eval y| <=
      Real.exp (100 * (d : Real) * Real.sqrt t) := by
  have hsqrt0 : 0 <= Real.sqrt t := Real.sqrt_nonneg t
  have hsqrtSq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht0
  have htsqrt : t <= Real.sqrt t := by
    nlinarith [Real.sq_sqrt ht0]
  have hexpOne : 1 <= Real.exp (100 * (d : Real) * Real.sqrt t) := by
    calc
      (1 : Real) = Real.exp 0 := by simp
      _ <= _ := Real.exp_le_exp.mpr (by positivity)
  by_cases hyin : |y| <= 1
  · exact (chebyshevT_abs_le_one d y (abs_le.mp hyin).1
      (abs_le.mp hyin).2).trans hexpOne
  · push Not at hyin
    have hyge : 1 <= |y| := le_of_lt hyin
    have hyupper : |y| <= 3 / 2 := by
      calc
        |y| <= 1 + 32 * t := hy
        _ <= 3 / 2 := by linarith
    have hrad : |y| ^ 2 - 1 <= 96 * t := by
      have hleft : |y| - 1 <= 32 * t := by linarith
      have hright : |y| + 1 <= 3 := by linarith
      calc
        |y| ^ 2 - 1 = (|y| - 1) * (|y| + 1) := by ring
        _ <= (32 * t) * 3 := by
          exact mul_le_mul hleft hright (by linarith) (by positivity)
        _ = 96 * t := by ring
    have hsqrtRad : Real.sqrt (|y| ^ 2 - 1) <= 10 * Real.sqrt t := by
      calc
        Real.sqrt (|y| ^ 2 - 1) <= Real.sqrt (100 * t) := by
          apply Real.sqrt_le_sqrt
          linarith
        _ = 10 * Real.sqrt t := by
          calc
            Real.sqrt (100 * t) = Real.sqrt 100 * Real.sqrt t := Real.sqrt_mul (by norm_num) t
            _ = 10 * Real.sqrt t := by
              rw [show (100 : Real) = 10 ^ 2 by norm_num,
                Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) <= 10)]
    have hbase : |y| + Real.sqrt (|y| ^ 2 - 1) <=
        1 + 42 * Real.sqrt t := by
      calc
        |y| + Real.sqrt (|y| ^ 2 - 1) <=
            (1 + 32 * t) + 10 * Real.sqrt t := add_le_add hy hsqrtRad
        _ <= 1 + 42 * Real.sqrt t := by nlinarith
    have hupper := chebyshevT_upper_bound d |y| hyge hd
    have hnonneg : 0 <= |y| + Real.sqrt (|y| ^ 2 - 1) := by positivity
    have hpow : (|y| + Real.sqrt (|y| ^ 2 - 1)) ^ d <=
        (1 + 42 * Real.sqrt t) ^ d :=
      pow_le_pow_left₀ hnonneg hbase d
    have hexp : (1 + 42 * Real.sqrt t) ^ d <=
        Real.exp ((42 * Real.sqrt t) * (d : Real)) :=
      one_add_pow_le_exp (42 * Real.sqrt t) (by positivity) d
    have hT : (chebyshevT d).eval |y| <=
        Real.exp (100 * (d : Real) * Real.sqrt t) := by
      calc
        (chebyshevT d).eval |y| <=
            (|y| + Real.sqrt (|y| ^ 2 - 1)) ^ d := hupper
        _ <= (1 + 42 * Real.sqrt t) ^ d := hpow
        _ <= Real.exp ((42 * Real.sqrt t) * (d : Real)) := hexp
        _ <= Real.exp (100 * (d : Real) * Real.sqrt t) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_nonneg (Nat.cast_nonneg d)
            (Real.sqrt_nonneg t)]
    have hext := chebyshevT_extremal d (chebyshevT d)
      (by rw [natDegree_chebyshevT]) y hyge
    have hsup : polySupNormUni (chebyshevT d) <= 1 := by
      apply polySupNormUni_le_of_bound
      intro x hx1 hx2
      exact chebyshevT_abs_le_one d x hx1 hx2
    have hTnonneg := chebyshevT_nonneg_ge_one d |y| hyge
    exact hext.trans ((mul_le_of_le_one_left hTnonneg hsup).trans hT)


/-- Extrapolate from `[t,1/4]` to `-t`. -/
theorem polynomial_extrapolate_negative_slab
    {d : Nat} (hd : 2 <= d) {t M : Real}
    (ht0 : 0 < t) (ht : t <= (1 : Real) / 64)
    (p : Polynomial Real) (hdeg : p.natDegree <= d)
    (hbound : forall z : Real, t <= z -> z <= (1 : Real) / 4 ->
      |p.eval z| <= M) :
    |p.eval (-t)| <=
      Real.exp (100 * (d : Real) * Real.sqrt t) * M := by
  let L : Real := 16 * (d : Real) ^ 2 * t
  let E : Real := Real.exp (100 * (d : Real) * Real.sqrt t)
  have hdpos : 0 < (d : Real) := Nat.cast_pos.mpr (by omega)
  have htquarter : t < (1 : Real) / 4 := lt_of_le_of_lt ht (by norm_num)
  have hL : 0 < L := by dsimp [L]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hEone : 1 <= E := by
    dsimp [E]
    calc
      (1 : Real) = Real.exp 0 := by simp
      _ <= _ := Real.exp_le_exp.mpr (by positivity)
  have hCsufficient : forall y : Real,
      |y| <= 1 + 2 * L / (d : Real) ^ 2 ->
      |(chebyshevT d).eval y| <= E := by
    intro y hy
    apply chebyshevT_abs_le_exp_slab d (by omega) ht0.le ht
    have hdne : (d : Real) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hdpos)
    have harg : 1 + 2 * L / (d : Real) ^ 2 = 1 + 32 * t := by
      dsimp [L]
      field_simp [hdne]
      ring
    rw [← harg]
    exact hy
  have hdist : -t ∈ Set.Icc
      (t - L * ((1 : Real) / 4 - t) / (d : Real) ^ 2)
      ((1 : Real) / 4 + L * ((1 : Real) / 4 - t) / (d : Real) ^ 2) := by
    constructor
    · have hdne : (d : Real) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hdpos)
      have hratio : L * ((1 : Real) / 4 - t) / (d : Real) ^ 2 =
          16 * t * ((1 : Real) / 4 - t) := by
        dsimp [L]
        field_simp [hdne]
      rw [hratio]
      have hsmall : t <= (1 : Real) / 8 := ht.trans (by norm_num)
      nlinarith [ht0.le]
    · have hratioNonneg : 0 <=
          L * ((1 : Real) / 4 - t) / (d : Real) ^ 2 := by
        exact div_nonneg (mul_nonneg hL.le (sub_nonneg.mpr htquarter.le))
          (sq_nonneg (d : Real))
      linarith
  exact affine_chebyshev_extrapolate L E M t ((1 : Real) / 4) (-t)
    hL hE hEone htquarter d hd p hdeg hbound hCsufficient hdist
end OptimalConvergenceRates.GeneralArchimedean

/-- If `x*p(x)` is bounded on `[0,1/4]` and `p` is nonnegative there,
then `p` itself is bounded by `O(d^2)`, including at the face `x=0`. -/
theorem quarterInterval_face_multiplier_bound
    {d : Nat} (hd : 2 <= d) (p : Polynomial Real)
    (hdeg : p.natDegree <= d)
    (hnonneg : forall x : Real, 0 <= x -> x <= (1 : Real) / 4 ->
      0 <= p.eval x)
    (hweighted : forall x : Real, 0 <= x -> x <= (1 : Real) / 4 ->
      x * p.eval x <= 1)
    {x : Real} (hx0 : 0 <= x) (hx4 : x <= (1 : Real) / 4) :
    p.eval x <= 8 * Real.exp 6 * (d : Real) ^ 2 := by
  let delta : Real := 1 / (8 * (d : Real) ^ 2)
  let M : Real := 8 * (d : Real) ^ 2
  have hdpos : 0 < (d : Real) := Nat.cast_pos.mpr (by omega)
  have hdsq : 0 < (d : Real) ^ 2 := sq_pos_of_pos hdpos
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta4 : delta < (1 : Real) / 4 := by
    dsimp [delta]
    rw [div_lt_iff₀ (by positivity : (0 : Real) < 8 * (d : Real) ^ 2)]
    have hdcast : (2 : Real) <= d := by exact_mod_cast hd
    nlinarith [sq_nonneg ((d : Real) - 2)]
  have hM : 0 < M := by dsimp [M]; positivity
  have hdeltaM : delta * M = 1 := by
    dsimp [delta, M]
    field_simp [ne_of_gt hdsq]
  have hCone : (1 : Real) <= Real.exp 6 := by
    calc
      (1 : Real) = Real.exp 0 := by simp
      _ <= Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
  by_cases hdx : delta <= x
  · have hp0 := hnonneg x hx0 hx4
    have hxp := hweighted x hx0 hx4
    have hdp : delta * p.eval x <= 1 := by
      calc
        delta * p.eval x <= x * p.eval x :=
          mul_le_mul_of_nonneg_right hdx hp0
        _ <= 1 := hxp
    have hpM : p.eval x <= M := by
      rw [← hdeltaM] at hdp
      exact le_of_mul_le_mul_left hdp hdelta
    calc
      p.eval x <= M := hpM
      _ <= Real.exp 6 * M := by
        simpa using mul_le_mul_of_nonneg_right hCone hM.le
      _ = 8 * Real.exp 6 * (d : Real) ^ 2 := by dsimp [M]; ring
  · push Not at hdx
    have hbound : forall z : Real, delta <= z -> z <= (1 : Real) / 4 ->
        |p.eval z| <= M := by
      intro z hzdelta hz4
      have hz0 := hdelta.le.trans hzdelta
      have hp0 := hnonneg z hz0 hz4
      rw [abs_of_nonneg hp0]
      have hzp := hweighted z hz0 hz4
      have hdp : delta * p.eval z <= 1 :=
        (mul_le_mul_of_nonneg_right hzdelta hp0).trans hzp
      rw [← hdeltaM] at hdp
      exact le_of_mul_le_mul_left hdp hdelta
    have hCsufficient : forall y : Real,
        |y| <= 1 + 2 / (d : Real) ^ 2 ->
        |(chebyshevT d).eval y| <= Real.exp 6 := by
      intro y hy
      exact chebyshevT_abs_le_exp_six_near_one d hd y
        (hy.trans (by
          have hquot : 2 / (d : Real) ^ 2 <= 4 / (d : Real) ^ 2 :=
            (div_le_div_iff₀ hdsq hdsq).mpr (by nlinarith [hdsq])
          linarith))
    have hdist : x ∈ Set.Icc
        (delta - ((1 : Real) / 4 - delta) / (d : Real) ^ 2)
        ((1 : Real) / 4 + ((1 : Real) / 4 - delta) / (d : Real) ^ 2) := by
      constructor
      · have hleft : delta - ((1 : Real) / 4 - delta) / (d : Real) ^ 2 <= 0 := by
          dsimp [delta]
          field_simp [ne_of_gt hdsq]
          have hdcast : (2 : Real) <= d := by exact_mod_cast hd
          nlinarith [sq_nonneg ((d : Real) - 2)]
        exact hleft.trans hx0
      · have htail : 0 <= ((1 : Real) / 4 - delta) / (d : Real) ^ 2 := by
          exact div_nonneg (sub_nonneg.mpr hdelta4.le) hdsq.le
        linarith
    have hext := affine_chebyshev_extrapolate 1 (Real.exp 6) M
      delta ((1 : Real) / 4) x (by norm_num) (Real.exp_pos 6) hCone
      hdelta4 d hd p hdeg hbound (by
        intro y hy
        simpa using hCsufficient y (by simpa using hy))
      (by simpa using hdist)
    calc
      p.eval x <= |p.eval x| := le_abs_self _
      _ <= Real.exp 6 * M := hext
      _ = 8 * Real.exp 6 * (d : Real) ^ 2 := by dsimp [M]; ring
