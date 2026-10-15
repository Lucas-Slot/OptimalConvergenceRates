/- Dimension-independent symmetric-hole estimates specialized to the Motzkin proof namespace. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.DirectionalRestrictions

open MvPolynomial Finset
open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin
theorem polynomial_contract_two_natDegree_le (P : Polynomial ℝ) :
    (Polynomial.contract 2 P).natDegree ≤ P.natDegree := by
  by_cases hP : P = 0
  · subst P
    rw [show (0 : Polynomial ℝ) = Polynomial.C 0 by simp]
    rw [Polynomial.contract_C]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hn (by omega : n ≤ n * 2))

noncomputable def polynomialEvenPart (P : Polynomial ℝ) : Polynomial ℝ :=
  (2 : ℝ)⁻¹ • (P + P.comp (-Polynomial.X))

noncomputable def polynomialOddPart (P : Polynomial ℝ) : Polynomial ℝ :=
  (2 : ℝ)⁻¹ • (P - P.comp (-Polynomial.X))

theorem polynomialEvenPart_eval (P : Polynomial ℝ) (t : ℝ) :
    (polynomialEvenPart P).eval t = (P.eval t + P.eval (-t)) / 2 := by
  dsimp [polynomialEvenPart]
  simp [Polynomial.eval_add, Polynomial.eval_comp]
  ring

theorem polynomialOddPart_eval (P : Polynomial ℝ) (t : ℝ) :
    (polynomialOddPart P).eval t = (P.eval t - P.eval (-t)) / 2 := by
  dsimp [polynomialOddPart]
  simp [Polynomial.eval_sub, Polynomial.eval_comp]
  ring

theorem polynomialEvenPart_add_oddPart (P : Polynomial ℝ) :
    polynomialEvenPart P + polynomialOddPart P = P := by
  dsimp [polynomialEvenPart, polynomialOddPart]
  ext n
  simp [Polynomial.coeff_add, Polynomial.coeff_sub]
  ring

theorem polynomial_coeff_comp_neg_X (P : Polynomial ℝ) (n : ℕ) :
    (P.comp (-Polynomial.X)).coeff n = P.coeff n * (-1 : ℝ) ^ n := by
  rw [show (-Polynomial.X : Polynomial ℝ) = Polynomial.C (-1 : ℝ) * Polynomial.X by simp]
  exact Polynomial.comp_C_mul_X_coeff

theorem polynomialEvenPart_odd_coeff_eq_zero
    (P : Polynomial ℝ) {n : ℕ} (hn : ¬ 2 ∣ n) :
    (polynomialEvenPart P).coeff n = 0 := by
  have hneven : ¬ Even n := by
    rw [even_iff_two_dvd]
    exact hn
  have hnodd : Odd n := Nat.not_even_iff_odd.mp hneven
  have hpow : (-1 : ℝ) ^ n = -1 := by
    exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)).mpr hnodd
  dsimp [polynomialEvenPart]
  rw [Polynomial.coeff_smul, Polynomial.coeff_add, polynomial_coeff_comp_neg_X, hpow]
  simp

theorem polynomialEvenPart_expand_contract (P : Polynomial ℝ) :
    Polynomial.expand ℝ 2 (Polynomial.contract 2 (polynomialEvenPart P)) =
      polynomialEvenPart P := by
  ext n
  rw [Polynomial.coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hn : 2 ∣ n
  · rw [ite_eq_left hn]
    rw [Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
    rw [Nat.div_mul_cancel hn]
  · rw [ite_eq_right hn]
    exact (polynomialEvenPart_odd_coeff_eq_zero P hn).symm

theorem polynomialEvenPart_contract_eval_sq (P : Polynomial ℝ) (t : ℝ) :
    (Polynomial.contract 2 (polynomialEvenPart P)).eval (t ^ 2) =
      (polynomialEvenPart P).eval t := by
  have h := congrArg (fun Q : Polynomial ℝ => Q.eval t) (polynomialEvenPart_expand_contract P)
  simpa using h


theorem polynomialEvenPart_contract_coeff_one (P : Polynomial ℝ) :
    (Polynomial.contract 2 (polynomialEvenPart P)).coeff 1 = P.coeff 2 := by
  rw [Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  dsimp [polynomialEvenPart]
  simp [Polynomial.coeff_add, polynomial_coeff_comp_neg_X]
  ring

theorem polynomial_second_derivative_eval_zero_eq_two_coeff (P : Polynomial ℝ) :
    (Polynomial.derivative (Polynomial.derivative P)).eval 0 = 2 * P.coeff 2 := by
  have h := polynomial_iterate_derivative_eval_zero P 2
  simpa [Nat.factorial] using h

theorem polynomial_contract_even_derivative_eval_zero_eq_coeff_two (P : Polynomial ℝ) :
    (Polynomial.derivative (Polynomial.contract 2 (polynomialEvenPart P))).eval 0 =
      P.coeff 2 := by
  have h := polynomial_iterate_derivative_eval_zero
    (Polynomial.contract 2 (polynomialEvenPart P)) 1
  rw [polynomialEvenPart_contract_coeff_one P] at h
  simpa [Nat.factorial] using h

theorem polynomial_second_derivative_eval_zero_eq_two_contract_even_derivative
    (P : Polynomial ℝ) :
    (Polynomial.derivative (Polynomial.derivative P)).eval 0 =
      2 * (Polynomial.derivative (Polynomial.contract 2 (polynomialEvenPart P))).eval 0 := by
  rw [polynomial_second_derivative_eval_zero_eq_two_coeff]
  rw [polynomial_contract_even_derivative_eval_zero_eq_coeff_two]


theorem polynomialEvenPart_bound_of_symmetric_bound
    {M : ℝ} (_hM : 0 ≤ M) (P : Polynomial ℝ)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS → |P.eval t| ≤ M) :
    ∀ t : ℝ, |t| ≤ schmInteriorS → |(polynomialEvenPart P).eval t| ≤ M := by
  intro t ht
  rw [polynomialEvenPart_eval]
  have htneg : |(-t : ℝ)| ≤ schmInteriorS := by simpa using ht
  have hp := hbound t ht
  have hn := hbound (-t) htneg
  have hsum_abs : |P.eval t + P.eval (-t)| ≤ 2 * M := by
    calc
      |P.eval t + P.eval (-t)| ≤ |P.eval t| + |P.eval (-t)| := abs_add_le _ _
      _ ≤ M + M := add_le_add hp hn
      _ = 2 * M := by ring
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  calc
    |(P.eval t + P.eval (-t)) / 2| = |P.eval t + P.eval (-t)| / 2 := by
      rw [abs_div, abs_of_pos htwo_pos]
    _ ≤ (2 * M) / 2 := div_le_div_of_nonneg_right hsum_abs (by norm_num)
    _ = M := by ring


theorem polynomialOddPart_natDegree_le (P : Polynomial ℝ) :
    (polynomialOddPart P).natDegree ≤ P.natDegree := by
  dsimp [polynomialOddPart]
  calc
    ((2 : ℝ)⁻¹ • (P - P.comp (-Polynomial.X))).natDegree
        ≤ (P - P.comp (-Polynomial.X)).natDegree := Polynomial.natDegree_smul_le _ _
    _ ≤ max P.natDegree (P.comp (-Polynomial.X)).natDegree := Polynomial.natDegree_sub_le _ _
    _ ≤ P.natDegree := by
      apply max_le
      · exact le_rfl
      · calc
          (P.comp (-Polynomial.X)).natDegree
              ≤ P.natDegree * (-Polynomial.X : Polynomial ℝ).natDegree :=
                Polynomial.natDegree_comp_le
          _ ≤ P.natDegree * 1 := by
                have hnegX : (-Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
                  exact Polynomial.natDegree_neg_le_of_le Polynomial.natDegree_X_le
                exact Nat.mul_le_mul_left _ hnegX
          _ = P.natDegree := by rw [Nat.mul_one]

theorem polynomialEvenPart_natDegree_le (P : Polynomial ℝ) :
    (polynomialEvenPart P).natDegree ≤ P.natDegree := by
  dsimp [polynomialEvenPart]
  calc
    ((2 : ℝ)⁻¹ • (P + P.comp (-Polynomial.X))).natDegree
        ≤ (P + P.comp (-Polynomial.X)).natDegree := Polynomial.natDegree_smul_le _ _
    _ ≤ max P.natDegree (P.comp (-Polynomial.X)).natDegree := Polynomial.natDegree_add_le _ _
    _ ≤ P.natDegree := by
      apply max_le
      · exact le_rfl
      · calc
          (P.comp (-Polynomial.X)).natDegree
              ≤ P.natDegree * (-Polynomial.X : Polynomial ℝ).natDegree :=
                Polynomial.natDegree_comp_le
          _ ≤ P.natDegree * 1 := by
                have hnegX : (-Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
                  exact Polynomial.natDegree_neg_le_of_le Polynomial.natDegree_X_le
                exact Nat.mul_le_mul_left _ hnegX
          _ = P.natDegree := by rw [Nat.mul_one]

theorem polynomialEvenPart_contract_natDegree_le (P : Polynomial ℝ) :
    (Polynomial.contract 2 (polynomialEvenPart P)).natDegree ≤ P.natDegree := by
  exact (polynomial_contract_two_natDegree_le (polynomialEvenPart P)).trans
    (polynomialEvenPart_natDegree_le P)

theorem polynomial_second_derivative_zero_bound_schm
    {d : ℕ} {M : ℝ} (hM : 0 ≤ M) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ d)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS → |P.eval t| ≤ M) :
    |(Polynomial.derivative (Polynomial.derivative P)).eval 0| ≤
      64 * (d : ℝ) ^ 2 * M := by
  let E : Polynomial ℝ := polynomialEvenPart P
  let R : Polynomial ℝ := Polynomial.contract 2 E
  let scale : ℝ := schmInteriorS ^ 2 / 2
  let A : Polynomial ℝ := Polynomial.C scale * Polynomial.X + Polynomial.C scale
  let Q : Polynomial ℝ := R.comp A
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    unfold schmInteriorS
    positivity
  have hscale_nonneg : 0 ≤ scale := hscale_pos.le
  have hRdeg : R.natDegree ≤ d := by
    dsimp [R, E]
    exact (polynomialEvenPart_contract_natDegree_le P).trans hdeg
  have hAdeg : A.natDegree ≤ 1 := by
    dsimp [A]
    calc
      (Polynomial.C scale * Polynomial.X + Polynomial.C scale).natDegree
          ≤ max (Polynomial.C scale * Polynomial.X).natDegree (Polynomial.C scale).natDegree :=
            Polynomial.natDegree_add_le _ _
      _ ≤ 1 := by
        apply max_le
        · calc
            (Polynomial.C scale * Polynomial.X : Polynomial ℝ).natDegree
                ≤ (Polynomial.C scale).natDegree + Polynomial.X.natDegree :=
                  Polynomial.natDegree_mul_le
            _ ≤ 0 + 1 := by
              apply Nat.add_le_add
              · simp [Polynomial.natDegree_C]
              · exact Polynomial.natDegree_X_le (R := ℝ)
            _ = 1 := by omega
        · calc
            (Polynomial.C scale : Polynomial ℝ).natDegree ≤ 0 := by
              simp [Polynomial.natDegree_C]
            _ ≤ 1 := by omega
  have hQdeg : Q.natDegree ≤ d := by
    dsimp [Q]
    calc
      (R.comp A).natDegree ≤ R.natDegree * A.natDegree := Polynomial.natDegree_comp_le
      _ ≤ R.natDegree * 1 := Nat.mul_le_mul_left _ hAdeg
      _ = R.natDegree := by omega
      _ ≤ d := hRdeg
  have hEbound := polynomialEvenPart_bound_of_symmetric_bound hM P hbound
  have hQbound : ∀ u : ℝ, -1 ≤ u → u ≤ 1 → |Q.eval u| ≤ M := by
    intro u hu1 hu2
    let s : ℝ := scale * (u + 1)
    have hs0 : 0 ≤ s := by
      dsimp [s]
      exact mul_nonneg hscale_nonneg (by linarith)
    have hsle : s ≤ schmInteriorS ^ 2 := by
      dsimp [s, scale]
      nlinarith
    have hsqrt_le : Real.sqrt s ≤ schmInteriorS := by
      have h := Real.sqrt_le_sqrt hsle
      rwa [Real.sqrt_sq schmInteriorS_pos.le] at h
    have ht : |Real.sqrt s| ≤ schmInteriorS := by
      simpa [abs_of_nonneg (Real.sqrt_nonneg s)] using hsqrt_le
    have heval := polynomialEvenPart_contract_eval_sq P (Real.sqrt s)
    rw [Real.sq_sqrt hs0] at heval
    have hAeval : A.eval u = s := by
      dsimp [A, s]
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
    have hQE : Q.eval u = E.eval (Real.sqrt s) := by
      dsimp [Q]
      rw [Polynomial.eval_comp, hAeval]
      simpa [R, E] using heval
    rw [hQE]
    exact hEbound (Real.sqrt s) ht
  have hmark := univariate_markov_first_derivative_inside_bound Q d hQdeg M hM hQbound
    (-1) (by norm_num) (by norm_num)
  have hderivQ : (Polynomial.derivative Q).eval (-1) =
      scale * (Polynomial.derivative R).eval 0 := by
    dsimp [Q, A]
    rw [Polynomial.derivative_comp]
    simp [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_X,
      Polynomial.derivative_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_X]
  rw [hderivQ, abs_mul, abs_of_pos hscale_pos] at hmark
  have hRderiv : |(Polynomial.derivative R).eval 0| ≤ ((d : ℝ) ^ 2 * M) / scale := by
    rw [le_div_iff₀ hscale_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmark
  rw [polynomial_second_derivative_eval_zero_eq_two_contract_even_derivative P]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |(Polynomial.derivative R).eval 0|
        ≤ 2 * (((d : ℝ) ^ 2 * M) / scale) :=
          mul_le_mul_of_nonneg_left hRderiv (by norm_num)
    _ = 64 * (d : ℝ) ^ 2 * M := by
      dsimp [scale]
      unfold schmInteriorS
      ring

theorem polynomialOddPart_eval_neg (P : Polynomial ℝ) (t : ℝ) :
    (polynomialOddPart P).eval (-t) = - (polynomialOddPart P).eval t := by
  rw [polynomialOddPart_eval, polynomialOddPart_eval]
  ring_nf

theorem polynomialOddPart_outer_bound
    {rho M : ℝ} (P : Polynomial ℝ)
    (hbound : ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) → |P.eval t| ≤ M) :
    ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) →
      |(polynomialOddPart P).eval t| ≤ M := by
  intro t ht
  have hp_pos := hbound t ht
  have hp_neg : |P.eval (-t)| ≤ M := by
    apply hbound (-t)
    constructor
    · simpa [abs_neg] using ht.1
    · simpa [abs_neg] using ht.2
  rw [polynomialOddPart_eval]
  have ht_bounds := abs_le.mp hp_pos
  have hneg_bounds := abs_le.mp hp_neg
  rw [abs_le]
  constructor <;> linarith

theorem polynomialOddPart_sq_evenPart_eval (P : Polynomial ℝ) (t : ℝ) :
    (polynomialEvenPart ((polynomialOddPart P) ^ 2)).eval t =
      ((polynomialOddPart P).eval t) ^ 2 := by
  rw [polynomialEvenPart_eval]
  rw [Polynomial.eval_pow, Polynomial.eval_pow, polynomialOddPart_eval_neg]
  ring

theorem polynomialEvenPart_outer_bound
    {rho M : ℝ} (hrho : 0 < rho) (P : Polynomial ℝ)
    (hbound : ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) → |P.eval t| ≤ M) :
    ∀ s : ℝ, rho ^ 2 ≤ s → s ≤ schmInteriorS ^ 2 →
      |(Polynomial.contract 2 (polynomialEvenPart P)).eval s| ≤ M := by
  intro s hs_low hs_high
  let t : ℝ := Real.sqrt s
  have hs_nonneg : 0 ≤ s := le_trans (sq_nonneg rho) hs_low
  have ht_nonneg : 0 ≤ t := by dsimp [t]; exact Real.sqrt_nonneg s
  have ht_sq : t ^ 2 = s := by
    dsimp [t]
    exact Real.sq_sqrt hs_nonneg
  have ht_abs : |t| = t := abs_of_nonneg ht_nonneg
  have hlow : rho ≤ |t| := by
    rw [ht_abs]
    by_contra hlt
    push Not at hlt
    have hsq_lt : t ^ 2 < rho ^ 2 := by
      nlinarith [hlt, hrho, ht_nonneg]
    nlinarith
  have hhigh : |t| ≤ schmInteriorS := by
    rw [ht_abs]
    by_contra hlt
    push Not at hlt
    have hsq_lt : schmInteriorS ^ 2 < t ^ 2 := by
      nlinarith [hlt, schmInteriorS_pos, ht_nonneg]
    nlinarith
  have hp_pos := hbound t ⟨hlow, hhigh⟩
  have hp_neg : |P.eval (-t)| ≤ M := by
    apply hbound (-t)
    constructor
    · simpa [abs_neg] using hlow
    · simpa [abs_neg] using hhigh
  have heval := polynomialEvenPart_contract_eval_sq P t
  rw [ht_sq] at heval
  rw [heval]
  rw [polynomialEvenPart_eval]
  have ht_bounds := abs_le.mp hp_pos
  have hneg_bounds := abs_le.mp hp_neg
  rw [abs_le]
  constructor <;> linarith

/-- One-sided Chebyshev extrapolation from `[rho^2, schmInteriorS^2]` back
through the short missing interval `[0, rho^2]`.  This is the scalar even-part
extrapolation used in the symmetric-hole proof. -/
theorem square_gap_chebyshev_extrapolate_to_zero
    {rho M : ℝ} {d : ℕ} (hrho : 0 < rho) (hrhoSmall : rho < schmInteriorS / 2)
    (hd : 2 ≤ d) (hdegCond : (d : ℝ) * rho ≤ schmInteriorS)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ d)
    (hbound : ∀ s : ℝ, rho ^ 2 ≤ s → s ≤ schmInteriorS ^ 2 → |P.eval s| ≤ M) :
    ∀ s : ℝ, 0 ≤ s → s ≤ schmInteriorS ^ 2 → |P.eval s| ≤ Real.exp 6 * M := by
  intro u hu0 huS
  have hspos : 0 < schmInteriorS := schmInteriorS_pos
  have hS2pos : 0 < schmInteriorS ^ 2 := sq_pos_of_pos hspos
  have hrho_nonneg : 0 ≤ rho := hrho.le
  have hrho_sq_nonneg : 0 ≤ rho ^ 2 := sq_nonneg rho
  have hrho_le_half : rho ≤ schmInteriorS / 2 := le_of_lt hrhoSmall
  have hrho_le_S : rho ≤ schmInteriorS := by linarith [hrhoSmall]
  have ha_lt_b : rho ^ 2 < schmInteriorS ^ 2 := by
    nlinarith [hrho, hspos, hrho_le_S]
  have hdR_pos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hdR_sq_pos : 0 < (d : ℝ) ^ 2 := sq_pos_of_pos hdR_pos
  have hdist_left : rho ^ 2 - 2 * (schmInteriorS ^ 2 - rho ^ 2) / (d : ℝ) ^ 2 ≤ 0 := by
    have hdeg_sq : (d : ℝ) ^ 2 * rho ^ 2 ≤ schmInteriorS ^ 2 := by
      have hnon : 0 ≤ (d : ℝ) * rho := mul_nonneg (Nat.cast_nonneg d) hrho.le
      have hsq := pow_le_pow_left₀ hnon hdegCond 2
      simpa [mul_pow] using hsq
    have hgap : schmInteriorS ^ 2 ≤ 2 * (schmInteriorS ^ 2 - rho ^ 2) := by
      have hrho_sq_le_quarter : rho ^ 2 ≤ schmInteriorS ^ 2 / 4 := by
        have hsq := pow_le_pow_left₀ hrho_nonneg hrho_le_half 2
        nlinarith [hsq]
      nlinarith
    have hmain : (d : ℝ) ^ 2 * rho ^ 2 ≤ 2 * (schmInteriorS ^ 2 - rho ^ 2) :=
      hdeg_sq.trans hgap
    have hdiv : rho ^ 2 ≤ 2 * (schmInteriorS ^ 2 - rho ^ 2) / (d : ℝ) ^ 2 := by
      rw [le_div_iff₀ hdR_sq_pos]
      nlinarith
    nlinarith
  have hdist : u ∈ Set.Icc (rho ^ 2 - 2 * (schmInteriorS ^ 2 - rho ^ 2) / (d : ℝ) ^ 2)
      (schmInteriorS ^ 2 + 2 * (schmInteriorS ^ 2 - rho ^ 2) / (d : ℝ) ^ 2) := by
    constructor
    · exact hdist_left.trans hu0
    · have hgap_nonneg : 0 ≤ schmInteriorS ^ 2 - rho ^ 2 := by nlinarith [ha_lt_b]
      have hnon : 0 ≤ 2 * (schmInteriorS ^ 2 - rho ^ 2) / (d : ℝ) ^ 2 := by
        exact div_nonneg (mul_nonneg (by norm_num) hgap_nonneg) hdR_sq_pos.le
      nlinarith
  exact affine_chebyshev_extrapolate 2 (Real.exp 6) M (rho ^ 2) (schmInteriorS ^ 2) u
    (by norm_num) (Real.exp_pos 6) (Real.one_le_exp (by norm_num)) ha_lt_b d hd P hdeg
    hbound
    (fun y hy =>
      chebyshevT_abs_le_exp_six_near_one d hd y
        (by norm_num at hy ⊢; exact hy))
    hdist

theorem symmetricHole_evenPart_bound
    {rho M : ℝ} {d : ℕ} (hrho : 0 < rho) (hrhoSmall : rho < schmInteriorS / 2)
    (hd : 2 ≤ d) (hdegCond : (d : ℝ) * rho ≤ schmInteriorS)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ d)
    (hbound : ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) → |P.eval t| ≤ M) :
    ∀ t : ℝ, |t| ≤ schmInteriorS → |(polynomialEvenPart P).eval t| ≤ Real.exp 6 * M := by
  intro t ht
  have ht_sq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have ht_sq_high : t ^ 2 ≤ schmInteriorS ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hQdeg : (Polynomial.contract 2 (polynomialEvenPart P)).natDegree ≤ d :=
    (polynomialEvenPart_contract_natDegree_le P).trans hdeg
  have hQbound := polynomialEvenPart_outer_bound hrho P hbound
  have h := square_gap_chebyshev_extrapolate_to_zero hrho hrhoSmall hd hdegCond
    (Polynomial.contract 2 (polynomialEvenPart P)) hQdeg hQbound (t ^ 2)
    ht_sq_nonneg ht_sq_high
  simpa [polynomialEvenPart_contract_eval_sq P t] using h

theorem symmetricHole_oddPart_sq_bound
    {rho M : ℝ} {d : ℕ} (hrho : 0 < rho) (hrhoSmall : rho < schmInteriorS / 2)
    (hd : 2 ≤ d) (hdegCond : ((2 * d : ℕ) : ℝ) * rho ≤ schmInteriorS)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ d)
    (hbound : ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) → |P.eval t| ≤ M) :
    ∀ t : ℝ, |t| ≤ schmInteriorS → ((polynomialOddPart P).eval t) ^ 2 ≤
      Real.exp 6 * M ^ 2 := by
  intro t ht
  let O : Polynomial ℝ := polynomialOddPart P
  let S : Polynomial ℝ := O ^ 2
  have hD : 2 ≤ 2 * d := by omega
  have hOdeg : O.natDegree ≤ d := (polynomialOddPart_natDegree_le P).trans hdeg
  have hSdeg : S.natDegree ≤ 2 * d := by
    dsimp [S]
    calc
      (O ^ 2).natDegree ≤ 2 * O.natDegree := Polynomial.natDegree_pow_le
      _ ≤ d * 2 := by
        rw [mul_comm]
        exact Nat.mul_le_mul_right 2 hOdeg
      _ = 2 * d := by omega
  have houterS : ∀ u : ℝ, (rho ≤ |u| ∧ |u| ≤ schmInteriorS) → |S.eval u| ≤ M ^ 2 := by
    intro u hu
    have hO := polynomialOddPart_outer_bound P hbound u hu
    dsimp [S, O]
    rw [Polynomial.eval_pow]
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hO 2
  have hQbound := polynomialEvenPart_outer_bound hrho S houterS
  have ht_sq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  have ht_sq_high : t ^ 2 ≤ schmInteriorS ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg t) ht 2
  have hQdeg : (Polynomial.contract 2 (polynomialEvenPart S)).natDegree ≤ 2 * d :=
    (polynomialEvenPart_contract_natDegree_le S).trans hSdeg
  have hsq := square_gap_chebyshev_extrapolate_to_zero hrho hrhoSmall hD hdegCond
    (Polynomial.contract 2 (polynomialEvenPart S)) hQdeg hQbound (t ^ 2)
    ht_sq_nonneg ht_sq_high
  have hsq' : |(polynomialEvenPart S).eval t| ≤ Real.exp 6 * M ^ 2 := by
    simpa [polynomialEvenPart_contract_eval_sq S t] using hsq
  dsimp [S, O] at hsq' ⊢
  rw [polynomialOddPart_sq_evenPart_eval] at hsq'
  simpa [abs_of_nonneg (sq_nonneg ((polynomialOddPart P).eval t))] using hsq'

theorem symmetricHole_oddPart_bound
    {rho M : ℝ} {d : ℕ} (hrho : 0 < rho) (hrhoSmall : rho < schmInteriorS / 2)
    (hd : 2 ≤ d) (hdegCond : ((2 * d : ℕ) : ℝ) * rho ≤ schmInteriorS)
    (hM : 0 ≤ M)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ d)
    (hbound : ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) → |P.eval t| ≤ M) :
    ∀ t : ℝ, |t| ≤ schmInteriorS → |(polynomialOddPart P).eval t| ≤ Real.exp 6 * M := by
  intro t ht
  have hsq := symmetricHole_oddPart_sq_bound hrho hrhoSmall hd hdegCond P hdeg hbound t ht
  have hexp_ge_one : (1 : ℝ) ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
  have hright_nonneg : 0 ≤ Real.exp 6 * M := mul_nonneg (Real.exp_pos 6).le hM
  apply abs_le_of_sq_le_sq
  · calc
      ((polynomialOddPart P).eval t) ^ 2 ≤ Real.exp 6 * M ^ 2 := hsq
      _ ≤ (Real.exp 6 * M) ^ 2 := by
        rw [mul_pow]
        have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
        have hexp_le_sq : Real.exp 6 ≤ (Real.exp 6) ^ 2 := by
          nlinarith [hexp_ge_one, Real.exp_pos 6]
        exact mul_le_mul_of_nonneg_right hexp_le_sq hM2
  · exact hright_nonneg

lemma polynomial_weighted_sum_natDegree_le_weightedJet {N k : ℕ}
    (P : Fin N → Polynomial ℝ) (a : Fin N → ℝ)
    (hdeg : ∀ i, (P i).natDegree ≤ k) :
    (∑ i : Fin N, Polynomial.C (a i) * P i).natDegree ≤ k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  calc
    (Polynomial.C (a i) * P i).natDegree ≤
        (Polynomial.C (a i)).natDegree + (P i).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 0 + k := by
      rw [Polynomial.natDegree_C]
      exact Nat.add_le_add_left (hdeg i) 0
    _ = k := by omega

lemma polynomial_weighted_sum_eval_weightedJet {N : ℕ}
    (P : Fin N → Polynomial ℝ) (a : Fin N → ℝ) (t : ℝ) :
    (∑ i : Fin N, Polynomial.C (a i) * P i).eval t =
      vecDot a (fun i : Fin N => (P i).eval t) := by
  unfold vecDot
  simp_rw [← Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem symmetricHole_scalar_bound
    {rho M : ℝ} {d : ℕ} (hrho : 0 < rho) (hrhoSmall : rho < schmInteriorS / 2)
    (hd : 2 ≤ d) (hdegCond : ((2 * d : ℕ) : ℝ) * rho ≤ schmInteriorS)
    (hM : 0 ≤ M)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ d)
    (hbound : ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) → |P.eval t| ≤ M) :
    ∀ t : ℝ, |t| ≤ schmInteriorS → |P.eval t| ≤ 2 * Real.exp 6 * M := by
  intro t ht
  have hdegCond1 : (d : ℝ) * rho ≤ schmInteriorS := by
    have hd_nonneg : 0 ≤ (d : ℝ) * rho := mul_nonneg (Nat.cast_nonneg d) hrho.le
    have htwo : (d : ℝ) * rho ≤ ((2 * d : ℕ) : ℝ) * rho := by
      have hdle : (d : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast (by omega : d ≤ 2 * d)
      exact mul_le_mul_of_nonneg_right hdle hrho.le
    exact htwo.trans hdegCond
  have hE := symmetricHole_evenPart_bound hrho hrhoSmall hd hdegCond1 P hdeg hbound t ht
  have hO := symmetricHole_oddPart_bound hrho hrhoSmall hd hdegCond hM P hdeg hbound t ht
  have hparts := congrArg (fun Q : Polynomial ℝ => Q.eval t) (polynomialEvenPart_add_oddPart P)
  have hsum : P.eval t = (polynomialEvenPart P).eval t + (polynomialOddPart P).eval t := by
    simpa [Polynomial.eval_add] using hparts.symm
  rw [hsum]
  have hE_bounds := abs_le.mp hE
  have hO_bounds := abs_le.mp hO
  rw [abs_le]
  constructor <;> linarith

theorem symmetricHole_vector_bound
    {N d : ℕ} {rho M : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < schmInteriorS / 2)
    (hd : 2 ≤ d) (hdegCond : ((2 * d : ℕ) : ℝ) * rho ≤ schmInteriorS)
    (hM : 0 ≤ M)
    (P : Fin N → Polynomial ℝ) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (hbound : ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ 2 * Real.exp 6 * M := by
  intro t ht
  let V : Fin N → ℝ := fun i => (P i).eval t
  by_cases hV0 : interiorVecNorm V = 0
  · have hright : 0 ≤ 2 * Real.exp 6 * M := by positivity
    simpa [V, hV0] using hright
  · let u : Fin N → ℝ := fun i => V i / interiorVecNorm V
    let R : Polynomial ℝ := ∑ i : Fin N, Polynomial.C (u i) * P i
    have hRdeg : R.natDegree ≤ d := by
      dsimp [R]
      exact polynomial_weighted_sum_natDegree_le_weightedJet P u hdeg
    have hRbound : ∀ x : ℝ, (rho ≤ |x| ∧ |x| ≤ schmInteriorS) → |R.eval x| ≤ M := by
      intro x hx
      dsimp [R]
      rw [polynomial_weighted_sum_eval_weightedJet]
      have hunit := abs_vecDot_unit_le (v := V)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hV0)
        (fun i : Fin N => (P i).eval x)
      exact hunit.trans (hbound x hx)
    have hscalar := symmetricHole_scalar_bound hrho hrhoSmall hd hdegCond hM R hRdeg hRbound t ht
    have hR_eval : R.eval t = interiorVecNorm V := by
      dsimp [R]
      rw [polynomial_weighted_sum_eval_weightedJet]
      change vecDot (fun i : Fin N => V i / interiorVecNorm V) V = interiorVecNorm V
      exact vecDot_unit_self
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hV0)
    rw [hR_eval] at hscalar
    simpa [V, abs_of_nonneg (interiorVecNorm_nonneg V)] using hscalar

lemma polynomial_second_derivative_eval_sum_weighted {N : ℕ}
    (P : Fin N → Polynomial ℝ) (a : Fin N → ℝ) :
    (Polynomial.derivative (Polynomial.derivative
        (∑ i : Fin N, Polynomial.C (a i) * P i))).eval 0 =
      ∑ i : Fin N, a i *
        (Polynomial.derivative (Polynomial.derivative (P i))).eval 0 := by
  rw [Polynomial.derivative_sum, Polynomial.derivative_sum]
  simp_rw [← Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Polynomial.derivative_mul]

theorem interior_bernstein_vector_second_derivative_schm_explicit
    {N d : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    interiorVecNorm
        (fun i : Fin N => (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) ≤
      64 * (d : ℝ) ^ 2 * M := by
  let D : Fin N → ℝ := fun i =>
    (Polynomial.derivative (Polynomial.derivative (P i))).eval 0
  by_cases hD0 : interiorVecNorm D = 0
  · have hright : 0 ≤ 64 * (d : ℝ) ^ 2 * M := by positivity
    simpa [D, hD0] using hright
  · let u : Fin N → ℝ := fun i => D i / interiorVecNorm D
    let R : Polynomial ℝ := ∑ i : Fin N, Polynomial.C (u i) * P i
    have hRdeg : R.natDegree ≤ d := by
      dsimp [R]
      exact polynomial_weighted_sum_natDegree_le_weightedJet P u hdeg
    have hRbound : ∀ t : ℝ, |t| ≤ schmInteriorS → |R.eval t| ≤ M := by
      intro t ht
      dsimp [R]
      rw [polynomial_weighted_sum_eval_weightedJet]
      have hunit := abs_vecDot_unit_le (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
        (fun i : Fin N => (P i).eval t)
      exact hunit.trans (hbound t ht)
    have hscalar := polynomial_second_derivative_zero_bound_schm hM R hRdeg hRbound
    have hderiv : (Polynomial.derivative (Polynomial.derivative R)).eval 0 =
        interiorVecNorm D := by
      dsimp [R]
      rw [polynomial_second_derivative_eval_sum_weighted]
      change vecDot (fun i : Fin N => D i / interiorVecNorm D) D = interiorVecNorm D
      exact vecDot_unit_self (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
    calc
      interiorVecNorm D = |(Polynomial.derivative (Polynomial.derivative R)).eval 0| := by
        rw [hderiv]
        exact (abs_of_nonneg (interiorVecNorm_nonneg D)).symm
      _ ≤ 64 * (d : ℝ) ^ 2 * M := hscalar


/-- Third-derivative Bernstein bound at the center of the small interval. -/
theorem polynomial_third_derivative_zero_bound_schm
    {d : ℕ} {M : ℝ} (hM : 0 ≤ M) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ d)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS → |P.eval t| ≤ M) :
    |(Polynomial.derivative
        (Polynomial.derivative (Polynomial.derivative P))).eval 0| ≤
      4096 * (d : ℝ) ^ 3 * M := by
  let D2 : Polynomial ℝ := Polynomial.derivative (Polynomial.derivative P)
  have hD2deg : D2.natDegree ≤ d := by
    exact (Polynomial.natDegree_derivative_le _).trans
      ((Nat.sub_le _ _).trans
        ((Polynomial.natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hdeg)))
  have hD2bound : ∀ x : ℝ, |x| ≤ schmInteriorS / 2 →
      |D2.eval x| ≤ 256 * (d : ℝ) ^ 2 * M := by
    intro x hx
    let A : Polynomial ℝ := Polynomial.C x + Polynomial.C (1 / 2 : ℝ) * Polynomial.X
    let R : Polynomial ℝ := P.comp A
    have hAdeg : A.natDegree ≤ 1 := by
      dsimp [A]
      exact (Polynomial.natDegree_add_le _ _).trans (by
        apply max_le
        · simp [Polynomial.natDegree_C]
        · exact (Polynomial.natDegree_mul_le.trans (by
            simp [Polynomial.natDegree_C])))
    have hRdeg : R.natDegree ≤ d := by
      dsimp [R]
      exact Polynomial.natDegree_comp_le.trans
        ((Nat.mul_le_mul_left _ hAdeg).trans (by simpa using hdeg))
    have hRbound : ∀ u : ℝ, |u| ≤ schmInteriorS → |R.eval u| ≤ M := by
      intro u hu
      rw [show R.eval u = P.eval (x + (1 / 2 : ℝ) * u) by
        simp [R, A, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul]]
      apply hbound
      calc
        |x + (1 / 2 : ℝ) * u| ≤ |x| + |(1 / 2 : ℝ) * u| := abs_add_le _ _
        _ ≤ schmInteriorS / 2 + schmInteriorS / 2 := by
          gcongr
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          nlinarith
        _ = schmInteriorS := by ring
    have hs := polynomial_second_derivative_zero_bound_schm hM R hRdeg hRbound
    have hderiv :
        (Polynomial.derivative (Polynomial.derivative R)).eval 0 =
          (1 / 4 : ℝ) * D2.eval x := by
      dsimp [R, A, D2]
      simp [Polynomial.derivative_comp, Polynomial.derivative_add,
        Polynomial.derivative_mul, Polynomial.eval_mul, Polynomial.eval_add]
      ring
    rw [hderiv, abs_mul] at hs
    norm_num at hs ⊢
    nlinarith
  let S : Polynomial ℝ := D2.comp (Polynomial.C (1 / 2 : ℝ) * Polynomial.X)
  have hSdeg : S.natDegree ≤ d := by
    dsimp [S]
    calc
      (D2.comp (Polynomial.C (1 / 2 : ℝ) * Polynomial.X)).natDegree ≤
          D2.natDegree * (Polynomial.C (1 / 2 : ℝ) * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ D2.natDegree * 1 := Nat.mul_le_mul_left _
        (Polynomial.natDegree_mul_le.trans (by simp [Polynomial.natDegree_C]))
      _ = D2.natDegree := by omega
      _ ≤ d := hD2deg
  have hSbound : ∀ u : ℝ, -schmInteriorS ≤ u → u ≤ schmInteriorS →
      |S.eval u| ≤ 256 * (d : ℝ) ^ 2 * M := by
    intro u hu1 hu2
    rw [show S.eval u = D2.eval ((1 / 2 : ℝ) * u) by
      simp [S, Polynomial.eval_comp, Polynomial.eval_mul]]
    apply hD2bound
    rw [abs_mul]
    have hu : |u| ≤ schmInteriorS := abs_le.mpr ⟨hu1, hu2⟩
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    nlinarith
  have hSM : 0 ≤ 256 * (d : ℝ) ^ 2 * M := by positivity
  let V : Fin 1 → Polynomial ℝ := fun _ => S
  have hVdeg : ∀ i, (V i).natDegree ≤ d := by intro i; exact hSdeg
  have hVbound : ∀ u : ℝ, |u| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin 1 => (V i).eval u) ≤ 256 * (d : ℝ) ^ 2 * M := by
    intro u hu
    have hs := hSbound u (abs_le.mp hu).1 (abs_le.mp hu).2
    simpa [V, interiorVecNorm, interiorVecSqNorm, Real.sqrt_sq_eq_abs] using hs
  have hb := interior_bernstein_vector_first_derivative_schm V hSM hVdeg hVbound
  have hbscalar : |(Polynomial.derivative S).eval 0| ≤
      8 * (d : ℝ) * (256 * (d : ℝ) ^ 2 * M) := by
    simpa [V, interiorVecNorm, interiorVecSqNorm, Real.sqrt_sq_eq_abs] using hb
  have hderivS : (Polynomial.derivative S).eval 0 =
      (1 / 2 : ℝ) * (Polynomial.derivative D2).eval 0 := by
    dsimp [S]
    simp [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.eval_mul]
  rw [hderivS, abs_mul] at hbscalar
  norm_num at hbscalar ⊢
  nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) hM]


lemma polynomial_third_derivative_eval_sum_weighted {N : ℕ}
    (P : Fin N → Polynomial ℝ) (a : Fin N → ℝ) :
    (Polynomial.derivative (Polynomial.derivative (Polynomial.derivative
        (∑ i : Fin N, Polynomial.C (a i) * P i)))).eval 0 =
      ∑ i : Fin N, a i *
        (Polynomial.derivative
          (Polynomial.derivative (Polynomial.derivative (P i)))).eval 0 := by
  rw [Polynomial.derivative_sum, Polynomial.derivative_sum, Polynomial.derivative_sum]
  simp_rw [← Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Polynomial.derivative_mul]

/-- Uniform vector-valued third-derivative Bernstein bound at the center. -/
theorem interior_bernstein_vector_third_derivative_schm_explicit
    {N d : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ d)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    interiorVecNorm
        (fun i : Fin N =>
          (Polynomial.derivative
            (Polynomial.derivative (Polynomial.derivative (P i)))).eval 0) ≤
      4096 * (d : ℝ) ^ 3 * M := by
  let D : Fin N → ℝ := fun i =>
    (Polynomial.derivative
      (Polynomial.derivative (Polynomial.derivative (P i)))).eval 0
  by_cases hD0 : interiorVecNorm D = 0
  · have hright : 0 ≤ 4096 * (d : ℝ) ^ 3 * M := by positivity
    simpa [D, hD0] using hright
  · let u : Fin N → ℝ := fun i => D i / interiorVecNorm D
    let R : Polynomial ℝ := ∑ i : Fin N, Polynomial.C (u i) * P i
    have hRdeg : R.natDegree ≤ d := by
      dsimp [R]
      exact polynomial_weighted_sum_natDegree_le_weightedJet P u hdeg
    have hRbound : ∀ t : ℝ, |t| ≤ schmInteriorS → |R.eval t| ≤ M := by
      intro t ht
      dsimp [R]
      rw [polynomial_weighted_sum_eval_weightedJet]
      have hunit := abs_vecDot_unit_le (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
        (fun i : Fin N => (P i).eval t)
      exact hunit.trans (hbound t ht)
    have hscalar := polynomial_third_derivative_zero_bound_schm hM R hRdeg hRbound
    have hderiv :
        (Polynomial.derivative
          (Polynomial.derivative (Polynomial.derivative R))).eval 0 =
        interiorVecNorm D := by
      dsimp [R]
      rw [polynomial_third_derivative_eval_sum_weighted]
      change vecDot (fun i : Fin N => D i / interiorVecNorm D) D = interiorVecNorm D
      exact vecDot_unit_self (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
    calc
      interiorVecNorm D =
          |(Polynomial.derivative
            (Polynomial.derivative (Polynomial.derivative R))).eval 0| := by
        rw [hderiv]
        exact (abs_of_nonneg (interiorVecNorm_nonneg D)).symm
      _ ≤ 4096 * (d : ℝ) ^ 3 * M := hscalar


end Motzkin

end OptimalConvergenceRates

end
