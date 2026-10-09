/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/WeightedJet/SymmetricHole.lean

  Symmetric-hole estimates controlling higher weighted-jet coefficients.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.WeightedJet.CoefficientBounds

open MvPolynomial Finset
open scoped Pointwise

noncomputable section

namespace OptimalConvergenceRates

def weightedJetHoleRadius (epsilon : ℝ) (k : ℕ) : ℝ :=
  4 * (epsilon ^ ((1 : ℝ) / 4) + (k : ℝ) * Real.sqrt epsilon)

theorem rpow_quarter_sq_eq_sqrt {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    (epsilon ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt epsilon := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul heps]
  norm_num

theorem weightedJetHole_sqrt_le_sq
    {epsilon : ℝ} {k : ℕ} {t : ℝ}
    (heps : 0 ≤ epsilon)
    (houter : weightedJetHoleRadius epsilon k ≤ |t|) :
    Real.sqrt epsilon ≤ t ^ 2 := by
  let q : ℝ := epsilon ^ ((1 : ℝ) / 4)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg heps _
  have hs0 : 0 ≤ Real.sqrt epsilon := Real.sqrt_nonneg _
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hq_le_hole : q ≤ weightedJetHoleRadius epsilon k := by
    dsimp [weightedJetHoleRadius, q]
    nlinarith [mul_nonneg hk0 hs0]
  have hq_le_abs : q ≤ |t| := hq_le_hole.trans houter
  have hsq := pow_le_pow_left₀ hq0 hq_le_abs 2
  rw [rpow_quarter_sq_eq_sqrt heps] at hsq
  simpa [sq_abs] using hsq

theorem weightedJetHole_linear_le_sq
    {epsilon : ℝ} {k : ℕ} {t : ℝ}
    (heps : 0 ≤ epsilon)
    (houter : weightedJetHoleRadius epsilon k ≤ |t|) :
    (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2 := by
  let a : ℝ := (k : ℝ) * Real.sqrt epsilon
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hq0 : 0 ≤ epsilon ^ ((1 : ℝ) / 4) := Real.rpow_nonneg heps _
  have ha_le_hole : a ≤ weightedJetHoleRadius epsilon k := by
    dsimp [weightedJetHoleRadius, a]
    nlinarith
  have ha_le_abs : a ≤ |t| := ha_le_hole.trans houter
  calc
    (k : ℝ) * Real.sqrt epsilon * |t| = a * |t| := by ring
    _ ≤ |t| * |t| := by
      exact mul_le_mul_of_nonneg_right ha_le_abs (abs_nonneg t)
    _ = t ^ 2 := by rw [← sq_abs]; ring

/-- Version of the unit-direction homogeneous-jet bound where the outer interval
starts beyond the explicit hole radius. -/
theorem weightedJet_higher_eval_bound_from_hole_radius_quarter
    {N k ell : ℕ} {epsilon A rho : ℝ}
    (heps : 0 < epsilon)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (hrho : 0 < rho)
    (hrhoSmall : rho < schmInteriorS / 2)
    (hradius : weightedJetHoleRadius epsilon k ≤ rho)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1) :
    ∃ C : ℝ, 0 < C ∧
      interiorVecNorm
          (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 (ell + 2) Q i)) ≤
        C * (k : ℝ) ^ ell *
          (2 * A + jetErrorConst * A + weightedJetQuarterConst * A) := by
  apply weightedJet_higher_eval_bound_from_outer_quarter heps hk hA hrho hrhoSmall
    Q hdeg hlocal hzeroLines hv
  · intro t ht
    exact weightedJetHole_sqrt_le_sq heps.le (hradius.trans ht.1)
  · intro t ht
    exact weightedJetHole_linear_le_sq heps.le (hradius.trans ht.1)


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
  · rw [if_pos hn]
    rw [Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
    rw [Nat.div_mul_cancel hn]
  · rw [if_neg hn]
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
            (Polynomial.C scale : Polynomial ℝ).natDegree ≤ 0 := by simp [Polynomial.natDegree_C]
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
    ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) → |(polynomialOddPart P).eval t| ≤ M := by
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
    push_neg at hlt
    have hsq_lt : t ^ 2 < rho ^ 2 := by
      nlinarith [hlt, hrho, ht_nonneg]
    nlinarith
  have hhigh : |t| ≤ schmInteriorS := by
    rw [ht_abs]
    by_contra hlt
    push_neg at hlt
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

theorem weightedJet_tail_full_bound_sixty_four
    {N k : ℕ} {epsilon A rho : ℝ}
    (heps : 0 < epsilon)
    (hk2 : 2 ≤ k)
    (hA : 1 ≤ A)
    (hrho : 0 < rho)
    (hrhoSmall : rho < schmInteriorS / 2)
    (hdegCond : ((2 * k : ℕ) : ℝ) * rho ≤ schmInteriorS)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1)
    (hsqrtOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      Real.sqrt epsilon ≤ t ^ 2)
    (hlinearOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2) :
    ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            (polynomialTailDivX2
              (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v)).eval t) ≤
        2 * Real.exp 6 * (2 * A + jetErrorConst * A + 64 * A) := by
  let P : Fin N → Polynomial ℝ := fun i =>
    polynomialTailDivX2 (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v)
  let M : ℝ := 2 * A + jetErrorConst * A + 64 * A
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hM : 0 ≤ M := by
    dsimp [M]
    nlinarith [jetErrorConst_pos.le, hA0]
  have hdegP : ∀ i, (P i).natDegree ≤ k := by
    intro i
    dsimp [P]
    exact (polynomialTailDivX2_natDegree_le _).trans
      ((univariateRestriction_natDegree_le (Q i) (0 : Fin 4 → ℝ) v).trans (hdeg i))
  have houter : ∀ t : ℝ, (rho ≤ |t| ∧ |t| ≤ schmInteriorS) →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M := by
    intro t ht
    have ht0 : t ≠ 0 := by
      intro htz
      subst t
      simp at ht
      linarith
    dsimp [P, M]
    exact weightedJet_tail_outer_bound_sixty_four heps (le_trans (by norm_num : 1 ≤ 2) hk2)
      hA Q hdeg hlocal hzeroLines hv ht.2 ht0 (hsqrtOuter t ht) (hlinearOuter t ht)
  simpa [P, M] using
    symmetricHole_vector_bound hrho hrhoSmall hk2 hdegCond hM P hdegP houter


theorem weightedJet_higher_eval_bound_two_sixty_four
    {N k : ℕ} {epsilon A rho : ℝ}
    (heps : 0 < epsilon)
    (hk2 : 2 ≤ k)
    (hA : 1 ≤ A)
    (hrho : 0 < rho)
    (hrhoSmall : rho < schmInteriorS / 2)
    (hdegCond : ((2 * k : ℕ) : ℝ) * rho ≤ schmInteriorS)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1)
    (hsqrtOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      Real.sqrt epsilon ≤ t ^ 2)
    (hlinearOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2) :
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 2 Q i)) ≤
      2 * Real.exp 6 * (2 * A + jetErrorConst * A + 64 * A) := by
  have htail := weightedJet_tail_full_bound_sixty_four heps hk2 hA hrho hrhoSmall
    hdegCond Q hdeg hlocal hzeroLines hv hsqrtOuter hlinearOuter
  have hzero : |(0 : ℝ)| ≤ schmInteriorS := by
    simpa using schmInteriorS_pos.le
  have hderiv : interiorVecNorm
        (fun i : Fin N =>
          ((Polynomial.derivative^[0])
            (polynomialTailDivX2
              (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v))).eval 0) ≤
      2 * Real.exp 6 * (2 * A + jetErrorConst * A + 64 * A) := by
    simpa using htail 0 hzero
  simpa using homogeneousPart_eval_norm_le_of_tail_derivative_norm_le
    (ell := 0) Q v hderiv

theorem weightedJet_higher_eval_bound_three_sixty_four
    {N k : ℕ} {epsilon A rho : ℝ}
    (heps : 0 < epsilon)
    (hk2 : 2 ≤ k)
    (hA : 1 ≤ A)
    (hrho : 0 < rho)
    (hrhoSmall : rho < schmInteriorS / 2)
    (hdegCond : ((2 * k : ℕ) : ℝ) * rho ≤ schmInteriorS)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1)
    (hsqrtOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      Real.sqrt epsilon ≤ t ^ 2)
    (hlinearOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2) :
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 3 Q i)) ≤
      8 * (k : ℝ) *
        (2 * Real.exp 6 * (2 * A + jetErrorConst * A + 64 * A)) := by
  let P : Fin N → Polynomial ℝ := fun i =>
    polynomialTailDivX2 (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v)
  let M : ℝ := 2 * Real.exp 6 * (2 * A + jetErrorConst * A + 64 * A)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hM : 0 ≤ M := by
    dsimp [M]
    have hinner : 0 ≤ 2 * A + jetErrorConst * A + 64 * A := by
      nlinarith [jetErrorConst_pos.le, hA0]
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos 6).le) hinner
  have hdegP : ∀ i, (P i).natDegree ≤ k := by
    intro i
    dsimp [P]
    exact (polynomialTailDivX2_natDegree_le _).trans
      ((univariateRestriction_natDegree_le (Q i) (0 : Fin 4 → ℝ) v).trans (hdeg i))
  have htail := weightedJet_tail_full_bound_sixty_four heps hk2 hA hrho hrhoSmall
    hdegCond Q hdeg hlocal hzeroLines hv hsqrtOuter hlinearOuter
  have hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M := by
    intro t ht
    dsimp [P, M]
    exact htail t ht
  have hbern := interior_bernstein_vector_first_derivative_schm P hM hdegP hbound
  have hderiv : interiorVecNorm
        (fun i : Fin N =>
          ((Polynomial.derivative^[1])
            (polynomialTailDivX2
              (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v))).eval 0) ≤
      8 * (k : ℝ) * M := by
    simpa [P] using hbern
  have hhom := homogeneousPart_eval_norm_le_of_tail_derivative_norm_le
    (ell := 1) Q v hderiv
  simpa [M, Nat.succ_eq_add_one] using hhom


theorem weightedJet_higher_eval_bound_four_sixty_four
    {N k : ℕ} {epsilon A rho : ℝ}
    (heps : 0 < epsilon)
    (hk2 : 2 ≤ k)
    (hA : 1 ≤ A)
    (hrho : 0 < rho)
    (hrhoSmall : rho < schmInteriorS / 2)
    (hdegCond : ((2 * k : ℕ) : ℝ) * rho ≤ schmInteriorS)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon)
    {v : Fin 4 → ℝ} (hv : localSqNorm v = 1)
    (hsqrtOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      Real.sqrt epsilon ≤ t ^ 2)
    (hlinearOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
      (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2) :
    interiorVecNorm
        (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 4 Q i)) ≤
      64 * (k : ℝ) ^ 2 *
        (2 * Real.exp 6 * (2 * A + jetErrorConst * A + 64 * A)) := by
  let P : Fin N → Polynomial ℝ := fun i =>
    polynomialTailDivX2 (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v)
  let M : ℝ := 2 * Real.exp 6 * (2 * A + jetErrorConst * A + 64 * A)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hM : 0 ≤ M := by
    dsimp [M]
    have hinner : 0 ≤ 2 * A + jetErrorConst * A + 64 * A := by
      nlinarith [jetErrorConst_pos.le, hA0]
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos 6).le) hinner
  have hdegP : ∀ i, (P i).natDegree ≤ k := by
    intro i
    dsimp [P]
    exact (polynomialTailDivX2_natDegree_le _).trans
      ((univariateRestriction_natDegree_le (Q i) (0 : Fin 4 → ℝ) v).trans (hdeg i))
  have htail := weightedJet_tail_full_bound_sixty_four heps hk2 hA hrho hrhoSmall
    hdegCond Q hdeg hlocal hzeroLines hv hsqrtOuter hlinearOuter
  have hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M := by
    intro t ht
    dsimp [P, M]
    exact htail t ht
  have hsecond := interior_bernstein_vector_second_derivative_schm_explicit P hM hdegP hbound
  have hderiv : interiorVecNorm
        (fun i : Fin N =>
          ((Polynomial.derivative^[2])
            (polynomialTailDivX2
              (univariateRestriction (Q i) (0 : Fin 4 → ℝ) v))).eval 0) ≤
      64 * (k : ℝ) ^ 2 * M := by
    simpa [P] using hsecond
  have hhom := homogeneousPart_eval_norm_le_of_tail_derivative_norm_le
    (ell := 2) Q v hderiv
  simpa [M, Nat.succ_eq_add_one, Nat.reduceAdd] using hhom



theorem weightedJet_hole_parameters_quarter
    {k : ℕ} {epsilon : ℝ}
    (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0)
    (hkSmall : (k : ℝ) ≤ weightedJetGamma0 * epsilon ^ (-(1 : ℝ) / 4))
    (_hk2 : 2 ≤ k) :
    0 < weightedJetHoleRadius epsilon k ∧
    weightedJetHoleRadius epsilon k < schmInteriorS / 2 ∧
    ((2 * k : ℕ) : ℝ) * weightedJetHoleRadius epsilon k ≤ schmInteriorS := by
  let q : ℝ := epsilon ^ ((1 : ℝ) / 4)
  let g : ℝ := weightedJetGamma0
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos heps _
  have hq0 : 0 ≤ q := hqpos.le
  have hsqrt_eq : Real.sqrt epsilon = q ^ 2 := by
    dsimp [q]
    rw [rpow_quarter_sq_eq_sqrt heps.le]
  let c : ℝ := schmInteriorLowerBoundConst / 4
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg schmInteriorLowerBoundConst_pos.le (by norm_num)
  have hc0_const : 0 ≤ schmInteriorLowerBoundConst / 4 := by
    exact div_nonneg schmInteriorLowerBoundConst_pos.le (by norm_num)
  have heps0_quarter_const :
      schmInteriorEpsilon0 ^ ((1 : ℝ) / 4) = schmInteriorLowerBoundConst / 4 := by
    unfold schmInteriorEpsilon0
    rw [← Real.rpow_natCast (schmInteriorLowerBoundConst / 4) 4]
    rw [← Real.rpow_mul hc0_const]
    norm_num
  have heps0_quarter : schmInteriorEpsilon0 ^ ((1 : ℝ) / 4) = c := by
    simpa [c] using heps0_quarter_const
  have hq_le_c : q ≤ c := by
    have h := Real.rpow_le_rpow heps.le heps0 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
    calc
      q ≤ schmInteriorEpsilon0 ^ ((1 : ℝ) / 4) := by simpa [q] using h
      _ = c := heps0_quarter
  have hc_le_g_quarter : c ≤ g / 4 := by
    dsimp [c, g]
    exact div_le_div_of_nonneg_right schmInteriorLowerBoundConst_le_gamma (by norm_num)
  have hq_le_g_quarter : q ≤ g / 4 := hq_le_c.trans hc_le_g_quarter
  have hginv_cancel : epsilon ^ (-(1 : ℝ) / 4) * q = 1 := by
    dsimp [q]
    rw [← Real.rpow_add heps]
    norm_num
  have hkq_le_g : (k : ℝ) * q ≤ g := by
    have hmul := mul_le_mul_of_nonneg_right hkSmall hq0
    dsimp [g] at hmul ⊢
    rw [mul_assoc, hginv_cancel, mul_one] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hkq0 : 0 ≤ (k : ℝ) * q := mul_nonneg (Nat.cast_nonneg k) hq0
  have hg_pos : 0 < g := by
    dsimp [g]
    exact weightedJetGamma0_pos
  have hg0 : 0 ≤ g := hg_pos.le
  have hq_le_g : q ≤ g := by
    have hg_nonneg : 0 ≤ g := hg0
    nlinarith [hq_le_g_quarter]
  have hhole_pos : 0 < weightedJetHoleRadius epsilon k := by
    dsimp [weightedJetHoleRadius]
    change 0 < 4 * (q + (k : ℝ) * Real.sqrt epsilon)
    rw [hsqrt_eq]
    have hterm_nonneg : 0 ≤ (k : ℝ) * Real.sqrt epsilon := by positivity
    nlinarith [hqpos]
  have hhole_le : weightedJetHoleRadius epsilon k ≤ 4 * (q + g * q) := by
    dsimp [weightedJetHoleRadius]
    rw [hsqrt_eq]
    have hkgq : (k : ℝ) * q ^ 2 ≤ g * q := by
      calc
        (k : ℝ) * q ^ 2 = ((k : ℝ) * q) * q := by ring
        _ ≤ g * q := mul_le_mul_of_nonneg_right hkq_le_g hq0
    nlinarith
  have hhole_small : weightedJetHoleRadius epsilon k < schmInteriorS / 2 := by
    have hupper : 4 * (q + g * q) ≤ g * (1 + g) := by
      have hgq : g * q ≤ g * (g / 4) := mul_le_mul_of_nonneg_left hq_le_g_quarter hg0
      nlinarith [hq_le_g_quarter, hgq]
    have hconst : g * (1 + g) < schmInteriorS / 2 := by
      dsimp [g]
      unfold weightedJetGamma0 schmInteriorS
      norm_num
    exact lt_of_le_of_lt (hhole_le.trans hupper) hconst
  have hprod_le : ((2 * k : ℕ) : ℝ) * weightedJetHoleRadius epsilon k ≤
      8 * ((k : ℝ) * q + ((k : ℝ) * q) ^ 2) := by
    have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by norm_num
    dsimp [weightedJetHoleRadius]
    rw [hsqrt_eq]
    calc
      ((2 * k : ℕ) : ℝ) * (4 * (q + (k : ℝ) * q ^ 2))
          = 8 * ((k : ℝ) * q + ((k : ℝ) * q) ^ 2) := by
            rw [hcast]
            ring
      _ ≤ 8 * ((k : ℝ) * q + ((k : ℝ) * q) ^ 2) := le_rfl
  have hprod_small : 8 * ((k : ℝ) * q + ((k : ℝ) * q) ^ 2) ≤ schmInteriorS := by
    have hsq_le : ((k : ℝ) * q) ^ 2 ≤ g ^ 2 := by
      exact pow_le_pow_left₀ hkq0 hkq_le_g 2
    have hconst : 8 * (g + g ^ 2) ≤ schmInteriorS := by
      dsimp [g]
      unfold weightedJetGamma0 schmInteriorS
      norm_num
    nlinarith
  exact ⟨hhole_pos, hhole_small, hprod_le.trans hprod_small⟩


theorem homogeneousPart4_eq_zero_of_totalDegree_le_one
    {m : ℕ} (hm : 2 ≤ m) {p : MvPolynomial (Fin 4) ℝ}
    (hp : p.totalDegree ≤ 1) :
    homogeneousPart4 m p = 0 := by
  ext α
  rw [coeff_homogeneousPart4]
  by_cases hα : α.sum (fun _ e => e) = m
  · simp only [hα, ↓reduceIte]
    exact coeff_eq_zero_of_totalDegree_lt_n4 hp (by omega)
  · simp only [hα, ↓reduceIte, coeff_zero]

theorem symmetricHole_weightedJet_ordered_coeff_bounds_degree_one
    {N k : ℕ} {A : ℝ}
    (hk : 1 ≤ k) (hnk2 : ¬ 2 ≤ k)
    (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k) :
    vecCoeffNorm4 (homogeneousPartVec4 2 Q) ≤ weightedJetQuarterConst * A ∧
    (∀ ijk : Fin 4 × Fin 4 × Fin 4,
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.coeff
          (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
            Finsupp.single ijk.2.2 1)
          (homogeneousPartVec4 3 Q i)) ≤ weightedJetQuarterConst * A * (k : ℝ) / 64) ∧
    (∀ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.coeff
          (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
            Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1)
          (homogeneousPartVec4 4 Q i)) ≤ weightedJetQuarterConst * A * (k : ℝ) ^ 2 / 256) := by
  have hk_le_one : k ≤ 1 := by omega
  have hdeg1 : ∀ i, (Q i).totalDegree ≤ 1 := by
    intro i
    exact (hdeg i).trans hk_le_one
  have hH2 : homogeneousPartVec4 2 Q = fun _ : Fin N => 0 := by
    funext i
    dsimp [homogeneousPartVec4]
    exact homogeneousPart4_eq_zero_of_totalDegree_le_one (by norm_num : 2 ≤ 2) (hdeg1 i)
  have hH3 : homogeneousPartVec4 3 Q = fun _ : Fin N => 0 := by
    funext i
    dsimp [homogeneousPartVec4]
    exact homogeneousPart4_eq_zero_of_totalDegree_le_one (by norm_num : 2 ≤ 3) (hdeg1 i)
  have hH4 : homogeneousPartVec4 4 Q = fun _ : Fin N => 0 := by
    funext i
    dsimp [homogeneousPartVec4]
    exact homogeneousPart4_eq_zero_of_totalDegree_le_one (by norm_num : 2 ≤ 4) (hdeg1 i)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  refine ⟨?_, ?_, ?_⟩
  · have hright : 0 ≤ weightedJetQuarterConst * A :=
      mul_nonneg weightedJetQuarterConst_nonneg hA0
    simpa [hH2, vecCoeffNorm4, coeffNorm4] using hright
  · intro ijk
    have hzeroNorm : interiorVecNorm (fun _i : Fin N => (0 : ℝ)) = 0 := by
      simp [interiorVecNorm, interiorVecSqNorm]
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hright : 0 ≤ weightedJetQuarterConst * A * (k : ℝ) / 64 := by
      exact div_nonneg (mul_nonneg (mul_nonneg weightedJetQuarterConst_nonneg hA0) hk0)
        (by norm_num)
    rw [hH3]
    simpa [hzeroNorm] using hright
  · intro ijkl
    have hzeroNorm : interiorVecNorm (fun _i : Fin N => (0 : ℝ)) = 0 := by
      simp [interiorVecNorm, interiorVecSqNorm]
    have hk20 : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg (k : ℝ)
    have hright : 0 ≤ weightedJetQuarterConst * A * (k : ℝ) ^ 2 / 256 := by
      exact div_nonneg (mul_nonneg (mul_nonneg weightedJetQuarterConst_nonneg hA0) hk20)
        (by norm_num)
    rw [hH4]
    simpa [hzeroNorm] using hright

theorem weightedJet_ordered_coeff_bounds_of_tail_unit_bounds
    {N k : ℕ} {A : ℝ}
    (hk : 1 ≤ k) (hA : 1 ≤ A)
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hunit2 : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 2 Q i)) ≤
        weightedJetTailConst * A)
    (hunit3 : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 3 Q i)) ≤
        8 * (k : ℝ) * (weightedJetTailConst * A))
    (hunit4 : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 4 Q i)) ≤
        64 * (k : ℝ) ^ 2 * (weightedJetTailConst * A)) :
    vecCoeffNorm4 (homogeneousPartVec4 2 Q) ≤ weightedJetQuarterConst * A ∧
    (∀ ijk : Fin 4 × Fin 4 × Fin 4,
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.coeff
          (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
            Finsupp.single ijk.2.2 1)
          (homogeneousPartVec4 3 Q i)) ≤ weightedJetQuarterConst * A * (k : ℝ) / 64) ∧
    (∀ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.coeff
          (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
            Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1)
          (homogeneousPartVec4 4 Q i)) ≤ weightedJetQuarterConst * A * (k : ℝ) ^ 2 / 256) := by
  classical
  let H2 : Fin N → MvPolynomial (Fin 4) ℝ := homogeneousPartVec4 2 Q
  let H3 : Fin N → MvPolynomial (Fin 4) ℝ := homogeneousPartVec4 3 Q
  let H4 : Fin N → MvPolynomial (Fin 4) ℝ := homogeneousPartVec4 4 Q
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk20 : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg (k : ℝ)
  have htail0 : 0 ≤ weightedJetTailConst := weightedJetTailConst_nonneg
  have hQC1000 : 1000 * weightedJetTailConst ≤ weightedJetQuarterConst :=
    weightedJetQuarterConst_absorbs_tail_1000
  have hhom2 : ∀ i, homogeneousPart4 2 (H2 i) = H2 i := by
    intro i
    dsimp [H2, homogeneousPartVec4]
    exact homogeneousPart4_idem 2 (Q i)
  have hhom3 : ∀ i, homogeneousPart4 3 (H3 i) = H3 i := by
    intro i
    dsimp [H3, homogeneousPartVec4]
    exact homogeneousPart4_idem 3 (Q i)
  have hhom4 : ∀ i, homogeneousPart4 4 (H4 i) = H4 i := by
    intro i
    dsimp [H4, homogeneousPartVec4]
    exact homogeneousPart4_idem 4 (Q i)
  have hunit2H : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H2 i)) ≤
        weightedJetTailConst * A := by
    intro v hv
    simpa [H2] using hunit2 v hv
  have hunit3H : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H3 i)) ≤
        8 * (k : ℝ) * (weightedJetTailConst * A) := by
    intro v hv
    simpa [H3] using hunit3 v hv
  have hunit4H : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H4 i)) ≤
        64 * (k : ℝ) ^ 2 * (weightedJetTailConst * A) := by
    intro v hv
    simpa [H4] using hunit4 v hv
  have h2 : vecCoeffNorm4 (homogeneousPartVec4 2 Q) ≤ weightedJetQuarterConst * A := by
    let S : Set ℝ := { y : ℝ |
      ∃ v : Fin 4 → ℝ, localSqNorm v = 1 ∧
        y = interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (H2 i)) }
    have hcoeff := coeff_norm_from_spherical_sup_norm_degree_two_uniform H2 hhom2
    have hSne : S.Nonempty := by
      let e : Fin 4 → ℝ := fun i => if i = 0 then 1 else 0
      refine ⟨interiorVecNorm (fun i : Fin N => MvPolynomial.eval e (H2 i)), ?_⟩
      refine ⟨e, ?_, rfl⟩
      simp [e, localSqNorm]
    have hSupper : ∀ y ∈ S, y ≤ weightedJetTailConst * A := by
      rintro y ⟨v, hv, rfl⟩
      exact hunit2H v hv
    have hsSup_le : sSup S ≤ weightedJetTailConst * A := csSup_le hSne hSupper
    calc
      vecCoeffNorm4 (homogeneousPartVec4 2 Q) = vecCoeffNorm4 H2 := rfl
      _ ≤ 1000 * sSup S := by simpa [S] using hcoeff
      _ ≤ 1000 * (weightedJetTailConst * A) :=
        mul_le_mul_of_nonneg_left hsSup_le (by norm_num)
      _ = (1000 * weightedJetTailConst) * A := by ring
      _ ≤ weightedJetQuarterConst * A := mul_le_mul_of_nonneg_right hQC1000 hA0
  have h3 : ∀ ijk : Fin 4 × Fin 4 × Fin 4,
      interiorVecNorm (fun i : Fin N => MvPolynomial.coeff
        (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
          Finsupp.single ijk.2.2 1) (homogeneousPartVec4 3 Q i)) ≤
        weightedJetQuarterConst * A * (k : ℝ) / 64 := by
    intro ijk
    let alpha3 : Fin 4 × Fin 4 × Fin 4 → Fin 4 →₀ ℕ := fun ijk =>
      Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 + Finsupp.single ijk.2.2 1
    let weight : ℝ := (500 : ℝ) ^ (2 * weightedDegree4 (alpha3 ijk))
    have hC3 : 0 ≤ 8 * (k : ℝ) * (weightedJetTailConst * A) := by positivity
    have hcoeff := weightedJet_ordered_cubic_coeff_bound_of_unit_eval_bound
      H3 hhom3 hC3 hunit3H ijk
    have hconst : 4096 * weight * weightedJetTailConst ≤ weightedJetQuarterConst := by
      dsimp [weight, alpha3]
      exact weightedJetQuarterConst_absorbs_tail_cubic ijk
    have hfactor0 : 0 ≤ A * (k : ℝ) / 64 :=
      div_nonneg (mul_nonneg hA0 hk0) (by norm_num)
    calc
      interiorVecNorm (fun i : Fin N => MvPolynomial.coeff
          (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
            Finsupp.single ijk.2.2 1) (homogeneousPartVec4 3 Q i))
          = interiorVecNorm (fun i : Fin N => MvPolynomial.coeff (alpha3 ijk) (H3 i)) := rfl
      _ ≤ weight * (8 * (8 * (k : ℝ) * (weightedJetTailConst * A))) := by
        simpa [weight, alpha3] using hcoeff
      _ = (4096 * weight * weightedJetTailConst) * (A * (k : ℝ) / 64) := by ring
      _ ≤ weightedJetQuarterConst * (A * (k : ℝ) / 64) :=
        mul_le_mul_of_nonneg_right hconst hfactor0
      _ = weightedJetQuarterConst * A * (k : ℝ) / 64 := by ring
  have h4 : ∀ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      interiorVecNorm (fun i : Fin N => MvPolynomial.coeff
        (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
          Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1) (homogeneousPartVec4 4 Q i)) ≤
        weightedJetQuarterConst * A * (k : ℝ) ^ 2 / 256 := by
    intro ijkl
    let alpha4 : ((Fin 4 × Fin 4) × Fin 4) × Fin 4 → Fin 4 →₀ ℕ := fun ijkl =>
      Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
        Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1
    let weight : ℝ := (500 : ℝ) ^ (2 * weightedDegree4 (alpha4 ijkl))
    have hC4 : 0 ≤ 64 * (k : ℝ) ^ 2 * (weightedJetTailConst * A) := by positivity
    have hcoeff := weightedJet_ordered_quartic_coeff_bound_of_unit_eval_bound
      H4 hhom4 hC4 hunit4H ijkl
    have hconst : 262144 * weight * weightedJetTailConst ≤ weightedJetQuarterConst := by
      dsimp [weight, alpha4]
      exact weightedJetQuarterConst_absorbs_tail_quartic ijkl
    have hfactor0 : 0 ≤ A * (k : ℝ) ^ 2 / 256 :=
      div_nonneg (mul_nonneg hA0 hk20) (by norm_num)
    calc
      interiorVecNorm (fun i : Fin N => MvPolynomial.coeff
          (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
            Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1)
          (homogeneousPartVec4 4 Q i))
          = interiorVecNorm (fun i : Fin N => MvPolynomial.coeff (alpha4 ijkl) (H4 i)) := rfl
      _ ≤ weight * (16 * (64 * (k : ℝ) ^ 2 * (weightedJetTailConst * A))) := by
        simpa [weight, alpha4] using hcoeff
      _ = (262144 * weight * weightedJetTailConst) * (A * (k : ℝ) ^ 2 / 256) := by
        ring
      _ ≤ weightedJetQuarterConst * (A * (k : ℝ) ^ 2 / 256) :=
        mul_le_mul_of_nonneg_right hconst hfactor0
      _ = weightedJetQuarterConst * A * (k : ℝ) ^ 2 / 256 := by ring
  exact ⟨h2, h3, h4⟩

/-- Analytic core of the higher-jet estimate.

This packages the symmetric-hole Remez/Bernstein argument for the divided
residual `W(t) = (Q(tv) - Q₀ - Q₁(tv))/t²`, after the algebraic reduction to
ordered coefficient vectors. -/
theorem symmetricHole_weightedJet_ordered_coeff_bounds
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (hkSmall : (k : ℝ) ≤ weightedJetGamma0 * epsilon ^ (-(1 : ℝ) / 4))
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon) :
    vecCoeffNorm4 (homogeneousPartVec4 2 Q) ≤ weightedJetQuarterConst * A ∧
    (∀ ijk : Fin 4 × Fin 4 × Fin 4,
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.coeff
          (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
            Finsupp.single ijk.2.2 1)
          (homogeneousPartVec4 3 Q i)) ≤ weightedJetQuarterConst * A * (k : ℝ) / 64) ∧
    (∀ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.coeff
          (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
            Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1)
          (homogeneousPartVec4 4 Q i)) ≤ weightedJetQuarterConst * A * (k : ℝ) ^ 2 / 256) := by
  by_cases hk2 : 2 ≤ k
  · let rho : ℝ := weightedJetHoleRadius epsilon k
    rcases weightedJet_hole_parameters_quarter heps heps0 hkSmall hk2 with
      ⟨hrho, hrhoSmall, hdegCond⟩
    have hsqrtOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
        Real.sqrt epsilon ≤ t ^ 2 := by
      intro t ht
      exact weightedJetHole_sqrt_le_sq heps.le ht.1
    have hlinearOuter : ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
        (k : ℝ) * Real.sqrt epsilon * |t| ≤ t ^ 2 := by
      intro t ht
      exact weightedJetHole_linear_le_sq heps.le ht.1
    have htailEq : 2 * Real.exp 6 * (2 * A + jetErrorConst * A + 64 * A) =
        weightedJetTailConst * A := by
      unfold weightedJetTailConst
      ring
    have hunit2 : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
        interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 2 Q i)) ≤
          weightedJetTailConst * A := by
      intro v hv
      have h := weightedJet_higher_eval_bound_two_sixty_four heps hk2 hA hrho hrhoSmall
        hdegCond Q hdeg hlocal hzeroLines hv hsqrtOuter hlinearOuter
      simpa [htailEq] using h
    have hunit3 : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
        interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 3 Q i)) ≤
          8 * (k : ℝ) * (weightedJetTailConst * A) := by
      intro v hv
      have h := weightedJet_higher_eval_bound_three_sixty_four heps hk2 hA hrho hrhoSmall
        hdegCond Q hdeg hlocal hzeroLines hv hsqrtOuter hlinearOuter
      simpa [htailEq] using h
    have hunit4 : ∀ v : Fin 4 → ℝ, localSqNorm v = 1 →
        interiorVecNorm (fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec4 4 Q i)) ≤
          64 * (k : ℝ) ^ 2 * (weightedJetTailConst * A) := by
      intro v hv
      have h := weightedJet_higher_eval_bound_four_sixty_four heps hk2 hA hrho hrhoSmall
        hdegCond Q hdeg hlocal hzeroLines hv hsqrtOuter hlinearOuter
      simpa [htailEq] using h
    exact weightedJet_ordered_coeff_bounds_of_tail_unit_bounds hk hA Q hunit2 hunit3 hunit4
  · exact symmetricHole_weightedJet_ordered_coeff_bounds_degree_one hk hk2 hA Q hdeg

/-- Higher-jet coefficient bounds obtained from the ordered-coefficient
symmetric-hole estimate and the fixed finite-dimensional coefficient
decompositions. -/
theorem symmetricHole_weightedJet_higher_coeff_bounds
    {N k : ℕ} {epsilon A : ℝ}
    (heps : 0 < epsilon)
    (heps0 : epsilon ≤ schmInteriorEpsilon0)
    (hk : 1 ≤ k)
    (hA : 1 ≤ A)
    (hkSmall : (k : ℝ) ≤ weightedJetGamma0 * epsilon ^ (-(1 : ℝ) / 4))
    (Q : Fin N → MvPolynomial (Fin 4) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ k)
    (hlocal : ∀ x, boxSmall x →
      interiorVecNorm (fun i : Fin N => MvPolynomial.eval x (Q i))
        ≤ A * (Real.sqrt epsilon + localSqNorm x))
    (hzeroLines : ∀ zi : Fin 4, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * choiLamZeroDirection zi j) (Q i))
        ≤ A * Real.sqrt epsilon) :
    vecCoeffNorm4 (homogeneousPartVec4 2 Q) ≤ weightedJetQuarterConst * A ∧
    vecCoeffNorm4 (homogeneousPartVec4 3 Q) ≤ weightedJetQuarterConst * A * (k : ℝ) ∧
    vecCoeffNorm4 (homogeneousPartVec4 4 Q) ≤ weightedJetQuarterConst * A * (k : ℝ) ^ 2 := by
  rcases symmetricHole_weightedJet_ordered_coeff_bounds heps heps0 hk hA hkSmall
      Q hdeg hlocal hzeroLines with ⟨h2, h3coeff, h4coeff⟩
  have hhom3 : ∀ i, homogeneousPart4 3 (homogeneousPartVec4 3 Q i) =
      homogeneousPartVec4 3 Q i := by
    intro i
    dsimp [homogeneousPartVec4]
    exact homogeneousPart4_idem 3 (Q i)
  have hhom4 : ∀ i, homogeneousPart4 4 (homogeneousPartVec4 4 Q i) =
      homogeneousPartVec4 4 Q i := by
    intro i
    dsimp [homogeneousPartVec4]
    exact homogeneousPart4_idem 4 (Q i)
  have h3 : vecCoeffNorm4 (homogeneousPartVec4 3 Q) ≤
      weightedJetQuarterConst * A * (k : ℝ) := by
    calc
      vecCoeffNorm4 (homogeneousPartVec4 3 Q)
          ≤ ∑ ijk : Fin 4 × Fin 4 × Fin 4, interiorVecNorm
              (fun i : Fin N => MvPolynomial.coeff
                (Finsupp.single ijk.1 1 + Finsupp.single ijk.2.1 1 +
                  Finsupp.single ijk.2.2 1)
                (homogeneousPartVec4 3 Q i)) := by
            simpa using vecCoeffNorm4_cubic_le_ordered_sum_coeff_vectors
              (homogeneousPartVec4 3 Q) hhom3
      _ ≤ ∑ _ijk : Fin 4 × Fin 4 × Fin 4,
            weightedJetQuarterConst * A * (k : ℝ) / 64 := by
            exact Finset.sum_le_sum (fun ijk _ => h3coeff ijk)
      _ = weightedJetQuarterConst * A * (k : ℝ) := by
            rw [Finset.sum_const]
            norm_num [Fintype.card_prod, Fintype.card_fin]
            ring
  have h4 : vecCoeffNorm4 (homogeneousPartVec4 4 Q) ≤
      weightedJetQuarterConst * A * (k : ℝ) ^ 2 := by
    calc
      vecCoeffNorm4 (homogeneousPartVec4 4 Q)
          ≤ ∑ ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4, interiorVecNorm
              (fun i : Fin N => MvPolynomial.coeff
                (Finsupp.single ijkl.1.1.1 1 + Finsupp.single ijkl.1.1.2 1 +
                  Finsupp.single ijkl.1.2 1 + Finsupp.single ijkl.2 1)
                (homogeneousPartVec4 4 Q i)) := by
            simpa using vecCoeffNorm4_quartic_le_ordered_sum_coeff_vectors
              (homogeneousPartVec4 4 Q) hhom4
      _ ≤ ∑ _ijkl : ((Fin 4 × Fin 4) × Fin 4) × Fin 4,
            weightedJetQuarterConst * A * (k : ℝ) ^ 2 / 256 := by
            exact Finset.sum_le_sum (fun ijkl _ => h4coeff ijkl)
      _ = weightedJetQuarterConst * A * (k : ℝ) ^ 2 := by
            rw [Finset.sum_const]
            norm_num [Fintype.card_prod, Fintype.card_fin]
            ring
  exact ⟨h2, h3, h4⟩

end OptimalConvergenceRates
