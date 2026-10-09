/- Explicit coefficient normal form for homogeneous ternary cubics. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.NonSOS

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

private def exp3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

private lemma finsupp_eq_exp3 (d : Fin 3 →₀ ℕ) : d = exp3 (d 0) (d 1) (d 2) := by
  ext i
  fin_cases i <;> simp [exp3]

@[simp] private lemma exp3_add (a b c d e f : ℕ) :
    exp3 a b c + exp3 d e f = exp3 (a + d) (b + e) (c + f) := by
  ext i
  fin_cases i <;> simp [exp3]

@[simp] private lemma exp3_nsmul (n a b c : ℕ) :
    n • exp3 a b c = exp3 (n * a) (n * b) (n * c) := by
  ext i
  fin_cases i <;> simp [exp3]

@[simp] private lemma coeff_mul_two (m : Fin 3 →₀ ℕ)
    (p : MvPolynomial (Fin 3) ℝ) : coeff m (p * 2) = 2 * coeff m p := by
  rw [mul_comm]
  exact MvPolynomial.coeff_C_mul m 2 p

@[simp] private lemma coeff_two_mul (m : Fin 3 →₀ ℕ)
    (p : MvPolynomial (Fin 3) ℝ) : coeff m (2 * p) = 2 * coeff m p := by
  exact MvPolynomial.coeff_C_mul m 2 p

@[simp] private lemma exp3_eq_exp3_iff (a b c d e f : ℕ) :
    exp3 a b c = exp3 d e f ↔ a = d ∧ b = e ∧ c = f := by
  constructor
  · intro h
    have h0 := congrArg (fun x : Fin 3 →₀ ℕ ↦ x 0) h
    have h1 := congrArg (fun x : Fin 3 →₀ ℕ ↦ x 1) h
    have h2 := congrArg (fun x : Fin 3 →₀ ℕ ↦ x 2) h
    simpa [exp3] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private lemma degree_three_coordinate_cases {d : Fin 3 →₀ ℕ} (hd : d.degree = 3) :
    (d 0 = 3 ∧ d 1 = 0 ∧ d 2 = 0) ∨
    (d 0 = 2 ∧ d 1 = 1 ∧ d 2 = 0) ∨
    (d 0 = 2 ∧ d 1 = 0 ∧ d 2 = 1) ∨
    (d 0 = 1 ∧ d 1 = 2 ∧ d 2 = 0) ∨
    (d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 1) ∨
    (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 2) ∨
    (d 0 = 0 ∧ d 1 = 3 ∧ d 2 = 0) ∨
    (d 0 = 0 ∧ d 1 = 2 ∧ d 2 = 1) ∨
    (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 2) ∨
    (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 3) := by
  have hdDegree := hd
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hd
  have h0 : d 0 ≤ 3 := (Finsupp.le_degree 0 d).trans_eq hdDegree
  have h1 : d 1 ≤ 3 := (Finsupp.le_degree 1 d).trans_eq hdDegree
  have h2 : d 2 ≤ 3 := (Finsupp.le_degree 2 d).trans_eq hdDegree
  interval_cases h0' : d 0 <;> interval_cases h1' : d 1 <;>
    interval_cases h2' : d 2 <;> omega

/-- The coefficient expansion of a ternary cubic form. -/
def cubicNormalForm (q : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  monomial (exp3 3 0 0) (coeff (exp3 3 0 0) q)
    + monomial (exp3 2 1 0) (coeff (exp3 2 1 0) q)
    + monomial (exp3 2 0 1) (coeff (exp3 2 0 1) q)
    + monomial (exp3 1 2 0) (coeff (exp3 1 2 0) q)
    + monomial (exp3 1 1 1) (coeff (exp3 1 1 1) q)
    + monomial (exp3 1 0 2) (coeff (exp3 1 0 2) q)
    + monomial (exp3 0 3 0) (coeff (exp3 0 3 0) q)
    + monomial (exp3 0 2 1) (coeff (exp3 0 2 1) q)
    + monomial (exp3 0 1 2) (coeff (exp3 0 1 2) q)
    + monomial (exp3 0 0 3) (coeff (exp3 0 0 3) q)

theorem eq_cubicNormalForm_of_homogeneousPart3_eq
    {q : MvPolynomial (Fin 3) ℝ} (hq : homogeneousPart3 3 q = q) :
    q = cubicNormalForm q := by
  ext d
  by_cases hd : d.degree = 3
  · rcases degree_three_coordinate_cases hd with h | h | h | h | h | h | h | h | h | h
    all_goals
      have hdexp := finsupp_eq_exp3 d
      rcases h with ⟨h0, h1, h2⟩
      simp only [h0, h1, h2] at hdexp
      subst d
      simp [cubicNormalForm]
  · have hcoeff : coeff d q = 0 :=
      (isHomogeneous_of_homogeneousPart3_eq hq).coeff_eq_zero hd
    have hne (a b c : ℕ) (hsum : a + b + c = 3) : d ≠ exp3 a b c := by
      intro h
      apply hd
      subst d
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]
      simp [exp3]
      omega
    have hne_rev (a b c : ℕ) (hsum : a + b + c = 3) : exp3 a b c ≠ d :=
      (hne a b c hsum).symm
    rw [hcoeff]
    simp [cubicNormalForm, hne_rev]

private lemma eval_monomial_exp3 (v : Fin 3 → ℝ) (a b c : ℕ) (r : ℝ) :
    eval v (monomial (exp3 a b c) r) = r * v 0 ^ a * v 1 ^ b * v 2 ^ c := by
  simp [MvPolynomial.eval_monomial, exp3, Fin.prod_univ_three]
  ring

private lemma eval_cubicNormalForm (q : MvPolynomial (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    eval v (cubicNormalForm q) =
      coeff (exp3 3 0 0) q * v 0 ^ 3
        + coeff (exp3 2 1 0) q * v 0 ^ 2 * v 1
        + coeff (exp3 2 0 1) q * v 0 ^ 2 * v 2
        + coeff (exp3 1 2 0) q * v 0 * v 1 ^ 2
        + coeff (exp3 1 1 1) q * v 0 * v 1 * v 2
        + coeff (exp3 1 0 2) q * v 0 * v 2 ^ 2
        + coeff (exp3 0 3 0) q * v 1 ^ 3
        + coeff (exp3 0 2 1) q * v 1 ^ 2 * v 2
        + coeff (exp3 0 1 2) q * v 1 * v 2 ^ 2
        + coeff (exp3 0 0 3) q * v 2 ^ 3 := by
  simp only [cubicNormalForm, map_add, eval_monomial_exp3]
  ring

lemma eval_homogeneous_cubic {q : MvPolynomial (Fin 3) ℝ}
    (hq : homogeneousPart3 3 q = q) (v : Fin 3 → ℝ) :
    eval v q = eval v (cubicNormalForm q) := by
  exact congrArg (eval v) (eq_cubicNormalForm_of_homogeneousPart3_eq hq)


lemma eval_axisX_of_homogeneous_cubic
    {q : MvPolynomial (Fin 3) ℝ} (hq : homogeneousPart3 3 q = q) :
    eval motzkinAxisX q = coeff (exp3 3 0 0) q := by
  rw [eval_homogeneous_cubic hq, eval_cubicNormalForm]
  have h0 : motzkinAxisX 0 = 1 := rfl
  have h1 : motzkinAxisX 1 = 0 := rfl
  have h2 : motzkinAxisX 2 = 0 := rfl
  simp [h0, h1, h2]

lemma eval_axisY_of_homogeneous_cubic
    {q : MvPolynomial (Fin 3) ℝ} (hq : homogeneousPart3 3 q = q) :
    eval motzkinAxisY q = coeff (exp3 0 3 0) q := by
  rw [eval_homogeneous_cubic hq, eval_cubicNormalForm]
  have h0 : motzkinAxisY 0 = 0 := rfl
  have h1 : motzkinAxisY 1 = 1 := rfl
  have h2 : motzkinAxisY 2 = 0 := rfl
  simp [h0, h1, h2]

lemma sign_walsh_of_homogeneous_cubic
    {q : MvPolynomial (Fin 3) ℝ} (hq : homogeneousPart3 3 q = q) :
    eval (motzkinSignDirection 0 0) q - eval (motzkinSignDirection 0 1) q
        + eval (motzkinSignDirection 1 0) q - eval (motzkinSignDirection 1 1) q =
      4 * (coeff (exp3 2 0 1) q + coeff (exp3 0 2 1) q
        + coeff (exp3 0 0 3) q) := by
  rw [eval_homogeneous_cubic hq, eval_cubicNormalForm,
    eval_homogeneous_cubic hq, eval_cubicNormalForm,
    eval_homogeneous_cubic hq, eval_cubicNormalForm,
    eval_homogeneous_cubic hq, eval_cubicNormalForm]
  simp [motzkinSignDirection]
  ring

lemma coeff_sq_exp402_of_homogeneous_cubic
    {q : MvPolynomial (Fin 3) ℝ} (hq : homogeneousPart3 3 q = q) :
    coeff (exp3 4 0 2) (q ^ 2) =
      2 * coeff (exp3 3 0 0) q * coeff (exp3 1 0 2) q
        + coeff (exp3 2 0 1) q ^ 2 := by
  rw [eq_cubicNormalForm_of_homogeneousPart3_eq hq]
  simp only [cubicNormalForm, pow_two]
  ring_nf
  simp [MvPolynomial.coeff_add, mul_comm,
    MvPolynomial.monomial_pow, MvPolynomial.monomial_mul,
    MvPolynomial.coeff_monomial]

lemma coeff_sq_exp042_of_homogeneous_cubic
    {q : MvPolynomial (Fin 3) ℝ} (hq : homogeneousPart3 3 q = q) :
    coeff (exp3 0 4 2) (q ^ 2) =
      2 * coeff (exp3 0 3 0) q * coeff (exp3 0 1 2) q
        + coeff (exp3 0 2 1) q ^ 2 := by
  rw [eq_cubicNormalForm_of_homogeneousPart3_eq hq]
  simp only [cubicNormalForm, pow_two]
  ring_nf
  simp [MvPolynomial.coeff_add, mul_comm,
    MvPolynomial.monomial_pow, MvPolynomial.monomial_mul,
    MvPolynomial.coeff_monomial]

lemma coeff_sq_exp006_of_homogeneous_cubic
    {q : MvPolynomial (Fin 3) ℝ} (hq : homogeneousPart3 3 q = q) :
    coeff (exp3 0 0 6) (q ^ 2) = coeff (exp3 0 0 3) q ^ 2 := by
  rw [eq_cubicNormalForm_of_homogeneousPart3_eq hq]
  simp only [cubicNormalForm, pow_two]
  ring_nf
  simp [MvPolynomial.coeff_add, mul_comm,
    MvPolynomial.monomial_pow, MvPolynomial.monomial_mul,
    MvPolynomial.coeff_monomial]


private lemma motzkinSextic_eq_monomials :
    motzkinSextic = monomial (exp3 4 2 0) 1 + monomial (exp3 2 4 0) 1
      + monomial (exp3 0 0 6) 1 - monomial (exp3 2 2 2) 3 := by
  have hcross :
      (3 * X (0 : Fin 3) ^ 2 * X (1 : Fin 3) ^ 2 * X (2 : Fin 3) ^ 2 :
        MvPolynomial (Fin 3) ℝ) = monomial (exp3 2 2 2) 3 := by
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.X_pow_eq_monomial]
    change C 3 * monomial (Finsupp.single (0 : Fin 3) 2) 1 *
        monomial (Finsupp.single (1 : Fin 3) 2) 1 *
        monomial (Finsupp.single (2 : Fin 3) 2) 1 = _
    rw [MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul,
      MvPolynomial.monomial_mul]
    simp [exp3]
  rw [motzkinSextic, hcross]
  simp [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, exp3]

/-- The Motzkin sextic is not a sum of squares of real polynomials. -/
theorem motzkinSextic_not_sos : ¬ IsSOS motzkinSextic := by
  rintro ⟨N, Q, hQ⟩
  let P : Fin N → MvPolynomial (Fin 3) ℝ := fun i ↦ homogeneousPart3 3 (Q i)
  have hP : motzkinSextic = ∑ i : Fin N, (P i) ^ 2 := by
    simpa [P] using motzkinSextic_eq_cubicParts_sq hQ
  have hPhom (i : Fin N) : homogeneousPart3 3 (P i) = P i := by
    unfold P
    rw [homogeneousPart3_eq_homogeneousComponent,
      homogeneousPart3_eq_homogeneousComponent]
    simpa using (MvPolynomial.homogeneousComponent_of_mem (m := 3)
      (MvPolynomial.homogeneousComponent_mem 3 (Q i)))
  have hzeroEval (z : Fin 3 → ℝ) (hz : eval z motzkinSextic = 0) (i : Fin N) :
      eval z (P i) = 0 := by
    have hsum : ∑ j : Fin N, eval z (P j) ^ 2 = 0 := by
      calc
        ∑ j : Fin N, eval z (P j) ^ 2 = eval z (∑ j : Fin N, (P j) ^ 2) := by
          simp
        _ = eval z motzkinSextic := by rw [← hP]
        _ = 0 := hz
    have hsquare :
        eval z (P i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (eval z (P j)))).mp
        hsum i (Finset.mem_univ i)
    nlinarith
  have hx3 (i : Fin N) : coeff (exp3 3 0 0) (P i) = 0 := by
    rw [← eval_axisX_of_homogeneous_cubic (hPhom i)]
    exact hzeroEval motzkinAxisX motzkinSextic_eval_axisX i
  have hy3 (i : Fin N) : coeff (exp3 0 3 0) (P i) = 0 := by
    rw [← eval_axisY_of_homogeneous_cubic (hPhom i)]
    exact hzeroEval motzkinAxisY motzkinSextic_eval_axisY i
  have hcoeff402 : coeff (exp3 4 0 2) motzkinSextic = 0 := by
    rw [motzkinSextic_eq_monomials]
    simp [MvPolynomial.coeff_monomial]
  have hsum_x2z : ∑ i : Fin N, coeff (exp3 2 0 1) (P i) ^ 2 = 0 := by
    have h := congrArg (coeff (exp3 4 0 2)) hP
    rw [hcoeff402, MvPolynomial.coeff_sum] at h
    simp_rw [coeff_sq_exp402_of_homogeneous_cubic (hPhom _), hx3] at h
    norm_num at h
    exact h.symm
  have hx2z (i : Fin N) : coeff (exp3 2 0 1) (P i) = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ sq_nonneg (coeff (exp3 2 0 1) (P j)))).mp
      hsum_x2z i (Finset.mem_univ i)
    nlinarith
  have hcoeff042 : coeff (exp3 0 4 2) motzkinSextic = 0 := by
    rw [motzkinSextic_eq_monomials]
    simp [MvPolynomial.coeff_monomial]
  have hsum_y2z : ∑ i : Fin N, coeff (exp3 0 2 1) (P i) ^ 2 = 0 := by
    have h := congrArg (coeff (exp3 0 4 2)) hP
    rw [hcoeff042, MvPolynomial.coeff_sum] at h
    simp_rw [coeff_sq_exp042_of_homogeneous_cubic (hPhom _), hy3] at h
    norm_num at h
    exact h.symm
  have hy2z (i : Fin N) : coeff (exp3 0 2 1) (P i) = 0 := by
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ sq_nonneg (coeff (exp3 0 2 1) (P j)))).mp
      hsum_y2z i (Finset.mem_univ i)
    nlinarith
  have hz3 (i : Fin N) : coeff (exp3 0 0 3) (P i) = 0 := by
    have hw := sign_walsh_of_homogeneous_cubic (hPhom i)
    have h00 := hzeroEval (motzkinSignDirection 0 0)
      (motzkinSextic_eval_signDirection 0 0) i
    have h01 := hzeroEval (motzkinSignDirection 0 1)
      (motzkinSextic_eval_signDirection 0 1) i
    have h10 := hzeroEval (motzkinSignDirection 1 0)
      (motzkinSextic_eval_signDirection 1 0) i
    have h11 := hzeroEval (motzkinSignDirection 1 1)
      (motzkinSextic_eval_signDirection 1 1) i
    rw [h00, h01, h10, h11, hx2z i, hy2z i] at hw
    norm_num at hw ⊢
    linarith
  have hcoeff006 : coeff (exp3 0 0 6) motzkinSextic = 1 := by
    rw [motzkinSextic_eq_monomials]
    simp [MvPolynomial.coeff_monomial]
  have h := congrArg (coeff (exp3 0 0 6)) hP
  rw [hcoeff006, MvPolynomial.coeff_sum] at h
  simp only [coeff_sq_exp006_of_homogeneous_cubic (hPhom _), hz3] at h
  norm_num at h

end Motzkin

end OptimalConvergenceRates

end
