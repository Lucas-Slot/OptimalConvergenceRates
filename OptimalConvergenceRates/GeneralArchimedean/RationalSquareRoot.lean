/-
  The algebraic core of the dyadic rational-square-root construction used in
  the quantitative conversion of a fixed-degree preordering refutation.
-/
import OptimalConvergenceRates.BasicNotions.UnivariateParity
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

noncomputable section

open Finset

namespace OptimalConvergenceRates
namespace GeneralArchimedean
namespace RationalSquareRoot

open UnivariateParity

/-- Coefficientwise nonnegativity for a real univariate polynomial. -/
def CoeffNonneg (P : Polynomial ℝ) : Prop :=
  ∀ k, 0 ≤ P.coeff k

theorem coeffNonneg_zero : CoeffNonneg (0 : Polynomial ℝ) := by
  intro k
  simp

theorem coeffNonneg_one : CoeffNonneg (1 : Polynomial ℝ) := by
  intro k
  simp only [Polynomial.coeff_one]
  split <;> norm_num

theorem coeffNonneg_C {c : ℝ} (hc : 0 ≤ c) :
    CoeffNonneg (Polynomial.C c) := by
  intro k
  by_cases hk : k = 0
  · subst k
    simpa using hc
  · simp [Polynomial.coeff_C, hk]

theorem coeffNonneg_X : CoeffNonneg (Polynomial.X : Polynomial ℝ) := by
  intro k
  simp only [Polynomial.coeff_X]
  split <;> norm_num

theorem CoeffNonneg.add {P Q : Polynomial ℝ}
    (hP : CoeffNonneg P) (hQ : CoeffNonneg Q) :
    CoeffNonneg (P + Q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact add_nonneg (hP k) (hQ k)

theorem CoeffNonneg.mul {P Q : Polynomial ℝ}
    (hP : CoeffNonneg P) (hQ : CoeffNonneg Q) :
    CoeffNonneg (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hP ij.1) (hQ ij.2)

theorem CoeffNonneg.pow {P : Polynomial ℝ}
    (hP : CoeffNonneg P) : ∀ k : ℕ, CoeffNonneg (P ^ k)
  | 0 => by simpa using coeffNonneg_one
  | k + 1 => by
      rw [pow_succ]
      exact (hP.pow k).mul hP

theorem coeffNonneg_prod {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial ℝ) (hP : ∀ i ∈ s, CoeffNonneg (P i)) :
    CoeffNonneg (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coeffNonneg_one
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hP a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))

theorem coeffNonneg_sum {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial ℝ) (hP : ∀ i ∈ s, CoeffNonneg (P i)) :
    CoeffNonneg (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coeffNonneg_zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hP a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))

/-- Composition preserves coefficientwise nonnegativity. -/
theorem CoeffNonneg.comp {P Q : Polynomial ℝ}
    (hP : CoeffNonneg P) (hQ : CoeffNonneg Q) :
    CoeffNonneg (P.comp Q) := by
  rw [Polynomial.comp_eq_aeval, Polynomial.aeval_eq_sum_range]
  apply coeffNonneg_sum
  intro k hk
  simpa only [Polynomial.smul_eq_C_mul] using
    (coeffNonneg_C (hP k)).mul (hQ.pow k)


/-- A coefficientwise nonnegative polynomial is nonnegative on the
nonnegative half-line. -/
theorem CoeffNonneg.eval_nonneg {P : Polynomial ℝ}
    (hP : CoeffNonneg P) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ P.eval x := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (hP k) (pow_nonneg hx k)

/-- If the constant coefficient vanishes, evaluation grows at least linearly
under dilation on the positive half-line.  The division-free formulation is
convenient in ordered-ring calculations. -/
theorem CoeffNonneg.mul_eval_le_mul_eval
    {P : Polynomial ℝ} (hP : CoeffNonneg P)
    (hP0 : P.coeff 0 = 0)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y * P.eval x ≤ x * P.eval y := by
  have hy : 0 ≤ y := hx.trans hxy
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [hP0]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hpow : x ^ j ≤ y ^ j := pow_le_pow_left₀ hx hxy j
    have hmul := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (hP (j + 1)) (mul_nonneg hx hy))
    convert hmul using 1 <;> simp [pow_succ] <;> ring

/-- The j-th dyadic scale used to approximate the square root. -/
def gridPoint (δ : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * Real.sqrt δ

theorem gridPoint_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) :
    0 ≤ gridPoint δ j := by
  dsimp [gridPoint]
  positivity

/-- Product over the dyadic grid before separating even and odd powers. -/
def gridProduct (δ : ℝ) (ell J : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.range (J + 1),
    (Polynomial.X + Polynomial.C (gridPoint δ j)) ^ (2 * ell)

/-- The residual factor whose square is the sign-conjugate grid product. -/
def gridResidual (δ : ℝ) (ell J : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.range (J + 1),
    (Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ^ ell

/-- Even component P0 in W(z) = P0(z^2) + z V0(z^2). -/
def numerator (δ : ℝ) (ell J : ℕ) : Polynomial ℝ :=
  evenContract (gridProduct δ ell J)

/-- Odd quotient V0 in W(z) = P0(z^2) + z V0(z^2). -/
def denominator (δ : ℝ) (ell J : ℕ) : Polynomial ℝ :=
  oddContract (gridProduct δ ell J)
/-- Shift the variable by δ and divide by a scalar c. -/
def normalizeShift (δ c : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C c⁻¹ * P.comp (Polynomial.X + Polynomial.C δ)

/-- The normalized denominator V with V(0) = 1, assuming its normalizing
value is nonzero. -/
def normalizedDenominator (δ : ℝ) (ell J : ℕ) : Polynomial ℝ :=
  normalizeShift δ ((denominator δ ell J).eval δ) (denominator δ ell J)
/-- Normalized numerator after shifting v = u + δ. -/
def normalizedNumerator (δ : ℝ) (ell J : ℕ) : Polynomial ℝ :=
  normalizeShift δ ((denominator δ ell J).eval δ) (numerator δ ell J)

/-- Normalized residual after shifting v = u + δ. -/
def normalizedResidual (δ : ℝ) (ell J : ℕ) : Polynomial ℝ :=
  normalizeShift δ ((denominator δ ell J).eval δ) (gridResidual δ ell J)

/-- The SOS error E = δ V^2 + R^2 in the rational-square-root identity. -/
def normalizedError (δ : ℝ) (ell J : ℕ) : Polynomial ℝ :=
  Polynomial.C δ * normalizedDenominator δ ell J ^ 2 +
    normalizedResidual δ ell J ^ 2





theorem gridProduct_eval (δ t : ℝ) (ell J : ℕ) :
    (gridProduct δ ell J).eval t =
      ∏ j ∈ Finset.range (J + 1), (t + gridPoint δ j) ^ (2 * ell) := by
  simp [gridProduct, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

theorem gridResidual_eval (δ v : ℝ) (ell J : ℕ) :
    (gridResidual δ ell J).eval v =
      ∏ j ∈ Finset.range (J + 1), ((gridPoint δ j) ^ 2 - v) ^ ell := by
  simp [gridResidual, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]

theorem gridProduct_coeffNonneg {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ) :
    CoeffNonneg (gridProduct δ ell J) := by
  apply coeffNonneg_prod
  intro j hj
  exact (coeffNonneg_X.add (coeffNonneg_C (gridPoint_nonneg hδ j))).pow _

theorem oddContract_coeff (P : Polynomial ℝ) (k : ℕ) :
    (oddContract P).coeff k = P.coeff (k * 2 + 1) := by
  rw [oddContract, Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0),
    Polynomial.coeff_divX]
  apply oddPart_odd_coeff
  omega

theorem denominator_coeffNonneg {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ) :
    CoeffNonneg (denominator δ ell J) := by
  intro k
  rw [denominator, oddContract_coeff]
  exact gridProduct_coeffNonneg hδ ell J (k * 2 + 1)
/-- The odd quotient is strictly positive at the shift point. The first
factor of W(-sqrt δ) vanishes, whereas every factor of W(sqrt δ) is
strictly positive. -/
theorem denominator_eval_self_pos
    {δ : ℝ} (hδ : 0 < δ) {ell : ℕ} (hell : 0 < ell) (J : ℕ) :
    0 < (denominator δ ell J).eval δ := by
  let t : ℝ := Real.sqrt δ
  have ht : 0 < t := by
    dsimp [t]
    exact Real.sqrt_pos.2 hδ
  have ht_sq : t ^ 2 = δ := Real.sq_sqrt hδ.le
  have hzero : (gridProduct δ ell J).eval (-t) = 0 := by
    rw [gridProduct_eval]
    apply Finset.prod_eq_zero (show 0 ∈ Finset.range (J + 1) by simp)
    simp [gridPoint, t, hell.ne']
  have hpositive : 0 < (gridProduct δ ell J).eval t := by
    rw [gridProduct_eval]
    apply Finset.prod_pos
    intro j hj
    apply pow_pos
    have hgrid : 0 < gridPoint δ j := by
      dsimp [gridPoint]
      positivity
    linarith
  have hplus := eval_evenContract_add_oddContract
    (gridProduct δ ell J) t
  have hminus := eval_evenContract_add_oddContract
    (gridProduct δ ell J) (-t)
  simp only [neg_sq] at hminus
  rw [ht_sq] at hplus hminus
  have hplus' :
      (gridProduct δ ell J).eval t =
        (numerator δ ell J).eval δ +
          t * (denominator δ ell J).eval δ := by
    simpa [numerator, denominator] using hplus
  have hminus' :
      (gridProduct δ ell J).eval (-t) =
        (numerator δ ell J).eval δ -
          t * (denominator δ ell J).eval δ := by
    simpa only [numerator, denominator, sub_eq_add_neg, neg_mul] using hminus
  rw [hzero] at hminus'
  have htV : 0 < t * (denominator δ ell J).eval δ := by
    linarith
  rcases (mul_pos_iff.mp htV) with h | h
  · exact h.2
  · exact False.elim ((not_lt_of_ge ht.le) h.1)


theorem normalizeShift_coeffNonneg
    {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    {P : Polynomial ℝ} (hP : CoeffNonneg P) :
    CoeffNonneg (normalizeShift δ c P) := by
  exact (coeffNonneg_C (inv_nonneg.mpr hc)).mul <|
    hP.comp (coeffNonneg_X.add (coeffNonneg_C hδ))

theorem normalizeShift_coeff_zero
    {δ c : ℝ} (P : Polynomial ℝ) (hc : 0 < c)
    (hvalue : P.eval δ = c) :
    (normalizeShift δ c P).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [normalizeShift, Polynomial.eval_mul, Polynomial.eval_comp,
    hvalue, hc.ne']

theorem normalizedDenominator_coeffNonneg
    {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ)
    (hpos : 0 < (denominator δ ell J).eval δ) :
    CoeffNonneg (normalizedDenominator δ ell J) := by
  exact normalizeShift_coeffNonneg hδ hpos.le
    (denominator_coeffNonneg hδ ell J)

theorem normalizedDenominator_coeff_zero
    {δ : ℝ} (ell J : ℕ)
    (hpos : 0 < (denominator δ ell J).eval δ) :
    (normalizedDenominator δ ell J).coeff 0 = 1 := by
  exact normalizeShift_coeff_zero _ hpos rfl



theorem gridProduct_mul_reflected_eval
    (δ t : ℝ) (ell J : ℕ) :
    (gridProduct δ ell J).eval t * (gridProduct δ ell J).eval (-t) =
      (gridResidual δ ell J).eval (t ^ 2) ^ 2 := by
  rw [gridProduct_eval, gridProduct_eval, gridResidual_eval]
  rw [← Finset.prod_mul_distrib]
  calc
    ∏ j ∈ Finset.range (J + 1),
        (t + gridPoint δ j) ^ (2 * ell) *
          (-t + gridPoint δ j) ^ (2 * ell) =
      ∏ j ∈ Finset.range (J + 1),
        (((gridPoint δ j) ^ 2 - t ^ 2) ^ ell) ^ 2 := by
          apply Finset.prod_congr rfl
          intro j hj
          calc
            (t + gridPoint δ j) ^ (2 * ell) *
                (-t + gridPoint δ j) ^ (2 * ell)
                = ((t + gridPoint δ j) *
                    (-t + gridPoint δ j)) ^ (2 * ell) := by
                      rw [mul_pow]
            _ = ((gridPoint δ j) ^ 2 - t ^ 2) ^ (2 * ell) := by
                  congr 1
                  ring
            _ = (((gridPoint δ j) ^ 2 - t ^ 2) ^ ell) ^ 2 := by
                  exact pow_mul' _ 2 ell
    _ = (∏ j ∈ Finset.range (J + 1),
        ((gridPoint δ j) ^ 2 - t ^ 2) ^ ell) ^ 2 := by
          rw [Finset.prod_pow]

/-- Exact square-root identity on the nonnegative half-line. This is the
pointwise form of P0(v)^2 - v V0(v)^2 = R0(v)^2. -/
theorem numerator_sq_sub_mul_denominator_sq
    {v : ℝ} (hv : 0 ≤ v) (δ : ℝ) (ell J : ℕ) :
    (numerator δ ell J).eval v ^ 2 -
        v * (denominator δ ell J).eval v ^ 2 =
      (gridResidual δ ell J).eval v ^ 2 := by
  let t := Real.sqrt v
  have ht : t ^ 2 = v := Real.sq_sqrt hv
  have hconj := conjugateProduct_eval_sq (gridProduct δ ell J) t
  have hgrid := gridProduct_mul_reflected_eval δ t ell J
  dsimp [conjugateProduct] at hconj
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_X] at hconj
  rw [ht] at hconj hgrid
  dsimp [numerator, denominator]
  linarith

theorem numerator_natDegree_le (δ : ℝ) (ell J : ℕ) :
    (numerator δ ell J).natDegree ≤ (gridProduct δ ell J).natDegree :=
  evenContract_natDegree_le _
/-- The dyadic construction satisfies the square-root relation as a polynomial
identity, not merely after evaluation. -/
theorem numerator_sq_sub_X_mul_denominator_sq
    (δ : ℝ) (ell J : ℕ) :
    numerator δ ell J ^ 2 -
        Polynomial.X * denominator δ ell J ^ 2 =
      gridResidual δ ell J ^ 2 := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro v hv
  change (numerator δ ell J ^ 2 -
      Polynomial.X * denominator δ ell J ^ 2).eval v =
    (gridResidual δ ell J ^ 2).eval v
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_X] using
      numerator_sq_sub_mul_denominator_sq hv δ ell J
/-- After shifting and normalizing, the construction satisfies
P(u)^2 - u V(u)^2 = E(u) as an exact polynomial identity. -/
theorem normalizedNumerator_sq_sub_X_mul_denominator_sq
    {δ : ℝ} (hδ : 0 < δ) {ell : ℕ} (hell : 0 < ell) (J : ℕ) :
    normalizedNumerator δ ell J ^ 2 -
        Polynomial.X * normalizedDenominator δ ell J ^ 2 =
      normalizedError δ ell J := by
  apply Polynomial.funext
  intro u
  let c : ℝ := (denominator δ ell J).eval δ
  have hc : 0 < c := denominator_eval_self_pos hδ hell J
  have hbase := congrArg (fun Q : Polynomial ℝ => Q.eval (u + δ))
    (numerator_sq_sub_X_mul_denominator_sq δ ell J)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_X] at hbase
  simp only [normalizedNumerator, normalizedDenominator, normalizedResidual,
    normalizedError, normalizeShift, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_comp]
  change (c⁻¹ * (numerator δ ell J).eval (u + δ)) ^ 2 -
      u * (c⁻¹ * (denominator δ ell J).eval (u + δ)) ^ 2 =
    δ * (c⁻¹ * (denominator δ ell J).eval (u + δ)) ^ 2 +
      (c⁻¹ * (gridResidual δ ell J).eval (u + δ)) ^ 2
  field_simp [hc.ne']
  nlinarith [hbase]

/-- The normalized error polynomial is an explicit sum of two squares. -/
theorem normalizedError_isSOSUni
    {δ : ℝ} (hδ : 0 ≤ δ) (ell J : ℕ) :
    IsSOSUni (normalizedError δ ell J) := by
  let q0 := Polynomial.C (Real.sqrt δ) * normalizedDenominator δ ell J
  let q1 := normalizedResidual δ ell J
  refine ⟨2, ![q0, q1], ?_⟩
  simp only [Fin.sum_univ_two]
  dsimp [q0, q1, normalizedError]
  rw [mul_pow]
  rw [← Polynomial.C_pow]
  rw [Real.sq_sqrt hδ]






theorem gridProduct_natDegree_le (δ : ℝ) (ell J : ℕ) :
    (gridProduct δ ell J).natDegree ≤ 2 * ell * (J + 1) := by
  calc
    (gridProduct δ ell J).natDegree ≤
        ∑ j ∈ Finset.range (J + 1),
          ((Polynomial.X + Polynomial.C (gridPoint δ j)) ^
            (2 * ell)).natDegree :=
      by
        change (∏ j ∈ Finset.range (J + 1),
          (Polynomial.X + Polynomial.C (gridPoint δ j)) ^
            (2 * ell)).natDegree ≤ _
        exact Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.range (J + 1), 2 * ell := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        ((Polynomial.X + Polynomial.C (gridPoint δ j)) ^
            (2 * ell)).natDegree ≤
            (2 * ell) *
              (Polynomial.X + Polynomial.C (gridPoint δ j)).natDegree :=
          Polynomial.natDegree_pow_le
        _ = 2 * ell := by rw [Polynomial.natDegree_X_add_C]; omega
    _ = 2 * ell * (J + 1) := by simp [mul_comm]

theorem gridResidual_natDegree_le (δ : ℝ) (ell J : ℕ) :
    (gridResidual δ ell J).natDegree ≤ ell * (J + 1) := by
  calc
    (gridResidual δ ell J).natDegree ≤
        ∑ j ∈ Finset.range (J + 1),
          ((Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ^
            ell).natDegree :=
      by
        change (∏ j ∈ Finset.range (J + 1),
          (Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ^
            ell).natDegree ≤ _
        exact Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.range (J + 1), ell := by
      apply Finset.sum_le_sum
      intro j hj
      have hlinear :
          (Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X).natDegree ≤ 1 := by
        change (Polynomial.C ((gridPoint δ j) ^ 2) + (-Polynomial.X)).natDegree ≤ 1
        exact (Polynomial.natDegree_add_le _ _).trans (by simp)
      calc
        ((Polynomial.C ((gridPoint δ j) ^ 2) - Polynomial.X) ^
            ell).natDegree ≤
            ell * (Polynomial.C ((gridPoint δ j) ^ 2) -
              Polynomial.X).natDegree := Polynomial.natDegree_pow_le
        _ ≤ ell * 1 := Nat.mul_le_mul_left ell hlinear
        _ = ell := by simp
    _ = ell * (J + 1) := by simp [mul_comm]

theorem normalizeShift_natDegree_le (δ c : ℝ) (P : Polynomial ℝ) :
    (normalizeShift δ c P).natDegree ≤ P.natDegree := by
  calc
    (normalizeShift δ c P).natDegree ≤
        (Polynomial.C c⁻¹).natDegree +
          (P.comp (Polynomial.X + Polynomial.C δ)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + P.natDegree := by
      apply Nat.add_le_add
      · simp
      · rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    _ = P.natDegree := by simp

theorem denominator_natDegree_le (δ : ℝ) (ell J : ℕ) :
    (denominator δ ell J).natDegree ≤ (gridProduct δ ell J).natDegree :=
  oddContract_natDegree_le _

theorem numerator_degree_bound (δ : ℝ) (ell J : ℕ) :
    (numerator δ ell J).natDegree ≤ 2 * ell * (J + 1) :=
  (numerator_natDegree_le δ ell J).trans (gridProduct_natDegree_le δ ell J)

theorem denominator_degree_bound (δ : ℝ) (ell J : ℕ) :
    (denominator δ ell J).natDegree ≤ 2 * ell * (J + 1) :=
  (denominator_natDegree_le δ ell J).trans (gridProduct_natDegree_le δ ell J)

theorem normalizedNumerator_degree_bound (δ : ℝ) (ell J : ℕ) :
    (normalizedNumerator δ ell J).natDegree ≤ 2 * ell * (J + 1) := by
  exact (normalizeShift_natDegree_le δ
    ((denominator δ ell J).eval δ) (numerator δ ell J)).trans
      (numerator_degree_bound δ ell J)

theorem normalizedDenominator_degree_bound (δ : ℝ) (ell J : ℕ) :
    (normalizedDenominator δ ell J).natDegree ≤ 2 * ell * (J + 1) := by
  exact (normalizeShift_natDegree_le δ
    ((denominator δ ell J).eval δ) (denominator δ ell J)).trans
      (denominator_degree_bound δ ell J)

theorem normalizedResidual_degree_bound (δ : ℝ) (ell J : ℕ) :
    (normalizedResidual δ ell J).natDegree ≤ ell * (J + 1) := by
  exact (normalizeShift_natDegree_le δ
    ((denominator δ ell J).eval δ) (gridResidual δ ell J)).trans
      (gridResidual_natDegree_le δ ell J)

theorem normalizedError_degree_bound (δ : ℝ) (ell J : ℕ) :
    (normalizedError δ ell J).natDegree ≤ 4 * ell * (J + 1) := by
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · calc
      (Polynomial.C δ * normalizedDenominator δ ell J ^ 2).natDegree ≤
          (normalizedDenominator δ ell J ^ 2).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ 2 * (normalizedDenominator δ ell J).natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ 2 * (2 * ell * (J + 1)) :=
        Nat.mul_le_mul_left 2
          (normalizedDenominator_degree_bound δ ell J)
      _ = 4 * ell * (J + 1) := by ring
  · calc
      (normalizedResidual δ ell J ^ 2).natDegree ≤
          2 * (normalizedResidual δ ell J).natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ 2 * (ell * (J + 1)) :=
        Nat.mul_le_mul_left 2 (normalizedResidual_degree_bound δ ell J)
      _ ≤ 4 * (ell * (J + 1)) :=
        Nat.mul_le_mul_right (ell * (J + 1)) (by omega)
      _ = 4 * ell * (J + 1) := by ring


end RationalSquareRoot
end GeneralArchimedean
end OptimalConvergenceRates

end
