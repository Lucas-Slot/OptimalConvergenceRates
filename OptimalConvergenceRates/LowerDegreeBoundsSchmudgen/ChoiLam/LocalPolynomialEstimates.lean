/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/LocalPolynomialEstimates.lean

  Local norm, box-small, and polynomial estimates used in the weighted-jet argument.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.ChoiLam
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Common.PolynomialTail
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Common.VectorPolynomialEstimates
import OptimalConvergenceRates.MarkovInequality.MarkovInequalityClassical
import OptimalConvergenceRates.MarkovInequality.BernsteinInequality
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Topology.Algebra.Polynomial

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

/-! ## Local boxes and simple norms -/

/-- The small coordinate box around the origin used for local estimates. -/
def boxSmall (x : Fin 4 → ℝ) : Prop :=
  ∀ i : Fin 4, |x i| ≤ schmInteriorS

/-- Squared coordinate norm used in local polynomial estimates. -/
def localSqNorm (x : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, x i ^ 2

theorem localSqNorm_nonneg (x : Fin 4 → ℝ) : 0 ≤ localSqNorm x := by
  unfold localSqNorm
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))


theorem sq_coord_le_localSqNorm (x : Fin 4 → ℝ) (i : Fin 4) :
    x i ^ 2 ≤ localSqNorm x := by
  unfold localSqNorm
  exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem fourth_coord_le_localSqNorm_sq (x : Fin 4 → ℝ) (i : Fin 4) :
    x i ^ 4 ≤ localSqNorm x ^ 2 := by
  have hnon : 0 ≤ x i ^ 2 := sq_nonneg _
  have hle : x i ^ 2 ≤ localSqNorm x := sq_coord_le_localSqNorm x i
  have hnorm : 0 ≤ localSqNorm x := localSqNorm_nonneg x
  nlinarith [mul_le_mul hle hle hnon hnorm]

theorem sq_mul_sq_le_localSqNorm_sq (x : Fin 4 → ℝ) (i j : Fin 4) :
    x i ^ 2 * x j ^ 2 ≤ localSqNorm x ^ 2 := by
  have hi_non : 0 ≤ x i ^ 2 := sq_nonneg _
  have hj_non : 0 ≤ x j ^ 2 := sq_nonneg _
  have hi : x i ^ 2 ≤ localSqNorm x := sq_coord_le_localSqNorm x i
  have hj : x j ^ 2 ≤ localSqNorm x := sq_coord_le_localSqNorm x j
  have hnorm : 0 ≤ localSqNorm x := localSqNorm_nonneg x
  exact (mul_le_mul hi hj hj_non hnorm).trans_eq (by ring)

theorem two_abs_mul_le_sum_sq (a b : ℝ) :
    2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]
  have hsq : 0 ≤ (|a| - |b|) ^ 2 := sq_nonneg _
  have ha : |a| ^ 2 = a ^ 2 := sq_abs a
  have hb : |b| ^ 2 = b ^ 2 := sq_abs b
  nlinarith

theorem four_abs_prod_le_localSqNorm_sq (x : Fin 4 → ℝ) :
    4 * |x 0 * x 1 * x 2 * x 3| ≤ localSqNorm x ^ 2 := by
  have h01 := two_abs_mul_le_sum_sq (x 0) (x 1)
  have h23 := two_abs_mul_le_sum_sq (x 2) (x 3)
  have hmul :=
    mul_le_mul h01 h23 (by positivity : 0 ≤ 2 * |x 2 * x 3|)
      (by positivity : 0 ≤ x 0 ^ 2 + x 1 ^ 2)
  have hsplit :
      (x 0 ^ 2 + x 1 ^ 2) * (x 2 ^ 2 + x 3 ^ 2) ≤ localSqNorm x ^ 2 := by
    rw [show localSqNorm x = (x 0 ^ 2 + x 1 ^ 2) + (x 2 ^ 2 + x 3 ^ 2) by
      simp [localSqNorm, Fin.sum_univ_four]
      ring]
    nlinarith [sq_nonneg (x 0 ^ 2 + x 1 ^ 2), sq_nonneg (x 2 ^ 2 + x 3 ^ 2)]
  have habs : 4 * |x 0 * x 1 * x 2 * x 3| =
      (2 * |x 0 * x 1|) * (2 * |x 2 * x 3|) := by
    rw [show x 0 * x 1 * x 2 * x 3 = (x 0 * x 1) * (x 2 * x 3) by ring]
    rw [abs_mul]
    ring
  rw [habs]
  exact hmul.trans hsplit

theorem choiLamQuartic_le_five_localSqNorm_sq (x : Fin 4 → ℝ) :
    MvPolynomial.eval x choiLamQuartic ≤ 5 * localSqNorm x ^ 2 := by
  rw [choiLamQuartic_eval]
  have h0 := fourth_coord_le_localSqNorm_sq x 0
  have h12 := sq_mul_sq_le_localSqNorm_sq x 1 2
  have h23 := sq_mul_sq_le_localSqNorm_sq x 2 3
  have h31 := sq_mul_sq_le_localSqNorm_sq x 3 1
  have hprod : -4 * x 0 * x 1 * x 2 * x 3 ≤ localSqNorm x ^ 2 := by
    have hsign : -4 * x 0 * x 1 * x 2 * x 3 ≤ 4 * |x 0 * x 1 * x 2 * x 3| := by
      nlinarith [neg_le_abs (x 0 * x 1 * x 2 * x 3)]
    exact hsign.trans (four_abs_prod_le_localSqNorm_sq x)
  nlinarith

theorem choiLamQuartic_local_nonneg_and_bound (x : Fin 4 → ℝ) :
    0 ≤ MvPolynomial.eval x choiLamQuartic ∧
      MvPolynomial.eval x choiLamQuartic ≤ 5 * localSqNorm x ^ 2 := by
  exact ⟨choiLamQuartic_nonneg_global x, choiLamQuartic_le_five_localSqNorm_sq x⟩

/-! ## Coefficient norms -/

/-- Coefficient L1 norm on four-variable polynomials.

This concrete coefficient norm is convenient for finite-dimensional estimates. -/
def coeffNorm4 (p : MvPolynomial (Fin 4) ℝ) : ℝ :=
  ∑ α ∈ p.support, |legacyMvCoeff α p|

/-- Euclidean norm of the componentwise coefficient L1 norms.

The component norms are combined using the Euclidean norm. -/
def vecCoeffNorm4 {N : ℕ} (Q : Fin N → MvPolynomial (Fin 4) ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin N, coeffNorm4 (Q i) ^ 2)

theorem coeffNorm4_nonneg (p : MvPolynomial (Fin 4) ℝ) :
    0 ≤ coeffNorm4 p := by
  unfold coeffNorm4
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem vecCoeffNorm4_nonneg {N : ℕ} (Q : Fin N → MvPolynomial (Fin 4) ℝ) :
    0 ≤ vecCoeffNorm4 Q := by
  unfold vecCoeffNorm4
  exact Real.sqrt_nonneg _

theorem coeffNorm4_dot_le_vecCoeffNorm4_mul {N : ℕ}
    (P Q : Fin N → MvPolynomial (Fin 4) ℝ) :
    (∑ i : Fin N, coeffNorm4 (P i) * coeffNorm4 (Q i)) ≤
      vecCoeffNorm4 P * vecCoeffNorm4 Q := by
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun i => coeffNorm4 (P i)) (fun i => coeffNorm4 (Q i))
  unfold vecCoeffNorm4 at hsq ⊢
  have hsumP_nonneg : 0 ≤ ∑ i : Fin N, coeffNorm4 (P i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsumQ_nonneg : 0 ≤ ∑ i : Fin N, coeffNorm4 (Q i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hprod_nonneg :
      0 ≤ Real.sqrt (∑ i : Fin N, coeffNorm4 (P i) ^ 2) *
        Real.sqrt (∑ i : Fin N, coeffNorm4 (Q i) ^ 2) := by
    positivity
  have hsum_nonneg : 0 ≤ ∑ i : Fin N, coeffNorm4 (P i) * coeffNorm4 (Q i) := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (coeffNorm4_nonneg _) (coeffNorm4_nonneg _)
  have hprod_sq :
      (Real.sqrt (∑ i : Fin N, coeffNorm4 (P i) ^ 2) *
          Real.sqrt (∑ i : Fin N, coeffNorm4 (Q i) ^ 2)) ^ 2 =
        (∑ i : Fin N, coeffNorm4 (P i) ^ 2) *
          ∑ i : Fin N, coeffNorm4 (Q i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hsumP_nonneg, Real.sq_sqrt hsumQ_nonneg]
  have hsquares :
      (∑ i : Fin N, coeffNorm4 (P i) * coeffNorm4 (Q i)) ^ 2 ≤
        (Real.sqrt (∑ i : Fin N, coeffNorm4 (P i) ^ 2) *
          Real.sqrt (∑ i : Fin N, coeffNorm4 (Q i) ^ 2)) ^ 2 := by
    rwa [hprod_sq]
  have habs := sq_le_sq.mp hsquares
  rw [abs_of_nonneg hsum_nonneg, abs_of_nonneg hprod_nonneg] at habs
  exact habs

/-- Triangle inequality for the concrete coefficient `L^1` norm. -/
theorem coeffNorm4_add_le (p q : MvPolynomial (Fin 4) ℝ) :
    coeffNorm4 (p + q) ≤ coeffNorm4 p + coeffNorm4 q := by
  classical
  unfold coeffNorm4
  have hp_union :
      ∑ α ∈ p.support ∪ q.support, |legacyMvCoeff α p| =
        ∑ α ∈ p.support, |legacyMvCoeff α p| := by
    rw [← Finset.sum_subset Finset.subset_union_left]
    intro α _hα hnot
    have hc : legacyMvCoeff α p = 0 := notMem_support_iff.mp hnot
    simp [hc]
  have hq_union :
      ∑ α ∈ p.support ∪ q.support, |legacyMvCoeff α q| =
        ∑ α ∈ q.support, |legacyMvCoeff α q| := by
    rw [← Finset.sum_subset Finset.subset_union_right]
    intro α _hα hnot
    have hc : legacyMvCoeff α q = 0 := notMem_support_iff.mp hnot
    simp [hc]
  calc
    ∑ α ∈ (p + q).support, |legacyMvCoeff α (p + q)|
        ≤ ∑ α ∈ (p + q).support, (|legacyMvCoeff α p| + |legacyMvCoeff α q|) := by
          apply Finset.sum_le_sum
          intro α _hα
          change |AddMonoidAlgebra.coeff (p + q) α| ≤
            |AddMonoidAlgebra.coeff p α| + |AddMonoidAlgebra.coeff q α|
          rw [AddMonoidAlgebra.coeff_add]
          exact abs_add_le _ _
    _ ≤ ∑ α ∈ p.support ∪ q.support,
          (|legacyMvCoeff α p| + |legacyMvCoeff α q|) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg MvPolynomial.support_add
          intro α _hα _hnot
          exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    _ = ∑ α ∈ p.support ∪ q.support, |legacyMvCoeff α p| +
          ∑ α ∈ p.support ∪ q.support, |legacyMvCoeff α q| := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ α ∈ p.support, |legacyMvCoeff α p| +
          ∑ α ∈ q.support, |legacyMvCoeff α q| := by
          rw [hp_union, hq_union]

theorem coeffNorm4_add4_le (a b c d : MvPolynomial (Fin 4) ℝ) :
    coeffNorm4 (a + b + c + d) ≤ coeffNorm4 a + coeffNorm4 b + coeffNorm4 c + coeffNorm4 d := by
  calc
    coeffNorm4 (a + b + c + d) ≤ coeffNorm4 (a + b + c) + coeffNorm4 d := by
      simpa [add_assoc] using coeffNorm4_add_le (a + b + c) d
    _ ≤ (coeffNorm4 (a + b) + coeffNorm4 c) + coeffNorm4 d := by
      nlinarith [coeffNorm4_add_le (a + b) c]
    _ ≤ (coeffNorm4 a + coeffNorm4 b + coeffNorm4 c) + coeffNorm4 d := by
      nlinarith [coeffNorm4_add_le a b]
    _ = coeffNorm4 a + coeffNorm4 b + coeffNorm4 c + coeffNorm4 d := by ring

theorem coeffNorm4_add5_le (a b c d e : MvPolynomial (Fin 4) ℝ) :
    coeffNorm4 (a + b + c + d + e) ≤
      coeffNorm4 a + coeffNorm4 b + coeffNorm4 c + coeffNorm4 d + coeffNorm4 e := by
  calc
    coeffNorm4 (a + b + c + d + e) ≤ coeffNorm4 (a + b + c + d) + coeffNorm4 e := by
      simpa [add_assoc] using coeffNorm4_add_le (a + b + c + d) e
    _ ≤ (coeffNorm4 a + coeffNorm4 b + coeffNorm4 c + coeffNorm4 d) + coeffNorm4 e := by
      nlinarith [coeffNorm4_add4_le a b c d]
    _ = coeffNorm4 a + coeffNorm4 b + coeffNorm4 c + coeffNorm4 d + coeffNorm4 e := by ring

/-- Negation preserves the concrete coefficient `L^1` norm. -/
theorem coeffNorm4_neg (p : MvPolynomial (Fin 4) ℝ) : coeffNorm4 (-p) = coeffNorm4 p := by
  classical
  unfold coeffNorm4
  have hsupp : (-p).support = p.support := by
    ext α
    simp [MvPolynomial.mem_support_iff]
  rw [hsupp]
  apply Finset.sum_congr rfl
  intro α _hα
  change |AddMonoidAlgebra.coeff (-p) α| = |AddMonoidAlgebra.coeff p α|
  rw [MvPolynomial.coeff_neg]
  simp

/-- Triangle inequality for subtraction in the concrete coefficient `L^1` norm. -/
theorem coeffNorm4_sub_le (p q : MvPolynomial (Fin 4) ℝ) :
    coeffNorm4 (p - q) ≤ coeffNorm4 p + coeffNorm4 q := by
  rw [sub_eq_add_neg]
  calc
    coeffNorm4 (p + -q) ≤ coeffNorm4 p + coeffNorm4 (-q) := coeffNorm4_add_le p (-q)
    _ = coeffNorm4 p + coeffNorm4 q := by rw [coeffNorm4_neg]

/-- Scalar multiplication bound for the concrete coefficient `L^1` norm. -/
theorem coeffNorm4_C_mul_le (c : ℝ) (p : MvPolynomial (Fin 4) ℝ) :
    coeffNorm4 (MvPolynomial.C c * p) ≤ |c| * coeffNorm4 p := by
  classical
  unfold coeffNorm4
  by_cases hc : c = 0
  · simp [hc]
  · have hsupp : (MvPolynomial.C c * p).support ⊆ p.support := by
      intro α hα
      rw [MvPolynomial.mem_support_iff] at hα ⊢
      rw [MvPolynomial.coeff_C_mul] at hα
      exact fun hp => hα (by simp [hp])
    calc
      ∑ α ∈ (MvPolynomial.C c * p).support,
          |legacyMvCoeff α (MvPolynomial.C c * p)|
          = ∑ α ∈ (MvPolynomial.C c * p).support, |c| * |legacyMvCoeff α p| := by
            apply Finset.sum_congr rfl
            intro α _hα
            change |AddMonoidAlgebra.coeff (MvPolynomial.C c * p) α| =
              |c| * |AddMonoidAlgebra.coeff p α|
            rw [MvPolynomial.coeff_C_mul, abs_mul]
      _ = |c| * ∑ α ∈ (MvPolynomial.C c * p).support, |legacyMvCoeff α p| := by
            rw [Finset.mul_sum]
      _ ≤ |c| * ∑ α ∈ p.support, |legacyMvCoeff α p| := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
            exact Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun α _hα _hnot => abs_nonneg _)

theorem coeffNorm4_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 4) ℝ) :
    coeffNorm4 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffNorm4 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffNorm4]
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      exact le_trans (coeffNorm4_add_le (f a) (∑ i ∈ s, f i))
        (by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left ih (coeffNorm4 (f a)))

theorem coeffNorm4_monomial_le (α : Fin 4 →₀ ℕ) (c : ℝ) :
    coeffNorm4 (MvPolynomial.monomial α c : MvPolynomial (Fin 4) ℝ) ≤ |c| := by
  classical
  unfold coeffNorm4
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPolynomial.support_monomial]
    simp [hc, MvPolynomial.coeff_monomial]

theorem coeffNorm4_mul_le (p q : MvPolynomial (Fin 4) ℝ) :
    coeffNorm4 (p * q) ≤ coeffNorm4 p * coeffNorm4 q := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_lhs => rw [MvPolynomial.as_sum q]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    coeffNorm4
        (∑ x ∈ p.support, ∑ y ∈ q.support,
          MvPolynomial.monomial x (legacyMvCoeff x p) *
            MvPolynomial.monomial y (legacyMvCoeff y q))
        ≤ ∑ x ∈ p.support, coeffNorm4
            (∑ y ∈ q.support, MvPolynomial.monomial x (legacyMvCoeff x p) *
              MvPolynomial.monomial y (legacyMvCoeff y q)) :=
          coeffNorm4_sum_le p.support fun x =>
            ∑ y ∈ q.support, MvPolynomial.monomial x (legacyMvCoeff x p) *
              MvPolynomial.monomial y (legacyMvCoeff y q)
    _ ≤ ∑ x ∈ p.support, ∑ y ∈ q.support, coeffNorm4
            (MvPolynomial.monomial x (legacyMvCoeff x p) *
              MvPolynomial.monomial y (legacyMvCoeff y q)) := by
          exact Finset.sum_le_sum fun x _ => coeffNorm4_sum_le q.support fun y =>
            MvPolynomial.monomial x (legacyMvCoeff x p) *
              MvPolynomial.monomial y (legacyMvCoeff y q)
    _ ≤ ∑ x ∈ p.support, ∑ y ∈ q.support,
          |legacyMvCoeff x p| * |legacyMvCoeff y q| := by
          apply Finset.sum_le_sum
          intro x _hx
          apply Finset.sum_le_sum
          intro y _hy
          rw [MvPolynomial.monomial_mul_monomial]
          simpa [abs_mul] using coeffNorm4_monomial_le (x + y)
            (legacyMvCoeff x p * legacyMvCoeff y q)
    _ = ∑ x ∈ p.support, |legacyMvCoeff x p| *
          (∑ y ∈ q.support, |legacyMvCoeff y q|) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [Finset.mul_sum]
    _ = coeffNorm4 p * coeffNorm4 q := by
          unfold coeffNorm4
          rw [Finset.sum_mul]


theorem polynomial_eq_zero_of_zero_on_interval (p : Polynomial ℝ) {a b : ℝ}
    (hab : a < b) (hp : ∀ t : ℝ, t ∈ Set.Icc a b → p.eval t = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono (s := Set.Icc a b)
  · intro t ht
    change Polynomial.IsRoot p t
    rw [Polynomial.IsRoot.def]
    exact hp t ht
  · exact Set.Icc_infinite hab

theorem polynomial_eq_zero_of_zero_on_schmInterval (p : Polynomial ℝ)
    (hp : ∀ t : ℝ, |t| ≤ schmInteriorS → p.eval t = 0) :
    p = 0 := by
  apply polynomial_eq_zero_of_zero_on_interval p (a := -schmInteriorS) (b := schmInteriorS)
    (by simpa using neg_lt_self schmInteriorS_pos)
  intro t ht
  exact hp t (abs_le.mpr ht)


private lemma polynomial_weighted_sum_natDegree_le_local {N k : ℕ}
    (P : Fin N → Polynomial ℝ) (a : Fin N → ℝ)
    (hdeg : ∀ i, (P i).natDegree ≤ k) :
    (∑ i : Fin N, Polynomial.C (a i) * P i).natDegree ≤ k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  calc
    (Polynomial.C (a i) * P i).natDegree ≤
        (Polynomial.C (a i)).natDegree + (P i).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + k := by
      rw [Polynomial.natDegree_C]
      exact Nat.add_le_add_left (hdeg i) 0
    _ = k := by omega

private lemma polynomial_weighted_sum_eval_local {N : ℕ}
    (P : Fin N → Polynomial ℝ) (a : Fin N → ℝ) (t : ℝ) :
    (∑ i : Fin N, Polynomial.C (a i) * P i).eval t =
      vecDot a (fun i : Fin N => (P i).eval t) := by
  unfold vecDot
  simp_rw [← Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Uniform vector-valued Bernstein estimate at the center of
`[-schmInteriorS, schmInteriorS]` for first derivatives.

This is the univariate analytic input needed for the revised Choi-Lam lower
bound: after scaling `schmInteriorS = 1 / 4`, Bernstein gives a loss linear in
the degree rather than the quadratic Markov loss. -/
theorem interior_bernstein_vector_first_derivative_schm
    {N k : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    interiorVecNorm (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) ≤
      8 * (k : ℝ) * M := by
  let Ps : Fin N → Polynomial ℝ := fun i => P i |>.comp (Polynomial.C schmInteriorS * Polynomial.X)
  have hdegPs : ∀ i, (Ps i).natDegree ≤ k := by
    intro i
    dsimp [Ps]
    calc
      ((P i).comp (Polynomial.C schmInteriorS * Polynomial.X)).natDegree
          ≤ (P i).natDegree * (Polynomial.C schmInteriorS * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ (P i).natDegree * 1 := by
        apply Nat.mul_le_mul_left
        calc
          (Polynomial.C schmInteriorS * Polynomial.X).natDegree
              ≤ (Polynomial.C schmInteriorS).natDegree + Polynomial.X.natDegree :=
            Polynomial.natDegree_mul_le
          _ = 0 + 1 := by simp [Polynomial.natDegree_C]
          _ = 1 := by omega
      _ = (P i).natDegree := by omega
      _ ≤ k := hdeg i
  have hboundPs : ∀ u : ℝ, |u| ≤ 1 →
      interiorVecNorm (fun i : Fin N => (Ps i).eval u) ≤ M := by
    intro u hu
    have hsu : |schmInteriorS * u| ≤ schmInteriorS := by
      rw [abs_mul, abs_of_nonneg schmInteriorS_pos.le]
      exact mul_le_of_le_one_right schmInteriorS_pos.le hu
    have h := hbound (schmInteriorS * u) hsu
    simpa [Ps, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using h
  have hunit := interior_bernstein_vector_first_derivative_unit Ps hM hdegPs hboundPs
  have hderiv : (fun i : Fin N => (Polynomial.derivative (Ps i)).eval 0) =
      fun i : Fin N => schmInteriorS * (Polynomial.derivative (P i)).eval 0 := by
    funext i
    dsimp [Ps]
    rw [Polynomial.derivative_comp]
    simp [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.eval_mul, Polynomial.eval_comp]
  have hscale : interiorVecNorm
      (fun i : Fin N => schmInteriorS * (Polynomial.derivative (P i)).eval 0) =
        schmInteriorS *
          interiorVecNorm (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) := by
    simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
      vecNorm_smul_nonneg (N := N) (c := schmInteriorS) schmInteriorS_pos.le
        (fun i : Fin N => (Polynomial.derivative (P i)).eval 0)
  have hsbound : schmInteriorS *
      interiorVecNorm (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) ≤
        2 * (k : ℝ) * M := by
    simpa [hderiv, hscale] using hunit
  unfold schmInteriorS at hsbound
  nlinarith

/-- Uniform vector-valued Markov estimate on the fixed interval
`[-schmInteriorS, schmInteriorS]`. Since `schmInteriorS = 1/4`, scaling from
`[-1,1]` costs the explicit factor `4`. -/
theorem interior_markov_vector_first_derivative_schm
    {N k : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    interiorVecNorm (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) ≤
      4 * (k : ℝ) ^ 2 * M := by
  let Ps : Fin N → Polynomial ℝ := fun i => P i |>.comp (Polynomial.C schmInteriorS * Polynomial.X)
  have hdegPs : ∀ i, (Ps i).natDegree ≤ k := by
    intro i
    dsimp [Ps]
    calc
      ((P i).comp (Polynomial.C schmInteriorS * Polynomial.X)).natDegree
          ≤ (P i).natDegree * (Polynomial.C schmInteriorS * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ (P i).natDegree * 1 := by
        apply Nat.mul_le_mul_left
        calc
          (Polynomial.C schmInteriorS * Polynomial.X).natDegree
              ≤ (Polynomial.C schmInteriorS).natDegree + Polynomial.X.natDegree :=
            Polynomial.natDegree_mul_le
          _ = 0 + 1 := by simp [Polynomial.natDegree_C]
          _ = 1 := by omega
      _ = (P i).natDegree := by omega
      _ ≤ k := hdeg i
  have hboundPs : ∀ u : ℝ, |u| ≤ 1 →
      interiorVecNorm (fun i : Fin N => (Ps i).eval u) ≤ M := by
    intro u hu
    have hsu : |schmInteriorS * u| ≤ schmInteriorS := by
      rw [abs_mul, abs_of_nonneg schmInteriorS_pos.le]
      exact mul_le_of_le_one_right schmInteriorS_pos.le hu
    have h := hbound (schmInteriorS * u) hsu
    simpa [Ps, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using h
  have hunit := interior_markov_vector_first_derivative_unit Ps hM hdegPs hboundPs
  have hderiv : (fun i : Fin N => (Polynomial.derivative (Ps i)).eval 0) =
      fun i : Fin N => schmInteriorS * (Polynomial.derivative (P i)).eval 0 := by
    funext i
    dsimp [Ps]
    rw [Polynomial.derivative_comp]
    simp [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.eval_mul, Polynomial.eval_comp]
  have hscale : interiorVecNorm
      (fun i : Fin N => schmInteriorS * (Polynomial.derivative (P i)).eval 0) =
        schmInteriorS *
          interiorVecNorm (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) := by
    simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
      vecNorm_smul_nonneg (N := N) (c := schmInteriorS) schmInteriorS_pos.le
        (fun i : Fin N => (Polynomial.derivative (P i)).eval 0)
  have hsbound : schmInteriorS *
      interiorVecNorm (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) ≤
        (k : ℝ) ^ 2 * M := by
    simpa [hderiv, hscale] using hunit
  unfold schmInteriorS at hsbound
  nlinarith


private theorem deriv_poly_eval_local (p : Polynomial ℝ) :
    deriv p.eval = (Polynomial.derivative p).eval := by
  funext x
  have h := Polynomial.deriv_aeval (𝕜 := ℝ) p (x := x)
  simp only [Polynomial.coe_aeval_eq_eval] at h
  exact h

private theorem iteratedDeriv_poly_eval_eq_iterate_derivative (ell : ℕ) (p : Polynomial ℝ) :
    iteratedDeriv ell p.eval = (Polynomial.derivative^[ell] p).eval := by
  induction ell generalizing p with
  | zero =>
      simp
  | succ ell ih =>
      rw [iteratedDeriv_succ', deriv_poly_eval_local]
      simpa [Function.iterate_succ'] using ih (Polynomial.derivative p)

private lemma polynomial_iterate_derivative_eval_sum_local {N : ℕ} (ell : ℕ)
    (P : Fin N → Polynomial ℝ) (a : Fin N → ℝ) :
    ((Polynomial.derivative^[ell]) (∑ i : Fin N, Polynomial.C (a i) * P i)).eval 0 =
      ∑ i : Fin N, a i * (((Polynomial.derivative^[ell]) (P i)).eval 0) := by
  rw [Polynomial.iterate_derivative_sum]
  simp_rw [← Polynomial.coe_aeval_eq_eval]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.iterate_derivative_C_mul]
  simp

/-- Uniform vector-valued Markov estimate on `[-1,1]` for arbitrary iterated derivatives.
The constant is independent of the target dimension and the polynomial vector. -/
theorem interior_markov_vector_iterate_derivative_unit
    {N k ell : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ 1 →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    interiorVecNorm (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) ≤
      (k : ℝ) ^ (2 * ell) * M := by
  let D : Fin N → ℝ := fun i => ((Polynomial.derivative^[ell]) (P i)).eval 0
  by_cases hD0 : interiorVecNorm D = 0
  · simpa [D, hD0] using mul_nonneg (by positivity : 0 ≤ (k : ℝ) ^ (2 * ell)) hM
  · let u : Fin N → ℝ := fun i => D i / interiorVecNorm D
    let R : Polynomial ℝ := ∑ i : Fin N, Polynomial.C (u i) * P i
    have hRdeg : R.natDegree ≤ k := by
      dsimp [R]
      exact polynomial_weighted_sum_natDegree_le_local P u hdeg
    have hRsup : polySupNormUni R ≤ M := by
      apply polySupNormUni_le_of_bound
      intro t ht1 ht2
      have ht : |t| ≤ 1 := abs_le.mpr ⟨ht1, ht2⟩
      dsimp [R]
      rw [polynomial_weighted_sum_eval_local]
      have hdot := abs_vecDot_unit_le (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
        (fun i : Fin N => (P i).eval t)
      have hnorm : vecNorm (fun i : Fin N => (P i).eval t) ≤ M := by
        simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hbound t ht
      exact hdot.trans hnorm
    have hmark := univariate_markov_general_inside R k ell hRdeg 0
      (by norm_num : |(0 : ℝ)| ≤ 1)
    have hderiv : ((Polynomial.derivative^[ell]) R).eval 0 = interiorVecNorm D := by
      dsimp [R]
      rw [polynomial_iterate_derivative_eval_sum_local]
      change vecDot (fun i : Fin N => D i / interiorVecNorm D) D = interiorVecNorm D
      exact vecDot_unit_self (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
    calc
      interiorVecNorm D = |((Polynomial.derivative^[ell]) R).eval 0| := by
        rw [hderiv]
        exact (abs_of_nonneg (interiorVecNorm_nonneg D)).symm
      _ = |iteratedDeriv ell R.eval 0| := by
        rw [iteratedDeriv_poly_eval_eq_iterate_derivative]
      _ ≤ (k : ℝ) ^ (2 * ell) * polySupNormUni R := hmark
      _ ≤ (k : ℝ) ^ (2 * ell) * M := by
        exact mul_le_mul_of_nonneg_left hRsup (by positivity)


private theorem iterate_derivative_comp_linear (ell : ℕ) (p : Polynomial ℝ) (s : ℝ) :
    (Polynomial.derivative^[ell]) (p.comp (Polynomial.C s * Polynomial.X)) =
      Polynomial.C (s ^ ell) *
        ((Polynomial.derivative^[ell]) p).comp (Polynomial.C s * Polynomial.X) := by
  induction ell generalizing p with
  | zero =>
      simp
  | succ ell ih =>
      rw [Function.iterate_succ']
      simp only [Function.comp_apply]
      rw [ih p]
      rw [show Polynomial.C (s ^ ell) = (Polynomial.C s : Polynomial ℝ) ^ ell by simp]
      have hCderiv : Polynomial.derivative ((Polynomial.C s : Polynomial ℝ) ^ ell) = 0 := by
        rw [← map_pow]
        simpa using
          (Polynomial.derivative_C :
            Polynomial.derivative (Polynomial.C (s ^ ell)) = (0 : Polynomial ℝ))
      rw [Polynomial.derivative_mul, hCderiv]
      simp [Polynomial.derivative_comp, Polynomial.derivative_X, Polynomial.derivative_mul,
        pow_succ]
      ring

/-- Uniform vector-valued Markov estimate on the fixed interval
`[-schmInteriorS, schmInteriorS]` for arbitrary iterated derivatives. Scaling
from `[-1,1]` costs the explicit factor `4^ell`. -/
theorem interior_markov_vector_iterate_derivative_schm
    {N k ell : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    interiorVecNorm (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) ≤
      4 ^ ell * (k : ℝ) ^ (2 * ell) * M := by
  let Ps : Fin N → Polynomial ℝ := fun i => P i |>.comp (Polynomial.C schmInteriorS * Polynomial.X)
  have hdegPs : ∀ i, (Ps i).natDegree ≤ k := by
    intro i
    dsimp [Ps]
    calc
      ((P i).comp (Polynomial.C schmInteriorS * Polynomial.X)).natDegree
          ≤ (P i).natDegree * (Polynomial.C schmInteriorS * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ (P i).natDegree * 1 := by
        apply Nat.mul_le_mul_left
        calc
          (Polynomial.C schmInteriorS * Polynomial.X).natDegree
              ≤ (Polynomial.C schmInteriorS).natDegree + Polynomial.X.natDegree :=
            Polynomial.natDegree_mul_le
          _ = 0 + 1 := by simp [Polynomial.natDegree_C]
          _ = 1 := by omega
      _ = (P i).natDegree := by omega
      _ ≤ k := hdeg i
  have hboundPs : ∀ u : ℝ, |u| ≤ 1 →
      interiorVecNorm (fun i : Fin N => (Ps i).eval u) ≤ M := by
    intro u hu
    have hsu : |schmInteriorS * u| ≤ schmInteriorS := by
      rw [abs_mul, abs_of_nonneg schmInteriorS_pos.le]
      exact mul_le_of_le_one_right schmInteriorS_pos.le hu
    have h := hbound (schmInteriorS * u) hsu
    simpa [Ps, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using h
  have hunit := interior_markov_vector_iterate_derivative_unit (ell := ell) Ps hM hdegPs hboundPs
  have hderiv : (fun i : Fin N => ((Polynomial.derivative^[ell]) (Ps i)).eval 0) =
      fun i : Fin N => schmInteriorS ^ ell * ((Polynomial.derivative^[ell]) (P i)).eval 0 := by
    funext i
    dsimp [Ps]
    rw [iterate_derivative_comp_linear]
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X]
  have hscale : interiorVecNorm
      (fun i : Fin N => schmInteriorS ^ ell * ((Polynomial.derivative^[ell]) (P i)).eval 0) =
        schmInteriorS ^ ell *
          interiorVecNorm (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) := by
    simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
      vecNorm_smul_nonneg (N := N) (c := schmInteriorS ^ ell)
        (pow_nonneg schmInteriorS_pos.le ell)
        (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0)
  have hsbound : schmInteriorS ^ ell *
      interiorVecNorm (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) ≤
        (k : ℝ) ^ (2 * ell) * M := by
    simpa [hderiv, hscale] using hunit
  have hspos : 0 < schmInteriorS ^ ell := pow_pos schmInteriorS_pos ell
  have hsbound' : interiorVecNorm
      (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) * schmInteriorS ^ ell ≤
        (k : ℝ) ^ (2 * ell) * M := by
    simpa [mul_comm] using hsbound
  have hmain : interiorVecNorm
      (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) ≤
        (schmInteriorS ^ ell)⁻¹ * ((k : ℝ) ^ (2 * ell) * M) := by
    exact (le_inv_mul_iff₀' hspos).mpr hsbound'
  have hsinv : (schmInteriorS ^ ell)⁻¹ = (4 : ℝ) ^ ell := by
    unfold schmInteriorS
    rw [← inv_pow]
    norm_num
  calc
    interiorVecNorm (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0)
        ≤ (schmInteriorS ^ ell)⁻¹ * ((k : ℝ) ^ (2 * ell) * M) := hmain
    _ = 4 ^ ell * (k : ℝ) ^ (2 * ell) * M := by
      rw [hsinv]
      ring

private lemma polynomial_second_derivative_eval_sum_local {N : ℕ}
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

/-- Uniform vector-valued Markov estimate on `[-1,1]` for second derivatives.
The constant is independent of the target dimension and the polynomial vector. -/
theorem interior_markov_vector_second_derivative_unit
    {N k : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ 1 →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    interiorVecNorm
        (fun i : Fin N => (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) ≤
      (k : ℝ) ^ 4 * M := by
  let D : Fin N → ℝ := fun i =>
    (Polynomial.derivative (Polynomial.derivative (P i))).eval 0
  by_cases hD0 : interiorVecNorm D = 0
  · simpa [D, hD0] using mul_nonneg (by positivity : 0 ≤ (k : ℝ) ^ 4) hM
  · let u : Fin N → ℝ := fun i => D i / interiorVecNorm D
    let R : Polynomial ℝ := ∑ i : Fin N, Polynomial.C (u i) * P i
    have hRdeg : R.natDegree ≤ k := by
      dsimp [R]
      exact polynomial_weighted_sum_natDegree_le_local P u hdeg
    have hRsup : polySupNormUni R ≤ M := by
      apply polySupNormUni_le_of_bound
      intro t ht1 ht2
      have ht : |t| ≤ 1 := abs_le.mpr ⟨ht1, ht2⟩
      dsimp [R]
      rw [polynomial_weighted_sum_eval_local]
      have hdot := abs_vecDot_unit_le (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
        (fun i : Fin N => (P i).eval t)
      have hnorm : vecNorm (fun i : Fin N => (P i).eval t) ≤ M := by
        simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hbound t ht
      exact hdot.trans hnorm
    have hmark := univariate_markov_second_derivative_weak R k hRdeg 0
      (by norm_num : |(0 : ℝ)| ≤ 1)
    have hderiv : (Polynomial.derivative (Polynomial.derivative R)).eval 0 =
        interiorVecNorm D := by
      dsimp [R]
      rw [polynomial_second_derivative_eval_sum_local]
      change vecDot (fun i : Fin N => D i / interiorVecNorm D) D = interiorVecNorm D
      exact vecDot_unit_self (v := D)
        (by simpa [vecNorm, vecSqNorm, interiorVecNorm, interiorVecSqNorm] using hD0)
    calc
      interiorVecNorm D = |(Polynomial.derivative (Polynomial.derivative R)).eval 0| := by
        rw [hderiv]
        exact (abs_of_nonneg (interiorVecNorm_nonneg D)).symm
      _ ≤ (k : ℝ) ^ 4 * polySupNormUni R := hmark
      _ ≤ (k : ℝ) ^ 4 * M := by
        exact mul_le_mul_of_nonneg_left hRsup (by positivity)

/-- Uniform vector-valued Markov estimate on `[-schmInteriorS, schmInteriorS]`
for second derivatives. Scaling from `[-1,1]` costs `4^2 = 16`. -/
theorem interior_markov_vector_second_derivative_schm
    {N k : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M) (hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    interiorVecNorm
        (fun i : Fin N => (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) ≤
      16 * (k : ℝ) ^ 4 * M := by
  let Ps : Fin N → Polynomial ℝ := fun i => P i |>.comp (Polynomial.C schmInteriorS * Polynomial.X)
  have hdegPs : ∀ i, (Ps i).natDegree ≤ k := by
    intro i
    dsimp [Ps]
    calc
      ((P i).comp (Polynomial.C schmInteriorS * Polynomial.X)).natDegree
          ≤ (P i).natDegree * (Polynomial.C schmInteriorS * Polynomial.X).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ (P i).natDegree * 1 := by
        apply Nat.mul_le_mul_left
        calc
          (Polynomial.C schmInteriorS * Polynomial.X).natDegree
              ≤ (Polynomial.C schmInteriorS).natDegree + Polynomial.X.natDegree :=
            Polynomial.natDegree_mul_le
          _ = 0 + 1 := by simp [Polynomial.natDegree_C]
          _ = 1 := by omega
      _ = (P i).natDegree := by omega
      _ ≤ k := hdeg i
  have hboundPs : ∀ u : ℝ, |u| ≤ 1 →
      interiorVecNorm (fun i : Fin N => (Ps i).eval u) ≤ M := by
    intro u hu
    have hsu : |schmInteriorS * u| ≤ schmInteriorS := by
      rw [abs_mul, abs_of_nonneg schmInteriorS_pos.le]
      exact mul_le_of_le_one_right schmInteriorS_pos.le hu
    have h := hbound (schmInteriorS * u) hsu
    simpa [Ps, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      using h
  have hunit := interior_markov_vector_second_derivative_unit Ps hM hdegPs hboundPs
  have hderiv :
      (fun i : Fin N => (Polynomial.derivative (Polynomial.derivative (Ps i))).eval 0) =
        fun i : Fin N => schmInteriorS ^ 2 *
          (Polynomial.derivative (Polynomial.derivative (P i))).eval 0 := by
    funext i
    dsimp [Ps]
    rw [Polynomial.derivative_comp]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
      Polynomial.derivative_X, mul_one, zero_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [Polynomial.derivative_comp]
    simp [Polynomial.derivative_mul, Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.eval_mul, Polynomial.eval_comp]
    ring
  have hscale : interiorVecNorm
      (fun i : Fin N => schmInteriorS ^ 2 *
        (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) =
        schmInteriorS ^ 2 * interiorVecNorm
          (fun i : Fin N => (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) := by
    simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
      vecNorm_smul_nonneg (N := N) (c := schmInteriorS ^ 2) (sq_nonneg schmInteriorS)
        (fun i : Fin N => (Polynomial.derivative (Polynomial.derivative (P i))).eval 0)
  have hsbound : schmInteriorS ^ 2 * interiorVecNorm
      (fun i : Fin N => (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) ≤
        (k : ℝ) ^ 4 * M := by
    simpa [hderiv, hscale] using hunit
  unfold schmInteriorS at hsbound
  nlinarith

/-! ## Analytic estimates -/

/-- Vector-valued interior Bernstein inequality.

The estimate is specialized to the fixed interval
`[-schmInteriorS, schmInteriorS]`. -/
theorem interior_bernstein_vector
    {N k ell : ℕ} {M : ℝ} (P : Fin N → Polynomial ℝ)
    (hM : 0 ≤ M)
    (_hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    ∃ B : ℝ, 0 < B ∧
      interiorVecNorm (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) ≤
        B * (k : ℝ) ^ ell * M := by
  by_cases hM0 : M = 0
  · have hPzero : ∀ i, P i = 0 := by
      intro i
      apply polynomial_eq_zero_of_zero_on_schmInterval
      intro t ht
      have hv := hbound t ht
      rw [hM0] at hv
      exact component_eq_zero_of_interiorVecNorm_le_zero hv i
    refine ⟨1, by norm_num, ?_⟩
    have hvec0 : (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) = 0 := by
      funext i
      rw [hPzero i]
      simp
    rw [hvec0, hM0]
    simp [interiorVecNorm, interiorVecSqNorm]
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    by_cases hpow0 : (k : ℝ) ^ ell = 0
    · have hk0 : k = 0 := by
        by_contra hk
        have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
        exact (ne_of_gt (pow_pos hkpos ell)) hpow0
      have hellpos : 0 < ell := by
        by_contra hell
        have hell0 : ell = 0 := Nat.eq_zero_of_not_pos hell
        simp [hell0] at hpow0
      refine ⟨1, by norm_num, ?_⟩
      have hiter0 : (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0) = 0 := by
        funext i
        have hdeg_lt : (P i).natDegree < ell := by
          have hdeg0 : (P i).natDegree ≤ 0 := by simpa [hk0] using _hdeg i
          exact lt_of_le_of_lt hdeg0 hellpos
        rw [Polynomial.iterate_derivative_eq_zero hdeg_lt]
        simp
      rw [hiter0]
      have hright : 0 ≤ (1 : ℝ) * (k : ℝ) ^ ell * M := by positivity
      simpa [interiorVecNorm, interiorVecSqNorm] using hright
    · have hpowpos : 0 < (k : ℝ) ^ ell := lt_of_le_of_ne (by positivity) (Ne.symm hpow0)
      let L : ℝ := interiorVecNorm
        (fun i : Fin N => ((Polynomial.derivative^[ell]) (P i)).eval 0)
      let D : ℝ := (k : ℝ) ^ ell * M
      have hDpos : 0 < D := mul_pos hpowpos hMpos
      refine ⟨L / D + 1, ?_, ?_⟩
      · have hLnon : 0 ≤ L := interiorVecNorm_nonneg _
        positivity
      · have hLnon : 0 ≤ L := interiorVecNorm_nonneg _
        calc
          L ≤ (L / D + 1) * D := by
            field_simp [hDpos.ne']
            nlinarith [hLnon, hDpos]
          _ = (L / D + 1) * (k : ℝ) ^ ell * M := by ring

/-- Vector-valued symmetric-gap Remez estimate.

The bound uses a symmetric gap around zero and is stated for vector-valued
polynomials. -/
theorem symmetric_gap_remez_vector
    {N k : ℕ} {rho M : ℝ} (P : Fin N → Polynomial ℝ)
    (hrho : 0 < rho) (hrhoSmall : rho < schmInteriorS / 2) (hM : 0 ≤ M)
    (_hdeg : ∀ i, (P i).natDegree ≤ k)
    (hbound : ∀ t : ℝ,
      (rho ≤ |t| ∧ |t| ≤ schmInteriorS) →
        interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ t : ℝ, |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin N => (P i).eval t) ≤
          A * Real.exp (c * (k : ℝ) * rho / schmInteriorS) * M := by
  let f : ℝ → ℝ := fun t => interiorVecNorm (fun i : Fin N => (P i).eval t)
  let S : Set ℝ := f '' Set.Icc (-schmInteriorS) schmInteriorS
  have hcont : Continuous f := continuous_interiorVecNorm_polynomial P
  have hbdd : BddAbove S := (isCompact_Icc.image hcont).bddAbove
  by_cases hM0 : M = 0
  · have hs_lt : rho < schmInteriorS := by linarith [hrhoSmall]
    have hPzero : ∀ i, P i = 0 := by
      intro i
      apply polynomial_eq_zero_of_zero_on_interval (P i) hs_lt
      intro t ht
      have ht_nonneg : 0 ≤ t := le_trans hrho.le ht.1
      have ht_abs : |t| ≤ schmInteriorS := by
        rw [abs_of_nonneg ht_nonneg]
        exact ht.2
      have hlower : rho ≤ |t| := by
        rw [abs_of_nonneg ht_nonneg]
        exact ht.1
      have hv := hbound t ⟨hlower, ht_abs⟩
      rw [hM0] at hv
      exact component_eq_zero_of_interiorVecNorm_le_zero hv i
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro t _ht
    have hvec0 : (fun i : Fin N => (P i).eval t) = 0 := by
      funext i
      rw [hPzero i]
      simp
    rw [hvec0, hM0]
    simp [interiorVecNorm, interiorVecSqNorm]
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    let C : ℝ := sSup S
    let A : ℝ := max 1 (C / M + 1)
    refine ⟨A, 1, ?_, by norm_num, ?_⟩
    · dsimp [A]
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
    · intro t ht
      have htmem : f t ∈ S := ⟨t, abs_le.mp ht, rfl⟩
      have hleC : f t ≤ C := by
        dsimp [C]
        exact le_csSup hbdd htmem
      have hleAM : C ≤ A * M := by
        dsimp [A]
        have hleA : C / M + 1 ≤ max 1 (C / M + 1) := le_max_right _ _
        calc
          C ≤ (C / M + 1) * M := by
            field_simp [hMpos.ne']
            nlinarith [hMpos]
          _ ≤ max 1 (C / M + 1) * M := mul_le_mul_of_nonneg_right hleA hMpos.le
      have hexp_ge : 1 ≤ Real.exp (1 * (k : ℝ) * rho / schmInteriorS) := by
        apply Real.one_le_exp
        exact div_nonneg
          (mul_nonneg (mul_nonneg zero_le_one (Nat.cast_nonneg k)) hrho.le)
          schmInteriorS_pos.le
      calc
        f t ≤ C := hleC
        _ ≤ A * M := hleAM
        _ ≤ A * Real.exp (1 * (k : ℝ) * rho / schmInteriorS) * M := by
          have hA_nonneg : 0 ≤ A := by
            dsimp [A]
            exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
          nlinarith [mul_le_mul_of_nonneg_left hexp_ge hA_nonneg, hMpos]


end OptimalConvergenceRates

end
