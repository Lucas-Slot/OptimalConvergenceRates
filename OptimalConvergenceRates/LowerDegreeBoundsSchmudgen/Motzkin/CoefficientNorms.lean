/- Ternary coefficient norms for the Motzkin jet argument. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.Algebra
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.VectorPolynomialEstimates

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

def motzkinCoeffNorm (p : MvPolynomial (Fin 3) ℝ) : ℝ :=
  ∑ α ∈ p.support, |MvPolynomial.coeff α p|

/-- Euclidean norm of the componentwise coefficient L1 norms.

The component norms are combined using the Euclidean norm. -/
def motzkinVecCoeffNorm {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin N, motzkinCoeffNorm (Q i) ^ 2)

theorem motzkinCoeffNorm_nonneg (p : MvPolynomial (Fin 3) ℝ) :
    0 ≤ motzkinCoeffNorm p := by
  unfold motzkinCoeffNorm
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem motzkinVecCoeffNorm_nonneg {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    0 ≤ motzkinVecCoeffNorm Q := by
  unfold motzkinVecCoeffNorm
  exact Real.sqrt_nonneg _

theorem motzkinCoeffNorm_dot_le_motzkinVecCoeffNorm_mul {N : ℕ}
    (P Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    (∑ i : Fin N, motzkinCoeffNorm (P i) * motzkinCoeffNorm (Q i)) ≤
      motzkinVecCoeffNorm P * motzkinVecCoeffNorm Q := by
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun i => motzkinCoeffNorm (P i)) (fun i => motzkinCoeffNorm (Q i))
  unfold motzkinVecCoeffNorm at hsq ⊢
  have hsumP_nonneg : 0 ≤ ∑ i : Fin N, motzkinCoeffNorm (P i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsumQ_nonneg : 0 ≤ ∑ i : Fin N, motzkinCoeffNorm (Q i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hprod_nonneg :
      0 ≤ Real.sqrt (∑ i : Fin N, motzkinCoeffNorm (P i) ^ 2) *
        Real.sqrt (∑ i : Fin N, motzkinCoeffNorm (Q i) ^ 2) := by
    positivity
  have hsum_nonneg : 0 ≤ ∑ i : Fin N, motzkinCoeffNorm (P i) * motzkinCoeffNorm (Q i) := by
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (motzkinCoeffNorm_nonneg _) (motzkinCoeffNorm_nonneg _)
  have hprod_sq :
      (Real.sqrt (∑ i : Fin N, motzkinCoeffNorm (P i) ^ 2) *
          Real.sqrt (∑ i : Fin N, motzkinCoeffNorm (Q i) ^ 2)) ^ 2 =
        (∑ i : Fin N, motzkinCoeffNorm (P i) ^ 2) *
          ∑ i : Fin N, motzkinCoeffNorm (Q i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hsumP_nonneg, Real.sq_sqrt hsumQ_nonneg]
  have hsquares :
      (∑ i : Fin N, motzkinCoeffNorm (P i) * motzkinCoeffNorm (Q i)) ^ 2 ≤
        (Real.sqrt (∑ i : Fin N, motzkinCoeffNorm (P i) ^ 2) *
          Real.sqrt (∑ i : Fin N, motzkinCoeffNorm (Q i) ^ 2)) ^ 2 := by
    rwa [hprod_sq]
  have habs := sq_le_sq.mp hsquares
  rw [abs_of_nonneg hsum_nonneg, abs_of_nonneg hprod_nonneg] at habs
  exact habs

/-- Triangle inequality for the concrete coefficient `L^1` norm. -/
theorem motzkinCoeffNorm_add_le (p q : MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (p + q) ≤ motzkinCoeffNorm p + motzkinCoeffNorm q := by
  classical
  unfold motzkinCoeffNorm
  have hp_union :
      ∑ α ∈ p.support ∪ q.support, |MvPolynomial.coeff α p| =
        ∑ α ∈ p.support, |MvPolynomial.coeff α p| := by
    rw [← Finset.sum_subset Finset.subset_union_left]
    intro α _hα hnot
    have hc : MvPolynomial.coeff α p = 0 := notMem_support_iff.mp hnot
    simp [hc]
  have hq_union :
      ∑ α ∈ p.support ∪ q.support, |MvPolynomial.coeff α q| =
        ∑ α ∈ q.support, |MvPolynomial.coeff α q| := by
    rw [← Finset.sum_subset Finset.subset_union_right]
    intro α _hα hnot
    have hc : MvPolynomial.coeff α q = 0 := notMem_support_iff.mp hnot
    simp [hc]
  calc
    ∑ α ∈ (p + q).support, |MvPolynomial.coeff α (p + q)|
        ≤ ∑ α ∈ (p + q).support, (|MvPolynomial.coeff α p| +
          |MvPolynomial.coeff α q|) := by
          apply Finset.sum_le_sum
          intro α _hα
          rw [MvPolynomial.coeff_add]
          exact abs_add_le _ _
    _ ≤ ∑ α ∈ p.support ∪ q.support,
          (|MvPolynomial.coeff α p| + |MvPolynomial.coeff α q|) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg MvPolynomial.support_add
          intro α _hα _hnot
          exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    _ = ∑ α ∈ p.support ∪ q.support, |MvPolynomial.coeff α p| +
          ∑ α ∈ p.support ∪ q.support, |MvPolynomial.coeff α q| := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ α ∈ p.support, |MvPolynomial.coeff α p| +
          ∑ α ∈ q.support, |MvPolynomial.coeff α q| := by
          rw [hp_union, hq_union]

theorem motzkinCoeffNorm_add4_le (a b c d : MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (a + b + c + d) ≤
      motzkinCoeffNorm a + motzkinCoeffNorm b +
        motzkinCoeffNorm c + motzkinCoeffNorm d := by
  calc
    motzkinCoeffNorm (a + b + c + d) ≤ motzkinCoeffNorm (a + b + c) + motzkinCoeffNorm d := by
      simpa [add_assoc] using motzkinCoeffNorm_add_le (a + b + c) d
    _ ≤ (motzkinCoeffNorm (a + b) + motzkinCoeffNorm c) + motzkinCoeffNorm d := by
      nlinarith [motzkinCoeffNorm_add_le (a + b) c]
    _ ≤ (motzkinCoeffNorm a + motzkinCoeffNorm b + motzkinCoeffNorm c) + motzkinCoeffNorm d := by
      nlinarith [motzkinCoeffNorm_add_le a b]
    _ = motzkinCoeffNorm a + motzkinCoeffNorm b + motzkinCoeffNorm c + motzkinCoeffNorm d := by ring

theorem motzkinCoeffNorm_add5_le (a b c d e : MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (a + b + c + d + e) ≤
      motzkinCoeffNorm a + motzkinCoeffNorm b + motzkinCoeffNorm c +
        motzkinCoeffNorm d + motzkinCoeffNorm e := by
  calc
    motzkinCoeffNorm (a + b + c + d + e) ≤
        motzkinCoeffNorm (a + b + c + d) + motzkinCoeffNorm e := by
      simpa [add_assoc] using motzkinCoeffNorm_add_le (a + b + c + d) e
    _ ≤ (motzkinCoeffNorm a + motzkinCoeffNorm b +
        motzkinCoeffNorm c + motzkinCoeffNorm d) + motzkinCoeffNorm e := by
      nlinarith [motzkinCoeffNorm_add4_le a b c d]
    _ = motzkinCoeffNorm a + motzkinCoeffNorm b + motzkinCoeffNorm c +
        motzkinCoeffNorm d + motzkinCoeffNorm e := by ring

/-- Negation preserves the concrete coefficient `L^1` norm. -/
theorem motzkinCoeffNorm_neg (p : MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (-p) = motzkinCoeffNorm p := by
  classical
  unfold motzkinCoeffNorm
  have hsupp : (-p).support = p.support := by
    ext α
    simp [MvPolynomial.mem_support_iff]
  rw [hsupp]
  apply Finset.sum_congr rfl
  intro α _hα
  rw [MvPolynomial.coeff_neg]
  simp

/-- Triangle inequality for subtraction in the concrete coefficient `L^1` norm. -/
theorem motzkinCoeffNorm_sub_le (p q : MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (p - q) ≤ motzkinCoeffNorm p + motzkinCoeffNorm q := by
  rw [sub_eq_add_neg]
  calc
    motzkinCoeffNorm (p + -q) ≤
        motzkinCoeffNorm p + motzkinCoeffNorm (-q) :=
      motzkinCoeffNorm_add_le p (-q)
    _ = motzkinCoeffNorm p + motzkinCoeffNorm q := by rw [motzkinCoeffNorm_neg]

/-- Scalar multiplication bound for the concrete coefficient `L^1` norm. -/
theorem motzkinCoeffNorm_C_mul_le (c : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (MvPolynomial.C c * p) ≤ |c| * motzkinCoeffNorm p := by
  classical
  unfold motzkinCoeffNorm
  by_cases hc : c = 0
  · simp [hc]
  · have hsupp : (MvPolynomial.C c * p).support ⊆ p.support := by
      intro α hα
      rw [MvPolynomial.mem_support_iff] at hα ⊢
      rw [MvPolynomial.coeff_C_mul] at hα
      exact fun hp => hα (by simp [hp])
    calc
      ∑ α ∈ (MvPolynomial.C c * p).support,
          |MvPolynomial.coeff α (MvPolynomial.C c * p)|
          = ∑ α ∈ (MvPolynomial.C c * p).support, |c| * |MvPolynomial.coeff α p| := by
            apply Finset.sum_congr rfl
            intro α _hα
            rw [MvPolynomial.coeff_C_mul, abs_mul]
      _ = |c| * ∑ α ∈ (MvPolynomial.C c * p).support, |MvPolynomial.coeff α p| := by
            rw [Finset.mul_sum]
      _ ≤ |c| * ∑ α ∈ p.support, |MvPolynomial.coeff α p| := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
            exact Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun α _hα _hnot => abs_nonneg _)

theorem motzkinCoeffNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, motzkinCoeffNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [motzkinCoeffNorm]
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      exact le_trans (motzkinCoeffNorm_add_le (f a) (∑ i ∈ s, f i))
        (by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left ih (motzkinCoeffNorm (f a)))

theorem motzkinCoeffNorm_monomial_le (α : Fin 3 →₀ ℕ) (c : ℝ) :
    motzkinCoeffNorm (MvPolynomial.monomial α c : MvPolynomial (Fin 3) ℝ) ≤ |c| := by
  classical
  unfold motzkinCoeffNorm
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPolynomial.support_monomial]
    simp [hc, MvPolynomial.coeff_monomial]

theorem motzkinCoeffNorm_mul_le (p q : MvPolynomial (Fin 3) ℝ) :
    motzkinCoeffNorm (p * q) ≤ motzkinCoeffNorm p * motzkinCoeffNorm q := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_lhs => rw [MvPolynomial.as_sum q]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    motzkinCoeffNorm
        (∑ x ∈ p.support, ∑ y ∈ q.support,
          MvPolynomial.monomial x (MvPolynomial.coeff x p) *
            MvPolynomial.monomial y (MvPolynomial.coeff y q))
        ≤ ∑ x ∈ p.support, motzkinCoeffNorm
            (∑ y ∈ q.support, MvPolynomial.monomial x (MvPolynomial.coeff x p) *
              MvPolynomial.monomial y (MvPolynomial.coeff y q)) :=
          motzkinCoeffNorm_sum_le p.support fun x =>
            ∑ y ∈ q.support, MvPolynomial.monomial x (MvPolynomial.coeff x p) *
              MvPolynomial.monomial y (MvPolynomial.coeff y q)
    _ ≤ ∑ x ∈ p.support, ∑ y ∈ q.support, motzkinCoeffNorm
            (MvPolynomial.monomial x (MvPolynomial.coeff x p) *
              MvPolynomial.monomial y (MvPolynomial.coeff y q)) := by
          exact Finset.sum_le_sum fun x _ => motzkinCoeffNorm_sum_le q.support fun y =>
            MvPolynomial.monomial x (MvPolynomial.coeff x p) *
              MvPolynomial.monomial y (MvPolynomial.coeff y q)
    _ ≤ ∑ x ∈ p.support, ∑ y ∈ q.support,
          |MvPolynomial.coeff x p| * |MvPolynomial.coeff y q| := by
          apply Finset.sum_le_sum
          intro x _hx
          apply Finset.sum_le_sum
          intro y _hy
          rw [MvPolynomial.monomial_mul]
          simpa [abs_mul] using motzkinCoeffNorm_monomial_le (x + y)
            (MvPolynomial.coeff x p * MvPolynomial.coeff y q)
    _ = ∑ x ∈ p.support, |MvPolynomial.coeff x p| *
          (∑ y ∈ q.support, |MvPolynomial.coeff y q|) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [Finset.mul_sum]
    _ = motzkinCoeffNorm p * motzkinCoeffNorm q := by
          unfold motzkinCoeffNorm
          rw [Finset.sum_mul]


end Motzkin

end OptimalConvergenceRates

end
