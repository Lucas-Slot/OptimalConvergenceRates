/-
  OptimalConvergenceRates/BasicNotions/CoefficientNorm.lean

  Dimension-generic coefficient ℓ¹ norms for real multivariate polynomials.
-/
import OptimalConvergenceRates.BasicNotions.SOS

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates

/-- Coefficient ℓ¹ distance between multivariate polynomials. -/
def coeffL1Distance {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∑ α ∈ (p - q).support, |MvPolynomial.coeff α (p - q)|

/-- The coefficient ℓ¹ norm, defined from the existing coefficient distance. -/
def coeffL1Norm {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  coeffL1Distance p 0

theorem coeffL1Norm_eq_sum {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    coeffL1Norm p = ∑ α ∈ p.support, |MvPolynomial.coeff α p| := by
  simp [coeffL1Norm, coeffL1Distance]

theorem coeffL1Norm_nonneg {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    0 ≤ coeffL1Norm p := by
  rw [coeffL1Norm_eq_sum]
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

@[simp]
theorem coeffL1Norm_zero {n : ℕ} :
    coeffL1Norm (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  simp [coeffL1Norm_eq_sum]

theorem abs_coeff_le_coeffL1Norm {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (α : Fin n →₀ ℕ) :
    |MvPolynomial.coeff α p| ≤ coeffL1Norm p := by
  classical
  rw [coeffL1Norm_eq_sum]
  by_cases hα : α ∈ p.support
  · exact Finset.single_le_sum
      (f := fun β ↦ |MvPolynomial.coeff β p|)
      (fun _ _ ↦ abs_nonneg _) hα
  · rw [MvPolynomial.notMem_support_iff.mp hα, abs_zero]
    exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Triangle inequality for the coefficient ℓ¹ norm. -/
theorem coeffL1Norm_add_le {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    coeffL1Norm (p + q) ≤ coeffL1Norm p + coeffL1Norm q := by
  classical
  simp only [coeffL1Norm_eq_sum]
  have hp :
      ∑ α ∈ p.support ∪ q.support, |MvPolynomial.coeff α p| =
        ∑ α ∈ p.support, |MvPolynomial.coeff α p| := by
    rw [← Finset.sum_subset Finset.subset_union_left]
    intro α _ hα
    simp [MvPolynomial.notMem_support_iff.mp hα]
  have hq :
      ∑ α ∈ p.support ∪ q.support, |MvPolynomial.coeff α q| =
        ∑ α ∈ q.support, |MvPolynomial.coeff α q| := by
    rw [← Finset.sum_subset Finset.subset_union_right]
    intro α _ hα
    simp [MvPolynomial.notMem_support_iff.mp hα]
  calc
    ∑ α ∈ (p + q).support, |MvPolynomial.coeff α (p + q)|
        ≤ ∑ α ∈ (p + q).support,
            (|MvPolynomial.coeff α p| + |MvPolynomial.coeff α q|) := by
          apply Finset.sum_le_sum
          intro α _
          simpa using abs_add_le (MvPolynomial.coeff α p) (MvPolynomial.coeff α q)
    _ ≤ ∑ α ∈ p.support ∪ q.support,
          (|MvPolynomial.coeff α p| + |MvPolynomial.coeff α q|) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg MvPolynomial.support_add
          intro α _ _
          positivity
    _ = ∑ α ∈ p.support ∪ q.support, |MvPolynomial.coeff α p| +
          ∑ α ∈ p.support ∪ q.support, |MvPolynomial.coeff α q| := by
          rw [← Finset.sum_add_distrib]
    _ = _ := by rw [hp, hq]

@[simp]
theorem coeffL1Norm_neg {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    coeffL1Norm (-p) = coeffL1Norm p := by
  classical
  simp only [coeffL1Norm_eq_sum]
  have hsupp : (-p).support = p.support := by
    ext α
    simp [MvPolynomial.mem_support_iff]
  rw [hsupp]
  apply Finset.sum_congr rfl
  intro α _
  simp

theorem coeffL1Norm_sub_le {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    coeffL1Norm (p - q) ≤ coeffL1Norm p + coeffL1Norm q := by
  simpa [sub_eq_add_neg] using coeffL1Norm_add_le p (-q)

theorem coeffL1Norm_C_mul_le {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    coeffL1Norm (C c * p) ≤ |c| * coeffL1Norm p := by
  classical
  simp only [coeffL1Norm_eq_sum]
  have hsupp : (C c * p).support ⊆ p.support := by
    intro α hα
    rw [MvPolynomial.mem_support_iff] at hα ⊢
    rw [MvPolynomial.coeff_C_mul] at hα
    exact fun hp ↦ hα (by simp [hp])
  calc
    ∑ α ∈ (C c * p).support, |MvPolynomial.coeff α (C c * p)|
        = ∑ α ∈ (C c * p).support, |c| * |MvPolynomial.coeff α p| := by
          apply Finset.sum_congr rfl
          intro α _
          simp [MvPolynomial.coeff_C_mul, abs_mul]
    _ = |c| * ∑ α ∈ (C c * p).support, |MvPolynomial.coeff α p| := by
          rw [Finset.mul_sum]
    _ ≤ |c| * ∑ α ∈ p.support, |MvPolynomial.coeff α p| := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsupp fun _ _ _ ↦ abs_nonneg _

theorem coeffL1Norm_sum_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℝ) :
    coeffL1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffL1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (coeffL1Norm_add_le _ _).trans
        (add_le_add (le_refl (coeffL1Norm (f a))) ih)

theorem coeffL1Norm_monomial_le {n : ℕ} (α : Fin n →₀ ℕ) (c : ℝ) :
    coeffL1Norm (MvPolynomial.monomial α c : MvPolynomial (Fin n) ℝ) ≤ |c| := by
  classical
  rw [coeffL1Norm_eq_sum]
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPolynomial.support_monomial]
    simp [hc, MvPolynomial.coeff_monomial]


/-- A constant polynomial has coefficient norm at most the absolute value
of its scalar. -/
theorem coeffL1Norm_C_le {n : ℕ} (c : ℝ) :
    coeffL1Norm (C c : MvPolynomial (Fin n) ℝ) ≤ |c| := by
  simpa only [MvPolynomial.C_apply] using
    coeffL1Norm_monomial_le (n := n) (0 : Fin n →₀ ℕ) c
/-- Submultiplicativity of the coefficient ℓ¹ norm. -/
theorem coeffL1Norm_mul_le {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    coeffL1Norm (p * q) ≤ coeffL1Norm p * coeffL1Norm q := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_lhs => rw [MvPolynomial.as_sum q]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    coeffL1Norm
        (∑ x ∈ p.support, ∑ y ∈ q.support,
          MvPolynomial.monomial x (MvPolynomial.coeff x p) *
            MvPolynomial.monomial y (MvPolynomial.coeff y q))
        ≤ ∑ x ∈ p.support, coeffL1Norm
            (∑ y ∈ q.support, MvPolynomial.monomial x (MvPolynomial.coeff x p) *
              MvPolynomial.monomial y (MvPolynomial.coeff y q)) :=
          coeffL1Norm_sum_le p.support fun x ↦
            ∑ y ∈ q.support, MvPolynomial.monomial x (MvPolynomial.coeff x p) *
              MvPolynomial.monomial y (MvPolynomial.coeff y q)
    _ ≤ ∑ x ∈ p.support, ∑ y ∈ q.support, coeffL1Norm
            (MvPolynomial.monomial x (MvPolynomial.coeff x p) *
              MvPolynomial.monomial y (MvPolynomial.coeff y q)) :=
          Finset.sum_le_sum fun x _ ↦ coeffL1Norm_sum_le q.support fun y ↦
            MvPolynomial.monomial x (MvPolynomial.coeff x p) *
              MvPolynomial.monomial y (MvPolynomial.coeff y q)
    _ ≤ ∑ x ∈ p.support, ∑ y ∈ q.support,
          |MvPolynomial.coeff x p| * |MvPolynomial.coeff y q| := by
          apply Finset.sum_le_sum
          intro x _
          apply Finset.sum_le_sum
          intro y _
          rw [MvPolynomial.monomial_mul]
          simpa [abs_mul] using coeffL1Norm_monomial_le (x + y)
            (MvPolynomial.coeff x p * MvPolynomial.coeff y q)
    _ = ∑ x ∈ p.support, |MvPolynomial.coeff x p| *
          (∑ y ∈ q.support, |MvPolynomial.coeff y q|) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ = coeffL1Norm p * coeffL1Norm q := by
          simp only [coeffL1Norm_eq_sum, Finset.sum_mul]


/-- The coefficient norm of a finite product is bounded by the product of
the coefficient norms. -/
theorem coeffL1Norm_prod_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin n) ℝ) :
    coeffL1Norm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coeffL1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using coeffL1Norm_C_le (n := n) (1 : ℝ)
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (coeffL1Norm_mul_le _ _).trans
        (mul_le_mul (le_refl _) ih
          (coeffL1Norm_nonneg _) (coeffL1Norm_nonneg _))
theorem coeffL1Norm_pow_le {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (k : ℕ) :
    coeffL1Norm (p ^ k) ≤ coeffL1Norm p ^ k := by
  induction k with
  | zero =>
      simpa using coeffL1Norm_monomial_le (n := n) (0 : Fin n →₀ ℕ) (1 : ℝ)
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact (coeffL1Norm_mul_le _ _).trans
        (mul_le_mul ih le_rfl (coeffL1Norm_nonneg p) (pow_nonneg (coeffL1Norm_nonneg p) k))

/-- Substitution by polynomials of coefficient norm at most `G ≥ 1` grows
the coefficient norm by at most `G` to the total degree. -/
theorem coeffL1Norm_aeval_le
    {n m : ℕ} (f : Fin n → MvPolynomial (Fin m) ℝ)
    (p : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (hf : ∀ i, coeffL1Norm (f i) ≤ G) :
    coeffL1Norm (MvPolynomial.aeval f p) ≤
      coeffL1Norm p * G ^ p.totalDegree := by
  classical
  have hmonomial (α : Fin n →₀ ℕ) (hα : α ∈ p.support) :
      coeffL1Norm
          (MvPolynomial.aeval f
            (MvPolynomial.monomial α (MvPolynomial.coeff α p))) ≤
        |MvPolynomial.coeff α p| * G ^ p.totalDegree := by
    have hprod :
        coeffL1Norm (α.prod fun i k => f i ^ k) ≤
          G ^ α.sum (fun _ k => k) := by
      rw [Finsupp.prod, Finsupp.sum]
      calc
        coeffL1Norm (∏ i ∈ α.support, f i ^ α i) ≤
            ∏ i ∈ α.support, coeffL1Norm (f i ^ α i) :=
          coeffL1Norm_prod_le α.support (fun i => f i ^ α i)
        _ ≤ ∏ i ∈ α.support, coeffL1Norm (f i) ^ α i := by
          apply Finset.prod_le_prod
          · intro i hi
            exact coeffL1Norm_nonneg (f i ^ α i)
          · intro i hi
            exact coeffL1Norm_pow_le (f i) (α i)
        _ ≤ ∏ i ∈ α.support, G ^ α i := by
          apply Finset.prod_le_prod
          · intro i hi
            exact pow_nonneg (coeffL1Norm_nonneg (f i)) (α i)
          · intro i hi
            exact pow_le_pow_left₀ (coeffL1Norm_nonneg (f i)) (hf i) (α i)
        _ = G ^ ∑ i ∈ α.support, α i :=
          Finset.prod_pow_eq_pow_sum _ _ _
    have hdegree : α.sum (fun _ k => k) ≤ p.totalDegree :=
      MvPolynomial.le_totalDegree hα
    have hprod' :
        coeffL1Norm (α.prod fun i k => f i ^ k) ≤
          G ^ p.totalDegree :=
      hprod.trans (pow_le_pow_right₀ hG hdegree)
    rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
    exact (coeffL1Norm_C_mul_le (MvPolynomial.coeff α p)
      (α.prod fun i k => f i ^ k)).trans
        (mul_le_mul_of_nonneg_left hprod' (abs_nonneg _))
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum]
  calc
    coeffL1Norm
        (∑ α ∈ p.support,
          MvPolynomial.aeval f
            (MvPolynomial.monomial α (MvPolynomial.coeff α p))) ≤
        ∑ α ∈ p.support,
          coeffL1Norm
            (MvPolynomial.aeval f
              (MvPolynomial.monomial α (MvPolynomial.coeff α p))) :=
      coeffL1Norm_sum_le p.support fun α =>
        MvPolynomial.aeval f
          (MvPolynomial.monomial α (MvPolynomial.coeff α p))
    _ ≤ ∑ α ∈ p.support,
          |MvPolynomial.coeff α p| * G ^ p.totalDegree := by
      exact Finset.sum_le_sum fun α hα => hmonomial α hα
    _ = coeffL1Norm p * G ^ p.totalDegree := by
      rw [coeffL1Norm_eq_sum, Finset.sum_mul]

end OptimalConvergenceRates

end
