/-
  Coefficient-bounded witnesses for the finite quadratic-module order.
-/
import OptimalConvergenceRates.GeneralArchimedean.Certificates
import OptimalConvergenceRates.GeneralArchimedean.ModuleOrder

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- A named, coefficient-bounded witness for `p ≤ q` in a truncated
quadratic module. -/
abbrev BoundedModuleLEAt
    (g : Fin m → MvPolynomial (Fin n) ℝ) (r : ℕ) (H : ℝ)
    (p q : MvPolynomial (Fin n) ℝ) :=
  BoundedQuadraticModuleCertificate g (q - p) r H

namespace BoundedModuleLEAt

/-- Forget the coefficient-tracked witness. -/
theorem toModuleLEAt
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r : ℕ} {H : ℝ} {p q : MvPolynomial (Fin n) ℝ}
    (c : BoundedModuleLEAt g r H p q) : ModuleLEAt g r p q :=
  c.toMem

/-- Reflexivity has zero coefficient cost and zero order. -/
def refl (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    BoundedModuleLEAt g 0 0 p p :=
  (BoundedQuadraticModuleCertificate.ofSOS g 0 IsSOS_zero (by simp)).congr
    (by ring)

/-- Increase only the truncation order. -/
def mono
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r s : ℕ} {H : ℝ} {p q : MvPolynomial (Fin n) ℝ}
    (c : BoundedModuleLEAt g r H p q) (hrs : r ≤ s) :
    BoundedModuleLEAt g s H p q :=
  BoundedQuadraticModuleCertificate.mono c hrs

/-- Increase only the coefficient budget. -/
def weakenBound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r : ℕ} {H K : ℝ} {p q : MvPolynomial (Fin n) ℝ}
    (c : BoundedModuleLEAt g r H p q) (hHK : H ≤ K) :
    BoundedModuleLEAt g r K p q :=
  BoundedQuadraticModuleCertificate.weakenBound c hHK

/-- Transitivity adds coefficient budgets and takes the maximum order. -/
def trans
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r s : ℕ} {H K : ℝ}
    {p q u : MvPolynomial (Fin n) ℝ}
    (c : BoundedModuleLEAt g r H p q)
    (d : BoundedModuleLEAt g s K q u) :
    BoundedModuleLEAt g (max r s) (H + K) p u :=
  (BoundedQuadraticModuleCertificate.add c d).congr (by ring)

/-- Addition of two bounded module inequalities. -/
def add
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r s : ℕ} {H K : ℝ}
    {p q u v : MvPolynomial (Fin n) ℝ}
    (c : BoundedModuleLEAt g r H p q)
    (d : BoundedModuleLEAt g s K u v) :
    BoundedModuleLEAt g (max r s) (H + K) (p + u) (q + v) :=
  (BoundedQuadraticModuleCertificate.add c d).congr (by ring)

/-- Multiplication on both sides by an SOS polynomial. -/
def sosMulLeft
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r : ℕ} {H : ℝ}
    {p q s : MvPolynomial (Fin n) ℝ}
    (c : BoundedModuleLEAt g r H p q) (hs : IsSOS s) :
    BoundedModuleLEAt g (s.totalDegree + r) (coeffL1Norm s * H)
      (s * p) (s * q) :=
  (BoundedQuadraticModuleCertificate.sosMul c hs).congr (by ring)

/-- SOS multiplication using an external coefficient bound for the factor. -/
def sosMulLeftOfNormLe
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r : ℕ} {H K : ℝ}
    {p q s : MvPolynomial (Fin n) ℝ}
    (c : BoundedModuleLEAt g r H p q) (hs : IsSOS s)
    (hsNorm : coeffL1Norm s ≤ K) :
    BoundedModuleLEAt g (s.totalDegree + r) (K * H)
      (s * p) (s * q) :=
  (c.sosMulLeft hs).weakenBound
    (mul_le_mul_of_nonneg_right hsNorm c.bound_nonneg)

/-- Multiplication of two module inequalities, with external coefficient
bounds for the lower factor of the first inequality and the upper factor of
the second.  This is the coefficient-tracked telescoping identity. -/
def mulOfNormLe
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r s : ℕ} {H K Hp Hv : ℝ}
    {p q u v : MvPolynomial (Fin n) ℝ}
    (c : BoundedModuleLEAt g r H p q)
    (d : BoundedModuleLEAt g s K u v)
    (hp : IsSOS p) (hv : IsSOS v)
    (hpNorm : coeffL1Norm p ≤ Hp)
    (hvNorm : coeffL1Norm v ≤ Hv) :
    BoundedModuleLEAt g
      (max (v.totalDegree + r) (p.totalDegree + s))
      (Hv * H + Hp * K) (p * u) (q * v) := by
  let c₁ := c.sosMulLeftOfNormLe hv hvNorm
  let c₂ := d.sosMulLeftOfNormLe hp hpNorm
  exact (c₁.add c₂).congr (by ring)

/-- Finite sums preserve a common order; their coefficient budgets add. -/
theorem sum {ι : Type*}
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (p q : ι → MvPolynomial (Fin n) ℝ)
    {r : ℕ} {H : ℝ}
    (hle : ∀ i ∈ s, BoundedModuleLEAt g r H (p i) (q i)) :
    Nonempty (BoundedModuleLEAt g r (s.card * H)
      (∑ i ∈ s, p i) (∑ i ∈ s, q i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨by
        simpa using (BoundedModuleLEAt.refl g
          (0 : MvPolynomial (Fin n) ℝ)).mono (Nat.zero_le r)⟩
  | @insert a s ha ih =>
      obtain ⟨ctail⟩ := ih fun i hi => hle i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.card_insert_of_notMem ha]
      have hadd := (hle a (Finset.mem_insert_self a s)).add
        ctail
      exact ⟨by
        simpa [max_self, Nat.cast_add, Nat.cast_one, add_mul, add_comm] using hadd⟩


/-- Proposition-safe finite summation when each bounded witness is only
known to be nonempty. -/
theorem sum_nonempty {ι : Type*}
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (p q : ι → MvPolynomial (Fin n) ℝ)
    {r : ℕ} {H : ℝ}
    (hle : ∀ i ∈ s, Nonempty (BoundedModuleLEAt g r H (p i) (q i))) :
    Nonempty (BoundedModuleLEAt g r (s.card * H)
      (∑ i ∈ s, p i) (∑ i ∈ s, q i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨by
        simpa using (BoundedModuleLEAt.refl g
          (0 : MvPolynomial (Fin n) ℝ)).mono (Nat.zero_le r)⟩
  | @insert a s ha ih =>
      obtain ⟨chead⟩ := hle a (Finset.mem_insert_self a s)
      obtain ⟨ctail⟩ := ih fun i hi =>
        hle i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.card_insert_of_notMem ha]
      have hadd := chead.add ctail
      exact ⟨by
        simpa [max_self, Nat.cast_add, Nat.cast_one, add_mul, add_comm]
          using hadd⟩
/-- Finite products preserve bounded module order.  If all factors have
coefficient norm at most K, the deliberately coarse exponential budget is
stable under the telescoping induction. -/
theorem prod {ι : Type*}
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι)
    (p q : ι → MvPolynomial (Fin n) ℝ)
    (r d : ℕ) {H K : ℝ}
    (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hp : ∀ i ∈ s, IsSOS (p i))
    (hq : ∀ i ∈ s, IsSOS (q i))
    (hpdeg : ∀ i ∈ s, (p i).totalDegree ≤ d)
    (hqdeg : ∀ i ∈ s, (q i).totalDegree ≤ d)
    (hpNorm : ∀ i ∈ s, coeffL1Norm (p i) ≤ K)
    (hqNorm : ∀ i ∈ s, coeffL1Norm (q i) ≤ K)
    (hle : ∀ i ∈ s, BoundedModuleLEAt g r H (p i) (q i)) :
    Nonempty (BoundedModuleLEAt g (s.card * (r + d))
      ((K + 1) ^ s.card * H)
      (∏ i ∈ s, p i) (∏ i ∈ s, q i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨by
        simpa using
          (BoundedModuleLEAt.refl g
            (1 : MvPolynomial (Fin n) ℝ)).weakenBound hH⟩
  | @insert a s ha ih =>
      obtain ⟨htail⟩ := ih
        (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi => hq i (Finset.mem_insert_of_mem hi))
        (fun i hi => hpdeg i (Finset.mem_insert_of_mem hi))
        (fun i hi => hqdeg i (Finset.mem_insert_of_mem hi))
        (fun i hi => hpNorm i (Finset.mem_insert_of_mem hi))
        (fun i hi => hqNorm i (Finset.mem_insert_of_mem hi))
        (fun i hi => hle i (Finset.mem_insert_of_mem hi))
      have hqtailSOS : IsSOS (∏ i ∈ s, q i) :=
        IsSOS_finset_prod fun i hi =>
          hq i (Finset.mem_insert_of_mem hi)
      have hqtailNorm :
          coeffL1Norm (∏ i ∈ s, q i) ≤ (K + 1) ^ s.card := by
        calc
          coeffL1Norm (∏ i ∈ s, q i) ≤
              ∏ i ∈ s, coeffL1Norm (q i) :=
            coeffL1Norm_prod_le s q
          _ ≤ ∏ _i ∈ s, K := by
            exact Finset.prod_le_prod₀
              (fun _ _ => coeffL1Norm_nonneg _)
              (fun i hi => hqNorm i (Finset.mem_insert_of_mem hi))
          _ = K ^ s.card := by simp
          _ ≤ (K + 1) ^ s.card := by
            exact pow_le_pow_left₀ hK (by linarith) _
      have hmul := BoundedModuleLEAt.mulOfNormLe
        (hle a (Finset.mem_insert_self a s)) htail
        (hp a (Finset.mem_insert_self a s)) hqtailSOS
        (hpNorm a (Finset.mem_insert_self a s)) hqtailNorm
      have hqtailDegree :
          (∏ i ∈ s, q i).totalDegree ≤ s.card * d :=
        totalDegree_finset_prod_le_card_mul s q d
          (fun i hi => hqdeg i (Finset.mem_insert_of_mem hi))
      have horder :
          max ((∏ i ∈ s, q i).totalDegree + r)
              ((p a).totalDegree + s.card * (r + d)) ≤
            (s.card + 1) * (r + d) := by
        apply max_le
        · calc
            (∏ i ∈ s, q i).totalDegree + r ≤
                s.card * d + r := Nat.add_le_add_right hqtailDegree r
            _ ≤ s.card * (r + d) + r := by
              gcongr
              exact Nat.le_add_left d r
            _ ≤ s.card * (r + d) + (r + d) := by omega
            _ = (s.card + 1) * (r + d) := by ring
        · calc
            (p a).totalDegree + s.card * (r + d) ≤
                d + s.card * (r + d) :=
              Nat.add_le_add_right
                (hpdeg a (Finset.mem_insert_self a s)) _
            _ ≤ (r + d) + s.card * (r + d) := by omega
            _ = (s.card + 1) * (r + d) := by ring
      have hbudget :
          (K + 1) ^ s.card * H +
              K * ((K + 1) ^ s.card * H) ≤
            (K + 1) ^ (s.card + 1) * H := by
        rw [pow_succ]
        ring_nf
        exact le_rfl
      rw [Finset.card_insert_of_notMem ha,
        Finset.prod_insert ha, Finset.prod_insert ha]
      exact ⟨(hmul.mono horder).weakenBound hbudget⟩

end BoundedModuleLEAt

end OptimalConvergenceRates.GeneralArchimedean

end
