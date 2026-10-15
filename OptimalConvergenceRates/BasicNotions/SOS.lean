/-
  OptimalConvergenceRates/BasicNotions/SOS.lean

  Sum-of-squares predicates, degree-bounded SOS witnesses, and basic SOS evaluation bounds.
-/
import OptimalConvergenceRates.BasicNotions.SOSVector
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

open MvPolynomial Finset
open scoped MonomialOrder

noncomputable section

namespace OptimalConvergenceRates

variable {n N : ℕ}

/-! ## Univariate SOS -/

/-- A univariate polynomial is SOS -/
def IsSOSUni (p : Polynomial ℝ) : Prop :=
  ∃ (m : ℕ) (q : Fin m → Polynomial ℝ), p = ∑ i : Fin m, (q i) ^ 2

/-- A square polynomial is SOS (witnessed by a single-element sum). -/
theorem IsSOSUni_sq (q : Polynomial ℝ) : IsSOSUni (q ^ 2) :=
  ⟨1, fun _ => q, by simp⟩

/-- A univariate SOS polynomial is nonnegative at every real point. -/
theorem IsSOSUni.eval_nonneg {p : Polynomial ℝ}
    (hp : IsSOSUni p) (x : ℝ) : 0 ≤ p.eval x := by
  obtain ⟨m, q, rfl⟩ := hp
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow]
  exact Finset.sum_nonneg fun i _ => sq_nonneg ((q i).eval x)


/-- In a univariate sum of real squares, no square-root summand can
have degree larger than half the degree of the sum. -/
theorem sum_sq_natDegree_leading_bound
    (P : Fin N → Polynomial ℝ) (i₀ : Fin N) :
    2 * (P i₀).natDegree ≤
      (∑ i : Fin N, (P i) ^ 2).natDegree := by
  classical
  let s : Finset ℕ :=
    Finset.univ.image fun i : Fin N => (P i).natDegree
  have hs : s.Nonempty := by
    exact ⟨(P i₀).natDegree, by simp [s]⟩
  let D : ℕ := s.max' hs
  have hDmem : D ∈ s := Finset.max'_mem s hs
  obtain ⟨j, -, hjD⟩ := Finset.mem_image.mp hDmem
  have hleD (i : Fin N) : (P i).natDegree ≤ D := by
    exact Finset.le_max' s (P i).natDegree (by simp [s])
  have hi₀D : (P i₀).natDegree ≤ D := hleD i₀
  by_cases hD0 : D = 0
  · omega
  have hPj : P j ≠ 0 := by
    intro hj
    have : D = 0 := by simpa [hj] using hjD.symm
    exact hD0 this
  have hcoeff_terms (i : Fin N) :
      ((P i) ^ 2).coeff (2 * D) = ((P i).coeff D) ^ 2 := by
    simpa using
      (Polynomial.coeff_pow_of_natDegree_le
        (p := P i) (m := 2) (n := D) (hleD i))
  have hcoeff_pos :
      0 < (∑ i : Fin N, (P i) ^ 2).coeff (2 * D) := by
    rw [← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply]
    simp_rw [hcoeff_terms]
    apply Finset.sum_pos'
    · intro i _
      exact sq_nonneg _
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      have hjcoeff : (P j).coeff D ≠ 0 := by
        rw [← hjD]
        exact Polynomial.leadingCoeff_ne_zero.mpr hPj
      exact sq_pos_of_ne_zero hjcoeff
  have hDdegree :
      2 * D ≤ (∑ i : Fin N, (P i) ^ 2).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (ne_of_gt hcoeff_pos)
  exact (Nat.mul_le_mul_left 2 hi₀D).trans hDdegree

/-- Degree-controlled form of a univariate SOS witness. -/
theorem IsSOSUni.exists_degree_controlled
    {p : Polynomial ℝ} (hp : IsSOSUni p) :
    ∃ (m : ℕ) (q : Fin m → Polynomial ℝ),
      p = ∑ i : Fin m, (q i) ^ 2 ∧
        ∀ i, 2 * (q i).natDegree ≤ p.natDegree := by
  obtain ⟨m, q, hq⟩ := hp
  refine ⟨m, q, hq, fun i => ?_⟩
  rw [hq]
  exact sum_sq_natDegree_leading_bound q i

/-! ## Multivariate SOS -/

/-- A polynomial is SOS if it can be written as a sum of squares -/
def IsSOS (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin n) ℝ),
    p = ∑ i : Fin m, (q i) ^ 2

/-- Evaluation of an explicit SOS decomposition is the squared norm of the
vector of evaluated summands. -/
theorem sos_eval_eq_vecSqNorm
    (σ : MvPolynomial (Fin n) ℝ) (P : Fin N → MvPolynomial (Fin n) ℝ)
    (hσ : σ = ∑ i : Fin N, (P i) ^ 2) (z : Fin n → ℝ) :
    MvPolynomial.eval z σ = vecSqNorm (fun i => MvPolynomial.eval z (P i)) := by
  rw [hσ]
  unfold vecSqNorm
  simp only [map_sum, map_pow]

/-- An SOS witness can be viewed as a finite vector whose squared norm evaluates
to the SOS polynomial. -/
theorem IsSOS.exists_vecSqNorm_eval
    (σ : MvPolynomial (Fin n) ℝ) (hσ : IsSOS σ) :
    ∃ (N : ℕ) (P : Fin N → MvPolynomial (Fin n) ℝ),
      σ = ∑ i : Fin N, (P i) ^ 2 ∧
      ∀ z : Fin n → ℝ,
        MvPolynomial.eval z σ = vecSqNorm (fun i => MvPolynomial.eval z (P i)) := by
  obtain ⟨N, P, hP⟩ := hσ
  exact ⟨N, P, hP, fun z => sos_eval_eq_vecSqNorm σ P hP z⟩

/-- A degree bound on an SOS polynomial controls the degrees of the square-root
summands in a fixed SOS representation.

This is the algebraic non-cancellation fact for leading terms of sums of squares
over `ℝ`. -/
private theorem sum_sq_totalDegree_leading_bound
    (P : Fin N → MvPolynomial (Fin n) ℝ) (i₀ : Fin N) :
    2 * (P i₀).totalDegree ≤ (∑ i : Fin N, (P i) ^ 2).totalDegree := by
  classical
  let m : MonomialOrder (Fin n) := MonomialOrder.degLex
  let s : Finset m.syn := Finset.univ.image fun i : Fin N => m.toSyn (m.degree (P i))
  have hs : s.Nonempty := by
    refine ⟨m.toSyn (m.degree (P i₀)), ?_⟩
    simp [s]
  let Dsyn : m.syn := s.max' hs
  let D : Fin n →₀ ℕ := m.toSyn.symm Dsyn
  have hDmem : Dsyn ∈ s := Finset.max'_mem s hs
  have hDmem' :
      Dsyn ∈ Finset.univ.image (fun i : Fin N => m.toSyn (m.degree (P i))) := by
    simpa [s] using hDmem
  rw [Finset.mem_image] at hDmem'
  obtain ⟨j, -, hjDsyn⟩ := hDmem'
  have hjD : m.degree (P j) = D := by
    apply m.toSyn.injective
    simpa [D] using hjDsyn
  have hleD (i : Fin N) : m.degree (P i) ≼[m] D := by
    have hi : m.toSyn (m.degree (P i)) ∈ s := by
      simp [s]
    have hle := Finset.le_max' s (m.toSyn (m.degree (P i))) hi
    simpa [D, Dsyn] using hle
  have hJtot : (P j).totalDegree = D.degree := by
    rw [← MvPolynomial.degree_degLexDegree (f := P j), ← hjD]
  have hi₀tot : (P i₀).totalDegree ≤ D.degree := by
    have := MvPolynomial.degLex_totalDegree_monotone (f := P i₀) (g := P j)
      (by simpa [m, hjD] using hleD i₀)
    exact this.trans_eq hJtot
  by_cases hD0 : D.degree = 0
  · nlinarith
  have hcoeff_terms : ∀ i : Fin N,
      ((P i) ^ 2).coeff (2 • D) =
        if m.degree (P i) = D then m.leadingCoeff (P i) ^ 2 else 0 := by
    intro i
    by_cases hiD : m.degree (P i) = D
    · rw [ite_eq_left hiD, ← hiD]
      change AddMonoidAlgebra.coeff (P i ^ 2) (2 • m.degree (P i)) = _
      rw [m.coeff_pow_nsmul_degree]
    · have hlt : m.degree (P i) ≺[m] D := lt_of_le_of_ne (hleD i) hiD
      have hpowle : m.degree ((P i) ^ 2) ≼[m] (2 • m.degree (P i)) :=
        m.degree_pow_le 2
      have htwolt : (2 • m.degree (P i)) ≺[m] (2 • D) := by
        change m.toSyn (2 • m.degree (P i)) < m.toSyn (2 • D)
        simpa [two_nsmul] using add_lt_add hlt hlt
      have hpowlt : m.degree ((P i) ^ 2) ≺[m] (2 • D) :=
        lt_of_le_of_lt hpowle htwolt
      change AddMonoidAlgebra.coeff (P i ^ 2) (2 • D) = _
      rw [m.coeff_eq_zero_of_lt hpowlt]
      simp [hiD]
  have hPj_ne : P j ≠ 0 := by
    intro hp
    have hDz : D = 0 := by
      simpa [hp] using hjD.symm
    exact hD0 (by simp [hDz])
  have hcoeff_pos : 0 < (∑ i : Fin N, (P i) ^ 2).coeff (2 • D) := by
    change 0 < AddMonoidAlgebra.coeff (∑ i : Fin N, (P i) ^ 2) (2 • D)
    rw [coeff_sum]
    simp_rw [hcoeff_terms]
    apply Finset.sum_pos'
    · intro i _
      by_cases hiD : m.degree (P i) = D
      · rw [ite_eq_left hiD]
        exact sq_nonneg _
      · rw [ite_eq_right hiD]
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      rw [ite_eq_left hjD]
      exact sq_pos_of_ne_zero (m.leadingCoeff_ne_zero_iff.mpr hPj_ne)
  have hmem : (2 • D) ∈ (∑ i : Fin N, (P i) ^ 2).support := by
    rw [mem_support_iff]
    exact ne_of_gt hcoeff_pos
  have htd := MvPolynomial.le_totalDegree hmem
  have htd' : 2 * D.degree ≤ (∑ i : Fin N, (P i) ^ 2).totalDegree := by
    rw [two_nsmul] at htd
    change Finsupp.degree (D + D) ≤ (∑ i : Fin N, (P i) ^ 2).totalDegree at htd
    rw [show (D + D).degree = D.degree + D.degree from map_add Finsupp.degree D D] at htd
    simpa [two_mul] using htd
  exact (Nat.mul_le_mul_left 2 hi₀tot).trans htd'

theorem sos_summand_totalDegree_le_of_sum_sq_totalDegree
    {n N r : ℕ}
    {σ : MvPolynomial (Fin n) ℝ}
    {P : Fin N → MvPolynomial (Fin n) ℝ}
    (hσ : σ = ∑ i : Fin N, (P i) ^ 2)
    (hdeg : σ.totalDegree ≤ 2 * r) :
    ∀ i : Fin N, (P i).totalDegree ≤ r := by
  intro i
  have hsum := sum_sq_totalDegree_leading_bound P i
  rw [← hσ] at hsum
  exact Nat.le_of_mul_le_mul_left (hsum.trans hdeg) (by norm_num : 0 < 2)

/-- A sum-of-squares witness with degree-controlled square roots.

The field `degree` bounds the degree of each square-root polynomial, not just the
resulting sum of squares. This extra datum supports vector-valued Markov and
endpoint arguments. -/
structure DegreeBoundedSOS (σ : MvPolynomial (Fin n) ℝ) (r : ℕ) where
  N : ℕ
  P : Fin N → MvPolynomial (Fin n) ℝ
  decomp : σ = ∑ i : Fin N, (P i) ^ 2
  degree : ∀ i, (P i).totalDegree ≤ r

theorem DegreeBoundedSOS.toIsSOS {σ : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hσ : DegreeBoundedSOS σ r) : IsSOS σ :=
  ⟨hσ.N, hσ.P, hσ.decomp⟩

theorem DegreeBoundedSOS.eval_eq_vecSqNorm {σ : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hσ : DegreeBoundedSOS σ r) (z : Fin n → ℝ) :
    MvPolynomial.eval z σ = vecSqNorm (fun i => MvPolynomial.eval z (hσ.P i)) :=
  sos_eval_eq_vecSqNorm σ hσ.P hσ.decomp z

/-- A degree-controlled SOS witness gives the expected coarse degree bound for
its sum of squares. -/
theorem DegreeBoundedSOS.totalDegree_le_two_mul {σ : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hσ : DegreeBoundedSOS σ r) : σ.totalDegree ≤ 2 * r := by
  rw [hσ.decomp]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  calc ((hσ.P i) ^ 2).totalDegree
      ≤ 2 * (hσ.P i).totalDegree := MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 * r := Nat.mul_le_mul_left 2 (hσ.degree i)

/-- A polynomial is nonnegative on a set S -/
def IsNonnegOn (p : MvPolynomial (Fin n) ℝ) (S : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ S, 0 ≤ MvPolynomial.eval x p


/-! ## SOS and preordering properties -/

theorem IsSOS_nonneg (p : MvPolynomial (Fin n) ℝ) (hp : IsSOS p) :
    IsNonnegOn p Set.univ := by
  obtain ⟨m, q, rfl⟩ := hp
  intro x _
  simp only [map_sum, map_pow]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-! ## SOS closure properties -/

/-- A polynomial squared is trivially SOS. -/
theorem IsSOS_sq (p : MvPolynomial (Fin n) ℝ) : IsSOS (p ^ 2) :=
  ⟨1, fun _ => p, by simp⟩

/-- Zero is SOS. -/
theorem IsSOS_zero : IsSOS (0 : MvPolynomial (Fin n) ℝ) :=
  ⟨0, Fin.elim0, by simp⟩

/-- A nonneg constant is SOS. -/
theorem IsSOS_C_nonneg (c : ℝ) (hc : 0 ≤ c) :
    IsSOS (MvPolynomial.C c : MvPolynomial (Fin n) ℝ) := by
  refine ⟨1, fun _ => MvPolynomial.C (Real.sqrt c), ?_⟩
  simp only [Fin.sum_univ_one, sq, ← MvPolynomial.C_mul, Real.mul_self_sqrt hc]

/-- IsSOS is closed under addition -/
theorem IsSOS_add {p q : MvPolynomial (Fin n) ℝ} (hp : IsSOS p) (hq : IsSOS q) :
    IsSOS (p + q) := by
  obtain ⟨m₁, f₁, rfl⟩ := hp
  obtain ⟨m₂, f₂, rfl⟩ := hq
  exact ⟨m₁ + m₂, Fin.append f₁ f₂, by
    rw [Fin.sum_univ_add]; simp [Fin.append]⟩

/-- IsSOS is closed under nonneg scalar multiplication: if c ≥ 0 and p is SOS, then C(c)·p is SOS -/
theorem IsSOS_nonneg_scale {p : MvPolynomial (Fin n) ℝ} (hp : IsSOS p)
    (c : ℝ) (hc : 0 ≤ c) : IsSOS (MvPolynomial.C c * p) := by
  obtain ⟨m, f, rfl⟩ := hp
  refine ⟨m, fun i => MvPolynomial.C (Real.sqrt c) * f i, ?_⟩
  simp only [Finset.mul_sum, mul_pow, ← MvPolynomial.C_pow]
  congr 1; ext i
  congr 1
  rw [Real.sq_sqrt hc]

/-- A finite sum of SOS polynomials is SOS -/
theorem IsSOS_sum_finset {ι : Type*} {s : Finset ι}
    {f : ι → MvPolynomial (Fin n) ℝ} (hf : ∀ i ∈ s, IsSOS (f i)) :
    IsSOS (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact ⟨0, Fin.elim0, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsSOS_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Product of two SOS polynomials is SOS.
    Proof: (∑ aᵢ²)(∑ bⱼ²) = ∑ᵢ ∑ⱼ (aᵢ·bⱼ)². -/
theorem IsSOS_mul {p q : MvPolynomial (Fin n) ℝ} (hp : IsSOS p) (hq : IsSOS q) :
    IsSOS (p * q) := by
  obtain ⟨m₁, f, rfl⟩ := hp
  obtain ⟨m₂, g, rfl⟩ := hq
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← mul_pow]
  apply IsSOS_sum_finset
  intro i _
  apply IsSOS_sum_finset
  intro j _
  exact ⟨1, fun _ => f i * g j, by simp⟩

/-- A finite product of SOS polynomials is SOS -/
theorem IsSOS_finset_prod {ι : Type*} {s : Finset ι}
    {f : ι → MvPolynomial (Fin n) ℝ} (hf : ∀ i ∈ s, IsSOS (f i)) :
    IsSOS (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty]; exact ⟨1, fun _ => 1, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact IsSOS_mul (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem IsSOS_add_sq {p : MvPolynomial (Fin n) ℝ} (hp : IsSOS p)
    (c : MvPolynomial (Fin n) ℝ) : IsSOS (p + c ^ 2) := by
  obtain ⟨m, q, rfl⟩ := hp
  refine ⟨m + 1, Fin.snoc q c, ?_⟩
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]


end OptimalConvergenceRates

end
