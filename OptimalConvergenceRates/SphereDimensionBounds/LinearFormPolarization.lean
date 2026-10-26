import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
/-! Finite polarization into powers of linear forms. The alternating
multiset proof follows the PolynomialMoments development. No quantitative
polarization bound is used. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.LinearFormPolarization
open scoped BigOperators
open MvPolynomial Finset

def linearFormPolynomial {n : ℕ} (z : Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i,C (z i)*X i

@[simp] theorem linearFormPolynomial_eval {n : ℕ} (z x : Fin n → ℝ) :
    eval x (linearFormPolynomial z)=∑ i,z i*x i := by
  simp [linearFormPolynomial]

theorem multiset_sum_map_X_eq_linearFormPolynomial_count {n : ℕ}
    (s : Multiset (Fin n)) :
    (s.map (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))).sum =
      linearFormPolynomial (fun i ↦ (s.count i : ℝ)) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [linearFormPolynomial]
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      simp only [linearFormPolynomial, Multiset.count_cons, Nat.cast_add,
        Nat.cast_ite, Nat.cast_one]
      simp_rw [map_add, add_mul]
      rw [Finset.sum_add_distrib]
      simp [eq_comm, add_comm]

/-- Alternating sum underlying the polarization identity. Using
`s.card + t.card` in the sign makes the powerset recursion subtraction-free;
it has the same parity as `s.card - t.card` whenever `t ≤ s`. -/
def polarizationAlternatingSum {R : Type*} [CommRing R]
    (s : Multiset R) (m : ℕ) : R :=
  (s.powerset.map fun t ↦
    (-1 : R) ^ (s.card + t.card) * t.sum ^ m).sum

theorem polarizationAlternatingSum_cons {R : Type*} [CommRing R]
    (a : R) (s : Multiset R) (m : ℕ) :
    polarizationAlternatingSum (a ::ₘ s) m =
      (s.powerset.map fun t ↦
        (-1 : R) ^ (s.card + t.card) *
          ((a + t.sum) ^ m - t.sum ^ m)).sum := by
  have hneg (p q : ℕ) :
      (-1 : R) ^ (p + 1 + q) = -((-1 : R) ^ (p + q)) := by
    rw [show p + 1 + q = (p + q) + 1 by omega, pow_succ]
    simp
  have hpos (p q : ℕ) :
      (-1 : R) ^ (p + 1 + (q + 1)) = (-1 : R) ^ (p + q) := by
    rw [show p + 1 + (q + 1) = (p + q) + 2 by omega, pow_add]
    simp
  simp only [polarizationAlternatingSum, Multiset.powerset_cons,
    Multiset.card_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Multiset.sum_cons]
  simp_rw [hpos s.card, hneg s.card]
  generalize s.powerset = u
  induction u using Multiset.induction_on with
  | empty => simp
  | @cons t u ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      linear_combination ih

theorem multiset_sum_map_finset_sum {α β R : Type*} [AddCommMonoid R]
    (s : Multiset α) (u : Finset β) (f : α → β → R) :
    (s.map (fun a => ∑ b ∈ u,f a b)).sum=
      ∑ b ∈ u,(s.map (fun a => f a b)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons,ih,Finset.sum_add_distrib]

/-- A binomial expansion turns one further powerset difference into lower
alternating sums. -/
theorem polarizationAlternatingSum_cons_eq_sum
    {R : Type*} [CommRing R] (a : R) (s : Multiset R) (m : ℕ) :
    polarizationAlternatingSum (a ::ₘ s) m =
      ∑ k ∈ Finset.range m,
        polarizationAlternatingSum s k *
          (a ^ (m - k) * (m.choose k : R)) := by
  rw [polarizationAlternatingSum_cons]
  have hdiff (b : R) :
      (a + b) ^ m - b ^ m =
        ∑ k ∈ Finset.range m,
          b ^ k * a ^ (m - k) * (m.choose k : R) := by
    rw [add_comm, add_pow, Finset.sum_range_succ]
    simp
  simp_rw [hdiff, mul_sum]
  rw [multiset_sum_map_finset_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  calc
    (s.powerset.map fun t ↦
        (-1 : R) ^ (s.card + t.card) *
          (t.sum ^ k * a ^ (m - k) * (m.choose k : R))).sum =
        (s.powerset.map fun t ↦
          ((-1 : R) ^ (s.card + t.card) * t.sum ^ k) *
            (a ^ (m - k) * (m.choose k : R))).sum := by
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro t _ht
      ring
    _ = polarizationAlternatingSum s k *
          (a ^ (m - k) * (m.choose k : R)) := by
      rw [Multiset.sum_map_mul_right]
      rfl

theorem polarizationAlternatingSum_eq_zero_of_lt
    {R : Type*} [CommRing R] (s : Multiset R) {m : ℕ}
    (hm : m < s.card) :
    polarizationAlternatingSum s m = 0 := by
  induction s using Multiset.induction_on generalizing m with
  | empty => simp at hm
  | @cons a s ih =>
      rw [polarizationAlternatingSum_cons_eq_sum]
      apply Finset.sum_eq_zero
      intro k hk
      have hkm : k < m := Finset.mem_range.mp hk
      have hms : m ≤ s.card := by
        simpa only [Multiset.card_cons, Nat.lt_succ_iff] using hm
      have hks : k < s.card := by omega
      rw [ih hks, zero_mul]

/-- The full-cardinality alternating sum retains exactly the term using
every factor, with coefficient `s.card!`. -/
theorem polarizationAlternatingSum_card_eq_factorial_mul_prod
    {R : Type*} [CommRing R] (s : Multiset R) :
    polarizationAlternatingSum s s.card =
      (s.card.factorial : R) * s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp [polarizationAlternatingSum]
  | @cons a s ih =>
      rw [polarizationAlternatingSum_cons_eq_sum]
      simp only [Multiset.card_cons, Finset.sum_range_succ]
      have hzero :
          (∑ k ∈ Finset.range s.card,
            polarizationAlternatingSum s k *
              (a ^ (s.card + 1 - k) *
                ((s.card + 1).choose k : R))) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [polarizationAlternatingSum_eq_zero_of_lt s
          (Finset.mem_range.mp hk), zero_mul]
      rw [hzero, zero_add, ih]
      simp only [Nat.add_sub_cancel_left, pow_one, Multiset.prod_cons,
        Nat.factorial_succ]
      rw [show (s.card + 1).choose s.card = s.card + 1 by
        exact Nat.choose_succ_self_right s.card]
      push_cast
      ring

theorem multiset_powerset_map {α β : Type*}
    (f : α → β) (s : Multiset α) :
    (s.map f).powerset = s.powerset.map (Multiset.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.powerset_cons, ih,
        Multiset.map_add, Multiset.map_map, Function.comp_apply]

theorem neg_one_pow_card_add_eq_sub {R : Type*} [CommRing R]
    {s t : Multiset R} (ht : t ≤ s) :
    (-1 : R) ^ (s.card + t.card) =
      (-1 : R) ^ (s.card - t.card) := by
  have hle : t.card ≤ s.card := Multiset.card_le_card ht
  have hcard :
      s.card + t.card = (s.card - t.card) + 2 * t.card := by
    omega
  rw [hcard, pow_add]
  have heven : (-1 : R) ^ (2 * t.card) = 1 := by
    rw [pow_mul]
    simp
  rw [heven, mul_one]

theorem mvPolynomial_multiset_prod_eq_polarization {n : ℕ}
    (u : Multiset (MvPolynomial (Fin n) ℝ)) :
    u.prod =
      (u.powerset.map fun t ↦
        MvPolynomial.C
            ((u.card.factorial : ℝ)⁻¹ *
              (-1 : ℝ) ^ (u.card - t.card)) *
          t.sum ^ u.card).sum := by
  symm
  calc
    (u.powerset.map fun t ↦
        MvPolynomial.C
            ((u.card.factorial : ℝ)⁻¹ *
              (-1 : ℝ) ^ (u.card - t.card)) *
          t.sum ^ u.card).sum =
        MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
          polarizationAlternatingSum u u.card := by
      calc
        _ = (u.powerset.map fun t ↦
            MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
              ((-1 : MvPolynomial (Fin n) ℝ) ^ (u.card + t.card) *
                t.sum ^ u.card)).sum := by
          apply congrArg Multiset.sum
          apply Multiset.map_congr rfl
          intro t ht
          have htu : t ≤ u := Multiset.mem_powerset.mp ht
          simp only [map_mul, map_pow, map_neg, map_one]
          rw [← neg_one_pow_card_add_eq_sub
            (R := MvPolynomial (Fin n) ℝ) htu]
          ring
        _ = MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
              (u.powerset.map fun t ↦
                (-1 : MvPolynomial (Fin n) ℝ) ^ (u.card + t.card) *
                  t.sum ^ u.card).sum := Multiset.sum_map_mul_left
        _ = _ := rfl
    _ = MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
          ((u.card.factorial : MvPolynomial (Fin n) ℝ) * u.prod) := by
      rw [polarizationAlternatingSum_card_eq_factorial_mul_prod]
    _ = u.prod := by
      rw [← mul_assoc]
      have hfactorial : (u.card.factorial : ℝ) ≠ 0 := by positivity
      have hcancel :
          MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
              (u.card.factorial : MvPolynomial (Fin n) ℝ) = 1 := by
        change MvPolynomial.C (u.card.factorial : ℝ)⁻¹ *
          MvPolynomial.C (u.card.factorial : ℝ) = 1
        rw [← map_mul, inv_mul_cancel₀ hfactorial, map_one]
      rw [hcancel, one_mul]

/-- The explicit alternating-submultiset polarization identity. Duplicate
submultisets retain their multiplicity in `Multiset.powerset`, as required for
repeated factors. -/
theorem multiset_prod_map_X_eq_polarization {n : ℕ}
    (s : Multiset (Fin n)) :
    (s.map (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))).prod =
      (s.powerset.map fun t ↦
        MvPolynomial.C
            ((s.card.factorial : ℝ)⁻¹ * (-1 : ℝ) ^ (s.card - t.card)) *
          (linearFormPolynomial (fun i ↦ (t.count i : ℝ))) ^ s.card).sum := by
  classical
  have h := mvPolynomial_multiset_prod_eq_polarization
    (s.map (fun i ↦
      (MvPolynomial.X i : MvPolynomial (Fin n) ℝ)))
  simpa only [multiset_powerset_map, Multiset.map_map,
    Function.comp_apply, Multiset.card_map,
    multiset_sum_map_X_eq_linearFormPolynomial_count] using h

/-- The product of the variables in an index multiset is its associated
monomial. -/
theorem multiset_prod_map_X_eq_monomial_toFinsupp {n : ℕ}
    (s : Multiset (Fin n)) :
    (s.map (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))).prod =
      MvPolynomial.monomial s.toFinsupp (1 : ℝ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih]
      rw [show (a ::ₘ s).toFinsupp =
        s.toFinsupp + Finsupp.single a 1 by
          rw [show a ::ₘ s = ({a} : Multiset (Fin n)) + s by rfl,
            Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
          exact add_comm _ _]
      rw [MvPolynomial.monomial_add_single]
      simp [mul_comm]

/-- The subspace spanned by `d`-th powers of the repository's linear-form
polynomials. -/
noncomputable def linearFormPowSpan (n d : ℕ) :
    Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  Submodule.span ℝ
    {q | ∃ z : Fin n → ℝ, q = (linearFormPolynomial z) ^ d}

/-- Monomial form of the polarization identity: `∏ ℓᵢ` lies in the span of
`d`-th powers of sums of the `ℓᵢ`. The proof applies the explicit alternating
subset formula to `s.toMultiset`; the preceding count lemma identifies every
subset sum with a `linearFormPolynomial`. -/
theorem monomial_mem_linearFormPowSpan {n : ℕ} (s : Fin n →₀ ℕ) :
    MvPolynomial.monomial s (1 : ℝ) ∈ linearFormPowSpan n s.degree := by
  classical
  let u : Multiset (Fin n) := s.toMultiset
  have hu : u.toFinsupp = s := by
    simp [u]
  have hcard : u.card = s.degree := by
    change s.toMultiset.card = ∑ i ∈ s.support, s i
    exact Finsupp.card_toMultiset s
  have hprod :
      (u.map (fun i ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℝ))).prod =
        MvPolynomial.monomial s (1 : ℝ) := by
    rw [multiset_prod_map_X_eq_monomial_toFinsupp, hu]
  rw [← hprod, multiset_prod_map_X_eq_polarization]
  induction u.powerset using Multiset.induction_on with
  | empty =>
      simp only [Multiset.map_zero, Multiset.sum_zero]
      exact (linearFormPowSpan n s.degree).zero_mem
  | @cons t ts ih =>
      rw [Multiset.map_cons, Multiset.sum_cons]
      apply (linearFormPowSpan n s.degree).add_mem
      · rw [← MvPolynomial.smul_eq_C_mul]
        apply (linearFormPowSpan n s.degree).smul_mem
        apply Submodule.subset_span
        refine ⟨fun i ↦ (t.count i : ℝ), ?_⟩
        rw [hcard]
      · exact ih

/-- Pure polarization identity: over the reals, every homogeneous polynomial
is a finite linear combination of powers of linear forms. -/
theorem exists_fin_sum_linearForm_pow_eq_of_isHomogeneous
    {n d : ℕ} (v : MvPolynomial (Fin n) ℝ) (hv : v.IsHomogeneous d) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (z : Fin N → Fin n → ℝ),
      v = ∑ j, MvPolynomial.C (c j) * (linearFormPolynomial (z j)) ^ d := by
  have hvspan : v ∈ linearFormPowSpan n d := by
    rw [v.as_sum]
    apply Submodule.sum_mem
    intro s hs
    have hcoeff : v.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hsdeg : s.degree = d := by
      by_contra hne
      exact hcoeff (hv.coeff_eq_zero hne)
    have hmono : MvPolynomial.monomial s (1 : ℝ) ∈ linearFormPowSpan n d := by
      simpa only [hsdeg] using monomial_mem_linearFormPowSpan s
    have hsmul := (linearFormPowSpan n d).smul_mem (v.coeff s) hmono
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using hsmul
  rcases Submodule.mem_span_set'.mp hvspan with ⟨N, c, g, hg⟩
  let z : Fin N → Fin n → ℝ := fun j ↦ Classical.choose (g j).2
  have hgz (j : Fin N) :
      (g j).1 = (linearFormPolynomial (z j)) ^ d := by
    exact Classical.choose_spec (g j).2
  refine ⟨N, c, z, ?_⟩
  calc
    v = ∑ j, c j • (g j).1 := hg.symm
    _ = ∑ j, MvPolynomial.C (c j) * (linearFormPolynomial (z j)) ^ d := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hgz]
      rw [MvPolynomial.smul_eq_C_mul]


end OptimalConvergenceRates.SphereDimensionBounds.LinearFormPolarization
