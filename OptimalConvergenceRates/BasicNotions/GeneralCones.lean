/-
  OptimalConvergenceRates/BasicNotions/GeneralCones.lean

  Generator-parametric preorderings and quadratic modules, with monotonicity and inclusion lemmas.
-/
import OptimalConvergenceRates.BasicNotions.SOS
import Mathlib.Data.Finset.Powerset

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n : ℕ}

/-! ## Generalized quadratic modules and preorderings -/

/-- A generalized quadratic module for arbitrary generators g₁,...,gₘ:
    QM(g)_r = { σ₀ + ∑ᵢ σᵢ · gᵢ : σᵢ SOS, deg(σ₀) ≤ r, deg(σᵢ · gᵢ) ≤ r }. -/
def GenQuadraticModule {m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ) (r : ℕ) :
    Set (MvPolynomial (Fin n) ℝ) :=
  { p | ∃ (σ₀ : MvPolynomial (Fin n) ℝ) (σ : Fin m → MvPolynomial (Fin n) ℝ),
    IsSOS σ₀ ∧
    (∀ i, IsSOS (σ i)) ∧
    σ₀.totalDegree ≤ r ∧
    (∀ i, (σ i * g i).totalDegree ≤ r) ∧
    p = σ₀ + ∑ i : Fin m, σ i * g i }

/-- A generalized preordering for arbitrary generators g₁,...,gₘ:
    T(g)_r = { ∑_{J ⊆ [m]} σ_J · ∏_{j ∈ J} gⱼ : σ_J SOS, deg(σ_J · g_J) ≤ r }. -/
def GenPreordering {m : ℕ} (g : Fin m → MvPolynomial (Fin n) ℝ) (r : ℕ) :
    Set (MvPolynomial (Fin n) ℝ) :=
  { p | ∃ (σ : Finset (Fin m) → MvPolynomial (Fin n) ℝ),
    (∀ J, IsSOS (σ J)) ∧
    (∀ J, (σ J * ∏ j ∈ J, g j).totalDegree ≤ r) ∧
    p = ∑ J ∈ Finset.univ.powerset, σ J * ∏ j ∈ J, g j }

/-- Closure of the generalized preordering under addition. -/
private theorem GenPreordering_add' {m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : p ∈ GenPreordering g r) (hq : q ∈ GenPreordering g r) :
    p + q ∈ GenPreordering g r := by
  obtain ⟨σ_p, hsos_p, hdeg_p, hsum_p⟩ := hp
  obtain ⟨σ_q, hsos_q, hdeg_q, hsum_q⟩ := hq
  refine ⟨fun J => σ_p J + σ_q J, ?_, ?_, ?_⟩
  · intro J; exact IsSOS_add (hsos_p J) (hsos_q J)
  · intro J
    calc ((σ_p J + σ_q J) * ∏ j ∈ J, g j).totalDegree
        = (σ_p J * ∏ j ∈ J, g j + σ_q J * ∏ j ∈ J, g j).totalDegree := by ring_nf
      _ ≤ max (σ_p J * ∏ j ∈ J, g j).totalDegree (σ_q J * ∏ j ∈ J, g j).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ r := max_le (hdeg_p J) (hdeg_q J)
  · rw [hsum_p, hsum_q, ← Finset.sum_add_distrib]
    congr 1; ext J; ring_nf

/-- Closure of GenPreordering under finite sums. -/
private theorem GenPreordering_sum' {m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hf : ∀ i ∈ s, f i ∈ GenPreordering g r) :
    ∑ i ∈ s, f i ∈ GenPreordering g r := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨0, fun _ => IsSOS_zero, fun _ => by simp, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact GenPreordering_add' (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The quadratic module is contained in the generalized preordering. -/
theorem GenQuadraticModule_subset_GenPreordering {m : ℕ}
    {g : Fin m → MvPolynomial (Fin n) ℝ} {r : ℕ} :
    GenQuadraticModule g r ⊆ GenPreordering g r := by
  intro p ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩
  rw [hsum]
  -- σ₀ ∈ GenPreordering: σ₀ = σ₀ * ∏_{j∈∅} g j
  have hσ₀ : σ₀ ∈ GenPreordering g r := by
    refine ⟨Function.update 0 ∅ σ₀, ?_, ?_, ?_⟩
    · intro J; by_cases hJ : J = ∅
      · subst hJ; rw [Function.update_self]; exact hsos₀
      · rw [Function.update_of_ne hJ, Pi.zero_apply]; exact IsSOS_zero
    · intro J; by_cases hJ : J = ∅
      · subst hJ; rw [Function.update_self, Finset.prod_empty, mul_one]; exact hdeg₀
      · rw [Function.update_of_ne hJ, Pi.zero_apply, zero_mul]; exact Nat.zero_le _
    · rw [Finset.sum_eq_single ∅
        (fun J _ hJ => by rw [Function.update_of_ne hJ, Pi.zero_apply, zero_mul])
        (fun h => absurd (Finset.mem_powerset.mpr (Finset.empty_subset _)) h)]
      rw [Function.update_self, Finset.prod_empty, mul_one]
  -- Each σ i * g i ∈ GenPreordering
  have hterm : ∀ i, σ i * g i ∈ GenPreordering g r := by
    intro i
    refine ⟨Function.update 0 {i} (σ i), ?_, ?_, ?_⟩
    · intro J; by_cases hJ : J = {i}
      · subst hJ; rw [Function.update_self]; exact hsos i
      · rw [Function.update_of_ne hJ, Pi.zero_apply]; exact IsSOS_zero
    · intro J; by_cases hJ : J = {i}
      · subst hJ; rw [Function.update_self, Finset.prod_singleton]; exact hdeg i
      · rw [Function.update_of_ne hJ, Pi.zero_apply, zero_mul]; exact Nat.zero_le _
    · rw [Finset.sum_eq_single {i}
        (fun J _ hJ => by rw [Function.update_of_ne hJ, Pi.zero_apply, zero_mul])
        (fun h => absurd (Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr
          (Finset.mem_univ i))) h)]
      rw [Function.update_self, Finset.prod_singleton]
  exact GenPreordering_add' hσ₀ (GenPreordering_sum' (fun i _ => hterm i))

/-- The generalized quadratic module is monotone in the degree parameter. -/
theorem GenQuadraticModule_mono {m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r s : ℕ} (hrs : r ≤ s) :
    GenQuadraticModule g r ⊆ GenQuadraticModule g s := by
  intro p ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩
  exact ⟨σ₀, σ, hsos₀, hsos, le_trans hdeg₀ hrs,
    fun i => le_trans (hdeg i) hrs, hsum⟩

/-- The generalized preordering is monotone in the degree parameter. -/
theorem GenPreordering_mono {m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {r s : ℕ} (hrs : r ≤ s) :
    GenPreordering g r ⊆ GenPreordering g s := by
  intro p ⟨σ, hsos, hdeg, hsum⟩
  exact ⟨σ, hsos, fun J => le_trans (hdeg J) hrs, hsum⟩

/-- The generalized quadratic module is closed under addition. -/
theorem GenQuadraticModule_add {m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : p ∈ GenQuadraticModule g r) (hq : q ∈ GenQuadraticModule g r) :
    p + q ∈ GenQuadraticModule g r := by
  obtain ⟨σ₀_p, σ_p, hsos₀_p, hsos_p, hdeg₀_p, hdeg_p, hsum_p⟩ := hp
  obtain ⟨σ₀_q, σ_q, hsos₀_q, hsos_q, hdeg₀_q, hdeg_q, hsum_q⟩ := hq
  refine ⟨σ₀_p + σ₀_q, fun i => σ_p i + σ_q i, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsSOS_add hsos₀_p hsos₀_q
  · intro i; exact IsSOS_add (hsos_p i) (hsos_q i)
  · exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le hdeg₀_p hdeg₀_q)
  · intro i
    calc ((σ_p i + σ_q i) * g i).totalDegree
        = (σ_p i * g i + σ_q i * g i).totalDegree := by ring_nf
      _ ≤ max (σ_p i * g i).totalDegree (σ_q i * g i).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ r := max_le (hdeg_p i) (hdeg_q i)
  · rw [hsum_p, hsum_q]
    simp only [add_mul, Finset.sum_add_distrib]; ring

/-- The generalized quadratic module is closed under nonneg scalar multiplication. -/
theorem GenQuadraticModule_nonneg_scale {m : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (hp : p ∈ GenQuadraticModule g r) :
    MvPolynomial.C c * p ∈ GenQuadraticModule g r := by
  obtain ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩ := hp
  refine ⟨MvPolynomial.C c * σ₀, fun i => MvPolynomial.C c * σ i, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsSOS_nonneg_scale hsos₀ c hc
  · intro i; exact IsSOS_nonneg_scale (hsos i) c hc
  · calc (MvPolynomial.C c * σ₀).totalDegree
        ≤ (MvPolynomial.C c).totalDegree + σ₀.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = σ₀.totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ r := hdeg₀
  · intro i
    calc (MvPolynomial.C c * σ i * g i).totalDegree
        = (MvPolynomial.C c * (σ i * g i)).totalDegree := by ring_nf
      _ ≤ (MvPolynomial.C c).totalDegree + (σ i * g i).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = (σ i * g i).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ r := hdeg i
  · rw [hsum, mul_add, Finset.mul_sum]; simp only [mul_assoc]


end OptimalConvergenceRates

end
