/-
  OptimalConvergenceRates/BasicNotions/GeneralConeOps.lean

  Reusable constructors and evaluation lemmas for generalized quadratic modules.
-/
import OptimalConvergenceRates.BasicNotions.GeneralCones

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates

variable {n m : ℕ}

/-- An SOS polynomial is a free term in every generalized quadratic module. -/
theorem genQuadraticModule_sos
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : IsSOS p) (hdegree : p.totalDegree ≤ r) :
    p ∈ GenQuadraticModule g r := by
  refine ⟨p, 0, hp, fun _ ↦ IsSOS_zero, hdegree, ?_, ?_⟩
  · intro i
    simp
  · simp

/-- A nonnegative constant has a degree-zero generalized quadratic-module certificate. -/
theorem genQuadraticModule_C_nonneg
    (g : Fin m → MvPolynomial (Fin n) ℝ) {c : ℝ} (hc : 0 ≤ c) :
    C c ∈ GenQuadraticModule g 0 :=
  genQuadraticModule_sos g (IsSOS_C_nonneg c hc) (by simp)

/-- Zero has a degree-zero generalized quadratic-module certificate. -/
theorem genQuadraticModule_zero (g : Fin m → MvPolynomial (Fin n) ℝ) :
    0 ∈ GenQuadraticModule g 0 := by
  simpa using genQuadraticModule_C_nonneg g (c := 0) (le_refl 0)

/-- One has a degree-zero generalized quadratic-module certificate. -/
theorem genQuadraticModule_one (g : Fin m → MvPolynomial (Fin n) ℝ) :
    1 ∈ GenQuadraticModule g 0 := by
  simpa using genQuadraticModule_C_nonneg g (c := 1) (by norm_num)

/-- A generator belongs at its own total degree. -/
theorem genQuadraticModule_generator
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    g i ∈ GenQuadraticModule g (g i).totalDegree := by
  classical
  refine ⟨0, Function.update 0 i 1, IsSOS_zero, ?_, by simp, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa using IsSOS_sq (1 : MvPolynomial (Fin n) ℝ)
    · simp [Function.update_of_ne hji, IsSOS_zero]
  · intro j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji]
  · rw [zero_add, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Function.update_of_ne hji]
    · simp

/-- Addition with two possibly different truncation orders. -/
theorem genQuadraticModule_add
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (hp : p ∈ GenQuadraticModule g r) (hq : q ∈ GenQuadraticModule g s) :
    p + q ∈ GenQuadraticModule g (max r s) :=
  GenQuadraticModule_add
    (GenQuadraticModule_mono (Nat.le_max_left r s) hp)
    (GenQuadraticModule_mono (Nat.le_max_right r s) hq)

/-- A finite sum of certificates at one common order is again a certificate. -/
theorem genQuadraticModule_sum
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hp : ∀ i ∈ s, p i ∈ GenQuadraticModule g r) :
    ∑ i ∈ s, p i ∈ GenQuadraticModule g r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using GenQuadraticModule_mono (Nat.zero_le r) (genQuadraticModule_zero g)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact GenQuadraticModule_add (hp a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ hp i (Finset.mem_insert_of_mem hi))

/-- Multiplication by an SOS polynomial preserves a generalized quadratic module and adds
the total degree of the multiplier to the truncation order. -/
theorem genQuadraticModule_sos_mul
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : IsSOS p) (hq : q ∈ GenQuadraticModule g r) :
    p * q ∈ GenQuadraticModule g (r + p.totalDegree) := by
  obtain ⟨τ₀, τ, hτ₀, hτ, hdegree₀, hdegree, hq⟩ := hq
  refine ⟨p * τ₀, fun i ↦ p * τ i, IsSOS_mul hp hτ₀,
    fun i ↦ IsSOS_mul hp (hτ i), ?_, ?_, ?_⟩
  · calc
      (p * τ₀).totalDegree ≤ p.totalDegree + τ₀.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ p.totalDegree + r := Nat.add_le_add_left hdegree₀ _
      _ = r + p.totalDegree := Nat.add_comm _ _
  · intro i
    calc
      (p * τ i * g i).totalDegree = (p * (τ i * g i)).totalDegree := by ring
      _ ≤ p.totalDegree + (τ i * g i).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ p.totalDegree + r := Nat.add_le_add_left (hdegree i) _
      _ = r + p.totalDegree := Nat.add_comm _ _
  · rw [hq, mul_add, Finset.mul_sum]
    simp only [mul_assoc]

/-- A single SOS multiple of a generator is a generalized quadratic-module term. -/
theorem genQuadraticModule_sos_mul_generator
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsSOS p) :
    p * g i ∈ GenQuadraticModule g ((p * g i).totalDegree) := by
  classical
  refine ⟨0, Function.update 0 i p, IsSOS_zero, ?_, by simp, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa using hp
    · simp [Function.update_of_ne hji, IsSOS_zero]
  · intro j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji]
  · rw [zero_add, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Function.update_of_ne hji]
    · simp

/-- Combine two square bounds, retaining an explicit truncation order. -/
theorem genQuadraticModule_mul_square_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {A B : ℝ} {a b : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (hB : 0 ≤ B)
    (ha : C A - a ^ 2 ∈ GenQuadraticModule g r)
    (hb : C B - b ^ 2 ∈ GenQuadraticModule g s) :
    C (A * B) - (a * b) ^ 2 ∈
      GenQuadraticModule g (max r (s + (a ^ 2).totalDegree)) := by
  have hleft := genQuadraticModule_sos_mul (IsSOS_C_nonneg B hB) ha
  have hright := genQuadraticModule_sos_mul (IsSOS_sq a) hb
  have hsum := genQuadraticModule_add hleft hright
  convert hsum using 1
  · simp
  · simp only [map_mul]
    ring

/-- Every generalized quadratic-module element is nonnegative wherever all generators are
nonnegative. -/
theorem GenQuadraticModule.eval_nonneg
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : p ∈ GenQuadraticModule g r) (x : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ MvPolynomial.eval x (g i)) :
    0 ≤ MvPolynomial.eval x p := by
  obtain ⟨σ₀, σ, hσ₀, hσ, -, -, rfl⟩ := hp
  rw [MvPolynomial.eval_add, MvPolynomial.eval_sum]
  apply add_nonneg
  · exact IsSOS_nonneg σ₀ hσ₀ x (Set.mem_univ x)
  · apply Finset.sum_nonneg
    intro i _
    rw [MvPolynomial.eval_mul]
    exact mul_nonneg (IsSOS_nonneg (σ i) (hσ i) x (Set.mem_univ x)) (hg i)

end OptimalConvergenceRates

end
