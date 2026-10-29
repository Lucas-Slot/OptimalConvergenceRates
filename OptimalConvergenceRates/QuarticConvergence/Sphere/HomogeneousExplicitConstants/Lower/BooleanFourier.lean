import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.BooleanAlgebra

/-! Finite real Fourier analysis on the Boolean cube. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators symmDiff

def booleanSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem booleanSign_false : booleanSign false = 1 := rfl
@[simp] theorem booleanSign_true : booleanSign true = -1 := rfl

@[simp] theorem booleanSign_sq (b : Bool) : booleanSign b ^ 2 = 1 := by
  cases b <;> norm_num [booleanSign]

@[simp] theorem booleanSign_abs (b : Bool) : |booleanSign b| = 1 := by
  cases b <;> norm_num [booleanSign]

section Fourier

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeSize (I : Type*) [Fintype I] : ℝ := (2 : ℝ) ^ Fintype.card I

omit [DecidableEq I] in
theorem cubeSize_pos : 0 < cubeSize I := by
  unfold cubeSize
  positivity

omit [DecidableEq I] in
theorem cubeSize_ne_zero : cubeSize I ≠ 0 := ne_of_gt cubeSize_pos

def cubeCharacter (S : Finset I) (x : I → Bool) : ℝ :=
  booleanCharacter (fun i ↦ booleanSign (x i)) S

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeCharacter_empty (x : I → Bool) : cubeCharacter ∅ x = 1 := by
  simp [cubeCharacter]

omit [Fintype I] in
theorem cubeCharacter_mul (S T : Finset I) (x : I → Bool) :
    cubeCharacter S x * cubeCharacter T x = cubeCharacter (S ∆ T) x :=
  booleanCharacter_mul _ (fun _ ↦ booleanSign_sq _) S T

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeCharacter_abs (S : Finset I) (x : I → Bool) :
    |cubeCharacter S x| = 1 := by
  simp [cubeCharacter, booleanCharacter, Finset.abs_prod]

theorem cubeCharacter_eq_prod (S : Finset I) (x : I → Bool) :
    cubeCharacter S x = ∏ i, if i ∈ S then booleanSign (x i) else 1 := by
  exact (Fintype.prod_ite_mem S _).symm

theorem sum_cubeCharacter (S : Finset I) :
    (∑ x : I → Bool, cubeCharacter S x) =
      if S = ∅ then cubeSize I else 0 := by
  classical
  calc
    (∑ x : I → Bool, cubeCharacter S x) =
        ∑ x : I → Bool, ∏ i, if i ∈ S then booleanSign (x i) else 1 := by
      simp_rw [cubeCharacter_eq_prod]
    _ = ∏ i, ∑ b : Bool, if i ∈ S then booleanSign b else 1 := by
      exact (Fintype.prod_sum fun i (b : Bool) ↦
        if i ∈ S then booleanSign b else (1 : ℝ)).symm
    _ = ∏ i : I, if i ∈ S then (0 : ℝ) else 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : i ∈ S <;> simp [h, Fintype.sum_bool]
    _ = if S = ∅ then cubeSize I else 0 := by
      by_cases hS : S = ∅
      · subst S
        simp [cubeSize]
      · rw [ite_eq_right hS]
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Orthogonality of the real Boolean characters under counting measure. -/
theorem cubeCharacter_orthogonality (S T : Finset I) :
    (∑ x : I → Bool, cubeCharacter S x * cubeCharacter T x) =
      if S = T then cubeSize I else 0 := by
  simp_rw [cubeCharacter_mul]
  rw [sum_cubeCharacter]
  simp

/-- The dual delta identity, with the summation running over all subsets. -/
theorem cubeCharacter_dual_orthogonality (x y : I → Bool) :
    (∑ S : Finset I, cubeCharacter S x * cubeCharacter S y) =
      if x = y then cubeSize I else 0 := by
  classical
  have hprod : (∑ S : Finset I, cubeCharacter S x * cubeCharacter S y) =
      ∏ i, (booleanSign (x i) * booleanSign (y i) + 1) := by
    rw [Fintype.prod_add]
    apply Finset.sum_congr rfl
    intro S hS
    simp only [Finset.prod_const_one, mul_one]
    exact (Finset.prod_mul_distrib).symm
  have hcoord (i : I) : booleanSign (x i) * booleanSign (y i) + 1 =
      if x i = y i then (2 : ℝ) else 0 := by
    cases x i <;> cases y i <;> norm_num [booleanSign]
  rw [hprod]
  simp_rw [hcoord]
  by_cases hxy : x = y
  · subst y
    simp [cubeSize]
  · rw [ite_eq_right hxy]
    have hne : ¬ ∀ i, x i = y i := fun h ↦ hxy (funext h)
    push_neg at hne
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

def cubeFourierCoeff (f : (I → Bool) → ℝ) (S : Finset I) : ℝ :=
  (cubeSize I)⁻¹ * ∑ x, f x * cubeCharacter S x

theorem cubeFourier_inversion (f : (I → Bool) → ℝ) (x : I → Bool) :
    (∑ S : Finset I, cubeFourierCoeff f S * cubeCharacter S x) = f x := by
  classical
  calc
    (∑ S : Finset I, cubeFourierCoeff f S * cubeCharacter S x) =
        ∑ S : Finset I, ∑ y : I → Bool,
          (cubeSize I)⁻¹ * f y * (cubeCharacter S y * cubeCharacter S x) := by
      apply Finset.sum_congr rfl
      intro S hS
      unfold cubeFourierCoeff
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ = ∑ y : I → Bool, ∑ S : Finset I,
        (cubeSize I)⁻¹ * f y * (cubeCharacter S y * cubeCharacter S x) :=
      Finset.sum_comm
    _ = ∑ y : I → Bool, (cubeSize I)⁻¹ * f y *
        (∑ S : Finset I, cubeCharacter S y * cubeCharacter S x) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ y : I → Bool, (cubeSize I)⁻¹ * f y *
        (if y = x then cubeSize I else 0) := by
      simp_rw [cubeCharacter_dual_orthogonality]
    _ = ∑ y : I → Bool, if y = x then f x else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hyx : y = x
      · subst y
        simp only [ite_eq_left rfl]
        calc
          (cubeSize I)⁻¹ * f x * cubeSize I =
              ((cubeSize I)⁻¹ * cubeSize I) * f x := by ring
          _ = f x := by rw [inv_mul_cancel₀ cubeSize_ne_zero, one_mul]
      · simp [hyx]
    _ = f x := by simp

@[simp] theorem cubeFourierCoeff_character (S T : Finset I) :
    cubeFourierCoeff (cubeCharacter T) S = if S = T then 1 else 0 := by
  unfold cubeFourierCoeff
  rw [cubeCharacter_orthogonality]
  by_cases h : S = T
  · subst T
    simp [cubeSize_ne_zero]
  · simp [h, Ne.symm h]

@[simp] theorem cubeFourierCoeff_zero (S : Finset I) :
    cubeFourierCoeff (fun _ : I → Bool ↦ 0) S = 0 := by
  simp [cubeFourierCoeff]

theorem cubeFourierCoeff_add (f g : (I → Bool) → ℝ) (S : Finset I) :
    cubeFourierCoeff (fun x ↦ f x + g x) S =
      cubeFourierCoeff f S + cubeFourierCoeff g S := by
  simp [cubeFourierCoeff, add_mul, Finset.sum_add_distrib, mul_add]

theorem cubeFourierCoeff_smul (c : ℝ) (f : (I → Bool) → ℝ) (S : Finset I) :
    cubeFourierCoeff (fun x ↦ c * f x) S = c * cubeFourierCoeff f S := by
  unfold cubeFourierCoeff
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

theorem cubeFourierCoeff_sum {J : Type*} [Fintype J]
    (f : J → (I → Bool) → ℝ) (S : Finset I) :
    cubeFourierCoeff (fun x ↦ ∑ j, f j x) S = ∑ j, cubeFourierCoeff (f j) S := by
  unfold cubeFourierCoeff
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

def cubeSynthesis (c : Finset I → ℝ) (x : I → Bool) : ℝ :=
  ∑ S, c S * cubeCharacter S x

@[simp] theorem cubeFourierCoeff_synthesis (c : Finset I → ℝ) (S : Finset I) :
    cubeFourierCoeff (cubeSynthesis c) S = c S := by
  unfold cubeSynthesis
  rw [cubeFourierCoeff_sum]
  simp_rw [cubeFourierCoeff_smul, cubeFourierCoeff_character]
  simp [mul_ite]

/-- The characters give a unique linear coordinate system for all Boolean
functions, not just for functions already supplied with an expansion. -/
def cubeFourierEquiv : ((I → Bool) → ℝ) ≃ₗ[ℝ] (Finset I → ℝ) where
  toFun := cubeFourierCoeff
  invFun := cubeSynthesis
  left_inv f := funext (cubeFourier_inversion f)
  right_inv c := funext (cubeFourierCoeff_synthesis c)
  map_add' f g := funext (cubeFourierCoeff_add f g)
  map_smul' c f := funext (cubeFourierCoeff_smul c f)

def cubeCharacterBasis : Module.Basis (Finset I) ℝ ((I → Bool) → ℝ) :=
  (Pi.basisFun ℝ (Finset I)).map cubeFourierEquiv.symm

@[simp] theorem cubeCharacterBasis_apply (S : Finset I) :
    cubeCharacterBasis S = cubeCharacter S := by
  ext x
  change cubeSynthesis ((Pi.basisFun ℝ (Finset I)) S) x = cubeCharacter S x
  rw [Pi.basisFun_apply]
  simp [cubeSynthesis, Pi.single_apply]

/-- Fourier degree uses the actual coordinate support of each character. -/
def HasBooleanDegree (d : ℕ) (f : (I → Bool) → ℝ) : Prop :=
  ∀ S : Finset I, d < S.card → cubeFourierCoeff f S = 0

def booleanDegreeSpace (d : ℕ) : Submodule ℝ ((I → Bool) → ℝ) where
  carrier := HasBooleanDegree d
  zero_mem' S hS := cubeFourierCoeff_zero S
  add_mem' {f g} hf hg S hS := by
    change cubeFourierCoeff (fun x ↦ f x + g x) S = 0
    rw [cubeFourierCoeff_add, hf S hS, hg S hS, add_zero]
  smul_mem' c f hf S hS := by
    change cubeFourierCoeff (fun x ↦ c * f x) S = 0
    rw [cubeFourierCoeff_smul, hf S hS, mul_zero]

abbrev BooleanIndex (I : Type*) (d : ℕ) := { S : Finset I // S.card ≤ d }

theorem cubeFourier_inversion_truncated (d : ℕ) (f : (I → Bool) → ℝ)
    (hf : HasBooleanDegree d f) (x : I → Bool) :
    (∑ S : BooleanIndex I d, cubeFourierCoeff f S.val * cubeCharacter S.val x) =
      f x := by
  classical
  calc
    (∑ S : BooleanIndex I d, cubeFourierCoeff f S.val * cubeCharacter S.val x) =
        ∑ S ∈ Finset.univ.filter (fun S : Finset I ↦ S.card ≤ d),
          cubeFourierCoeff f S * cubeCharacter S x :=
      (Finset.sum_subtype
        (Finset.univ.filter (fun S : Finset I ↦ S.card ≤ d))
        (by intro S; simp)
        (fun S ↦ cubeFourierCoeff f S * cubeCharacter S x)).symm
    _ = ∑ S : Finset I, cubeFourierCoeff f S * cubeCharacter S x := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro S hS hnot
      have hlarge : d < S.card := by simpa using hnot
      rw [hf S hlarge, zero_mul]
    _ = f x := cubeFourier_inversion f x

theorem cubeFourierCoeff_abs_le (f : (I → Bool) → ℝ) (B : ℝ)
    (hB : ∀ x, |f x| ≤ B) (S : Finset I) : |cubeFourierCoeff f S| ≤ B := by
  have hsum : |∑ x : I → Bool, f x * cubeCharacter S x| ≤ cubeSize I * B := by
    calc
      |∑ x : I → Bool, f x * cubeCharacter S x| ≤
          ∑ x : I → Bool, |f x * cubeCharacter S x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : I → Bool, B := by
        apply Finset.sum_le_sum
        intro x hx
        simpa only [abs_mul, cubeCharacter_abs, mul_one] using hB x
      _ = cubeSize I * B := by simp [cubeSize, Fintype.card_fun]
  unfold cubeFourierCoeff
  rw [abs_mul, abs_inv, abs_of_pos cubeSize_pos]
  calc
    (cubeSize I)⁻¹ * |∑ x, f x * cubeCharacter S x| ≤
        (cubeSize I)⁻¹ * (cubeSize I * B) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr cubeSize_pos.le)
    _ = B := by rw [← mul_assoc, inv_mul_cancel₀ cubeSize_ne_zero, one_mul]

theorem cubeFourier_sum_abs_le (f : (I → Bool) → ℝ) (B : ℝ)
    (hB : ∀ x, |f x| ≤ B) :
    (∑ S : Finset I, |cubeFourierCoeff f S|) ≤ cubeSize I * B := by
  calc
    (∑ S : Finset I, |cubeFourierCoeff f S|) ≤ ∑ _S : Finset I, B :=
      Finset.sum_le_sum (fun S _ ↦ cubeFourierCoeff_abs_le f B hB S)
    _ = cubeSize I * B := by simp [cubeSize, Fintype.card_finset]

end Fourier

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
