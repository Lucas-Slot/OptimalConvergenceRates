import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticPadding

/-! Singular extension of the SAME explicit global linear weighted
quadratic completion. No separate nonlinear completion is selected. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticSingular

set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators InnerProductSpace Topology
open WeightedQuadraticSplit WeightedQuadraticPadding

theorem diagonal_norm_mono {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) (x : Point (Fin n)) :
    ‖diagonal a x‖ ≤ ‖diagonal b x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq, norm_sq]
  apply Finset.sum_le_sum
  intro i _
  rw [diagonal_apply, diagonal_apply, mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (ha i) ((ha i).trans (hab i))).2 (hab i)) (sq_nonneg _)

theorem kernel_entry_zero {n : ℕ} (a : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    {D : ℝ} (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ x : Point (Fin n), |matrixForm S x x| ≤ D * ‖diagonal a x‖ * ‖x‖)
    (i j : Fin n) (hai : a i=0) (haj : a j=0) : S i j=0 := by
  have hi : diagonal a (EuclideanSpace.single i 1) = 0 := by
    rw [diagonal_single, hai]
    ext k
    simp
  have hj : diagonal a (EuclideanSpace.single j 1) = 0 := by
    rw [diagonal_single, haj]
    ext k
    simp
  have hk := kernel_vanishing (matrixForm S) (diagonal a) (matrixForm_symmetric S hS) hdom hi hj
  simpa only [matrixForm_single] using hk

theorem active_entry_zero {n : ℕ} (a : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) {D : ℝ} (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ x : Point (Fin n), |matrixForm S x x| ≤ D * ‖diagonal a x‖ * ‖x‖)
    (i j : Fin n) (hij : i.val≤j.val) (hai : a i=0) : S i j=0 := by
  have haj : a j=0 := le_antisymm
    (by simpa only [hai] using hmono (Fin.le_iff_val_le_val.mpr hij)) (ha j)
  exact kernel_entry_zero a S hS hdom i j hai haj

theorem shifted_domination {n : ℕ} (a : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i, 0 ≤ a i) {D eps : ℝ} (hD : 0 ≤ D) (heps : 0 ≤ eps)
    (hdom : ∀ x : Point (Fin n), |matrixForm S x x| ≤ D * ‖diagonal a x‖ * ‖x‖)
    (x : Point (Fin n)) :
    |matrixForm S x x| ≤ D * ‖diagonal (fun i => a i+eps) x‖ * ‖x‖ := by
  apply (hdom x).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (diagonal_norm_mono a (fun i => a i+eps) ha (fun _ => le_add_of_nonneg_right heps) x) hD)
    (norm_nonneg _)

theorem triangular_norm_le_shift {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    {D eps : ℝ} (hD : 0 ≤ D) (heps : 0 < eps) (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ x : Point (Fin n), |matrixForm S x x| ≤ D * ‖diagonal a x‖ * ‖x‖)
    (x : Point (Fin n)) :
    ‖Matrix.toEuclideanLin (triangularCompletion (fun i => a i+eps) S) x‖ ≤
      D*(1+2*(Nat.clog 2 n:ℝ))*‖x‖ := by
  apply triangular_norm_le_clog hn (fun i => a i+eps) S
    (fun i => add_pos_of_nonneg_of_pos (ha i) heps)
    (fun _ _ hij => by linarith [hmono hij]) hD hS
  exact shifted_domination a S ha hD heps.le hdom

theorem continuousAt_div_shift (u v : ℝ) (hz : v = 0 → u = 0) :
    ContinuousAt (fun eps : ℝ => u/(v+eps)) 0 := by
  by_cases hv : v=0
  · simp only [hz hv, zero_div]
    exact continuousAt_const
  · exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simpa using hv)

/-- Every coefficient converges to the SAME displayed triangular rule.
Zero denominators have zero numerators by the original domination. -/
theorem triangular_shift_continuous {n : ℕ} (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    {D : ℝ} (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ x : Point (Fin n), |matrixForm S x x| ≤ D * ‖diagonal a x‖ * ‖x‖)
    (i j : Fin n) :
    ContinuousAt (fun eps : ℝ => triangularCompletion (fun k => a k+eps) S i j) 0 := by
  by_cases hij : i.val<j.val
  · simp only [triangularCompletion, ite_eq_left hij]
    apply continuousAt_div_shift
    intro hi
    rw [active_entry_zero a S ha hmono hS hdom i j hij.le hi]
    ring
  · by_cases heq : i.val=j.val
    · simp only [triangularCompletion, ite_eq_right hij, ite_eq_left heq]
      apply continuousAt_div_shift
      intro hi
      exact active_entry_zero a S ha hmono hS hdom i j heq.le hi
    · simp only [triangularCompletion, ite_eq_right hij, ite_eq_right heq]
      exact continuousAt_const

theorem matrix_norm_eq_sqrt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Point (Fin n)) :
    ‖Matrix.toEuclideanLin M x‖ = Real.sqrt (∑ i, (∑ j, M i j*x j)^2) := by
  have h : (∑ i, (∑ j, M i j*x j)^2) = ‖Matrix.toEuclideanLin M x‖^2 := by
    rw [norm_sq]
    rfl
  rw [h, Real.sqrt_sq (norm_nonneg _)]

theorem triangular_shift_norm_continuous {n : ℕ} (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    {D : ℝ} (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Fin n), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖)
    (x : Point (Fin n)) :
    ContinuousAt (fun eps : ℝ => ‖Matrix.toEuclideanLin (triangularCompletion (fun i => a i+eps) S) x‖) 0 := by
  have hr (i : Fin n) : ContinuousAt (fun eps : ℝ =>
      ∑ j, triangularCompletion (fun k => a k+eps) S i j*x j) 0 :=
    tendsto_finsetSum _ (fun j _ => (triangular_shift_continuous a S ha hmono hS hdom i j).mul continuousAt_const)
  have hs : ContinuousAt (fun eps : ℝ =>
      ∑ i, (∑ j, triangularCompletion (fun k => a k+eps) S i j*x j)^2) 0 :=
    tendsto_finsetSum _ (fun i _ => (hr i).pow 2)
  have hf : (fun eps : ℝ => ‖Matrix.toEuclideanLin (triangularCompletion (fun i => a i+eps) S) x‖) =
      (fun eps : ℝ => Real.sqrt (∑ i, (∑ j, triangularCompletion (fun k => a k+eps) S i j*x j)^2)) := by
    funext eps
    exact matrix_norm_eq_sqrt _ _
  rw [hf]
  exact Real.continuous_sqrt.continuousAt.comp hs

/-- The SAME explicit global linear coefficient choice obeys the
logarithmic bound at every nonnegative antitone spectrum, including all
zero eigenvalues. No nonlinear completion is taken in the limit. -/
theorem triangular_norm_le_semidefinite {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    {D : ℝ} (hD : 0 ≤ D) (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Fin n), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖)
    (x : Point (Fin n)) :
    ‖Matrix.toEuclideanLin (triangularCompletion a S) x‖ ≤
      D*(1+2*(Nat.clog 2 n:ℝ))*‖x‖ := by
  let f : ℝ → ℝ := fun eps => ‖Matrix.toEuclideanLin (triangularCompletion (fun i => a i+eps) S) x‖
  have hcont : ContinuousAt f 0 := triangular_shift_norm_continuous a S ha hmono hS hdom x
  have hlim : Filter.Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) := hcont.continuousWithinAt.tendsto
  have hevent : ∀ᶠ eps : ℝ in 𝓝[>] (0:ℝ), f eps ≤ D*(1+2*(Nat.clog 2 n:ℝ))*‖x‖ := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact triangular_norm_le_shift hn a S ha hmono hD heps hS hdom x
  have h := le_of_tendsto hlim hevent
  simpa only [f, add_zero] using h

/-- Exact weighted entries, with zero denominators handled by the
proved kernel constraints on S rather than by a completion premise. -/
theorem triangular_entry_identity {n : ℕ} (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    {D : ℝ} (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Fin n), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖)
    (i j : Fin n) :
    a i*triangularCompletion a S i j+a j*triangularCompletion a S j i = 2*S i j := by
  rcases lt_trichotomy i.val j.val with hij | heq | hji
  · have hnot : ¬ (j.val < i.val) := not_lt.mpr hij.le
    have hne : j.val≠i.val := ne_of_gt hij
    simp only [triangularCompletion, ite_eq_left hij, ite_eq_right hnot, ite_eq_right hne, mul_zero, add_zero]
    by_cases hi : a i=0
    · simp [hi, active_entry_zero a S ha hmono hS hdom i j hij.le hi]
    · field_simp [hi]
  · have he : i=j := Fin.ext heq
    subst j
    simp only [triangularCompletion, lt_irrefl, ite_false, ite_true]
    by_cases hi : a i=0
    · simp [hi, kernel_entry_zero a S hS hdom i i hi hi]
    · field_simp [hi]
      ring
  · have hnot : ¬ (i.val < j.val) := not_lt.mpr hji.le
    have hne : i.val≠j.val := ne_of_gt hji
    simp only [triangularCompletion, ite_eq_left hji, ite_eq_right hnot, ite_eq_right hne, mul_zero, zero_add]
    by_cases hj : a j=0
    · have hs := active_entry_zero a S ha hmono hS hdom j i hji.le hj
      rw [hS i j]
      simp [hj, hs]
    · rw [hS i j]
      field_simp [hj]

theorem triangular_matrix_identity {n : ℕ} (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    {D : ℝ} (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Fin n), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖) :
    Matrix.diagonal a * triangularMap a S +
      Matrix.transpose (triangularMap a S) * Matrix.diagonal a = (2:ℝ) • S := by
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  change a i * triangularCompletion a S i j +
    triangularCompletion a S j i * a j = 2 * S i j
  simpa only [mul_comm (a j)] using triangular_entry_identity a S ha hmono hS hdom i j

open MvPolynomial

def polynomialVector {n : ℕ} (a : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : MvPolynomial (Fin n) ℝ := ∑ j, C (triangularCompletion a S i j)*X j

def quadraticPolynomial {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, ∑ j, C (S i j)*X i*X j

theorem polynomialVector_homogeneous {n : ℕ} (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (polynomialVector a S i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (MvPolynomial.isHomogeneous_X ℝ j).C_mul _

theorem quadraticPolynomial_homogeneous {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    (quadraticPolynomial S).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact ((MvPolynomial.isHomogeneous_X ℝ i).C_mul _).mul (MvPolynomial.isHomogeneous_X ℝ j)

/-- Exact identity in the actual multivariate polynomial ring, also at
singular spectra. The displayed vector consists of actual linear roots. -/
theorem polynomial_identity {n : ℕ} (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    {D : ℝ} (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Fin n), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖) :
    (∑ i, C (a i)*X i*polynomialVector a S i) = quadraticPolynomial S := by
  apply MvPolynomial.funext
  intro x
  simp only [polynomialVector, quadraticPolynomial, map_sum, map_mul, eval_C, eval_X, Finset.mul_sum]
  have hp (i j : Fin n) :
      a i*x i*(triangularCompletion a S i j*x j)+a j*x j*(triangularCompletion a S j i*x i) =
      2*(S i j*x i*x j) := by
    linear_combination (x i*x j)*triangular_entry_identity a S ha hmono hS hdom i j
  have hs : (∑ i, ∑ j, (a i*x i*(triangularCompletion a S i j*x j)+
      a j*x j*(triangularCompletion a S j i*x i))) = ∑ i, ∑ j, 2*(S i j*x i*x j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hp i j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ht : (∑ i, ∑ j, a j*x j*(triangularCompletion a S j i*x i)) =
      ∑ i, ∑ j, a i*x i*(triangularCompletion a S i j*x j) := by rw [Finset.sum_comm]
  rw [ht] at hs
  simp only [← Finset.mul_sum] at hs ⊢
  linarith

theorem polynomialVector_eval {n : ℕ} (a : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (x : Point (Fin n)) (i : Fin n) :
    eval (fun j => x j) (polynomialVector a S i) =
      Matrix.toEuclideanLin (triangularCompletion a S) x i := by
  simp [polynomialVector, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

theorem quadraticPolynomial_eval {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (x : Point (Fin n)) :
    eval (fun j => x j) (quadraticPolynomial S) = matrixForm S x x := by
  simp only [quadraticPolynomial, map_sum, map_mul, eval_C, eval_X, matrixForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem polynomialVector_norm_le {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a)
    {D : ℝ} (hD : 0 ≤ D) (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Fin n), |eval (fun i => z i) (quadraticPolynomial S)| ≤
      D * ‖diagonal a z‖ * ‖z‖) (x : Point (Fin n)) :
    ‖(WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => eval (fun j => x j) (polynomialVector a S i))‖ ≤
      D*(1+2*(Nat.clog 2 n:ℝ))*‖x‖ := by
  have hv : (WithLp.equiv 2 (Fin n → ℝ)).symm
      (fun i => eval (fun j => x j) (polynomialVector a S i)) =
      Matrix.toEuclideanLin (triangularCompletion a S) x := by
    ext i
    exact polynomialVector_eval a S x i
  rw [hv]
  apply triangular_norm_le_semidefinite hn a S ha hmono hD hS
  intro z
  simpa only [quadraticPolynomial_eval] using hdom z

end OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticSingular
