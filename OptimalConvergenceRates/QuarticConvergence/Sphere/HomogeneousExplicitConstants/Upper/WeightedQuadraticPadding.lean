import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedQuadraticTree

/-! Actual ordered finite coordinate transport and zero-column padding
for the balanced weighted quadratic completion. The norm theorem here
assumes a strictly positive spectrum; singular extension is separate. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace WeightedQuadraticPadding

set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators InnerProductSpace
open WeightedQuadraticSplit WeightedQuadraticTree

def coordEquivFin : (d : ℕ) → Coord d ≃ Fin (2^d)
  | 0 => Equiv.refl _
  | d+1 => (Equiv.sumCongr (coordEquivFin d) (coordEquivFin d)).trans
      (finSumFinEquiv.trans (finCongr (by rw [pow_succ]; omega)))

@[simp] theorem coordEquivFin_inl_val (d : ℕ) (i : Coord d) :
    (coordEquivFin (d+1) (Sum.inl i)).val = (coordEquivFin d i).val := by
  rfl

@[simp] theorem coordEquivFin_inr_val (d : ℕ) (i : Coord d) :
    (coordEquivFin (d+1) (Sum.inr i)).val = 2^d + (coordEquivFin d i).val := by
  rfl

theorem high_index_lt_low (d : ℕ) (i j : Coord d) :
    (coordEquivFin (d+1) (Sum.inl i)).val < (coordEquivFin (d+1) (Sum.inr j)).val := by
  simp only [coordEquivFin_inl_val, coordEquivFin_inr_val]
  have h := (coordEquivFin d i).isLt
  omega

/-- An actual antitone positive finite spectrum supplies the recursive
ordering property; a pre-existing spectral tree is not an extra premise. -/
theorem orderedPositive_of_antitone (d : ℕ) (a : Fin (2 ^ d) → ℝ)
    (ha : ∀ i, 0 < a i) (hmono : Antitone a) :
    OrderedPositive d (fun i ↦ a (coordEquivFin d i)) := by
  induction d with
  | zero => exact fun i ↦ ha (coordEquivFin 0 i)
  | succ d ih =>
    let aH : Fin (2^d) → ℝ := fun i ↦ a (coordEquivFin (d+1) (Sum.inl ((coordEquivFin d).symm i)))
    let aL : Fin (2^d) → ℝ := fun i ↦ a (coordEquivFin (d+1) (Sum.inr ((coordEquivFin d).symm i)))
    have hH : Antitone aH := by
      intro i j hij
      apply hmono
      apply Fin.le_iff_val_le_val.mpr
      simpa only [coordEquivFin_inl_val, Equiv.apply_symm_apply] using
        Fin.le_iff_val_le_val.mp hij
    have hL : Antitone aL := by
      intro i j hij
      apply hmono
      apply Fin.le_iff_val_le_val.mpr
      simp only [coordEquivFin_inr_val, Equiv.apply_symm_apply]
      exact Nat.add_le_add_left (Fin.le_iff_val_le_val.mp hij) _
    refine ⟨?_,?_,?_⟩
    · simpa only [aH, Equiv.symm_apply_apply] using ih aH (fun i ↦ ha _) hH
    · simpa only [aL, Equiv.symm_apply_apply] using ih aL (fun i ↦ ha _) hL
    · intro i j
      apply hmono
      exact Fin.le_iff_val_le_val.mpr (high_index_lt_low d i j).le

/-- The recursive coefficient rule has this explicit index formula. -/
theorem completion_entry_formula (d : ℕ) (a : Coord d → ℝ)
    (S : Matrix (Coord d) (Coord d) ℝ) (i j : Coord d) :
    completion d a S i j =
      if (coordEquivFin d i).val < (coordEquivFin d j).val then 2*S i j/a i
      else if (coordEquivFin d i).val = (coordEquivFin d j).val then S i j/a i else 0 := by
  induction d with
  | zero =>
    fin_cases i
    fin_cases j
    simp [completion, coordEquivFin]
  | succ d ih =>
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simpa only [completion, Matrix.fromBlocks_apply₁₁,
          coordEquivFin_inl_val] using
          ih (fun i ↦ a (Sum.inl i)) (fun i j ↦ S (Sum.inl i) (Sum.inl j)) i j
      | inr j =>
        have hlt := high_index_lt_low d i j
        simp only [coordEquivFin_inl_val, coordEquivFin_inr_val] at hlt
        simp [completion, hlt, crossCoefficients]
    | inr i =>
      cases j with
      | inl j =>
        have hnot : ¬(coordEquivFin (d+1) (Sum.inr i)).val <
            (coordEquivFin (d+1) (Sum.inl j)).val :=
          not_lt.mpr (high_index_lt_low d j i).le
        have hne := ne_of_gt (high_index_lt_low d j i)
        simp only [coordEquivFin_inl_val, coordEquivFin_inr_val] at hnot
        simp only [coordEquivFin_inl_val, coordEquivFin_inr_val] at hne
        simp [completion, hnot, hne]
      | inr j =>
        simpa only [completion, Matrix.fromBlocks_apply₂₂,
          coordEquivFin_inr_val, Nat.add_lt_add_iff_left, Nat.add_left_cancel_iff] using
          ih (fun i ↦ a (Sum.inr i)) (fun i j ↦ S (Sum.inr i) (Sum.inr j)) i j

/-- The resulting finite-coordinate choice is fixed, explicit, and linear
in S even when eigenvalues vanish. Its norm theorem is proved below. -/
def triangularCompletion {n : ℕ} (a : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : ℝ :=
  if i.val < j.val then 2*S i j/a i else if i.val=j.val then S i j/a i else 0

theorem completion_eq_triangular (d : ℕ) (a : Fin (2 ^ d) → ℝ)
    (S : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℝ) (i j : Coord d) :
    completion d (fun i ↦ a (coordEquivFin d i))
      (fun i j ↦ S (coordEquivFin d i) (coordEquivFin d j)) i j =
      triangularCompletion a S (coordEquivFin d i) (coordEquivFin d j) := by
  rw [completion_entry_formula]
  rfl

/-- A single global linear coefficient choice, including at zero
eigenvalues. The norm/identity hypotheses are separate theorems. -/
def triangularMap {n : ℕ} (a : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := triangularCompletion a
  map_add' S T := by
    ext i j
    simp only [triangularCompletion, Matrix.add_apply]
    split_ifs <;> ring
  map_smul' c S := by
    ext i j
    simp only [triangularCompletion, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

def toTree (d : ℕ) (x : Point (Fin (2 ^ d))) : Point (Coord d) :=
  (WithLp.equiv 2 (Coord d → ℝ)).symm (fun i ↦ x (coordEquivFin d i))

def fromTree (d : ℕ) (y : Point (Coord d)) : Point (Fin (2^d)) :=
  (WithLp.equiv 2 (Fin (2^d) → ℝ)).symm (fun i ↦ y ((coordEquivFin d).symm i))

@[simp] theorem toTree_fromTree (d : ℕ) (y : Point (Coord d)) :
    toTree d (fromTree d y) = y := by
  ext i
  change y ((coordEquivFin d).symm (coordEquivFin d i)) = y i
  rw [Equiv.symm_apply_apply]

@[simp] theorem fromTree_toTree (d : ℕ) (x : Point (Fin (2 ^ d))) :
    fromTree d (toTree d x) = x := by
  ext i
  change x (coordEquivFin d ((coordEquivFin d).symm i)) = x i
  rw [Equiv.apply_symm_apply]

@[simp] theorem norm_toTree (d : ℕ) (x : Point (Fin (2 ^ d))) : ‖toTree d x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq, norm_sq]
  change (∑ i, (x (coordEquivFin d i))^2) = ∑ j, (x j)^2
  exact (coordEquivFin d).sum_comp (fun j ↦ (x j)^2)

@[simp] theorem norm_fromTree (d : ℕ) (y : Point (Coord d)) : ‖fromTree d y‖ = ‖y‖ := by
  rw [← norm_toTree d (fromTree d y), toTree_fromTree]

theorem diagonal_toTree (d : ℕ) (a : Fin (2 ^ d) → ℝ) (x : Point (Fin (2 ^ d))) :
    diagonal (fun i ↦ a (coordEquivFin d i)) (toTree d x) = toTree d (diagonal a x) := by
  ext i
  simp [diagonal_apply, toTree]

def treeMatrix (d : ℕ) (S : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℝ) :
    Matrix (Coord d) (Coord d) ℝ := fun i j ↦ S (coordEquivFin d i) (coordEquivFin d j)

theorem matrixForm_toTree (d : ℕ) (S : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℝ)
    (x : Point (Fin (2 ^ d))) :
    matrixForm (treeMatrix d S) (toTree d x) (toTree d x) = matrixForm S x x := by
  simp only [matrixForm_apply, treeMatrix]
  change (∑ i, ∑ j, x (coordEquivFin d i) *
    S (coordEquivFin d i) (coordEquivFin d j) * x (coordEquivFin d j)) = _
  calc
    _ = ∑ i, ∑ k, x (coordEquivFin d i) * S (coordEquivFin d i) k * x k := by
      apply Finset.sum_congr rfl
      intro i _
      exact (coordEquivFin d).sum_comp (fun k ↦ x (coordEquivFin d i)*S (coordEquivFin d i) k*x k)
    _ = _ := (coordEquivFin d).sum_comp (fun i ↦ ∑ k, x i*S i k*x k)

theorem triangular_toTree (d : ℕ) (a : Fin (2 ^ d) → ℝ)
    (S : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℝ) (x : Point (Fin (2 ^ d))) :
    toTree d (Matrix.toEuclideanLin (triangularCompletion a S) x) =
      Matrix.toEuclideanLin (completion d (fun i ↦ a (coordEquivFin d i)) (treeMatrix d S))
        (toTree d x) := by
  ext i
  change (∑ k, triangularCompletion a S (coordEquivFin d i) k * x k) =
    ∑ j, completion d (fun i ↦ a (coordEquivFin d i)) (treeMatrix d S) i j * x (coordEquivFin d j)
  calc
    _ = ∑ j, triangularCompletion a S (coordEquivFin d i) (coordEquivFin d j) * x (coordEquivFin d
      j) :=
      ((coordEquivFin d).sum_comp (fun k ↦ triangularCompletion a S (coordEquivFin d i) k*x k)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun r : ℝ ↦ r*x (coordEquivFin d j)) (completion_eq_triangular d a S i j).symm

/-- The actual finite triangular choice has the balanced logarithmic
bound in a full power-of-two dimension, with no spectral-tree premise. -/
theorem triangular_norm_le_pow (d : ℕ) (a : Fin (2 ^ d) → ℝ)
    (S : Matrix (Fin (2 ^ d)) (Fin (2 ^ d)) ℝ) (ha : ∀ i, 0 < a i) (hmono : Antitone a)
    {D : ℝ} (hD : 0 ≤ D) (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Fin (2^d)), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖)
    (x : Point (Fin (2^d))) :
    ‖Matrix.toEuclideanLin (triangularCompletion a S) x‖ ≤ D * (1+2*(d:ℝ)) * ‖x‖ := by
  have hd : ∀ y : Point (Coord d), |matrixForm (treeMatrix d S) y y| ≤
      D * ‖diagonal (fun i ↦ a (coordEquivFin d i)) y‖ * ‖y‖ := by
    intro y
    rw [← toTree_fromTree d y, matrixForm_toTree, diagonal_toTree, norm_toTree, norm_toTree]
    exact hdom (fromTree d y)
  have hc := completion_norm_le d (fun i ↦ a (coordEquivFin d i)) (treeMatrix d S)
    (orderedPositive_of_antitone d a ha hmono) hD
    (fun i j ↦ hS (coordEquivFin d i) (coordEquivFin d j)) hd (toTree d x)
  rw [← triangular_toTree] at hc
  simpa only [norm_toTree] using hc

def embed {n : ℕ} (m : ℕ) (x : Point (Fin n)) : Point (Fin (n+m)) :=
  (WithLp.equiv 2 (Fin (n+m) → ℝ)).symm (Fin.append (fun i ↦ x i) (fun _ ↦ 0))

def restrict {n : ℕ} (m : ℕ) (z : Point (Fin (n + m))) : Point (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i ↦ z (Fin.castAdd m i))

def tail {n m : ℕ} (z : Point (Fin (n + m))) : Point (Fin m) :=
  (WithLp.equiv 2 (Fin m → ℝ)).symm (fun j ↦ z (Fin.natAdd n j))

theorem norm_sq_restrict_tail {n m : ℕ} (z : Point (Fin (n + m))) :
    ‖z‖^2 = ‖restrict m z‖^2 + ‖tail z‖^2 := by
  simp only [norm_sq]
  rw [Fin.sum_univ_add]
  rfl

theorem norm_restrict_le {n m : ℕ} (z : Point (Fin (n + m))) : ‖restrict m z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [norm_sq_restrict_tail z, sq_nonneg ‖tail z‖]

@[simp] theorem norm_embed {n : ℕ} (m : ℕ) (x : Point (Fin n)) : ‖embed m x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [norm_sq, embed, Fin.sum_univ_add]

def lastIndex {n : ℕ} (hn : 0 < n) : Fin n := ⟨n-1,by omega⟩

def padSpectrum {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ) : Fin (n+m) → ℝ :=
  Fin.append a (fun _ ↦ a (lastIndex hn))

theorem padSpectrum_pos {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ)
    (ha : ∀ i, 0 < a i) : ∀ j, 0<padSpectrum a hn m j := by
  intro j
  refine Fin.addCases (m:=n) (n:=m) (fun j ↦ ?_) (fun j ↦ ?_) j
  · simpa only [padSpectrum, Fin.append_left] using ha j
  · simpa only [padSpectrum, Fin.append_right] using ha (lastIndex hn)

theorem padSpectrum_antitone {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ)
    (ha : Antitone a) : Antitone (padSpectrum a hn m) := by
  intro i j
  refine Fin.addCases (m:=n) (n:=m) (fun i ↦ ?_) (fun i ↦ ?_) i
  · refine Fin.addCases (m:=n) (n:=m) (fun j ↦ ?_) (fun j ↦ ?_) j
    · intro hij
      simp only [padSpectrum, Fin.append_left]
      apply ha
      apply Fin.le_iff_val_le_val.mpr
      exact Fin.le_iff_val_le_val.mp hij
    · intro _
      simp only [padSpectrum, Fin.append_left, Fin.append_right]
      apply ha
      apply Fin.le_iff_val_le_val.mpr
      have hi := i.isLt
      dsimp [lastIndex]
      omega
  · refine Fin.addCases (m:=n) (n:=m) (fun j ↦ ?_) (fun j ↦ ?_) j
    · intro hij
      change n+i.val ≤ j.val at hij
      have hj := j.isLt
      omega
    · intro _
      simp only [padSpectrum, Fin.append_right, le_refl]

def padMatrix {n : ℕ} (m : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n+m)) (Fin (n+m)) ℝ :=
  Fin.append (fun i ↦ Fin.append (S i) (fun _ ↦ 0)) (fun _ ↦ fun _ ↦ 0)

theorem padMatrix_symmetric {n : ℕ} (m : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : ∀ i j, S i j = S j i) : ∀ i j, padMatrix m S i j = padMatrix m S j i := by
  intro i j
  refine Fin.addCases (m:=n) (n:=m) (fun i ↦ ?_) (fun i ↦ ?_) i
  · refine Fin.addCases (m:=n) (n:=m) (fun j ↦ ?_) (fun j ↦ ?_) j
    · simpa only [padMatrix, Fin.append_left] using hS i j
    · simp [padMatrix]
  · refine Fin.addCases (m:=n) (n:=m) (fun j ↦ ?_) (fun j ↦ ?_) j <;> simp [padMatrix]

theorem padMatrix_form {n m : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (z : Point (Fin (n + m))) :
    matrixForm (padMatrix m S) z z = matrixForm S (restrict m z) (restrict m z) := by
  simp [matrixForm_apply, padMatrix, restrict, Fin.sum_univ_add]

theorem restrict_diagonal {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ)
    (z : Point (Fin (n + m))) :
    restrict m (diagonal (padSpectrum a hn m) z) = diagonal a (restrict m z) := by
  ext i
  simp [restrict, diagonal_apply, padSpectrum]

theorem padMatrix_domination {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ z : Point (Fin n), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖)
    (z : Point (Fin (n+m))) :
    |matrixForm (padMatrix m S) z z| ≤ D * ‖diagonal (padSpectrum a hn m) z‖ * ‖z‖ := by
  rw [padMatrix_form]
  have hL := norm_restrict_le (diagonal (padSpectrum a hn m) z)
  rw [restrict_diagonal] at hL
  calc
    |matrixForm S (restrict m z) (restrict m z)| ≤
        D * ‖diagonal a (restrict m z)‖ * ‖restrict m z‖ := hdom _
    _ ≤ D * ‖diagonal (padSpectrum a hn m) z‖ * ‖restrict m z‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hD) (norm_nonneg _)
    _ ≤ D * ‖diagonal (padSpectrum a hn m) z‖ * ‖z‖ :=
      mul_le_mul_of_nonneg_left (norm_restrict_le z) (mul_nonneg hD (norm_nonneg _))

@[simp] theorem triangular_pad_prefix {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    triangularCompletion (padSpectrum a hn m) (padMatrix m S) (Fin.castAdd m i) (Fin.castAdd m j) =
      triangularCompletion a S i j := by
  simp [triangularCompletion, padSpectrum, padMatrix]

theorem triangular_restrict_embed {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ)
    (S : Matrix (Fin n) (Fin n) ℝ) (x : Point (Fin n)) :
    restrict m (Matrix.toEuclideanLin
      (triangularCompletion (padSpectrum a hn m) (padMatrix m S)) (embed m x)) =
      Matrix.toEuclideanLin (triangularCompletion a S) x := by
  ext i
  change (∑ j : Fin (n+m), triangularCompletion (padSpectrum a hn m) (padMatrix m S)
    (Fin.castAdd m i) j * embed m x j) = ∑ j, triangularCompletion a S i j*x j
  rw [Fin.sum_univ_add]
  simp [embed]

/-- Every positive ordered finite spectrum has the actual logarithmic
completion, by zero-column padding to a power of two. -/
theorem triangular_norm_le_of_le_pow {n d : ℕ} (hn : 0 < n) (hnd : n ≤ 2 ^ d)
    (a : Fin n → ℝ) (S : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i, 0 < a i) (hmono : Antitone a) {D : ℝ} (hD : 0 ≤ D)
    (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Fin n), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖)
    (x : Point (Fin n)) :
    ‖Matrix.toEuclideanLin (triangularCompletion a S) x‖ ≤ D*(1+2*(d:ℝ))*‖x‖ := by
  let m := 2^d-n
  have heq : n+m=2^d := Nat.add_sub_of_le hnd
  have hfull := triangular_norm_le_pow d
  rw [← heq] at hfull
  have hbig := hfull (padSpectrum a hn m) (padMatrix m S)
    (padSpectrum_pos a hn m ha) (padSpectrum_antitone a hn m hmono) hD
    (padMatrix_symmetric m S hS) (padMatrix_domination a hn m S hD hdom) (embed m x)
  have hsmall := norm_restrict_le (Matrix.toEuclideanLin
    (triangularCompletion (padSpectrum a hn m) (padMatrix m S)) (embed m x))
  rw [triangular_restrict_embed] at hsmall
  exact hsmall.trans (by simpa only [norm_embed] using hbig)

theorem triangular_norm_le_clog {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (S : Matrix (Fin n) (Fin n) ℝ) (ha : ∀ i, 0 < a i) (hmono : Antitone a)
    {D : ℝ} (hD : 0 ≤ D) (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Fin n), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖)
    (x : Point (Fin n)) :
    ‖Matrix.toEuclideanLin (triangularCompletion a S) x‖ ≤
      D*(1+2*(Nat.clog 2 n:ℝ))*‖x‖ :=
  triangular_norm_le_of_le_pow hn (Nat.le_pow_clog (by norm_num : 1<2) n) a S ha hmono hD hS hdom x

end WeightedQuadraticPadding
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
