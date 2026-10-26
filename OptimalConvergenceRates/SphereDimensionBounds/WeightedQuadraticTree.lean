import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Funext
import OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticSplit

/-! An actual balanced recursive weighted quadratic completion.
The initial construction uses a full depth-d binary coordinate tree. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticTree

set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators InnerProductSpace
open WeightedQuadraticSplit

def Coord : ℕ → Type
  | 0 => Fin 1
  | d+1 => Coord d ⊕ Coord d

instance coordFintype (d : ℕ) : Fintype (Coord d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype (Fin 1))
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Coord d ⊕ Coord d))

instance coordDecidableEq (d : ℕ) : DecidableEq (Coord d) := by
  induction d with
  | zero => exact inferInstanceAs (DecidableEq (Fin 1))
  | succ d ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Coord d ⊕ Coord d))

instance coordNonempty (d : ℕ) : Nonempty (Coord d) := by
  induction d with
  | zero => exact ⟨(0 : Fin 1)⟩
  | succ d ih =>
    obtain ⟨i⟩ := ih
    exact ⟨Sum.inl i⟩

/-- Both children are spectrally ordered, positive, and every high
eigenvalue dominates every low eigenvalue. -/
def OrderedPositive : (d : ℕ) → (Coord d → ℝ) → Prop
  | 0,a => ∀ i, 0 < a i
  | d+1,a => OrderedPositive d (fun i => a (Sum.inl i)) ∧
      OrderedPositive d (fun j => a (Sum.inr j)) ∧
      ∀ i j, a (Sum.inr j) ≤ a (Sum.inl i)

theorem orderedPositive_pos (d : ℕ) (a : Coord d → ℝ) (ha : OrderedPositive d a) :
    ∀ i, 0 < a i := by
  induction d with
  | zero => exact ha
  | succ d ih =>
    intro i
    cases i with
    | inl i => exact ih _ ha.1 i
    | inr j => exact ih _ ha.2.1 j

theorem split_threshold (d : ℕ) (a : Coord (d + 1) → ℝ) (ha : OrderedPositive (d + 1) a) :
    ∃ tau : ℝ, 0 < tau ∧ (∀ i, tau ≤ a (Sum.inl i)) ∧
      (∀ j, 0 ≤ a (Sum.inr j)) ∧ (∀ j, a (Sum.inr j) ≤ tau) := by
  obtain ⟨i,hi⟩ := Finite.exists_min (fun i : Coord d => a (Sum.inl i))
  exact ⟨a (Sum.inl i), orderedPositive_pos d _ ha.1 i, hi,
    fun j => (orderedPositive_pos d _ ha.2.1 j).le, fun j => ha.2.2 i j⟩

/-- The displayed recursive coefficient choice, independent of D. -/
def completion : (d : ℕ) → (Coord d → ℝ) →
    Matrix (Coord d) (Coord d) ℝ → Matrix (Coord d) (Coord d) ℝ
  | 0,a,S => fun i j => S i j / a i
  | d+1,a,S => Matrix.fromBlocks
      (completion d (fun i => a (Sum.inl i)) (fun i j => S (Sum.inl i) (Sum.inl j)))
      (crossCoefficients (fun i => a (Sum.inl i)) S)
      0
      (completion d (fun i => a (Sum.inr i)) (fun i j => S (Sum.inr i) (Sum.inr j)))

theorem completion_entry_identity (d : ℕ) (a : Coord d → ℝ)
    (S : Matrix (Coord d) (Coord d) ℝ) (ha : ∀ i, a i ≠ 0)
    (hS : ∀ i j, S i j = S j i) (i j : Coord d) :
    a i * completion d a S i j + a j * completion d a S j i = 2 * S i j := by
  induction d with
  | zero =>
    fin_cases i
    fin_cases j
    simp only [completion]
    field_simp [ha (0 : Fin 1)]
    ring
  | succ d ih =>
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simpa only [completion, Matrix.fromBlocks_apply₁₁] using
          ih (fun i => a (Sum.inl i)) (fun i j => S (Sum.inl i) (Sum.inl j))
            (fun i => ha (Sum.inl i)) (fun i j => hS (Sum.inl i) (Sum.inl j)) i j
      | inr j =>
        simp only [completion, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
          Matrix.zero_apply, mul_zero, add_zero]
        exact weighted_crossCoefficients (fun i => a (Sum.inl i))
          (fun i => ha (Sum.inl i)) S i j
    | inr i =>
      cases j with
      | inl j =>
        simp only [completion, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
          Matrix.zero_apply, mul_zero, zero_add]
        rw [weighted_crossCoefficients (fun i => a (Sum.inl i))
          (fun i => ha (Sum.inl i)) S j i, hS (Sum.inl j) (Sum.inr i)]
      | inr j =>
        simpa only [completion, Matrix.fromBlocks_apply₂₂] using
          ih (fun i => a (Sum.inr i)) (fun i j => S (Sum.inr i) (Sum.inr j))
            (fun i => ha (Sum.inr i)) (fun i j => hS (Sum.inr i) (Sum.inr j)) i j

theorem completion_add (d : ℕ) (a : Coord d → ℝ)
    (S T : Matrix (Coord d) (Coord d) ℝ) :
    completion d a (S+T) = completion d a S + completion d a T := by
  induction d with
  | zero => ext i j; simp [completion, add_div, Matrix.add_apply, Pi.add_apply]
  | succ d ih =>
    ext i j
    simp only [Matrix.add_apply]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simpa only [completion, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Pi.add_apply] using!
          congrFun (congrFun (ih (fun i => a (Sum.inl i))
            (fun i j => S (Sum.inl i) (Sum.inl j)) (fun i j => T (Sum.inl i) (Sum.inl j))) i) j
      | inr j => simp [completion, crossCoefficients, add_div, mul_add, Matrix.add_apply, Pi.add_apply]
    | inr i =>
      cases j with
      | inl j => simp [completion, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply]
      | inr j =>
        simpa only [completion, Matrix.fromBlocks_apply₂₂, Matrix.add_apply, Pi.add_apply] using!
          congrFun (congrFun (ih (fun i => a (Sum.inr i))
            (fun i j => S (Sum.inr i) (Sum.inr j)) (fun i j => T (Sum.inr i) (Sum.inr j))) i) j

theorem completion_smul (d : ℕ) (a : Coord d → ℝ)
    (c : ℝ) (S : Matrix (Coord d) (Coord d) ℝ) :
    completion d a (c • S) = c • completion d a S := by
  induction d with
  | zero => ext i j; simp only [completion, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
  | succ d ih =>
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simpa only [completion, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] using!
          congrFun (congrFun (ih (fun i => a (Sum.inl i))
            (fun i j => S (Sum.inl i) (Sum.inl j))) i) j
      | inr j => simp only [completion, Matrix.fromBlocks_apply₁₂, crossCoefficients,
          Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]; ring
    | inr i =>
      cases j with
      | inl j => simp [completion, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply]
      | inr j =>
        simpa only [completion, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] using!
          congrFun (congrFun (ih (fun i => a (Sum.inr i))
            (fun i j => S (Sum.inr i) (Sum.inr j))) i) j

/-- The complete chosen operator is linear in the input matrix. -/
def completionMap (d : ℕ) (a : Coord d → ℝ) :
    Matrix (Coord d) (Coord d) ℝ →ₗ[ℝ] Matrix (Coord d) (Coord d) ℝ where
  toFun := completion d a
  map_add' := completion_add d a
  map_smul' := completion_smul d a

theorem completion_matrix_identity (d : ℕ) (a : Coord d → ℝ)
    (S : Matrix (Coord d) (Coord d) ℝ) (ha : ∀ i, a i ≠ 0)
    (hS : ∀ i j, S i j = S j i) :
    Matrix.diagonal a * completion d a S + (completion d a S).transpose * Matrix.diagonal a = (2:ℝ) • S := by
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.transpose_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [mul_comm (a j)] using completion_entry_identity d a S ha hS i j

section BlockHelpers

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def highPart (z : Point (ι ⊕ κ)) : Point ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm (fun i => z (Sum.inl i))

def lowPart (z : Point (ι ⊕ κ)) : Point κ :=
  (WithLp.equiv 2 (κ → ℝ)).symm (fun j => z (Sum.inr j))

omit [DecidableEq ι] [DecidableEq κ] in
theorem norm_sq_parts (z : Point (ι ⊕ κ)) :
    ‖z‖^2 = ‖highPart z‖^2 + ‖lowPart z‖^2 := by
  simp [norm_sq, highPart, lowPart, Fintype.sum_sum_type]

omit [DecidableEq ι] [DecidableEq κ] in
theorem norm_highPart_le (z : Point (ι ⊕ κ)) : ‖highPart z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [norm_sq_parts z, sq_nonneg ‖lowPart z‖]

omit [DecidableEq ι] [DecidableEq κ] in
theorem norm_lowPart_le (z : Point (ι ⊕ κ)) : ‖lowPart z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [norm_sq_parts z, sq_nonneg ‖highPart z‖]

theorem blockDiag_apply (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (z : Point (ι ⊕ κ)) :
    Matrix.toEuclideanLin (Matrix.fromBlocks A 0 0 B) z =
      high (Matrix.toEuclideanLin A (highPart z)) + low (Matrix.toEuclideanLin B (lowPart z)) := by
  ext i
  cases i <;>
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, high, low, highPart, lowPart]

theorem crossBlock_apply (C : Matrix ι κ ℝ) (z : Point (ι ⊕ κ)) :
    Matrix.toEuclideanLin (Matrix.fromBlocks 0 C 0 0) z =
      high (κ:=κ) (Matrix.toEuclideanLin C (lowPart z)) := by
  ext i
  cases i <;>
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, high, lowPart]

/-- Disjoint diagonal output blocks cost a maximum bound, not their sum. -/
theorem blockDiag_norm_le (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ x : Point ι, ‖Matrix.toEuclideanLin A x‖ ≤ K * ‖x‖)
    (hB : ∀ y : Point κ, ‖Matrix.toEuclideanLin B y‖ ≤ K * ‖y‖) (z : Point (ι ⊕ κ)) :
    ‖Matrix.toEuclideanLin (Matrix.fromBlocks A 0 0 B) z‖ ≤ K * ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).mp
  have hAs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).2 (hA (highPart z))
  have hBs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (norm_nonneg _))).2 (hB (lowPart z))
  calc
    ‖Matrix.toEuclideanLin (Matrix.fromBlocks A 0 0 B) z‖^2 =
        ‖Matrix.toEuclideanLin A (highPart z)‖^2 + ‖Matrix.toEuclideanLin B (lowPart z)‖^2 := by
      rw [blockDiag_apply, norm_add_sq_real, high_low_inner, norm_high, norm_low]
      ring
    _ ≤ (K * ‖highPart z‖)^2 + (K * ‖lowPart z‖)^2 := add_le_add hAs hBs
    _ = K^2 * (‖highPart z‖^2 + ‖lowPart z‖^2) := by ring
    _ = (K * ‖z‖)^2 := by rw [← norm_sq_parts]; ring

theorem crossBlock_norm_le (C : Matrix ι κ ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hC : ∀ y : Point κ, ‖Matrix.toEuclideanLin C y‖ ≤ K * ‖y‖) (z : Point (ι ⊕ κ)) :
    ‖Matrix.toEuclideanLin (Matrix.fromBlocks 0 C 0 (0 : Matrix κ κ ℝ)) z‖ ≤ K * ‖z‖ := by
  rw [crossBlock_apply, norm_high]
  exact (hC (lowPart z)).trans (mul_le_mul_of_nonneg_left (norm_lowPart_le z) hK)

theorem upperBlock_norm_le (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (C : Matrix ι κ ℝ)
    {K J : ℝ} (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hA : ∀ x : Point ι, ‖Matrix.toEuclideanLin A x‖ ≤ K * ‖x‖)
    (hB : ∀ y : Point κ, ‖Matrix.toEuclideanLin B y‖ ≤ K * ‖y‖)
    (hC : ∀ y : Point κ, ‖Matrix.toEuclideanLin C y‖ ≤ J * ‖y‖) (z : Point (ι ⊕ κ)) :
    ‖Matrix.toEuclideanLin (Matrix.fromBlocks A C 0 B) z‖ ≤ (K + J) * ‖z‖ := by
  have hm : Matrix.fromBlocks A C 0 B =
      Matrix.fromBlocks A 0 0 B + Matrix.fromBlocks 0 C 0 0 := by
    ext i j
    cases i <;> cases j <;> simp
  rw [hm, map_add, LinearMap.add_apply]
  calc
    ‖Matrix.toEuclideanLin (Matrix.fromBlocks A 0 0 B) z +
        Matrix.toEuclideanLin (Matrix.fromBlocks 0 C 0 0) z‖ ≤
        ‖Matrix.toEuclideanLin (Matrix.fromBlocks A 0 0 B) z‖ +
          ‖Matrix.toEuclideanLin (Matrix.fromBlocks 0 C 0 0) z‖ := norm_add_le _ _
    _ ≤ K * ‖z‖ + J * ‖z‖ :=
      add_le_add (blockDiag_norm_le A B hK hA hB z) (crossBlock_norm_le C hJ hC z)
    _ = (K + J) * ‖z‖ := by ring

theorem matrixForm_high_high (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x y : Point ι) :
    matrixForm S (high x) (high y) =
      matrixForm (fun i j => S (Sum.inl i) (Sum.inl j)) x y := by
  simp [matrixForm, Matrix.toBilin'_apply, high, Fintype.sum_sum_type]

theorem matrixForm_low_low (S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (x y : Point κ) :
    matrixForm S (low x) (low y) =
      matrixForm (fun i j => S (Sum.inr i) (Sum.inr j)) x y := by
  simp [matrixForm, Matrix.toBilin'_apply, low, Fintype.sum_sum_type]

end BlockHelpers

theorem card_coord (d : ℕ) : Fintype.card (Coord d) = 2^d := by
  induction d with
  | zero => exact rfl
  | succ d ih =>
    change Fintype.card (Coord d ⊕ Coord d) = _
    rw [Fintype.card_sum, ih, pow_succ]
    ring

/-- The fully constructed completion costs only the balanced tree depth.
Disjoint sibling blocks are combined by a maximum estimate at each step. -/
theorem completion_norm_le (d : ℕ) (a : Coord d → ℝ)
    (S : Matrix (Coord d) (Coord d) ℝ) (ha : OrderedPositive d a)
    {D : ℝ} (hD : 0 ≤ D) (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Coord d), |matrixForm S z z| ≤ D * ‖diagonal a z‖ * ‖z‖)
    (z : Point (Coord d)) :
    ‖Matrix.toEuclideanLin (completion d a S) z‖ ≤ D * (1 + 2 * (d:ℝ)) * ‖z‖ := by
  induction d with
  | zero =>
    have hc := (singleton_completion S a hD hdom (0 : Fin 1)).2
    have hv : Matrix.toEuclideanLin (completion 0 a S) z =
        (S (0 : Fin 1) (0 : Fin 1) / a (0 : Fin 1)) • z := by
      ext i
      fin_cases i
      simp only [Matrix.toLpLin_apply, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
      simp [completion, Matrix.mulVec, dotProduct, Coord, Fin.sum_univ_one]
    rw [hv, norm_smul, Real.norm_eq_abs]
    norm_num only [Nat.cast_zero, mul_zero, add_zero, mul_one]
    exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  | succ d ih =>
    let aH : Coord d → ℝ := fun i => a (Sum.inl i)
    let aL : Coord d → ℝ := fun i => a (Sum.inr i)
    let SH : Matrix (Coord d) (Coord d) ℝ := fun i j => S (Sum.inl i) (Sum.inl j)
    let SL : Matrix (Coord d) (Coord d) ℝ := fun i j => S (Sum.inr i) (Sum.inr j)
    have hae : Sum.elim aH aL = a := by
      funext i
      cases i <;> rfl
    have hd : ∀ z : Point (Coord d ⊕ Coord d), |matrixForm S z z| ≤
        D * ‖diagonal (Sum.elim aH aL) z‖ * ‖z‖ := by
      simpa only [hae] using! hdom
    have hdH : ∀ x : Point (Coord d), |matrixForm SH x x| ≤ D * ‖diagonal aH x‖ * ‖x‖ := by
      intro x
      have hx := hd (high (κ:=Coord d) x)
      erw [matrixForm_high_high S x x, diagonal_high, norm_high, norm_high] at hx
      exact hx
    have hdL : ∀ y : Point (Coord d), |matrixForm SL y y| ≤ D * ‖diagonal aL y‖ * ‖y‖ := by
      intro y
      have hy := hd (low (ι:=Coord d) y)
      erw [matrixForm_low_low S y y, diagonal_low, norm_low, norm_low] at hy
      exact hy
    let K : ℝ := D * (1 + 2 * (d:ℝ))
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hCH : ∀ x : Point (Coord d),
        ‖Matrix.toEuclideanLin (completion d aH SH) x‖ ≤ K * ‖x‖ := by
      intro x
      exact ih aH SH ha.1 (fun i j => hS (Sum.inl i) (Sum.inl j)) hdH x
    have hCL : ∀ y : Point (Coord d),
        ‖Matrix.toEuclideanLin (completion d aL SL) y‖ ≤ K * ‖y‖ := by
      intro y
      exact ih aL SL ha.2.1 (fun i j => hS (Sum.inr i) (Sum.inr j)) hdL y
    obtain ⟨tau,htau,hH,hL0,hL⟩ := split_threshold d a ha
    have hCross : ∀ y : Point (Coord d),
        ‖Matrix.toEuclideanLin (crossCoefficients aH S) y‖ ≤ (2*D) * ‖y‖ := by
      intro y
      exact crossCompletion_norm_le S aH aL hD htau hH hL0 hL hS hd y
    have htotal := upperBlock_norm_le (completion d aH SH) (completion d aL SL)
      (crossCoefficients aH S) hK (by positivity : 0 ≤ 2*D) hCH hCL hCross z
    convert htotal using 1 <;> first | rfl | (simp only [K]; push_cast; ring_nf <;> rfl)

open MvPolynomial

def polynomialVector (d : ℕ) (a : Coord d → ℝ)
    (S : Matrix (Coord d) (Coord d) ℝ) (i : Coord d) : MvPolynomial (Coord d) ℝ :=
  ∑ j, C (completion d a S i j) * X j

def quadraticPolynomial (d : ℕ) (S : Matrix (Coord d) (Coord d) ℝ) :
    MvPolynomial (Coord d) ℝ := ∑ i, ∑ j, C (S i j) * X i * X j

theorem polynomialVector_homogeneous (d : ℕ) (a : Coord d → ℝ)
    (S : Matrix (Coord d) (Coord d) ℝ) (i : Coord d) :
    (polynomialVector d a S i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (MvPolynomial.isHomogeneous_X ℝ j).C_mul _

theorem quadraticPolynomial_homogeneous (d : ℕ) (S : Matrix (Coord d) (Coord d) ℝ) :
    (quadraticPolynomial d S).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact ((MvPolynomial.isHomogeneous_X ℝ i).C_mul _).mul (MvPolynomial.isHomogeneous_X ℝ j)

/-- The complete recursive construction divides the actual full quadratic
polynomial, with no sphere quotient or completion premise. -/
theorem polynomial_identity (d : ℕ) (a : Coord d → ℝ)
    (S : Matrix (Coord d) (Coord d) ℝ) (ha : ∀ i, a i ≠ 0)
    (hS : ∀ i j, S i j = S j i) :
    (∑ i, C (a i) * X i * polynomialVector d a S i) = quadraticPolynomial d S := by
  apply MvPolynomial.funext
  intro x
  simp only [polynomialVector, quadraticPolynomial, map_sum, map_mul, eval_C, eval_X, Finset.mul_sum]
  have hp (i j : Coord d) :
      a i*x i*(completion d a S i j*x j) + a j*x j*(completion d a S j i*x i) =
      2*(S i j*x i*x j) := by
    linear_combination (x i*x j)*completion_entry_identity d a S ha hS i j
  have hs : (∑ i, ∑ j, (a i*x i*(completion d a S i j*x j) +
      a j*x j*(completion d a S j i*x i))) = ∑ i, ∑ j, 2*(S i j*x i*x j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hp i j
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have ht : (∑ i, ∑ j, a j*x j*(completion d a S j i*x i)) =
      ∑ i, ∑ j, a i*x i*(completion d a S i j*x j) := by rw [Finset.sum_comm]
  rw [ht] at hs
  simp only [← Finset.mul_sum] at hs ⊢
  linarith

theorem polynomialVector_eval (d : ℕ) (a : Coord d → ℝ)
    (S : Matrix (Coord d) (Coord d) ℝ) (x : Point (Coord d)) (i : Coord d) :
    eval (fun j => x j) (polynomialVector d a S i) = Matrix.toEuclideanLin (completion d a S) x i := by
  simp [polynomialVector, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

theorem quadraticPolynomial_eval (d : ℕ) (S : Matrix (Coord d) (Coord d) ℝ)
    (x : Point (Coord d)) :
    eval (fun j => x j) (quadraticPolynomial d S) = matrixForm S x x := by
  simp only [quadraticPolynomial, map_sum, map_mul, eval_C, eval_X, matrixForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem polynomialVector_norm_le (d : ℕ) (a : Coord d → ℝ)
    (S : Matrix (Coord d) (Coord d) ℝ) (ha : OrderedPositive d a)
    {D : ℝ} (hD : 0 ≤ D) (hS : ∀ i j, S i j = S j i)
    (hdom : ∀ z : Point (Coord d), |eval (fun i => z i) (quadraticPolynomial d S)| ≤
      D * ‖diagonal a z‖ * ‖z‖) (x : Point (Coord d)) :
    ‖(WithLp.equiv 2 (Coord d → ℝ)).symm
      (fun i => eval (fun j => x j) (polynomialVector d a S i))‖ ≤
      D * (1+2*(d:ℝ)) * ‖x‖ := by
  have hv : (WithLp.equiv 2 (Coord d → ℝ)).symm
      (fun i => eval (fun j => x j) (polynomialVector d a S i)) =
      Matrix.toEuclideanLin (completion d a S) x := by
    ext i
    exact polynomialVector_eval d a S x i
  rw [hv]
  apply completion_norm_le d a S ha hD hS
  intro z
  simpa only [quadraticPolynomial_eval] using hdom z

end OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticTree
