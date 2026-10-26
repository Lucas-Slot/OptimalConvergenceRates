import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.LinearMap
/-! Concrete operator-ball duality for bounded weighted symmetric completions.
The scalar-domination-to-trace step is a separate spectral obligation. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticExistence

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

section FiniteDimensionalSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A real functional attains its dual norm, with the positive sign,
on the actual compact operator ball. -/
theorem dual_norm_attained (f : E →L[ℝ] ℝ) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ f x = ‖f‖ := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    (show (Metric.closedBall (0 : E) 1).Nonempty from ⟨0, by simp⟩) f.continuous.continuousOn
  have hxn : ‖x‖ ≤ 1 := by simpa using hx
  have hm : 0 ≤ f x := by simpa using hmax (show (0:E) ∈ Metric.closedBall 0 1 by simp)
  have hb (y : E) (hy : y ∈ Metric.closedBall 0 1) : ‖f y‖ ≤ f x := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have hneg : -y ∈ Metric.closedBall (0:E) 1 := by simpa using hy
      have hh : f (-y) ≤ f x := hmax hneg
      simp only [map_neg] at hh
      linarith
    · exact hmax hy
  have hn : ‖f‖ ≤ f x := by
    rw [← f.sSup_unitClosedBall_eq_norm]
    apply csSup_le
    · exact ⟨0, 0, by simp, by simp⟩
    · rintro r ⟨y, hy, rfl⟩
      exact hb y hy
  refine ⟨x, hxn, le_antisymm ?_ hn⟩
  calc
    f x ≤ ‖f x‖ := le_abs_self _
    _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ ≤ ‖f‖ := by nlinarith [norm_nonneg f]

theorem dual_norm_attained_radius (f : E →L[ℝ] ℝ) {b : ℝ} (hb : 0 ≤ b) :
    ∃ x : E, ‖x‖ ≤ b ∧ f x = b * ‖f‖ := by
  obtain ⟨x,hx,hfx⟩ := dual_norm_attained f
  refine ⟨b • x, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    nlinarith
  · simp [map_smul, hfx]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A concrete compact-ball separation theorem: all dual support tests
give an actual bounded preimage, without a chosen right inverse. -/
theorem bounded_preimage_of_dual (T : E →L[ℝ] F) (y : F) {b : ℝ} (hb : 0 ≤ b)
    (hdual : ∀ f : F →L[ℝ] ℝ, f y ≤ b * ‖f.comp T‖) :
    ∃ x : E, ‖x‖ ≤ b ∧ T x = y := by
  let K := T '' Metric.closedBall (0:E) b
  have hkc : IsCompact K := (isCompact_closedBall (0:E) b).image T.continuous
  have hkv : Convex ℝ K := (convex_closedBall (0:E) b).linear_image T.toLinearMap
  have hy : y ∈ K := by
    by_contra hn
    obtain ⟨f,u,hku,huy⟩ := geometric_hahn_banach_closed_point hkv hkc.isClosed hn
    obtain ⟨x,hx,hfx⟩ := dual_norm_attained_radius (f.comp T) hb
    have hxK : T x ∈ K := ⟨x, by simpa using hx, rfl⟩
    have hh := hku (T x) hxK
    have hbound := hdual f
    change f (T x) = b * ‖f.comp T‖ at hfx
    linarith
  obtain ⟨x,hx,hxy⟩ := hy
  exact ⟨x, by simpa using hx, hxy⟩

end FiniteDimensionalSupport

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Mat := Matrix ι ι ℝ

def tracePair (X Y : Mat (ι := ι)) : ℝ := Matrix.trace (X.transpose * Y)

omit [DecidableEq ι] in
theorem tracePair_entries (X Y : Mat (ι := ι)) :
    tracePair X Y = ∑ i, ∑ j, X i j * Y i j := by
  simp only [tracePair, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

omit [DecidableEq ι] in
theorem tracePair_comm (X Y : Mat (ι := ι)) : tracePair X Y = tracePair Y X := by
  simp only [tracePair_entries]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def traceLinear (X : Mat (ι := ι)) : Mat (ι:=ι) →ₗ[ℝ] ℝ where
  toFun := tracePair X
  map_add' A B := by simp [tracePair, Matrix.mul_add, Matrix.trace_add]
  map_smul' r A := by simp [tracePair, Matrix.mul_smul, Matrix.trace_smul]

def traceFunctional (X : Mat (ι := ι)) : Mat (ι:=ι) →L[ℝ] ℝ :=
  (traceLinear X).toContinuousLinearMap

def dualOperatorNorm (X : Mat (ι := ι)) : ℝ := ‖traceFunctional X‖

theorem dualOperatorNorm_nonneg (X : Mat (ι := ι)) : 0 ≤ dualOperatorNorm X :=
  norm_nonneg (traceFunctional X)

theorem traceFunctional_apply (X Y : Mat (ι := ι)) :
    traceFunctional X Y = tracePair X Y := rfl

theorem tracePair_le_dualOperatorNorm (X Y : Mat (ι := ι)) :
    |tracePair X Y| ≤ dualOperatorNorm X * ‖Y‖ :=
  (traceFunctional X).le_opNorm Y

def matrixSym (A : Mat (ι := ι)) : Mat (ι:=ι) :=
  (1/2:ℝ) • (A+A.transpose)

omit [Fintype ι] [DecidableEq ι] in
theorem matrixSym_transpose (A : Mat (ι := ι)) : (matrixSym A).transpose = matrixSym A := by
  ext i j
  simp [matrixSym, Matrix.transpose_apply, add_comm]
  ring

theorem tracePair_sym_left (X Y : Mat (ι := ι)) (hY : Y.transpose = Y) :
    tracePair (matrixSym X) Y = tracePair X Y := by
  have ht : Matrix.trace (X*Y) = Matrix.trace (X.transpose*Y) := by
    calc
      Matrix.trace (X*Y) = Matrix.trace ((X*Y).transpose) := (Matrix.trace_transpose _).symm
      _ = Matrix.trace (Y.transpose*X.transpose) := by rw [Matrix.transpose_mul]
      _ = Matrix.trace (X.transpose*Y) := by rw [hY, Matrix.trace_mul_comm]
  simp [tracePair, matrixSym, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, ht]
  ring

theorem tracePair_sym_right (X Y : Mat (ι := ι)) (hX : X.transpose = X) :
    tracePair X (matrixSym Y) = tracePair X Y := by
  rw [tracePair_comm, tracePair_sym_left Y X hX, tracePair_comm]

def weightedMap (L : Mat (ι := ι)) : Mat (ι:=ι) →ₗ[ℝ] Mat (ι:=ι) where
  toFun C := matrixSym (L*C)
  map_add' C D := by
    ext i j
    simp [matrixSym, Matrix.mul_add, Matrix.add_apply, Matrix.transpose_apply]
    ring
  map_smul' r C := by
    ext i j
    simp [matrixSym, Matrix.mul_smul, Matrix.smul_apply, Matrix.transpose_apply]
    ring

theorem weightedMap_symmetric (L C : Mat (ι := ι)) :
    (weightedMap L C).transpose = weightedMap L C := matrixSym_transpose _

theorem weightedMap_eq (L C : Mat (ι := ι)) (hL : L.transpose = L) :
    weightedMap L C = (1/2:ℝ) • (L*C+C.transpose*L) := by
  simp [weightedMap, matrixSym, Matrix.transpose_mul, hL]

theorem weighted_trace_adjoint (L X C : Mat (ι := ι))
    (hL : L.transpose = L) (hX : X.transpose = X) :
    tracePair X (weightedMap L C) = tracePair (L*X) C := by
  change tracePair X (matrixSym (L*C)) = _
  rw [tracePair_sym_right X (L*C) hX]
  simp only [tracePair, Matrix.transpose_mul, hL, Matrix.mul_assoc]

def functionalMatrix (f : Mat (ι := ι) →L[ℝ] ℝ) : Mat (ι:=ι) :=
  fun i j => f (Matrix.single i j 1)

theorem functionalMatrix_represents (f : Mat (ι := ι) →L[ℝ] ℝ) (Y : Mat (ι := ι)) :
    f Y = tracePair (functionalMatrix f) Y := by
  rw [tracePair_entries]
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : Matrix.single i j (Y i j) =
      (Y i j) • Matrix.single i j (1:ℝ) := by simp
  rw [he, map_smul]
  simp [functionalMatrix, mul_comm]

theorem symmetric_test_representation (f : Mat (ι := ι) →L[ℝ] ℝ) :
    ∃ X : Mat (ι:=ι), X.transpose=X ∧
      ∀ Y : Mat (ι:=ι), Y.transpose=Y → f Y=tracePair X Y := by
  refine ⟨matrixSym (functionalMatrix f), matrixSym_transpose _, ?_⟩
  intro Y hY
  rw [tracePair_sym_left _ _ hY, functionalMatrix_represents]

def completionSet (L : Mat (ι := ι)) (b : ℝ) : Set (Mat (ι:=ι)) :=
  (weightedMap L).toContinuousLinearMap '' Metric.closedBall 0 b

theorem completionSet_isCompact (L : Mat (ι := ι)) (b : ℝ) :
    IsCompact (completionSet L b) :=
  (isCompact_closedBall (0 : Mat (ι:=ι)) b).image
    (weightedMap L).toContinuousLinearMap.continuous

theorem completionSet_isClosed (L : Mat (ι := ι)) (b : ℝ) :
    IsClosed (completionSet L b) := (completionSet_isCompact L b).isClosed

theorem completionSet_convex (L : Mat (ι := ι)) (b : ℝ) :
    Convex ℝ (completionSet L b) :=
  (convex_closedBall (0 : Mat (ι:=ι)) b).linear_image (weightedMap L)

/-- This is the actual support function of the bounded completion set.
The norm is the dual of the Euclidean operator norm, defined by a trace
functional; no singular-value formula is assumed. -/
theorem weighted_support_attained (L X : Mat (ι := ι)) (hL : L.transpose = L)
    (hX : X.transpose = X) {b : ℝ} (hb : 0 ≤ b) :
    ∃ C : Mat (ι:=ι), ‖C‖ ≤ b ∧
      tracePair X (weightedMap L C) = b * dualOperatorNorm (L*X) := by
  obtain ⟨C,hC,hval⟩ := dual_norm_attained_radius (traceFunctional (L*X)) hb
  refine ⟨C,hC,?_⟩
  rw [weighted_trace_adjoint L X C hL hX]
  exact hval

/-- The trace-test-to-completion implication is unconditional functional
analysis. Deriving its explicit trace hypothesis from scalar quadratic
domination is a separate polar/spectral lemma, not assumed as a theorem. -/
theorem bounded_completion_of_trace_tests (L S : Mat (ι := ι))
    (hL : L.transpose = L) (hS : S.transpose = S) {b : ℝ} (hb : 0 ≤ b)
    (htest : ∀ X : Mat (ι:=ι), X.transpose=X →
      |tracePair X S| ≤ b * dualOperatorNorm (L*X)) :
    ∃ C : Mat (ι:=ι), ‖C‖ ≤ b ∧ weightedMap L C = S := by
  apply bounded_preimage_of_dual (weightedMap L).toContinuousLinearMap S hb
  intro f
  obtain ⟨X,hX,hrep⟩ := symmetric_test_representation f
  have hc : f.comp (weightedMap L).toContinuousLinearMap = traceFunctional (L*X) := by
    ext C
    change f (weightedMap L C) = tracePair (L*X) C
    rw [hrep _ (weightedMap_symmetric L C), weighted_trace_adjoint L X C hL hX]
  rw [hrep _ hS, hc]
  exact (le_abs_self _).trans (htest X hX)

theorem trace_tests_of_bounded_completion (L S C : Mat (ι := ι))
    (hL : L.transpose = L) {b : ℝ} (hC : ‖C‖ ≤ b) (heq : weightedMap L C = S) :
    ∀ X : Mat (ι:=ι), X.transpose=X →
      |tracePair X S| ≤ b * dualOperatorNorm (L*X) := by
  intro X hX
  rw [← heq, weighted_trace_adjoint L X C hL hX]
  calc
    |tracePair (L*X) C| ≤ dualOperatorNorm (L*X) * ‖C‖ :=
      tracePair_le_dualOperatorNorm _ _
    _ ≤ dualOperatorNorm (L*X) * b :=
      mul_le_mul_of_nonneg_left hC (dualOperatorNorm_nonneg _)
    _ = _ := mul_comm _ _

/-- Exact bounded-completion characterization, including singular L
and zero radius, in actual operator norm. -/
theorem bounded_completion_iff_trace_tests (L S : Mat (ι := ι))
    (hL : L.transpose = L) (hS : S.transpose = S) {b : ℝ} (hb : 0 ≤ b) :
    (∃ C : Mat (ι:=ι), ‖C‖ ≤ b ∧ weightedMap L C=S) ↔
      ∀ X : Mat (ι:=ι), X.transpose=X →
        |tracePair X S| ≤ b * dualOperatorNorm (L*X) := by
  constructor
  · rintro ⟨C,hC,heq⟩
    exact trace_tests_of_bounded_completion L S C hL hC heq
  · exact bounded_completion_of_trace_tests L S hL hS hb

theorem exists_explicit_matrix_completion_of_trace_tests (L S : Mat (ι := ι))
    (hL : L.transpose = L) (hS : S.transpose = S) {D : ℝ} (hD : 0 ≤ D)
    (htest : ∀ X : Mat (ι:=ι), X.transpose=X →
      |tracePair X S| ≤ (2*D) * dualOperatorNorm (L*X)) :
    ∃ C : Mat (ι:=ι), ‖C‖ ≤ 2*D ∧
      (1/2:ℝ) • (L*C+C.transpose*L)=S := by
  obtain ⟨C,hC,heq⟩ := bounded_completion_of_trace_tests L S hL hS (by positivity) htest
  exact ⟨C,hC,by simpa only [weightedMap_eq L C hL] using heq⟩

theorem euclidean_apply_le_operatorNorm (C : Mat (ι := ι)) (x : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanLin C x‖ ≤ ‖C‖ * ‖x‖ :=
  (Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℝ) C).le_opNorm x

theorem exists_completion_apply_bound_of_trace_tests (L S : Mat (ι := ι))
    (hL : L.transpose = L) (hS : S.transpose = S) {D : ℝ} (hD : 0 ≤ D)
    (htest : ∀ X : Mat (ι:=ι), X.transpose=X →
      |tracePair X S| ≤ (2*D) * dualOperatorNorm (L*X)) :
    ∃ C : Mat (ι:=ι), (1/2:ℝ) • (L*C+C.transpose*L)=S ∧
      ∀ x : EuclideanSpace ℝ ι, ‖Matrix.toEuclideanLin C x‖ ≤ (2*D) * ‖x‖ := by
  obtain ⟨C,hC,heq⟩ := exists_explicit_matrix_completion_of_trace_tests L S hL hS hD htest
  refine ⟨C,heq,?_⟩
  intro x
  exact (euclidean_apply_le_operatorNorm C x).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

def rankOne (x : EuclideanSpace ℝ ι) : Mat (ι:=ι) := fun i j => x i * x j

def quadraticValue (S : Mat (ι := ι)) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ j, S i j * x i * x j

omit [DecidableEq ι] in
theorem tracePair_rankOne (S : Mat (ι := ι)) (x : EuclideanSpace ℝ ι) :
    tracePair S (rankOne x) = quadraticValue S x := by
  simp only [tracePair_entries, rankOne, quadraticValue]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The scalar source inequality gives the required trace test once an
actual finite signed rank-one decomposition with the stated cost is
provided. Constructing that cost-controlled decomposition is the precise
remaining polar/spectral obligation. -/
theorem trace_bound_of_rank_one_budget (L S X : Mat (ι := ι)) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ x : EuclideanSpace ℝ ι,
      |quadraticValue S x| ≤ D * ‖Matrix.toEuclideanLin L x‖ * ‖x‖)
    {m : ℕ} (v : Fin m → EuclideanSpace ℝ ι) (eps : Fin m → ℝ)
    (heps : ∀ k, |eps k| ≤ 1)
    (hX : X=∑ k, eps k • rankOne (v k))
    (hcost : (∑ k, ‖Matrix.toEuclideanLin L (v k)‖ * ‖v k‖) ≤
      2 * dualOperatorNorm (L*X)) :
    |tracePair X S| ≤ (2*D) * dualOperatorNorm (L*X) := by
  rw [tracePair_comm]
  change |traceFunctional S X| ≤ _
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul, smul_eq_mul, traceFunctional_apply, tracePair_rankOne]
  calc
    |∑ k, eps k * quadraticValue S (v k)| ≤ ∑ k, |eps k * quadraticValue S (v k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, D * ‖Matrix.toEuclideanLin L (v k)‖ * ‖v k‖ := by
      apply Finset.sum_le_sum
      intro k _
      calc
        |eps k * quadraticValue S (v k)| = |eps k| * |quadraticValue S (v k)| := abs_mul _ _
        _ ≤ 1 * |quadraticValue S (v k)| :=
          mul_le_mul_of_nonneg_right (heps k) (abs_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using hdom (v k)
    _ = D * (∑ k, ‖Matrix.toEuclideanLin L (v k)‖ * ‖v k‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ D * (2 * dualOperatorNorm (L*X)) := mul_le_mul_of_nonneg_left hcost hD
    _ = _ := by ring

theorem bounded_completion_of_rank_one_budgets (L S : Mat (ι := ι))
    (hL : L.transpose = L) (hS : S.transpose = S) {D : ℝ} (hD : 0 ≤ D)
    (hdom : ∀ x : EuclideanSpace ℝ ι,
      |quadraticValue S x| ≤ D * ‖Matrix.toEuclideanLin L x‖ * ‖x‖)
    (hgeometry : ∀ X : Mat (ι:=ι), X.transpose=X →
      ∃ (m : ℕ) (v : Fin m → EuclideanSpace ℝ ι) (eps : Fin m → ℝ),
        (∀ k, |eps k| ≤ 1) ∧ X=∑ k, eps k • rankOne (v k) ∧
        (∑ k, ‖Matrix.toEuclideanLin L (v k)‖ * ‖v k‖) ≤
          2 * dualOperatorNorm (L*X)) :
    ∃ C : Mat (ι:=ι), ‖C‖ ≤ 2*D ∧ (1/2:ℝ) • (L*C+C.transpose*L)=S := by
  apply exists_explicit_matrix_completion_of_trace_tests L S hL hS hD
  intro X hX
  obtain ⟨m,v,eps,heps,hdec,hcost⟩ := hgeometry X hX
  exact trace_bound_of_rank_one_budget L S X hD hdom v eps heps hdec hcost

end Matrices

end OptimalConvergenceRates.SphereDimensionBounds.WeightedQuadraticExistence
