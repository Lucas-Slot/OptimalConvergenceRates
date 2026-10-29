import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
/-! Dimension-free polarization for an actual symmetric continuous four-linear form.
No polynomial-to-multilinear representation theorem is assumed or asserted. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def quarticApply (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)
    (a b c d : E) : ℝ := A ![a, b, c, d]

def SymmetricQuarticForm (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 4)) (v : Fin 4 → E), A (fun i ↦ v (σ i)) = A v

def quarticDiagonal (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (x : E) : ℝ :=
  quarticApply A x x x x

variable (A : ContinuousMultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)

theorem quarticDiagonal_eq (x : E) : quarticDiagonal A x = A (fun _ ↦ x) := by
  unfold quarticDiagonal quarticApply
  congr 1
  ext i
  fin_cases i <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem quarticTuple_update0 (a b c d x : E) :
    Function.update ![a, b, c, d] (0 : Fin 4) x = ![x, b, c, d] := by
  ext j
  fin_cases j <;> simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem quarticTuple_update1 (a b c d x : E) :
    Function.update ![a, b, c, d] (1 : Fin 4) x = ![a, x, c, d] := by
  ext j
  fin_cases j <;> simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem quarticTuple_update2 (a b c d x : E) :
    Function.update ![a, b, c, d] (2 : Fin 4) x = ![a, b, x, d] := by
  ext j
  fin_cases j <;> simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem quarticTuple_update3 (a b c d x : E) :
    Function.update ![a, b, c, d] (3 : Fin 4) x = ![a, b, c, x] := by
  ext j
  fin_cases j <;> simp

theorem quarticApply_add0 (b c d x y : E) :
    quarticApply A (x + y) b c d =
      quarticApply A x b c d + quarticApply A y b c d := by
  have h := A.map_update_add ![(0 : E), b, c, d] (0 : Fin 4) x y
  simpa only [quarticApply, quarticTuple_update0] using! h

theorem quarticApply_add1 (a c d x y : E) :
    quarticApply A a (x + y) c d =
      quarticApply A a x c d + quarticApply A a y c d := by
  have h := A.map_update_add ![a, (0 : E), c, d] (1 : Fin 4) x y
  simpa only [quarticApply, quarticTuple_update1] using! h

theorem quarticApply_add2 (a b d x y : E) :
    quarticApply A a b (x + y) d =
      quarticApply A a b x d + quarticApply A a b y d := by
  have h := A.map_update_add ![a, b, (0 : E), d] (2 : Fin 4) x y
  simpa only [quarticApply, quarticTuple_update2] using! h

theorem quarticApply_add3 (a b c x y : E) :
    quarticApply A a b c (x + y) =
      quarticApply A a b c x + quarticApply A a b c y := by
  have h := A.map_update_add ![a, b, c, (0 : E)] (3 : Fin 4) x y
  simpa only [quarticApply, quarticTuple_update3] using! h

theorem quarticApply_neg0 (b c d x : E) :
    quarticApply A (-x) b c d = -quarticApply A x b c d := by
  have h := A.map_update_neg ![(0 : E), b, c, d] (0 : Fin 4) x
  simpa only [quarticApply, quarticTuple_update0] using! h

theorem quarticApply_neg1 (a c d x : E) :
    quarticApply A a (-x) c d = -quarticApply A a x c d := by
  have h := A.map_update_neg ![a, (0 : E), c, d] (1 : Fin 4) x
  simpa only [quarticApply, quarticTuple_update1] using! h

theorem quarticApply_neg2 (a b d x : E) :
    quarticApply A a b (-x) d = -quarticApply A a b x d := by
  have h := A.map_update_neg ![a, b, (0 : E), d] (2 : Fin 4) x
  simpa only [quarticApply, quarticTuple_update2] using! h

theorem quarticApply_neg3 (a b c x : E) :
    quarticApply A a b c (-x) = -quarticApply A a b c x := by
  have h := A.map_update_neg ![a, b, c, (0 : E)] (3 : Fin 4) x
  simpa only [quarticApply, quarticTuple_update3] using! h

def quarticSign : Bool → ℝ
  | true => 1
  | false => -1

def quarticHalfPolarizationSum (a b c d : E) : ℝ :=
  ∑ s1 : Bool, ∑ s2 : Bool, ∑ s3 : Bool,
    (quarticSign s1 * quarticSign s2 * quarticSign s3) *
      quarticDiagonal A (a + quarticSign s1 • b + quarticSign s2 • c + quarticSign s3 • d)


theorem quarticApply_permutation (hA : SymmetricQuarticForm A) (v : Fin 4 → E)
    (f : Fin 4 → Fin 4) (hf : Function.Bijective f) :
    A (fun i ↦ v (f i)) = A v :=
  hA (Equiv.ofBijective f hf) v

theorem quarticApply_swap0 (hA : SymmetricQuarticForm A) (a b c d : E) :
    quarticApply A b a c d = quarticApply A a b c d := by
  have h := quarticApply_permutation A hA ![a, b, c, d] (![1, 0, 2, 3]) (by decide)
  have hv : (fun i ↦ (![a, b, c, d] : Fin 4 → E) ((![1, 0, 2, 3] : Fin 4 → Fin 4) i)) =
      ![b, a, c, d] := by ext i; fin_cases i <;> rfl
  rw [hv] at h
  exact h

theorem quarticApply_swap1 (hA : SymmetricQuarticForm A) (a b c d : E) :
    quarticApply A a c b d = quarticApply A a b c d := by
  have h := quarticApply_permutation A hA ![a, b, c, d] (![0, 2, 1, 3]) (by decide)
  have hv : (fun i ↦ (![a, b, c, d] : Fin 4 → E) ((![0, 2, 1, 3] : Fin 4 → Fin 4) i)) =
      ![a, c, b, d] := by ext i; fin_cases i <;> rfl
  rw [hv] at h
  exact h

theorem quarticApply_swap2 (hA : SymmetricQuarticForm A) (a b c d : E) :
    quarticApply A a b d c = quarticApply A a b c d := by
  have h := quarticApply_permutation A hA ![a, b, c, d] (![0, 1, 3, 2]) (by decide)
  have hv : (fun i ↦ (![a, b, c, d] : Fin 4 → E) ((![0, 1, 3, 2] : Fin 4 → Fin 4) i)) =
      ![a, b, d, c] := by ext i; fin_cases i <;> rfl
  rw [hv] at h
  exact h

def quarticOddDifference (x y : E) : ℝ :=
  quarticDiagonal A (x + y) - quarticDiagonal A (x - y)

set_option maxHeartbeats 1000000 in
theorem quarticOddDifference_eq (hA : SymmetricQuarticForm A) (x y : E) :
    quarticOddDifference A x y =
      8 * quarticApply A x x x y + 8 * quarticApply A x y y y := by
  simp only [quarticOddDifference, quarticDiagonal, sub_eq_add_neg,
    quarticApply_add0, quarticApply_add1, quarticApply_add2, quarticApply_add3,
    quarticApply_neg0, quarticApply_neg1, quarticApply_neg2, quarticApply_neg3]
  simp only [quarticApply_swap0 A hA, quarticApply_swap1 A hA, quarticApply_swap2 A hA]
  ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem quarticHalfPolarization_identity (hA : SymmetricQuarticForm A) (a b c d : E) :
    quarticHalfPolarizationSum A a b c d = 192 * quarticApply A a b c d := by
  have hgroup : quarticHalfPolarizationSum A a b c d =
      quarticOddDifference A (a + b + c) d -
        quarticOddDifference A (a + b - c) d -
        quarticOddDifference A (a - b + c) d +
        quarticOddDifference A (a - b - c) d := by
    simp only [quarticHalfPolarizationSum, Fintype.sum_bool, quarticSign,
      ite_true, ite_false, one_smul, neg_one_smul, one_mul, mul_one, neg_mul, mul_neg,
      neg_neg, quarticOddDifference, sub_eq_add_neg]
    ring
  rw [hgroup]
  simp only [quarticOddDifference_eq A hA]
  simp only [sub_eq_add_neg, quarticApply_add0, quarticApply_add1,
    quarticApply_add2, quarticApply_add3, quarticApply_neg0, quarticApply_neg1,
    quarticApply_neg2, quarticApply_neg3]
  simp only [quarticApply_swap0 A hA, quarticApply_swap1 A hA, quarticApply_swap2 A hA]
  ring

end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
