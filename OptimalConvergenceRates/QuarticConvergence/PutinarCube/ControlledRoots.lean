/-
  Controlled retained roots for the Putinar extension.

  This file is deliberately an adapter over `Analysis/FiniteAtomFilter`: it
  keeps the exact retained roots constructed there, together with their
  regularity, dyadic labels, and canonical Boolean-filter polynomials, while
  retaining the atom-side overlap/jet budget needed by the later cube repair.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FiniteAtomFilter

open MvPolynomial Finset Set
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- Decreasing the analytic error constant preserves the complete atom-side
manuscript input. In particular, no roots, radii, scale labels, or regularity
data are changed. -/
def finiteRetainedRootManuscriptInput_monoErrorConstant
    {n : ℕ} {C E₁ E₂ : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (input : FiniteRetainedRootManuscriptInput atoms E₂)
    (hE₁ : 0 ≤ E₁) (hE : E₁ ≤ E₂) :
    FiniteRetainedRootManuscriptInput atoms E₁ := by
  have hjet : 0 ≤ input.regular.jetBound := input.regular.jetBound_nonneg
  have hoverlap : 0 ≤ (atoms.overlapBound : ℝ) := Nat.cast_nonneg _
  have hfar : 0 ≤
      (atoms.overlapBound : ℝ) + 2 * input.farShellConstant :=
    add_nonneg hoverlap (mul_nonneg (by norm_num) input.farShellConstant_nonneg)
  have hjetE : input.regular.jetBound * E₁ ≤
      input.regular.jetBound * E₂ :=
    mul_le_mul_of_nonneg_left hE hjet
  have hjetE₁ : 0 ≤ input.regular.jetBound * E₁ :=
    mul_nonneg hjet hE₁
  refine {
    regular := input.regular
    dyadic := input.dyadic
    filterIncrementOscillation := input.filterIncrementOscillation
    farShellCount := input.farShellCount
    farShell := input.farShell
    farShellConstant := input.farShellConstant
    farShellConstant_nonneg := input.farShellConstant_nonneg
    scale_far_shell_distance := input.scale_far_shell_distance
    scale_far_shell_card_budget := input.scale_far_shell_card_budget
    cross_constant_budget := ?_
    square_constant_budget := ?_ }
  · apply le_trans _ input.cross_constant_budget
    apply mul_le_mul_of_nonneg_left _ hoverlap
    apply mul_le_mul_of_nonneg_left hjetE hjet
  · apply le_trans _ input.square_constant_budget
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16 / 15)
    apply mul_le_mul_of_nonneg_right _ hfar
    exact pow_le_pow_left₀ hjetE₁ hjetE 2

/-- The public controlled-root package. The Boolean-filter data are dependent
on `atoms`, so the polynomial approximants are definitionally the filters of
the same roots carrying `regular` and `dyadic` control. The final field is
the atom budget needed before any root-count-dependent estimate is attempted. -/
structure FiniteControlledRootData (n : ℕ) (C : ℝ) (k : ℕ)
    (F : MvPolynomial (Fin n) ℝ) where
  atoms : FiniteRetainedRootData n C k F
  regular : FiniteRetainedRootRegularity atoms
  dyadic : FiniteRetainedRootDyadic atoms
  filterIncrementOscillation :
    FiniteRetainedRootFilterIncrementOscillation atoms regular
  manuscript : FiniteBooleanFilterManuscriptBounds atoms regular
  filter : FiniteBooleanFilterData atoms
  overlap_jetBound_sq_le :
    (atoms.overlapBound : ℝ) * regular.jetBound ^ 2 ≤ C / 4

/-- Recombine a controlled package into the established scale-resolved API.
This is the compatibility map used by all existing quartic sphere assembly
theorems. -/
def FiniteControlledRootData.toFilteredRootScaleData
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F) :
    FiniteFilteredRootScaleData n C k F :=
  data.atoms.withBooleanFilterData data.filter

/-- The combined package retains exactly the original root family. -/
@[simp] theorem FiniteControlledRootData.toFilteredRootScaleData_root
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F) :
    data.toFilteredRootScaleData.root = data.atoms.root := rfl

/-- The combined package retains exactly the canonical filtered polynomial
family stored in its Boolean-filter data. -/
@[simp] theorem FiniteControlledRootData.toFilteredRootScaleData_polynomial
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F) :
    data.toFilteredRootScaleData.polynomial = data.filter.polynomial := rfl

/-- The controlled package retains the second-difference estimate for the
one-step filter error on the same roots used by its Boolean-filter
polynomials. -/
def FiniteControlledRootData.filterErrorSecondDifference
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F) (hn : 2 ≤ n) :
    FiniteRetainedRootFilterErrorSecondDifference data.atoms data.regular :=
  data.filterIncrementOscillation.toSecondDifference hn

/-- Uniform existence of controlled retained roots. -/
def HasFiniteControlledRootData (n : ℕ) (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k → Nonempty (FiniteControlledRootData n C k F)

/-- For every sphere dimension at least three, the existing atom construction
produces positive uniform constants and a controlled retained-root package.

The construction asks the atom layer for the enlarged constant `E + 1`.
Downward coercion supplies the actual Boolean-filter constant `E`, while the
extra unit yields the independent budget
`overlapBound * jetBound² ≤ C / 4` on the very same roots. -/
theorem finiteControlledRootData {n : ℕ} (hn : 3 ≤ n) :
    ∃ (C : ℝ) (k₀ : ℕ), 0 < C ∧ 1 ≤ k₀ ∧
      HasFiniteControlledRootData n C k₀ := by
  obtain ⟨E, hE, hmake⟩ :=
    exists_finiteBooleanFilterManuscriptBounds_of_secondDifference hn
  have hEshift : 0 ≤ E + 1 := by linarith
  obtain ⟨C, k₀, hC, hk₀, hinput⟩ :=
    finiteRetainedRootManuscriptInput hn (E + 1) hEshift
  refine ⟨C, k₀, hC, hk₀, ?_⟩
  intro F hF hnorm k hk
  let stage := Classical.choice (hinput F hF hnorm k hk)
  let atoms := stage.1
  let shifted := stage.2
  let input : FiniteRetainedRootManuscriptInput atoms E :=
    finiteRetainedRootManuscriptInput_monoErrorConstant shifted hE (by linarith)
  let packingConstant : ℝ :=
    (atoms.overlapBound : ℝ) + 2 * input.farShellConstant
  have hkone : 1 ≤ k := hk₀.trans hk
  have hpackingConstant : 0 ≤ packingConstant :=
    add_nonneg (Nat.cast_nonneg atoms.overlapBound)
      (mul_nonneg (by norm_num) input.farShellConstant_nonneg)
  have hpacking : ∀ x ∈ sphereSet n, ∀ j : Fin atoms.J,
      ∑ i ∈ Finset.univ.filter (fun i => atoms.scale i = j),
        sphereChordalDecayWeight (2 * (n + 3))
          (atoms.center i) (atoms.radius i) x ≤ packingConstant := by
    intro x hx j
    apply atoms.sum_scale_decayWeight_le_overlap_add_of_far x hx j
    exact atoms.sum_scale_far_decayWeight_le_two_mul_of_shell_bounds x j
      (input.farShell ⟨x, hx⟩) input.farShellConstant_nonneg
      (by
        intro q
        exact atoms.sum_decayWeight_le_half_pow_of_shell
          ((Finset.univ.filter (fun i => atoms.scale i = j ∧
            ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
              (fun i => input.farShell ⟨x, hx⟩ i = q)) x
          (input.scale_far_shell_distance x hx j q)
          (input.scale_far_shell_card_budget x hx j q))
  have hbounds := hmake atoms input.regular hkone
    (input.filterIncrementOscillation.toSecondDifference (by omega))
    packingConstant hpackingConstant hpacking input.cross_constant_budget
    input.square_constant_budget
  let manuscript := Classical.choice hbounds
  let localized := manuscript.toLocalizedBounds input.dyadic hkone
  let analytic := localized.toAnalyticBounds hkone
  let bounds := analytic.toBooleanFilterBounds hkone
  let filter := bounds.toBooleanFilterData input.regular (by omega)
  have hcontrolled :
      (atoms.overlapBound : ℝ) * input.regular.jetBound ^ 2 ≤ C / 4 := by
    apply le_trans _ shifted.cross_constant_budget
    have hoverlap : 0 ≤ (atoms.overlapBound : ℝ) := Nat.cast_nonneg _
    apply mul_le_mul_of_nonneg_left _ hoverlap
    rw [pow_two]
    have hjet := input.regular.jetBound_nonneg
    calc
      input.regular.jetBound * input.regular.jetBound =
          input.regular.jetBound * (input.regular.jetBound * 1) := by ring
      _ ≤ input.regular.jetBound * (input.regular.jetBound * (E + 1)) := by
        gcongr
        linarith
  exact ⟨{
    atoms := atoms
    regular := input.regular
    dyadic := input.dyadic
    filterIncrementOscillation := input.filterIncrementOscillation
    manuscript := manuscript
    filter := filter
    overlap_jetBound_sq_le := hcontrolled }⟩

end QuarticConvergence
end OptimalConvergenceRates

end
