/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/AtomInduction.lean

  Dimension induction and global assembly for Euclidean atoms.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.Atoms
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.CurvatureParentPatch
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.SplitAtomAssembly
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.BoundedUniformSplit

open Set
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence
/-- Uniform atoms for exactly the bounded-split side of the refined parent dichotomy.  The scale
threshold is chosen before the fine-cover cutoff constant; atom constants may depend on that
cutoff constant. -/
def HasUniformBoundedSplitParentAtomRealization (n : ℕ) : Prop :=
  ∀ A Cjet : ℝ, 1 ≤ A → 0 ≤ Cjet →
    ∃ sigmaMax : ℝ, 0 < sigmaMax ∧ sigmaMax ≤ 1 ∧
      ∀ parentDilation : ℝ, 4 * A ≤ parentDilation →
        ∀ sigma : ℝ, 0 < sigma → sigma ≤ sigmaMax →
          ∀ parentA : ℝ, 1 ≤ parentA →
            ∃ Katom : ℝ, ∃ B : ℕ, 0 < Katom ∧ 0 < B ∧
              ∀ {u : (Fin (n + 1) → ℝ) → ℝ} {parentB : ℕ},
                NormalizedNonnegativeC6 u → NonnegativeJetControl u Cjet →
                ∀ (cover : FineQuantitativeScaleCover
                    u parentDilation sigma parentA parentB) {i : ℕ},
                  i ∈ cover.active →
                  IntrinsicBoundedSplitPreprocessing n
                    (intrinsicRescaledPatch u (cover.center i)
                      (nonnegativeJetScale u (cover.center i))) Cjet →
                  Nonempty (LocalizedEuclideanAtomFamily
                    (fun z ↦ cover.intrinsicCutoff i z ^ 2 *
                      intrinsicRescaledPatch u (cover.center i)
                        (nonnegativeJetScale u (cover.center i)) z)
                    A 1 Katom B 0
                    (cover.radius i / nonnegativeJetScale u (cover.center i))
                    parentDilation)


/-- Assemble the bounded-base curvature branch from its quantitative split data. The exact split,
residual normalization, lower-dimensional recursion, interval partition, coordinate transport, and
localization, quantitative graph recurrence, and root/residual derivative estimates are all
proved explicitly. -/
theorem uniformBoundedSplitParentAtomRealization {n : ℕ}
    (hind : HasUniformEuclideanAtomDecomposition n) :
    HasUniformBoundedSplitParentAtomRealization n := by
  intro A Cjet hA hCjet
  let sigmaMax := boundedSplitSigmaMax Cjet
  refine ⟨sigmaMax, boundedSplitSigmaMax_pos hCjet,
    boundedSplitSigmaMax_le_one Cjet, ?_⟩
  intro parentDilation hparentDilation sigma hsigma hsigmaMax parentA hparentA
  let childRadius := curvatureChildRadiusCap A parentA
  have hchildRadius : 0 < childRadius :=
    curvatureChildRadiusCap_pos hA hparentA
  have hchildRadiusOne : childRadius ≤ 1 :=
    curvatureChildRadiusCap_le_one hA hparentA
  have hchildDilation : 1 ≤ 8 * A := by nlinarith
  rcases hind (8 * A) childRadius hchildDilation hchildRadius hchildRadiusOne with
    ⟨Cchild, Bchild, hCchild, hBchild, hchildren⟩
  rcases exists_scaledIntervalSquarePartition (8 * A) (by positivity) with
    ⟨Cp, Bp, hCp, hBp, hpartitions⟩
  rcases exists_uniformFineCoverQuantitativeCurvatureSplitOutput n hCjet
      parentA hparentA with
    ⟨Mmain, Azeta, Aresidual, hMmain, hAzeta, hAresidual, houtputs⟩
  let Cbase := max Mmain (curvatureResidualAtomConstant
    (parentA ^ 7) Cp Cchild Azeta Aresidual)
  let Katom := max 1 Cbase
  let B := 1 + Bchild * Bp
  have hKatom : 0 < Katom := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB : 0 < B := by dsimp [B]; omega
  refine ⟨Katom, B, hKatom, hB, ?_⟩
  intro u parentB hu hcontrol cover i hi prep
  rcases houtputs hu hcontrol cover hi hsigmaMax prep with ⟨data⟩
  rcases exists_localizedFineCoverCurvatureSplitAtomFamily cover hi prep data
      hA hparentA (hsigmaMax.trans (boundedSplitSigmaMax_le_half Cjet))
      hparentDilation hMmain hCchild.le (zero_le_one.trans hCp) hAzeta hAresidual
      hchildren hpartitions with ⟨atoms⟩
  exact ⟨atoms.increaseJetConstant (C' := Katom) (le_max_right _ _)⟩

/-- The localized parent realization is fully assembled from the value/curvature dichotomy. Both
branches, their quantitative derivative estimates, and their atom-family assembly are explicit; the
bounded-split derivative estimates are fully proved. -/
theorem uniformLocalizedParentAtomRealization_of_split {n : ℕ}
    (hind : HasUniformEuclideanAtomDecomposition n)
    (hjets : HasUniformNonnegativeJetBounds (n + 1))
    (_hsplit : HasUniformLocalSplit n) :
    HasUniformLocalizedParentAtomRealization (n + 1) := by
  classical
  rcases hjets with ⟨Cjet, hCjet, hcontrolAll⟩
  have hCjet0 : 0 ≤ Cjet := hCjet.le
  have hcurvature := uniformBoundedSplitParentAtomRealization hind
  intro A hA
  rcases hcurvature A Cjet hA hCjet0 with
    ⟨sigmaMax, hsigmaMax, hsigmaMaxOne, hcurvatureForScale⟩
  let delta := curvaturePreprocessValueThreshold Cjet
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact curvaturePreprocessValueThreshold_pos hCjet0
  let rho := positiveValueCutoffRadius Cjet delta
  have hrho : 0 < rho := by
    dsimp [rho]
    exact positiveValueCutoffRadius_pos hCjet0 hdelta
  let parentDilation := 4 * A
  have hparentDilation : 2 ≤ parentDilation := by
    dsimp [parentDilation]
    nlinarith
  have hAtomDilation : 2 * A ≤ parentDilation := by
    dsimp [parentDilation]
    nlinarith
  have hCurvatureDilation : 4 * A ≤ parentDilation := by
    dsimp [parentDilation]
    exact le_rfl
  let sigma := min sigmaMax (rho / 4)
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact lt_min hsigmaMax (div_pos hrho (by norm_num))
  have hsigmaMax' : sigma ≤ sigmaMax := min_le_left _ _
  have hsigmaOne : sigma ≤ 1 := hsigmaMax'.trans hsigmaMaxOne
  have hsigmaPositive : 2 * sigma ≤ positiveValueCutoffRadius Cjet delta := by
    have hsigmaRho : sigma ≤ rho / 4 := min_le_right _ _
    dsimp [rho] at hsigmaRho ⊢
    nlinarith
  refine ⟨parentDilation, sigma, hparentDilation, hsigma, hsigmaOne, ?_⟩
  intro parentA hparentA
  rcases exists_uniform_positiveLocalizedParentAtom
      Cjet delta parentA A parentDilation sigma hCjet0 hdelta hparentA
        hAtomDilation hsigmaPositive with
    ⟨Kpositive, hKpositive, hpositive⟩
  rcases hcurvatureForScale parentDilation hCurvatureDilation sigma hsigma hsigmaMax'
      parentA hparentA with
    ⟨Kcurvature, Bcurvature, hKcurvature, hBcurvature, hcurvature⟩
  let K := max Kpositive Kcurvature
  let B := max 1 Bcurvature
  have hK : 0 < K := hKpositive.trans_le (le_max_left _ _)
  have hB : 0 < B := by
    dsimp [B]
    omega
  refine ⟨K, B, hK, hB, ?_⟩
  intro parentB u hu cover
  have hcontrol : NonnegativeJetControl u Cjet := hcontrolAll u hu
  have activeFamily : ∀ i, i ∈ cover.active →
      Nonempty (LocalizedEuclideanAtomFamily
        (fun x ↦ cover.cutoff i x ^ 2 * u x) A 1 K B
        (cover.center i) (cover.radius i) parentDilation) := by
    intro i hi
    have hr : 0 < cover.radius i := cover.radius_pos i hi
    have hR : 0 < nonnegativeJetScale u (cover.center i) :=
      hr.trans_le (cover.radius_comparable i hi).1
    rcases intrinsicRescaledPatch_value_or_boundedSplitPreprocessing
        hu hcontrol (cover.center i) hR with hvalue | hpreprocess
    · rcases hpositive cover hu hcontrol hi hvalue with ⟨atoms⟩
      let widened : LocalizedEuclideanAtomFamily
          (fun z ↦ cover.intrinsicCutoff i z ^ 2 *
            intrinsicRescaledPatch u (cover.center i)
              (nonnegativeJetScale u (cover.center i)) z)
          A 1 K B 0
          (cover.radius i / nonnegativeJetScale u (cover.center i))
          parentDilation :=
        (atoms.increaseJetConstant (C' := K) (by
          exact le_max_left _ _)).increaseOverlapBudget (B' := B) (by
            exact Nat.le_max_left _ _)
      exact ⟨widened.intrinsicCoverParentToPhysical hu cover hi⟩
    · rcases hpreprocess with ⟨preprocess⟩
      rcases hcurvature hu hcontrol cover hi preprocess with ⟨atoms⟩
      let widened : LocalizedEuclideanAtomFamily
          (fun z ↦ cover.intrinsicCutoff i z ^ 2 *
            intrinsicRescaledPatch u (cover.center i)
              (nonnegativeJetScale u (cover.center i)) z)
          A 1 K B 0
          (cover.radius i / nonnegativeJetScale u (cover.center i))
          parentDilation :=
        (atoms.increaseJetConstant (C' := K) (by
          exact le_max_right _ _)).increaseOverlapBudget (B' := B) (by
            exact Nat.le_max_right _ _)
      exact ⟨widened.intrinsicCoverParentToPhysical hu cover hi⟩
  let patch : ∀ i, LocalizedEuclideanAtomFamily
      (fun x ↦ cover.cutoff i x ^ 2 * u x) A 1 K B
      (cover.center i) (cover.radius i) parentDilation := fun i ↦
    if hi : i ∈ cover.active then Classical.choice (activeFamily i hi)
    else
      (zeroLocalizedEuclideanAtomFamily A 1 K B hK.le
        (cover.center i) (cover.radius i) parentDilation).congrTarget (by
          funext x
          rw [cover.cutoff_eq_zero_of_not_active i hi]
          simp)
  refine ⟨patch, ?_⟩
  intro i hi
  simp only [patch, hi, ↓reduceDIte]
  rw [LocalizedEuclideanAtomFamily.congrTarget_atoms_active]
  rfl

/-- Fine quantitative covers and localized parent realizations assemble into a unit-cap atom
family.  This theorem performs the full global countable summation and overlap bookkeeping. -/
theorem uniformEuclideanAtomsAtOne_of_localizedParentRealization {q : ℕ}
    (hjets : HasUniformNonnegativeJetBounds q)
    (hpatch : HasUniformLocalizedParentAtomRealization q) :
    HasUniformEuclideanAtomDecompositionAtOne q := by
  intro A hA
  rcases hpatch A hA with
    ⟨parentDilation, σ, hparentDilation, hσ, hσone, hlocalForA⟩
  have hfine : HasUniformFineScaleCover q := uniformFineScaleCover_of_jetBounds hjets
  rcases hfine parentDilation hparentDilation σ hσ hσone with
    ⟨parentA, parentB, hparentA, hparentB, hcover⟩
  rcases hlocalForA parentA hparentA with
    ⟨C, childB, hC, hchildB, hlocal⟩
  refine ⟨C, parentB * childB, hC, Nat.mul_pos hparentB hchildB, ?_⟩
  intro u hu
  rcases hcover u hu with ⟨cover⟩
  rcases hlocal u hu cover with ⟨patch, hpatchEmpty⟩
  exact ⟨flattenLocalizedEuclideanAtomFamilies hu cover.toScaleCover patch hpatchEmpty⟩

/-- The unit-cap successor construction now reduces to the exact localized analytic realization
above.  The supplied ordinary cover is retained for compatibility with the established theorem
interface; fine covers are obtained constructively from the same jet bounds. -/
theorem uniformEuclideanAtomsAtOne_succ_of_cover_split {n : ℕ}
    (hind : HasUniformEuclideanAtomDecomposition n)
    (hjets : HasUniformNonnegativeJetBounds (n + 1))
    (_hcover : HasUniformScaleCover (n + 1))
    (hsplit : HasUniformLocalSplit n) :
    HasUniformEuclideanAtomDecompositionAtOne (n + 1) := by
  exact uniformEuclideanAtomsAtOne_of_localizedParentRealization hjets
    (uniformLocalizedParentAtomRealization_of_split hind hjets hsplit)

/-- The full successor theorem follows from the natural unit-cap construction by contracting the
input and pulling the atoms back, with all support, overlap, and scaled-jet fields preserved. -/
theorem uniformEuclideanAtoms_succ_of_cover_split {n : ℕ}
    (hind : HasUniformEuclideanAtomDecomposition n)
    (hjets : HasUniformNonnegativeJetBounds (n + 1))
    (hcover : HasUniformScaleCover (n + 1))
    (hsplit : HasUniformLocalSplit n) :
    HasUniformEuclideanAtomDecomposition (n + 1) := by
  exact hasUniformEuclideanAtomDecomposition_of_atOne
    (uniformEuclideanAtomsAtOne_succ_of_cover_split hind hjets hcover hsplit)

/-- The zero-dimensional construction and the genuine successor step give Euclidean atoms in
every dimension.  All analytic inputs at each successor are the proved uniform inputs from
`JetBounds`, `ScaleCover`, and the concrete local split construction. -/
theorem uniformEuclideanAtoms_all_dimensions (n : ℕ) :
    HasUniformEuclideanAtomDecomposition n := by
  induction n with
  | zero => exact uniformEuclideanAtoms_zero
  | succ n hind =>
      have hjets : HasUniformNonnegativeJetBounds (n + 1) :=
        uniformNonnegativeJetBounds (n + 1)
      exact uniformEuclideanAtoms_succ_of_cover_split hind hjets
        (uniformScaleCover_of_jetBounds hjets) (uniformLocalSplit n)

/-- Compatibility wrapper for the original parameterized interface. -/
theorem uniformEuclideanAtoms_of_cover_split {n : ℕ} (_hn : 1 ≤ n)
    (_hjets : HasUniformNonnegativeJetBounds n)
    (_hcover : HasUniformScaleCover n)
    (_hsplit : HasUniformLocalSplit n) : HasUniformEuclideanAtomDecomposition n := by
  exact uniformEuclideanAtoms_all_dimensions n

end QuarticConvergence
end OptimalConvergenceRates

end
