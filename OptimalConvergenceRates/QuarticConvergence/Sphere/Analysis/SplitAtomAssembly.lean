/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/SplitAtomAssembly.lean

  Quantitative assembly of the two terms in a one-normal-coordinate square split.

  This file deliberately sits downstream of `Atoms`: it isolates the countable-product,
  support, overlap, and normalization bookkeeping from the local analytic estimates which
  produce a `UniformLocalSplitData` with uniform derivative bounds.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.Atoms
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.CoordinateSplit
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.CurvatureParentPatch

open Set
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Every individual square in an atom family is bounded by the represented nonnegative sum. -/
theorem EuclideanAtomFamily.root_sq_le_target {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) (i : ℕ) (x : Fin n → ℝ) :
    atoms.root i x ^ 2 ≤ u x := by
  exact le_hasSum (atoms.square_identity x) i (fun k _hk ↦ sq_nonneg (atoms.root k x))

/-- Remove active indices whose root is the zero function.  This does not alter any roots or the
represented target, but makes activity carry the useful fact that the root has nonempty support. -/
def EuclideanAtomFamily.pruneZeroRoots {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) :
    EuclideanAtomFamily u A radiusCap C B where
  root := atoms.root
  active := atoms.active ∩ {i | atoms.root i ≠ 0}
  center := atoms.center
  radius := atoms.radius
  root_eq_zero_of_not_active := by
    intro i hi
    by_cases hia : i ∈ atoms.active
    · have hz : atoms.root i = 0 := by
        by_contra hnz
        exact hi ⟨hia, hnz⟩
      exact hz
    · exact atoms.root_eq_zero_of_not_active i hia
  radius_pos := by
    intro i hi
    exact atoms.radius_pos i hi.1
  radius_le_cap := by
    intro i hi
    exact atoms.radius_le_cap i hi.1
  root_contDiff := atoms.root_contDiff
  root_compact_support := atoms.root_compact_support
  supported := atoms.supported
  square_identity := atoms.square_identity
  dilated_overlap := by
    intro x s
    let small : Set ℕ := {i | i ∈ s ∧ i ∈ atoms.active ∩ {k | atoms.root k ≠ 0} ∧
      x ∈ Metric.ball (atoms.center i) (A * atoms.radius i)}
    let large : Set ℕ := {i | i ∈ s ∧ i ∈ atoms.active ∧
      x ∈ Metric.ball (atoms.center i) (A * atoms.radius i)}
    have hsub : small ⊆ large := by
      intro i hi
      exact ⟨hi.1, hi.2.1.1, hi.2.2⟩
    have hfinite : large.Finite := s.finite_toSet.subset (fun _ hi ↦ hi.1)
    change Set.ncard small ≤ B
    exact (Set.ncard_le_ncard hsub hfinite).trans (atoms.dilated_overlap x s)
  scaled_jets := by
    intro i j hj x
    exact atoms.scaled_jets i j hj x

@[simp] theorem EuclideanAtomFamily.pruneZeroRoots_root {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) :
    atoms.pruneZeroRoots.root = atoms.root := rfl

theorem EuclideanAtomFamily.pruneZeroRoots_active_nonzero {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) {i : ℕ}
    (hi : i ∈ atoms.pruneZeroRoots.active) : atoms.root i ≠ 0 :=
  hi.2

/-- A family representing a target supported in one ball can be made genuinely localized by
discarding zero roots.  The additive `radiusCap` margin accounts for locating an active center
from one nonzero point of its root. -/
noncomputable def EuclideanAtomFamily.localizeOfTargetSupport {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B)
    {parentCenter : Fin n → ℝ} {supportRadius parentRadius parentDilation : ℝ}
    (hA : 0 ≤ A)
    (hsupport : Function.support u ⊆ Metric.ball parentCenter supportRadius)
    (hmargin : (A + 1) * radiusCap + supportRadius ≤
      parentDilation * parentRadius) :
    LocalizedEuclideanAtomFamily u A radiusCap C B
      parentCenter parentRadius parentDilation where
  atoms := atoms.pruneZeroRoots
  dilated_ball_subset_parent := by
    intro i hi z hz
    have hia : i ∈ atoms.active := hi.1
    have hinz : atoms.root i ≠ 0 := hi.2
    obtain ⟨x, hx⟩ : ∃ x, atoms.root i x ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hinz
      funext x
      exact hall x
    have hxAtom : x ∈ Metric.ball (atoms.center i) (atoms.radius i) :=
      atoms.supported i hx
    have htargetPos : 0 < u x :=
      lt_of_lt_of_le (sq_pos_of_ne_zero hx) (atoms.root_sq_le_target i x)
    have hxTarget : x ∈ Function.support u := by
      simpa [Function.mem_support] using htargetPos.ne'
    have hxParent := hsupport hxTarget
    have hri : 0 < atoms.radius i := atoms.radius_pos i hia
    have hriCap : atoms.radius i ≤ radiusCap := atoms.radius_le_cap i hia
    have hAone : 0 ≤ A + 1 := by linarith
    have hcap : (A + 1) * atoms.radius i ≤ (A + 1) * radiusCap :=
      mul_le_mul_of_nonneg_left hriCap hAone
    rw [Metric.mem_ball] at hz hxAtom hxParent ⊢
    have hz' : dist z (atoms.center i) < A * atoms.radius i := hz
    have htriangle : dist z parentCenter ≤
        dist z (atoms.center i) + dist (atoms.center i) x + dist x parentCenter := by
      calc
        dist z parentCenter ≤ dist z (atoms.center i) + dist (atoms.center i) parentCenter :=
          dist_triangle _ _ _
        _ ≤ dist z (atoms.center i) +
            (dist (atoms.center i) x + dist x parentCenter) := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    have hstrict : dist z (atoms.center i) + dist (atoms.center i) x +
        dist x parentCenter < (A + 1) * atoms.radius i + supportRadius := by
      rw [dist_comm (atoms.center i) x]
      calc
        dist z (atoms.center i) + dist x (atoms.center i) + dist x parentCenter <
            A * atoms.radius i + atoms.radius i + supportRadius := by
          linarith [hz', hxAtom, hxParent]
        _ = (A + 1) * atoms.radius i + supportRadius := by ring
    exact htriangle.trans_lt
      (hstrict.trans_le ((add_le_add hcap le_rfl).trans hmargin))
/-- Enlarge only the radius cap advertised by a localized family. -/
def LocalizedEuclideanAtomFamily.increaseRadiusCap {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap newCap C : ℝ} {B : ℕ}
    {parentCenter : Fin n → ℝ} {parentRadius parentDilation : ℝ}
    (atoms : LocalizedEuclideanAtomFamily u A radiusCap C B
      parentCenter parentRadius parentDilation) (hcap : radiusCap ≤ newCap) :
    LocalizedEuclideanAtomFamily u A newCap C B
      parentCenter parentRadius parentDilation where
  atoms := atoms.atoms.increaseRadiusCap hcap
  dilated_ball_subset_parent := atoms.dilated_ball_subset_parent

/-- A one-root Euclidean family, without asking for parent-localization data. -/
noncomputable def singleEuclideanAtomFamily {n : ℕ}
    {target root : (Fin n → ℝ) → ℝ} {A radiusCap C r : ℝ}
    {center : Fin n → ℝ}
    (hr : 0 < r) (hrCap : r ≤ radiusCap) (hC : 0 ≤ C)
    (hrootSmooth : ContDiff ℝ 4 root) (hrootCompact : HasCompactSupport root)
    (hrootSupport : Function.support root ⊆ Metric.ball center r)
    (hsquare : ∀ x, target x = root x ^ 2)
    (hjets : ∀ j, j ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ j root x‖ * r ^ j ≤ C * r ^ 2) :
    EuclideanAtomFamily target A radiusCap C 1 :=
  (singleLocalizedEuclideanAtomFamily hr hrCap hC hrootSmooth hrootCompact
    hrootSupport hsquare hjets (fun _ hx ↦ hx)).atoms

/-- Use the atom radius on active indices and a harmless unit fallback on inactive indices.  This
lets us choose an interval square partition for every natural index without imposing positivity
on the unused radii of an `EuclideanAtomFamily`. -/
noncomputable def EuclideanAtomFamily.intervalLiftScale {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) (i : ℕ) : ℝ := by
  classical
  exact if i ∈ atoms.active then atoms.radius i else 1

theorem EuclideanAtomFamily.intervalLiftScale_pos {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) (i : ℕ) :
    0 < atoms.intervalLiftScale i := by
  by_cases hi : i ∈ atoms.active
  · simpa [EuclideanAtomFamily.intervalLiftScale, hi] using atoms.radius_pos i hi
  · simp [EuclideanAtomFamily.intervalLiftScale, hi]

@[simp] theorem EuclideanAtomFamily.intervalLiftScale_of_active {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) {i : ℕ}
    (hi : i ∈ atoms.active) : atoms.intervalLiftScale i = atoms.radius i := by
  simp [EuclideanAtomFamily.intervalLiftScale, hi]

/-- An interval square partition selected at the radius of every active tangential atom. -/
structure AtomwiseIntervalSquarePartitions {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) (D Cp : ℝ) (Bp : ℕ) where
  partition : ∀ i, ScaledIntervalSquarePartition
    (atoms.intervalLiftScale i) D Cp Bp

/-- The proved one-dimensional construction supplies partitions simultaneously at all atom
radii.  No countable choice beyond the already noncomputable atom theorem is exposed downstream. -/
theorem exists_atomwiseIntervalSquarePartitions {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) {D : ℝ} (hD : 0 ≤ D) :
    ∃ Cp : ℝ, ∃ Bp : ℕ, 1 ≤ Cp ∧ 0 < Bp ∧
      Nonempty (AtomwiseIntervalSquarePartitions atoms D Cp Bp) := by
  classical
  obtain ⟨Cp, Bp, hCp, hBp, hpart⟩ := exists_scaledIntervalSquarePartition D hD
  refine ⟨Cp, Bp, hCp, hBp, ⟨⟨fun i ↦ Classical.choice
    (hpart (atoms.intervalLiftScale i) (atoms.intervalLiftScale_pos i))⟩⟩⟩

/-- Pullback through a norm-at-most-one continuous linear map cannot increase the norm of an
iterated derivative. -/
theorem norm_iteratedFDeriv_comp_continuousLinearMap_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) {f : F → ℝ}
    (hf : ContDiff ℝ 4 f) {j : ℕ} (hj : j ≤ 4) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y ↦ f (L y)) x‖ ≤
      ‖iteratedFDeriv ℝ j f (L x)‖ := by
  have hcomp : iteratedFDeriv ℝ j (f ∘ L) x =
      (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ ↦ L) :=
    L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hj)
  change ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ _
  rw [hcomp]
  calc
    ‖(iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ ↦ L)‖ ≤
        ‖iteratedFDeriv ℝ j f (L x)‖ * ∏ _ : Fin j, ‖L‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * ∏ _ : Fin j, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg L) (fun _ _ ↦ hL))
        (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j f (L x)‖ := by simp

/-- Normal-coordinate pullback. -/
def normalCoordinatePullback {n : ℕ} (f : ℝ → ℝ)
    (z : ℝ × (Fin n → ℝ)) : ℝ := f z.1

/-- Tangential-coordinate pullback. -/
def tangentialCoordinatePullback {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (z : ℝ × (Fin n → ℝ)) : ℝ := f z.2

theorem normalCoordinatePullback_contDiff {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 4 f) : ContDiff ℝ 4 (normalCoordinatePullback (n := n) f) := by
  exact hf.comp contDiff_fst

theorem tangentialCoordinatePullback_contDiff {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 4 f) :
    ContDiff ℝ 4 (tangentialCoordinatePullback f) := by
  exact hf.comp contDiff_snd

theorem norm_iteratedFDeriv_normalCoordinatePullback_le {n j : ℕ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) (hj : j ≤ 4)
    (z : ℝ × (Fin n → ℝ)) :
    ‖iteratedFDeriv ℝ j (normalCoordinatePullback f) z‖ ≤
      ‖iteratedFDeriv ℝ j f z.1‖ := by
  let L : (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa only [one_mul] using norm_fst_le z
  simpa [normalCoordinatePullback, L] using
    norm_iteratedFDeriv_comp_continuousLinearMap_le L hL hf hj z

theorem norm_iteratedFDeriv_tangentialCoordinatePullback_le {n j : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 4 f) (hj : j ≤ 4)
    (z : ℝ × (Fin n → ℝ)) :
    ‖iteratedFDeriv ℝ j (tangentialCoordinatePullback f) z‖ ≤
      ‖iteratedFDeriv ℝ j f z.2‖ := by
  let L : (ℝ × (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa only [one_mul] using norm_snd_le z
  simpa [tangentialCoordinatePullback, L] using
    norm_iteratedFDeriv_comp_continuousLinearMap_le L hL hf hj z

/-- Lift lower-dimensional atoms through atom-scale normal square partitions and multiply by a
compact parent cutoff.  The output is expressed in the repository's canonical `Fin (n+1)`
coordinates.  The factor `1024` is the explicit four-derivative product/isometry loss, and the
overlap budget is exactly the tangential budget times the interval budget. -/
noncomputable def EuclideanAtomFamily.liftThroughNormalPartition {n : ℕ}
    {v : (Fin n → ℝ) → ℝ} {A radiusCap Cchild Cp Mparent : ℝ}
    {Bchild Bp : ℕ}
    (atoms : EuclideanAtomFamily v (2 * A) radiusCap Cchild Bchild)
    (partitions : AtomwiseIntervalSquarePartitions atoms (2 * A) Cp Bp)
    (parent : (ℝ × (Fin n → ℝ)) → ℝ)
    (hCchild : 0 ≤ Cchild) (hCp : 0 ≤ Cp) (hMparent : 0 ≤ Mparent)
    (hparentSmooth : ContDiff ℝ 4 parent) (hparentCompact : HasCompactSupport parent)
    (hparentScaled : ∀ i, i ∈ atoms.active → ∀ q, q ≤ 4 → ∀ z,
      ‖iteratedFDeriv ℝ q parent z‖ * atoms.radius i ^ q ≤ Mparent) :
    EuclideanAtomFamily
      (fun x ↦
        parent (finSuccSplitIsometry n x) ^ 2 * v (finSuccSplitIsometry n x).2)
      A (2 * radiusCap) (1024 * Mparent * Cp * Cchild) (Bchild * Bp) := by
  classical
  let split := finSuccSplitIsometry n
  let join := finSuccJoinIsometry n
  let liftedRoot : ℕ → (Fin (n + 1) → ℝ) → ℝ := fun k x ↦
    let p := Nat.pairEquiv.symm k
    parent (split x) *
      (partitions.partition p.1).cutoff p.2 (split x).1 *
        atoms.root p.1 (split x).2
  refine {
    root := liftedRoot
    active := {k | (Nat.pairEquiv.symm k).1 ∈ atoms.active}
    center := fun k ↦
      let p := Nat.pairEquiv.symm k
      join ((partitions.partition p.1).center p.2, atoms.center p.1)
    radius := fun k ↦ 2 * atoms.radius (Nat.pairEquiv.symm k).1
    root_eq_zero_of_not_active := ?_
    radius_pos := ?_
    radius_le_cap := ?_
    root_contDiff := ?_
    root_compact_support := ?_
    supported := ?_
    square_identity := ?_
    dilated_overlap := ?_
    scaled_jets := ?_ }
  · intro k hk
    let p := Nat.pairEquiv.symm k
    have hpi : p.1 ∉ atoms.active := by simpa [p] using hk
    have hz := atoms.root_eq_zero_of_not_active p.1 hpi
    funext x
    change parent (split x) * (partitions.partition p.1).cutoff p.2 (split x).1 *
      atoms.root p.1 (split x).2 = 0
    rw [hz]
    simp
  · intro k hk
    have hpi : (Nat.pairEquiv.symm k).1 ∈ atoms.active := hk
    exact mul_pos (by norm_num) (atoms.radius_pos _ hpi)
  · intro k hk
    have hpi : (Nat.pairEquiv.symm k).1 ∈ atoms.active := hk
    exact mul_le_mul_of_nonneg_left (atoms.radius_le_cap _ hpi) (by norm_num)
  · intro k
    let p := Nat.pairEquiv.symm k
    have hnormal : ContDiff ℝ 4
        (normalCoordinatePullback (n := n) ((partitions.partition p.1).cutoff p.2)) :=
      normalCoordinatePullback_contDiff
        ((partitions.partition p.1).cutoff_contDiff p.2 |>.of_le (by norm_num))
    have hchild : ContDiff ℝ 4
        (tangentialCoordinatePullback (atoms.root p.1)) :=
      tangentialCoordinatePullback_contDiff (atoms.root_contDiff p.1)
    have hproduct : ContDiff ℝ 4 (fun z ↦ parent z *
        normalCoordinatePullback (n := n) ((partitions.partition p.1).cutoff p.2) z *
          tangentialCoordinatePullback (atoms.root p.1) z) :=
      (hparentSmooth.mul hnormal).mul hchild
    simpa [liftedRoot, p, split, normalCoordinatePullback,
      tangentialCoordinatePullback, Function.comp_def] using
      hproduct.comp (finSuccSplit_contDiff n 4)
  · intro k
    let p := Nat.pairEquiv.symm k
    let productRoot : (ℝ × (Fin n → ℝ)) → ℝ := fun z ↦
      parent z * normalCoordinatePullback (n := n) ((partitions.partition p.1).cutoff p.2) z *
        tangentialCoordinatePullback (atoms.root p.1) z
    have hproductCompact : HasCompactSupport productRoot := by
      exact hparentCompact.mul_right.mul_right
    simpa [liftedRoot, productRoot, p, split, normalCoordinatePullback,
      tangentialCoordinatePullback, Function.comp_def] using
      hproductCompact.comp_homeomorph (finSuccSplitEquiv n).toHomeomorph
  · intro k x hx
    let p := Nat.pairEquiv.symm k
    by_cases hpi : p.1 ∈ atoms.active
    · have hnormalNe : (partitions.partition p.1).cutoff p.2 (split x).1 ≠ 0 := by
        intro hzero
        apply hx
        change parent (split x) * (partitions.partition p.1).cutoff p.2 (split x).1 *
          atoms.root p.1 (split x).2 = 0
        simp [hzero]
      have hchildNe : atoms.root p.1 (split x).2 ≠ 0 := by
        intro hzero
        apply hx
        change parent (split x) * (partitions.partition p.1).cutoff p.2 (split x).1 *
          atoms.root p.1 (split x).2 = 0
        simp [hzero]
      have hnormal := (partitions.partition p.1).cutoff_support p.2 hnormalNe
      have hchild := atoms.supported p.1 hchildNe
      have hr : 0 < atoms.radius p.1 := atoms.radius_pos p.1 hpi
      rw [Metric.mem_ball] at hnormal hchild ⊢
      have hnormal' : dist (split x).1 ((partitions.partition p.1).center p.2) <
          2 * atoms.radius p.1 := by
        simpa [EuclideanAtomFamily.intervalLiftScale, hpi] using hnormal
      have hdist : dist x
          (join ((partitions.partition p.1).center p.2, atoms.center p.1)) =
          dist (split x)
            ((partitions.partition p.1).center p.2, atoms.center p.1) := by
        rw [← dist_finSuccJoinIsometry n]
        simp [split, join]
      rw [hdist, Prod.dist_eq]
      exact max_lt hnormal' (hchild.trans (by linarith))
    · have hzero := atoms.root_eq_zero_of_not_active p.1 hpi
      exfalso
      apply hx
      change parent (split x) * (partitions.partition p.1).cutoff p.2 (split x).1 *
        atoms.root p.1 (split x).2 = 0
      simp [hzero]
  · intro x
    let z := split x
    let f : ℕ × ℕ → ℝ := fun p ↦
      (parent z * (partitions.partition p.1).cutoff p.2 z.1 *
        atoms.root p.1 z.2) ^ 2
    have hinner : ∀ i, HasSum (fun k ↦ f (i, k))
        (parent z ^ 2 * atoms.root i z.2 ^ 2) := by
      intro i
      have hcut : HasSum (fun k ↦ (partitions.partition i).cutoff k z.1 ^ 2) 1 := by
        have hs := ((partitions.partition i).summable_cutoff_sq z.1).hasSum
        rw [(partitions.partition i).square_partition] at hs
        exact hs
      have hscaled := hcut.mul_right (parent z ^ 2 * atoms.root i z.2 ^ 2)
      convert hscaled using 1
      · funext k
        simp [f]
        ring
      · simp
    have houter : HasSum (fun i ↦ parent z ^ 2 * atoms.root i z.2 ^ 2)
        (parent z ^ 2 * v z.2) := by
      exact (atoms.square_identity z.2).mul_left (parent z ^ 2)
    have hprodSummable : Summable f := by
      rw [summable_prod_of_nonneg (fun p ↦ sq_nonneg
        (parent z * (partitions.partition p.1).cutoff p.2 z.1 *
          atoms.root p.1 z.2))]
      refine ⟨fun i ↦ (hinner i).summable, ?_⟩
      convert houter.summable using 1
      funext i
      exact (hinner i).tsum_eq
    have hprod : HasSum f (parent z ^ 2 * v z.2) := by
      have h := hprodSummable.hasSum
      have htsum : ∑' p, f p = parent z ^ 2 * v z.2 := by
        rw [hprodSummable.tsum_prod' (fun i ↦ (hinner i).summable)]
        exact (tsum_congr fun i ↦ (hinner i).tsum_eq).trans houter.tsum_eq
      rwa [htsum] at h
    have hreindexed : HasSum (f ∘ Nat.pairEquiv.symm)
        (parent z ^ 2 * v z.2) :=
      (Nat.pairEquiv.symm.hasSum_iff).2 hprod
    simpa [liftedRoot, f, z, Function.comp_def] using hreindexed
  · intro x s
    let z := split x
    let pairTarget : Set (ℕ × ℕ) := {p |
      Nat.pairEquiv p ∈ s ∧ p.1 ∈ atoms.active ∧
        x ∈ Metric.ball
          (join ((partitions.partition p.1).center p.2, atoms.center p.1))
          (A * (2 * atoms.radius p.1))}
    have hpairFinite : pairTarget.Finite := by
      have hpre : (Nat.pairEquiv ⁻¹' (s : Set ℕ)).Finite :=
        s.finite_toSet.preimage Nat.pairEquiv.injective.injOn
      exact hpre.subset (fun _ hp ↦ hp.1)
    have hbase : Set.ncard (Prod.fst '' pairTarget) ≤ Bchild := by
      let baseIndices : Finset ℕ := s.image (fun k ↦ (Nat.pairEquiv.symm k).1)
      let baseTarget : Set ℕ := {i | i ∈ baseIndices ∧ i ∈ atoms.active ∧
        z.2 ∈ Metric.ball (atoms.center i) ((2 * A) * atoms.radius i)}
      have hsubset : Prod.fst '' pairTarget ⊆ baseTarget := by
        rintro i ⟨p, hp, rfl⟩
        refine ⟨?_, hp.2.1, ?_⟩
        · simp only [Nat.pairEquiv_symm_apply, Finset.mem_image, baseIndices]
          exact ⟨Nat.pairEquiv p, hp.1,
            congr_arg Prod.fst (Nat.pairEquiv.symm_apply_apply p)⟩
        · have hpball := hp.2.2
          rw [Metric.mem_ball] at hpball ⊢
          have hdist : dist x
              (join ((partitions.partition p.1).center p.2, atoms.center p.1)) =
              dist z ((partitions.partition p.1).center p.2, atoms.center p.1) := by
            rw [← dist_finSuccJoinIsometry n]
            simp [z, split, join]
          rw [hdist, Prod.dist_eq] at hpball
          have htangential := (le_max_right
            (dist z.1 ((partitions.partition p.1).center p.2))
            (dist z.2 (atoms.center p.1))).trans_lt hpball
          simpa [mul_assoc, mul_left_comm, mul_comm] using htangential
      have hfinite : baseTarget.Finite :=
        baseIndices.finite_toSet.subset (fun _ hi ↦ hi.1)
      exact (Set.ncard_le_ncard hsubset hfinite).trans
        (atoms.dilated_overlap z.2 baseIndices)
    have hfiber : ∀ i ∈ Prod.fst '' pairTarget,
        Set.ncard {p | p ∈ pairTarget ∧ p.1 = i} ≤ Bp := by
      intro i hi
      let fiber : Set (ℕ × ℕ) := {p | p ∈ pairTarget ∧ p.1 = i}
      have hfiberFinite : fiber.Finite := hpairFinite.subset (fun _ hp ↦ hp.1)
      have hsndInj : Set.InjOn Prod.snd fiber := by
        intro p hp q hq heq
        apply Prod.ext
        · exact hp.2.trans hq.2.symm
        · exact heq
      have hsndFinite : (Prod.snd '' fiber).Finite := hfiberFinite.image Prod.snd
      let children : Finset ℕ := hsndFinite.toFinset
      have hiActive : i ∈ atoms.active := by
        rcases hi with ⟨p, hp, rfl⟩
        exact hp.2.1
      have hchildSet : {k | k ∈ children ∧
          z.1 ∈ Metric.ball ((partitions.partition i).center k)
            ((2 * A) * atoms.intervalLiftScale i)} = Prod.snd '' fiber := by
        ext k
        constructor
        · intro hk
          simpa [children] using hk.1
        · rintro ⟨p, hp, rfl⟩
          have hpi : p.1 = i := hp.2
          have hpdata := hp.1
          subst i
          refine ⟨?_, ?_⟩
          · simp only [children, Set.Finite.mem_toFinset, Set.mem_image Prod.snd fiber]
            exact ⟨p, hp, rfl⟩
          · have hpball := hpdata.2.2
            rw [Metric.mem_ball] at hpball ⊢
            have hdist : dist x
                (join ((partitions.partition p.1).center p.2, atoms.center p.1)) =
                dist z ((partitions.partition p.1).center p.2, atoms.center p.1) := by
              rw [← dist_finSuccJoinIsometry n]
              simp [z, split, join]
            rw [hdist, Prod.dist_eq] at hpball
            have hnormal := (le_max_left
              (dist z.1 ((partitions.partition p.1).center p.2))
              (dist z.2 (atoms.center p.1))).trans_lt hpball
            simpa [EuclideanAtomFamily.intervalLiftScale, hpdata.2.1,
              mul_assoc, mul_left_comm, mul_comm] using hnormal
      have hwithin := (partitions.partition i).overlap z.1 children
      rw [hchildSet] at hwithin
      rw [← hsndInj.ncard_image]
      exact hwithin
    have hpairCard : Set.ncard pairTarget ≤ Bchild * Bp :=
      ncard_pair_set_le_mul hpairFinite hbase hfiber
    let natTarget : Set ℕ := {k | k ∈ s ∧
      (Nat.pairEquiv.symm k).1 ∈ atoms.active ∧
      x ∈ Metric.ball
        (join ((partitions.partition (Nat.pairEquiv.symm k).1).center
          (Nat.pairEquiv.symm k).2, atoms.center (Nat.pairEquiv.symm k).1))
        (A * (2 * atoms.radius (Nat.pairEquiv.symm k).1))}
    have hnatImage : Nat.pairEquiv '' pairTarget = natTarget := by
      ext k
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hinv := Nat.pairEquiv.symm_apply_apply p
        change Nat.pairEquiv p ∈ s ∧
          (Nat.pairEquiv.symm (Nat.pairEquiv p)).1 ∈ atoms.active ∧
          x ∈ Metric.ball
            (join ((partitions.partition (Nat.pairEquiv.symm (Nat.pairEquiv p)).1).center
              (Nat.pairEquiv.symm (Nat.pairEquiv p)).2,
              atoms.center (Nat.pairEquiv.symm (Nat.pairEquiv p)).1))
            (A * (2 * atoms.radius (Nat.pairEquiv.symm (Nat.pairEquiv p)).1))
        rw [hinv]
        exact hp
      · intro hk
        change k ∈ s ∧ (Nat.pairEquiv.symm k).1 ∈ atoms.active ∧
          x ∈ Metric.ball
            (join ((partitions.partition (Nat.pairEquiv.symm k).1).center
              (Nat.pairEquiv.symm k).2, atoms.center (Nat.pairEquiv.symm k).1))
            (A * (2 * atoms.radius (Nat.pairEquiv.symm k).1)) at hk
        refine ⟨Nat.pairEquiv.symm k, ?_, Nat.pairEquiv.apply_symm_apply k⟩
        change Nat.pairEquiv (Nat.pairEquiv.symm k) ∈ s ∧
          (Nat.pairEquiv.symm k).1 ∈ atoms.active ∧
          x ∈ Metric.ball
            (join ((partitions.partition (Nat.pairEquiv.symm k).1).center
              (Nat.pairEquiv.symm k).2, atoms.center (Nat.pairEquiv.symm k).1))
            (A * (2 * atoms.radius (Nat.pairEquiv.symm k).1))
        refine ⟨?_, hk.2.1, hk.2.2⟩
        simpa only [Nat.pairEquiv.apply_symm_apply] using hk.1
    have hcardEq : Set.ncard natTarget = Set.ncard pairTarget := by
      rw [← hnatImage, Nat.pairEquiv.injective.injOn.ncard_image]
    change Set.ncard natTarget ≤ Bchild * Bp
    rw [hcardEq]
    exact hpairCard
  · intro k j hj x
    let p := Nat.pairEquiv.symm k
    by_cases hpi : p.1 ∈ atoms.active
    · let normal : (ℝ × (Fin n → ℝ)) → ℝ :=
        normalCoordinatePullback (n := n) ((partitions.partition p.1).cutoff p.2)
      let child : (ℝ × (Fin n → ℝ)) → ℝ :=
        tangentialCoordinatePullback (atoms.root p.1)
      let parentAmbient : (Fin (n + 1) → ℝ) → ℝ := fun y ↦ parent (split y)
      let normalAmbient : (Fin (n + 1) → ℝ) → ℝ := fun y ↦ normal (split y)
      let childAmbient : (Fin (n + 1) → ℝ) → ℝ := fun y ↦ child (split y)
      have hnormalSmooth : ContDiff ℝ 4 normal :=
        normalCoordinatePullback_contDiff
          ((partitions.partition p.1).cutoff_contDiff p.2 |>.of_le (by norm_num))
      have hchildSmooth : ContDiff ℝ 4 child :=
        tangentialCoordinatePullback_contDiff (atoms.root_contDiff p.1)
      have hparentAmbientSmooth : ContDiff ℝ 4 parentAmbient := by
        exact hparentSmooth.comp (finSuccSplit_contDiff n 4)
      have hnormalAmbientSmooth : ContDiff ℝ 4 normalAmbient := by
        exact hnormalSmooth.comp (finSuccSplit_contDiff n 4)
      have hchildAmbientSmooth : ContDiff ℝ 4 childAmbient := by
        exact hchildSmooth.comp (finSuccSplit_contDiff n 4)
      have hparentBound : ∀ q, q ≤ 4 →
          ‖iteratedFDeriv ℝ q parentAmbient x‖ * atoms.radius p.1 ^ q ≤ Mparent := by
        intro q hq
        have hnorm : ‖iteratedFDeriv ℝ q parentAmbient x‖ =
            ‖iteratedFDeriv ℝ q parent (split x)‖ := by
          simpa [parentAmbient, split, Function.comp_def] using
            (finSuccSplitIsometry n).norm_iteratedFDeriv_comp_right parent x q
        rw [hnorm]
        exact hparentScaled p.1 hpi q hq (split x)
      have hnormalBound : ∀ q, q ≤ 4 →
          ‖iteratedFDeriv ℝ q normalAmbient x‖ * atoms.radius p.1 ^ q ≤ Cp := by
        intro q hq
        have hnorm : ‖iteratedFDeriv ℝ q normalAmbient x‖ =
            ‖iteratedFDeriv ℝ q normal (split x)‖ := by
          simpa [normalAmbient, split, Function.comp_def] using
            (finSuccSplitIsometry n).norm_iteratedFDeriv_comp_right normal x q
        rw [hnorm]
        calc
          ‖iteratedFDeriv ℝ q normal (split x)‖ * atoms.radius p.1 ^ q ≤
              ‖iteratedFDeriv ℝ q ((partitions.partition p.1).cutoff p.2)
                (split x).1‖ * atoms.radius p.1 ^ q :=
            mul_le_mul_of_nonneg_right
              (norm_iteratedFDeriv_normalCoordinatePullback_le
                ((partitions.partition p.1).cutoff_contDiff p.2 |>.of_le (by norm_num))
                hq (split x)) (pow_nonneg (atoms.radius_pos p.1 hpi).le q)
          _ ≤ Cp := by
            simpa [EuclideanAtomFamily.intervalLiftScale, hpi] using
              (partitions.partition p.1).scaled_cutoff p.2 q hq (split x).1
      have hchildBound : ∀ q, q ≤ 4 →
          ‖iteratedFDeriv ℝ q childAmbient x‖ * atoms.radius p.1 ^ q ≤
            Cchild * atoms.radius p.1 ^ 2 := by
        intro q hq
        have hnorm : ‖iteratedFDeriv ℝ q childAmbient x‖ =
            ‖iteratedFDeriv ℝ q child (split x)‖ := by
          simpa [childAmbient, split, Function.comp_def] using
            (finSuccSplitIsometry n).norm_iteratedFDeriv_comp_right child x q
        rw [hnorm]
        exact (mul_le_mul_of_nonneg_right
          (norm_iteratedFDeriv_tangentialCoordinatePullback_le
            (atoms.root_contDiff p.1) hq (split x))
          (pow_nonneg (atoms.radius_pos p.1 hpi).le q)).trans
            (atoms.scaled_jets p.1 q hq (split x).2)
      have hbase := liftedAtom_scaledJets
        (m := n + 1) (parent := parentAmbient) (normal := normalAmbient)
        (child := childAmbient) (x := x) (atoms.radius_pos p.1 hpi)
        hMparent hCp hCchild hparentAmbientSmooth hnormalAmbientSmooth
        hchildAmbientSmooth hparentBound hnormalBound hchildBound hj
      have hrootEq : liftedRoot k = fun y ↦
          parentAmbient y * normalAmbient y * childAmbient y := by
        funext y
        simp [liftedRoot, parentAmbient, normalAmbient, childAmbient, normal, child,
          p, split, normalCoordinatePullback, tangentialCoordinatePullback]
      rw [hrootEq, mul_pow]
      have hpow : (2 : ℝ) ^ j ≤ 16 := by
        interval_cases j <;> norm_num
      calc
        ‖iteratedFDeriv ℝ j (fun y ↦
            parentAmbient y * normalAmbient y * childAmbient y) x‖ *
            (2 ^ j * atoms.radius p.1 ^ j) =
            (‖iteratedFDeriv ℝ j (fun y ↦
              parentAmbient y * normalAmbient y * childAmbient y) x‖ *
              atoms.radius p.1 ^ j) * 2 ^ j := by ring
        _ ≤ (256 * Mparent * Cp * Cchild * atoms.radius p.1 ^ 2) * 2 ^ j :=
          mul_le_mul_of_nonneg_right hbase (pow_nonneg (by norm_num) j)
        _ ≤ (256 * Mparent * Cp * Cchild * atoms.radius p.1 ^ 2) * 16 :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = (1024 * Mparent * Cp * Cchild) *
            (2 * atoms.radius p.1) ^ 2 := by ring
    · have hzero := atoms.root_eq_zero_of_not_active p.1 hpi
      have hfun : liftedRoot k = 0 := by
        funext y
        change parent (split y) * (partitions.partition p.1).cutoff p.2 (split y).1 *
          atoms.root p.1 (split y).2 = 0
        simp [hzero]
      rw [hfun]
      change ‖iteratedFDeriv ℝ j (fun _ : Fin (n + 1) → ℝ ↦ (0 : ℝ)) x‖ *
          (2 * atoms.radius p.1) ^ j ≤
        (1024 * Mparent * Cp * Cchild) * (2 * atoms.radius p.1) ^ 2
      rw [iteratedFDeriv_zero_fun]
      simp only [Pi.zero_apply, norm_zero, zero_mul]
      positivity

/-- Pull an atom family back through a uniformly conditioned continuous linear equivalence.
The input dilation is enlarged by both condition numbers.  The output radii grow by the inverse
Lipschitz bound, and the four-jet constant records the worst derivative loss. -/
noncomputable def EuclideanAtomFamily.pullbackContinuousLinearEquiv {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C K Kinv : ℝ} {B : ℕ}
    (T : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (atoms : EuclideanAtomFamily u (K * Kinv * A) radiusCap C B)
    (hK : 1 ≤ K) (hT : ‖T.toContinuousLinearMap‖ ≤ K)
    (hKinv : 1 ≤ Kinv) (hTinv : ‖T.symm.toContinuousLinearMap‖ ≤ Kinv)
    (hC : 0 ≤ C) :
    EuclideanAtomFamily (fun x ↦ u (T x)) A (Kinv * radiusCap)
      (C * (K * Kinv) ^ 4) B where
  root := fun i x ↦ atoms.root i (T x)
  active := atoms.active
  center := fun i ↦ T.symm (atoms.center i)
  radius := fun i ↦ Kinv * atoms.radius i
  root_eq_zero_of_not_active := by
    intro i hi
    rw [atoms.root_eq_zero_of_not_active i hi]
    rfl
  radius_pos := by
    intro i hi
    exact mul_pos (lt_of_lt_of_le zero_lt_one hKinv) (atoms.radius_pos i hi)
  radius_le_cap := by
    intro i hi
    exact mul_le_mul_of_nonneg_left (atoms.radius_le_cap i hi)
      (zero_le_one.trans hKinv)
  root_contDiff := by
    intro i
    exact (atoms.root_contDiff i).comp T.contDiff
  root_compact_support := by
    intro i
    simpa [Function.comp_def] using
      (atoms.root_compact_support i).comp_homeomorph T.toHomeomorph
  supported := by
    intro i x hx
    have hold := atoms.supported i hx
    rw [Metric.mem_ball] at hold ⊢
    have hrewrite : x - T.symm (atoms.center i) =
        T.symm (T x - atoms.center i) := by
      rw [map_sub, T.symm_apply_apply]
    rw [dist_eq_norm, hrewrite]
    rw [dist_eq_norm] at hold
    calc
      ‖T.symm (T x - atoms.center i)‖ ≤
          ‖T.symm.toContinuousLinearMap‖ * ‖T x - atoms.center i‖ :=
        T.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ Kinv * ‖T x - atoms.center i‖ :=
        mul_le_mul_of_nonneg_right hTinv (norm_nonneg _)
      _ < Kinv * atoms.radius i :=
        mul_lt_mul_of_pos_left hold (lt_of_lt_of_le zero_lt_one hKinv)
  square_identity := by
    intro x
    exact atoms.square_identity (T x)
  dilated_overlap := by
    intro x s
    let small : Set ℕ := {i | i ∈ s ∧ i ∈ atoms.active ∧
      x ∈ Metric.ball (T.symm (atoms.center i)) (A * (Kinv * atoms.radius i))}
    let large : Set ℕ := {i | i ∈ s ∧ i ∈ atoms.active ∧
      T x ∈ Metric.ball (atoms.center i) ((K * Kinv * A) * atoms.radius i)}
    have hsub : small ⊆ large := by
      intro i hi
      change i ∈ s ∧ i ∈ atoms.active ∧
        x ∈ Metric.ball (T.symm (atoms.center i))
          (A * (Kinv * atoms.radius i)) at hi
      refine ⟨hi.1, hi.2.1, ?_⟩
      have hiball := hi.2.2
      rw [Metric.mem_ball] at hiball ⊢
      have hrewrite : T x - atoms.center i = T (x - T.symm (atoms.center i)) := by
        rw [map_sub, T.apply_symm_apply]
      rw [dist_eq_norm, hrewrite]
      rw [dist_eq_norm] at hiball
      calc
        ‖T (x - T.symm (atoms.center i))‖ ≤
            ‖T.toContinuousLinearMap‖ * ‖x - T.symm (atoms.center i)‖ :=
          T.toContinuousLinearMap.le_opNorm _
        _ ≤ K * ‖x - T.symm (atoms.center i)‖ :=
          mul_le_mul_of_nonneg_right hT (norm_nonneg _)
        _ < K * (A * (Kinv * atoms.radius i)) :=
          mul_lt_mul_of_pos_left hiball (lt_of_lt_of_le zero_lt_one hK)
        _ = (K * Kinv * A) * atoms.radius i := by ring
    have hfinite : large.Finite := s.finite_toSet.subset (fun _ hi ↦ hi.1)
    change Set.ncard small ≤ B
    exact (Set.ncard_le_ncard hsub hfinite).trans (atoms.dilated_overlap (T x) s)
  scaled_jets := by
    intro i j hj x
    by_cases hia : i ∈ atoms.active
    · have hri : 0 < atoms.radius i := atoms.radius_pos i hia
      have hcomp : iteratedFDeriv ℝ j (atoms.root i ∘ T) x =
          (iteratedFDeriv ℝ j (atoms.root i) (T x)).compContinuousLinearMap
            (fun _ ↦ T.toContinuousLinearMap) :=
        T.toContinuousLinearMap.iteratedFDeriv_comp_right (atoms.root_contDiff i) x
          (by exact_mod_cast hj)
      change ‖iteratedFDeriv ℝ j (atoms.root i ∘ T) x‖ *
          (Kinv * atoms.radius i) ^ j ≤
        (C * (K * Kinv) ^ 4) * (Kinv * atoms.radius i) ^ 2
      rw [hcomp]
      have hprod : (∏ _ : Fin j, ‖T.toContinuousLinearMap‖) ≤ K ^ j := by
        calc
          (∏ _ : Fin j, ‖T.toContinuousLinearMap‖) ≤ ∏ _ : Fin j, K :=
            Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
              (fun _ _ ↦ hT)
          _ = K ^ j := by simp
      have hKi : 0 < Kinv := lt_of_lt_of_le zero_lt_one hKinv
      have hK0 : 0 ≤ K := zero_le_one.trans hK
      have hKinv0 : 0 ≤ Kinv := hKi.le
      have hcond : 1 ≤ K * Kinv := by nlinarith
      have hjpow : (K * Kinv) ^ j ≤ (K * Kinv) ^ 4 :=
        pow_le_pow_right₀ hcond hj
      have hnormComp :
          ‖(iteratedFDeriv ℝ j (atoms.root i) (T x)).compContinuousLinearMap
            (fun _ ↦ T.toContinuousLinearMap)‖ ≤
          ‖iteratedFDeriv ℝ j (atoms.root i) (T x)‖ * K ^ j := by
        exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
          (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))
      calc
        ‖(iteratedFDeriv ℝ j (atoms.root i) (T x)).compContinuousLinearMap
            (fun _ ↦ T.toContinuousLinearMap)‖ *
            (Kinv * atoms.radius i) ^ j ≤
          (‖iteratedFDeriv ℝ j (atoms.root i) (T x)‖ * K ^ j) *
            (Kinv * atoms.radius i) ^ j :=
          mul_le_mul_of_nonneg_right hnormComp
            (pow_nonneg (mul_nonneg hKinv0 hri.le) j)
        _ = (‖iteratedFDeriv ℝ j (atoms.root i) (T x)‖ * atoms.radius i ^ j) *
            (K * Kinv) ^ j := by
          rw [mul_pow]
          ring
        _ ≤ (C * atoms.radius i ^ 2) * (K * Kinv) ^ j :=
          mul_le_mul_of_nonneg_right (atoms.scaled_jets i j hj (T x))
            (pow_nonneg (mul_nonneg hK0 hKinv0) j)
        _ ≤ (C * atoms.radius i ^ 2) * (K * Kinv) ^ 4 :=
          mul_le_mul_of_nonneg_left hjpow (mul_nonneg hC (sq_nonneg _))
        _ ≤ (C * (K * Kinv) ^ 4) * (Kinv * atoms.radius i) ^ 2 := by
          have hsquare : atoms.radius i ^ 2 ≤ (Kinv * atoms.radius i) ^ 2 := by
            nlinarith [sq_nonneg ((Kinv - 1) * atoms.radius i)]
          calc
            (C * atoms.radius i ^ 2) * (K * Kinv) ^ 4 =
                (C * (K * Kinv) ^ 4) * atoms.radius i ^ 2 := by ring
            _ ≤ (C * (K * Kinv) ^ 4) * (Kinv * atoms.radius i) ^ 2 :=
              mul_le_mul_of_nonneg_left hsquare
                (mul_nonneg hC (pow_nonneg (mul_nonneg hK0 hKinv0) 4))
    · have hz := atoms.root_eq_zero_of_not_active i hia
      have hfun : (fun x ↦ atoms.root i (T x)) = 0 := by
        rw [hz]
        rfl
      rw [hfun]
      change ‖iteratedFDeriv ℝ j (fun _ : Fin n → ℝ ↦ (0 : ℝ)) x‖ *
          (Kinv * atoms.radius i) ^ j ≤
        (C * (K * Kinv) ^ 4) * (Kinv * atoms.radius i) ^ 2
      rw [iteratedFDeriv_zero_fun]
      simp only [Pi.zero_apply, norm_zero, zero_mul]
      positivity
/-- The ambient automorphism taking canonical leading/trailing coordinates to the chosen
unit-direction frame. -/
def canonicalToUnitDirectionFrame {n : ℕ} (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  (finSuccSplitEquiv n).trans (unitDirectionCoordinateFrame v hv)

theorem canonicalToUnitDirectionFrame_apply {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) (x : Fin (n + 1) → ℝ) :
    canonicalToUnitDirectionFrame v hv x =
      unitDirectionCoordinateFrame v hv (finSuccSplitIsometry n x) := rfl

theorem norm_canonicalToUnitDirectionFrame_le_two {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    ‖(canonicalToUnitDirectionFrame v hv).toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖unitDirectionCoordinateFrame v hv (finSuccSplitEquiv n x)‖ ≤ 2 * ‖x‖
  calc
    ‖unitDirectionCoordinateFrame v hv (finSuccSplitEquiv n x)‖ ≤
        2 * ‖finSuccSplitEquiv n x‖ :=
      norm_unitDirectionCoordinateFrame_apply_le_two_mul v hv _
    _ = 2 * ‖x‖ := by rw [norm_finSuccSplitEquiv]
theorem norm_canonicalToUnitDirectionFrame_symm_le_two {n : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1) :
    ‖(canonicalToUnitDirectionFrame v hv).symm.toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖finSuccJoinEquiv n ((unitDirectionCoordinateFrame v hv).symm x)‖ ≤ 2 * ‖x‖
  rw [norm_finSuccJoinEquiv]
  exact norm_unitDirectionCoordinateFrame_symm_apply_le_two_mul v hv x

/-- Undo the canonical unit-direction coordinates.  This is the concrete transport used after
the normal/tangential lift; it costs a factor two in radius and `4^4 = 256` in fourth-order jets. -/
noncomputable def EuclideanAtomFamily.fromUnitDirectionCoordinates {n : ℕ}
    {u : (Fin (n + 1) → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (v : Fin (n + 1) → ℝ) (hv : ‖v‖ = 1)
    (atoms : EuclideanAtomFamily
      (fun x ↦ u (canonicalToUnitDirectionFrame v hv x))
      (4 * A) radiusCap C B) (hC : 0 ≤ C) :
    EuclideanAtomFamily u A (2 * radiusCap) (256 * C) B := by
  let Q := canonicalToUnitDirectionFrame v hv
  have atoms' : EuclideanAtomFamily
      (fun x ↦ u (Q x)) (((2 : ℝ) * 2) * A) radiusCap C B := by
    rw [show ((2 : ℝ) * 2) * A = 4 * A by ring]
    simpa [Q] using atoms
  let pulled := atoms'.pullbackContinuousLinearEquiv Q.symm
    (A := A) (K := 2) (Kinv := 2) (by norm_num)
    (norm_canonicalToUnitDirectionFrame_symm_le_two v hv)
    (by norm_num) (norm_canonicalToUnitDirectionFrame_le_two v hv) hC
  have htarget : (fun x ↦ (fun y ↦ u (Q y)) (Q.symm x)) = u := by
    funext x
    simp [Q]
  have hconstant : C * ((2 : ℝ) * 2) ^ 4 = 256 * C := by ring
  simpa [pulled, Q, hconstant, mul_assoc] using pulled.congrTarget htarget

/-! ## Quantitative curvature-split assembly -/

/-- Coordinates of an ambient point in the normal/tangential frame selected by a curvature
preprocessing package. -/
def curvatureSplitCoordinates {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C) :
    (Fin (n + 1) → ℝ) → (ℝ × (Fin n → ℝ)) :=
  (unitDirectionCoordinateFrame prep.direction prep.direction_norm).symm

/-- The parent cutoff pulled back to the selected normal/tangential frame. -/
def curvatureParentCutoffPullback {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (cutoff : (Fin (n + 1) → ℝ) → ℝ) :
    (ℝ × (Fin n → ℝ)) → ℝ :=
  cutoff ∘ unitDirectionCoordinateFrame prep.direction prep.direction_norm

/-- The explicit square root of the main term after undoing the doubled curvature
normalization. -/
def curvatureMainRoot {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (cutoff : (Fin (n + 1) → ℝ) → ℝ)
    (root : (ℝ × (Fin n → ℝ)) → ℝ)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (Real.sqrt (1 / 2 : ℝ) * cutoff x) *
    root (curvatureSplitCoordinates prep x)

/-- The residual target before using that the tangential cutoff is one over the parent cutoff. -/
def curvatureCutoffResidual {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (cutoff : (Fin (n + 1) → ℝ) → ℝ)
    (zeta residual : (Fin n → ℝ) → ℝ)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  (1 / 2 : ℝ) * cutoff x ^ 2 *
    (zeta (curvatureSplitCoordinates prep x).2 ^ 2 *
      residual (curvatureSplitCoordinates prep x).2)

theorem curvatureMainRoot_contDiff {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    {root : (ℝ × (Fin n → ℝ)) → ℝ}
    (hcutoff : ContDiff ℝ 4 cutoff) (hroot : ContDiff ℝ 4 root) :
    ContDiff ℝ 4 (curvatureMainRoot prep cutoff root) := by
  have hcoordinates : ContDiff ℝ 4 (curvatureSplitCoordinates prep) :=
    (unitDirectionCoordinateFrame prep.direction prep.direction_norm).symm.contDiff
  have hconstant : ContDiff ℝ 4
      (fun _ : Fin (n + 1) → ℝ ↦ Real.sqrt (1 / 2 : ℝ)) := contDiff_const
  change ContDiff ℝ 4 (fun x ↦
    (Real.sqrt (1 / 2 : ℝ) * cutoff x) *
      root (curvatureSplitCoordinates prep x))
  exact (hconstant.mul hcutoff).mul (hroot.comp hcoordinates)

theorem curvatureMainRoot_compactSupport {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    (root : (ℝ × (Fin n → ℝ)) → ℝ)
    (hcutoff : HasCompactSupport cutoff) :
    HasCompactSupport (curvatureMainRoot prep cutoff root) := by
  have hscaled : HasCompactSupport (fun x ↦ Real.sqrt (1 / 2 : ℝ) * cutoff x) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      hcutoff.smul_left (f := fun _ ↦ Real.sqrt (1 / 2 : ℝ))
  change HasCompactSupport (fun x ↦
    (Real.sqrt (1 / 2 : ℝ) * cutoff x) *
      root (curvatureSplitCoordinates prep x))
  exact hscaled.mul_right
theorem support_curvatureMainRoot_subset {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (cutoff : (Fin (n + 1) → ℝ) → ℝ)
    (root : (ℝ × (Fin n → ℝ)) → ℝ) :
    Function.support (curvatureMainRoot prep cutoff root) ⊆
      Function.support cutoff := by
  intro x hx hzero
  apply hx
  simp [curvatureMainRoot, hzero]

theorem curvatureMainRoot_sq {n : ℕ} {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (cutoff : (Fin (n + 1) → ℝ) → ℝ)
    (root : (ℝ × (Fin n → ℝ)) → ℝ)
    (x : Fin (n + 1) → ℝ) :
    curvatureMainRoot prep cutoff root x ^ 2 =
      (1 / 2 : ℝ) * cutoff x ^ 2 *
        root (curvatureSplitCoordinates prep x) ^ 2 := by
  rw [curvatureMainRoot, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem support_curvatureCutoffResidual_subset {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (cutoff : (Fin (n + 1) → ℝ) → ℝ)
    (zeta residual : (Fin n → ℝ) → ℝ) :
    Function.support (curvatureCutoffResidual prep cutoff zeta residual) ⊆
      Function.support cutoff := by
  intro x hx hzero
  apply hx
  simp [curvatureCutoffResidual, hzero]

/-- Exactly the quantitative information which the bounded analytic split must supply to the
atom-assembly layer.  All bounds are global; the exact identities are needed only where the
actual parent cutoff is nonzero. -/
structure QuantitativeCurvatureSplitOutput {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    (cutoff : (Fin (n + 1) → ℝ) → ℝ)
    (parentRadius Mmain Azeta Aresidual : ℝ) where
  root : (ℝ × (Fin n → ℝ)) → ℝ
  residual : (Fin n → ℝ) → ℝ
  zeta : (Fin n → ℝ) → ℝ
  root_contDiff : ContDiff ℝ 4 root
  residual_contDiff : ContDiff ℝ 6 residual
  residual_nonnegative : ∀ y, 0 ≤ residual y
  zeta_contDiff : ContDiff ℝ 6 zeta
  zeta_compactSupport : HasCompactSupport zeta
  exact_square_on_cutoff : ∀ z,
    cutoff (unitDirectionCoordinateFrame prep.direction prep.direction_norm z) ≠ 0 →
      prep.input.function z = root z ^ 2 + residual z.2
  zeta_eq_one_on_cutoff : ∀ z,
    cutoff (unitDirectionCoordinateFrame prep.direction prep.direction_norm z) ≠ 0 →
      zeta z.2 = 1
  main_scaled_jets : ∀ j, j ≤ 4 → ∀ x,
    ‖iteratedFDeriv ℝ j (curvatureMainRoot prep cutoff root) x‖ *
        (2 * parentRadius) ^ j ≤ Mmain * (2 * parentRadius) ^ 2
  zeta_global_jets : ∀ j, j ≤ 6 → ∀ y,
    ‖iteratedFDeriv ℝ j zeta y‖ ≤ Azeta
  residual_global_jets : ∀ j, j ≤ 6 → ∀ y,
    ‖iteratedFDeriv ℝ j residual y‖ ≤ Aresidual

theorem QuantitativeCurvatureSplitOutput.target_identity {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    {prep : IntrinsicBoundedSplitPreprocessing n Φ C}
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    {parentRadius Mmain Azeta Aresidual : ℝ}
    (data : QuantitativeCurvatureSplitOutput prep cutoff
      parentRadius Mmain Azeta Aresidual) (x : Fin (n + 1) → ℝ) :
    curvatureMainRoot prep cutoff data.root x ^ 2 +
        curvatureCutoffResidual prep cutoff data.zeta data.residual x =
      cutoff x ^ 2 * Φ x := by
  by_cases hcut : cutoff x = 0
  · simp [curvatureMainRoot, curvatureCutoffResidual, hcut]
  · let T := unitDirectionCoordinateFrame prep.direction prep.direction_norm
    let z := T.symm x
    have hTz : T z = x := T.apply_symm_apply x
    have hsplit := data.exact_square_on_cutoff z (by simpa [T, hTz] using hcut)
    have hzeta := data.zeta_eq_one_on_cutoff z (by simpa [T, hTz] using hcut)
    have hfunction := congrFun prep.function_eq z
    have hfunction' : prep.input.function z = 2 * Φ x := by
      simpa [doubledCurvaturePullback, T, hTz] using hfunction
    rw [curvatureMainRoot_sq]
    simp only [curvatureCutoffResidual]
    have hcoordinates : curvatureSplitCoordinates prep x = z := by
      simp [curvatureSplitCoordinates, z, T]
    rw [hcoordinates, hzeta]
    norm_num
    nlinarith

/-- Assemble atomwise interval partitions from a single scale-uniform selector. -/
noncomputable def AtomwiseIntervalSquarePartitions.ofSelector {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C D Cp : ℝ} {B Bp : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B)
    (selector : ∀ r : ℝ, 0 < r → Nonempty (ScaledIntervalSquarePartition r D Cp Bp)) :
    AtomwiseIntervalSquarePartitions atoms D Cp Bp where
  partition := fun i ↦ Classical.choice
    (selector (atoms.intervalLiftScale i) (atoms.intervalLiftScale_pos i))

theorem curvatureParentCutoffPullback_contDiff {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    (hcutoff : ContDiff ℝ 4 cutoff) :
    ContDiff ℝ 4 (curvatureParentCutoffPullback prep cutoff) := by
  exact hcutoff.comp
    (unitDirectionCoordinateFrame prep.direction prep.direction_norm).contDiff

theorem curvatureParentCutoffPullback_compactSupport {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    (hcutoff : HasCompactSupport cutoff) :
    HasCompactSupport (curvatureParentCutoffPullback prep cutoff) := by
  simpa [curvatureParentCutoffPullback, Function.comp_def] using
    hcutoff.comp_homeomorph
      (unitDirectionCoordinateFrame prep.direction prep.direction_norm).toHomeomorph

/-- Pulling the parent cutoff into a unit-direction frame costs at most `2^j`, hence at most
sixteen through the fourth derivative. -/
theorem norm_iteratedFDeriv_curvatureParentCutoffPullback_le {n j : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C Acut : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    (hcutoff : ContDiff ℝ 4 cutoff) (hAcut : 0 ≤ Acut)
    (hcutoffBound : ∀ q, q ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ q cutoff x‖ ≤ Acut)
    (hj : j ≤ 4) (z : ℝ × (Fin n → ℝ)) :
    ‖iteratedFDeriv ℝ j (curvatureParentCutoffPullback prep cutoff) z‖ ≤
      16 * Acut := by
  let T := unitDirectionCoordinateFrame prep.direction prep.direction_norm
  have hpull := coordinateFramePullback_iteratedFDeriv
    (m := 4) hcutoff T z hj
  have hcomp : iteratedFDeriv ℝ j (curvatureParentCutoffPullback prep cutoff) z =
      (iteratedFDeriv ℝ j cutoff (T z)).compContinuousLinearMap
        (fun _ ↦ T.toContinuousLinearMap) := by
    simpa [curvatureParentCutoffPullback, coordinateFramePullback, T] using hpull
  rw [hcomp]
  have hnormT : ‖T.toContinuousLinearMap‖ ≤ 2 := by
    simpa [T] using norm_unitDirectionCoordinateFrame_le_two
      prep.direction prep.direction_norm
  have hprod : (∏ _ : Fin j, ‖T.toContinuousLinearMap‖) ≤ (2 : ℝ) ^ j := by
    calc
      (∏ _ : Fin j, ‖T.toContinuousLinearMap‖) ≤ ∏ _ : Fin j, (2 : ℝ) :=
        Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ hnormT)
      _ = (2 : ℝ) ^ j := by simp
  have hpow : (2 : ℝ) ^ j ≤ 16 := by
    interval_cases j <;> norm_num
  calc
    ‖(iteratedFDeriv ℝ j cutoff (T z)).compContinuousLinearMap
        (fun _ ↦ T.toContinuousLinearMap)‖ ≤
      ‖iteratedFDeriv ℝ j cutoff (T z)‖ *
        ∏ _ : Fin j, ‖T.toContinuousLinearMap‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ Acut * (2 : ℝ) ^ j :=
      mul_le_mul (hcutoffBound j hj (T z)) hprod
        (by positivity) hAcut
    _ ≤ Acut * 16 := mul_le_mul_of_nonneg_left hpow hAcut
    _ = 16 * Acut := by ring

theorem curvatureParentCutoffPullback_scaled_le {n j : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C Acut r : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    (hcutoff : ContDiff ℝ 4 cutoff) (hAcut : 0 ≤ Acut)
    (hcutoffBound : ∀ q, q ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ q cutoff x‖ ≤ Acut)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hj : j ≤ 4)
    (z : ℝ × (Fin n → ℝ)) :
    ‖iteratedFDeriv ℝ j (curvatureParentCutoffPullback prep cutoff) z‖ * r ^ j ≤
      16 * Acut := by
  have hglobal := norm_iteratedFDeriv_curvatureParentCutoffPullback_le
    prep hcutoff hAcut hcutoffBound hj z
  have hrpow : r ^ j ≤ 1 := pow_le_one₀ hr0 hr1
  calc
    ‖iteratedFDeriv ℝ j (curvatureParentCutoffPullback prep cutoff) z‖ * r ^ j ≤
        (16 * Acut) * r ^ j :=
      mul_le_mul_of_nonneg_right hglobal (pow_nonneg hr0 j)
    _ ≤ (16 * Acut) * 1 :=
      mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = 16 * Acut := by ring

/-- Fixed child cap leaving enough room for interval lifting and the norm-two frame pullback. -/
def curvatureChildRadiusCap (A parentA : ℝ) : ℝ :=
  1 / (16 * (A + 1) * parentA)

theorem curvatureChildRadiusCap_pos {A parentA : ℝ}
    (hA : 1 ≤ A) (hparentA : 1 ≤ parentA) :
    0 < curvatureChildRadiusCap A parentA := by
  apply one_div_pos.mpr
  positivity

theorem curvatureChildRadiusCap_le_one {A parentA : ℝ}
    (hA : 1 ≤ A) (hparentA : 1 ≤ parentA) :
    curvatureChildRadiusCap A parentA ≤ 1 := by
  rw [curvatureChildRadiusCap, div_le_one (by positivity)]
  nlinarith [mul_pos (show 0 < A + 1 by linarith)
    (show 0 < parentA by linarith)]

theorem four_mul_curvatureChildRadiusCap_le_one {A parentA : ℝ}
    (hA : 1 ≤ A) (hparentA : 1 ≤ parentA) :
    4 * curvatureChildRadiusCap A parentA ≤ 1 := by
  rw [curvatureChildRadiusCap]
  have hden : 0 < 16 * (A + 1) * parentA := by positivity
  rw [show 4 * (1 / (16 * (A + 1) * parentA)) =
      4 / (16 * (A + 1) * parentA) by ring]
  rw [div_le_one hden]
  nlinarith [mul_pos (show 0 < A + 1 by linarith)
    (show 0 < parentA by linarith)]

/-- The exact margin inequality used after lift (factor two) and frame pullback (factor two). -/
theorem curvatureResidual_localization_margin
    {A parentA parentRadius parentDilation : ℝ}
    (hA : 1 ≤ A) (hparentA : 1 ≤ parentA)
    (hparentRadius : parentA⁻¹ ≤ parentRadius)
    (hD : 4 * A ≤ parentDilation) :
    (A + 1) * (4 * curvatureChildRadiusCap A parentA) +
        2 * parentRadius ≤ parentDilation * parentRadius := by
  have hAp : 0 < A + 1 := by linarith
  have hp : 0 < parentA := by linarith
  have hq : 0 < parentRadius := lt_of_lt_of_le (inv_pos.mpr hp) hparentRadius
  have hcap : (A + 1) * (4 * curvatureChildRadiusCap A parentA) =
      1 / (4 * parentA) := by
    rw [curvatureChildRadiusCap]
    field_simp
    ring
  have hinvQuarter : 1 / (4 * parentA) ≤ parentRadius / 4 := by
    have := mul_le_mul_of_nonneg_right hparentRadius (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa [div_eq_mul_inv] using this
  have hfour : parentRadius / 4 + 2 * parentRadius ≤ 4 * A * parentRadius := by
    nlinarith
  have hDmul : 4 * A * parentRadius ≤ parentDilation * parentRadius :=
    mul_le_mul_of_nonneg_right hD hq.le
  rw [hcap]
  nlinarith [hinvQuarter, hfour, hDmul]

theorem curvatureMain_ball_localization {n : ℕ}
    {A parentRadius parentDilation : ℝ} (hparentRadius : 0 < parentRadius)
    (hD : 2 * A ≤ parentDilation) :
    Metric.ball (0 : Fin n → ℝ) (A * (2 * parentRadius)) ⊆
      Metric.ball 0 (parentDilation * parentRadius) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx ⊢
  have hradius : A * (2 * parentRadius) ≤ parentDilation * parentRadius := by
    nlinarith
  exact hx.trans_le hradius

/-- Normalization used before applying the lower-dimensional induction hypothesis. -/
def curvatureResidualNormalizationConstant (Azeta Aresidual : ℝ) : ℝ :=
  max 1 (64 * (64 * Azeta * Azeta) * Aresidual)

def normalizedCurvatureResidual {n : ℕ}
    (zeta residual : (Fin n → ℝ) → ℝ) (Azeta Aresidual : ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun y ↦ (curvatureResidualNormalizationConstant Azeta Aresidual)⁻¹ *
    (zeta y ^ 2 * residual y)

theorem curvatureResidualNormalizationConstant_pos (Azeta Aresidual : ℝ) :
    0 < curvatureResidualNormalizationConstant Azeta Aresidual := by
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem QuantitativeCurvatureSplitOutput.normalized_residual {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    {prep : IntrinsicBoundedSplitPreprocessing n Φ C}
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    {parentRadius Mmain Azeta Aresidual : ℝ}
    (data : QuantitativeCurvatureSplitOutput prep cutoff
      parentRadius Mmain Azeta Aresidual)
    (hAzeta : 0 ≤ Azeta) (hAresidual : 0 ≤ Aresidual) :
    NormalizedNonnegativeC6
      (normalizedCurvatureResidual data.zeta data.residual Azeta Aresidual) := by
  simpa [normalizedCurvatureResidual, curvatureResidualNormalizationConstant] using
    normalized_cutoffResidual data.residual_nonnegative data.zeta_contDiff
      data.residual_contDiff data.zeta_compactSupport hAzeta hAresidual
      data.zeta_global_jets data.residual_global_jets

/-- Explicit jet constant produced by normalize, recurse, lift, halve, and undo the frame. -/
def curvatureResidualAtomConstant
    (Acut Cp Cchild Azeta Aresidual : ℝ) : ℝ :=
  256 * (Real.sqrt (1 / 2 : ℝ) *
    (1024 * (16 * Acut) * Cp *
      (Real.sqrt (curvatureResidualNormalizationConstant Azeta Aresidual) * Cchild)))

theorem curvatureResidualAtomConstant_nonnegative
    {Acut Cp Cchild Azeta Aresidual : ℝ}
    (hAcut : 0 ≤ Acut) (hCp : 0 ≤ Cp) (hCchild : 0 ≤ Cchild) :
    0 ≤ curvatureResidualAtomConstant Acut Cp Cchild Azeta Aresidual := by
  unfold curvatureResidualAtomConstant
  positivity

/-- The entire residual path: normalize, invoke the lower-dimensional atoms, lift through the
normal interval partition, divide by the doubled-curvature factor, and undo the selected frame. -/
theorem exists_curvatureCutoffResidualAtoms {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    {prep : IntrinsicBoundedSplitPreprocessing n Φ C}
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    {parentRadius Mmain Azeta Aresidual A parentA Acut Cchild Cp : ℝ}
    {Bchild Bp : ℕ}
    (data : QuantitativeCurvatureSplitOutput prep cutoff
      parentRadius Mmain Azeta Aresidual)
    (hA : 1 ≤ A) (hparentA : 1 ≤ parentA)
    (hAcut : 0 ≤ Acut) (hCchild : 0 ≤ Cchild) (hCp : 0 ≤ Cp)
    (hAzeta : 0 ≤ Azeta) (hAresidual : 0 ≤ Aresidual)
    (hcutoffSmooth : ContDiff ℝ 4 cutoff)
    (hcutoffCompact : HasCompactSupport cutoff)
    (hcutoffBound : ∀ q, q ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ q cutoff x‖ ≤ Acut)
    (hchildren : ∀ w : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 w →
      Nonempty (EuclideanAtomFamily w (8 * A)
        (curvatureChildRadiusCap A parentA) Cchild Bchild))
    (hpartitions : ∀ r : ℝ, 0 < r →
      Nonempty (ScaledIntervalSquarePartition r (8 * A) Cp Bp)) :
    Nonempty (EuclideanAtomFamily
      (curvatureCutoffResidual prep cutoff data.zeta data.residual)
      A (4 * curvatureChildRadiusCap A parentA)
      (curvatureResidualAtomConstant Acut Cp Cchild Azeta Aresidual)
      (Bchild * Bp)) := by
  classical
  let childCap := curvatureChildRadiusCap A parentA
  let K := curvatureResidualNormalizationConstant Azeta Aresidual
  let normalized := normalizedCurvatureResidual data.zeta data.residual Azeta Aresidual
  have hK : 0 < K := curvatureResidualNormalizationConstant_pos _ _
  have hnormalized : NormalizedNonnegativeC6 normalized := by
    simpa [normalized] using data.normalized_residual hAzeta hAresidual
  obtain ⟨child₀⟩ := hchildren normalized hnormalized
  let childScaled₀ := child₀.constScale K hK.le
  have hchildTarget : (fun y ↦ K * normalized y) =
      (fun y ↦ data.zeta y ^ 2 * data.residual y) := by
    funext y
    dsimp [normalized, normalizedCurvatureResidual, K]
    rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
  let childScaled := childScaled₀.congrTarget hchildTarget
  have hchildDilation : (8 : ℝ) * A = 2 * (4 * A) := by ring
  let child : EuclideanAtomFamily
      (fun y ↦ data.zeta y ^ 2 * data.residual y)
      (2 * (4 * A)) childCap (Real.sqrt K * Cchild) Bchild := by
    rw [← hchildDilation]
    exact childScaled
  have hpartitionSelector : ∀ r : ℝ, 0 < r →
      Nonempty (ScaledIntervalSquarePartition r (2 * (4 * A)) Cp Bp) := by
    intro r hr
    rw [← hchildDilation]
    exact hpartitions r hr
  let partitions : AtomwiseIntervalSquarePartitions child (2 * (4 * A)) Cp Bp :=
    AtomwiseIntervalSquarePartitions.ofSelector child hpartitionSelector
  have hchildCapOne : childCap ≤ 1 := by
    simpa [childCap] using curvatureChildRadiusCap_le_one hA hparentA
  have hparentScaled : ∀ i, i ∈ child.active → ∀ q, q ≤ 4 →
      ∀ z : ℝ × (Fin n → ℝ),
      ‖iteratedFDeriv ℝ q (curvatureParentCutoffPullback prep cutoff) z‖ *
          child.radius i ^ q ≤ 16 * Acut := by
    intro i hi q hq z
    exact curvatureParentCutoffPullback_scaled_le prep hcutoffSmooth hAcut
      hcutoffBound (child.radius_pos i hi).le
      ((child.radius_le_cap i hi).trans hchildCapOne) hq z
  let lifted := child.liftThroughNormalPartition partitions
    (curvatureParentCutoffPullback prep cutoff)
    (mul_nonneg (Real.sqrt_nonneg K) hCchild)
    hCp (by positivity : 0 ≤ 16 * Acut)
    (curvatureParentCutoffPullback_contDiff prep hcutoffSmooth)
    (curvatureParentCutoffPullback_compactSupport prep hcutoffCompact)
    hparentScaled
  let halved := lifted.constScale (1 / 2 : ℝ) (by norm_num)
  let Q := canonicalToUnitDirectionFrame prep.direction prep.direction_norm
  have hcanonicalTarget :
      (fun x ↦ (1 / 2 : ℝ) *
        ((curvatureParentCutoffPullback prep cutoff (finSuccSplitIsometry n x)) ^ 2 *
          ((fun y ↦ data.zeta y ^ 2 * data.residual y)
            (finSuccSplitIsometry n x).2))) =
      (fun x ↦ curvatureCutoffResidual prep cutoff data.zeta data.residual (Q x)) := by
    funext x
    have hcoordinates : curvatureSplitCoordinates prep (Q x) =
        finSuccSplitIsometry n x := by
      simp [curvatureSplitCoordinates, Q, canonicalToUnitDirectionFrame]
    rw [curvatureCutoffResidual, hcoordinates]
    simp [curvatureParentCutoffPullback, Q, canonicalToUnitDirectionFrame]
    ring
  let canonical := halved.congrTarget hcanonicalTarget
  let transported := canonical.fromUnitDirectionCoordinates
    prep.direction prep.direction_norm
    (by positivity)
  have hcap : 2 * (2 * childCap) = 4 * curvatureChildRadiusCap A parentA := by
    simp [childCap]
    ring
  have hconstant :
      256 * (Real.sqrt (1 / 2 : ℝ) *
        (1024 * (16 * Acut) * Cp * (Real.sqrt K * Cchild))) =
      curvatureResidualAtomConstant Acut Cp Cchild Azeta Aresidual := by
    rfl
  exact ⟨by
    rw [← hcap, ← hconstant]
    exact transported⟩

/-- Full local curvature-branch assembly from the narrowly quantitative analytic output.
The main square is added only after the residual atoms have been transported back to ambient
coordinates, so its natural `2 * parentRadius` support does not pay the frame condition number. -/
theorem exists_localizedCurvatureSplitAtomFamily {n : ℕ}
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    {prep : IntrinsicBoundedSplitPreprocessing n Φ C}
    {cutoff : (Fin (n + 1) → ℝ) → ℝ}
    {parentRadius Mmain Azeta Aresidual A parentA Acut Cchild Cp
      parentDilation : ℝ}
    {Bchild Bp : ℕ}
    (data : QuantitativeCurvatureSplitOutput prep cutoff
      parentRadius Mmain Azeta Aresidual)
    (hA : 1 ≤ A) (hparentA : 1 ≤ parentA)
    (hparentRadius : 0 < parentRadius)
    (hparentRadiusLower : parentA⁻¹ ≤ parentRadius)
    (hparentRadiusHalf : parentRadius ≤ 1 / 2)
    (hparentDilation : 4 * A ≤ parentDilation)
    (hMmain : 0 ≤ Mmain) (hAcut : 0 ≤ Acut)
    (hCchild : 0 ≤ Cchild) (hCp : 0 ≤ Cp)
    (hAzeta : 0 ≤ Azeta) (hAresidual : 0 ≤ Aresidual)
    (hcutoffSmooth : ContDiff ℝ 4 cutoff)
    (hcutoffCompact : HasCompactSupport cutoff)
    (hcutoffSupport : Function.support cutoff ⊆
      Metric.ball 0 (2 * parentRadius))
    (hcutoffBound : ∀ q, q ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ q cutoff x‖ ≤ Acut)
    (hchildren : ∀ w : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 w →
      Nonempty (EuclideanAtomFamily w (8 * A)
        (curvatureChildRadiusCap A parentA) Cchild Bchild))
    (hpartitions : ∀ r : ℝ, 0 < r →
      Nonempty (ScaledIntervalSquarePartition r (8 * A) Cp Bp)) :
    Nonempty (LocalizedEuclideanAtomFamily
      (fun x ↦ cutoff x ^ 2 * Φ x)
      A 1
      (max Mmain (curvatureResidualAtomConstant
        Acut Cp Cchild Azeta Aresidual))
      (1 + Bchild * Bp) 0 parentRadius parentDilation) := by
  obtain ⟨residualAtoms⟩ := exists_curvatureCutoffResidualAtoms
    data hA hparentA hAcut hCchild hCp hAzeta hAresidual
    hcutoffSmooth hcutoffCompact hcutoffBound hchildren hpartitions
  have hresidualSupport :
      Function.support (curvatureCutoffResidual prep cutoff data.zeta data.residual) ⊆
        Metric.ball (0 : Fin (n + 1) → ℝ) (2 * parentRadius) :=
    (support_curvatureCutoffResidual_subset prep cutoff data.zeta data.residual).trans
      hcutoffSupport
  have hmargin :
      (A + 1) * (4 * curvatureChildRadiusCap A parentA) +
          2 * parentRadius ≤ parentDilation * parentRadius :=
    curvatureResidual_localization_margin hA hparentA
      hparentRadiusLower hparentDilation
  let residualLocalizedSmall := residualAtoms.localizeOfTargetSupport
    (zero_le_one.trans hA) hresidualSupport hmargin
  have hresidualCap : 4 * curvatureChildRadiusCap A parentA ≤ 1 :=
    four_mul_curvatureChildRadiusCap_le_one hA hparentA
  let residualLocalized := residualLocalizedSmall.increaseRadiusCap hresidualCap
  have hmainRadius : 0 < 2 * parentRadius := by positivity
  have hmainRadiusCap : 2 * parentRadius ≤ 1 := by nlinarith
  have hmainLocal :
      Metric.ball (0 : Fin (n + 1) → ℝ) (A * (2 * parentRadius)) ⊆
        Metric.ball 0 (parentDilation * parentRadius) :=
    curvatureMain_ball_localization hparentRadius (by linarith)
  let main : LocalizedEuclideanAtomFamily
      (fun x ↦ curvatureMainRoot prep cutoff data.root x ^ 2)
      A 1 Mmain 1 0 parentRadius parentDilation :=
    singleLocalizedEuclideanAtomFamily hmainRadius hmainRadiusCap hMmain
      (curvatureMainRoot_contDiff prep hcutoffSmooth data.root_contDiff)
      (curvatureMainRoot_compactSupport prep data.root hcutoffCompact)
      ((support_curvatureMainRoot_subset prep cutoff data.root).trans hcutoffSupport)
      (fun _ ↦ rfl) data.main_scaled_jets hmainLocal
  let combined := main.add residualLocalized
  have htarget :
      (fun x ↦ curvatureMainRoot prep cutoff data.root x ^ 2 +
        curvatureCutoffResidual prep cutoff data.zeta data.residual x) =
      (fun x ↦ cutoff x ^ 2 * Φ x) := by
    funext x
    exact data.target_identity x
  exact ⟨combined.congrTarget htarget⟩

/-- Fine-cover specialization of the full local curvature assembly.  All cutoff estimates and
the lower/upper bounds on the intrinsic parent-radius ratio are discharged from the cover API. -/
theorem exists_localizedFineCoverCurvatureSplitAtomFamily {n : ℕ}
    {u : (Fin (n + 1) → ℝ) → ℝ}
    {parentDilation sigma parentA : ℝ} {parentB : ℕ}
    (cover : FineQuantitativeScaleCover
      u parentDilation sigma parentA parentB)
    {i : ℕ} (hi : i ∈ cover.active)
    {Φ : (Fin (n + 1) → ℝ) → ℝ} {C : ℝ}
    (prep : IntrinsicBoundedSplitPreprocessing n Φ C)
    {Mmain Azeta Aresidual A Cchild Cp : ℝ} {Bchild Bp : ℕ}
    (data : QuantitativeCurvatureSplitOutput prep (cover.intrinsicCutoff i)
      (cover.radius i / nonnegativeJetScale u (cover.center i))
      Mmain Azeta Aresidual)
    (hA : 1 ≤ A) (hparentA : 1 ≤ parentA)
    (hsigma : sigma ≤ 1 / 2) (hparentDilation : 4 * A ≤ parentDilation)
    (hMmain : 0 ≤ Mmain) (hCchild : 0 ≤ Cchild) (hCp : 0 ≤ Cp)
    (hAzeta : 0 ≤ Azeta) (hAresidual : 0 ≤ Aresidual)
    (hchildren : ∀ w : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 w →
      Nonempty (EuclideanAtomFamily w (8 * A)
        (curvatureChildRadiusCap A parentA) Cchild Bchild))
    (hpartitions : ∀ r : ℝ, 0 < r →
      Nonempty (ScaledIntervalSquarePartition r (8 * A) Cp Bp)) :
    Nonempty (LocalizedEuclideanAtomFamily
      (fun x ↦ cover.intrinsicCutoff i x ^ 2 * Φ x)
      A 1
      (max Mmain (curvatureResidualAtomConstant
        (parentA ^ 7) Cp Cchild Azeta Aresidual))
      (1 + Bchild * Bp) 0
      (cover.radius i / nonnegativeJetScale u (cover.center i))
      parentDilation) := by
  let R := nonnegativeJetScale u (cover.center i)
  let q := cover.radius i / R
  have hq : 0 < q := by
    simpa [q, R] using cover.radiusRatio_pos hi
  have hparentApos : 0 < parentA := lt_of_lt_of_le zero_lt_one hparentA
  have hqLower : parentA⁻¹ ≤ q := by
    simpa [q, R] using cover.inv_le_radiusRatio hi hparentApos
  have hR : 0 < R := (cover.radius_pos i hi).trans_le
    (cover.radius_comparable i hi).1
  have hqSigma : q ≤ sigma := by
    dsimp [q]
    rw [div_le_iff₀ hR]
    exact cover.radius_le_fine i hi
  have hqHalf : q ≤ 1 / 2 := hqSigma.trans hsigma
  have hsupport : Function.support (cover.intrinsicCutoff i) ⊆
      Metric.ball (0 : Fin (n + 1) → ℝ) (2 * q) := by
    have hbase := cover.intrinsicCutoff_support_subset_radius hi
    have hradiusEq : cover.intrinsicCutoffRadius i = 2 * q := by
      dsimp [FineQuantitativeScaleCover.intrinsicCutoffRadius, q, R]
      ring
    rw [hradiusEq] at hbase
    exact hbase
  have hAcut : 0 ≤ parentA ^ 7 := pow_nonneg (zero_le_one.trans hparentA) 7
  have hcutoffBound : ∀ j, j ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ j (cover.intrinsicCutoff i) x‖ ≤ parentA ^ 7 := by
    intro j hj x
    exact cover.intrinsicCutoff_uniform_deriv_bound hparentA hi x j (hj.trans (by norm_num))
  simpa [q, R] using exists_localizedCurvatureSplitAtomFamily
    data hA hparentA hq hqLower hqHalf hparentDilation hMmain hAcut
    hCchild hCp hAzeta hAresidual
    ((cover.intrinsicCutoff_contDiff i).of_le (by norm_num))
    (cover.intrinsicCutoff_compactSupport hi) hsupport hcutoffBound
    hchildren hpartitions
end QuarticConvergence
end OptimalConvergenceRates
