/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/Atoms.lean

  The uniform scale-resolved Euclidean atom theorem.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ParentPatch
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.UniformSplit
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FineScaleCover
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.IntervalPartition
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.PositiveValueCutoff
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Pairing

open Set
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A countable Euclidean square decomposition with prescribed dilation and radius cap. -/
structure EuclideanAtomFamily {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (A radiusCap C : ℝ) (B : ℕ) where
  root : ℕ → ((Fin n → ℝ) → ℝ)
  active : Set ℕ
  center : ℕ → (Fin n → ℝ)
  radius : ℕ → ℝ
  root_eq_zero_of_not_active : ∀ i, i ∉ active → root i = 0
  radius_pos : ∀ i, i ∈ active → 0 < radius i
  radius_le_cap : ∀ i, i ∈ active → radius i ≤ radiusCap
  root_contDiff : ∀ i, ContDiff ℝ 4 (root i)
  root_compact_support : ∀ i, HasCompactSupport (root i)
  supported : ∀ i, Function.support (root i) ⊆ Metric.ball (center i) (radius i)
  square_identity : ∀ x, HasSum (fun i ↦ root i x ^ 2) (u x)
  dilated_overlap : ∀ x (s : Finset ℕ),
    Set.ncard {i | i ∈ s ∧ i ∈ active ∧ x ∈ Metric.ball (center i) (A * radius i)} ≤ B
  scaled_jets : ∀ i j, j ≤ 4 → ∀ x,
    ‖iteratedFDeriv ℝ j (root i) x‖ * radius i ^ j ≤ C * radius i ^ 2
/-- Combine two atom families by a disjoint countable reindexing.  The overlap budgets add and
the common jet bound is the larger of the two bounds. -/
noncomputable def EuclideanAtomFamily.add {n : ℕ}
    {u v : (Fin n → ℝ) → ℝ} {A radiusCap C₁ C₂ : ℝ} {B₁ B₂ : ℕ}
    (left : EuclideanAtomFamily u A radiusCap C₁ B₁)
    (right : EuclideanAtomFamily v A radiusCap C₂ B₂) :
    EuclideanAtomFamily (fun x ↦ u x + v x) A radiusCap (max C₁ C₂) (B₁ + B₂) := by
  let e : ℕ ⊕ ℕ ≃ ℕ := Equiv.natSumNatEquivNat
  let whichRoot : ℕ ⊕ ℕ → ((Fin n → ℝ) → ℝ) := Sum.elim left.root right.root
  let whichActive : ℕ ⊕ ℕ → Prop := Sum.elim (fun i ↦ i ∈ left.active)
    (fun i ↦ i ∈ right.active)
  let whichCenter : ℕ ⊕ ℕ → (Fin n → ℝ) := Sum.elim left.center right.center
  let whichRadius : ℕ ⊕ ℕ → ℝ := Sum.elim left.radius right.radius
  refine {
    root := fun k ↦ whichRoot (e.symm k)
    active := {k | whichActive (e.symm k)}
    center := fun k ↦ whichCenter (e.symm k)
    radius := fun k ↦ whichRadius (e.symm k)
    root_eq_zero_of_not_active := ?_
    radius_pos := ?_
    radius_le_cap := ?_
    root_contDiff := ?_
    root_compact_support := ?_
    supported := ?_
    square_identity := ?_
    dilated_overlap := ?_
    scaled_jets := ?_
  }
  · intro k hk
    cases hq : e.symm k with
    | inl i =>
        exact left.root_eq_zero_of_not_active i (by
          intro hi
          exact hk (by simpa [whichActive, hq]))
    | inr i =>
        exact right.root_eq_zero_of_not_active i (by
          intro hi
          exact hk (by simpa [whichActive, hq]))
  · intro k hk
    cases hq : e.symm k with
    | inl i => exact left.radius_pos i (by simpa [whichActive, hq] using hk)
    | inr i => exact right.radius_pos i (by simpa [whichActive, hq] using hk)
  · intro k hk
    cases hq : e.symm k with
    | inl i => exact left.radius_le_cap i (by simpa [whichActive, hq] using hk)
    | inr i => exact right.radius_le_cap i (by simpa [whichActive, hq] using hk)
  · intro k
    cases hq : e.symm k with
    | inl i => exact left.root_contDiff i
    | inr i => exact right.root_contDiff i
  · intro k
    cases hq : e.symm k with
    | inl i => exact left.root_compact_support i
    | inr i => exact right.root_compact_support i
  · intro k
    cases hq : e.symm k with
    | inl i => exact left.supported i
    | inr i => exact right.supported i
  · intro x
    let f : ℕ ⊕ ℕ → ℝ := Sum.elim
      (fun i ↦ left.root i x ^ 2) (fun i ↦ right.root i x ^ 2)
    have hsum : HasSum f (u x + v x) := HasSum.sum
      (by simpa [f] using left.square_identity x)
      (by simpa [f] using right.square_identity x)
    have hreindexed : HasSum (f ∘ e.symm) (u x + v x) :=
      (e.symm.hasSum_iff).2 hsum
    convert hreindexed using 1
    funext k
    cases hq : e.symm k <;> simp [whichRoot, f, hq]
  · intro x s
    let sLeft : Finset ℕ := s.preimage (fun i ↦ e (Sum.inl i))
      (e.injective.comp Sum.inl_injective).injOn
    let sRight : Finset ℕ := s.preimage (fun i ↦ e (Sum.inr i))
      (e.injective.comp Sum.inr_injective).injOn
    let leftTarget : Set ℕ := {i | i ∈ sLeft ∧ i ∈ left.active ∧
      x ∈ Metric.ball (left.center i) (A * left.radius i)}
    let rightTarget : Set ℕ := {i | i ∈ sRight ∧ i ∈ right.active ∧
      x ∈ Metric.ball (right.center i) (A * right.radius i)}
    let target : Set ℕ := {k | k ∈ s ∧ whichActive (e.symm k) ∧
      x ∈ Metric.ball (whichCenter (e.symm k)) (A * whichRadius (e.symm k))}
    have htarget : target = e '' (Sum.inl '' leftTarget ∪ Sum.inr '' rightTarget) := by
      ext k
      constructor
      · intro hk
        rcases hk with ⟨hks, hka, hkball⟩
        cases hq : e.symm k with
        | inl i =>
            have hek : e (Sum.inl i) = k := by
              rw [← hq]
              exact e.apply_symm_apply k
            refine ⟨Sum.inl i, Or.inl ⟨i, ?_, rfl⟩, hek⟩
            refine ⟨?_, ?_, ?_⟩
            · simpa [sLeft, hek]
            · simpa [whichActive, hq] using hka
            · simpa [whichCenter, whichRadius, hq] using hkball
        | inr i =>
            have hek : e (Sum.inr i) = k := by
              rw [← hq]
              exact e.apply_symm_apply k
            refine ⟨Sum.inr i, Or.inr ⟨i, ?_, rfl⟩, hek⟩
            refine ⟨?_, ?_, ?_⟩
            · simpa [sRight, hek]
            · simpa [whichActive, hq] using hka
            · simpa [whichCenter, whichRadius, hq] using hkball
      · rintro ⟨q, hq, rfl⟩
        rcases hq with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
        · simpa [target, whichActive, whichCenter, whichRadius, sLeft, leftTarget] using hi
        · simpa [target, whichActive, whichCenter, whichRadius, sRight, rightTarget] using hi
    change Set.ncard target ≤ B₁ + B₂
    rw [htarget, e.injective.injOn.ncard_image]
    calc
      Set.ncard (Sum.inl '' leftTarget ∪ Sum.inr '' rightTarget) ≤
          Set.ncard (Sum.inl '' leftTarget) + Set.ncard (Sum.inr '' rightTarget) :=
        Set.ncard_union_le _ _
      _ = Set.ncard leftTarget + Set.ncard rightTarget := by
        rw [Sum.inl_injective.injOn.ncard_image, Sum.inr_injective.injOn.ncard_image]
      _ ≤ B₁ + B₂ := Nat.add_le_add (left.dilated_overlap x sLeft)
        (right.dilated_overlap x sRight)
  · intro k j hj x
    cases hq : e.symm k with
    | inl i =>
        exact (left.scaled_jets i j hj x).trans
          (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (sq_nonneg _))
    | inr i =>
        exact (right.scaled_jets i j hj x).trans
          (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (sq_nonneg _))

/-- A patchwise atom family whose enlarged assigned balls remain inside one enlarged parent
ball. This is the exact geometric datum needed to combine countably many parent patches while
preserving a uniform overlap bound. -/
structure LocalizedEuclideanAtomFamily {n : ℕ} (target : (Fin n → ℝ) → ℝ)
    (A radiusCap C : ℝ) (B : ℕ) (parentCenter : Fin n → ℝ)
    (parentRadius parentDilation : ℝ) where
  atoms : EuclideanAtomFamily target A radiusCap C B
  dilated_ball_subset_parent : ∀ i, i ∈ atoms.active →
    Metric.ball (atoms.center i) (A * atoms.radius i) ⊆
      Metric.ball parentCenter (parentDilation * parentRadius)


/-- Combine two localized families living over the same parent ball.  This is the exact local
assembly used after splitting a parent contribution into its main square and residual sum of
squares. -/
noncomputable def LocalizedEuclideanAtomFamily.add {n : ℕ}
    {u v : (Fin n → ℝ) → ℝ} {A radiusCap C₁ C₂ parentRadius parentDilation : ℝ}
    {B₁ B₂ : ℕ} {parentCenter : Fin n → ℝ}
    (left : LocalizedEuclideanAtomFamily u A radiusCap C₁ B₁
      parentCenter parentRadius parentDilation)
    (right : LocalizedEuclideanAtomFamily v A radiusCap C₂ B₂
      parentCenter parentRadius parentDilation) :
    LocalizedEuclideanAtomFamily (fun x ↦ u x + v x) A radiusCap
      (max C₁ C₂) (B₁ + B₂) parentCenter parentRadius parentDilation where
  atoms := left.atoms.add right.atoms
  dilated_ball_subset_parent := by
    intro k hk
    let e : ℕ ⊕ ℕ ≃ ℕ := Equiv.natSumNatEquivNat
    cases hq : e.symm k with
    | inl i =>
        have hkEq : k = e (Sum.inl i) := by
          calc
            k = e (e.symm k) := (e.apply_symm_apply k).symm
            _ = e (Sum.inl i) := congrArg e hq
        subst k
        have hi : i ∈ left.atoms.active := by
          simpa [EuclideanAtomFamily.add, e] using hk
        simpa [EuclideanAtomFamily.add, e] using
          left.dilated_ball_subset_parent i hi
    | inr i =>
        have hkEq : k = e (Sum.inr i) := by
          calc
            k = e (e.symm k) := (e.apply_symm_apply k).symm
            _ = e (Sum.inr i) := congrArg e hq
        subst k
        have hi : i ∈ right.atoms.active := by
          simpa [EuclideanAtomFamily.add, e] using hk
        simpa [EuclideanAtomFamily.add, e] using
          right.dilated_ball_subset_parent i hi

/-- Package one compactly supported root as a localized atom family.  The assigned ball and its
enlarged-parent containment remain explicit, so this constructor applies to both the positive
root and the main curvature root on a parent patch. -/
noncomputable def singleLocalizedEuclideanAtomFamily {n : ℕ}
    {target root : (Fin n → ℝ) → ℝ} {A radiusCap C r parentRadius parentDilation : ℝ}
    {center parentCenter : Fin n → ℝ}
    (hr : 0 < r) (hrCap : r ≤ radiusCap) (hC : 0 ≤ C)
    (hrootSmooth : ContDiff ℝ 4 root) (hrootCompact : HasCompactSupport root)
    (hrootSupport : Function.support root ⊆ Metric.ball center r)
    (hsquare : ∀ x, target x = root x ^ 2)
    (hjets : ∀ j, j ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ j root x‖ * r ^ j ≤ C * r ^ 2)
    (hlocal : Metric.ball center (A * r) ⊆
      Metric.ball parentCenter (parentDilation * parentRadius)) :
    LocalizedEuclideanAtomFamily target A radiusCap C 1
      parentCenter parentRadius parentDilation where
  atoms := {
    root := fun i ↦ if i = 0 then root else 0
    active := {0}
    center := fun _ ↦ center
    radius := fun _ ↦ r
    root_eq_zero_of_not_active := by
      intro i hi
      have hi0 : i ≠ 0 := by simpa using hi
      simp [hi0]
    radius_pos := by intros; exact hr
    radius_le_cap := by intros; exact hrCap
    root_contDiff := by
      intro i
      by_cases hi : i = 0
      · simp [hi, hrootSmooth]
      · rw [if_neg hi]
        exact contDiff_const
    root_compact_support := by
      intro i
      by_cases hi : i = 0
      · simpa [hi] using hrootCompact
      · simp [hi, HasCompactSupport]
    supported := by
      intro i x hx
      by_cases hi : i = 0
      · simpa [hi] using hrootSupport (by simpa [hi] using hx)
      · simp [hi] at hx
    square_identity := by
      intro x
      convert (hasSum_ite_eq 0 (target x) :
        HasSum (fun i : ℕ ↦ if i = 0 then target x else 0) (target x)) using 1
      funext i
      by_cases hi : i = 0
      · subst i
        simp [hsquare]
      · simp [hi]
    dilated_overlap := by
      intro x s
      have hsubset : {i | i ∈ s ∧ i ∈ ({0} : Set ℕ) ∧
          x ∈ Metric.ball center (A * r)} ⊆ ({0} : Set ℕ) := by
        intro i hi
        exact hi.2.1
      exact (Set.ncard_le_ncard hsubset (Set.finite_singleton 0)).trans (by simp)
    scaled_jets := by
      intro i j hj x
      by_cases hi : i = 0
      · subst i
        simpa using hjets j hj x
      · simp only [if_neg hi]
        change ‖iteratedFDeriv ℝ j (fun _ : Fin n → ℝ ↦ (0 : ℝ)) x‖ * r ^ j ≤
          C * r ^ 2
        rw [iteratedFDeriv_zero_fun]
        simp only [Pi.zero_apply, norm_zero, zero_mul]
        exact mul_nonneg hC (sq_nonneg r) }
  dilated_ball_subset_parent := by
    intro i hi
    simpa using hlocal
/-- A finite set of pairs has cardinality at most the number of first coordinates times a
uniform bound for each first-coordinate fiber. -/
theorem ncard_pair_set_le_mul {S : Set (ℕ × ℕ)} (hS : S.Finite) {P Q : ℕ}
    (hbase : Set.ncard (Prod.fst '' S) ≤ P)
    (hfiber : ∀ i ∈ Prod.fst '' S,
      Set.ncard {p | p ∈ S ∧ p.1 = i} ≤ Q) :
    Set.ncard S ≤ P * Q := by
  classical
  let s : Finset (ℕ × ℕ) := hS.toFinset
  have hsCard : s.card = Set.ncard S := by
    simpa [s] using (Set.ncard_eq_toFinset_card S hS).symm
  have hbaseCard : (s.image Prod.fst).card ≤ P := by
    have hfiniteImage : (Prod.fst '' S).Finite := hS.image Prod.fst
    have himage : hfiniteImage.toFinset = s.image Prod.fst :=
      Set.Finite.toFinset_image Prod.fst hS hfiniteImage
    rw [← himage, ← Set.ncard_eq_toFinset_card (Prod.fst '' S) hfiniteImage]
    exact hbase
  rw [← hsCard, Finset.card_eq_sum_card_image Prod.fst s]
  calc
    ∑ i ∈ s.image Prod.fst, (s.filter (fun p ↦ p.1 = i)).card ≤
        ∑ _i ∈ s.image Prod.fst, Q := by
      gcongr with i hi
      have hiImage : i ∈ Prod.fst '' S := by
        simpa [s] using hi
      have hfiniteFiber : ({p | p ∈ S ∧ p.1 = i} : Set (ℕ × ℕ)).Finite :=
        hS.subset (fun _ hp ↦ hp.1)
      have hset : hfiniteFiber.toFinset = s.filter (fun p ↦ p.1 = i) := by
        ext p
        simp [s]
      rw [← hset, ← Set.ncard_eq_toFinset_card _ hfiniteFiber]
      exact hfiber i hiImage
    _ = (s.image Prod.fst).card * Q := by simp
    _ ≤ P * Q := Nat.mul_le_mul_right Q hbaseCard


/-- Flatten uniformly localized atom families over a quantitative parent cover.  The square
identity is obtained by Tonelli for the nonnegative square series, while the global overlap is
the product of the parent and within-parent budgets. -/
noncomputable def flattenLocalizedEuclideanAtomFamilies {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {parentDilation parentA A C : ℝ} {parentB childB : ℕ}
    (cover : QuantitativeScaleCover u parentDilation parentA parentB)
    (patch : ∀ i, LocalizedEuclideanAtomFamily
      (fun x ↦ cover.cutoff i x ^ 2 * u x) A 1 C childB
      (cover.center i) (cover.radius i) parentDilation)
    (patch_empty_of_parent_inactive : ∀ i, i ∉ cover.active → (patch i).atoms.active = ∅) :
    EuclideanAtomFamily u A 1 C (parentB * childB) where
  root := fun k ↦
    let p := Nat.pairEquiv.symm k
    (patch p.1).atoms.root p.2
  active := {k | let p := Nat.pairEquiv.symm k
    p.1 ∈ cover.active ∧ p.2 ∈ (patch p.1).atoms.active}
  center := fun k ↦
    let p := Nat.pairEquiv.symm k
    (patch p.1).atoms.center p.2
  radius := fun k ↦
    let p := Nat.pairEquiv.symm k
    (patch p.1).atoms.radius p.2
  root_eq_zero_of_not_active := by
    intro k hk
    let p := Nat.pairEquiv.symm k
    have hnot : p.1 ∉ cover.active ∨ p.2 ∉ (patch p.1).atoms.active := by
      by_cases hp : p.1 ∈ cover.active
      · right
        intro hq
        exact hk (by simpa [p] using And.intro hp hq)
      · exact Or.inl hp
    apply (patch p.1).atoms.root_eq_zero_of_not_active
    rcases hnot with hp | hq
    · rw [patch_empty_of_parent_inactive p.1 hp]
      simp
    · exact hq
  radius_pos := by
    intro k hk
    let p := Nat.pairEquiv.symm k
    exact (patch p.1).atoms.radius_pos p.2 (by simpa [p] using hk.2)
  radius_le_cap := by
    intro k hk
    let p := Nat.pairEquiv.symm k
    exact (patch p.1).atoms.radius_le_cap p.2 (by simpa [p] using hk.2)
  root_contDiff := by
    intro k
    exact (patch (Nat.pairEquiv.symm k).1).atoms.root_contDiff
      (Nat.pairEquiv.symm k).2
  root_compact_support := by
    intro k
    exact (patch (Nat.pairEquiv.symm k).1).atoms.root_compact_support
      (Nat.pairEquiv.symm k).2
  supported := by
    intro k
    exact (patch (Nat.pairEquiv.symm k).1).atoms.supported
      (Nat.pairEquiv.symm k).2
  square_identity := by
    intro x
    let f : ℕ × ℕ → ℝ := fun p ↦ (patch p.1).atoms.root p.2 x ^ 2
    have hinner : ∀ i, HasSum (fun j ↦ f (i, j)) (cover.cutoff i x ^ 2 * u x) := by
      intro i
      simpa [f] using (patch i).atoms.square_identity x
    have houter : HasSum (fun i ↦ cover.cutoff i x ^ 2 * u x) (u x) := by
      by_cases hux : u x = 0
      · simp [hux]
      · have hxSupport : x ∈ Function.support u := by simpa [Function.mem_support]
        have hscale : 0 < nonnegativeJetScale u x :=
          support_subset_nonnegativeJetScale_pos hu hxSupport
        have hcutSummable : Summable (fun i ↦ cover.cutoff i x ^ 2) := by
          apply summable_of_finite_support
          exact (cover.point_finite x).subset (by
            intro i hi
            simpa [Function.mem_support] using hi)
        have hcut : HasSum (fun i ↦ cover.cutoff i x ^ 2) 1 := by
          have h := hcutSummable.hasSum
          rw [cover.square_partition x hscale] at h
          exact h
        simpa [mul_comm] using hcut.mul_right (u x)
    have hprodSummable : Summable f := by
      rw [summable_prod_of_nonneg (fun p ↦ sq_nonneg ((patch p.1).atoms.root p.2 x))]
      refine ⟨fun i ↦ (hinner i).summable, ?_⟩
      convert houter.summable using 1
      funext i
      exact (hinner i).tsum_eq
    have hprod : HasSum f (u x) := by
      have h := hprodSummable.hasSum
      have htsum : ∑' p, f p = u x := by
        rw [hprodSummable.tsum_prod' (fun i ↦ (hinner i).summable)]
        exact (tsum_congr fun i ↦ (hinner i).tsum_eq).trans houter.tsum_eq
      rwa [htsum] at h
    have hreindexed : HasSum (f ∘ Nat.pairEquiv.symm) (u x) :=
      (Nat.pairEquiv.symm.hasSum_iff).2 hprod
    simpa [f, Function.comp_def] using hreindexed
  dilated_overlap := by
    intro x s
    let pairTarget : Set (ℕ × ℕ) := {p |
      Nat.pairEquiv p ∈ s ∧ p.1 ∈ cover.active ∧
        p.2 ∈ (patch p.1).atoms.active ∧
        x ∈ Metric.ball ((patch p.1).atoms.center p.2)
          (A * (patch p.1).atoms.radius p.2)}
    have hpairFinite : pairTarget.Finite := by
      have hpre : (Nat.pairEquiv ⁻¹' (s : Set ℕ)).Finite :=
        s.finite_toSet.preimage Nat.pairEquiv.injective.injOn
      exact hpre.subset (fun _ hp ↦ hp.1)
    have hbase : Set.ncard (Prod.fst '' pairTarget) ≤ parentB := by
      let parentIndices : Finset ℕ := s.image (fun k ↦ (Nat.pairEquiv.symm k).1)
      let parentTarget : Set ℕ := {i | i ∈ parentIndices ∧ i ∈ cover.active ∧
        x ∈ Metric.ball (cover.center i) (parentDilation * cover.radius i)}
      have hsubset : Prod.fst '' pairTarget ⊆ parentTarget := by
        rintro i ⟨p, hp, rfl⟩
        refine ⟨?_, hp.2.1, ?_⟩
        · simp only [Nat.pairEquiv_symm_apply, Finset.mem_image, parentIndices]
          exact ⟨Nat.pairEquiv p, hp.1,
            congr_arg Prod.fst (Nat.pairEquiv.symm_apply_apply p)⟩
        · exact (patch p.1).dilated_ball_subset_parent p.2 hp.2.2.1 hp.2.2.2
      have hparentFinite : parentTarget.Finite :=
        parentIndices.finite_toSet.subset (fun _ hi ↦ hi.1)
      exact (Set.ncard_le_ncard hsubset hparentFinite).trans
        (cover.overlap x parentIndices)
    have hfiber : ∀ i ∈ Prod.fst '' pairTarget,
        Set.ncard {p | p ∈ pairTarget ∧ p.1 = i} ≤ childB := by
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
      have hchildSet : {q | q ∈ children ∧ q ∈ (patch i).atoms.active ∧
          x ∈ Metric.ball ((patch i).atoms.center q) (A * (patch i).atoms.radius q)} =
          Prod.snd '' fiber := by
        ext q
        constructor
        · intro hq
          simpa [children] using hq.1
        · rintro ⟨p, hp, rfl⟩
          have hpi : p.1 = i := hp.2
          have hdata := hp.1
          subst i
          refine ⟨?_, hdata.2.2.1, hdata.2.2.2⟩
          simp only [children, Set.Finite.mem_toFinset, Set.mem_image Prod.snd fiber]
          exact ⟨p, hp, rfl⟩
      have hwithin := (patch i).atoms.dilated_overlap x children
      rw [hchildSet] at hwithin
      rw [← hsndInj.ncard_image]
      exact hwithin
    have hpairCard : Set.ncard pairTarget ≤ parentB * childB :=
      ncard_pair_set_le_mul hpairFinite hbase hfiber
    let natTarget : Set ℕ := {k | k ∈ s ∧
      (let p := Nat.pairEquiv.symm k
       p.1 ∈ cover.active ∧ p.2 ∈ (patch p.1).atoms.active) ∧
      x ∈ Metric.ball
        ((patch (Nat.pairEquiv.symm k).1).atoms.center (Nat.pairEquiv.symm k).2)
        (A * (patch (Nat.pairEquiv.symm k).1).atoms.radius (Nat.pairEquiv.symm k).2)}
    have hnatImage : Nat.pairEquiv '' pairTarget = natTarget := by
      ext k
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hinv := Nat.pairEquiv.symm_apply_apply p
        change Nat.pairEquiv p ∈ s ∧
          ((Nat.pairEquiv.symm (Nat.pairEquiv p)).1 ∈ cover.active ∧
            (Nat.pairEquiv.symm (Nat.pairEquiv p)).2 ∈
              (patch (Nat.pairEquiv.symm (Nat.pairEquiv p)).1).atoms.active) ∧
          x ∈ Metric.ball
            ((patch (Nat.pairEquiv.symm (Nat.pairEquiv p)).1).atoms.center
              (Nat.pairEquiv.symm (Nat.pairEquiv p)).2)
            (A * (patch (Nat.pairEquiv.symm (Nat.pairEquiv p)).1).atoms.radius
              (Nat.pairEquiv.symm (Nat.pairEquiv p)).2)
        rw [hinv]
        exact ⟨hp.1, ⟨hp.2.1, hp.2.2.1⟩, hp.2.2.2⟩
      · intro hk
        change k ∈ s ∧
          ((Nat.pairEquiv.symm k).1 ∈ cover.active ∧
            (Nat.pairEquiv.symm k).2 ∈ (patch (Nat.pairEquiv.symm k).1).atoms.active) ∧
          x ∈ Metric.ball
            ((patch (Nat.pairEquiv.symm k).1).atoms.center (Nat.pairEquiv.symm k).2)
            (A * (patch (Nat.pairEquiv.symm k).1).atoms.radius
              (Nat.pairEquiv.symm k).2) at hk
        refine ⟨Nat.pairEquiv.symm k, ?_, Nat.pairEquiv.apply_symm_apply k⟩
        refine ⟨?_, hk.2.1.1, hk.2.1.2, hk.2.2⟩
        simpa only [Nat.pairEquiv.apply_symm_apply] using hk.1
    have hcardEq : Set.ncard natTarget = Set.ncard pairTarget := by
      rw [← hnatImage, Nat.pairEquiv.injective.injOn.ncard_image]
    change Set.ncard natTarget ≤ parentB * childB
    rw [hcardEq]
    exact hpairCard
  scaled_jets := by
    intro k j hj x
    exact (patch (Nat.pairEquiv.symm k).1).atoms.scaled_jets
      (Nat.pairEquiv.symm k).2 j hj x
/-- The identically zero function has the empty active atom family. -/
def zeroEuclideanAtomFamily {n : ℕ} (A radiusCap C : ℝ) (hC : 0 ≤ C) :
    EuclideanAtomFamily (fun _ : Fin n → ℝ ↦ 0) A radiusCap C 0 where
  root := fun _ _ ↦ 0
  active := ∅
  center := fun _ ↦ 0
  radius := fun _ ↦ radiusCap
  root_eq_zero_of_not_active := by
    intro i hi
    rfl
  radius_pos := by
    intro i hi
    simp at hi
  radius_le_cap := by
    intro i hi
    simp at hi
  root_contDiff := by
    intro i
    exact contDiff_const
  root_compact_support := by
    intro i
    simp [HasCompactSupport]
  supported := by
    intro i x hx
    simp [Function.support] at hx
  square_identity := by
    intro x
    convert (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0) using 1
    funext i
    norm_num
  dilated_overlap := by simp
  scaled_jets := by
    intro i j hj x
    rw [iteratedFDeriv_zero_fun]
    simpa using mul_nonneg hC (sq_nonneg radiusCap)

/-- Enlarge the advertised overlap budget without changing an atom family. -/
def EuclideanAtomFamily.increaseOverlapBudget {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {A radiusCap C : ℝ} {B B' : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) (hB : B ≤ B') :
    EuclideanAtomFamily u A radiusCap C B' where
  root := atoms.root
  active := atoms.active
  center := atoms.center
  radius := atoms.radius
  root_eq_zero_of_not_active := atoms.root_eq_zero_of_not_active
  radius_pos := atoms.radius_pos
  radius_le_cap := atoms.radius_le_cap
  root_contDiff := atoms.root_contDiff
  root_compact_support := atoms.root_compact_support
  supported := atoms.supported
  square_identity := atoms.square_identity
  dilated_overlap := fun x s ↦ (atoms.dilated_overlap x s).trans hB
  scaled_jets := atoms.scaled_jets

/-- The zero target has an empty localized family over any advertised parent ball. -/
def zeroLocalizedEuclideanAtomFamily {n : ℕ}
    (A radiusCap C : ℝ) (B : ℕ) (hC : 0 ≤ C)
    (parentCenter : Fin n → ℝ) (parentRadius parentDilation : ℝ) :
    LocalizedEuclideanAtomFamily (fun _ : Fin n → ℝ ↦ 0)
      A radiusCap C B parentCenter parentRadius parentDilation where
  atoms := (zeroEuclideanAtomFamily A radiusCap C hC).increaseOverlapBudget
    (Nat.zero_le B)
  dilated_ball_subset_parent := by
    intro i hi
    simp [EuclideanAtomFamily.increaseOverlapBudget, zeroEuclideanAtomFamily] at hi

/-- Enlarge the scale-invariant jet constant without changing an atom family. -/
def EuclideanAtomFamily.increaseJetConstant {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {A radiusCap C C' : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) (hC : C ≤ C') :
    EuclideanAtomFamily u A radiusCap C' B where
  root := atoms.root
  active := atoms.active
  center := atoms.center
  radius := atoms.radius
  root_eq_zero_of_not_active := atoms.root_eq_zero_of_not_active
  radius_pos := atoms.radius_pos
  radius_le_cap := atoms.radius_le_cap
  root_contDiff := atoms.root_contDiff
  root_compact_support := atoms.root_compact_support
  supported := atoms.supported
  square_identity := atoms.square_identity
  dilated_overlap := atoms.dilated_overlap
  scaled_jets := by
    intro i j hj x
    exact (atoms.scaled_jets i j hj x).trans
      (mul_le_mul_of_nonneg_right hC (sq_nonneg _))

/-- Enlarge the jet constant of a localized family, preserving its parent-ball containment. -/
def LocalizedEuclideanAtomFamily.increaseJetConstant {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C C' parentRadius parentDilation : ℝ}
    {B : ℕ} {parentCenter : Fin n → ℝ}
    (atoms : LocalizedEuclideanAtomFamily u A radiusCap C B
      parentCenter parentRadius parentDilation) (hC : C ≤ C') :
    LocalizedEuclideanAtomFamily u A radiusCap C' B
      parentCenter parentRadius parentDilation where
  atoms := atoms.atoms.increaseJetConstant hC
  dilated_ball_subset_parent := atoms.dilated_ball_subset_parent

/-- Enlarge the overlap budget of a localized family, preserving its parent-ball containment. -/
def LocalizedEuclideanAtomFamily.increaseOverlapBudget {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C parentRadius parentDilation : ℝ}
    {B B' : ℕ} {parentCenter : Fin n → ℝ}
    (atoms : LocalizedEuclideanAtomFamily u A radiusCap C B
      parentCenter parentRadius parentDilation) (hB : B ≤ B') :
    LocalizedEuclideanAtomFamily u A radiusCap C B'
      parentCenter parentRadius parentDilation where
  atoms := atoms.atoms.increaseOverlapBudget hB
  dilated_ball_subset_parent := atoms.dilated_ball_subset_parent

/-- Multiplying the represented function by a nonnegative constant rescales every root by its
square root, without changing any support, radius, or overlap data. -/
noncomputable def EuclideanAtomFamily.constScale {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {A radiusCap C : ℝ} {B : ℕ} (atoms : EuclideanAtomFamily u A radiusCap C B)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    EuclideanAtomFamily (fun x ↦ lambda * u x) A radiusCap (Real.sqrt lambda * C) B where
  root := fun i ↦ Real.sqrt lambda • atoms.root i
  active := atoms.active
  center := atoms.center
  radius := atoms.radius
  root_eq_zero_of_not_active := by
    intro i hi
    rw [atoms.root_eq_zero_of_not_active i hi]
    simp
  radius_pos := atoms.radius_pos
  radius_le_cap := atoms.radius_le_cap
  root_contDiff := by
    intro i
    exact (atoms.root_contDiff i).const_smul (Real.sqrt lambda)
  root_compact_support := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (atoms.root_compact_support i).smul_left (f := fun _ ↦ Real.sqrt lambda)
  supported := by
    intro i x hx
    apply atoms.supported i
    intro hzero
    apply hx
    simp [hzero]
  square_identity := by
    intro x
    have hsum := (atoms.square_identity x).mul_left lambda
    convert hsum using 1
    · funext i
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt hlambda]
  dilated_overlap := atoms.dilated_overlap
  scaled_jets := by
    intro i j hj x
    have hsmooth : ContDiffAt ℝ j (atoms.root i) x :=
      ((atoms.root_contDiff i).of_le (by exact_mod_cast hj)).contDiffAt
    rw [iteratedFDeriv_const_smul_apply hsmooth, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg lambda)]
    calc
      Real.sqrt lambda * ‖iteratedFDeriv ℝ j (atoms.root i) x‖ * atoms.radius i ^ j =
          Real.sqrt lambda *
            (‖iteratedFDeriv ℝ j (atoms.root i) x‖ * atoms.radius i ^ j) := by ring
      _ ≤ Real.sqrt lambda * (C * atoms.radius i ^ 2) :=
        mul_le_mul_of_nonneg_left (atoms.scaled_jets i j hj x) (Real.sqrt_nonneg lambda)
      _ = (Real.sqrt lambda * C) * atoms.radius i ^ 2 := by ring

/-- Translate every atom and its assigned center by the same vector.  All scale-invariant fields
are unchanged. -/
noncomputable def EuclideanAtomFamily.translate {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {A radiusCap C : ℝ} {B : ℕ} (atoms : EuclideanAtomFamily u A radiusCap C B)
    (c : Fin n → ℝ) :
    EuclideanAtomFamily (fun x ↦ u (x - c)) A radiusCap C B where
  root := fun i x ↦ atoms.root i (x - c)
  active := atoms.active
  center := fun i ↦ c + atoms.center i
  radius := atoms.radius
  root_eq_zero_of_not_active := by
    intro i hi
    rw [atoms.root_eq_zero_of_not_active i hi]
    rfl
  radius_pos := atoms.radius_pos
  radius_le_cap := atoms.radius_le_cap
  root_contDiff := by
    intro i
    exact (atoms.root_contDiff i).comp (by fun_prop)
  root_compact_support := by
    intro i
    simpa [Function.comp_def] using
      (atoms.root_compact_support i).comp_homeomorph (Homeomorph.subRight c)
  supported := by
    intro i x hx
    have hold := atoms.supported i hx
    rw [Metric.mem_ball] at hold ⊢
    have hdist : dist x (c + atoms.center i) = dist (x - c) (atoms.center i) := by
      simp only [dist_eq_norm]
      congr 1
      abel
    rwa [hdist]
  square_identity := by
    intro x
    exact atoms.square_identity (x - c)
  dilated_overlap := by
    intro x s
    have hset : {i | i ∈ s ∧ i ∈ atoms.active ∧
          x ∈ Metric.ball (c + atoms.center i) (A * atoms.radius i)} =
        {i | i ∈ s ∧ i ∈ atoms.active ∧
          x - c ∈ Metric.ball (atoms.center i) (A * atoms.radius i)} := by
      ext i
      simp only [Set.mem_setOf_eq, Metric.mem_ball]
      have hdist : dist x (c + atoms.center i) = dist (x - c) (atoms.center i) := by
        simp only [dist_eq_norm]
        congr 1
        abel
      rw [hdist]
    rw [hset]
    exact atoms.dilated_overlap (x - c) s
  scaled_jets := by
    intro i j hj x
    have hderiv : iteratedFDeriv ℝ j (fun y ↦ atoms.root i (y - c)) x =
        iteratedFDeriv ℝ j (atoms.root i) (x - c) := by
      simpa [sub_eq_add_neg, add_comm] using
        iteratedFDeriv_comp_add_left (𝕜 := ℝ) j (-c) x (f := atoms.root i)
    rw [hderiv]
    exact atoms.scaled_jets i j hj (x - c)
/-- Pulling a unit-cap atom family back through the dilation `x ↦ rho⁻¹ • x` gives an
atom family with prescribed radius cap `rho`.  The overlap budget is unchanged and the
scale-invariant jet constant changes by the expected factor `rho⁻²`. -/
noncomputable def EuclideanAtomFamily.contractRadius {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A C rho : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily (fun x ↦ u (rho • x)) A 1 C B)
    (hrho : 0 < rho) :
    EuclideanAtomFamily u A rho (C / rho ^ 2) B where
  root := fun i x ↦ atoms.root i (rho⁻¹ • x)
  active := atoms.active
  center := fun i ↦ rho • atoms.center i
  radius := fun i ↦ rho * atoms.radius i
  root_eq_zero_of_not_active := by
    intro i hi
    rw [atoms.root_eq_zero_of_not_active i hi]
    rfl
  radius_pos := by
    intro i hi
    exact mul_pos hrho (atoms.radius_pos i hi)
  radius_le_cap := by
    intro i hi
    have := atoms.radius_le_cap i hi
    nlinarith
  root_contDiff := by
    intro i
    exact (atoms.root_contDiff i).comp (by fun_prop)
  root_compact_support := by
    intro i
    exact (atoms.root_compact_support i).comp_smul (inv_ne_zero hrho.ne')
  supported := by
    intro i x hx
    have hold := atoms.supported i hx
    have hne : rho ≠ 0 := hrho.ne'
    have hxscale : x = rho • (rho⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    have hdist : dist x (rho • atoms.center i) =
        rho * dist (rho⁻¹ • x) (atoms.center i) := by
      calc
        dist x (rho • atoms.center i) =
            dist (rho • (rho⁻¹ • x)) (rho • atoms.center i) := by rw [← hxscale]
        _ = ‖rho‖ * dist (rho⁻¹ • x) (atoms.center i) :=
          dist_smul₀ rho (rho⁻¹ • x) (atoms.center i)
        _ = rho * dist (rho⁻¹ • x) (atoms.center i) := by
          rw [Real.norm_of_nonneg hrho.le]
    rw [Metric.mem_ball] at hold ⊢
    rw [hdist]
    exact (mul_lt_mul_iff_right₀ hrho).mpr hold
  square_identity := by
    intro x
    have hsum := atoms.square_identity (rho⁻¹ • x)
    have hne : rho ≠ 0 := hrho.ne'
    have harg : rho • (rho⁻¹ • x) = x := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    simpa only [harg] using hsum
  dilated_overlap := by
    intro x s
    have hne : rho ≠ 0 := hrho.ne'
    have hxscale : x = rho • (rho⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    have hset : {i | i ∈ s ∧ i ∈ atoms.active ∧
          x ∈ Metric.ball (rho • atoms.center i) (A * (rho * atoms.radius i))} =
        {i | i ∈ s ∧ i ∈ atoms.active ∧
          rho⁻¹ • x ∈ Metric.ball (atoms.center i) (A * atoms.radius i)} := by
      ext i
      simp only [Set.mem_setOf_eq, Metric.mem_ball]
      have hdist : dist x (rho • atoms.center i) =
          rho * dist (rho⁻¹ • x) (atoms.center i) := by
        calc
          dist x (rho • atoms.center i) =
              dist (rho • (rho⁻¹ • x)) (rho • atoms.center i) := by rw [← hxscale]
          _ = ‖rho‖ * dist (rho⁻¹ • x) (atoms.center i) :=
            dist_smul₀ rho (rho⁻¹ • x) (atoms.center i)
          _ = rho * dist (rho⁻¹ • x) (atoms.center i) := by
            rw [Real.norm_of_nonneg hrho.le]
      rw [hdist, show A * (rho * atoms.radius i) =
        rho * (A * atoms.radius i) by ring]
      constructor
      · rintro ⟨his, hia, hball⟩
        exact ⟨his, hia, (mul_lt_mul_iff_right₀ hrho).mp hball⟩
      · rintro ⟨his, hia, hball⟩
        exact ⟨his, hia, (mul_lt_mul_iff_right₀ hrho).mpr hball⟩
    rw [hset]
    exact atoms.dilated_overlap (rho⁻¹ • x) s
  scaled_jets := by
    intro i j hj x
    let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
      rho⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ)
    by_cases hia : i ∈ atoms.active
    · have hcomp :
          iteratedFDeriv ℝ j (atoms.root i ∘ L) x =
            (iteratedFDeriv ℝ j (atoms.root i) (L x)).compContinuousLinearMap
              (fun _ ↦ L) :=
        L.iteratedFDeriv_comp_right (atoms.root_contDiff i) x (by exact_mod_cast hj)
      change ‖iteratedFDeriv ℝ j (atoms.root i ∘ L) x‖ *
          (rho * atoms.radius i) ^ j ≤
        (C / rho ^ 2) * (rho * atoms.radius i) ^ 2
      rw [hcomp]
      have hnormL : ‖L‖ ≤ rho⁻¹ := by
        dsimp only [L]
        calc
          ‖rho⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
              ‖rho⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ := by
            exact norm_smul_le (rho⁻¹ : ℝ) (ContinuousLinearMap.id ℝ (Fin n → ℝ))
          _ ≤ rho⁻¹ * 1 := by
            rw [Real.norm_of_nonneg (inv_nonneg.mpr hrho.le)]
            gcongr
            exact ContinuousLinearMap.norm_id_le
          _ = rho⁻¹ := mul_one _
      have hprod : (∏ _ : Fin j, ‖L‖) ≤ (rho⁻¹) ^ j := by
        calc
          (∏ _ : Fin j, ‖L‖) ≤ ∏ _ : Fin j, rho⁻¹ :=
            Finset.prod_le_prod (fun _ _ ↦ norm_nonneg L) (fun _ _ ↦ hnormL)
          _ = (rho⁻¹) ^ j := by simp
      have hradius : 0 < atoms.radius i := atoms.radius_pos i hia
      have hscaled_nonneg : 0 ≤ (rho * atoms.radius i) ^ j :=
        pow_nonneg (mul_nonneg hrho.le hradius.le) j
      have hinvpow : (rho⁻¹) ^ j * rho ^ j = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hrho.ne', one_pow]
      calc
        ‖(iteratedFDeriv ℝ j (atoms.root i) (L x)).compContinuousLinearMap
            (fun _ ↦ L)‖ * (rho * atoms.radius i) ^ j
            ≤ (‖iteratedFDeriv ℝ j (atoms.root i) (L x)‖ *
                ∏ _ : Fin j, ‖L‖) * (rho * atoms.radius i) ^ j :=
              mul_le_mul_of_nonneg_right
                (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
                hscaled_nonneg
        _ ≤ (‖iteratedFDeriv ℝ j (atoms.root i) (L x)‖ * (rho⁻¹) ^ j) *
            (rho * atoms.radius i) ^ j :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)) hscaled_nonneg
        _ = ‖iteratedFDeriv ℝ j (atoms.root i) (L x)‖ * atoms.radius i ^ j := by
          rw [mul_pow]
          calc
            (‖iteratedFDeriv ℝ j (atoms.root i) (L x)‖ * (rho⁻¹) ^ j) *
                (rho ^ j * atoms.radius i ^ j) =
              ‖iteratedFDeriv ℝ j (atoms.root i) (L x)‖ *
                ((rho⁻¹) ^ j * rho ^ j) * atoms.radius i ^ j := by ring
            _ = _ := by rw [hinvpow]; ring
        _ ≤ C * atoms.radius i ^ 2 := atoms.scaled_jets i j hj (L x)
        _ = (C / rho ^ 2) * (rho * atoms.radius i) ^ 2 := by
          field_simp [hrho.ne']
    · have hzero := atoms.root_eq_zero_of_not_active i hia
      change ‖iteratedFDeriv ℝ j (atoms.root i ∘ L) x‖ *
          (rho * atoms.radius i) ^ j ≤
        (C / rho ^ 2) * (rho * atoms.radius i) ^ 2
      have hfun : (atoms.root i ∘ L) = 0 := by
        rw [hzero]
        rfl
      rw [hfun]
      change ‖iteratedFDeriv ℝ j (fun _ : Fin n → ℝ ↦ (0 : ℝ)) x‖ *
          (rho * atoms.radius i) ^ j ≤
        (C / rho ^ 2) * (rho * atoms.radius i) ^ 2
      rw [iteratedFDeriv_zero_fun]
      simp only [Pi.zero_apply, norm_zero, zero_mul]
      have hold := atoms.scaled_jets i 0 (by norm_num) (L x)
      rw [hzero, norm_iteratedFDeriv_zero] at hold
      simp only [Pi.zero_apply, norm_zero, zero_mul] at hold
      calc
        0 ≤ C * atoms.radius i ^ 2 := hold
        _ = (C / rho ^ 2) * (rho * atoms.radius i) ^ 2 := by
          field_simp [hrho.ne']

/-- Enlarge only the advertised radius cap; the roots, assigned balls, overlap and jets are
unchanged. -/
def EuclideanAtomFamily.increaseRadiusCap {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {A radiusCap C : ℝ} {B : ℕ} (atoms : EuclideanAtomFamily u A radiusCap C B)
    {newCap : ℝ} (hcap : radiusCap ≤ newCap) :
    EuclideanAtomFamily u A newCap C B where
  root := atoms.root
  active := atoms.active
  center := atoms.center
  radius := atoms.radius
  root_eq_zero_of_not_active := atoms.root_eq_zero_of_not_active
  radius_pos := atoms.radius_pos
  radius_le_cap := fun i hi ↦ (atoms.radius_le_cap i hi).trans hcap
  root_contDiff := atoms.root_contDiff
  root_compact_support := atoms.root_compact_support
  supported := atoms.supported
  square_identity := atoms.square_identity
  dilated_overlap := atoms.dilated_overlap
  scaled_jets := atoms.scaled_jets

/-- Undo the fourth-order normalization on a parent patch.  The construction is transparent in
the active set and geometry: roots are multiplied by `R²`, while centers and
radii are dilated by `R` and translated by `c`.  The scale-invariant jet and overlap constants
are exactly preserved. -/
noncomputable def EuclideanAtomFamily.affineRescaleUnitCap {n : ℕ}
    {v : (Fin n → ℝ) → ℝ} {A C R : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily v A 1 C B) (hR : 0 < R) (c : Fin n → ℝ) :
    EuclideanAtomFamily
      (fun x ↦ R ^ 4 * v (R⁻¹ • (x - c))) A R C B where
  root := fun i x ↦ R ^ 2 * atoms.root i (R⁻¹ • (x - c))
  active := atoms.active
  center := fun i ↦ c + R • atoms.center i
  radius := fun i ↦ R * atoms.radius i
  root_eq_zero_of_not_active := by
    intro i hi
    rw [atoms.root_eq_zero_of_not_active i hi]
    ext x
    simp
  radius_pos := by
    intro i hi
    exact mul_pos hR (atoms.radius_pos i hi)
  radius_le_cap := by
    intro i hi
    have hir := atoms.radius_le_cap i hi
    nlinarith
  root_contDiff := by
    intro i
    exact contDiff_const.mul ((atoms.root_contDiff i).comp (by fun_prop))
  root_compact_support := by
    intro i
    have hscaled : HasCompactSupport (fun y ↦ atoms.root i (R⁻¹ • y)) :=
      (atoms.root_compact_support i).comp_smul (inv_ne_zero hR.ne')
    have htranslated : HasCompactSupport (fun x ↦ atoms.root i (R⁻¹ • (x - c))) := by
      simpa [Function.comp_def] using hscaled.comp_homeomorph (Homeomorph.subRight c)
    exact htranslated.mul_left
  supported := by
    intro i x hx
    have hinner : R⁻¹ • (x - c) ∈ Function.support (atoms.root i) := by
      intro hzero
      apply hx
      simp [hzero]
    have hold := atoms.supported i hinner
    rw [Metric.mem_ball] at hold ⊢
    have hdist : dist x (c + R • atoms.center i) =
        R * dist (R⁻¹ • (x - c)) (atoms.center i) := by
      calc
        dist x (c + R • atoms.center i) =
            ‖R • (R⁻¹ • (x - c) - atoms.center i)‖ := by
          rw [dist_eq_norm]
          congr 1
          rw [smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
          abel
        _ = R * ‖R⁻¹ • (x - c) - atoms.center i‖ := by
          rw [norm_smul, Real.norm_of_nonneg hR.le]
        _ = R * dist (R⁻¹ • (x - c)) (atoms.center i) := by
          rw [dist_eq_norm]
    rw [hdist]
    exact (mul_lt_mul_iff_right₀ hR).2 hold
  square_identity := by
    intro x
    have hsum := (atoms.square_identity (R⁻¹ • (x - c))).mul_left (R ^ 4)
    convert hsum using 1
    funext i
    ring
  dilated_overlap := by
    intro x s
    have hset : {i | i ∈ s ∧ i ∈ atoms.active ∧
          x ∈ Metric.ball (c + R • atoms.center i) (A * (R * atoms.radius i))} =
        {i | i ∈ s ∧ i ∈ atoms.active ∧
          R⁻¹ • (x - c) ∈ Metric.ball (atoms.center i) (A * atoms.radius i)} := by
      ext i
      simp only [Set.mem_setOf_eq, Metric.mem_ball]
      have hdist : dist x (c + R • atoms.center i) =
          R * dist (R⁻¹ • (x - c)) (atoms.center i) := by
        calc
          dist x (c + R • atoms.center i) =
              ‖R • (R⁻¹ • (x - c) - atoms.center i)‖ := by
            rw [dist_eq_norm]
            congr 1
            rw [smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
            abel
          _ = R * ‖R⁻¹ • (x - c) - atoms.center i‖ := by
            rw [norm_smul, Real.norm_of_nonneg hR.le]
          _ = R * dist (R⁻¹ • (x - c)) (atoms.center i) := by
            rw [dist_eq_norm]
      rw [hdist, show A * (R * atoms.radius i) =
        R * (A * atoms.radius i) by ring]
      constructor
      · rintro ⟨his, hia, hball⟩
        exact ⟨his, hia, (mul_lt_mul_iff_right₀ hR).1 hball⟩
      · rintro ⟨his, hia, hball⟩
        exact ⟨his, hia, (mul_lt_mul_iff_right₀ hR).2 hball⟩
    rw [hset]
    exact atoms.dilated_overlap (R⁻¹ • (x - c)) s
  scaled_jets := by
    intro i j hj x
    let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
      R⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ)
    let g : (Fin n → ℝ) → ℝ := atoms.root i ∘ L
    have hg : ContDiff ℝ 4 g := (atoms.root_contDiff i).comp L.contDiff
    have htranslate :
        iteratedFDeriv ℝ j (fun y ↦ R ^ 2 * g (y - c)) x =
          iteratedFDeriv ℝ j (fun y ↦ R ^ 2 * g y) (x - c) := by
      simpa [sub_eq_add_neg, add_comm] using
        iteratedFDeriv_comp_add_left (𝕜 := ℝ) j (-c) x
          (f := fun y ↦ R ^ 2 * g y)
    have hscalar :
        iteratedFDeriv ℝ j (fun y ↦ R ^ 2 * g y) (x - c) =
          R ^ 2 • iteratedFDeriv ℝ j g (x - c) := by
      change iteratedFDeriv ℝ j (R ^ 2 • g) (x - c) =
        R ^ 2 • iteratedFDeriv ℝ j g (x - c)
      exact iteratedFDeriv_const_smul_apply
        ((hg.of_le (by exact_mod_cast hj)).contDiffAt)
    have hcomp :
        iteratedFDeriv ℝ j g (x - c) =
          (iteratedFDeriv ℝ j (atoms.root i) (L (x - c))).compContinuousLinearMap
            (fun _ ↦ L) := by
      exact L.iteratedFDeriv_comp_right (atoms.root_contDiff i) (x - c)
        (by exact_mod_cast hj)
    have hnormL : ‖L‖ ≤ R⁻¹ := by
      dsimp only [L]
      calc
        ‖R⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
            ‖R⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ :=
          norm_smul_le (R⁻¹ : ℝ) (ContinuousLinearMap.id ℝ (Fin n → ℝ))
        _ ≤ R⁻¹ * 1 := by
          rw [Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
          gcongr
          exact ContinuousLinearMap.norm_id_le
        _ = R⁻¹ := mul_one _
    have hprod : (∏ _ : Fin j, ‖L‖) ≤ (R⁻¹) ^ j := by
      calc
        (∏ _ : Fin j, ‖L‖) ≤ ∏ _ : Fin j, R⁻¹ :=
          Finset.prod_le_prod (fun _ _ ↦ norm_nonneg L) (fun _ _ ↦ hnormL)
        _ = (R⁻¹) ^ j := by simp
    have hinvpow : (R⁻¹) ^ j * R ^ j = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hR.ne', one_pow]
    change ‖iteratedFDeriv ℝ j (fun y ↦ R ^ 2 * g (y - c)) x‖ *
      (R * atoms.radius i) ^ j ≤ C * (R * atoms.radius i) ^ 2
    by_cases hia : i ∈ atoms.active
    · have hradius : 0 < atoms.radius i := atoms.radius_pos i hia
      have hphysical : 0 ≤ (R * atoms.radius i) ^ j :=
        pow_nonneg (mul_nonneg hR.le hradius.le) j
      rw [htranslate, hscalar, hcomp, norm_smul,
        Real.norm_of_nonneg (sq_nonneg R)]
      calc
        R ^ 2 *
            ‖(iteratedFDeriv ℝ j (atoms.root i) (L (x - c))).compContinuousLinearMap
              (fun _ ↦ L)‖ * (R * atoms.radius i) ^ j
            ≤ R ^ 2 *
                (‖iteratedFDeriv ℝ j (atoms.root i) (L (x - c))‖ *
                  ∏ _ : Fin j, ‖L‖) * (R * atoms.radius i) ^ j := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left
                  (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
                  (sq_nonneg R)) hphysical
        _ ≤ R ^ 2 *
                (‖iteratedFDeriv ℝ j (atoms.root i) (L (x - c))‖ * (R⁻¹) ^ j) *
              (R * atoms.radius i) ^ j := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)) (sq_nonneg R))
              hphysical
        _ = R ^ 2 *
            (‖iteratedFDeriv ℝ j (atoms.root i) (L (x - c))‖ * atoms.radius i ^ j) := by
          rw [mul_pow]
          calc
            R ^ 2 *
                  (‖iteratedFDeriv ℝ j (atoms.root i) (L (x - c))‖ * (R⁻¹) ^ j) *
                (R ^ j * atoms.radius i ^ j) =
              R ^ 2 * ‖iteratedFDeriv ℝ j (atoms.root i) (L (x - c))‖ *
                ((R⁻¹) ^ j * R ^ j) * atoms.radius i ^ j := by ring
            _ = _ := by rw [hinvpow]; ring
        _ ≤ R ^ 2 * (C * atoms.radius i ^ 2) :=
          mul_le_mul_of_nonneg_left
            (atoms.scaled_jets i j hj (L (x - c))) (sq_nonneg R)
        _ = C * (R * atoms.radius i) ^ 2 := by ring
    · have hzero := atoms.root_eq_zero_of_not_active i hia
      have hfun : (fun y ↦ R ^ 2 * g (y - c)) = 0 := by
        funext y
        simp [g, hzero]
      rw [hfun]
      change ‖iteratedFDeriv ℝ j (fun _ : Fin n → ℝ ↦ (0 : ℝ)) x‖ *
        (R * atoms.radius i) ^ j ≤ C * (R * atoms.radius i) ^ 2
      rw [iteratedFDeriv_zero_fun]
      simp only [Pi.zero_apply, norm_zero, zero_mul]
      have hold := atoms.scaled_jets i 0 (by norm_num) (L (x - c))
      rw [hzero, norm_iteratedFDeriv_zero] at hold
      simp only [Pi.zero_apply, norm_zero, zero_mul] at hold
      calc
        0 ≤ R ^ 2 * (C * atoms.radius i ^ 2) :=
          mul_nonneg (sq_nonneg R) hold
        _ = C * (R * atoms.radius i) ^ 2 := by ring

/-- When the parent intrinsic scale is at most one, undoing normalization lands directly in the
unit-cap interface used by the global patch assembly. -/
noncomputable def EuclideanAtomFamily.affineRescaleToUnitCap {n : ℕ}
    {v : (Fin n → ℝ) → ℝ} {A C R : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily v A 1 C B) (hR : 0 < R) (hRone : R ≤ 1)
    (c : Fin n → ℝ) :
    EuclideanAtomFamily
      (fun x ↦ R ^ 4 * v (R⁻¹ • (x - c))) A 1 C B :=
  (atoms.affineRescaleUnitCap hR c).increaseRadiusCap hRone

/-- Change the target of a localized family along a proved function equality. -/
def LocalizedEuclideanAtomFamily.congrTarget {n : ℕ} {u v : (Fin n → ℝ) → ℝ}
    {A radiusCap C parentRadius parentDilation : ℝ} {B : ℕ}
    {parentCenter : Fin n → ℝ}
    (atoms : LocalizedEuclideanAtomFamily u A radiusCap C B
      parentCenter parentRadius parentDilation)
    (h : u = v) : LocalizedEuclideanAtomFamily v A radiusCap C B
      parentCenter parentRadius parentDilation := by
  rw [← h]
  exact atoms

/-- Changing only the represented target does not change the active atom indices. -/
@[simp] theorem LocalizedEuclideanAtomFamily.congrTarget_atoms_active {n : ℕ}
    {u v : (Fin n → ℝ) → ℝ} {A radiusCap C parentRadius parentDilation : ℝ}
    {B : ℕ} {parentCenter : Fin n → ℝ}
    (atoms : LocalizedEuclideanAtomFamily u A radiusCap C B
      parentCenter parentRadius parentDilation) (h : u = v) :
    (atoms.congrTarget h).atoms.active = atoms.atoms.active := by
  subst v
  rfl

/-- Undo fourth-order intrinsic normalization while preserving localization inside the
corresponding physical parent ball. -/
noncomputable def LocalizedEuclideanAtomFamily.affineRescaleToUnitCap {n : ℕ}
    {v : (Fin n → ℝ) → ℝ} {A C R r D : ℝ} {B : ℕ}
    (atoms : LocalizedEuclideanAtomFamily v A 1 C B 0 (r / R) D)
    (hR : 0 < R) (hRone : R ≤ 1) (c : Fin n → ℝ) :
    LocalizedEuclideanAtomFamily
      (fun x ↦ R ^ 4 * v (R⁻¹ • (x - c))) A 1 C B c r D where
  atoms := atoms.atoms.affineRescaleToUnitCap hR hRone c
  dilated_ball_subset_parent := by
    intro i hi x hx
    have hiOld : i ∈ atoms.atoms.active := by
      simpa [EuclideanAtomFamily.affineRescaleToUnitCap,
        EuclideanAtomFamily.affineRescaleUnitCap,
        EuclideanAtomFamily.increaseRadiusCap] using hi
    have hxOld : R⁻¹ • (x - c) ∈
        Metric.ball (atoms.atoms.center i) (A * atoms.atoms.radius i) := by
      rw [Metric.mem_ball] at hx ⊢
      have hdist : dist x (c + R • atoms.atoms.center i) =
          R * dist (R⁻¹ • (x - c)) (atoms.atoms.center i) := by
        calc
          dist x (c + R • atoms.atoms.center i) =
              ‖R • (R⁻¹ • (x - c) - atoms.atoms.center i)‖ := by
            rw [dist_eq_norm]
            congr 1
            rw [smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
            abel
          _ = R * ‖R⁻¹ • (x - c) - atoms.atoms.center i‖ := by
            rw [norm_smul, Real.norm_of_nonneg hR.le]
          _ = R * dist (R⁻¹ • (x - c)) (atoms.atoms.center i) := by
            rw [dist_eq_norm]
      change dist x (c + R • atoms.atoms.center i) < A * (R * atoms.atoms.radius i) at hx
      rw [hdist, show A * (R * atoms.atoms.radius i) =
        R * (A * atoms.atoms.radius i) by ring] at hx
      exact (mul_lt_mul_iff_right₀ hR).mp hx
    have hold := atoms.dilated_ball_subset_parent i hiOld hxOld
    rw [Metric.mem_ball] at hold ⊢
    have hdist : dist x c = R * dist (R⁻¹ • (x - c)) 0 := by
      calc
        dist x c = ‖x - c‖ := dist_eq_norm x c
        _ = ‖R • (R⁻¹ • (x - c))‖ := by
          rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
        _ = R * ‖R⁻¹ • (x - c)‖ := by
          rw [norm_smul, Real.norm_of_nonneg hR.le]
        _ = R * dist (R⁻¹ • (x - c)) 0 := by rw [dist_zero_right]
    rw [hdist]
    have hmul := mul_lt_mul_of_pos_left hold hR
    convert hmul using 1; field_simp [hR.ne']

/-- Undo intrinsic normalization for the actual fine-cover parent contribution.  The exact cutoff
pullback identity turns the normalized localized atoms into atoms for the physical parent
summand, preserving every quantitative constant. -/
noncomputable def LocalizedEuclideanAtomFamily.intrinsicCoverParentToPhysical {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {D sigma parentA A C : ℝ} {parentB B : ℕ}
    (hu : NormalizedNonnegativeC6 u)
    (cover : FineQuantitativeScaleCover u D sigma parentA parentB) {i : ℕ}
    (hi : i ∈ cover.active)
    (atoms : LocalizedEuclideanAtomFamily
      (fun z ↦ cover.intrinsicCutoff i z ^ 2 *
        intrinsicRescaledPatch u (cover.center i)
          (nonnegativeJetScale u (cover.center i)) z)
      A 1 C B 0
      (cover.radius i / nonnegativeJetScale u (cover.center i)) D) :
    LocalizedEuclideanAtomFamily (fun x ↦ cover.cutoff i x ^ 2 * u x)
      A 1 C B (cover.center i) (cover.radius i) D := by
  let R := nonnegativeJetScale u (cover.center i)
  have hr : 0 < cover.radius i := cover.radius_pos i hi
  have hR : 0 < R := hr.trans_le (cover.radius_comparable i hi).1
  have hRone : R ≤ 1 := by
    simpa [R] using nonnegativeJetScale_le_one hu (cover.center i)
  let physical := atoms.affineRescaleToUnitCap hR hRone (cover.center i)
  have htarget :
      (fun x ↦ R ^ 4 *
        (cover.intrinsicCutoff i (R⁻¹ • (x - cover.center i)) ^ 2 *
          intrinsicRescaledPatch u (cover.center i) R
            (R⁻¹ • (x - cover.center i)))) =
        (fun x ↦ cover.cutoff i x ^ 2 * u x) := by
    funext x
    have harg : cover.center i + R • (R⁻¹ • (x - cover.center i)) = x := by
      rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      abel
    simp only [FineQuantitativeScaleCover.intrinsicCutoff, intrinsicRescaledPatch]
    rw [show nonnegativeJetScale u (cover.center i) = R from rfl, harg]
    rw [show R ^ 4 * (cover.cutoff i x ^ 2 * ((R ^ 4)⁻¹ * u x)) =
      (R ^ 4 * (R ^ 4)⁻¹) * (cover.cutoff i x ^ 2 * u x) by ring,
      mul_inv_cancel₀ (pow_ne_zero 4 hR.ne'), one_mul]
  exact physical.congrTarget htarget

/-- Change only the definitionally represented target function along a proved function equality. -/
def EuclideanAtomFamily.congrTarget {n : ℕ} {u v : (Fin n → ℝ) → ℝ}
    {A radiusCap C : ℝ} {B : ℕ} (atoms : EuclideanAtomFamily u A radiusCap C B)
    (h : u = v) : EuclideanAtomFamily v A radiusCap C B := by
  rw [← h]
  exact atoms

/-- Atomizing the intrinsic normalized patch and undoing its affine normalization gives atoms for
the original function, with no loss in the scale-invariant jet or overlap constants. -/
noncomputable def EuclideanAtomFamily.intrinsicPatchToPhysical {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {c : Fin n → ℝ} {A C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily
      (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) A 1 C B)
    (hR : 0 < nonnegativeJetScale u c) (hRone : nonnegativeJetScale u c ≤ 1) :
    EuclideanAtomFamily u A 1 C B := by
  let R := nonnegativeJetScale u c
  let physical := atoms.affineRescaleToUnitCap hR hRone c
  have htarget :
      (fun x ↦ R ^ 4 * intrinsicRescaledPatch u c R (R⁻¹ • (x - c))) = u := by
    funext x
    have harg : c + R • (R⁻¹ • (x - c)) = x := by
      rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
      abel
    simp only [intrinsicRescaledPatch, harg]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 4 hR.ne'), one_mul]
  exact physical.congrTarget htarget
/-- Uniform Euclidean atoms with constants independent of the normalized input function. -/
def HasUniformEuclideanAtomDecomposition (n : ℕ) : Prop :=
  ∀ A radiusCap : ℝ, 1 ≤ A → 0 < radiusCap → radiusCap ≤ 1 →
    ∃ C : ℝ, ∃ B : ℕ, 0 < C ∧ 0 < B ∧
      ∀ u : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 u →
        Nonempty (EuclideanAtomFamily u A radiusCap C B)

/-- The unit-radius-cap form of the Euclidean atom theorem.  Spatial contraction upgrades this
apparently weaker statement to every prescribed positive cap at most one. -/
def HasUniformEuclideanAtomDecompositionAtOne (n : ℕ) : Prop :=
  ∀ A : ℝ, 1 ≤ A →
    ∃ C : ℝ, ∃ B : ℕ, 0 < C ∧ 0 < B ∧
      ∀ u : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 u →
        Nonempty (EuclideanAtomFamily u A 1 C B)

/-- It is enough to construct uniform atoms with unit radius cap.  Contracting the normalized
input and pulling the resulting roots back supplies any smaller prescribed cap. -/
theorem hasUniformEuclideanAtomDecomposition_of_atOne {n : ℕ}
    (hone : HasUniformEuclideanAtomDecompositionAtOne n) :
    HasUniformEuclideanAtomDecomposition n := by
  intro A radiusCap hA hradius hradiusOne
  rcases hone A hA with ⟨C, B, hC, hB, hatoms⟩
  refine ⟨C / radiusCap ^ 2, B, ?_, hB, ?_⟩
  · exact div_pos hC (sq_pos_of_pos hradius)
  · intro u hu
    have hcontracted := hu.comp_smul hradius hradiusOne
    rcases hatoms (fun x ↦ u (radiusCap • x)) hcontracted with ⟨atoms⟩
    exact ⟨atoms.contractRadius hradius⟩
/-- The lifted one-dimensional interval partition preserves the child square identity. -/
theorem liftedAtom_square_identity {n : ℕ} (v η : ℕ → ((Fin n → ℝ) → ℝ))
    (x : Fin n → ℝ) (hv : HasSum (fun i ↦ v i x ^ 2) 1)
    (hη : HasSum (fun i ↦ η i x ^ 2) 1) :
    HasSum (fun p : ℕ × ℕ ↦ (v p.1 x * η p.2 x) ^ 2) 1 := by
  have hprod : Summable (fun p : ℕ × ℕ ↦ v p.1 x ^ 2 * η p.2 x ^ 2) :=
    hv.summable.mul_of_nonneg hη.summable (fun i ↦ sq_nonneg (v i x))
      (fun i ↦ sq_nonneg (η i x))
  simpa [mul_pow] using hv.mul hη hprod


/-- Reindex the two countable child families by one natural number.  This is the concrete
indexing used when a cutoff family and a recursively decomposed residual are multiplied. -/
theorem liftedAtom_square_identity_nat {n : ℕ}
    (v η : ℕ → ((Fin n → ℝ) → ℝ)) (x : Fin n → ℝ)
    (hv : HasSum (fun i ↦ v i x ^ 2) 1)
    (hη : HasSum (fun i ↦ η i x ^ 2) 1) :
    HasSum (fun k : ℕ ↦
      let p := Nat.pairEquiv.symm k
      (v p.1 x * η p.2 x) ^ 2) 1 := by
  have hp : HasSum (fun p : ℕ × ℕ ↦ (v p.1 x * η p.2 x) ^ 2) 1 :=
    liftedAtom_square_identity v η x hv hη
  have hreindexed : HasSum
      ((fun p : ℕ × ℕ ↦ (v p.1 x * η p.2 x) ^ 2) ∘ Nat.pairEquiv.symm) 1 :=
    (Nat.pairEquiv.symm.hasSum_iff).2 hp
  simpa only [Function.comp_apply] using hreindexed

/-- Products of two `C⁴` atom factors remain `C⁴`. -/
theorem atomProduct_contDiff_four {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g) :
    ContDiff ℝ 4 (fun x ↦ f x * g x) := by
  exact hf.mul hg

/-- A scale-invariant product rule through the four derivatives retained by atom roots. -/
theorem norm_iteratedFDeriv_mul_scaled_le_four {m j : ℕ}
    {f g : (Fin m → ℝ) → ℝ} {r Mf Mg : ℝ} {x : Fin m → ℝ}
    (hr : 0 < r) (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g)
    (hfbound : ∀ q, q ≤ 4 → ‖iteratedFDeriv ℝ q f x‖ * r ^ q ≤ Mf)
    (hgbound : ∀ q, q ≤ 4 → ‖iteratedFDeriv ℝ q g x‖ * r ^ q ≤ Mg)
    (hj : j ≤ 4) :
    ‖iteratedFDeriv ℝ j (fun y ↦ f y * g y) x‖ * r ^ j ≤ 16 * Mf * Mg := by
  have hbase := norm_iteratedFDeriv_mul_le hf hg x (n := j) (by exact_mod_cast hj)
  have hscaled := mul_le_mul_of_nonneg_right hbase (pow_nonneg hr.le j)
  calc
    ‖iteratedFDeriv ℝ j (fun y ↦ f y * g y) x‖ * r ^ j ≤
        (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖) * r ^ j := hscaled
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (‖iteratedFDeriv ℝ i f x‖ * r ^ i) *
            (‖iteratedFDeriv ℝ (j - i) g x‖ * r ^ (j - i)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hi_le : i ≤ j := Finset.mem_range_succ_iff.mp hi
      rw [show r ^ j = r ^ i * r ^ (j - i) by rw [← pow_add, Nat.add_sub_of_le hi_le]]
      ring
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Mf * Mg := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_le_j : i ≤ j := Finset.mem_range_succ_iff.mp hi
      have hi_le : i ≤ 4 := hi_le_j.trans hj
      have hji_le : j - i ≤ 4 := (Nat.sub_le j i).trans hj
      gcongr
      · exact hfbound i hi_le
      · exact hgbound (j - i) hji_le
    _ = (2 : ℝ) ^ j * Mf * Mg := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]
    _ ≤ 16 * Mf * Mg := by
      have hpow : (2 : ℝ) ^ j ≤ 16 := by
        interval_cases j <;> norm_num
      gcongr
/-- Parent cutoff, normal interval cutoff, and tangential child root retain the required
`radius^(2-j)` scaling after lifting. -/
theorem liftedAtom_scaledJets {m j : ℕ}
    {parent normal child : (Fin m → ℝ) → ℝ} {r Mparent Mnormal Cchild : ℝ}
    {x : Fin m → ℝ} (hr : 0 < r)
    (hMparent : 0 ≤ Mparent) (hMnormal : 0 ≤ Mnormal) (hCchild : 0 ≤ Cchild)
    (hparent : ContDiff ℝ 4 parent) (hnormal : ContDiff ℝ 4 normal)
    (hchild : ContDiff ℝ 4 child)
    (hparent_bound : ∀ q, q ≤ 4 →
      ‖iteratedFDeriv ℝ q parent x‖ * r ^ q ≤ Mparent)
    (hnormal_bound : ∀ q, q ≤ 4 →
      ‖iteratedFDeriv ℝ q normal x‖ * r ^ q ≤ Mnormal)
    (hchild_bound : ∀ q, q ≤ 4 →
      ‖iteratedFDeriv ℝ q child x‖ * r ^ q ≤ Cchild * r ^ 2)
    (hj : j ≤ 4) :
    ‖iteratedFDeriv ℝ j (fun y ↦ parent y * normal y * child y) x‖ * r ^ j ≤
      256 * Mparent * Mnormal * Cchild * r ^ 2 := by
  have hparentNormal : ContDiff ℝ 4 (fun y ↦ parent y * normal y) :=
    hparent.mul hnormal
  have hparentNormal_bound : ∀ q, q ≤ 4 →
      ‖iteratedFDeriv ℝ q (fun y ↦ parent y * normal y) x‖ * r ^ q ≤
        16 * Mparent * Mnormal := by
    intro q hq
    exact norm_iteratedFDeriv_mul_scaled_le_four hr hMparent hMnormal
      hparent hnormal hparent_bound hnormal_bound hq
  have hleft_nonnegative : 0 ≤ 16 * Mparent * Mnormal := by positivity
  have hright_nonnegative : 0 ≤ Cchild * r ^ 2 :=
    mul_nonneg hCchild (sq_nonneg r)
  have h := norm_iteratedFDeriv_mul_scaled_le_four hr hleft_nonnegative
    hright_nonnegative hparentNormal hchild hparentNormal_bound hchild_bound hj
  calc
    ‖iteratedFDeriv ℝ j (fun y ↦ parent y * normal y * child y) x‖ * r ^ j ≤
        16 * (16 * Mparent * Mnormal) * (Cchild * r ^ 2) := h
    _ = 256 * Mparent * Mnormal * Cchild * r ^ 2 := by ring
/-- If an atom factor has compact topological support, so does its product with another factor. -/
theorem atomProduct_compact_support {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ}
    (hf : HasCompactSupport f)
    (_hg : HasCompactSupport g) :
    HasCompactSupport fun x ↦ f x * g x := by
  exact hf.mul_right

/-- A product atom is supported wherever either chosen factor is supported. -/
theorem atomProduct_support_subset_left {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ) :
    Function.support (fun x ↦ f x * g x) ⊆ Function.support f := by
  rw [Function.support_mul]
  exact Set.inter_subset_left

/-- The symmetric support inclusion for product atoms. -/
theorem atomProduct_support_subset_right {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ) :
    Function.support (fun x ↦ f x * g x) ⊆ Function.support g := by
  rw [Function.support_mul]
  exact Set.inter_subset_right

/-- A globally `C⁴` root for the positive-value alternative.  Regularizing before taking the
square root avoids any loss of smoothness away from the cutoff support. -/
def regularizedPositivePatchRoot {n : ℕ} (a : ℝ)
    (cutoff function : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  cutoff x * Real.sqrt (positiveIdentityRegularization a (function x))

theorem regularizedPositivePatchRoot_contDiff {n : ℕ} {a : ℝ}
    {cutoff function : (Fin n → ℝ) → ℝ}
    (ha : 0 < a) (hcutoff : ContDiff ℝ 4 cutoff) (hfunction : ContDiff ℝ 4 function) :
    ContDiff ℝ 4 (regularizedPositivePatchRoot a cutoff function) := by
  have hreg : ContDiff ℝ 4 (fun x ↦ positiveIdentityRegularization a (function x)) :=
    (positiveIdentityRegularization_contDiff a).comp hfunction
  have hsqrt : ContDiff ℝ 4
      (fun x ↦ Real.sqrt (positiveIdentityRegularization a (function x))) :=
    hreg.sqrt (fun x ↦ ne_of_gt (positiveIdentityRegularization_pos ha))
  exact hcutoff.mul hsqrt

theorem regularizedPositivePatchRoot_compactSupport {n : ℕ} {a : ℝ}
    {cutoff function : (Fin n → ℝ) → ℝ} (hcutoff : HasCompactSupport cutoff) :
    HasCompactSupport (regularizedPositivePatchRoot a cutoff function) := by
  exact hcutoff.mul_right

theorem support_regularizedPositivePatchRoot_subset {n : ℕ} (a : ℝ)
    (cutoff function : (Fin n → ℝ) → ℝ) :
    Function.support (regularizedPositivePatchRoot a cutoff function) ⊆
      Function.support cutoff := by
  intro x hx hzero
  apply hx
  simp [regularizedPositivePatchRoot, hzero]

/-- On the support of the cutoff, a positive lower bound makes the regularized root an exact
square root.  Outside that support both sides vanish. -/
theorem regularizedPositivePatchRoot_sq {n : ℕ} {a : ℝ}
    {cutoff function : (Fin n → ℝ) → ℝ} (ha : 0 < a)
    (hlower : ∀ x, cutoff x ≠ 0 → a ≤ function x) (x : Fin n → ℝ) :
    regularizedPositivePatchRoot a cutoff function x ^ 2 = cutoff x ^ 2 * function x := by
  by_cases hcut : cutoff x = 0
  · simp [regularizedPositivePatchRoot, hcut]
  · have heq := positiveIdentityRegularization_eq_self ha (hlower x hcut)
    rw [regularizedPositivePatchRoot, mul_pow, heq,
      Real.sq_sqrt (le_trans ha.le (hlower x hcut))]

/-- Turn the regularized positive-value root into a complete one-atom localized family.  Thus the
positive branch of the successor only has to establish its quantitative lower and jet bounds. -/
noncomputable def regularizedPositiveLocalizedAtomFamily {n : ℕ}
    {cutoff function : (Fin n → ℝ) → ℝ}
    {a A radiusCap C r parentRadius parentDilation : ℝ}
    {center parentCenter : Fin n → ℝ}
    (ha : 0 < a) (hlower : ∀ x, cutoff x ≠ 0 → a ≤ function x)
    (hr : 0 < r) (hrCap : r ≤ radiusCap) (hC : 0 ≤ C)
    (hcutoffSmooth : ContDiff ℝ 4 cutoff) (hfunctionSmooth : ContDiff ℝ 4 function)
    (hcutoffCompact : HasCompactSupport cutoff)
    (hcutoffSupport : Function.support cutoff ⊆ Metric.ball center r)
    (hjets : ∀ j, j ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ j (regularizedPositivePatchRoot a cutoff function) x‖ * r ^ j ≤
        C * r ^ 2)
    (hlocal : Metric.ball center (A * r) ⊆
      Metric.ball parentCenter (parentDilation * parentRadius)) :
    LocalizedEuclideanAtomFamily (fun x ↦ cutoff x ^ 2 * function x)
      A radiusCap C 1 parentCenter parentRadius parentDilation :=
  singleLocalizedEuclideanAtomFamily hr hrCap hC
    (regularizedPositivePatchRoot_contDiff ha hcutoffSmooth hfunctionSmooth)
    (regularizedPositivePatchRoot_compactSupport hcutoffCompact)
    ((support_regularizedPositivePatchRoot_subset a cutoff function).trans hcutoffSupport)
    (fun x ↦ (regularizedPositivePatchRoot_sq ha hlower x).symm) hjets hlocal

/-- The lower-dimensional envelope produced by the exact local split remains nonnegative. -/
theorem UniformLocalSplitData.residual_nonnegative {n : ℕ}
    {input : NormalizedLocalSplitInput n} (data : UniformLocalSplitData input)
    (y : Fin n → ℝ) : 0 ≤ data.residual y := by
  rw [data.residual_eq_envelope]
  exact input.nonnegative_on (data.graph.graph y, y) (data.graph.graph_point_mem y)
/-- A common derivative bound for a cutoff and a nonnegative residual gives one explicit common
normalization constant for the cutoff residual.  This is the uniform normalization required before
applying the lower-dimensional induction hypothesis. -/
theorem normalized_cutoffResidual {n : ℕ} {zeta psi : (Fin n → ℝ) → ℝ}
    (hpsi_nonnegative : ∀ x, 0 ≤ psi x)
    (hzeta_smooth : ContDiff ℝ 6 zeta) (hpsi_smooth : ContDiff ℝ 6 psi)
    (hzeta_compact : HasCompactSupport zeta) {Azeta Apsi : ℝ}
    (hAzeta : 0 ≤ Azeta) (hApsi : 0 ≤ Apsi)
    (hzeta_bound : ∀ j, j ≤ 6 → ∀ x, ‖iteratedFDeriv ℝ j zeta x‖ ≤ Azeta)
    (hpsi_bound : ∀ j, j ≤ 6 → ∀ x, ‖iteratedFDeriv ℝ j psi x‖ ≤ Apsi) :
    let K := max 1 (64 * (64 * Azeta * Azeta) * Apsi)
    NormalizedNonnegativeC6 (fun x ↦ K⁻¹ * (zeta x ^ 2 * psi x)) := by
  let square : (Fin n → ℝ) → ℝ := fun x ↦ zeta x * zeta x
  let K : ℝ := max 1 (64 * (64 * Azeta * Azeta) * Apsi)
  have hsquare_smooth : ContDiff ℝ 6 square := hzeta_smooth.mul hzeta_smooth
  have hsquare_bound : ∀ j, j ≤ 6 → ∀ x,
      ‖iteratedFDeriv ℝ j square x‖ ≤ 64 * Azeta * Azeta := by
    intro j hj x
    have h := norm_iteratedFDeriv_mul_scaled_le_of_contDiffAt
      (m := n) (n := j) (f := zeta) (g := zeta) (r := 1)
      zero_lt_one hAzeta hAzeta hzeta_smooth.contDiffAt hzeta_smooth.contDiffAt
      (fun q hq ↦ by simpa using hzeta_bound q hq x)
      (fun q hq ↦ by simpa using hzeta_bound q hq x) hj
    simpa [square] using h
  have hproduct_smooth : ContDiff ℝ 6 (fun x ↦ square x * psi x) :=
    hsquare_smooth.mul hpsi_smooth
  have hproduct_bound : ∀ j, j ≤ 6 → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y ↦ square y * psi y) x‖ ≤
        64 * (64 * Azeta * Azeta) * Apsi := by
    intro j hj x
    have hSquareNonneg : 0 ≤ 64 * Azeta * Azeta := by positivity
    have h := norm_iteratedFDeriv_mul_scaled_le_of_contDiffAt
      (m := n) (n := j) (f := square) (g := psi) (r := 1)
      zero_lt_one hSquareNonneg hApsi hsquare_smooth.contDiffAt hpsi_smooth.contDiffAt
      (fun q hq ↦ by simpa using hsquare_bound q hq x)
      (fun q hq ↦ by simpa using hpsi_bound q hq x) hj
    simpa using h
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcompact : HasCompactSupport (fun x ↦ square x * psi x) := by
    have hsquareCompact : HasCompactSupport square := by
      simpa [square] using hzeta_compact.mul_right (f' := zeta)
    exact hsquareCompact.mul_right
  have hnormalized := normalizedNonnegativeC6_of_bound
    (u := fun x ↦ square x * psi x)
    (fun x ↦ mul_nonneg (mul_self_nonneg (zeta x)) (hpsi_nonnegative x))
    hproduct_smooth hcompact K hK
    (fun j hj x ↦ (hproduct_bound j hj x).trans (le_max_right _ _))
  simpa [K, square, pow_two] using hnormalized
/-- The positive-value alternative is now a complete theorem: the actual fine-cover cutoff times
the intrinsic parent patch is one localized square with a dimension- and scale-independent atom
bound.  The positive branch is fully quantitative. -/
theorem exists_uniform_positiveLocalizedParentAtom
    (C delta parentA atomA parentDilation sigma : ℝ)
    (hC : 0 ≤ C) (hdelta : 0 < delta) (hparentA : 1 ≤ parentA)
    (hdilation : 2 * atomA ≤ parentDilation)
    (hsigma : 2 * sigma ≤ positiveValueCutoffRadius C delta) :
    ∃ Katom : ℝ, 0 < Katom ∧
      ∀ {n : ℕ} {u : (Fin n → ℝ) → ℝ} {parentB : ℕ}
        (cover : FineQuantitativeScaleCover
          u parentDilation sigma parentA parentB),
        NormalizedNonnegativeC6 u → NonnegativeJetControl u C →
        ∀ {i : ℕ}, i ∈ cover.active →
          delta ≤ intrinsicRescaledPatch u (cover.center i)
            (nonnegativeJetScale u (cover.center i)) 0 →
          Nonempty (LocalizedEuclideanAtomFamily
            (fun z ↦ cover.intrinsicCutoff i z ^ 2 *
              intrinsicRescaledPatch u (cover.center i)
                (nonnegativeJetScale u (cover.center i)) z)
            atomA 1 Katom 1 0
            (cover.radius i / nonnegativeJetScale u (cover.center i))
            parentDilation) := by
  obtain ⟨Katom, hKatom, hrootBound⟩ :=
    FineQuantitativeScaleCover.exists_positiveRoot_uniform_atom_bound
      C delta parentA hC hdelta hparentA
  refine ⟨Katom, hKatom, ?_⟩
  intro n u parentB cover hu hcontrol i hi hcenter
  let R := nonnegativeJetScale u (cover.center i)
  let r := cover.radius i
  let s := cover.intrinsicCutoffRadius i
  have hr : 0 < r := cover.radius_pos i hi
  have hR : 0 < R := hr.trans_le (cover.radius_comparable i hi).1
  have hs : 0 < s := cover.intrinsicCutoffRadius_pos hi
  have hsCap : s ≤ 1 := by
    calc
      s ≤ 2 * sigma := cover.intrinsicCutoffRadius_le_two_mul hi
      _ ≤ positiveValueCutoffRadius C delta := hsigma
      _ ≤ 1 := positiveValueCutoffRadius_le_one C delta
  refine ⟨singleLocalizedEuclideanAtomFamily hs hsCap hKatom.le
    (cover.positiveRoot_contDiff hu i hdelta)
    (cover.positiveRoot_compactSupport hi delta)
    (cover.support_positiveRoot_subset hi delta)
    (fun z ↦ (cover.positiveRoot_sq hu hcontrol hi hdelta hcenter hsigma z).symm)
    (fun j hj z ↦ hrootBound cover hu hcontrol hi hsigma z j hj) ?_⟩
  apply Metric.ball_subset_ball
  have hratio : 0 ≤ r / R := (div_pos hr hR).le
  calc
    atomA * s = (2 * atomA) * (r / R) := by
      dsimp [s, FineQuantitativeScaleCover.intrinsicCutoffRadius, r, R]
      ring
    _ ≤ parentDilation * (r / R) :=
      mul_le_mul_of_nonneg_right hdilation hratio

/-- The zero-dimensional Euclidean atom theorem, used as the base of dimension induction. -/
theorem uniformEuclideanAtoms_zero : HasUniformEuclideanAtomDecomposition 0 := by
  intro A radiusCap hA hradius hradiusOne
  let C : ℝ := 1 / radiusCap ^ 2
  refine ⟨C, 1, ?_, by norm_num, ?_⟩
  · dsimp [C]
    positivity
  · intro u hu
    let root : ℕ → ((Fin 0 → ℝ) → ℝ) := fun i =>
      if i = 0 then fun _ => Real.sqrt (u 0) else 0
    refine ⟨{
      root := root
      active := {0}
      center := fun _ => 0
      radius := fun _ => radiusCap
      root_eq_zero_of_not_active := ?_
      radius_pos := ?_
      radius_le_cap := ?_
      root_contDiff := ?_
      root_compact_support := ?_
      supported := ?_
      square_identity := ?_
      dilated_overlap := ?_
      scaled_jets := ?_
    }⟩
    · intro i hi
      have hi0 : i ≠ 0 := by simpa using hi
      simp [root, hi0]
    · intro i hi
      exact hradius
    · intro i hi
      exact le_rfl
    · intro i
      have hconst : root i = fun _ => root i 0 := by
        funext x
        rw [Subsingleton.elim x 0]
      rw [hconst]
      exact contDiff_const
    · intro i
      exact Set.toFinite (tsupport (root i)) |>.isCompact
    · intro i x hx
      have hx0 : x = 0 := Subsingleton.elim _ _
      subst x
      simpa [Metric.mem_ball] using hradius
    · intro x
      have hx0 : x = 0 := Subsingleton.elim _ _
      subst x
      convert (hasSum_ite_eq 0 (u 0) :
        HasSum (fun i : ℕ => if i = 0 then u 0 else 0) (u 0)) using 1
      funext i
      by_cases hi : i = 0
      · subst i
        simp only [root, if_pos]
        exact Real.sq_sqrt (hu.nonnegative 0)
      · simp [root, hi]
    · intro x s
      have hsub : {i | i ∈ s ∧ i ∈ ({0} : Set ℕ) ∧
          x ∈ Metric.ball 0 (A * radiusCap)} ⊆ ({0} : Set ℕ) := by
        intro i hi
        exact hi.2.1
      exact (Set.ncard_le_ncard hsub (Set.finite_singleton 0)).trans (by simp)
    · intro i j hj x
      have hCr : C * radiusCap ^ 2 = 1 := by
        dsimp [C]
        field_simp
      have hu1 := hu.iteratedFDeriv_le_one 0 (by norm_num) 0
      have hu0 : 0 ≤ u 0 := hu.nonnegative 0
      have huupper : u 0 ≤ 1 := by
        exact (le_abs_self (u 0)).trans (by
          simpa [iteratedFDeriv_zero_apply, Real.norm_eq_abs] using hu1)
      have hsqrt : Real.sqrt (u 0) ≤ 1 := by
        rw [Real.sqrt_le_one]
        exact huupper
      have hrootle : ‖root i x‖ ≤ 1 := by
        by_cases hi : i = 0
        · subst i
          simpa [root, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt
        · simp [root, hi]
      have hconst : root i = fun _ => root i x := by
        funext y
        rw [Subsingleton.elim y x]
      rw [hconst]
      rcases j with _ | j
      · simpa [iteratedFDeriv_zero_apply, hCr] using hrootle
      · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
        simp [hCr]
-- The normalization witness is retained in the family interface even when this layer only
-- forwards it.
set_option linter.unusedVariables false in
/-- Uniform realization of localized parent contributions.  The local atom constants may depend
on the quantitative cutoff constant `parentA`; this quantifier order is essential because the
intrinsically rescaled cutoff derivatives are bounded by a power of `parentA`. -/
def HasUniformLocalizedParentAtomRealization (q : ℕ) : Prop :=
  ∀ A : ℝ, 1 ≤ A →
    ∃ parentDilation σ : ℝ,
      2 ≤ parentDilation ∧ 0 < σ ∧ σ ≤ 1 ∧
      ∀ parentA : ℝ, 1 ≤ parentA →
        ∃ C : ℝ, ∃ childB : ℕ, 0 < C ∧ 0 < childB ∧
          ∀ {parentB : ℕ} (u : (Fin q → ℝ) → ℝ)
            (hu : NormalizedNonnegativeC6 u)
            (cover : FineQuantitativeScaleCover
              u parentDilation σ parentA parentB),
            ∃ patch : ∀ i, LocalizedEuclideanAtomFamily
                (fun x ↦ cover.cutoff i x ^ 2 * u x) A 1 C childB
                (cover.center i) (cover.radius i) parentDilation,
              ∀ i, i ∉ cover.active → (patch i).atoms.active = ∅

end QuarticConvergence
end OptimalConvergenceRates

end
