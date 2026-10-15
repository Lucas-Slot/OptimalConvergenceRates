/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/ScaleCover.lean

  Slow variation and the quantitative square partition used by the atom induction.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.JetBounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.LocallyFinite

open Finset Set
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- Uniform slow variation for the intrinsic fourth-order scale. -/
def HasIntrinsicScaleSlowVariation (n : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧
    ∀ u : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 u → ∀ x y,
      dist x y ≤ c * nonnegativeJetScale u x →
        nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
        nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x

/-- A countable quantitative square partition at the intrinsic local scale. The constant `A`
records both inverse scale comparability and the derivative bounds for a fixed smooth cutoff
profile, while `D` is the prescribed support-ball dilation whose overlap is controlled. -/
structure QuantitativeScaleCover {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (D A : ℝ) (B : ℕ) where
  two_le_dilation : 2 ≤ D
  center : ℕ → (Fin n → ℝ)
  radius : ℕ → ℝ
  cutoff : ℕ → ((Fin n → ℝ) → ℝ)
  active : Set ℕ
  cutoff_eq_zero_of_not_active : ∀ i, i ∉ active → cutoff i = 0
  radius_pos : ∀ i, i ∈ active → 0 < radius i
  radius_comparable : ∀ i, i ∈ active →
    radius i ≤ nonnegativeJetScale u (center i) ∧
      nonnegativeJetScale u (center i) ≤ A * radius i
  cutoff_contDiff : ∀ i, ContDiff ℝ 6 (cutoff i)
  cutoff_support : ∀ i, Function.support (cutoff i) ⊆ Metric.ball (center i) (2 * radius i)
  square_partition : ∀ x, 0 < nonnegativeJetScale u x → ∑' i, cutoff i x ^ 2 = 1
  overlap : ∀ x (s : Finset ℕ),
    Set.ncard {i | i ∈ s ∧ i ∈ active ∧
      x ∈ Metric.ball (center i) (D * radius i)} ≤ B
  scaled_cutoff : ∀ i j, j ≤ 6 → ∀ x,
    ‖iteratedFDeriv ℝ j (cutoff i) x‖ * radius i ^ j ≤ A

/-- A uniform bound on the size of every finite subfamily forces the whole set to be
finite. This elementary form is convenient for overlap interfaces indexed by `ℕ`. -/
theorem finite_of_uniform_finset_ncard_le {p : ℕ → Prop} {B : ℕ}
    (h : ∀ s : Finset ℕ, Set.ncard {i | i ∈ s ∧ p i} ≤ B) :
    Set.Finite {i | p i} := by
  by_contra hinf
  have hinf' : Set.Infinite {i | p i} := hinf
  obtain ⟨t, ht, hcard⟩ := hinf'.exists_subset_card_eq (B + 1)
  have hb := h t
  have heq : {i | i ∈ t ∧ p i} = (t : Set ℕ) := by
    ext i
    simp only [mem_ofPred_eq, mem_coe]
    constructor
    · exact fun hi => hi.1
    · intro hi
      exact ⟨hi, ht hi⟩
  rw [heq] at hb
  have hle : t.card ≤ B := by simpa using hb
  omega
/-- The same finite-subfamily hypothesis also preserves its cardinality constant for the
whole set. -/
theorem ncard_le_of_uniform_finset_ncard_le {p : ℕ → Prop} {B : ℕ}
    (h : ∀ s : Finset ℕ, Set.ncard {i | i ∈ s ∧ p i} ≤ B) :
    Set.ncard {i | p i} ≤ B := by
  have hfinite : Set.Finite {i | p i} := finite_of_uniform_finset_ncard_le h
  simpa using h hfinite.toFinset

/-- The norm of a countable sum with at most `B` nonzero terms, each of norm at most
`M`, is at most `B * M`. -/
theorem norm_tsum_le_of_finite_support_card {F : Type*} [NormedAddCommGroup F]
    (f : ℕ → F) (B : ℕ) (M : ℝ)
    (hfinite : Set.Finite {i | f i ≠ 0})
    (hcard : Set.ncard {i | f i ≠ 0} ≤ B)
    (hbound : ∀ i, ‖f i‖ ≤ M) (hM : 0 ≤ M) :
    ‖∑' i, f i‖ ≤ B * M := by
  let t := hfinite.toFinset
  rw [tsum_eq_sum (s := t)]
  · calc
      ‖∑ i ∈ t, f i‖ ≤ ∑ i ∈ t, ‖f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ t, M := by gcongr with i hi; exact hbound i
      _ = t.card * M := by simp
      _ = Set.ncard {i | f i ≠ 0} * M := by
        rw [Set.ncard_eq_toFinset_card _ hfinite]
      _ ≤ B * M := by
        gcongr
  · intro i hi
    have hi' : i ∉ {i | f i ≠ 0} := by simpa [t] using hi
    simpa using hi'

/-- A finite-support countable-sum norm bound in scale-invariant form. -/
theorem norm_tsum_mul_pow_le_of_finite_support_card {F : Type*}
    [NormedAddCommGroup F] (f : ℕ → F) (B : ℕ) (M r : ℝ) (j : ℕ)
    (hfinite : Set.Finite {i | f i ≠ 0})
    (hcard : Set.ncard {i | f i ≠ 0} ≤ B)
    (hbound : ∀ i, ‖f i‖ * r ^ j ≤ M) (hr : 0 < r) (hM : 0 ≤ M) :
    ‖∑' i, f i‖ * r ^ j ≤ B * M := by
  have hrpow : 0 < r ^ j := pow_pos hr j
  have hone (i : ℕ) : ‖f i‖ ≤ M / r ^ j := by
    exact (le_div_iff₀ hrpow).2 (hbound i)
  have hdiv : 0 ≤ M / r ^ j := div_nonneg hM hrpow.le
  have hsum := norm_tsum_le_of_finite_support_card f B (M / r ^ j)
    hfinite hcard hone hdiv
  calc
    ‖∑' i, f i‖ * r ^ j ≤ (B * (M / r ^ j)) * r ^ j :=
      mul_le_mul_of_nonneg_right hsum hrpow.le
    _ = B * M := by field_simp

namespace QuantitativeScaleCover



/-- Point-finiteness is a consequence of quantitative overlap and cutoff support, so it
does not need to be supplied separately when constructing a scale cover. -/
theorem point_finite {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {D A : ℝ} {B : ℕ} (cover : QuantitativeScaleCover u D A B) (x : Fin n → ℝ) :
    Set.Finite {i | cover.cutoff i x ≠ 0} := by
  refine finite_of_uniform_finset_ncard_le (B := B) ?_
  intro s
  let target : Set ℕ :=
    {i | i ∈ s ∧ i ∈ cover.active ∧
      x ∈ Metric.ball (cover.center i) (D * cover.radius i)}
  have htarget : target.Finite := s.finite_toSet.subset (by
    intro i hi
    exact hi.1)
  have hsubset : {i | i ∈ s ∧ cover.cutoff i x ≠ 0} ⊆ target := by
    rintro i ⟨hi, hcut⟩
    have hactive : i ∈ cover.active := by
      by_contra hnot
      apply hcut
      rw [cover.cutoff_eq_zero_of_not_active i hnot]
      rfl
    refine ⟨hi, hactive, Metric.ball_subset_ball ?_ (cover.cutoff_support i hcut)⟩
    exact mul_le_mul_of_nonneg_right cover.two_le_dilation
      (cover.radius_pos i hactive).le
  exact (Set.ncard_le_ncard hsubset htarget).trans (cover.overlap x s)

end QuantitativeScaleCover

/-- Uniform existence of the quantitative square cover in a fixed dimension, for every
prescribed dilation at least two. -/
def HasUniformScaleCover (n : ℕ) : Prop :=
  ∀ D : ℝ, 2 ≤ D → ∃ A : ℝ, ∃ B : ℕ, 1 ≤ A ∧ 0 < B ∧
      ∀ u : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 u →
        Nonempty (QuantitativeScaleCover u D A B)

/-- The zero function is represented by the genuinely empty quantitative cover.  Active
indices are essential here: positive scale-comparable radii cannot exist when the intrinsic
scale vanishes identically. -/
def zeroQuantitativeScaleCover {n : ℕ} {D A : ℝ} (hD : 2 ≤ D) (hA : 0 ≤ A) :
    QuantitativeScaleCover (fun _ : Fin n → ℝ => 0) D A 1 where
  two_le_dilation := hD
  center := fun _ => 0
  radius := fun _ => 1
  cutoff := fun _ _ => 0
  active := ∅
  cutoff_eq_zero_of_not_active := by
    intro i hi
    rfl
  radius_pos := by simp
  radius_comparable := by simp
  cutoff_contDiff := by
    intro i
    exact contDiff_const
  cutoff_support := by
    intro i x hx
    simp [Function.support] at hx
  square_partition := by
    intro x hx
    simp [nonnegativeJetScale] at hx
  overlap := by simp
  scaled_cutoff := by
    intro i j hj x
    rw [iteratedFDeriv_fun_zero]
    simpa using hA

@[simp] theorem zeroQuantitativeScaleCover_active {n : ℕ} {D A : ℝ}
    (hD : 2 ≤ D) (hA : 0 ≤ A) :
    (zeroQuantitativeScaleCover (n := n) hD hA).active = ∅ := rfl

/-- The intrinsic balls on the positive-scale locus form a bounded-radius ball package.
The bound `R ≤ 1` is precisely what is needed by mathlib's topological Besicovitch theorem. -/
def intrinsicScaleBallPackage {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : NormalizedNonnegativeC6 u) (ε : ℝ) (hε : 0 < ε) :
    Besicovitch.BallPackage {x : Fin n → ℝ // 0 < nonnegativeJetScale u x}
      (Fin n → ℝ) where
  c := fun x => x.1
  r := fun x => ε * nonnegativeJetScale u x.1
  rpos := fun x => mul_pos hε x.2
  r_bound := ε
  r_le := fun x => by
    exact mul_le_of_le_one_right hε.le (nonnegativeJetScale_le_one hu x.1)

/-- Besicovitch selection splits intrinsic balls into finitely many closed-ball-disjoint
families whose corresponding open balls cover every positive-scale point.  This discharges
the first geometric extraction step of the scale-cover proof. -/
theorem exists_disjoint_intrinsic_covering_families {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
        Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x},
      (∀ color, (s color).PairwiseDisjoint fun i =>
        Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)) ∧
      Set.range (intrinsicScaleBallPackage hu ε hε).c ⊆
        ⋃ color, ⋃ i ∈ s color,
          Metric.ball i.1 (ε * nonnegativeJetScale u i.1) := by
  exact Besicovitch.exist_disjoint_covering_families
    (Besicovitch.one_lt_goodτ (Fin n → ℝ))
    (Besicovitch.isEmpty_satelliteConfig_multiplicity (Fin n → ℝ))
    (intrinsicScaleBallPackage hu ε hε)

/-- Each disjoint selected family is countable. The proof uses separability of Euclidean
space and the nonempty open balls contained in the selected disjoint closed balls. -/
theorem disjoint_intrinsic_family_countable {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (ε : ℝ) (hε : 0 < ε)
    (s : Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : s.PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)) :
    s.Countable := by
  have hopen : s.PairwiseDisjoint fun i =>
      Metric.ball i.1 (ε * nonnegativeJetScale u i.1) :=
    hdis.mono (fun i => Metric.ball_subset_closedBall)
  exact hopen.countable_of_isOpen
    (fun i hi => Metric.isOpen_ball)
    (fun i hi => ⟨i.1, Metric.mem_ball_self (mul_pos hε i.2)⟩)

/-- The union of the finitely many Besicovitch colors is countable. -/
theorem disjoint_intrinsic_families_iUnion_countable {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (ε : ℝ) (hε : 0 < ε)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)) :
    (⋃ color, s color).Countable :=
  Set.countable_iUnion fun color =>
    disjoint_intrinsic_family_countable ε hε (s color) (hdis color)

/-- A duplicate-free natural-number indexing of a countable subset.  The explicit active
set lets the ambient type remain inhabited even when the indexed subset is empty. -/
structure CountableSetNatIndexing {α : Type*} (s : Set α) where
  active : Set ℕ
  value : ℕ → α
  value_mem : ∀ i, i ∈ active → value i ∈ s
  value_injOn : Set.InjOn value active
  surjective_on : ∀ x, x ∈ s → ∃ i, i ∈ active ∧ value i = x

/-- Every countable subset of an inhabited ambient type has a duplicate-free active
natural-number indexing. Inactive indices are sent to the prescribed default. -/
def countableSetNatIndexing {α : Type*} (default : α) {s : Set α}
    (hs : s.Countable) : CountableSetNatIndexing s := by
  let enc : Encodable s := hs.toEncodable
  let encode : s → ℕ := @Encodable.encode s enc
  let value : ℕ → α := Set.enumerateCountable hs default
  refine
    { active := Set.range encode
      value := value
      value_mem := ?_
      value_injOn := ?_
      surjective_on := ?_ }
  · intro i hi
    obtain ⟨x, rfl⟩ := hi
    change Set.enumerateCountable hs default (encode x) ∈ s
    simp [Set.enumerateCountable, encode, enc]
  · intro i hi j hj hij
    obtain ⟨x, rfl⟩ := hi
    obtain ⟨y, rfl⟩ := hj
    have hxy : x = y := by
      apply Subtype.ext
      simpa [value, Set.enumerateCountable, encode, enc] using hij
    exact congr_arg encode hxy
  · intro x hx
    let y : s := ⟨x, hx⟩
    refine ⟨encode y, ⟨y, rfl⟩, ?_⟩
    change Set.enumerateCountable hs default (encode y) = x
    simp [Set.enumerateCountable, encode, enc, y]

/-- Ambient centers belonging to at least one selected Besicovitch color. -/
def selectedIntrinsicCenters {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x}) : Set (Fin n → ℝ) :=
  Subtype.val '' ⋃ color, s color

/-- The selected centers are countable after forgetting their positivity certificate. -/
theorem selectedIntrinsicCenters_countable {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)) :
    (selectedIntrinsicCenters s).Countable :=
  (disjoint_intrinsic_families_iUnion_countable ε hε s hdis).image Subtype.val

/-- The selected centers, indexed without duplicates by an active subset of `ℕ`. -/
def selectedIntrinsicCentersNatIndexing {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)) :
    CountableSetNatIndexing (selectedIntrinsicCenters s) :=
  countableSetNatIndexing 0 (selectedIntrinsicCenters_countable hε s hdis)

/-- Every active indexed center has positive intrinsic scale. -/
theorem selectedIntrinsicCentersNatIndexing_value_pos {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1))
    (i : ℕ) (hi : i ∈ (selectedIntrinsicCentersNatIndexing hε s hdis).active) :
    0 < nonnegativeJetScale u ((selectedIntrinsicCentersNatIndexing hε s hdis).value i) := by
  obtain ⟨z, hz, hzi⟩ :=
    (selectedIntrinsicCentersNatIndexing hε s hdis).value_mem i hi
  simpa [← hzi] using z.2

/-- The indexed inner balls still cover the full positive-scale locus. -/
theorem selectedIntrinsicCentersNatIndexing_cover {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1))
    (hcover : Set.range (fun x : {x : Fin n → ℝ // 0 < nonnegativeJetScale u x} => x.1) ⊆
      ⋃ color, ⋃ z ∈ s color,
        Metric.ball z.1 (ε * nonnegativeJetScale u z.1)) :
    {x | 0 < nonnegativeJetScale u x} ⊆
      ⋃ i ∈ (selectedIntrinsicCentersNatIndexing hε s hdis).active,
        Metric.ball ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)
          (ε * nonnegativeJetScale u
            ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)) := by
  intro x hx
  have hxrange : x ∈ Set.range
      (fun z : {z : Fin n → ℝ // 0 < nonnegativeJetScale u z} => z.1) :=
    ⟨⟨x, hx⟩, rfl⟩
  have hxcov := hcover hxrange
  simp only [Set.mem_iUnion] at hxcov ⊢
  obtain ⟨color, z, hzcolor, hxball⟩ := hxcov
  have hzselected : z.1 ∈ selectedIntrinsicCenters s := by
    exact ⟨z, Set.mem_iUnion.2 ⟨color, hzcolor⟩, rfl⟩
  obtain ⟨i, hi, hcenter⟩ :=
    (selectedIntrinsicCentersNatIndexing hε s hdis).surjective_on z.1 hzselected
  refine ⟨i, hi, ?_⟩
  simpa [hcenter] using hxball

/-- Ordered form of scale comparability for two intrinsic balls whose `D`-dilates meet.
The smallness condition on `ε` puts the second center inside the slow-variation ball of the
larger-scale center. -/
theorem intrinsicScale_comparable_of_common_scaled_ball_ordered {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {c C D ε : ℝ}
    (hD : 0 ≤ D) (hε : 0 < ε) (hsmall : 2 * D * ε ≤ c)
    (hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x)
    {ci cj x : Fin n → ℝ}
    (hRi : 0 < nonnegativeJetScale u ci)
    (horder : nonnegativeJetScale u cj ≤ nonnegativeJetScale u ci)
    (hi : x ∈ Metric.ball ci (D * (ε * nonnegativeJetScale u ci)))
    (hj : x ∈ Metric.ball cj (D * (ε * nonnegativeJetScale u cj))) :
    nonnegativeJetScale u ci ≤ C * nonnegativeJetScale u cj ∧
      nonnegativeJetScale u cj ≤ C * nonnegativeJetScale u ci := by
  have hi' : dist ci x < D * (ε * nonnegativeJetScale u ci) := by
    simpa [dist_comm] using (Metric.mem_ball.mp hi)
  have hj' : dist x cj < D * (ε * nonnegativeJetScale u cj) :=
    Metric.mem_ball.mp hj
  have hcenters : dist ci cj < c * nonnegativeJetScale u ci := by
    calc
      dist ci cj ≤ dist ci x + dist x cj := dist_triangle _ _ _
      _ < D * (ε * nonnegativeJetScale u ci) +
          D * (ε * nonnegativeJetScale u cj) := add_lt_add hi' hj'
      _ ≤ D * (ε * nonnegativeJetScale u ci) +
          D * (ε * nonnegativeJetScale u ci) := by gcongr
      _ = (2 * D * ε) * nonnegativeJetScale u ci := by ring
      _ ≤ c * nonnegativeJetScale u ci :=
        mul_le_mul_of_nonneg_right hsmall hRi.le
  exact hvar ci cj hcenters.le

/-- Symmetric form of scale comparability for any two intrinsic balls whose prescribed
dilates meet. -/
theorem intrinsicScale_comparable_of_common_scaled_balls {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {c C D ε : ℝ}
    (hD : 0 ≤ D) (hε : 0 < ε) (hsmall : 2 * D * ε ≤ c)
    (hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x)
    {ci cj x : Fin n → ℝ}
    (hRi : 0 < nonnegativeJetScale u ci)
    (hRj : 0 < nonnegativeJetScale u cj)
    (hi : x ∈ Metric.ball ci (D * (ε * nonnegativeJetScale u ci)))
    (hj : x ∈ Metric.ball cj (D * (ε * nonnegativeJetScale u cj))) :
    nonnegativeJetScale u ci ≤ C * nonnegativeJetScale u cj ∧
      nonnegativeJetScale u cj ≤ C * nonnegativeJetScale u ci := by
  rcases le_total (nonnegativeJetScale u cj) (nonnegativeJetScale u ci) with h | h
  · exact intrinsicScale_comparable_of_common_scaled_ball_ordered
      hD hε hsmall hvar hRi h hi hj
  · exact (intrinsicScale_comparable_of_common_scaled_ball_ordered
      hD hε hsmall hvar hRj h hj hi).symm

/-- A selected intrinsic ball whose `D`-dilate contains `x` lies in a fixed ball about `x`
once its scale is bounded above by a reference scale. -/
theorem intrinsic_ball_subset_common_ball {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {D ε C : ℝ}
    (hD : 0 ≤ D) (hε : 0 < ε)
    {ci cref x : Fin n → ℝ}
    (hcomp : nonnegativeJetScale u ci ≤ C * nonnegativeJetScale u cref)
    (hi : x ∈ Metric.ball ci (D * (ε * nonnegativeJetScale u ci))) :
    Metric.ball ci (ε * nonnegativeJetScale u ci) ⊆
      Metric.ball x ((D + 1) * ε * C * nonnegativeJetScale u cref) := by
  intro y hy
  have hy' : dist y ci < ε * nonnegativeJetScale u ci := Metric.mem_ball.mp hy
  have hi' : dist ci x < D * (ε * nonnegativeJetScale u ci) := by
    simpa [dist_comm] using (Metric.mem_ball.mp hi)
  rw [Metric.mem_ball]
  calc
    dist y x ≤ dist y ci + dist ci x := dist_triangle _ _ _
    _ < ε * nonnegativeJetScale u ci +
        D * (ε * nonnegativeJetScale u ci) := add_lt_add hy' hi'
    _ = (D + 1) * ε * nonnegativeJetScale u ci := by ring
    _ ≤ (D + 1) * ε * (C * nonnegativeJetScale u cref) := by gcongr
    _ = (D + 1) * ε * C * nonnegativeJetScale u cref := by ring

/-- Conversely, scale comparability puts a common positive-radius ball inside every selected
intrinsic ball meeting the prescribed point. -/
theorem common_scale_ball_subset_intrinsic_ball {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {ε C : ℝ}
    (hε : 0 ≤ ε) (hC : 1 ≤ C)
    {ci cref : Fin n → ℝ}
    (hcomp : nonnegativeJetScale u cref ≤ C * nonnegativeJetScale u ci) :
    Metric.ball ci (ε * nonnegativeJetScale u cref / C) ⊆
      Metric.ball ci (ε * nonnegativeJetScale u ci) := by
  apply Metric.ball_subset_ball
  apply (div_le_iff₀ (zero_lt_one.trans_le hC)).2
  calc
    ε * nonnegativeJetScale u cref ≤
        ε * (C * nonnegativeJetScale u ci) :=
      mul_le_mul_of_nonneg_left hcomp hε
    _ = ε * nonnegativeJetScale u ci * C := by ring

/-- A compact set contains only uniformly many points separated at a fixed positive scale.
No volume formula is needed: choose a finite cover by smaller balls and inject a separated
finite subset into the cover. -/
theorem exists_finset_card_bound_of_separated_mem_compact
    {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℕ, ∀ s : Finset X, (∀ x ∈ s, x ∈ K) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * δ ≤ dist x y) → s.card ≤ B := by
  obtain ⟨t, htK, htfinite, hcover⟩ := hK.finite_cover_balls hδ
  refine ⟨t.ncard, ?_⟩
  intro s hsK hsep
  have hchoice : ∀ x : {x // x ∈ s}, ∃ a, a ∈ t ∧ dist x.1 a < δ := by
    intro x
    have hxcover := hcover (hsK x.1 x.2)
    simp only [mem_iUnion] at hxcover
    obtain ⟨a, ha⟩ := hxcover
    obtain ⟨hat, hxa⟩ := ha
    exact ⟨a, hat, Metric.mem_ball.mp hxa⟩
  choose f hft hfdist using hchoice
  let F : {x // x ∈ s} → {a // a ∈ t} := fun x => ⟨f x, hft x⟩
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hsep_xy := hsep x.1 x.2 y.1 y.2 hne
    have hFval : f x = f y := congr_arg Subtype.val hxy
    have hlt : dist x.1 y.1 < 2 * δ := by
      calc
        dist x.1 y.1 ≤ dist x.1 (f x) + dist (f x) y.1 := dist_triangle _ _ _
        _ = dist x.1 (f x) + dist (f y) y.1 := by rw [hFval]
        _ < δ + δ := add_lt_add (hfdist x) (by simpa [dist_comm] using hfdist y)
        _ = 2 * δ := by ring
    exact (not_lt_of_ge hsep_xy) hlt
  letI : Finite t := htfinite
  letI : Fintype t := Fintype.ofFinite t
  have hcard := Fintype.card_le_of_injective F hFinj
  have htcard : Fintype.card {a // a ∈ t} = t.ncard := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq t
  calc
    s.card = Fintype.card {x // x ∈ s} := by simp
    _ ≤ Fintype.card {a // a ∈ t} := hcard
    _ ≤ t.ncard := htcard.le

/-- Disjoint closed balls with radii bounded below by `δ` have centers separated by
`2δ`. The midpoint supplies the contradiction if the centers were closer. -/
theorem two_mul_le_dist_of_disjoint_closedBalls {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} {rx ry δ : ℝ} (hδx : δ ≤ rx) (hδy : δ ≤ ry)
    (hdis : Disjoint (Metric.closedBall x rx) (Metric.closedBall y ry)) :
    2 * δ ≤ dist x y := by
  by_contra hnot
  have hdist : dist x y < 2 * δ := lt_of_not_ge hnot
  let m := midpoint ℝ x y
  have hmx : m ∈ Metric.closedBall x rx := by
    rw [Metric.mem_closedBall]
    change dist (midpoint ℝ x y) x ≤ rx
    rw [dist_midpoint_left]
    norm_num
    linarith
  have hmy : m ∈ Metric.closedBall y ry := by
    rw [Metric.mem_closedBall]
    change dist (midpoint ℝ x y) y ≤ ry
    rw [dist_midpoint_right]
    norm_num
    linarith
  exact Set.disjoint_left.mp hdis hmx hmy

-- The positivity binders are retained to expose the complete packing interface; the proof
-- recovers them from the positive-radius subtype.
set_option linter.unusedVariables false in
/-- For one disjoint Besicovitch color, the number of intrinsic balls whose `D`-dilates
contain a point is bounded uniformly in the input function and in the reference scale.
Rescaling by the reference radius reduces the claim to compact packing in a fixed ball. -/
theorem exists_intrinsic_color_card_bound (n : ℕ) {D C : ℝ}
    (hD : 0 ≤ D) (hC : 1 ≤ C) :
    ∃ B : ℕ, ∀ {u : (Fin n → ℝ) → ℝ} {ε : ℝ}
      {x cref : Fin n → ℝ}
      (hε : 0 < ε) (href : 0 < nonnegativeJetScale u cref)
      (s : Finset {z : Fin n → ℝ // 0 < nonnegativeJetScale u z}),
      (∀ i ∈ s, x ∈ Metric.ball i.1
        (D * (ε * nonnegativeJetScale u i.1))) →
      (∀ i ∈ s,
        nonnegativeJetScale u i.1 ≤ C * nonnegativeJetScale u cref ∧
        nonnegativeJetScale u cref ≤ C * nonnegativeJetScale u i.1) →
      ((s : Set {z : Fin n → ℝ // 0 < nonnegativeJetScale u z}).PairwiseDisjoint
        fun i => Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)) →
      s.card ≤ B := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨B, hB⟩ := exists_finset_card_bound_of_separated_mem_compact
    (X := Fin n → ℝ) (K := Metric.closedBall (0 : Fin n → ℝ) (D * C))
    (isCompact_closedBall (0 : Fin n → ℝ) (D * C)) (one_div_pos.mpr hCpos)
  refine ⟨B, ?_⟩
  intro u ε x cref hε href s hmeet hcomp hdis
  let a := ε * nonnegativeJetScale u cref
  have hapos : 0 < a := mul_pos hε href
  let F : {z : Fin n → ℝ // 0 < nonnegativeJetScale u z} → (Fin n → ℝ) :=
    fun i => a⁻¹ • (i.1 - x)
  have hFinj : Function.Injective F := by
    intro i j hij
    apply Subtype.ext
    have hsub : i.1 - x = j.1 - x :=
      smul_right_injective (Fin n → ℝ) (inv_ne_zero hapos.ne') hij
    exact sub_left_inj.mp hsub
  have himage_mem : ∀ z ∈ s.image F,
      z ∈ Metric.closedBall (0 : Fin n → ℝ) (D * C) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨i, his, rfl⟩ := hz
    have hi := Metric.mem_ball.mp (hmeet i his)
    have hi' : ‖i.1 - x‖ < D * (ε * nonnegativeJetScale u i.1) := by
      simpa [dist_eq_norm, norm_sub_rev] using hi
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖a⁻¹ • (i.1 - x)‖ ≤ D * C
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos)]
    calc
      a⁻¹ * ‖i.1 - x‖ ≤
          a⁻¹ * (D * (ε * nonnegativeJetScale u i.1)) :=
        (mul_lt_mul_of_pos_left hi' (inv_pos.mpr hapos)).le
      _ ≤ a⁻¹ * (D * (ε * (C * nonnegativeJetScale u cref))) := by
        gcongr
        exact (hcomp i his).1
      _ = D * C := by
        dsimp [a]
        field_simp
  have himage_sep : ∀ z ∈ s.image F, ∀ w ∈ s.image F, z ≠ w →
      2 * (1 / C) ≤ dist z w := by
    intro z hz w hw hzw
    rw [Finset.mem_image] at hz hw
    obtain ⟨i, his, rfl⟩ := hz
    obtain ⟨j, hjs, rfl⟩ := hw
    have hij : i ≠ j := fun hij => hzw (congr_arg F hij)
    have hd := hdis his hjs hij
    have hδi : ε * nonnegativeJetScale u cref / C ≤
        ε * nonnegativeJetScale u i.1 := by
      apply (div_le_iff₀ hCpos).2
      calc
        ε * nonnegativeJetScale u cref ≤
            ε * (C * nonnegativeJetScale u i.1) :=
          mul_le_mul_of_nonneg_left (hcomp i his).2 hε.le
        _ = ε * nonnegativeJetScale u i.1 * C := by ring
    have hδj : ε * nonnegativeJetScale u cref / C ≤
        ε * nonnegativeJetScale u j.1 := by
      apply (div_le_iff₀ hCpos).2
      calc
        ε * nonnegativeJetScale u cref ≤
            ε * (C * nonnegativeJetScale u j.1) :=
          mul_le_mul_of_nonneg_left (hcomp j hjs).2 hε.le
        _ = ε * nonnegativeJetScale u j.1 * C := by ring
    have hsep := two_mul_le_dist_of_disjoint_closedBalls hδi hδj hd
    have hdistF : dist (F i) (F j) = a⁻¹ * dist i.1 j.1 := by
      rw [dist_eq_norm]
      change ‖a⁻¹ • (i.1 - x) - a⁻¹ • (j.1 - x)‖ =
        a⁻¹ * ‖i.1 - j.1‖
      rw [← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hapos)]
      congr 1
      abel
    rw [hdistF]
    calc
      2 * (1 / C) = a⁻¹ * (2 * (ε * nonnegativeJetScale u cref / C)) := by
        dsimp [a]
        field_simp
      _ ≤ a⁻¹ * dist i.1 j.1 :=
        mul_le_mul_of_nonneg_left hsep (inv_pos.mpr hapos).le
  have hbound := hB (s.image F) himage_mem himage_sep
  rw [Finset.card_image_of_injective _ hFinj] at hbound
  exact hbound

/-- A fixed packing bound for one Besicovitch color. -/
def intrinsicColorCardBound (n : ℕ) {D C : ℝ} (hD : 0 ≤ D) (hC : 1 ≤ C) : ℕ :=
  Classical.choose (exists_intrinsic_color_card_bound n hD hC)

-- The positivity binders mirror the existential packing theorem and are intentionally retained.
set_option linter.unusedVariables false in
theorem intrinsicColorCardBound_spec (n : ℕ) {D C : ℝ} (hD : 0 ≤ D) (hC : 1 ≤ C) :
    ∀ {u : (Fin n → ℝ) → ℝ} {ε : ℝ} {x cref : Fin n → ℝ}
      (hε : 0 < ε) (href : 0 < nonnegativeJetScale u cref)
      (s : Finset {z : Fin n → ℝ // 0 < nonnegativeJetScale u z}),
      (∀ i ∈ s, x ∈ Metric.ball i.1
        (D * (ε * nonnegativeJetScale u i.1))) →
      (∀ i ∈ s,
        nonnegativeJetScale u i.1 ≤ C * nonnegativeJetScale u cref ∧
        nonnegativeJetScale u cref ≤ C * nonnegativeJetScale u i.1) →
      ((s : Set {z : Fin n → ℝ // 0 < nonnegativeJetScale u z}).PairwiseDisjoint
        fun i => Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)) →
      s.card ≤ intrinsicColorCardBound n hD hC :=
  Classical.choose_spec (exists_intrinsic_color_card_bound n hD hC)

/-- The corresponding all-color overlap bound. -/
def intrinsicOverlapBound (n : ℕ) {D C : ℝ} (hD : 0 ≤ D) (hC : 1 ≤ C) : ℕ :=
  Fintype.card (Fin (Besicovitch.multiplicity (Fin n → ℝ))) *
    intrinsicColorCardBound n hD hC

/-- Uniform cardinality bounds for finitely many Besicovitch colors add with only the
number of colors as a factor. Disjointness between distinct colors is not required. -/
theorem ncard_iUnion_le_mul_of_uniform {ι α : Type*} [Fintype ι]
    (s : ι → Set α) {B : ℕ} (h : ∀ i, (s i).ncard ≤ B) :
    (⋃ i, s i).ncard ≤ Fintype.card ι * B := by
  calc
    (⋃ i, s i).ncard ≤ ∑ i, (s i).ncard := Set.ncard_iUnion_le_of_fintype s
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i hi => h i
    _ = Fintype.card ι * B := by simp

/-- The duplicate-free natural indexing preserves the uniform overlap bound obtained
color-by-color from the Besicovitch selection. -/
theorem selectedIntrinsicCentersNatIndexing_overlap_bound (n : ℕ)
    {u : (Fin n → ℝ) → ℝ} {c C D ε : ℝ}
    (hD : 0 ≤ D) (hC : 1 ≤ C) (hε : 0 < ε) (hsmall : 2 * D * ε ≤ c)
    (hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)) :
    ∀ x (t : Finset ℕ),
      Set.ncard {i | i ∈ t ∧
        i ∈ (selectedIntrinsicCentersNatIndexing hε s hdis).active ∧
        x ∈ Metric.ball ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)
          (D * (ε * nonnegativeJetScale u
            ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)))} ≤
      intrinsicOverlapBound n hD hC := by
  let Bcolor := intrinsicColorCardBound n hD hC
  intro x t
  let I := selectedIntrinsicCentersNatIndexing hε s hdis
  let target : Set ℕ := {i | i ∈ t ∧ i ∈ I.active ∧
    x ∈ Metric.ball (I.value i) (D * (ε * nonnegativeJetScale u (I.value i)))}
  by_cases htarget : target.Nonempty
  · obtain ⟨iref, hiref⟩ := htarget
    have hiref_active : iref ∈ I.active := hiref.2.1
    have hrefpos : 0 < nonnegativeJetScale u (I.value iref) := by
      exact selectedIntrinsicCentersNatIndexing_value_pos hε s hdis iref hiref_active
    let q : Fin (Besicovitch.multiplicity (Fin n → ℝ)) → Set ℕ := fun color =>
      {i | i ∈ target ∧ ∃ z, z ∈ s color ∧ z.1 = I.value i}
    have htarget_union : target = ⋃ color, q color := by
      apply Set.Subset.antisymm
      · intro i hi
        have himem := I.value_mem i hi.2.1
        obtain ⟨z, hzunion, hzval⟩ := himem
        simp only [Set.mem_iUnion] at hzunion ⊢
        obtain ⟨color, hzcolor⟩ := hzunion
        exact ⟨color, hi, z, hzcolor, hzval⟩
      · intro i hi
        simp only [Set.mem_iUnion] at hi
        obtain ⟨color, hitarget, z, hzcolor, hzval⟩ := hi
        exact hitarget
    have hq (color : Fin (Besicovitch.multiplicity (Fin n → ℝ))) :
        (q color).ncard ≤ Bcolor := by
      have hqfinite : (q color).Finite := t.finite_toSet.subset (by
        intro i hi
        exact hi.1.1)
      let F : q color → {z : Fin n → ℝ // 0 < nonnegativeJetScale u z} := fun i =>
        ⟨I.value i.1,
          selectedIntrinsicCentersNatIndexing_value_pos hε s hdis i.1 i.2.1.2.1⟩
      have hFinj : Function.Injective F := by
        intro i j hij
        apply Subtype.ext
        apply I.value_injOn i.2.1.2.1 j.2.1.2.1
        exact congr_arg Subtype.val hij
      letI : Finite (q color) := hqfinite
      letI : Fintype (q color) := Fintype.ofFinite (q color)
      let selected : Finset {z : Fin n → ℝ // 0 < nonnegativeJetScale u z} :=
        Finset.univ.image F
      have hselected_mem (z : {z : Fin n → ℝ // 0 < nonnegativeJetScale u z})
          (hz : z ∈ selected) : z ∈ s color := by
        simp only [selected, Finset.mem_image, Finset.mem_univ, true_and] at hz
        obtain ⟨i, rfl⟩ := hz
        obtain ⟨w, hwcolor, hwval⟩ := i.2.2
        have hFw : F i = w := by
          apply Subtype.ext
          exact hwval.symm
        simpa [hFw] using hwcolor
      have hmeet (z : {z : Fin n → ℝ // 0 < nonnegativeJetScale u z})
          (hz : z ∈ selected) :
          x ∈ Metric.ball z.1 (D * (ε * nonnegativeJetScale u z.1)) := by
        simp only [selected, Finset.mem_image, Finset.mem_univ, true_and] at hz
        obtain ⟨i, rfl⟩ := hz
        exact i.2.1.2.2
      have hcomp (z : {z : Fin n → ℝ // 0 < nonnegativeJetScale u z})
          (hz : z ∈ selected) :
          nonnegativeJetScale u z.1 ≤ C * nonnegativeJetScale u (I.value iref) ∧
            nonnegativeJetScale u (I.value iref) ≤ C * nonnegativeJetScale u z.1 := by
        exact intrinsicScale_comparable_of_common_scaled_balls hD hε hsmall hvar z.2
          hrefpos (hmeet z hz) hiref.2.2
      have hselected_disjoint :
          ((selected : Finset {z : Fin n → ℝ // 0 < nonnegativeJetScale u z}) :
            Set {z : Fin n → ℝ // 0 < nonnegativeJetScale u z}).PairwiseDisjoint
              fun z => Metric.closedBall z.1 (ε * nonnegativeJetScale u z.1) := by
        intro z hz w hw hzw
        exact hdis color (hselected_mem z hz) (hselected_mem w hw) hzw
      have hb := intrinsicColorCardBound_spec n hD hC hε hrefpos selected
        hmeet hcomp hselected_disjoint
      have hcard : selected.card = (q color).ncard := by
        dsimp [selected]
        rw [Finset.card_image_of_injective _ hFinj]
        rw [Finset.card_univ]
        rw [← Nat.card_eq_fintype_card]
        exact Nat.card_coe_set_eq (q color)
      rw [hcard] at hb
      exact hb
    change target.ncard ≤ _
    rw [htarget_union]
    simpa [intrinsicOverlapBound, Bcolor] using ncard_iUnion_le_mul_of_uniform q hq
  · have hempty : target = ∅ := Set.not_nonempty_iff_eq_empty.mp htarget
    change target.ncard ≤ _
    simp [hempty]

/-- The radius-two ball at an active center, and the empty set at an inactive index. -/
def activeScaledBall {E : Type*} [PseudoMetricSpace E] (R : E → ℝ)
    (center : ℕ → E) (active : Set ℕ) (ε : ℝ) (i : ℕ) : Set E :=
  by
    classical
    exact if i ∈ active then Metric.ball (center i) (2 * (ε * R (center i))) else ∅

/-- Point-finiteness for a slightly larger dilation implies local finiteness of radius-two
balls at every positive-scale point. Slow variation supplies the missing scale comparison. -/
theorem activeScaledBall_locallyFiniteAt_of_pointFinite {E : Type*}
    [PseudoMetricSpace E] (R : E → ℝ) (center : ℕ → E) (active : Set ℕ)
    {c C L ε : ℝ} (hC : 1 ≤ C) (hL : C + 2 < L) (hε : 0 < ε)
    (hsmall : 3 * ε ≤ c) (hcenter : ∀ i, i ∈ active → 0 < R (center i))
    (hvar : ∀ x y, dist x y ≤ c * R x → R x ≤ C * R y ∧ R y ≤ C * R x)
    (hpoint : ∀ x, Set.Finite {i | i ∈ active ∧
      x ∈ Metric.ball (center i) (L * (ε * R (center i)))}) :
    ∀ x, 0 < R x → ∃ V ∈ 𝓝 x,
      Set.Finite {i | ((activeScaledBall R center active ε i) ∩ V).Nonempty} := by
  intro x hx
  have hεRx : 0 < ε * R x := mul_pos hε hx
  refine ⟨Metric.ball x (ε * R x), Metric.ball_mem_nhds x hεRx, ?_⟩
  apply (hpoint x).subset
  intro i hi
  obtain ⟨y, hyball, hyx⟩ := hi
  have hiactive : i ∈ active := by
    by_contra hnot
    simp [activeScaledBall, hnot] at hyball
  have hRi : 0 < R (center i) := hcenter i hiactive
  have hycenter : dist (center i) y < 2 * (ε * R (center i)) := by
    have hyball' : y ∈ Metric.ball (center i) (2 * (ε * R (center i))) := by
      simpa [activeScaledBall, hiactive] using hyball
    simpa [dist_comm] using Metric.mem_ball.mp hyball'
  have hyx' : dist y x < ε * R x := Metric.mem_ball.mp hyx
  have hcenterx : dist (center i) x <
      2 * (ε * R (center i)) + ε * R x := by
    exact (dist_triangle (center i) y x).trans_lt (add_lt_add hycenter hyx')
  have hxcomp : R x ≤ C * R (center i) := by
    rcases le_total (R x) (R (center i)) with hxi | hix
    · exact hxi.trans (le_mul_of_one_le_left hRi.le hC)
    · have hdist : dist x (center i) ≤ c * R x := by
        apply LT.lt.le
        rw [dist_comm]
        calc
          dist (center i) x < 2 * (ε * R (center i)) + ε * R x := hcenterx
          _ ≤ 2 * (ε * R x) + ε * R x := by gcongr
          _ = (3 * ε) * R x := by ring
          _ ≤ c * R x := mul_le_mul_of_nonneg_right hsmall hx.le
      exact (hvar x (center i) hdist).1
  refine ⟨hiactive, Metric.mem_ball.mpr ?_⟩
  rw [dist_comm]
  calc
    dist (center i) x < 2 * (ε * R (center i)) + ε * R x := hcenterx
    _ ≤ 2 * (ε * R (center i)) + ε * (C * R (center i)) := by gcongr
    _ = (C + 2) * (ε * R (center i)) := by ring
    _ < L * (ε * R (center i)) :=
      mul_lt_mul_of_pos_right hL (mul_pos hε hRi)

/-- The intrinsic scale is continuous whenever the function is twice continuously
differentiable. -/
theorem continuous_nonnegativeJetScale {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 u) : Continuous (nonnegativeJetScale u) := by
  exact hu.continuous.sqrt.sqrt.max
    ((hu.continuous_iteratedFDeriv (by exact_mod_cast (le_refl 2))).norm.sqrt)

/-- The positive intrinsic-scale locus is open. -/
theorem isOpen_nonnegativeJetScale_pos {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 u) : IsOpen {x | 0 < nonnegativeJetScale u x} := by
  exact isOpen_lt continuous_const (continuous_nonnegativeJetScale hu)

/-- Every point in the support of a normalized nonnegative function has positive intrinsic
scale. -/
theorem support_subset_nonnegativeJetScale_pos {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u) :
    Function.support u ⊆ {x | 0 < nonnegativeJetScale u x} := by
  intro x hx
  have hux : 0 < u x := lt_of_le_of_ne (hu.nonnegative x) (Ne.symm hx)
  exact (Real.sqrt_pos.2 (Real.sqrt_pos.2 hux)).trans_le
    (sqrt_sqrt_le_nonnegativeJetScale u x)

/-- The fixed smooth bump profile that is one on the unit ball and supported in the radius-two
ball. All rescaled cutoffs in the quantitative cover can be built from this profile. -/
def unitScaleBump (n : ℕ) : ContDiffBump (0 : Fin n → ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩
/-- The fixed profile whose rescalings are the squared raw summands in the normalization
denominator. -/
def unitScaleBumpSquare (n : ℕ) : (Fin n → ℝ) → ℝ :=
  fun x => (unitScaleBump n x) ^ 2

/-- In each fixed dimension, the unit-scale bump and all its derivatives through order six have
one common finite bound. -/
theorem unitScaleBump_uniform_deriv_bound (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ j, j ≤ 6 → ∀ x,
      ‖iteratedFDeriv ℝ j (unitScaleBump n) x‖ ≤ A := by
  have hbound : ∀ j : ℕ, ∃ M : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ j (unitScaleBump n) x‖ ≤ M := by
    intro j
    have hbdd : BddAbove (Set.range fun x =>
        ‖iteratedFDeriv ℝ j (unitScaleBump n) x‖) := by
      apply (((unitScaleBump n).contDiff.continuous_iteratedFDeriv
        (by exact_mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport)
      apply HasCompactSupport.comp_left _ norm_zero
      exact (unitScaleBump n).hasCompactSupport.iteratedFDeriv j
    rcases hbdd with ⟨M, hM⟩
    exact ⟨M, fun x => hM (Set.mem_range_self x)⟩
  choose M hM using hbound
  let A := max (((Finset.range 7).image M).max' (by simp)) 1
  refine ⟨A, le_max_right _ _, ?_⟩
  intro j hj x
  exact (hM j x).trans <| (Finset.le_max'
    ((Finset.range 7).image M) (M j) (Finset.mem_image_of_mem M
      (by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hj))).trans
        (le_max_left _ _)

/-- In each fixed dimension, the squared unit-scale profile and all its derivatives through
order six have one common finite bound. -/
theorem unitScaleBumpSquare_uniform_deriv_bound (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ j, j ≤ 6 → ∀ x,
      ‖iteratedFDeriv ℝ j (unitScaleBumpSquare n) x‖ ≤ A := by
  have hcompactMul := HasCompactSupport.mul_left
    (f := (unitScaleBump n : (Fin n → ℝ) → ℝ))
    (unitScaleBump n).hasCompactSupport
  have hcompactEq : unitScaleBumpSquare n =
      (unitScaleBump n : (Fin n → ℝ) → ℝ) * unitScaleBump n := by
    funext x
    simp [unitScaleBumpSquare, pow_two]
  have hcompact := hcompactEq.symm ▸ hcompactMul
  have hbound : ∀ j : ℕ, ∃ M : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ j (unitScaleBumpSquare n) x‖ ≤ M := by
    intro j
    have hsmooth : ContDiff ℝ j (unitScaleBumpSquare n) := by
      have hunit : ContDiff ℝ j (unitScaleBump n) := (unitScaleBump n).contDiff
      unfold unitScaleBumpSquare
      exact hunit.pow 2
    have hbdd : BddAbove (Set.range fun x =>
        ‖iteratedFDeriv ℝ j (unitScaleBumpSquare n) x‖) := by
      apply (hsmooth.continuous_iteratedFDeriv
        (by exact_mod_cast le_rfl)).norm.bddAbove_range_of_hasCompactSupport
      apply HasCompactSupport.comp_left _ norm_zero
      exact hcompact.iteratedFDeriv j
    rcases hbdd with ⟨M, hM⟩
    exact ⟨M, fun x => hM (Set.mem_range_self x)⟩
  choose M hM using hbound
  let A := max (((Finset.range 7).image M).max' (by simp)) 1
  refine ⟨A, le_max_right _ _, ?_⟩
  intro j hj x
  exact (hM j x).trans <| (Finset.le_max'
    ((Finset.range 7).image M) (M j) (Finset.mem_image_of_mem M
      (by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hj))).trans
        (le_max_left _ _)


/-- Translate and rescale the fixed bump profile to a center and radius. -/
def rescaledUnitBump {n : ℕ} (c : Fin n → ℝ) (r : ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => unitScaleBump n (r⁻¹ • (x - c))

/-- Every translated and rescaled unit bump is `C⁶`. -/
theorem rescaledUnitBump_contDiff {n : ℕ} (c : Fin n → ℝ) (r : ℝ) :
    ContDiff ℝ 6 (rescaledUnitBump c r) := by
  change ContDiff ℝ 6 (fun x => unitScaleBump n (r⁻¹ • (x - c)))
  exact (unitScaleBump n).contDiff.comp (by fun_prop)

/-- Translation and inverse-radius rescaling transfer any uniform profile derivative
bound into its scale-invariant form. -/
theorem rescaledFunction_scaled_deriv_bound {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {A : ℝ} (hf : ContDiff ℝ 6 f)
    (hA : ∀ j, j ≤ 6 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (j : ℕ) (hj : j ≤ 6)
    (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (fun z => f (r⁻¹ • (z - c))) x‖ * r ^ j ≤ A := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    r⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  let g : (Fin n → ℝ) → ℝ := f ∘ L
  have hfun : (fun z => f (r⁻¹ • (z - c))) = fun z => g (z - c) := by
    funext z
    rfl
  rw [hfun, iteratedFDeriv_comp_sub]
  have hcomp : iteratedFDeriv ℝ j g (x - c) =
      (iteratedFDeriv ℝ j f (L (x - c))).compContinuousLinearMap
        (fun _ => L) :=
    L.iteratedFDeriv_comp_right hf (x - c) (by exact_mod_cast hj)
  rw [hcomp]
  have hA0 : 0 ≤ A := by
    exact (norm_nonneg (iteratedFDeriv ℝ 0 f 0)).trans
      (hA 0 (by norm_num) 0)
  have hnormL : ‖L‖ ≤ r⁻¹ := by
    calc
      ‖L‖ ≤ ‖r⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ := by
        exact norm_smul_le (r⁻¹ : ℝ) (ContinuousLinearMap.id ℝ (Fin n → ℝ))
      _ ≤ r⁻¹ * 1 := by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        gcongr
        exact ContinuousLinearMap.norm_id_le
      _ = r⁻¹ := mul_one _
  have hprod : (∏ _ : Fin j, ‖L‖) ≤ (r⁻¹) ^ j := by
    calc
      (∏ _ : Fin j, ‖L‖) ≤ ∏ _ : Fin j, r⁻¹ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg L) (fun _ _ => hnormL)
      _ = (r⁻¹) ^ j := by simp
  calc
    ‖(iteratedFDeriv ℝ j f (L (x - c))).compContinuousLinearMap
          (fun _ => L)‖ * r ^ j
        ≤ (‖iteratedFDeriv ℝ j f (L (x - c))‖ *
          ∏ _ : Fin j, ‖L‖) * r ^ j := by
            gcongr
            exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (A * ∏ _ : Fin j, ‖L‖) * r ^ j := by
      gcongr
      exact hA j hj _
    _ ≤ (A * (r⁻¹) ^ j) * r ^ j := by gcongr
    _ = A := by
      rw [inv_pow]
      field_simp


/-- Rescaling the fixed profile gives exactly the radius powers required by the quantitative
cover interface. The proof also covers the zero-dimensional ambient space. -/
theorem rescaledUnitBump_scaled_deriv_bound {n : ℕ} {A : ℝ}
    (hA : ∀ j, j ≤ 6 → ∀ x, ‖iteratedFDeriv ℝ j (unitScaleBump n) x‖ ≤ A)
    (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (j : ℕ) (hj : j ≤ 6)
    (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (rescaledUnitBump c r) x‖ * r ^ j ≤ A := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    r⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  let g : (Fin n → ℝ) → ℝ := (unitScaleBump n) ∘ L
  have hbase : ContDiff ℝ 6 (unitScaleBump n) := (unitScaleBump n).contDiff
  have hfun : rescaledUnitBump c r = fun z => g (z - c) := by
    funext z
    rfl
  rw [hfun, iteratedFDeriv_comp_sub]
  have hcomp : iteratedFDeriv ℝ j g (x - c) =
      (iteratedFDeriv ℝ j (unitScaleBump n) (L (x - c))).compContinuousLinearMap
        (fun _ => L) :=
    L.iteratedFDeriv_comp_right hbase (x - c) (by exact_mod_cast hj)
  rw [hcomp]
  have hA0 : 0 ≤ A := by
    exact (norm_nonneg (iteratedFDeriv ℝ 0 (unitScaleBump n) 0)).trans
      (hA 0 (by norm_num) 0)
  have hnormL : ‖L‖ ≤ r⁻¹ := by
    calc
      ‖L‖ ≤ ‖r⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ := by
        exact norm_smul_le (r⁻¹ : ℝ) (ContinuousLinearMap.id ℝ (Fin n → ℝ))
      _ ≤ r⁻¹ * 1 := by
        rw [Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        gcongr
        exact ContinuousLinearMap.norm_id_le
      _ = r⁻¹ := mul_one _
  have hprod : (∏ _ : Fin j, ‖L‖) ≤ (r⁻¹) ^ j := by
    calc
      (∏ _ : Fin j, ‖L‖) ≤ ∏ _ : Fin j, r⁻¹ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg L) (fun _ _ => hnormL)
      _ = (r⁻¹) ^ j := by simp
  calc
    ‖(iteratedFDeriv ℝ j (unitScaleBump n) (L (x - c))).compContinuousLinearMap
          (fun _ => L)‖ * r ^ j
        ≤ (‖iteratedFDeriv ℝ j (unitScaleBump n) (L (x - c))‖ *
          ∏ _ : Fin j, ‖L‖) * r ^ j := by
            gcongr
            exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ (A * ∏ _ : Fin j, ‖L‖) * r ^ j := by
      gcongr
      exact hA j hj _
    _ ≤ (A * (r⁻¹) ^ j) * r ^ j := by gcongr
    _ = A := by
      rw [inv_pow]
      field_simp

/-- The rescaled function is the standard `ContDiffBump` with inner radius `r` and outer
radius `2r`. -/
def centeredScaleBump {n : ℕ} (c : Fin n → ℝ) (r : ℝ) (hr : 0 < r) :
    ContDiffBump c := ⟨r, 2 * r, hr, by linarith⟩

theorem centeredScaleBump_eq_rescaledUnitBump {n : ℕ} (c : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (centeredScaleBump c r hr : (Fin n → ℝ) → ℝ) = rescaledUnitBump c r := by
  funext x
  simp [centeredScaleBump, rescaledUnitBump, unitScaleBump, ContDiffBump.toFun, hr.ne']

/-- The rescaled bump has exactly the desired radius-two open-ball support. -/
theorem support_rescaledUnitBump {n : ℕ} (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    Function.support (rescaledUnitBump c r) = Metric.ball c (2 * r) := by
  rw [← centeredScaleBump_eq_rescaledUnitBump c hr]
  exact (centeredScaleBump c r hr).support_eq

/-- The rescaled bump equals one throughout its inner closed ball. -/
theorem rescaledUnitBump_eq_one {n : ℕ} (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    {x : Fin n → ℝ} (hx : x ∈ Metric.closedBall c r) :
    rescaledUnitBump c r x = 1 := by
  rw [← centeredScaleBump_eq_rescaledUnitBump c hr]
  exact (centeredScaleBump c r hr).one_of_mem_closedBall hx

/-- Every rescaled unit bump takes values in `[0,1]`. -/
theorem rescaledUnitBump_mem_Icc {n : ℕ} (c : Fin n → ℝ) (r : ℝ)
    (x : Fin n → ℝ) :
    0 ≤ rescaledUnitBump c r x ∧ rescaledUnitBump c r x ≤ 1 := by
  exact ⟨(unitScaleBump n).nonneg, (unitScaleBump n).le_one⟩

/-- Rescaled unit bumps at active intrinsic centers, extended by zero on inactive indices. -/
def activeIntrinsicRawBump {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (center : ℕ → (Fin n → ℝ)) (active : Set ℕ) (ε : ℝ)
    (i : ℕ) : (Fin n → ℝ) → ℝ := by
  classical
  exact if i ∈ active then
    rescaledUnitBump (center i) (ε * nonnegativeJetScale u (center i)) else 0

theorem activeIntrinsicRawBump_eq_zero_of_not_active {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε : ℝ} {i : ℕ} (hi : i ∉ active) :
    activeIntrinsicRawBump u center active ε i = 0 := by
  simp [activeIntrinsicRawBump, hi]

/-- Every raw bump is smooth, including the inactive zero functions. -/
theorem activeIntrinsicRawBump_contDiff {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε : ℝ} (i : ℕ) :
    ContDiff ℝ 6 (activeIntrinsicRawBump u center active ε i) := by
  classical
  by_cases hi : i ∈ active
  · simp only [activeIntrinsicRawBump, ite_eq_left hi]
    exact rescaledUnitBump_contDiff _ _
  · rw [activeIntrinsicRawBump_eq_zero_of_not_active hi]
    exact contDiff_const

/-- The support of an active raw bump is exactly its radius-two ball. -/
theorem support_activeIntrinsicRawBump {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε : ℝ} (hε : 0 < ε)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    (i : ℕ) :
    Function.support (activeIntrinsicRawBump u center active ε i) =
      activeScaledBall (nonnegativeJetScale u) center active ε i := by
  classical
  by_cases hi : i ∈ active
  · simp only [activeIntrinsicRawBump, activeScaledBall, ite_eq_left hi]
    exact support_rescaledUnitBump _ (mul_pos hε (hcenter i hi))
  · simp [activeIntrinsicRawBump, activeScaledBall, hi, Function.support]

/-- Every iterated derivative of a raw bump is supported in the closed outer ball. -/
theorem support_iteratedFDeriv_activeIntrinsicRawBump_subset_closedBall {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε : ℝ} (hε : 0 < ε)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    (i j : ℕ) :
    Function.support (iteratedFDeriv ℝ j
      (activeIntrinsicRawBump u center active ε i)) ⊆
      Metric.closedBall (center i) (2 * (ε * nonnegativeJetScale u (center i))) := by
  intro x hx
  have hsupp := support_iteratedFDeriv_subset j hx
  rw [tsupport, support_activeIntrinsicRawBump hε hcenter i] at hsupp
  by_cases hi : i ∈ active
  · have heq : activeScaledBall (nonnegativeJetScale u) center active ε i =
        Metric.ball (center i) (2 * (ε * nonnegativeJetScale u (center i))) := by
      simp [activeScaledBall, hi]
    rw [heq] at hsupp
    exact Metric.closure_ball_subset_closedBall hsupp
  · simp [activeScaledBall, hi] at hsupp

/-- A nonzero iterated derivative of an active raw bump lies in any fixed enlargement
from its closed radius-two support; radius three is used for scale comparison. -/
theorem iteratedFDeriv_activeIntrinsicRawBump_ne_zero_mem_three_ball {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε : ℝ} (hε : 0 < ε)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    {i j : ℕ} (hi : i ∈ active) {x : Fin n → ℝ}
    (hderiv : iteratedFDeriv ℝ j
      (activeIntrinsicRawBump u center active ε i) x ≠ 0) :
    x ∈ Metric.ball (center i) (3 * (ε * nonnegativeJetScale u (center i))) := by
  have hclosed := support_iteratedFDeriv_activeIntrinsicRawBump_subset_closedBall
    hε hcenter i j hderiv
  exact Metric.closedBall_subset_ball (by
    exact mul_lt_mul_of_pos_right (by norm_num)
      (mul_pos hε (hcenter i hi))) hclosed


/-- Active raw bumps inherit the uniform scaled derivative bound of the unit profile. -/
theorem activeIntrinsicRawBump_scaled_deriv_bound {n : ℕ} {A : ℝ}
    (hA : ∀ j, j ≤ 6 → ∀ x,
      ‖iteratedFDeriv ℝ j (unitScaleBump n) x‖ ≤ A)
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε : ℝ} (hε : 0 < ε)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    (i : ℕ) (hi : i ∈ active) (j : ℕ) (hj : j ≤ 6) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (activeIntrinsicRawBump u center active ε i) x‖ *
        (ε * nonnegativeJetScale u (center i)) ^ j ≤ A := by
  classical
  rw [show activeIntrinsicRawBump u center active ε i =
      rescaledUnitBump (center i) (ε * nonnegativeJetScale u (center i)) by
    simp [activeIntrinsicRawBump, hi]]
  exact rescaledUnitBump_scaled_deriv_bound hA (center i)
    (mul_pos hε (hcenter i hi)) j hj x

/-- Squared active raw bumps inherit scale-invariant derivative bounds from the squared
unit profile. -/
theorem activeIntrinsicRawBump_sq_scaled_deriv_bound {n : ℕ} {A : ℝ}
    (hA : ∀ j, j ≤ 6 → ∀ x,
      ‖iteratedFDeriv ℝ j (unitScaleBumpSquare n) x‖ ≤ A)
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε : ℝ} (hε : 0 < ε)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    (i : ℕ) (hi : i ∈ active) (j : ℕ) (hj : j ≤ 6) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j
        (fun y => activeIntrinsicRawBump u center active ε i y ^ 2) x‖ *
      (ε * nonnegativeJetScale u (center i)) ^ j ≤ A := by
  let r := ε * nonnegativeJetScale u (center i)
  have hr : 0 < r := mul_pos hε (hcenter i hi)
  have hsmooth : ContDiff ℝ 6 (unitScaleBumpSquare n) := by
    have hunit : ContDiff ℝ 6 (unitScaleBump n) := (unitScaleBump n).contDiff
    unfold unitScaleBumpSquare
    exact hunit.pow 2
  have heq : (fun y => activeIntrinsicRawBump u center active ε i y ^ 2) =
      fun y => unitScaleBumpSquare n (r⁻¹ • (y - center i)) := by
    funext y
    simp [activeIntrinsicRawBump, hi, rescaledUnitBump, unitScaleBumpSquare, r]
  rw [heq]
  exact rescaledFunction_scaled_deriv_bound hsmooth hA (center i) hr j hj x


/-- Every iterated derivative of a squared raw bump is supported in the same closed outer
ball as the unsquared bump. -/
theorem support_iteratedFDeriv_activeIntrinsicRawBump_sq_subset_closedBall {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε : ℝ} (hε : 0 < ε)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    (i j : ℕ) :
    Function.support (iteratedFDeriv ℝ j
      (fun y => activeIntrinsicRawBump u center active ε i y ^ 2)) ⊆
      Metric.closedBall (center i) (2 * (ε * nonnegativeJetScale u (center i))) := by
  intro x hx
  have hsupp := support_iteratedFDeriv_subset j hx
  rw [tsupport] at hsupp
  have heq : Function.support
      (fun y => activeIntrinsicRawBump u center active ε i y ^ 2) =
      Function.support (activeIntrinsicRawBump u center active ε i) := by
    ext y
    simp [Function.support]
  rw [heq, support_activeIntrinsicRawBump hε hcenter i] at hsupp
  by_cases hi : i ∈ active
  · have hball : activeScaledBall (nonnegativeJetScale u) center active ε i =
        Metric.ball (center i) (2 * (ε * nonnegativeJetScale u (center i))) := by
      simp [activeScaledBall, hi]
    rw [hball] at hsupp
    exact Metric.closure_ball_subset_closedBall hsupp
  · simp [activeScaledBall, hi] at hsupp


/-- Quantitative overlap bounds the number of nonzero squared-bump derivative terms at
each point, using any dilation strictly larger than two. -/
theorem activeIntrinsicRawBump_sq_deriv_ncard_le {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε D : ℝ} {B : ℕ} (hD : 2 < D) (hε : 0 < ε)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    (hoverlap : ∀ x (t : Finset ℕ), Set.ncard {i | i ∈ t ∧ i ∈ active ∧
      x ∈ Metric.ball (center i) (D * (ε * nonnegativeJetScale u (center i)))} ≤ B)
    (j : ℕ) (x : Fin n → ℝ) :
    Set.ncard {i | iteratedFDeriv ℝ j
      (fun y => activeIntrinsicRawBump u center active ε i y ^ 2) x ≠ 0} ≤ B := by
  refine ncard_le_of_uniform_finset_ncard_le (B := B) ?_
  intro t
  let target : Set ℕ := {i | i ∈ t ∧ i ∈ active ∧
    x ∈ Metric.ball (center i) (D * (ε * nonnegativeJetScale u (center i)))}
  have htarget : target.Finite := t.finite_toSet.subset fun i hi => hi.1
  have hsubset : {i | i ∈ t ∧ iteratedFDeriv ℝ j
      (fun y => activeIntrinsicRawBump u center active ε i y ^ 2) x ≠ 0} ⊆ target := by
    intro i hi
    have hiactive : i ∈ active := by
      by_contra hnot
      have hzero : (fun y => activeIntrinsicRawBump u center active ε i y ^ 2) =
          fun _ => 0 := by
        funext y
        simp [activeIntrinsicRawBump_eq_zero_of_not_active hnot]
      have hne := hi.2
      rw [hzero, iteratedFDeriv_fun_zero, Pi.zero_apply] at hne
      exact hne rfl
    have hclosed := support_iteratedFDeriv_activeIntrinsicRawBump_sq_subset_closedBall
      hε hcenter i j hi.2
    have hrpos : 0 < ε * nonnegativeJetScale u (center i) :=
      mul_pos hε (hcenter i hiactive)
    refine ⟨hi.1, hiactive, Metric.closedBall_subset_ball ?_ hclosed⟩
    exact mul_lt_mul_of_pos_right hD hrpos
  exact (Set.ncard_le_ncard hsubset htarget).trans (hoverlap x t)


/-- The selected indexed raw family contains a bump equal to one at every positive-scale point. -/
theorem exists_selectedIntrinsicRawBump_eq_one {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1))
    (hcover : Set.range (fun x : {x : Fin n → ℝ // 0 < nonnegativeJetScale u x} => x.1) ⊆
      ⋃ color, ⋃ z ∈ s color,
        Metric.ball z.1 (ε * nonnegativeJetScale u z.1))
    {x : Fin n → ℝ} (hx : 0 < nonnegativeJetScale u x) :
    ∃ i, i ∈ (selectedIntrinsicCentersNatIndexing hε s hdis).active ∧
      activeIntrinsicRawBump u (selectedIntrinsicCentersNatIndexing hε s hdis).value
        (selectedIntrinsicCentersNatIndexing hε s hdis).active ε i x = 1 := by
  have hindexed := selectedIntrinsicCentersNatIndexing_cover hε s hdis hcover hx
  simp only [Set.mem_iUnion] at hindexed
  obtain ⟨i, hi, hxball⟩ := hindexed
  refine ⟨i, hi, ?_⟩
  simp only [activeIntrinsicRawBump, ite_eq_left hi]
  apply rescaledUnitBump_eq_one _
    (mul_pos hε (selectedIntrinsicCentersNatIndexing_value_pos hε s hdis i hi))
  exact Metric.ball_subset_closedBall hxball


/-- Finite-subfamily overlap of dilated balls gives point-finiteness of the raw bumps. -/
theorem activeIntrinsicRawBump_pointFinite {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε D : ℝ} {B : ℕ} (hD : 2 ≤ D) (hε : 0 < ε)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    (hoverlap : ∀ x (t : Finset ℕ), Set.ncard {i | i ∈ t ∧ i ∈ active ∧
      x ∈ Metric.ball (center i) (D * (ε * nonnegativeJetScale u (center i)))} ≤ B) :
    ∀ x, Set.Finite {i | activeIntrinsicRawBump u center active ε i x ≠ 0} := by
  intro x
  refine finite_of_uniform_finset_ncard_le (B := B) ?_
  intro t
  let target : Set ℕ := {i | i ∈ t ∧ i ∈ active ∧
    x ∈ Metric.ball (center i) (D * (ε * nonnegativeJetScale u (center i)))}
  have htarget : target.Finite := t.finite_toSet.subset fun i hi => hi.1
  have hsubset : {i | i ∈ t ∧
      activeIntrinsicRawBump u center active ε i x ≠ 0} ⊆ target := by
    intro i hi
    have hiactive : i ∈ active := by
      by_contra hnot
      exact hi.2 (by rw [activeIntrinsicRawBump_eq_zero_of_not_active hnot]; rfl)
    have hsupp : x ∈ activeScaledBall (nonnegativeJetScale u) center active ε i := by
      rw [← support_activeIntrinsicRawBump hε hcenter i]
      exact hi.2
    have hball2 : x ∈ Metric.ball (center i)
        (2 * (ε * nonnegativeJetScale u (center i))) := by
      simpa [activeScaledBall, hiactive] using hsupp
    refine ⟨hi.1, hiactive, Metric.ball_subset_ball ?_ hball2⟩
    exact mul_le_mul_of_nonneg_right hD (mul_pos hε (hcenter i hiactive)).le
  exact (Set.ncard_le_ncard hsubset htarget).trans (hoverlap x t)

/-- Quantitative overlap bounds the full pointwise support cardinality of the raw bump
family by the same constant. -/
theorem activeIntrinsicRawBump_ncard_le {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε D : ℝ} {B : ℕ} (hD : 2 ≤ D) (hε : 0 < ε)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    (hoverlap : ∀ x (t : Finset ℕ), Set.ncard {i | i ∈ t ∧ i ∈ active ∧
      x ∈ Metric.ball (center i) (D * (ε * nonnegativeJetScale u (center i)))} ≤ B) :
    ∀ x, Set.ncard {i | activeIntrinsicRawBump u center active ε i x ≠ 0} ≤ B := by
  intro x
  refine ncard_le_of_uniform_finset_ncard_le (B := B) ?_
  intro t
  let target : Set ℕ := {i | i ∈ t ∧ i ∈ active ∧
    x ∈ Metric.ball (center i) (D * (ε * nonnegativeJetScale u (center i)))}
  have htarget : target.Finite := t.finite_toSet.subset fun i hi => hi.1
  have hsubset : {i | i ∈ t ∧
      activeIntrinsicRawBump u center active ε i x ≠ 0} ⊆ target := by
    intro i hi
    have hiactive : i ∈ active := by
      by_contra hnot
      exact hi.2 (by rw [activeIntrinsicRawBump_eq_zero_of_not_active hnot]; rfl)
    have hsupp : x ∈ activeScaledBall (nonnegativeJetScale u) center active ε i := by
      rw [← support_activeIntrinsicRawBump hε hcenter i]
      exact hi.2
    have hball2 : x ∈ Metric.ball (center i)
        (2 * (ε * nonnegativeJetScale u (center i))) := by
      simpa [activeScaledBall, hiactive] using hsupp
    refine ⟨hi.1, hiactive, Metric.ball_subset_ball ?_ hball2⟩
    exact mul_le_mul_of_nonneg_right hD
      (mul_pos hε (hcenter i hiactive)).le
  exact (Set.ncard_le_ncard hsubset htarget).trans (hoverlap x t)


/-- Every active-or-zero raw bump takes values in `[0,1]`. -/
theorem activeIntrinsicRawBump_mem_Icc {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)}
    {active : Set ℕ} {ε : ℝ} (i : ℕ) (x : Fin n → ℝ) :
    0 ≤ activeIntrinsicRawBump u center active ε i x ∧
      activeIntrinsicRawBump u center active ε i x ≤ 1 := by
  classical
  by_cases hi : i ∈ active
  · simpa [activeIntrinsicRawBump, hi] using
      rescaledUnitBump_mem_Icc (center i) (ε * nonnegativeJetScale u (center i)) x
  · simp [activeIntrinsicRawBump, hi]
/-- Pointwise square normalization of a countable family.  This is the algebraic
normalization used to turn a locally finite raw bump cover into a square partition. -/
def squareNormalizedFamily {X : Type*} (bump : ℕ → X → ℝ) (i : ℕ) (x : X) : ℝ :=
  bump i x / Real.sqrt (∑' k, bump k x ^ 2)


/-- A locally finite family of smooth functions has a smooth pointwise `tsum` at the
point in question. The proof replaces the series by one finite sum on a neighborhood. -/
theorem contDiffAt_tsum_of_support_locallyFiniteAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : ℕ∞} {f : ℕ → E → F} {x : E}
    (hf : ∀ i, ContDiff ℝ N (f i))
    (hloc : ∃ V ∈ 𝓝 x, Set.Finite {i | (Function.support (f i) ∩ V).Nonempty}) :
    ContDiffAt ℝ N (fun y => ∑' i, f i y) x := by
  obtain ⟨V, hV, hfinite⟩ := hloc
  let indices : Finset ℕ := hfinite.toFinset
  have hsmooth : ContDiff ℝ N (fun y => ∑ i ∈ indices, f i y) := by
    fun_prop
  refine hsmooth.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hV] with y hy
  rw [tsum_eq_sum]
  intro i hi
  have hinonempty : ¬(Function.support (f i) ∩ V).Nonempty := by
    simpa [indices] using hi
  by_contra hfiy
  exact hinonempty ⟨y, hfiy, hy⟩

/-- At a locally finite point, iterated differentiation commutes with the pointwise
countable sum. Both sides reduce to the same finite sum on a neighborhood. -/
theorem iteratedFDeriv_tsum_of_support_locallyFiniteAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {N : ℕ∞} {f : ℕ → E → F} {x : E} {j : ℕ}
    (hf : ∀ i, ContDiff ℝ N (f i))
    (hloc : ∃ V ∈ 𝓝 x, Set.Finite {i | (Function.support (f i) ∩ V).Nonempty})
    (hj : j ≤ N) :
    iteratedFDeriv ℝ j (fun y => ∑' i, f i y) x =
      ∑' i, iteratedFDeriv ℝ j (f i) x := by
  obtain ⟨V, hV, hfinite⟩ := hloc
  let indices : Finset ℕ := hfinite.toFinset
  have heq : (fun y => ∑' i, f i y) =ᶠ[𝓝 x] fun y => ∑ i ∈ indices, f i y := by
    filter_upwards [hV] with y hy
    rw [tsum_eq_sum]
    intro i hi
    have hinonempty : ¬(Function.support (f i) ∩ V).Nonempty := by
      simpa [indices] using hi
    by_contra hfiy
    exact hinonempty ⟨y, hfiy, hy⟩
  have hderiv := (heq.iteratedFDeriv ℝ j).eq_of_nhds
  rw [iteratedFDeriv_sum
    (fun i hi => (hf i).of_le (by exact_mod_cast hj))] at hderiv
  rw [tsum_eq_sum (s := indices)]
  · simpa using hderiv
  · intro i hi
    have hinonempty : ¬(Function.support (f i) ∩ V).Nonempty := by
      simpa [indices] using hi
    have hzero : f i =ᶠ[𝓝 x] 0 := by
      filter_upwards [hV] with y hy
      by_contra hfiy
      exact hinonempty ⟨y, hfiy, hy⟩
    have hderivzero := (hzero.iteratedFDeriv ℝ j).eq_of_nhds
    have hzeroiter : iteratedFDeriv ℝ j (0 : E → F) = 0 := by
      rw [show (0 : E → F) = (fun _ => 0) by rfl]
      exact iteratedFDeriv_fun_zero
    rw [hzeroiter] at hderivzero
    exact hderivzero


/-- The local square sum of a smooth, locally finite family is smooth. -/
theorem contDiffAt_rawSquareTsum_of_support_locallyFiniteAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ∞} {bump : ℕ → E → ℝ} {x : E}
    (hsmooth : ∀ i, ContDiff ℝ N (bump i))
    (hloc : ∃ V ∈ 𝓝 x,
      Set.Finite {i | (Function.support (bump i) ∩ V).Nonempty}) :
    ContDiffAt ℝ N (fun y => ∑' i, bump i y ^ 2) x := by
  apply contDiffAt_tsum_of_support_locallyFiniteAt (f := fun i y => bump i y ^ 2)
  · intro i
    exact (hsmooth i).pow 2
  · obtain ⟨V, hV, hfinite⟩ := hloc
    refine ⟨V, hV, hfinite.subset ?_⟩
    intro i hi
    exact hi.mono (Set.inter_subset_inter_left V fun y hy => by
      change bump i y ≠ 0
      intro hzero
      exact hy (by simp [hzero]))
/-- Square normalization is smooth at every locally finite point where the raw square sum
is positive. -/
theorem squareNormalizedFamily_contDiffAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ∞} {bump : ℕ → E → ℝ} {x : E}
    (hsmooth : ∀ i, ContDiff ℝ N (bump i))
    (hloc : ∃ V ∈ 𝓝 x,
      Set.Finite {i | (Function.support (bump i) ∩ V).Nonempty})
    (hpos : 0 < ∑' i, bump i x ^ 2) (i : ℕ) :
    ContDiffAt ℝ N (squareNormalizedFamily bump i) x := by
  have hsum := contDiffAt_rawSquareTsum_of_support_locallyFiniteAt hsmooth hloc
  have hsqrt := hsum.sqrt hpos.ne'
  have hsqrt_ne : Real.sqrt (∑' k, bump k x ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  exact (hsmooth i).contDiffAt.div hsqrt hsqrt_ne

/-- Local finiteness and positivity on a locus, together with local vanishing off that
locus, make every square-normalized member globally smooth. -/
theorem squareNormalizedFamily_contDiff_of_locallyFiniteOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ∞} {bump : ℕ → E → ℝ} (P : E → Prop)
    (hsmooth : ∀ i, ContDiff ℝ N (bump i))
    (hloc : ∀ x, P x → ∃ V ∈ 𝓝 x,
      Set.Finite {i | (Function.support (bump i) ∩ V).Nonempty})
    (hpos : ∀ x, P x → 0 < ∑' i, bump i x ^ 2)
    (hzero : ∀ i x, ¬P x → bump i =ᶠ[𝓝 x] 0) (i : ℕ) :
    ContDiff ℝ N (squareNormalizedFamily bump i) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : P x
  · exact squareNormalizedFamily_contDiffAt hsmooth (hloc x hx) (hpos x hx) i
  · have hconst : ContDiffAt ℝ N (fun _ : E => (0 : ℝ)) x := contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [hzero i x hx] with y hy
    change bump i y = 0 at hy
    simp [squareNormalizedFamily, hy]

/-- At a zero-scale point, every fixed active raw bump vanishes on a neighborhood, provided
its outer radius is smaller than the slow-variation radius. -/
theorem activeIntrinsicRawBump_eventuallyEq_zero_of_scale_eq_zero {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {center : ℕ → (Fin n → ℝ)} {active : Set ℕ}
    {c C ε : ℝ} (hε : 0 < ε) (houter : 2 * ε < c)
    (hcenter : ∀ i, i ∈ active → 0 < nonnegativeJetScale u (center i))
    (hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x)
    (i : ℕ) (x : Fin n → ℝ) (hx : nonnegativeJetScale u x = 0) :
    activeIntrinsicRawBump u center active ε i =ᶠ[𝓝 x] 0 := by
  classical
  by_cases hi : i ∈ active
  · have hRi : 0 < nonnegativeJetScale u (center i) := hcenter i hi
    have hcRi_lt : c * nonnegativeJetScale u (center i) < dist (center i) x := by
      by_contra hnot
      have hcomp := (hvar (center i) x (le_of_not_gt hnot)).1
      rw [hx, mul_zero] at hcomp
      exact (not_le_of_gt hRi) hcomp
    have houter_lt : 2 * (ε * nonnegativeJetScale u (center i)) < dist x (center i) := by
      rw [dist_comm]
      calc
        2 * (ε * nonnegativeJetScale u (center i)) =
            (2 * ε) * nonnegativeJetScale u (center i) := by ring
        _ < c * nonnegativeJetScale u (center i) := mul_lt_mul_of_pos_right houter hRi
        _ < dist (center i) x := hcRi_lt
    have hxcompl : x ∈ (Metric.closedBall (center i)
        (2 * (ε * nonnegativeJetScale u (center i))))ᶜ := by
      simpa [Metric.mem_closedBall, not_le] using houter_lt
    have hnhds : (Metric.closedBall (center i)
        (2 * (ε * nonnegativeJetScale u (center i))))ᶜ ∈ 𝓝 x :=
      (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hxcompl)
    filter_upwards [hnhds] with y hy
    have hraw : activeIntrinsicRawBump u center active ε i y = 0 := by
      by_contra hne
      have hsupp : y ∈ activeScaledBall (nonnegativeJetScale u) center active ε i := by
        rw [← support_activeIntrinsicRawBump hε hcenter i]
        exact hne
      have hball : y ∈ Metric.ball (center i)
          (2 * (ε * nonnegativeJetScale u (center i))) := by
        simpa [activeScaledBall, hi] using hsupp
      exact hy (Metric.ball_subset_closedBall hball)
    exact hraw
  · rw [activeIntrinsicRawBump_eq_zero_of_not_active hi]


/-- The selected raw square sum is `C⁶` at every positive intrinsic-scale point. -/
theorem selectedRawSquareTsum_contDiffAt {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {c C L ε : ℝ}
    (hC : 1 ≤ C) (hL : C + 2 < L) (hε : 0 < ε) (hsmall : 2 * L * ε ≤ c)
    (hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1))
    {B : ℕ}
    (hoverlap : ∀ x (t : Finset ℕ), Set.ncard {i | i ∈ t ∧
      i ∈ (selectedIntrinsicCentersNatIndexing hε s hdis).active ∧
      x ∈ Metric.ball ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)
        (L * (ε * nonnegativeJetScale u
          ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)))} ≤ B)
    (x : Fin n → ℝ) (hx : 0 < nonnegativeJetScale u x) :
    ContDiffAt ℝ 6 (fun y => ∑' i,
      activeIntrinsicRawBump u (selectedIntrinsicCentersNatIndexing hε s hdis).value
        (selectedIntrinsicCentersNatIndexing hε s hdis).active ε i y ^ 2) x := by
  let I := selectedIntrinsicCentersNatIndexing hε s hdis
  let bump := activeIntrinsicRawBump u I.value I.active ε
  have hcenter : ∀ i, i ∈ I.active → 0 < nonnegativeJetScale u (I.value i) := by
    exact selectedIntrinsicCentersNatIndexing_value_pos hε s hdis
  have hsmall3 : 3 * ε ≤ c := by
    calc
      3 * ε ≤ (2 * L) * ε :=
        mul_le_mul_of_nonneg_right (by linarith : 3 ≤ 2 * L) hε.le
      _ = 2 * L * ε := by ring
      _ ≤ c := hsmall
  have hpoint (y : Fin n → ℝ) : Set.Finite {i | i ∈ I.active ∧
      y ∈ Metric.ball (I.value i) (L * (ε * nonnegativeJetScale u (I.value i)))} := by
    refine finite_of_uniform_finset_ncard_le (B := B) ?_
    intro t
    exact hoverlap y t
  obtain ⟨V, hV, hfinite⟩ := activeScaledBall_locallyFiniteAt_of_pointFinite
    (nonnegativeJetScale u) I.value I.active hC hL hε hsmall3 hcenter hvar hpoint x hx
  have hloc : ∃ V ∈ 𝓝 x,
      Set.Finite {i | (Function.support (bump i) ∩ V).Nonempty} := by
    refine ⟨V, hV, ?_⟩
    convert hfinite using 1
    ext i
    change (Function.support (activeIntrinsicRawBump u I.value I.active ε i) ∩ V).Nonempty ↔
      (activeScaledBall (nonnegativeJetScale u) I.value I.active ε i ∩ V).Nonempty
    rw [support_activeIntrinsicRawBump hε hcenter i]
  exact contDiffAt_rawSquareTsum_of_support_locallyFiniteAt
    (fun i => activeIntrinsicRawBump_contDiff i) hloc


/-- The selected Besicovitch raw family has globally smooth square-normalized cutoffs once
overlap is controlled at a dilation strictly larger than `C + 2`. -/
theorem selectedSquareNormalizedFamily_contDiff {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {c C L ε : ℝ}
    (hC : 1 ≤ C) (hL : C + 2 < L) (hε : 0 < ε) (hsmall : 2 * L * ε ≤ c)
    (hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1))
    (hcover : Set.range (fun x : {x : Fin n → ℝ // 0 < nonnegativeJetScale u x} => x.1) ⊆
      ⋃ color, ⋃ z ∈ s color,
        Metric.ball z.1 (ε * nonnegativeJetScale u z.1))
    {B : ℕ}
    (hoverlap : ∀ x (t : Finset ℕ), Set.ncard {i | i ∈ t ∧
      i ∈ (selectedIntrinsicCentersNatIndexing hε s hdis).active ∧
      x ∈ Metric.ball ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)
        (L * (ε * nonnegativeJetScale u
          ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)))} ≤ B) :
    ∀ i, ContDiff ℝ 6 (squareNormalizedFamily
      (activeIntrinsicRawBump u (selectedIntrinsicCentersNatIndexing hε s hdis).value
        (selectedIntrinsicCentersNatIndexing hε s hdis).active ε) i) := by
  let I := selectedIntrinsicCentersNatIndexing hε s hdis
  let bump := activeIntrinsicRawBump u I.value I.active ε
  have hcenter : ∀ i, i ∈ I.active → 0 < nonnegativeJetScale u (I.value i) := by
    exact selectedIntrinsicCentersNatIndexing_value_pos hε s hdis
  have hL3 : 3 < L := by linarith
  have hsmall3 : 3 * ε ≤ c := by
    calc
      3 * ε ≤ (2 * L) * ε :=
        (mul_lt_mul_of_pos_right (by linarith : 3 < 2 * L) hε).le
      _ = 2 * L * ε := by ring
      _ ≤ c := hsmall
  have houter : 2 * ε < c := by
    calc
      2 * ε < (2 * L) * ε :=
        mul_lt_mul_of_pos_right (by linarith : 2 < 2 * L) hε
      _ = 2 * L * ε := by ring
      _ ≤ c := hsmall
  have hpoint (x : Fin n → ℝ) : Set.Finite {i | i ∈ I.active ∧
      x ∈ Metric.ball (I.value i) (L * (ε * nonnegativeJetScale u (I.value i)))} := by
    refine finite_of_uniform_finset_ncard_le (B := B) ?_
    intro t
    exact hoverlap x t
  have hloc : ∀ x, 0 < nonnegativeJetScale u x → ∃ V ∈ 𝓝 x,
      Set.Finite {i | (Function.support (bump i) ∩ V).Nonempty} := by
    intro x hx
    obtain ⟨V, hV, hfinite⟩ := activeScaledBall_locallyFiniteAt_of_pointFinite
      (nonnegativeJetScale u) I.value I.active hC hL hε hsmall3 hcenter hvar hpoint x hx
    refine ⟨V, hV, ?_⟩
    convert hfinite using 1
    ext i
    change (Function.support (activeIntrinsicRawBump u I.value I.active ε i) ∩ V).Nonempty ↔
      (activeScaledBall (nonnegativeJetScale u) I.value I.active ε i ∩ V).Nonempty
    rw [support_activeIntrinsicRawBump hε hcenter i]
  have hL2 : 2 ≤ L := by linarith
  have hpointBump : ∀ x, Set.Finite {i | bump i x ≠ 0} := by
    exact activeIntrinsicRawBump_pointFinite hL2 hε hcenter hoverlap
  have hpos : ∀ x, 0 < nonnegativeJetScale u x → 0 < ∑' i, bump i x ^ 2 := by
    intro x hx
    obtain ⟨i, hi, hone⟩ := exists_selectedIntrinsicRawBump_eq_one hε s hdis hcover hx
    have hone' : bump i x = 1 := by simpa [bump, I] using hone
    have hsummable : Summable (fun k => bump k x ^ 2) := by
      apply summable_of_hasFiniteSupport
      exact (hpointBump x).subset (by
        intro k hk
        change bump k x ≠ 0
        intro hzero
        exact hk (by simp [hzero]))
    have hsingle := hsummable.sum_le_tsum {i} (fun k hk => sq_nonneg (bump k x))
    have hone_le : 1 ≤ ∑' k, bump k x ^ 2 := by simpa [hone'] using hsingle
    exact zero_lt_one.trans_le hone_le
  have hzero : ∀ i x, ¬0 < nonnegativeJetScale u x → bump i =ᶠ[𝓝 x] 0 := by
    intro i x hx
    have hxzero : nonnegativeJetScale u x = 0 :=
      le_antisymm (not_lt.mp hx) (nonnegativeJetScale_nonneg u x)
    exact activeIntrinsicRawBump_eventuallyEq_zero_of_scale_eq_zero hε houter hcenter
      hvar i x hxzero
  intro i
  exact squareNormalizedFamily_contDiff_of_locallyFiniteOn
    (fun x => 0 < nonnegativeJetScale u x)
    (fun i => activeIntrinsicRawBump_contDiff i) hloc hpos hzero i
/-- Square normalization does not enlarge the support of any member. -/
theorem support_squareNormalizedFamily_subset {X : Type*} (bump : ℕ → X → ℝ) (i : ℕ) :
    Function.support (squareNormalizedFamily bump i) ⊆ Function.support (bump i) := by
  intro x hx
  change bump i x ≠ 0
  intro hb
  exact hx (by simp [squareNormalizedFamily, hb])

/-- Point-finiteness of a raw family is inherited by its square normalization. -/
theorem squareNormalizedFamily_point_finite {X : Type*} (bump : ℕ → X → ℝ)
    (hfinite : ∀ x, Set.Finite {i | bump i x ≠ 0}) (x : X) :
    Set.Finite {i | squareNormalizedFamily bump i x ≠ 0} := by
  apply (hfinite x).subset
  intro i hi
  change bump i x ≠ 0
  intro hb
  exact hi (by simp [squareNormalizedFamily, hb])

/-- If the raw family is point-finite and not simultaneously zero, its normalized
squares sum exactly to one. -/
theorem squareNormalizedFamily_square_tsum {X : Type*} (bump : ℕ → X → ℝ)
    (hfinite : ∀ x, Set.Finite {i | bump i x ≠ 0}) (x : X)
    (hpos : 0 < ∑' i, bump i x ^ 2) :
    ∑' i, squareNormalizedFamily bump i x ^ 2 = 1 := by
  have hsummable : Summable (fun i => bump i x ^ 2) := by
    apply summable_of_hasFiniteSupport
    exact (hfinite x).subset (by
      intro i hi
      change bump i x ≠ 0
      intro hb
      exact hi (by simp [hb]))
  have hsqrt : (Real.sqrt (∑' i, bump i x ^ 2)) ^ 2 = ∑' i, bump i x ^ 2 :=
    Real.sq_sqrt hpos.le
  calc
    ∑' i, squareNormalizedFamily bump i x ^ 2 =
        ∑' i, bump i x ^ 2 / (∑' k, bump k x ^ 2) := by
          apply tsum_congr
          intro i
          dsimp [squareNormalizedFamily]
          rw [div_pow, hsqrt]
    _ = (∑' i, bump i x ^ 2) / (∑' k, bump k x ^ 2) := by
      exact (hsummable.hasSum.div_const _).tsum_eq
    _ = 1 := div_self hpos.ne'

/-- A raw bump which equals one forces the square-normalization denominator to be at
least one. -/
theorem one_le_raw_square_tsum {X : Type*} (bump : ℕ → X → ℝ)
    (hfinite : ∀ x, Set.Finite {i | bump i x ≠ 0}) (x : X)
    (icover : ℕ) (hone : bump icover x = 1) :
    1 ≤ ∑' i, bump i x ^ 2 := by
  have hsummable : Summable (fun i => bump i x ^ 2) := by
    apply summable_of_hasFiniteSupport
    exact (hfinite x).subset (by
      intro i hi
      change bump i x ≠ 0
      intro hb
      exact hi (by simp [hb]))
  have hsingle := hsummable.sum_le_tsum {icover} (fun i hi => sq_nonneg (bump i x))
  simpa [hone] using hsingle
/-- A point-finite family taking values in `[0,1]` has square sum bounded by the
cardinality of its pointwise support. -/
theorem raw_square_tsum_le_card {X : Type*} (bump : ℕ → X → ℝ) (x : X) (B : ℕ)
    (hfinite : Set.Finite {i | bump i x ≠ 0})
    (hcard : Set.ncard {i | bump i x ≠ 0} ≤ B)
    (hrange : ∀ i, 0 ≤ bump i x ∧ bump i x ≤ 1) :
    ∑' i, bump i x ^ 2 ≤ B := by
  let t := hfinite.toFinset
  rw [tsum_eq_sum (s := t)]
  · calc
      ∑ i ∈ t, bump i x ^ 2 ≤ ∑ _i ∈ t, (1 : ℝ) := by
        gcongr with i hi
        have hi0 := (hrange i).1
        have hi1 := (hrange i).2
        nlinarith [mul_nonneg hi0 (sub_nonneg.mpr hi1),
          sq_nonneg (bump i x)]
      _ = t.card := by simp
      _ = Set.ncard {i | bump i x ≠ 0} := by
        simp [t, Set.ncard_eq_toFinset_card _ hfinite]
      _ ≤ B := by exact_mod_cast hcard
  · intro i hi
    have hi' : i ∉ {i | bump i x ≠ 0} := by simpa [t] using hi
    simp only [Set.mem_ofPred_eq, ne_eq, not_not] at hi'
    simp [hi']

/-- A cardinality bound on the raw pointwise support gives the corresponding square-root
denominator bound. -/
theorem sqrt_raw_square_tsum_le_sqrt_card {X : Type*} (bump : ℕ → X → ℝ) (x : X)
    (B : ℕ) (hsum : ∑' i, bump i x ^ 2 ≤ B) :
    Real.sqrt (∑' i, bump i x ^ 2) ≤ Real.sqrt B := by
  exact Real.sqrt_le_sqrt hsum

/-- Two-sided square-sum bounds pass to the square-root denominator. -/
theorem sqrt_mem_Icc_of_one_le_of_le {S B : ℝ} (hS : 1 ≤ S) (hB : S ≤ B) :
    1 ≤ Real.sqrt S ∧ Real.sqrt S ≤ Real.sqrt B := by
  constructor
  · rw [Real.one_le_sqrt]
    exact hS
  · exact Real.sqrt_le_sqrt hB

/-- A square-sum denominator bounded below by one is nonzero, and its reciprocal has
absolute value at most one. -/
theorem sqrt_ne_zero_and_abs_inv_le_one_of_one_le {S : ℝ} (hS : 1 ≤ S) :
    Real.sqrt S ≠ 0 ∧ |(Real.sqrt S)⁻¹| ≤ 1 := by
  have hsqrt : 1 ≤ Real.sqrt S := by
    rw [Real.one_le_sqrt]
    exact hS
  have hsqrtpos : 0 < Real.sqrt S := zero_lt_one.trans_le hsqrt
  exact ⟨hsqrtpos.ne', by
    rw [abs_inv, abs_of_nonneg (Real.sqrt_nonneg S)]
    exact inv_le_one_of_one_le₀ hsqrt⟩


/-- If a raw bump family takes values in `[-1,1]` and one member equals one, every
square-normalized member also has absolute value at most one. -/
theorem squareNormalizedFamily_abs_le_one {X : Type*} (bump : ℕ → X → ℝ)
    (hfinite : ∀ x, Set.Finite {i | bump i x ≠ 0}) (x : X)
    (icover : ℕ) (hone : bump icover x = 1) (i : ℕ)
    (hrange : ∀ i, |bump i x| ≤ 1) :
    |squareNormalizedFamily bump i x| ≤ 1 := by
  have hden : 1 ≤ Real.sqrt (∑' k, bump k x ^ 2) := by
    rw [Real.one_le_sqrt]
    exact one_le_raw_square_tsum bump hfinite x icover hone
  rw [squareNormalizedFamily, abs_div]
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_one₀ (zero_lt_one.trans_le hden)).2 ((hrange i).trans hden)

/-- Every normalized iterated derivative below order six is globally one-Lipschitz. -/
theorem norm_iteratedFDeriv_sub_le_dist {n j : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    (hj : j + 1 ≤ 6) (x y : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j u y - iteratedFDeriv ℝ j u x‖ ≤ dist x y := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ j u) :=
    hu.contDiff.differentiable_iteratedFDeriv (by exact_mod_cast hj)
  have hbound (z : Fin n → ℝ) :
      ‖fderiv ℝ (iteratedFDeriv ℝ j u) z‖ ≤ 1 := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hu.iteratedFDeriv_le_one (j + 1) hj z
  have hmv := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (x := x) (y := y) (C := (1 : ℝ))
    (fun z _ => hdiff z) (fun z _ => hbound z) (Set.mem_univ x) (Set.mem_univ y)
  simpa [dist_eq_norm, norm_sub_rev] using hmv

/-- Hessian variation on a segment is controlled by the third derivative at its first endpoint
and the normalized fourth derivative. -/
theorem norm_hessian_sub_le {n : ℕ} {u : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hu : NormalizedNonnegativeC6 u) (hcontrol : NonnegativeJetControl u C)
    (x y : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ 2 u y - iteratedFDeriv ℝ 2 u x‖ ≤
      (C * nonnegativeJetScale u x + dist x y) * dist x y := by
  let R := nonnegativeJetScale u x
  let d := dist x y
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ 2 u) :=
    hu.contDiff.differentiable_iteratedFDeriv (by norm_num)
  have hbound (z : Fin n → ℝ) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ (iteratedFDeriv ℝ 2 u) z‖ ≤ C * R + d := by
    rw [norm_fderiv_iteratedFDeriv]
    calc
      ‖iteratedFDeriv ℝ 3 u z‖ =
          ‖(iteratedFDeriv ℝ 3 u z - iteratedFDeriv ℝ 3 u x) +
            iteratedFDeriv ℝ 3 u x‖ := by rw [sub_add_cancel]
      _ ≤ ‖iteratedFDeriv ℝ 3 u z - iteratedFDeriv ℝ 3 u x‖ +
            ‖iteratedFDeriv ℝ 3 u x‖ := norm_add_le _ _
      _ ≤ dist x z + C * R := by
        gcongr
        · simpa [dist_comm] using norm_iteratedFDeriv_sub_le_dist hu (by norm_num) x z
        · exact hcontrol.third x
      _ ≤ d + C * R := by
        gcongr
        simpa [d, dist_eq_norm, norm_sub_rev] using norm_sub_le_of_mem_segment hz
      _ = C * R + d := by ring
  have hmv := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (s := segment ℝ x y) (x := x) (y := y) (C := C * R + d)
    (fun z _ => hdiff z) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa [R, d, dist_eq_norm, norm_sub_rev] using hmv

/-- Fourth-order Taylor control of the value in terms of the intrinsic scale at the first
endpoint. -/
theorem abs_value_sub_le {n : ℕ} {u : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hu : NormalizedNonnegativeC6 u) (hcontrol : NonnegativeJetControl u C)
    (x y : Fin n → ℝ) :
    |u y - u x| ≤
      C * nonnegativeJetScale u x ^ 3 * dist x y +
        nonnegativeJetScale u x ^ 2 * dist x y ^ 2 / 2 +
        C * nonnegativeJetScale u x * dist x y ^ 3 / 6 + dist x y ^ 4 / 6 := by
  by_cases hxy : x = y
  · subst y
    simp
  let R := nonnegativeJetScale u x
  let d := dist x y
  let v : Fin n → ℝ := NormedSpace.normalize (y - x)
  have hd : 0 < d := dist_pos.mpr hxy
  have hvzero : y - x ≠ 0 := sub_ne_zero.mpr fun h => hxy h.symm
  have hv : ‖v‖ = 1 := NormedSpace.norm_normalize hvzero
  have hdNorm : d = ‖y - x‖ := by simp [d, dist_eq_norm, norm_sub_rev]
  have hxyline : x + d • v = y := by
    rw [hdNorm]
    exact eq_of_sub_eq_zero (by
      rw [add_sub_assoc, NormedSpace.norm_smul_normalize]
      abel)
  have hsqrt : Real.sqrt (u x) ≤ R ^ 2 := by
    rw [← Real.sq_sqrt (Real.sqrt_nonneg (u x))]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (sqrt_sqrt_le_nonnegativeJetScale u x) 2
  have hD1 : |iteratedFDeriv ℝ 1 u x (fun _ => v)| ≤ C * R ^ 3 := by
    rw [← Real.norm_eq_abs]
    calc
      ‖iteratedFDeriv ℝ 1 u x (fun _ => v)‖ ≤
          ‖iteratedFDeriv ℝ 1 u x‖ * ∏ _ : Fin 1, ‖v‖ :=
            (iteratedFDeriv ℝ 1 u x).le_opNorm _
      _ ≤ (C * R * Real.sqrt (u x)) * ∏ _ : Fin 1, ‖v‖ := by
        gcongr
        exact hcontrol.first x
      _ ≤ C * R ^ 3 := by
        simp only [hv, Finset.prod_const_one, mul_one]
        have hCR : 0 ≤ C * R := mul_nonneg hcontrol.constant_nonneg
          (nonnegativeJetScale_nonneg u x)
        nlinarith [mul_le_mul_of_nonneg_left hsqrt hCR]
  have hD2 : |iteratedFDeriv ℝ 2 u x (fun _ => v)| ≤ R ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc
      ‖iteratedFDeriv ℝ 2 u x (fun _ => v)‖ ≤
          ‖iteratedFDeriv ℝ 2 u x‖ * ∏ _ : Fin 2, ‖v‖ :=
            (iteratedFDeriv ℝ 2 u x).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 2 u x‖ := by simp [hv]
      _ ≤ R ^ 2 := by
        exact norm_iteratedFDeriv_two_le_nonnegativeJetScale_sq u x
  have hD3 : |iteratedFDeriv ℝ 3 u x (fun _ => v)| ≤ C * R := by
    rw [← Real.norm_eq_abs]
    calc
      ‖iteratedFDeriv ℝ 3 u x (fun _ => v)‖ ≤
          ‖iteratedFDeriv ℝ 3 u x‖ * ∏ _ : Fin 3, ‖v‖ :=
            (iteratedFDeriv ℝ 3 u x).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 3 u x‖ := by simp [hv]
      _ ≤ C * R := hcontrol.third x
  let f : ℝ → ℝ := fun s => u (x + s • v)
  have hf : ContDiff ℝ 4 f := by
    dsimp [f]
    apply (hu.contDiff.comp ?_).of_le (by norm_num)
    fun_prop
  have hrem := abs_sub_explicit_taylor_three_le hd hf
    (fun s => norm_iteratedDeriv_line_le_one hu x v hv.le s)
  have hline0 : f 0 = u x := by simp [f]
  have hlined : f d = u y := by simp [f, hxyline]
  have hdone : deriv f 0 = iteratedFDeriv ℝ 1 u x (fun _ => v) := by
    rw [← iteratedDeriv_one]
    exact iteratedDeriv_line_zero hu.contDiff (by norm_num) x v
  have hdtwo : iteratedDeriv 2 f 0 = iteratedFDeriv ℝ 2 u x (fun _ => v) :=
    iteratedDeriv_line_zero hu.contDiff (by norm_num) x v
  have hdthree : iteratedDeriv 3 f 0 = iteratedFDeriv ℝ 3 u x (fun _ => v) :=
    iteratedDeriv_line_zero hu.contDiff (by norm_num) x v
  rw [hline0, hlined, hdone, hdtwo, hdthree] at hrem
  let b := iteratedFDeriv ℝ 1 u x (fun _ => v)
  let q := iteratedFDeriv ℝ 2 u x (fun _ => v)
  let e := iteratedFDeriv ℝ 3 u x (fun _ => v)
  have hsum : |b * d + q * d ^ 2 / 2 + e * d ^ 3 / 6| ≤
      |b| * d + |q| * d ^ 2 / 2 + |e| * d ^ 3 / 6 := by
    calc
      |b * d + q * d ^ 2 / 2 + e * d ^ 3 / 6| ≤
          |b * d + q * d ^ 2 / 2| + |e * d ^ 3 / 6| := abs_add_le _ _
      _ ≤ (|b * d| + |q * d ^ 2 / 2|) + |e * d ^ 3 / 6| := by
        gcongr
        exact abs_add_le _ _
      _ = |b| * d + |q| * d ^ 2 / 2 + |e| * d ^ 3 / 6 := by
        simp [abs_mul, abs_div, abs_of_nonneg hd.le]
  calc
    |u y - u x| =
        |(u y - (u x + b * d + q * d ^ 2 / 2 + e * d ^ 3 / 6)) +
          (b * d + q * d ^ 2 / 2 + e * d ^ 3 / 6)| := by
            congr 1
            ring
    _ ≤ |u y - (u x + b * d + q * d ^ 2 / 2 + e * d ^ 3 / 6)| +
        |b * d + q * d ^ 2 / 2 + e * d ^ 3 / 6| := abs_add_le _ _
    _ ≤ d ^ 4 / 6 + (|b| * d + |q| * d ^ 2 / 2 + |e| * d ^ 3 / 6) :=
      add_le_add hrem hsum
    _ = |b| * d + |q| * d ^ 2 / 2 + |e| * d ^ 3 / 6 + d ^ 4 / 6 := by ring
    _ ≤ C * R ^ 3 * d + R ^ 2 * d ^ 2 / 2 + C * R * d ^ 3 / 6 +
        d ^ 4 / 6 := by
      dsimp [b, q, e]
      have hd0 : 0 ≤ d := hd.le
      gcongr
    _ = C * nonnegativeJetScale u x ^ 3 * dist x y +
        nonnegativeJetScale u x ^ 2 * dist x y ^ 2 / 2 +
        C * nonnegativeJetScale u x * dist x y ^ 3 / 6 + dist x y ^ 4 / 6 := by
      rfl

/-- On a sufficiently small intrinsic ball, the value and Hessian vary by less than one tenth
of their respective natural scales. -/
theorem intrinsicScale_small_variation {n : ℕ} {u : (Fin n → ℝ) → ℝ} {C : ℝ}
    (hu : NormalizedNonnegativeC6 u) (hcontrol : NonnegativeJetControl u C)
    (x y : Fin n → ℝ)
    (hxy : dist x y ≤ (1 / (100 * (C + 1))) * nonnegativeJetScale u x) :
    |u y - u x| ≤ nonnegativeJetScale u x ^ 4 / 10 ∧
      ‖iteratedFDeriv ℝ 2 u y - iteratedFDeriv ℝ 2 u x‖ ≤
        nonnegativeJetScale u x ^ 2 / 10 := by
  let R := nonnegativeJetScale u x
  let d := dist x y
  have hC0 : 0 ≤ C := hcontrol.constant_nonneg
  have hR0 : 0 ≤ R := nonnegativeJetScale_nonneg u x
  have hd0 : 0 ≤ d := dist_nonneg
  have hA : 0 < C + 1 := by linarith
  have hcpos : 0 < 1 / (100 * (C + 1)) := by positivity
  have hcsmall : 1 / (100 * (C + 1)) ≤ (1 / 100 : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 100 * (C + 1))]
    nlinarith
  have hCcsmall : C * (1 / (100 * (C + 1))) ≤ (1 / 100 : ℝ) := by
    rw [show C * (1 / (100 * (C + 1))) = C / (100 * (C + 1)) by ring]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 100 * (C + 1))]
    nlinarith
  have hdR100 : d ≤ R / 100 := by
    calc
      d ≤ (1 / (100 * (C + 1))) * R := hxy
      _ ≤ (1 / 100) * R := mul_le_mul_of_nonneg_right hcsmall hR0
      _ = R / 100 := by ring
  have hCdR100 : C * d ≤ R / 100 := by
    calc
      C * d ≤ C * ((1 / (100 * (C + 1))) * R) :=
        mul_le_mul_of_nonneg_left hxy hC0
      _ = (C * (1 / (100 * (C + 1)))) * R := by ring
      _ ≤ (1 / 100) * R := mul_le_mul_of_nonneg_right hCcsmall hR0
      _ = R / 100 := by ring
  have hdR : d ≤ R := by linarith
  have hd2 : d ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hd0 hdR 2
  have hd3 : d ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hd0 hdR 3
  have hterm1 : C * R ^ 3 * d ≤ R ^ 4 / 100 := by
    calc
      C * R ^ 3 * d = R ^ 3 * (C * d) := by ring
      _ ≤ R ^ 3 * (R / 100) :=
        mul_le_mul_of_nonneg_left hCdR100 (pow_nonneg hR0 3)
      _ = R ^ 4 / 100 := by ring
  have hterm2 : R ^ 2 * d ^ 2 / 2 ≤ R ^ 4 / 100 := by
    have hd2small : d ^ 2 ≤ R ^ 2 / 100 := by
      calc
        d ^ 2 = d * d := by ring
        _ ≤ d * R := mul_le_mul_of_nonneg_left hdR hd0
        _ ≤ (R / 100) * R := mul_le_mul_of_nonneg_right hdR100 hR0
        _ = R ^ 2 / 100 := by ring
    calc
      R ^ 2 * d ^ 2 / 2 ≤ R ^ 2 * (R ^ 2 / 100) / 2 := by gcongr
      _ ≤ R ^ 4 / 100 := by nlinarith [sq_nonneg (R ^ 2)]
  have hterm3 : C * R * d ^ 3 / 6 ≤ R ^ 4 / 100 := by
    calc
      C * R * d ^ 3 / 6 = (C * d) * (R * d ^ 2) / 6 := by ring
      _ ≤ (R / 100) * (R * R ^ 2) / 6 := by gcongr
      _ ≤ R ^ 4 / 100 := by nlinarith [pow_nonneg hR0 4]
  have hterm4 : d ^ 4 / 6 ≤ R ^ 4 / 100 := by
    have hd4small : d ^ 4 ≤ R ^ 4 / 100 := by
      calc
        d ^ 4 = d * d ^ 3 := by ring
        _ ≤ d * R ^ 3 := mul_le_mul_of_nonneg_left hd3 hd0
        _ ≤ (R / 100) * R ^ 3 :=
          mul_le_mul_of_nonneg_right hdR100 (pow_nonneg hR0 3)
        _ = R ^ 4 / 100 := by ring
    nlinarith [hd4small]
  constructor
  · have hv := abs_value_sub_le hu hcontrol x y
    dsimp [R, d] at *
    nlinarith [pow_nonneg hR0 4]
  · have hh := norm_hessian_sub_le hu hcontrol x y
    have hfirst : C * R * d ≤ R ^ 2 / 100 := by
      calc
        C * R * d = R * (C * d) := by ring
        _ ≤ R * (R / 100) := mul_le_mul_of_nonneg_left hCdR100 hR0
        _ = R ^ 2 / 100 := by ring
    have hsecond : d ^ 2 ≤ R ^ 2 / 100 := by
      calc
        d ^ 2 = d * d := by ring
        _ ≤ d * R := mul_le_mul_of_nonneg_left hdR hd0
        _ ≤ (R / 100) * R := mul_le_mul_of_nonneg_right hdR100 hR0
        _ = R ^ 2 / 100 := by ring
    dsimp [R, d] at *
    nlinarith

/-- Nonnegative jet estimates imply slow variation of the intrinsic scale. -/
theorem intrinsicScale_slowVariation_of_jetBounds {n : ℕ}
    (hjets : HasUniformNonnegativeJetBounds n) : HasIntrinsicScaleSlowVariation n := by
  rcases hjets with ⟨C, hC, hcontrols⟩
  refine ⟨1 / (100 * (C + 1)), 2, by positivity, by norm_num, ?_⟩
  intro u hu x y hxy
  let R := nonnegativeJetScale u x
  let S := nonnegativeJetScale u y
  let qx := Real.sqrt (Real.sqrt (u x))
  let qy := Real.sqrt (Real.sqrt (u y))
  let sx := Real.sqrt ‖iteratedFDeriv ℝ 2 u x‖
  let sy := Real.sqrt ‖iteratedFDeriv ℝ 2 u y‖
  have hcontrol := hcontrols u hu
  have hsmall := intrinsicScale_small_variation hu hcontrol x y hxy
  have hsmallR : |u y - u x| ≤ R ^ 4 / 10 ∧
      ‖iteratedFDeriv ℝ 2 u y - iteratedFDeriv ℝ 2 u x‖ ≤ R ^ 2 / 10 := by
    simpa [R] using hsmall
  have hR0 : 0 ≤ R := nonnegativeJetScale_nonneg u x
  have hqx0 : 0 ≤ qx := Real.sqrt_nonneg _
  have hqy0 : 0 ≤ qy := Real.sqrt_nonneg _
  have hsx0 : 0 ≤ sx := Real.sqrt_nonneg _
  have hsy0 : 0 ≤ sy := Real.sqrt_nonneg _
  have hqx4 : qx ^ 4 = u x := by
    have hx0 : 0 ≤ u x := hu.nonnegative x
    have hsqrt0 : 0 ≤ Real.sqrt (u x) := Real.sqrt_nonneg _
    have hq2 : qx ^ 2 = Real.sqrt (u x) := Real.sq_sqrt hsqrt0
    rw [show qx ^ 4 = (qx ^ 2) ^ 2 by ring, hq2, Real.sq_sqrt hx0]
  have hqy4 : qy ^ 4 = u y := by
    have hy0 : 0 ≤ u y := hu.nonnegative y
    have hsqrt0 : 0 ≤ Real.sqrt (u y) := Real.sqrt_nonneg _
    have hq2 : qy ^ 2 = Real.sqrt (u y) := Real.sq_sqrt hsqrt0
    rw [show qy ^ 4 = (qy ^ 2) ^ 2 by ring, hq2, Real.sq_sqrt hy0]
  have hsx2 : sx ^ 2 = ‖iteratedFDeriv ℝ 2 u x‖ :=
    Real.sq_sqrt (norm_nonneg _)
  have hsy2 : sy ^ 2 = ‖iteratedFDeriv ℝ 2 u y‖ :=
    Real.sq_sqrt (norm_nonneg _)
  have hRdef : R = max qx sx := rfl
  have hSdef : S = max qy sy := rfl
  have hqyS : qy ≤ S := by rw [hSdef]; exact le_max_left _ _
  have hsyS : sy ≤ S := by rw [hSdef]; exact le_max_right _ _
  have huxR : u x ≤ R ^ 4 := by
    simpa [R] using value_le_nonnegativeJetScale_pow_four hu x
  have hHxR : ‖iteratedFDeriv ℝ 2 u x‖ ≤ R ^ 2 := by
    simpa [R] using norm_iteratedFDeriv_two_le_nonnegativeJetScale_sq u x
  have hvalUpper : u y ≤ u x + R ^ 4 / 10 := by
    have := (abs_le.mp hsmallR.1).2
    linarith
  have hHUpper : ‖iteratedFDeriv ℝ 2 u y‖ ≤
      ‖iteratedFDeriv ℝ 2 u x‖ + R ^ 2 / 10 := by
    calc
      ‖iteratedFDeriv ℝ 2 u y‖ =
          ‖(iteratedFDeriv ℝ 2 u y - iteratedFDeriv ℝ 2 u x) +
            iteratedFDeriv ℝ 2 u x‖ := by rw [sub_add_cancel]
      _ ≤ ‖iteratedFDeriv ℝ 2 u y - iteratedFDeriv ℝ 2 u x‖ +
          ‖iteratedFDeriv ℝ 2 u x‖ := norm_add_le _ _
      _ ≤ ‖iteratedFDeriv ℝ 2 u x‖ + R ^ 2 / 10 := by linarith [hsmallR.2]
  have hqyUpper : qy ≤ 2 * R := by
    apply (pow_le_pow_iff_left₀ (n := 4) hqy0 (mul_nonneg (by norm_num) hR0)
      (by norm_num)).mp
    rw [hqy4]
    nlinarith [pow_nonneg hR0 4]
  have hsyUpper : sy ≤ 2 * R := by
    apply (sq_le_sq₀ hsy0 (mul_nonneg (by norm_num) hR0)).mp
    rw [hsy2]
    nlinarith [sq_nonneg R]
  have hUpper : S ≤ 2 * R := by
    rw [hSdef]
    exact max_le hqyUpper hsyUpper
  have hLower : R ≤ 2 * S := by
    by_cases hdom : qx ≤ sx
    · have hReq : R = sx := by rw [hRdef, max_eq_right hdom]
      have hHLower : ‖iteratedFDeriv ℝ 2 u x‖ ≤
          R ^ 2 / 10 + ‖iteratedFDeriv ℝ 2 u y‖ := by
        calc
          ‖iteratedFDeriv ℝ 2 u x‖ =
              ‖(iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y) +
                iteratedFDeriv ℝ 2 u y‖ := by rw [sub_add_cancel]
          _ ≤ ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ +
              ‖iteratedFDeriv ℝ 2 u y‖ := norm_add_le _ _
          _ ≤ R ^ 2 / 10 + ‖iteratedFDeriv ℝ 2 u y‖ := by
            rw [norm_sub_rev]
            gcongr
            exact hsmallR.2
      have hRsy : R ≤ 2 * sy := by
        apply (sq_le_sq₀ hR0 (mul_nonneg (by norm_num) hsy0)).mp
        rw [hReq, hsx2, mul_pow, hsy2]
        have hR2 : R ^ 2 = ‖iteratedFDeriv ℝ 2 u x‖ := by rw [hReq, hsx2]
        nlinarith [sq_nonneg R, hR2]
      exact hRsy.trans (mul_le_mul_of_nonneg_left hsyS (by norm_num))
    · have hsxqx : sx ≤ qx := le_of_not_ge hdom
      have hReq : R = qx := by rw [hRdef, max_eq_left hsxqx]
      have hvalLower : u x ≤ R ^ 4 / 10 + u y := by
        have := (abs_le.mp hsmallR.1).1
        linarith
      have hRqy : R ≤ 2 * qy := by
        apply (pow_le_pow_iff_left₀ (n := 4) hR0 (mul_nonneg (by norm_num) hqy0)
          (by norm_num)).mp
        rw [hReq, hqx4, mul_pow, hqy4]
        have hR4 : R ^ 4 = u x := by rw [hReq, hqx4]
        nlinarith [pow_nonneg hR0 4, hR4, hu.nonnegative y]
      exact hRqy.trans (mul_le_mul_of_nonneg_left hqyS (by norm_num))
  exact ⟨hLower, hUpper⟩


/-- Derivatives of the locally finite raw square sum are uniformly bounded at the scale
of any active reference bump whose radius-three ball contains the evaluation point. -/
theorem selectedRawSquareTsum_scaled_deriv_bound {n : ℕ} {A₀ : ℝ}
    (hA₀ : ∀ j, j ≤ 6 → ∀ x,
      ‖iteratedFDeriv ℝ j (unitScaleBumpSquare n) x‖ ≤ A₀)
    {u : (Fin n → ℝ) → ℝ} {c C L ε : ℝ}
    (hC : 1 ≤ C) (hL : C + 2 < L) (hε : 0 < ε) (hsmall : 2 * L * ε ≤ c)
    (hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1))
    (i : ℕ) (hi : i ∈ (selectedIntrinsicCentersNatIndexing hε s hdis).active)
    (j : ℕ) (hj : j ≤ 6) (x : Fin n → ℝ)
    (hxball : x ∈ Metric.ball
      ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)
      (3 * (ε * nonnegativeJetScale u
        ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)))) :
    ‖iteratedFDeriv ℝ j (fun y => ∑' k,
        activeIntrinsicRawBump u
          (selectedIntrinsicCentersNatIndexing hε s hdis).value
          (selectedIntrinsicCentersNatIndexing hε s hdis).active ε k y ^ 2) x‖ *
      (ε * nonnegativeJetScale u
        ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)) ^ j ≤
      intrinsicOverlapBound n (show 0 ≤ L by linarith) hC * (A₀ * C ^ j) := by
  let I := selectedIntrinsicCentersNatIndexing hε s hdis
  let bump := activeIntrinsicRawBump u I.value I.active ε
  let r : ℕ → ℝ := fun k => ε * nonnegativeJetScale u (I.value k)
  let df : ℕ → ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin n → ℝ) ℝ :=
    fun k => iteratedFDeriv ℝ j (fun y => bump k y ^ 2) x
  have hcenter : ∀ k, k ∈ I.active → 0 < nonnegativeJetScale u (I.value k) := by
    exact selectedIntrinsicCentersNatIndexing_value_pos hε s hdis
  have hL0 : 0 ≤ L := by linarith
  have hL2 : 2 < L := by linarith
  have hLthree : 3 < L := by linarith
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hA₀0 : 0 ≤ A₀ :=
    (norm_nonneg (iteratedFDeriv ℝ 0 (unitScaleBumpSquare n) 0)).trans
      (hA₀ 0 (by norm_num) 0)
  have hri : 0 < r i := mul_pos hε (hcenter i hi)
  have hoverlap := selectedIntrinsicCentersNatIndexing_overlap_bound n hL0 hC hε
    hsmall hvar s hdis
  have hpoint (y : Fin n → ℝ) : Set.Finite {k | k ∈ I.active ∧
      y ∈ Metric.ball (I.value k) (L * r k)} := by
    refine finite_of_uniform_finset_ncard_le (B := intrinsicOverlapBound n hL0 hC) ?_
    intro t
    simpa [I, r] using hoverlap y t
  have hsmall3 : 3 * ε ≤ c := by
    calc
      3 * ε ≤ (2 * L) * ε :=
        mul_le_mul_of_nonneg_right (by linarith : 3 ≤ 2 * L) hε.le
      _ = 2 * L * ε := by ring
      _ ≤ c := hsmall
  have hsmall6 : 2 * 3 * ε ≤ c := by
    calc
      2 * 3 * ε ≤ 2 * L * ε := by
        gcongr
      _ ≤ c := hsmall
  have hdistx : dist (I.value i) x ≤ c * nonnegativeJetScale u (I.value i) := by
    have hxlt : dist (I.value i) x < 3 * r i := by
      simpa [dist_comm, I, r] using Metric.mem_ball.mp hxball
    calc
      dist (I.value i) x ≤ 3 * r i := hxlt.le
      _ = (3 * ε) * nonnegativeJetScale u (I.value i) := by simp [r]; ring
      _ ≤ c * nonnegativeJetScale u (I.value i) :=
        mul_le_mul_of_nonneg_right hsmall3 (hcenter i hi).le
  have hxpos : 0 < nonnegativeJetScale u x := by
    have hcomp := (hvar (I.value i) x hdistx).1
    by_contra hnot
    have hxzero : nonnegativeJetScale u x = 0 :=
      le_antisymm (not_lt.mp hnot) (nonnegativeJetScale_nonneg u x)
    rw [hxzero, mul_zero] at hcomp
    exact (not_le_of_gt (hcenter i hi)) hcomp
  have hlocBall := activeScaledBall_locallyFiniteAt_of_pointFinite
    (nonnegativeJetScale u) I.value I.active hC hL hε hsmall3 hcenter hvar hpoint x hxpos
  have hloc : ∃ V ∈ 𝓝 x, Set.Finite
      {k | (Function.support (fun y => bump k y ^ 2) ∩ V).Nonempty} := by
    obtain ⟨V, hV, hfinite⟩ := hlocBall
    refine ⟨V, hV, ?_⟩
    convert hfinite using 1
    ext k
    constructor
    · rintro ⟨y, hy, hyV⟩
      have hraw : y ∈ Function.support (bump k) := by
        change bump k y ≠ 0
        change bump k y ^ 2 ≠ 0 at hy
        exact fun hzero => hy (by simp [hzero])
      have hsupp : Function.support (bump k) =
          activeScaledBall (nonnegativeJetScale u) I.value I.active ε k := by
        simpa [bump] using support_activeIntrinsicRawBump hε hcenter k
      rw [hsupp] at hraw
      exact ⟨y, hraw, hyV⟩
    · rintro ⟨y, hy, hyV⟩
      have hsupp : Function.support (bump k) =
          activeScaledBall (nonnegativeJetScale u) I.value I.active ε k := by
        simpa [bump] using support_activeIntrinsicRawBump hε hcenter k
      have hraw : y ∈ Function.support (bump k) := by simpa [hsupp] using hy
      refine ⟨y, ?_, hyV⟩
      change bump k y ^ 2 ≠ 0
      exact pow_ne_zero 2 hraw
  have hderiv : iteratedFDeriv ℝ j (fun y => ∑' k, bump k y ^ 2) x = ∑' k, df k := by
    exact iteratedFDeriv_tsum_of_support_locallyFiniteAt
      (f := fun k y => bump k y ^ 2)
      (fun k => (activeIntrinsicRawBump_contDiff k).pow 2) hloc (by exact_mod_cast hj)
  have hfiniteDf : Set.Finite {k | df k ≠ 0} := by
    apply (hpoint x).subset
    intro k hk
    have hkactive : k ∈ I.active := by
      by_contra hnot
      have hzero : (fun y => bump k y ^ 2) = fun _ => 0 := by
        funext y
        simp [bump, activeIntrinsicRawBump_eq_zero_of_not_active hnot]
      have hk' := hk
      dsimp [df] at hk'
      rw [hzero, iteratedFDeriv_fun_zero, Pi.zero_apply] at hk'
      exact hk' rfl
    have hclosed := support_iteratedFDeriv_activeIntrinsicRawBump_sq_subset_closedBall
      hε hcenter k j (by simpa [df, bump] using hk)
    have hrk : 0 < r k := mul_pos hε (hcenter k hkactive)
    refine ⟨hkactive, Metric.closedBall_subset_ball ?_ hclosed⟩
    exact mul_lt_mul_of_pos_right hL2 hrk
  have hcardDf : Set.ncard {k | df k ≠ 0} ≤ intrinsicOverlapBound n hL0 hC := by
    exact activeIntrinsicRawBump_sq_deriv_ncard_le hL2 hε hcenter hoverlap j x
  have hterm (k : ℕ) : ‖df k‖ * (r i) ^ j ≤ A₀ * C ^ j := by
    by_cases hkzero : df k = 0
    · rw [hkzero, norm_zero, zero_mul]
      positivity
    · have hkactive : k ∈ I.active := by
        by_contra hnot
        have hzero : (fun y => bump k y ^ 2) = fun _ => 0 := by
          funext y
          simp [bump, activeIntrinsicRawBump_eq_zero_of_not_active hnot]
        dsimp [df] at hkzero
        rw [hzero, iteratedFDeriv_fun_zero, Pi.zero_apply] at hkzero
        exact hkzero rfl
      have hclosed := support_iteratedFDeriv_activeIntrinsicRawBump_sq_subset_closedBall
        hε hcenter k j (by simpa [df, bump] using hkzero)
      have hrk : 0 < r k := mul_pos hε (hcenter k hkactive)
      have hkball : x ∈ Metric.ball (I.value k) (3 * r k) :=
        Metric.closedBall_subset_ball (mul_lt_mul_of_pos_right (by norm_num) hrk) hclosed
      have hcomp := intrinsicScale_comparable_of_common_scaled_balls
        (u := u) (c := c) (C := C) (D := 3) (ε := ε)
        (by norm_num) hε hsmall6 hvar (hcenter i hi) (hcenter k hkactive)
        (by simpa [I, r] using hxball) (by simpa [r] using hkball)
      have hir : r i ≤ C * r k := by
        calc
          r i = ε * nonnegativeJetScale u (I.value i) := rfl
          _ ≤ ε * (C * nonnegativeJetScale u (I.value k)) :=
            mul_le_mul_of_nonneg_left hcomp.1 hε.le
          _ = C * r k := by simp [r]; ring
      have hscaled := activeIntrinsicRawBump_sq_scaled_deriv_bound hA₀ hε hcenter
        k hkactive j hj x
      have hscaled' : ‖df k‖ * (r k) ^ j ≤ A₀ := by
        simpa [df, bump, r] using hscaled
      calc
        ‖df k‖ * (r i) ^ j ≤ ‖df k‖ * (C * r k) ^ j := by gcongr
        _ = C ^ j * (‖df k‖ * (r k) ^ j) := by ring
        _ ≤ C ^ j * A₀ := mul_le_mul_of_nonneg_left hscaled' (pow_nonneg hC0 j)
        _ = A₀ * C ^ j := by ring
  rw [hderiv]
  exact norm_tsum_mul_pow_le_of_finite_support_card df
    (intrinsicOverlapBound n hL0 hC) (A₀ * C ^ j) (r i) j
    hfiniteDf hcardDf hterm hri (mul_nonneg hA₀0 (pow_nonneg hC0 j))


/-- On the positive intrinsic-scale locus, the selected raw square sum lies between one
and the explicit overlap constant. -/
theorem selectedIntrinsicRawBump_square_tsum_mem_Icc {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {c C L ε : ℝ}
    (hC : 1 ≤ C) (hL : C + 2 < L) (hε : 0 < ε) (hsmall : 2 * L * ε ≤ c)
    (hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1))
    (hcover : Set.range (fun x : {x : Fin n → ℝ // 0 < nonnegativeJetScale u x} => x.1) ⊆
      ⋃ color, ⋃ z ∈ s color,
        Metric.ball z.1 (ε * nonnegativeJetScale u z.1))
    (x : Fin n → ℝ) (hx : 0 < nonnegativeJetScale u x) :
    1 ≤ ∑' i, activeIntrinsicRawBump u
        (selectedIntrinsicCentersNatIndexing hε s hdis).value
        (selectedIntrinsicCentersNatIndexing hε s hdis).active ε i x ^ 2 ∧
      ∑' i, activeIntrinsicRawBump u
        (selectedIntrinsicCentersNatIndexing hε s hdis).value
        (selectedIntrinsicCentersNatIndexing hε s hdis).active ε i x ^ 2 ≤
        intrinsicOverlapBound n (show 0 ≤ L by linarith) hC := by
  let I := selectedIntrinsicCentersNatIndexing hε s hdis
  let bump := activeIntrinsicRawBump u I.value I.active ε
  have hcenter : ∀ k, k ∈ I.active → 0 < nonnegativeJetScale u (I.value k) := by
    exact selectedIntrinsicCentersNatIndexing_value_pos hε s hdis
  have hL2 : 2 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hoverlap := selectedIntrinsicCentersNatIndexing_overlap_bound n hL0 hC hε
    hsmall hvar s hdis
  have hpoint : ∀ y, Set.Finite {i | bump i y ≠ 0} :=
    activeIntrinsicRawBump_pointFinite hL2 hε hcenter hoverlap
  have hfinite : Set.Finite {i | bump i x ≠ 0} := hpoint x
  have hcard : Set.ncard {i | bump i x ≠ 0} ≤ intrinsicOverlapBound n hL0 hC :=
    activeIntrinsicRawBump_ncard_le hL2 hε hcenter hoverlap x
  obtain ⟨icover, hicover, hone⟩ :=
    exists_selectedIntrinsicRawBump_eq_one hε s hdis hcover hx
  have hone' : bump icover x = 1 := by simpa [bump, I] using hone
  constructor
  · exact one_le_raw_square_tsum bump hpoint x icover hone'
  · exact raw_square_tsum_le_card bump x (intrinsicOverlapBound n hL0 hC)
      hfinite hcard (fun i => activeIntrinsicRawBump_mem_Icc i x)


/-- Zeroth-order normalized cutoff bound; this part does not require any quotient
derivative estimates. -/
theorem selectedSquareNormalizedFamily_zero_order_scaled_deriv_bound {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {c C L ε : ℝ}
    (hC : 1 ≤ C) (hL : C + 2 < L) (hε : 0 < ε) (hsmall : 2 * L * ε ≤ c)
    (hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x)
    (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
      Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
    (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
      Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1))
    (hcover : Set.range (fun x : {x : Fin n → ℝ // 0 < nonnegativeJetScale u x} => x.1) ⊆
      ⋃ color, ⋃ z ∈ s color,
        Metric.ball z.1 (ε * nonnegativeJetScale u z.1))
    (i : ℕ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ 0 (squareNormalizedFamily
      (activeIntrinsicRawBump u (selectedIntrinsicCentersNatIndexing hε s hdis).value
        (selectedIntrinsicCentersNatIndexing hε s hdis).active ε) i) x‖ *
      (ε * nonnegativeJetScale u
        ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)) ^ 0 ≤ 1 := by
  let I := selectedIntrinsicCentersNatIndexing hε s hdis
  let bump := activeIntrinsicRawBump u I.value I.active ε
  have hcenter : ∀ k, k ∈ I.active → 0 < nonnegativeJetScale u (I.value k) := by
    exact selectedIntrinsicCentersNatIndexing_value_pos hε s hdis
  have hL2 : 2 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hoverlap := selectedIntrinsicCentersNatIndexing_overlap_bound n hL0 hC hε
    hsmall hvar s hdis
  have hpoint : ∀ y, Set.Finite {k | bump k y ≠ 0} := by
    exact activeIntrinsicRawBump_pointFinite hL2 hε hcenter hoverlap
  rw [norm_iteratedFDeriv_zero, pow_zero, mul_one, Real.norm_eq_abs]
  by_cases hx : 0 < nonnegativeJetScale u x
  · obtain ⟨icover, hicover, hone⟩ :=
      exists_selectedIntrinsicRawBump_eq_one hε s hdis hcover hx
    have hone' : bump icover x = 1 := by simpa [bump, I] using hone
    apply squareNormalizedFamily_abs_le_one bump hpoint x icover hone' i
    intro k
    have hrange := activeIntrinsicRawBump_mem_Icc (u := u) (center := I.value)
      (active := I.active) (ε := ε) k x
    rw [abs_of_nonneg hrange.1]
    exact hrange.2
  · have hxzero : nonnegativeJetScale u x = 0 :=
      le_antisymm (not_lt.mp hx) (nonnegativeJetScale_nonneg u x)
    have houter : 2 * ε < c := by
      calc
        2 * ε < (2 * L) * ε :=
          mul_lt_mul_of_pos_right (by linarith : 2 < 2 * L) hε
        _ = 2 * L * ε := by ring
        _ ≤ c := hsmall
    have hzero := activeIntrinsicRawBump_eventuallyEq_zero_of_scale_eq_zero
      hε houter hcenter hvar i x hxzero
    have hzero_at : bump i x = 0 := by
      simpa [bump] using hzero.eq_of_nhds
    simp [squareNormalizedFamily, bump, I, hzero_at]

/-- Pointwise version of mathlib's bilinear product derivative bound. The proof localizes the two
`ContDiffAt` hypotheses to one open neighborhood and then uses the existing within-set theorem. -/
theorem norm_iteratedFDeriv_mul_le_of_contDiffAt {m n : ℕ}
    {f g : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ}
    (hf : ContDiffAt ℝ 6 f x) (hg : ContDiffAt ℝ 6 g x) (hn : n ≤ 6) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  obtain ⟨uf, huf, hfOn⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨ug, hug, hgOn⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp (Filter.inter_mem huf hug)
  have hfs : ContDiffOn ℝ 6 f s := hfOn.mono (hs_sub.trans inter_subset_left)
  have hgs : ContDiffOn ℝ 6 g s := hgOn.mono (hs_sub.trans inter_subset_right)
  have hsu : UniqueDiffOn ℝ s := hs_open.uniqueDiffOn
  have hn' : (n : WithTop ℕ∞) ≤ 6 := by exact_mod_cast hn
  have hbound := norm_iteratedFDerivWithin_mul_le hfs hgs hsu hxs hn'
  have hfg : ContDiffAt ℝ 6 (fun y => f y * g y) x := hf.mul hg
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hsu (hfg.of_le hn') hxs] at hbound
  calc
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f s x‖ *
            ‖iteratedFDerivWithin ℝ (n - i) g s x‖ := hbound
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi_le : i ≤ 6 := (Finset.mem_range_succ_iff.mp hi).trans hn
      have hi_le' : (i : WithTop ℕ∞) ≤ 6 := by exact_mod_cast hi_le
      have hni_le : n - i ≤ 6 := (Nat.sub_le n i).trans hn
      have hni_le' : ((n - i : ℕ) : WithTop ℕ∞) ≤ 6 := by exact_mod_cast hni_le
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hsu (hf.of_le hi_le') hxs,
        iteratedFDerivWithin_eq_iteratedFDeriv hsu (hg.of_le hni_le') hxs]

/-- Scale-invariant pointwise product rule through order six. -/
theorem norm_iteratedFDeriv_mul_scaled_le_of_contDiffAt {m n : ℕ}
    {f g : (Fin m → ℝ) → ℝ} {r Mf Mg : ℝ} {x : Fin m → ℝ}
    (hr : 0 < r) (hMf : 0 ≤ Mf) (hMg : 0 ≤ Mg)
    (hf : ContDiffAt ℝ 6 f x) (hg : ContDiffAt ℝ 6 g x)
    (hfbound : ∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q f x‖ * r ^ q ≤ Mf)
    (hgbound : ∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q g x‖ * r ^ q ≤ Mg)
    (hn : n ≤ 6) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ * r ^ n ≤ 64 * Mf * Mg := by
  have hbase := norm_iteratedFDeriv_mul_le_of_contDiffAt hf hg hn
  have hscaled := mul_le_mul_of_nonneg_right hbase (pow_nonneg hr.le n)
  calc
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ * r ^ n ≤
        (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖) * r ^ n := hscaled
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (‖iteratedFDeriv ℝ i f x‖ * r ^ i) *
            (‖iteratedFDeriv ℝ (n - i) g x‖ * r ^ (n - i)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      have hi_le : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hrpow : r ^ n = r ^ i * r ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_of_le hi_le]
      rw [hrpow]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Mf * Mg := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_le_n : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hi_le : i ≤ 6 := hi_le_n.trans hn
      have hni_le : n - i ≤ 6 := (Nat.sub_le n i).trans hn
      gcongr
      · exact hfbound i hi_le
      · exact hgbound (n - i) hni_le
    _ = (2 : ℝ) ^ n * Mf * Mg := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      norm_cast
      rw [Nat.sum_range_choose]
    _ ≤ 64 * Mf * Mg := by
      have hpow : (2 : ℝ) ^ n ≤ 64 := by
        have hn' : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
        rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
      gcongr

/-- The scalar function `t ↦ t⁻¹ᐟ²` has uniformly bounded derivatives through order six on
`[1, ∞)`. -/
theorem invSqrtRpow_iteratedFDeriv_norm_le (k : ℕ) (hk : k ≤ 6)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖iteratedFDeriv ℝ k (fun z : ℝ => z ^ (-(1 / 2 : ℝ))) t‖ ≤ 10400 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul]
  simp only [Real.norm_eq_abs]
  have hpowNonneg : 0 ≤ t ^ (-(1 / 2 : ℝ) - k) := Real.rpow_nonneg (by linarith) _
  rw [abs_of_nonneg hpowNonneg]
  have hpow : t ^ (-(1 / 2 : ℝ) - k) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht (by
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      norm_num at hk0 ⊢
      linarith)
  have hcoeff : |(descPochhammer ℝ k).eval (-(1 / 2 : ℝ))| ≤ 10400 := by
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [descPochhammer]
  calc
    |(descPochhammer ℝ k).eval (-(1 / 2 : ℝ))| *
        t ^ (-(1 / 2 : ℝ) - k) ≤
        |(descPochhammer ℝ k).eval (-(1 / 2 : ℝ))| * 1 := by
      gcongr
    _ ≤ 10400 := by simpa using hcoeff

/-- Scale-invariant composition bound for the inverse square root. -/
theorem invSqrtRpow_comp_scaled_deriv_bound {m n : ℕ} {S : (Fin m → ℝ) → ℝ}
    {r Mden : ℝ} {x : Fin m → ℝ} (hr : 0 < r)
    (hS : ContDiffAt ℝ 6 S x) (hSone : 1 ≤ S x)
    (hSbound : ∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q S x‖ * r ^ q ≤ Mden)
    (hn : n ≤ 6) :
    ‖iteratedFDeriv ℝ n (fun y => (S y) ^ (-(1 / 2 : ℝ))) x‖ * r ^ n ≤
      (n.factorial : ℝ) * 10400 * (max Mden 1) ^ n := by
  let outer : ℝ → ℝ := fun z => z ^ (-(1 / 2 : ℝ))
  let t : Set ℝ := Set.Ioi 0
  have hSpos : 0 < S x := zero_lt_one.trans_le hSone
  have htOpen : IsOpen t := isOpen_Ioi
  have htUnique : UniqueDiffOn ℝ t := htOpen.uniqueDiffOn
  have houter : ContDiffOn ℝ 6 outer t := by
    intro z hz
    exact (Real.contDiffAt_rpow_const_of_ne (show z ≠ 0 from ne_of_gt hz)).contDiffWithinAt
  obtain ⟨uS, huS, hSOn⟩ := hS.contDiffOn le_rfl (by simp)
  have hposNhd : S ⁻¹' t ∈ 𝓝 x := hS.continuousAt (htOpen.mem_nhds hSpos)
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp (Filter.inter_mem huS hposNhd)
  have hSs : ContDiffOn ℝ 6 S s := hSOn.mono (hs_sub.trans inter_subset_left)
  have hst : MapsTo S s t := fun y hy => (hs_sub hy).2
  have hsUnique : UniqueDiffOn ℝ s := hs_open.uniqueDiffOn
  let K := max Mden 1
  let D := K / r
  have hKone : 1 ≤ K := le_max_right _ _
  have hMdenK : Mden ≤ K := le_max_left _ _
  have hD : ∀ q, 1 ≤ q → q ≤ n → ‖iteratedFDerivWithin ℝ q S s x‖ ≤ D ^ q := by
    intro q hqone hqn
    have hq6 : q ≤ 6 := hqn.trans hn
    have hq6' : (q : WithTop ℕ∞) ≤ 6 := by exact_mod_cast hq6
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hsUnique (hS.of_le hq6') hxs]
    have hrq : 0 < r ^ q := pow_pos hr q
    change ‖iteratedFDeriv ℝ q S x‖ ≤ (K / r) ^ q
    rw [div_pow]
    apply (le_div_iff₀ hrq).2
    exact (hSbound q hq6).trans
      (hMdenK.trans (le_self_pow₀ hKone (Nat.ne_of_gt hqone)))
  have hC : ∀ q, q ≤ n → ‖iteratedFDerivWithin ℝ q outer t (S x)‖ ≤ 10400 := by
    intro q hqn
    have hq6 : q ≤ 6 := hqn.trans hn
    have hq6' : (q : WithTop ℕ∞) ≤ 6 := by exact_mod_cast hq6
    rw [iteratedFDerivWithin_eq_iteratedFDeriv htUnique
      ((Real.contDiffAt_rpow_const_of_ne hSpos.ne').of_le hq6') hSpos]
    exact invSqrtRpow_iteratedFDeriv_norm_le q hq6 (S x) hSone
  have hn' : (n : WithTop ℕ∞) ≤ 6 := by exact_mod_cast hn
  have hbound := norm_iteratedFDerivWithin_comp_le houter hSs hn'
    htUnique hsUnique hst hxs hC hD
  have houterAt : ContDiffAt ℝ 6 outer (S x) := Real.contDiffAt_rpow_const_of_ne hSpos.ne'
  have hcompAt : ContDiffAt ℝ n (outer ∘ S) x :=
    (houterAt.of_le hn').comp x (hS.of_le hn')
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hsUnique hcompAt hxs] at hbound
  have hscaled := mul_le_mul_of_nonneg_right hbound (pow_nonneg hr.le n)
  change ‖iteratedFDeriv ℝ n (fun y => (S y) ^ (-(1 / 2 : ℝ))) x‖ * r ^ n ≤ _
  calc
    _ ≤ ((n.factorial : ℝ) * 10400 * D ^ n) * r ^ n := hscaled
    _ = (n.factorial : ℝ) * 10400 * K ^ n := by
      simp only [D, div_pow]
      field_simp

/-- The first derivative of square-root normalization is controlled directly by the product,
square-root, and reciprocal derivative formulas. -/
theorem exists_uniform_sqrtQuotient_first_deriv_bound
    (Mnum Mden : ℝ) (hMnum : 0 ≤ Mnum) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {m : ℕ}
      {f S : (Fin m → ℝ) → ℝ} {r : ℝ} {x : Fin m → ℝ},
      0 < r → ContDiffAt ℝ 6 f x → ContDiffAt ℝ 6 S x → 1 ≤ S x →
      (∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q f x‖ * r ^ q ≤ Mnum) →
      (∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q S x‖ * r ^ q ≤ Mden) →
      ‖iteratedFDeriv ℝ 1 (fun y => f y / Real.sqrt (S y)) x‖ * r ≤ A := by
  let A := max (Mnum * (Mden + 1)) 1
  refine ⟨A, le_max_right _ _, ?_⟩
  intro m f S r x hr hf hS hSone hfbound hSbound
  have hSpos : 0 < S x := zero_lt_one.trans_le hSone
  have hsqrtOne : 1 ≤ Real.sqrt (S x) := by
    rw [Real.one_le_sqrt]
    exact hSone
  have hsqrtPos : 0 < Real.sqrt (S x) := zero_lt_one.trans_le hsqrtOne
  have hfDiff : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hSDiff : DifferentiableAt ℝ S x := hS.differentiableAt (by norm_num)
  let g : (Fin m → ℝ) → ℝ := fun y => (Real.sqrt (S y))⁻¹
  have hsqrtHas := hSDiff.hasFDerivAt.sqrt hSpos.ne'
  have hgHas : HasFDerivAt g
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (-((Real.sqrt (S x)) ^ 2)⁻¹)).comp
          ((1 / (2 * Real.sqrt (S x))) • fderiv ℝ S x)) x := by
    simpa [g, Function.comp_def] using
      (hasFDerivAt_inv hsqrtPos.ne').comp x hsqrtHas
  have hgDiff : DifferentiableAt ℝ g x := hgHas.differentiableAt
  have hf0 : ‖f x‖ ≤ Mnum := by
    simpa [norm_iteratedFDeriv_zero] using hfbound 0 (by norm_num)
  have hf1 : ‖fderiv ℝ f x‖ * r ≤ Mnum := by
    simpa [norm_iteratedFDeriv_one] using hfbound 1 (by norm_num)
  have hS1 : ‖fderiv ℝ S x‖ * r ≤ Mden := by
    simpa [norm_iteratedFDeriv_one] using hSbound 1 (by norm_num)
  have hg0 : ‖g x‖ ≤ 1 := by
    change ‖(Real.sqrt (S x))⁻¹‖ ≤ 1
    rw [norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_le_one_of_one_le₀ hsqrtOne
  have ha : |1 / (2 * Real.sqrt (S x))| ≤ 1 := by
    rw [abs_div, abs_one, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_one₀ (mul_pos (by norm_num) hsqrtPos)).2 (by nlinarith)
  have hb : ‖-((Real.sqrt (S x)) ^ 2)⁻¹‖ ≤ 1 := by
    rw [norm_neg, norm_inv, norm_pow, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hsqrtOne)
  have hg1 : ‖fderiv ℝ g x‖ ≤ ‖fderiv ℝ S x‖ := by
    rw [hgHas.fderiv]
    calc
      ‖(ContinuousLinearMap.toSpanSingleton ℝ (-((Real.sqrt (S x)) ^ 2)⁻¹)).comp
          ((1 / (2 * Real.sqrt (S x))) • fderiv ℝ S x)‖ ≤
          ‖ContinuousLinearMap.toSpanSingleton ℝ (-((Real.sqrt (S x)) ^ 2)⁻¹)‖ *
            ‖(1 / (2 * Real.sqrt (S x))) • fderiv ℝ S x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (1 * ‖fderiv ℝ S x‖) := by
        gcongr
        · simpa using hb
        · exact (norm_smul_le _ _).trans
            (mul_le_mul_of_nonneg_right
              (by simpa [Real.norm_eq_abs] using ha)
              (norm_nonneg (fderiv ℝ S x)))
      _ = ‖fderiv ℝ S x‖ := by ring
  rw [norm_iteratedFDeriv_one]
  have hfun : (fun y => f y / Real.sqrt (S y)) = fun y => f y * g y := by
    funext y
    simp [g, div_eq_mul_inv]
  rw [hfun]
  have hfd : fderiv ℝ (fun y => f y * g y) x =
      f x • fderiv ℝ g x + g x • fderiv ℝ f x := by
    change fderiv ℝ (f * g) x = _
    exact fderiv_mul hfDiff hgDiff
  rw [hfd]
  calc
    ‖f x • fderiv ℝ g x + g x • fderiv ℝ f x‖ * r ≤
        (‖f x‖ * ‖fderiv ℝ g x‖ + ‖g x‖ * ‖fderiv ℝ f x‖) * r := by
      gcongr
      have hleft : ‖f x • fderiv ℝ g x‖ ≤ ‖f x‖ * ‖fderiv ℝ g x‖ :=
        norm_smul_le (f x) (fderiv ℝ g x)
      have hright : ‖g x • fderiv ℝ f x‖ ≤ ‖g x‖ * ‖fderiv ℝ f x‖ :=
        norm_smul_le (g x) (fderiv ℝ f x)
      exact (norm_add_le _ _).trans (add_le_add hleft hright)
    _ ≤ (Mnum * ‖fderiv ℝ S x‖ + 1 * ‖fderiv ℝ f x‖) * r := by
      gcongr
    _ = Mnum * (‖fderiv ℝ S x‖ * r) + ‖fderiv ℝ f x‖ * r := by ring
    _ ≤ Mnum * Mden + Mnum := by gcongr
    _ = Mnum * (Mden + 1) := by ring
    _ ≤ A := le_max_left _ _

/-- Standard finite-order calculus input for square-root normalization. This statement is
independent of the intrinsic scale and covering construction: bounded numerator and denominator
jets at one positive-denominator point give bounded jets of `f / sqrt S` at the same scale. -/
theorem exists_uniform_sqrtQuotient_higher_deriv_bound
    (Mnum Mden : ℝ) (hMnum : 0 ≤ Mnum) (hMden : 0 ≤ Mden) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {m : ℕ}
      {f S : (Fin m → ℝ) → ℝ} {r : ℝ} {x : Fin m → ℝ},
      0 < r → ContDiffAt ℝ 6 f x → ContDiffAt ℝ 6 S x → 1 ≤ S x →
      (∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q f x‖ * r ^ q ≤ Mnum) →
      (∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q S x‖ * r ^ q ≤ Mden) →
      ∀ j, 2 ≤ j → j ≤ 6 →
        ‖iteratedFDeriv ℝ j (fun y => f y / Real.sqrt (S y)) x‖ * r ^ j ≤ A := by
  let K := max Mden 1
  let Mg := (Nat.factorial 6 : ℝ) * 10400 * K ^ 6
  let A := max (64 * Mnum * Mg) 1
  refine ⟨A, le_max_right _ _, ?_⟩
  intro m f S r x hr hf hS hSone hfbound hSbound j _hjtwo hj
  have hSpos : 0 < S x := zero_lt_one.trans_le hSone
  let g : (Fin m → ℝ) → ℝ := fun y => (S y) ^ (-(1 / 2 : ℝ))
  have hg : ContDiffAt ℝ 6 g x := by
    simpa [g, Function.comp_def] using
      (Real.contDiffAt_rpow_const_of_ne hSpos.ne').comp x hS
  have hKone : 1 ≤ K := le_max_right _ _
  have hKnonneg : 0 ≤ K := hMden.trans (le_max_left _ _)
  have hMg : 0 ≤ Mg := by
    dsimp [Mg]
    exact mul_nonneg (by positivity) (pow_nonneg hKnonneg 6)
  have hgbound : ∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q g x‖ * r ^ q ≤ Mg := by
    intro q hq
    have hcomp := invSqrtRpow_comp_scaled_deriv_bound hr hS hSone hSbound hq
    have hqfact : (q.factorial : ℝ) ≤ (Nat.factorial 6 : ℝ) := by
      exact_mod_cast Nat.factorial_le hq
    have hqpow : K ^ q ≤ K ^ 6 := pow_le_pow_right₀ hKone hq
    calc
      ‖iteratedFDeriv ℝ q g x‖ * r ^ q ≤
          (q.factorial : ℝ) * 10400 * K ^ q := by simpa [g, K] using hcomp
      _ ≤ (Nat.factorial 6 : ℝ) * 10400 * K ^ 6 := by gcongr
      _ = Mg := rfl
  have hproduct := norm_iteratedFDeriv_mul_scaled_le_of_contDiffAt
    hr hMnum hMg hf hg hfbound hgbound hj
  have heq : (fun y => f y / Real.sqrt (S y)) =ᶠ[𝓝 x] (fun y => f y * g y) := by
    filter_upwards [hS.continuousAt (isOpen_Ioi.mem_nhds hSpos)] with y hy
    change f y / Real.sqrt (S y) = f y * (S y) ^ (-(1 / 2 : ℝ))
    rw [div_eq_mul_inv, Real.sqrt_eq_rpow, Real.rpow_neg hy.le]
  have hderiv := (heq.iteratedFDeriv ℝ j).eq_of_nhds
  rw [hderiv]
  exact hproduct.trans (le_max_left _ _)

/-- All positive derivative orders through six, obtained by combining the explicit first-order
calculation with the proved higher-order calculus estimate. -/
theorem exists_uniform_sqrtQuotient_positive_deriv_bound
    (Mnum Mden : ℝ) (hMnum : 0 ≤ Mnum) (hMden : 0 ≤ Mden) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {m : ℕ}
      {f S : (Fin m → ℝ) → ℝ} {r : ℝ} {x : Fin m → ℝ},
      0 < r → ContDiffAt ℝ 6 f x → ContDiffAt ℝ 6 S x → 1 ≤ S x →
      (∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q f x‖ * r ^ q ≤ Mnum) →
      (∀ q, q ≤ 6 → ‖iteratedFDeriv ℝ q S x‖ * r ^ q ≤ Mden) →
      ∀ j, 1 ≤ j → j ≤ 6 →
        ‖iteratedFDeriv ℝ j (fun y => f y / Real.sqrt (S y)) x‖ * r ^ j ≤ A := by
  obtain ⟨A₁, hA₁, hfirst⟩ :=
    exists_uniform_sqrtQuotient_first_deriv_bound Mnum Mden hMnum
  obtain ⟨A₂, hA₂, hhigher⟩ :=
    exists_uniform_sqrtQuotient_higher_deriv_bound Mnum Mden hMnum hMden
  let A := max A₁ A₂
  refine ⟨A, hA₁.trans (le_max_left _ _), ?_⟩
  intro m f S r x hr hf hS hSone hfbound hSbound j hjone hj
  by_cases hj1 : j = 1
  · subst j
    have hle : A₁ ≤ A := le_max_left _ _
    simpa only [pow_one] using (hfirst hr hf hS hSone hfbound hSbound).trans hle
  · exact (hhigher hr hf hS hSone hfbound hSbound j (by omega) hj).trans
      (le_max_right _ _)

/-- Positive-order derivative propagation through square normalization. All geometric,
local-finiteness, positivity, and smoothness hypotheses are explicit in this statement. -/
theorem exists_uniform_selectedSquareNormalizedFamily_positive_deriv_bound
    (n : ℕ) (C L ε : ℝ) (hC : 1 ≤ C) (hL : C + 2 < L) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {u : (Fin n → ℝ) → ℝ} {c : ℝ},
      2 * L * ε ≤ c →
      (∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
        nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
        nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x) →
      ∀ (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
          Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
        (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
          Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)),
        Set.range (fun x : {x : Fin n → ℝ // 0 < nonnegativeJetScale u x} => x.1) ⊆
          ⋃ color, ⋃ z ∈ s color,
            Metric.ball z.1 (ε * nonnegativeJetScale u z.1) →
        ∀ i, i ∈ (selectedIntrinsicCentersNatIndexing hε s hdis).active →
          ∀ j, 1 ≤ j → j ≤ 6 → ∀ x,
            ‖iteratedFDeriv ℝ j (squareNormalizedFamily
              (activeIntrinsicRawBump u
                (selectedIntrinsicCentersNatIndexing hε s hdis).value
                (selectedIntrinsicCentersNatIndexing hε s hdis).active ε) i) x‖ *
              (ε * nonnegativeJetScale u
                ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)) ^ j ≤ A := by
  obtain ⟨Araw, hArawOne, hAraw⟩ := unitScaleBump_uniform_deriv_bound n
  obtain ⟨Asq, hAsqOne, hAsq⟩ := unitScaleBumpSquare_uniform_deriv_bound n
  have hL0 : 0 ≤ L := by linarith
  let B := intrinsicOverlapBound n hL0 hC
  let M : ℕ → ℝ := fun q => B * (Asq * C ^ q)
  let Mden := max (((Finset.range 7).image M).max' (by simp)) 1
  have hMdenOne : 1 ≤ Mden := le_max_right _ _
  have hMbound (q : ℕ) (hq : q ≤ 6) : M q ≤ Mden :=
    (Finset.le_max' ((Finset.range 7).image M) (M q)
      (Finset.mem_image_of_mem M (by
        simpa only [Finset.mem_range] using Nat.lt_succ_of_le hq))).trans
          (le_max_left _ _)
  obtain ⟨A, hA, hquot⟩ := exists_uniform_sqrtQuotient_positive_deriv_bound
    Araw Mden (zero_le_one.trans hArawOne) (zero_le_one.trans hMdenOne)
  refine ⟨A, hA, ?_⟩
  intro u c hsmall hvar s hdis hcover i hi j hjone hj x
  let I := selectedIntrinsicCentersNatIndexing hε s hdis
  let bump := activeIntrinsicRawBump u I.value I.active ε
  let S : (Fin n → ℝ) → ℝ := fun y => ∑' k, bump k y ^ 2
  let r := ε * nonnegativeJetScale u (I.value i)
  have hcenter : ∀ k, k ∈ I.active → 0 < nonnegativeJetScale u (I.value k) := by
    exact selectedIntrinsicCentersNatIndexing_value_pos hε s hdis
  have hiI : i ∈ I.active := by simpa [I] using hi
  have hri : 0 < r := mul_pos hε (hcenter i hiI)
  have hoverlap := selectedIntrinsicCentersNatIndexing_overlap_bound n hL0 hC hε
    hsmall hvar s hdis
  by_cases hzero : iteratedFDeriv ℝ j (squareNormalizedFamily bump i) x = 0
  · rw [hzero, norm_zero, zero_mul]
    exact zero_le_one.trans hA
  · have hsuppNorm := support_iteratedFDeriv_subset j hzero
    have hsuppRaw : x ∈ closure (Function.support (bump i)) :=
      closure_mono (support_squareNormalizedFamily_subset bump i) hsuppNorm
    have hsupport : Function.support (bump i) =
        Metric.ball (I.value i) (2 * r) := by
      have hs := support_activeIntrinsicRawBump hε hcenter i
      simpa [bump, activeScaledBall, hiI, r] using hs
    rw [hsupport] at hsuppRaw
    have hclosed : x ∈ Metric.closedBall (I.value i) (2 * r) :=
      Metric.closure_ball_subset_closedBall hsuppRaw
    have hxball : x ∈ Metric.ball (I.value i) (3 * r) :=
      Metric.closedBall_subset_ball (mul_lt_mul_of_pos_right (by norm_num) hri) hclosed
    have hsmall3 : 3 * ε ≤ c := by
      calc
        3 * ε ≤ (2 * L) * ε :=
          mul_le_mul_of_nonneg_right (by linarith : 3 ≤ 2 * L) hε.le
        _ = 2 * L * ε := by ring
        _ ≤ c := hsmall
    have hdistx : dist (I.value i) x ≤ c * nonnegativeJetScale u (I.value i) := by
      have hxlt : dist (I.value i) x < 3 * r := by
        simpa [dist_comm] using Metric.mem_ball.mp hxball
      calc
        dist (I.value i) x ≤ 3 * r := hxlt.le
        _ = (3 * ε) * nonnegativeJetScale u (I.value i) := by simp [r]; ring
        _ ≤ c * nonnegativeJetScale u (I.value i) :=
          mul_le_mul_of_nonneg_right hsmall3 (hcenter i hiI).le
    have hxpos : 0 < nonnegativeJetScale u x := by
      have hcomp := (hvar (I.value i) x hdistx).1
      by_contra hnot
      have hxzero : nonnegativeJetScale u x = 0 :=
        le_antisymm (not_lt.mp hnot) (nonnegativeJetScale_nonneg u x)
      rw [hxzero, mul_zero] at hcomp
      exact (not_le_of_gt (hcenter i hiI)) hcomp
    have hSbounds := selectedIntrinsicRawBump_square_tsum_mem_Icc
      hC hL hε hsmall hvar s hdis hcover x hxpos
    have hSone : 1 ≤ S x := by simpa [S, bump, I] using hSbounds.1
    have hSsmooth : ContDiffAt ℝ 6 S x := by
      simpa [S, bump, I] using selectedRawSquareTsum_contDiffAt
        hC hL hε hsmall hvar s hdis hoverlap x hxpos
    have hbumpsmooth : ContDiffAt ℝ 6 (bump i) x :=
      (activeIntrinsicRawBump_contDiff i).contDiffAt
    have hnumbound : ∀ q, q ≤ 6 →
        ‖iteratedFDeriv ℝ q (bump i) x‖ * r ^ q ≤ Araw := by
      intro q hq
      simpa [bump, r] using activeIntrinsicRawBump_scaled_deriv_bound
        hAraw hε hcenter i hiI q hq x
    have hdenbound : ∀ q, q ≤ 6 →
        ‖iteratedFDeriv ℝ q S x‖ * r ^ q ≤ Mden := by
      intro q hq
      have hqbound := selectedRawSquareTsum_scaled_deriv_bound hAsq
        hC hL hε hsmall hvar s hdis i hi q hq x
        (by simpa [I, r] using hxball)
      have hqbound' : ‖iteratedFDeriv ℝ q S x‖ * r ^ q ≤ M q := by
        simpa [S, bump, I, r, M, B] using hqbound
      exact hqbound'.trans (hMbound q hq)
    have hfinal := hquot hri hbumpsmooth hSsmooth hSone hnumbound hdenbound
      j hjone hj
    have hnormalized : squareNormalizedFamily bump i =
        fun y => bump i y / Real.sqrt (S y) := by
      funext y
      simp only [squareNormalizedFamily, S]
    rw [hnormalized]
    simpa [bump, S, r, I] using hfinal

/-- All-order derivative propagation, obtained by combining the elementary zeroth-order
bound with the positive-order estimate. -/
theorem exists_uniform_selectedSquareNormalizedFamily_scaled_deriv_bound
    (n : ℕ) (C L ε : ℝ) (hC : 1 ≤ C) (hL : C + 2 < L) (hε : 0 < ε) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {u : (Fin n → ℝ) → ℝ} {c : ℝ},
      2 * L * ε ≤ c →
      (∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
        nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
        nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x) →
      ∀ (s : Fin (Besicovitch.multiplicity (Fin n → ℝ)) →
          Set {x : Fin n → ℝ // 0 < nonnegativeJetScale u x})
        (hdis : ∀ color, (s color).PairwiseDisjoint fun i =>
          Metric.closedBall i.1 (ε * nonnegativeJetScale u i.1)),
        Set.range (fun x : {x : Fin n → ℝ // 0 < nonnegativeJetScale u x} => x.1) ⊆
          ⋃ color, ⋃ z ∈ s color,
            Metric.ball z.1 (ε * nonnegativeJetScale u z.1) →
        ∀ i, i ∈ (selectedIntrinsicCentersNatIndexing hε s hdis).active →
          ∀ j, j ≤ 6 → ∀ x,
            ‖iteratedFDeriv ℝ j (squareNormalizedFamily
              (activeIntrinsicRawBump u
                (selectedIntrinsicCentersNatIndexing hε s hdis).value
                (selectedIntrinsicCentersNatIndexing hε s hdis).active ε) i) x‖ *
              (ε * nonnegativeJetScale u
                ((selectedIntrinsicCentersNatIndexing hε s hdis).value i)) ^ j ≤ A := by
  obtain ⟨A, hA, hpositive⟩ :=
    exists_uniform_selectedSquareNormalizedFamily_positive_deriv_bound n C L ε hC hL hε
  refine ⟨A, hA, ?_⟩
  intro u c hsmall hvar s hdis hcover i hi j hj x
  by_cases hj0 : j = 0
  · subst j
    exact (selectedSquareNormalizedFamily_zero_order_scaled_deriv_bound hC hL hε hsmall
      hvar s hdis hcover i x).trans hA
  · exact hpositive hsmall hvar s hdis hcover i hi j
      (Nat.one_le_iff_ne_zero.mpr hj0) hj x

-- The jet-bound hypothesis is part of the public scale-cover interface used downstream.
set_option linter.unusedVariables false in
/-- A slow intrinsic scale admits a countable quantitative square partition with uniform
normalized derivative bounds. -/
theorem quantitativeSquarePartition_of_slowVariation {n : ℕ}
    (hjets : HasUniformNonnegativeJetBounds n)
    (hslow : HasIntrinsicScaleSlowVariation n) : HasUniformScaleCover n := by
  rcases hslow with ⟨c₀, C, hc₀, hC, hvariation⟩
  intro D hD
  let c := min c₀ 1
  classical
  let L := max D (C + 3)
  let ε := c / (4 * L)
  have hc : 0 < c := by simp [c, hc₀]
  have hc_le_c₀ : c ≤ c₀ := min_le_left _ _
  have hc_le_one : c ≤ 1 := min_le_right _ _
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hL_lower : C + 3 ≤ L := le_max_right _ _
  have hDL : D ≤ L := le_max_left _ _
  have hLpos : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have hLstrict : C + 2 < L := by linarith
  have hε : 0 < ε := by positivity
  have hε_le_one : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < 4 * L)).2
    nlinarith
  have hsmallL : 2 * L * ε ≤ c := by
    have hLe : L ≠ 0 := hLpos.ne'
    dsimp [ε]
    calc
      2 * L * (c / (4 * L)) = c / 2 := by field_simp; ring
      _ ≤ c := by linarith
  have hsmallD : 2 * D * ε ≤ c := by
    calc
      2 * D * ε ≤ 2 * L * ε := by gcongr
      _ ≤ c := hsmallL
  obtain ⟨Aderiv, hAderiv, hderiv⟩ :=
    exists_uniform_selectedSquareNormalizedFamily_scaled_deriv_bound
      n C L ε hC hLstrict hε
  let A := max Aderiv ε⁻¹
  have hA : 1 ≤ A := hAderiv.trans (le_max_left _ _)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hinv_le_A : ε⁻¹ ≤ A := le_max_right _ _
  have hAε : 1 ≤ A * ε := by
    calc
      1 = ε⁻¹ * ε := by field_simp
      _ ≤ A * ε := mul_le_mul_of_nonneg_right hinv_le_A hε.le
  have hD0 : 0 ≤ D := (by linarith : 0 ≤ D)
  let BD := intrinsicOverlapBound n hD0 hC
  let B := max BD 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨A, B, hA, hB, ?_⟩
  intro u hu
  have hvar : ∀ x y, dist x y ≤ c * nonnegativeJetScale u x →
      nonnegativeJetScale u x ≤ C * nonnegativeJetScale u y ∧
      nonnegativeJetScale u y ≤ C * nonnegativeJetScale u x := by
    intro x y hxy
    apply hvariation u hu x y
    exact hxy.trans (mul_le_mul_of_nonneg_right hc_le_c₀
      (nonnegativeJetScale_nonneg u x))
  obtain ⟨s, hdis, hcover⟩ := exists_disjoint_intrinsic_covering_families hu ε hε
  let I := selectedIntrinsicCentersNatIndexing hε s hdis
  let bump := activeIntrinsicRawBump u I.value I.active ε
  let cutoff := squareNormalizedFamily bump
  let radius : ℕ → ℝ := fun i => if i ∈ I.active then
    ε * nonnegativeJetScale u (I.value i) else 1
  have hcenter : ∀ i, i ∈ I.active → 0 < nonnegativeJetScale u (I.value i) := by
    exact selectedIntrinsicCentersNatIndexing_value_pos hε s hdis
  have hoverlapL := selectedIntrinsicCentersNatIndexing_overlap_bound n hL0 hC hε
    hsmallL hvar s hdis
  have hoverlapD := selectedIntrinsicCentersNatIndexing_overlap_bound n hD0 hC hε
    hsmallD hvar s hdis
  have hcont := selectedSquareNormalizedFamily_contDiff hC hLstrict hε hsmallL
    hvar s hdis hcover hoverlapL
  have hderiv' := hderiv hsmallL hvar s hdis hcover
  refine ⟨{
    two_le_dilation := hD
    center := I.value
    radius := radius
    cutoff := cutoff
    active := I.active
    cutoff_eq_zero_of_not_active := ?_
    radius_pos := ?_
    radius_comparable := ?_
    cutoff_contDiff := ?_
    cutoff_support := ?_
    square_partition := ?_
    overlap := ?_
    scaled_cutoff := ?_ }⟩
  · intro i hi
    funext x
    simp [cutoff, squareNormalizedFamily, bump, activeIntrinsicRawBump, hi]
  · intro i hi
    simp [radius, hi, mul_pos hε (hcenter i hi)]
  · intro i hi
    have hRi : 0 ≤ nonnegativeJetScale u (I.value i) :=
      nonnegativeJetScale_nonneg u (I.value i)
    constructor
    · simp only [radius, ite_eq_left hi]
      calc
        ε * nonnegativeJetScale u (I.value i) ≤
            1 * nonnegativeJetScale u (I.value i) :=
          mul_le_mul_of_nonneg_right hε_le_one hRi
        _ = nonnegativeJetScale u (I.value i) := one_mul _
    · simp only [radius, ite_eq_left hi]
      calc
        nonnegativeJetScale u (I.value i) ≤
            (A * ε) * nonnegativeJetScale u (I.value i) :=
          by simpa only [one_mul] using mul_le_mul_of_nonneg_right hAε hRi
        _ = A * (ε * nonnegativeJetScale u (I.value i)) := by ring
  · intro i
    simpa [cutoff, bump, I] using hcont i
  · intro i
    by_cases hi : i ∈ I.active
    · have hsupp := support_squareNormalizedFamily_subset bump i
      have hraw := support_activeIntrinsicRawBump hε hcenter i
      rw [hraw] at hsupp
      simpa [cutoff, radius, activeScaledBall, hi] using hsupp
    · have hzero : cutoff i = 0 := by
        funext x
        simp [cutoff, squareNormalizedFamily, bump, activeIntrinsicRawBump, hi]
      rw [hzero]
      simp [Function.support]
  · intro x hx
    have hL2 : 2 ≤ L := by linarith
    have hpoint : ∀ y, Set.Finite {i | bump i y ≠ 0} := by
      exact activeIntrinsicRawBump_pointFinite hL2 hε hcenter hoverlapL
    obtain ⟨i, hi, hone⟩ := exists_selectedIntrinsicRawBump_eq_one hε s hdis hcover hx
    have hone' : bump i x = 1 := by simpa [bump, I] using hone
    have hsum : 0 < ∑' k, bump k x ^ 2 :=
      zero_lt_one.trans_le (one_le_raw_square_tsum bump hpoint x i hone')
    simpa [cutoff] using squareNormalizedFamily_square_tsum bump hpoint x hsum
  · intro x t
    have hbound := hoverlapD x t
    have hrewrite : {i | i ∈ t ∧ i ∈ I.active ∧
        x ∈ Metric.ball (I.value i) (D * radius i)} =
        {i | i ∈ t ∧ i ∈ I.active ∧
          x ∈ Metric.ball (I.value i)
            (D * (ε * nonnegativeJetScale u (I.value i)))} := by
      ext i
      by_cases hi : i ∈ I.active <;> simp [radius, hi]
    rw [hrewrite]
    exact hbound.trans (le_max_left _ _)
  · intro i j hj x
    by_cases hi : i ∈ I.active
    · have hb := hderiv' i hi j hj x
      simpa only [cutoff, bump, I, radius, ite_eq_left hi] using
        hb.trans (show Aderiv ≤ A from le_max_left _ _)
    · have hzero : cutoff i = 0 := by
        funext y
        simp [cutoff, squareNormalizedFamily, bump, activeIntrinsicRawBump, hi]
      rw [hzero]
      change ‖iteratedFDeriv ℝ j (fun _ : Fin n → ℝ => (0 : ℝ)) x‖ * radius i ^ j ≤ A
      rw [iteratedFDeriv_fun_zero]
      simpa using hA0

/-- The complete scale-cover stage, assembled from its two analytic leaves. -/
theorem uniformScaleCover_of_jetBounds {n : ℕ}
    (hjets : HasUniformNonnegativeJetBounds n) : HasUniformScaleCover n := by
  exact quantitativeSquarePartition_of_slowVariation hjets
    (intrinsicScale_slowVariation_of_jetBounds hjets)

end QuarticConvergence
end OptimalConvergenceRates

end
