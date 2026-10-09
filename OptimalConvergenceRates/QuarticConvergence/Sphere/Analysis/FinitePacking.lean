/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/FinitePacking.lean

  Finite-resolution truncation, dyadic labels, and ambient-grid shell packing.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.Radial
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterContinuousCancellation
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotationJets
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterSphereTaylor
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.ContinuousRootFilter
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Reflection
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Repair

open Finset MeasureTheory MvPolynomial Set
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers
open SpherePolynomialQuadrature

/-- A set is finite when all of its finite subsets have a common cardinality bound. -/
theorem finite_of_finite_subset_ncard_le {α : Type*} (s : Set α) (B : ℕ)
    (h : ∀ t : Set α, t ⊆ s → t.Finite → t.ncard ≤ B) : s.Finite := by
  by_contra hs
  have hinfinite : s.Infinite := hs
  obtain ⟨t, hts, htfinite, htcard⟩ :=
    hinfinite.exists_subset_ncard_eq (B + 1)
  have hle := h t hts htfinite
  omega

/-- Bounded finite-subfamily overlap makes the full set of atoms through one point finite. -/
theorem SphereAtomFamily.finite_cap_indices {n : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {C : ℝ} {B : ℕ} (atoms : SphereAtomFamily n F C B)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    {i | i ∈ atoms.active ∧
      sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2}.Finite := by
  apply finite_of_finite_subset_ncard_le _ B
  intro t ht htfinite
  let u : Finset ℕ := htfinite.toFinset
  have hoverlap := atoms.dilated_overlap x hx u
  have heq :
      {i | i ∈ u ∧ i ∈ atoms.active ∧
        sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2} = t := by
    ext i
    simp only [Set.mem_setOf_eq]
    rw [htfinite.mem_toFinset]
    constructor
    · exact fun hi ↦ hi.1
    · intro hi
      exact ⟨hi, (ht hi).1, (ht hi).2⟩
  rw [heq] at hoverlap
  exact hoverlap

/-- On the compact sphere, only finitely many active atoms have radius at least `r > 0`. -/
theorem SphereAtomFamily.finite_active_radius_ge {n : ℕ}
    {F : MvPolynomial (Fin n) ℝ} {C : ℝ} {B : ℕ}
    (atoms : SphereAtomFamily n F C B) {r : ℝ} (hr : 0 < r) :
    {i | i ∈ atoms.active ∧ r ≤ atoms.radius i}.Finite := by
  obtain ⟨t, _htsub, htfinite, hcover⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (euclideanUnitSphere n))).finite_cover_balls
      (half_pos hr)
  let capIndices : euclideanUnitSphere n → Set ℕ := fun y ↦
    {i | i ∈ atoms.active ∧
      sphereChordalSq (euclideanSphereCoordinates y) (atoms.center i).1 ≤
        atoms.radius i ^ 2}
  have hfiniteUnion : (⋃ y ∈ t, capIndices y).Finite := by
    apply htfinite.biUnion
    intro y hy
    exact atoms.finite_cap_indices (euclideanSphereCoordinates y)
      (euclideanSphereCoordinates_mem_sphereSet y)
  apply hfiniteUnion.subset
  intro i hi
  have hcenter : sphereSetEuclideanCoordinates (atoms.center i) ∈ Set.univ :=
    Set.mem_univ _
  have hc := hcover hcenter
  simp only [Set.mem_iUnion, Metric.mem_ball] at hc
  obtain ⟨y, hy, hdist⟩ := hc
  refine Set.mem_iUnion_of_mem y ?_
  refine Set.mem_iUnion_of_mem hy ?_
  change i ∈ capIndices y
  refine ⟨hi.1, ?_⟩
  change sphereChordalSq (euclideanSphereCoordinates y)
    (euclideanSphereCoordinates (sphereSetEuclideanCoordinates (atoms.center i))) ≤
      atoms.radius i ^ 2
  rw [sphereChordalSq_euclideanSphereCoordinates_eq_dist_sq]
  have hradius_nonneg : 0 ≤ atoms.radius i := le_trans (le_of_lt hr) hi.2
  have hdist_le : dist y (sphereSetEuclideanCoordinates (atoms.center i)) ≤ r := by
    rw [dist_comm]
    linarith
  exact (sq_le_sq₀ dist_nonneg hradius_nonneg).2
    (hdist_le.trans hi.2)

/-- The active indices retained at resolution `1 / k`. -/
noncomputable def SphereAtomFamily.retainedIndices {n : ℕ}
    {F : MvPolynomial (Fin n) ℝ} {C : ℝ} {B : ℕ}
    (atoms : SphereAtomFamily n F C B) (k : ℕ) (hk : 1 ≤ k) : Finset ℕ :=
  (atoms.finite_active_radius_ge (r := 1 / (k : ℝ)) (by positivity)).toFinset

@[simp] theorem SphereAtomFamily.mem_retainedIndices {n : ℕ}
    {F : MvPolynomial (Fin n) ℝ} {C : ℝ} {B : ℕ}
    (atoms : SphereAtomFamily n F C B) (k : ℕ) (hk : 1 ≤ k) (i : ℕ) :
    i ∈ atoms.retainedIndices k hk ↔
      i ∈ atoms.active ∧ 1 / (k : ℝ) ≤ atoms.radius i := by
  simp [SphereAtomFamily.retainedIndices]

/-- The bounded-overlap axiom controls the complete cap-index set, not just finite tests. -/
theorem SphereAtomFamily.cap_indices_ncard_le {n : ℕ}
    {F : MvPolynomial (Fin n) ℝ} {C : ℝ} {B : ℕ}
    (atoms : SphereAtomFamily n F C B) (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    Set.ncard {i | i ∈ atoms.active ∧
      sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2} ≤ B := by
  let hfinite := atoms.finite_cap_indices x hx
  let s := hfinite.toFinset
  have hoverlap := atoms.dilated_overlap x hx s
  have heq :
      {i | i ∈ s ∧ i ∈ atoms.active ∧
        sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2} =
      {i | i ∈ atoms.active ∧
        sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2} := by
    ext i
    simp only [Set.mem_setOf_eq]
    rw [hfinite.mem_toFinset]
    tauto
  rw [heq] at hoverlap
  exact hoverlap

/-- The zeroth scaled-jet estimate is the pointwise atom amplitude bound. -/
theorem SphereAtomFamily.abs_root_le {n : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {C : ℝ} {B : ℕ} (atoms : SphereAtomFamily n F C B)
    (i : ℕ) (x : Fin n → ℝ) :
    |atoms.root i x| ≤ C * atoms.radius i ^ 2 := by
  have hjet := atoms.scaled_jets i 0 (by omega) x
  simpa [iteratedFDeriv_zero_apply, Real.norm_eq_abs] using hjet

/-- An atom discarded below resolution `1 / k` has quartically small square. -/
theorem SphereAtomFamily.root_sq_le_of_radius_lt_inv {n : ℕ}
    {F : MvPolynomial (Fin n) ℝ} {C : ℝ} {B : ℕ}
    (atoms : SphereAtomFamily n F C B) (k : ℕ) (hk : 1 ≤ k)
    (i : ℕ) (hi : i ∈ atoms.active)
    (hsmall : atoms.radius i < 1 / (k : ℝ)) (x : Fin n → ℝ) :
    atoms.root i x ^ 2 ≤ C ^ 2 * (1 / (k : ℝ)) ^ 4 := by
  have hroot := atoms.abs_root_le i x
  have hrnonneg : 0 ≤ atoms.radius i := (atoms.radius_pos i hi).le
  have hrle : atoms.radius i ≤ 1 / (k : ℝ) := hsmall.le
  have hinvnonneg : 0 ≤ 1 / (k : ℝ) := by positivity
  calc
    atoms.root i x ^ 2 = |atoms.root i x| ^ 2 := by rw [sq_abs]
    _ ≤ (C * atoms.radius i ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hroot 2
    _ = C ^ 2 * atoms.radius i ^ 4 := by ring
    _ ≤ C ^ 2 * (1 / (k : ℝ)) ^ 4 := by gcongr

/-- The discarded complement has a uniform pointwise quartic tail bound. -/
theorem SphereAtomFamily.retained_tail_tsum_le {n : ℕ}
    {F : MvPolynomial (Fin n) ℝ} {C : ℝ} {B : ℕ}
    (atoms : SphereAtomFamily n F C B) (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    ∑' j : {i // i ∉ atoms.retainedIndices k hk}, atoms.root j.1 x ^ 2 ≤
      (B : ℝ) * (C ^ 2 * (1 / (k : ℝ)) ^ 4) := by
  let tailSupport : Set {i // i ∉ atoms.retainedIndices k hk} :=
    {j | atoms.root j.1 x ^ 2 ≠ 0}
  have himageSubset :
      ((Subtype.val : {i // i ∉ atoms.retainedIndices k hk} → ℕ) '' tailSupport) ⊆
        {i | i ∈ atoms.active ∧
          sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2} := by
    rintro i ⟨j, hj, rfl⟩
    have hroot : atoms.root j.1 x ≠ 0 := by
      intro hzero
      exact hj (by simp [hzero])
    have hactive : j.1 ∈ atoms.active := by
      by_contra hnot
      rw [atoms.root_eq_zero_of_not_active j.1 hnot] at hroot
      exact hroot rfl
    exact ⟨hactive, atoms.supported j.1 x hx hroot⟩
  have hsupportFinite : tailSupport.Finite := by
    apply Set.Finite.of_finite_image
    · exact (atoms.finite_cap_indices x hx).subset himageSubset
    · exact Subtype.val_injective.injOn
  have hcard : tailSupport.ncard ≤ B := by
    calc
      tailSupport.ncard =
          ((Subtype.val : {i // i ∉ atoms.retainedIndices k hk} → ℕ) ''
            tailSupport).ncard :=
        (Set.ncard_image_of_injective tailSupport Subtype.val_injective).symm
      _ ≤ Set.ncard {i | i ∈ atoms.active ∧
          sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2} :=
        Set.ncard_le_ncard himageSubset (atoms.finite_cap_indices x hx)
      _ ≤ B := atoms.cap_indices_ncard_le x hx
  rw [tsum_eq_sum (s := hsupportFinite.toFinset)]
  · calc
      ∑ j ∈ hsupportFinite.toFinset, atoms.root j.1 x ^ 2 ≤
          ∑ _j ∈ hsupportFinite.toFinset,
            C ^ 2 * (1 / (k : ℝ)) ^ 4 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjSupport : j ∈ tailSupport := by
          simpa using hj
        have hroot : atoms.root j.1 x ≠ 0 := by
          intro hzero
          exact hjSupport (by simp [hzero])
        have hactive : j.1 ∈ atoms.active := by
          by_contra hnot
          rw [atoms.root_eq_zero_of_not_active j.1 hnot] at hroot
          exact hroot rfl
        have hsmall : atoms.radius j.1 < 1 / (k : ℝ) := by
          apply lt_of_not_ge
          intro hlower
          exact j.2 ((atoms.mem_retainedIndices k hk j.1).2 ⟨hactive, hlower⟩)
        exact atoms.root_sq_le_of_radius_lt_inv k hk j.1 hactive hsmall x
      _ = (hsupportFinite.toFinset.card : ℝ) *
          (C ^ 2 * (1 / (k : ℝ)) ^ 4) := by simp
      _ ≤ (B : ℝ) * (C ^ 2 * (1 / (k : ℝ)) ^ 4) := by
        apply mul_le_mul_of_nonneg_right
        · rw [Set.ncard_eq_toFinset_card tailSupport hsupportFinite] at hcard
          exact_mod_cast hcard
        · positivity
  · intro j hj
    have hjNotSupport : j ∉ tailSupport := by
      simpa using hj
    change ¬ atoms.root j.1 x ^ 2 ≠ 0 at hjNotSupport
    exact not_ne_iff.mp hjNotSupport

/-- Removing the atoms below resolution `1 / k` changes the square sum by `O(k⁻⁴)`. -/
theorem SphereAtomFamily.retained_sum_remainder_le {n : ℕ}
    {F : MvPolynomial (Fin n) ℝ} {C : ℝ} {B : ℕ}
    (atoms : SphereAtomFamily n F C B) (k : ℕ) (hk : 1 ≤ k)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    |MvPolynomial.eval x F -
        ∑ i ∈ atoms.retainedIndices k hk, atoms.root i x ^ 2| ≤
      (B : ℝ) * (C ^ 2 * (1 / (k : ℝ)) ^ 4) := by
  have hsummable : Summable (fun i ↦ atoms.root i x ^ 2) :=
    (atoms.square_identity x hx).summable
  have hsplit := hsummable.sum_add_tsum_subtype_compl (atoms.retainedIndices k hk)
  rw [(atoms.square_identity x hx).tsum_eq] at hsplit
  have hremainder : MvPolynomial.eval x F -
      ∑ i ∈ atoms.retainedIndices k hk, atoms.root i x ^ 2 =
        ∑' j : {i // i ∉ atoms.retainedIndices k hk}, atoms.root j.1 x ^ 2 := by
    linarith
  rw [hremainder, abs_of_nonneg]
  · exact atoms.retained_tail_tsum_le k hk x hx
  · exact tsum_nonneg fun _ ↦ sq_nonneg _

/-- Finite radii above `1 / k` admit a common finite range of dyadic labels. -/
structure FiniteDyadicScaleData {N : ℕ} (k : ℕ) (radius : Fin N → ℝ) where
  J : ℕ
  scale : Fin N → Fin J
  scale_lower : ∀ i, (2 : ℝ) ^ (scale i : ℕ) / (k : ℝ) ≤ radius i
  scale_upper : ∀ i, radius i < (2 : ℝ) ^ ((scale i : ℕ) + 1) / (k : ℝ)

/-- The Archimedean dyadic bracketing can be chosen uniformly over a finite family. -/
theorem finiteDyadicScaleData_exists {N k : ℕ} (hk : 1 ≤ k)
    (radius : Fin N → ℝ) (hradius_lower : ∀ i, 1 / (k : ℝ) ≤ radius i) :
    Nonempty (FiniteDyadicScaleData k radius) := by
  have hkreal : 0 < (k : ℝ) := by positivity
  have hbracket : ∀ i, ∃ j : ℕ,
      (2 : ℝ) ^ j / (k : ℝ) ≤ radius i ∧
        radius i < (2 : ℝ) ^ (j + 1) / (k : ℝ) := by
    intro i
    have hx : 1 ≤ (k : ℝ) * radius i := by
      calc
        1 = (k : ℝ) * (1 / (k : ℝ)) := by field_simp
        _ ≤ (k : ℝ) * radius i :=
          mul_le_mul_of_nonneg_left (hradius_lower i) hkreal.le
    obtain ⟨j, hjlower, hjupper⟩ :=
      exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
    refine ⟨j, (div_le_iff₀ hkreal).2 ?_, (lt_div_iff₀ hkreal).2 ?_⟩
    · simpa [mul_comm] using hjlower
    · simpa [mul_comm] using hjupper
  let label : Fin N → ℕ := fun i ↦ Classical.choose (hbracket i)
  have hlabel_spec : ∀ i,
      (2 : ℝ) ^ label i / (k : ℝ) ≤ radius i ∧
        radius i < (2 : ℝ) ^ (label i + 1) / (k : ℝ) := fun i ↦
    Classical.choose_spec (hbracket i)
  let J : ℕ := 1 + ∑ i : Fin N, label i
  have hlabel_lt : ∀ i, label i < J := by
    intro i
    have hle : label i ≤ ∑ j : Fin N, label j :=
      Finset.single_le_sum (fun j _ ↦ Nat.zero_le (label j)) (Finset.mem_univ i)
    dsimp [J]
    omega
  let scale : Fin N → Fin J := fun i ↦ ⟨label i, hlabel_lt i⟩
  exact ⟨{
    J := J
    scale := scale
    scale_lower := fun i ↦ (hlabel_spec i).1
    scale_upper := fun i ↦ (hlabel_spec i).2 }⟩

/-- The one-step normalized zonal-filter error, duplicated here to keep packing acyclic. -/
noncomputable def packingNormalizedZonalFilterError {n : ℕ}
    (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ) (x : sphereSet n) : ℝ :=
  normalizedFunctionZonalKernelValue p k base v x.1 - v x

/-- The axial-reflection symmetric increment used by the finite packing export. -/
def packingSphereSymmetricIncrement {n : ℕ} (v : sphereSet n → ℝ)
    (x y : sphereSet n) : ℝ :=
  v y + v (sphereAxialReflection x y) - 2 * v x

/-- The finite family obtained by discarding sphere atoms below resolution `1 / k`. -/
structure FiniteSphereAtomTruncation (n : ℕ) (A : ℝ) (k : ℕ)
    (F : MvPolynomial (Fin n) ℝ) where
  N : ℕ
  J : ℕ
  root : Fin N → ((Fin n → ℝ) → ℝ)
  base : sphereSet n
  center : Fin N → sphereSet n
  radius : Fin N → ℝ
  scale : Fin N → Fin J
  overlapBound : ℕ
  jetBound : ℝ
  jetBound_nonneg : 0 ≤ jetBound
  radius_pos : ∀ i, 0 < radius i
  radius_lower : ∀ i, 1 / (k : ℝ) ≤ radius i
  radius_upper : ∀ i, radius i ≤ 1
  supported : ∀ i x (hx : x ∈ sphereSet n), root i x ≠ 0 →
    (⟨x, hx⟩ : sphereSet n) ∈ sphereChordalCap (center i) (radius i)
  cap_overlap_card : ∀ x (_hx : x ∈ sphereSet n),
    (Finset.univ.filter fun i ↦ sphereChordalSq x (center i).1 ≤ radius i ^ 2).card ≤
      overlapBound
  remainder : ∀ x ∈ sphereSet n,
    |MvPolynomial.eval x F - ∑ i, root i x ^ 2| ≤ A / (4 * (k : ℝ) ^ 4)
  root_contDiff : ∀ i, ContDiff ℝ 4 (root i)
  scaled_jet : ∀ i j, j ≤ 4 → ∀ x,
    ‖iteratedFDeriv ℝ j (root i) x‖ * radius i ^ j ≤ jetBound * radius i ^ 2
  scale_lower : ∀ i, (2 : ℝ) ^ (scale i : ℕ) / (k : ℝ) ≤ radius i
  scale_upper : ∀ i, radius i < (2 : ℝ) ^ ((scale i : ℕ) + 1) / (k : ℝ)


/-- A finite dyadic shell labeling relative to one sphere point.  The two inequalities make the
shell index an actual bracket for the center distance measured in units of the atom radius. -/
structure FiniteSphereDistanceShellData {n : ℕ} {A : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin n) ℝ} (atoms : FiniteSphereAtomTruncation n A k F)
    (x : sphereSet n) where
  shellCount : ℕ
  shell : Fin atoms.N → Fin shellCount
  lower : ∀ i, ¬ sphereChordalSq x.1 (atoms.center i).1 ≤ atoms.radius i ^ 2 →
    (2 : ℝ) ^ (shell i : ℕ) * atoms.radius i ≤
      Real.sqrt (sphereChordalSq x.1 (atoms.center i).1)
  upper : ∀ i, ¬ sphereChordalSq x.1 (atoms.center i).1 ≤ atoms.radius i ^ 2 →
    Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) <
      (2 : ℝ) ^ ((shell i : ℕ) + 1) * atoms.radius i

/-- Every finite atom truncation admits finitely many dyadic distance shells around every sphere
point.  This is the Archimedean labeling stage preceding the uniform shell-cardinality bound. -/
theorem finiteSphereDistanceShellData_exists {n : ℕ} {A : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin n) ℝ} (atoms : FiniteSphereAtomTruncation n A k F)
    (x : sphereSet n) : Nonempty (FiniteSphereDistanceShellData atoms x) := by
  let d : Fin atoms.N → ℝ := fun i =>
    Real.sqrt (sphereChordalSq x.1 (atoms.center i).1)
  have hratio : ∀ i, ¬ sphereChordalSq x.1 (atoms.center i).1 ≤ atoms.radius i ^ 2 →
      1 ≤ d i / atoms.radius i := by
    intro i hfar
    have hr : 0 < atoms.radius i := atoms.radius_pos i
    have hsnonneg : 0 ≤ sphereChordalSq x.1 (atoms.center i).1 :=
      sphereChordalSq_nonneg _ _
    have hsqrt_sq : d i ^ 2 = sphereChordalSq x.1 (atoms.center i).1 := by
      exact Real.sq_sqrt hsnonneg
    have hdist : atoms.radius i < d i := by
      have hsq : atoms.radius i ^ 2 < sphereChordalSq x.1 (atoms.center i).1 :=
        lt_of_not_ge hfar
      have hd0 : 0 ≤ d i := Real.sqrt_nonneg _
      nlinarith
    exact (le_div_iff₀ hr).2 (by simpa using hdist.le)
  have hbracket : ∀ i (hfar :
      ¬ sphereChordalSq x.1 (atoms.center i).1 ≤ atoms.radius i ^ 2),
      ∃ q : ℕ,
        (2 : ℝ) ^ q * atoms.radius i ≤ d i ∧
          d i < (2 : ℝ) ^ (q + 1) * atoms.radius i := by
    intro i hfar
    have hr : 0 < atoms.radius i := atoms.radius_pos i
    obtain ⟨q, hqLower, hqUpper⟩ :=
      exists_nat_pow_near (hratio i hfar) (by norm_num : (1 : ℝ) < 2)
    refine ⟨q, ?_, ?_⟩
    · exact (le_div_iff₀ hr).mp (by simpa [d] using hqLower)
    · exact (div_lt_iff₀ hr).mp (by simpa [d] using hqUpper)
  let label : Fin atoms.N → ℕ := fun i =>
    if hfar : ¬ sphereChordalSq x.1 (atoms.center i).1 ≤ atoms.radius i ^ 2 then
      Classical.choose (hbracket i hfar)
    else 0
  have hlabel_spec : ∀ i (hfar :
      ¬ sphereChordalSq x.1 (atoms.center i).1 ≤ atoms.radius i ^ 2),
      (2 : ℝ) ^ label i * atoms.radius i ≤ d i ∧
        d i < (2 : ℝ) ^ (label i + 1) * atoms.radius i := by
    intro i hfar
    dsimp only [label]
    rw [dif_pos hfar]
    exact Classical.choose_spec (hbracket i hfar)
  let Q : ℕ := 1 + ∑ i : Fin atoms.N, label i
  have hlabel_lt : ∀ i, label i < Q := by
    intro i
    have hle : label i ≤ ∑ j : Fin atoms.N, label j :=
      Finset.single_le_sum (fun j _ ↦ Nat.zero_le (label j)) (Finset.mem_univ i)
    dsimp [Q]
    omega
  let shell : Fin atoms.N → Fin Q := fun i => ⟨label i, hlabel_lt i⟩
  exact ⟨{
    shellCount := Q
    shell := shell
    lower := fun i hi => by
      simpa [shell, d] using (hlabel_spec i hi).1
    upper := fun i hi => by
      simpa [shell, d] using (hlabel_spec i hi).2
  }⟩
/-- One finite dyadic distance-shell range valid simultaneously at every sphere point. -/
structure UniformFiniteSphereDistanceShellData {n : ℕ} {A : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin n) ℝ} (atoms : FiniteSphereAtomTruncation n A k F) where
  shellCount : ℕ
  shell : sphereSet n → Fin atoms.N → Fin shellCount
  lower : ∀ x i, ¬ sphereChordalSq x.1 (atoms.center i).1 ≤ atoms.radius i ^ 2 →
    (2 : ℝ) ^ (shell x i : ℕ) * atoms.radius i ≤
      Real.sqrt (sphereChordalSq x.1 (atoms.center i).1)
  upper : ∀ x i, ¬ sphereChordalSq x.1 (atoms.center i).1 ≤ atoms.radius i ^ 2 →
    Real.sqrt (sphereChordalSq x.1 (atoms.center i).1) <
      (2 : ℝ) ^ ((shell x i : ℕ) + 1) * atoms.radius i

/-- Retained radii are at least `1/k` and sphere chordal distance is at most two, so one power
of two above `2k` bounds every least dyadic distance label. -/
theorem uniformFiniteSphereDistanceShellData_exists {n : ℕ} {A : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin n) ℝ} (atoms : FiniteSphereAtomTruncation n A k F)
    (hk : 1 ≤ k) : Nonempty (UniformFiniteSphereDistanceShellData atoms) := by
  have hkreal : 0 < (k : ℝ) := by positivity
  have htwoK : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  obtain ⟨j, hjLower, hjUpper⟩ :=
    exists_nat_pow_near htwoK (by norm_num : (1 : ℝ) < 2)
  let Q : ℕ := j + 1
  have htwo_lt_powQ_div : (2 : ℝ) < 2 ^ Q / (k : ℝ) := by
    apply (lt_div_iff₀ hkreal).2
    simpa [Q, mul_comm] using hjUpper
  have htwo_lt_powQ_radius (i : Fin atoms.N) :
      (2 : ℝ) < 2 ^ Q * atoms.radius i := by
    calc
      (2 : ℝ) < 2 ^ Q / (k : ℝ) := htwo_lt_powQ_div
      _ = 2 ^ Q * (1 / (k : ℝ)) := by ring
      _ ≤ 2 ^ Q * atoms.radius i := by
        gcongr
        exact atoms.radius_lower i
  let d : sphereSet n → Fin atoms.N → ℝ := fun x i =>
    Real.sqrt (sphereChordalSq x.1 (atoms.center i).1)
  have hd_le_two (x : sphereSet n) (i : Fin atoms.N) : d x i ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num
      exact sphereChordalSq_le_four x.2 (atoms.center i).2
  let P : sphereSet n → Fin atoms.N → ℕ → Prop := fun x i q =>
    d x i < (2 : ℝ) ^ (q + 1) * atoms.radius i
  have hP_Q (x : sphereSet n) (i : Fin atoms.N) : P x i Q := by
    dsimp [P]
    calc
      d x i ≤ 2 := hd_le_two x i
      _ < 2 ^ Q * atoms.radius i := htwo_lt_powQ_radius i
      _ < 2 ^ (Q + 1) * atoms.radius i := by
        have hr : 0 < atoms.radius i := atoms.radius_pos i
        have hp : 0 < (2 : ℝ) ^ Q := pow_pos (by norm_num) Q
        calc
          2 ^ Q * atoms.radius i < (2 * 2 ^ Q) * atoms.radius i := by
            nlinarith
          _ = 2 ^ (Q + 1) * atoms.radius i := by
            rw [pow_succ]
            ring
  have hP_exists (x : sphereSet n) (i : Fin atoms.N) : ∃ q, P x i q :=
    ⟨Q, hP_Q x i⟩
  let labelNat : sphereSet n → Fin atoms.N → ℕ := fun x i => Nat.find (hP_exists x i)
  have hlabel_le (x : sphereSet n) (i : Fin atoms.N) : labelNat x i ≤ Q := by
    exact Nat.find_min' (hP_exists x i) (hP_Q x i)
  let shell : sphereSet n → Fin atoms.N → Fin (Q + 1) := fun x i =>
    ⟨labelNat x i, Nat.lt_succ_of_le (hlabel_le x i)⟩
  refine ⟨{
    shellCount := Q + 1
    shell := shell
    lower := ?_
    upper := ?_
  }⟩
  · intro x i hfar
    have hr : 0 < atoms.radius i := atoms.radius_pos i
    have hsnonneg : 0 ≤ sphereChordalSq x.1 (atoms.center i).1 :=
      sphereChordalSq_nonneg _ _
    have hsqrt_sq : d x i ^ 2 = sphereChordalSq x.1 (atoms.center i).1 := by
      exact Real.sq_sqrt hsnonneg
    have hdist : atoms.radius i ≤ d x i := by
      have hsq : atoms.radius i ^ 2 < sphereChordalSq x.1 (atoms.center i).1 :=
        lt_of_not_ge hfar
      have hd0 : 0 ≤ d x i := Real.sqrt_nonneg _
      nlinarith
    change (2 : ℝ) ^ labelNat x i * atoms.radius i ≤ d x i
    rcases hlabelEq : labelNat x i with _ | q
    · simpa using hdist
    · have hminimal : ¬ P x i q := by
        apply Nat.find_min (hP_exists x i)
        have hq : q < labelNat x i := by omega
        simpa [labelNat] using hq
      change (2 : ℝ) ^ (q + 1) * atoms.radius i ≤ d x i
      exact le_of_not_gt hminimal
  · intro x i hfar
    change d x i < (2 : ℝ) ^ (labelNat x i + 1) * atoms.radius i
    exact Nat.find_spec (hP_exists x i)


/-- The canonical globally bounded distance-shell labeling at a positive resolution. -/
noncomputable def canonicalUniformFiniteSphereDistanceShellData
    {n : ℕ} {A : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteSphereAtomTruncation n A k F) (hk : 1 ≤ k) :
    UniformFiniteSphereDistanceShellData atoms :=
  Classical.choice (uniformFiniteSphereDistanceShellData_exists atoms hk)

/-- Chordal square is symmetric. -/
theorem packing_sphereChordalSq_comm {n : ℕ} (x y : Fin n → ℝ) :
    sphereChordalSq x y = sphereChordalSq y x := by
  unfold sphereChordalSq
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The square root of chordal square obeys the triangle inequality.  This local copy keeps the
finite-packing layer independent of the later retained-root API. -/
theorem packing_sqrt_sphereChordalSq_triangle {n : ℕ} (x y z : sphereSet n) :
    Real.sqrt (sphereChordalSq x.1 z.1) ≤
      Real.sqrt (sphereChordalSq x.1 y.1) +
        Real.sqrt (sphereChordalSq y.1 z.1) := by
  have hdist (a b : sphereSet n) :
      Real.sqrt (sphereChordalSq a.1 b.1) =
        dist (sphereSetEuclideanCoordinates a) (sphereSetEuclideanCoordinates b) := by
    have hsq := sphereChordalSq_euclideanSphereCoordinates_eq_dist_sq
      (sphereSetEuclideanCoordinates a) (sphereSetEuclideanCoordinates b)
    change sphereChordalSq a.1 b.1 =
      dist (sphereSetEuclideanCoordinates a) (sphereSetEuclideanCoordinates b) ^ 2 at hsq
    rw [hsq, Real.sqrt_sq dist_nonneg]
  rw [hdist, hdist, hdist]
  exact dist_triangle _ _ _

/-- Sharp small-cap regularity and the probability bound give a power upper bound for chordal
caps of arbitrary nonnegative radius, with constants uniform in the center. -/
theorem exists_uniform_chordalCap_power_bounds_global {n : ℕ} (hn : 3 ≤ n) :
    ∃ c V : ℝ, 0 < c ∧ 0 ≤ V ∧
      (∀ (center : sphereSet n) (radius : ℝ), 0 ≤ radius → radius ≤ 1 →
        c * radius ^ (n - 1) ≤
          (normalizedSphereMeasure n).real (sphereChordalCap center radius)) ∧
      (∀ (center : sphereSet n) (radius : ℝ), 0 ≤ radius →
        (normalizedSphereMeasure n).real (sphereChordalCap center radius) ≤
          V * radius ^ (n - 1)) := by
  let ref := sphereReferencePoint n (dimension_pos_of_three_le hn)
  obtain ⟨c, C, hc, hC, hsmall⟩ :=
    normalizedSphereMeasure_chordalCap_small_power_bounds_at hn ref
  refine ⟨c, C + 1, hc, by positivity, ?_, ?_⟩
  · intro center radius hr0 hr1
    rw [normalizedSphereMeasureReal_sphereChordalCap_eq_on_sphere
      (by omega) radius center ref]
    exact (hsmall radius hr0 hr1).1
  · intro center radius hr0
    by_cases hr1 : radius ≤ 1
    · calc
        (normalizedSphereMeasure n).real (sphereChordalCap center radius) ≤
            C * radius ^ (n - 1) := by
          rw [normalizedSphereMeasureReal_sphereChordalCap_eq_on_sphere
            (by omega) radius center ref]
          exact (hsmall radius hr0 hr1).2
        _ ≤ (C + 1) * radius ^ (n - 1) := by
          apply mul_le_mul_of_nonneg_right (by linarith)
          positivity
    · letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
        normalizedSphereMeasure_isProbability n (by omega)
      have hrone : 1 ≤ radius := le_of_not_ge hr1
      calc
        (normalizedSphereMeasure n).real (sphereChordalCap center radius) ≤
            (normalizedSphereMeasure n).real Set.univ :=
          measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
        _ = 1 := by simp
        _ ≤ (C + 1) * radius ^ (n - 1) := by
          have hpow : 1 ≤ radius ^ (n - 1) := one_le_pow₀ hrone
          calc
            (1 : ℝ) = 1 * 1 := by ring
            _ ≤ (C + 1) * radius ^ (n - 1) :=
              mul_le_mul (by linarith) hpow zero_le_one (by linarith)

/-- A finite family of chordal caps with overlap at most B, all contained in one measurable
set, has total cap measure at most B times the measure of that set. -/
theorem FiniteSphereAtomTruncation.sum_cap_measure_le_overlap_mul_outer
    {n : ℕ} {A : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteSphereAtomTruncation n A k F) (hn : 0 < n)
    (s : Finset (Fin atoms.N)) (u : Set (sphereSet n)) (hu : MeasurableSet u)
    (hsub : ∀ i ∈ s, sphereChordalCap (atoms.center i) (atoms.radius i) ⊆ u) :
    ∑ i ∈ s, (normalizedSphereMeasure n).real
        (sphereChordalCap (atoms.center i) (atoms.radius i)) ≤
      (atoms.overlapBound : ℝ) * (normalizedSphereMeasure n).real u := by
  classical
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  have hcapIntegrable (i : Fin atoms.N) :
      Integrable ((sphereChordalCap (atoms.center i) (atoms.radius i)).indicator
        (fun _ : sphereSet n ↦ (1 : ℝ))) (normalizedSphereMeasure n) :=
    IntegrableOn.integrable_indicator integrableOn_const
      (measurableSet_sphereChordalCap _ _)
  have houterIntegrable :
      Integrable (u.indicator (fun _ : sphereSet n ↦ (atoms.overlapBound : ℝ)))
        (normalizedSphereMeasure n) :=
    IntegrableOn.integrable_indicator integrableOn_const hu
  have hpoint (z : sphereSet n) :
      ∑ i ∈ s, (sphereChordalCap (atoms.center i) (atoms.radius i)).indicator
          (fun _ : sphereSet n ↦ (1 : ℝ)) z ≤
        u.indicator (fun _ : sphereSet n ↦ (atoms.overlapBound : ℝ)) z := by
    by_cases hz : z ∈ u
    · have hfilter :
          s.filter (fun i ↦ z ∈ sphereChordalCap (atoms.center i) (atoms.radius i)) ⊆
            Finset.univ.filter (fun i ↦
              sphereChordalSq z.1 (atoms.center i).1 ≤ atoms.radius i ^ 2) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        simpa only [sphereChordalCap, Set.mem_setOf_eq] using hi.2
      have hcard :
          (s.filter (fun i ↦
            z ∈ sphereChordalCap (atoms.center i) (atoms.radius i))).card ≤
              atoms.overlapBound :=
        (Finset.card_le_card hfilter).trans (atoms.cap_overlap_card z.1 z.2)
      simpa only [Set.indicator_apply, hz, if_true, Finset.sum_boole] using
        (show ((s.filter (fun i ↦
          z ∈ sphereChordalCap (atoms.center i) (atoms.radius i))).card : ℝ) ≤
            (atoms.overlapBound : ℝ) by exact_mod_cast hcard)
    · rw [Set.indicator_of_notMem hz]
      have hsum :
          ∑ i ∈ s, (sphereChordalCap (atoms.center i) (atoms.radius i)).indicator
            (fun _ : sphereSet n ↦ (1 : ℝ)) z = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Set.indicator_of_notMem]
        exact fun hzi ↦ hz (hsub i hi hzi)
      rw [hsum]
  calc
    ∑ i ∈ s, (normalizedSphereMeasure n).real
        (sphereChordalCap (atoms.center i) (atoms.radius i)) =
        ∑ i ∈ s, ∫ z : sphereSet n,
          (sphereChordalCap (atoms.center i) (atoms.radius i)).indicator
            (fun _ : sphereSet n ↦ (1 : ℝ)) z ∂normalizedSphereMeasure n := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [Pi.one_apply] using
        (integral_indicator_one
          (μ := normalizedSphereMeasure n)
          (measurableSet_sphereChordalCap (atoms.center i) (atoms.radius i))).symm
    _ = ∫ z : sphereSet n,
        ∑ i ∈ s, (sphereChordalCap (atoms.center i) (atoms.radius i)).indicator
          (fun _ : sphereSet n ↦ (1 : ℝ)) z ∂normalizedSphereMeasure n := by
      rw [integral_finset_sum s (fun i _ ↦ hcapIntegrable i)]
    _ ≤ ∫ z : sphereSet n,
        u.indicator (fun _ : sphereSet n ↦ (atoms.overlapBound : ℝ)) z
          ∂normalizedSphereMeasure n :=
      integral_mono
        (integrable_finset_sum s (fun i _ ↦ hcapIntegrable i))
        houterIntegrable hpoint
    _ = (atoms.overlapBound : ℝ) * (normalizedSphereMeasure n).real u := by
      rw [integral_indicator_const _ hu, smul_eq_mul]
      ring

/-- Reindex the retained atoms, attach dyadic labels, and package the quartic tail estimate. -/
noncomputable def SphereAtomFamily.toFiniteTruncation {n : ℕ}
    {F : MvPolynomial (Fin n) ℝ} {C : ℝ} {B : ℕ}
    (hn : 0 < n) (hC : 0 ≤ C) (atoms : SphereAtomFamily n F C B)
    (k : ℕ) (hk : 1 ≤ k) :
    FiniteSphereAtomTruncation n (4 * (B : ℝ) * C ^ 2) k F := by
  let s := atoms.retainedIndices k hk
  let I := {i // i ∈ s}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let radius : Fin (Fintype.card I) → ℝ := fun i ↦ atoms.radius (e i).1
  have hradius_lower : ∀ i, 1 / (k : ℝ) ≤ radius i := by
    intro i
    exact (atoms.mem_retainedIndices k hk (e i).1).1 (e i).2 |>.2
  let scales := Classical.choice (finiteDyadicScaleData_exists hk radius hradius_lower)
  refine {
    N := Fintype.card I
    J := scales.J
    root := fun i ↦ atoms.root (e i).1
    base := sphereNorthPolePoint hn
    center := fun i ↦ atoms.center (e i).1
    radius := radius
    scale := scales.scale
    overlapBound := B
    jetBound := C
    jetBound_nonneg := hC
    radius_pos := ?_
    radius_lower := hradius_lower
    radius_upper := ?_
    supported := ?_
    cap_overlap_card := ?_
    remainder := ?_
    root_contDiff := ?_
    scaled_jet := ?_
    scale_lower := scales.scale_lower
    scale_upper := scales.scale_upper }
  · intro i
    have hi := (atoms.mem_retainedIndices k hk (e i).1).1 (e i).2
    exact atoms.radius_pos (e i).1 hi.1
  · intro i
    have hi := (atoms.mem_retainedIndices k hk (e i).1).1 (e i).2
    exact atoms.radius_le_one (e i).1 hi.1
  · intro i x hx hroot
    exact atoms.supported (e i).1 x hx hroot
  · intro x hx
    let u : Finset (Fin (Fintype.card I)) :=
      Finset.univ.filter fun i ↦
        sphereChordalSq x (atoms.center (e i).1).1 ≤ atoms.radius (e i).1 ^ 2
    have hinjective : Function.Injective (fun i : Fin (Fintype.card I) ↦ (e i).1) :=
      Subtype.val_injective.comp e.injective
    have himageSubset :
        (fun i : Fin (Fintype.card I) ↦ (e i).1) '' (u : Set (Fin (Fintype.card I))) ⊆
          {j | j ∈ atoms.active ∧
            sphereChordalSq x (atoms.center j).1 ≤ atoms.radius j ^ 2} := by
      rintro j ⟨i, hiu, rfl⟩
      have hiretained := (atoms.mem_retainedIndices k hk (e i).1).1 (e i).2
      have hcap :
          sphereChordalSq x (atoms.center (e i).1).1 ≤ atoms.radius (e i).1 ^ 2 := by
        simpa [u] using hiu
      exact ⟨hiretained.1, hcap⟩
    change u.card ≤ B
    calc
      u.card = (u : Set (Fin (Fintype.card I))).ncard :=
        (Set.ncard_coe_finset u).symm
      _ = ((fun i : Fin (Fintype.card I) ↦ (e i).1) ''
          (u : Set (Fin (Fintype.card I)))).ncard :=
        (Set.ncard_image_of_injective _ hinjective).symm
      _ ≤ Set.ncard {j | j ∈ atoms.active ∧
          sphereChordalSq x (atoms.center j).1 ≤ atoms.radius j ^ 2} :=
        Set.ncard_le_ncard himageSubset (atoms.finite_cap_indices x hx)
      _ ≤ B := atoms.cap_indices_ncard_le x hx
  · intro x hx
    have hsum :
        ∑ i : Fin (Fintype.card I), atoms.root (e i).1 x ^ 2 =
          ∑ i ∈ s, atoms.root i x ^ 2 := by
      calc
        ∑ i : Fin (Fintype.card I), atoms.root (e i).1 x ^ 2 =
            ∑ j : I, atoms.root j.1 x ^ 2 :=
          e.sum_comp (fun j : I ↦ atoms.root j.1 x ^ 2)
        _ = ∑ i ∈ s, atoms.root i x ^ 2 :=
          (Finset.sum_subtype s (fun i ↦ Iff.rfl) (fun i ↦ atoms.root i x ^ 2)).symm
    rw [hsum]
    calc
      |MvPolynomial.eval x F - ∑ i ∈ s, atoms.root i x ^ 2| ≤
          (B : ℝ) * (C ^ 2 * (1 / (k : ℝ)) ^ 4) :=
        atoms.retained_sum_remainder_le k hk x hx
      _ = (4 * (B : ℝ) * C ^ 2) / (4 * (k : ℝ) ^ 4) := by
        field_simp
  · intro i
    exact atoms.root_contDiff (e i).1
  · intro i j hj x
    exact atoms.scaled_jets (e i).1 j hj x

/-- Increasing the error constant preserves a finite atom truncation. -/
def FiniteSphereAtomTruncation.mono {n k : ℕ} {A C : ℝ}
    {F : MvPolynomial (Fin n) ℝ} (atoms : FiniteSphereAtomTruncation n A k F)
    (hAC : A ≤ C) (hk : 1 ≤ k) : FiniteSphereAtomTruncation n C k F := by
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  refine { atoms with remainder := ?_ }
  intro x hx
  exact (atoms.remainder x hx).trans
    (div_le_div_of_nonneg_right hAC (by positivity))
/-- The zero polynomial has an empty finite atom truncation at every positive resolution. -/
def zeroFiniteSphereAtomTruncation {n : ℕ} (hn : 0 < n) (A : ℝ) (hA : 0 ≤ A)
    (k : ℕ) : FiniteSphereAtomTruncation n A k 0 where
  N := 0
  J := 1
  root := Fin.elim0
  base := sphereNorthPolePoint hn
  center := Fin.elim0
  radius := Fin.elim0
  scale := Fin.elim0
  overlapBound := 0
  jetBound := 0
  jetBound_nonneg := le_rfl
  radius_pos := by
    intro i
    exact Fin.elim0 i
  radius_lower := by
    intro i
    exact Fin.elim0 i
  radius_upper := by
    intro i
    exact Fin.elim0 i
  supported := by
    intro i
    exact Fin.elim0 i
  cap_overlap_card := by simp
  remainder := by
    intro x hx
    simp only [map_zero, univ_eq_empty, sum_empty, sub_self, abs_zero]
    positivity
  root_contDiff := by
    intro i
    exact Fin.elim0 i
  scaled_jet := by
    intro i
    exact Fin.elim0 i
  scale_lower := by
    intro i
    exact Fin.elim0 i
  scale_upper := by
    intro i
    exact Fin.elim0 i


/-- Uniform finite truncation of the countable sphere atom family. -/
def HasUniformFiniteSphereAtomTruncation (n : ℕ) : Prop :=
  ∃ A J : ℝ, ∃ B : ℕ, 0 < A ∧ 0 ≤ J ∧ 0 < B ∧
    ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
      ∀ k, 1 ≤ k → Nonempty {atoms : FiniteSphereAtomTruncation n A k F //
        atoms.jetBound ≤ J ∧ atoms.overlapBound ≤ B}

/-- The genuinely analytic data that upgrades one finite truncation to the filter stage. -/
structure FiniteSphereAtomUpgrade {n : ℕ} {A : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin n) ℝ} (atoms : FiniteSphereAtomTruncation n A k F)
    (D : ℝ) where
  filter_increment_oscillation : ∀ (i : Fin atoms.N) (x y : sphereSet n),
    |packingNormalizedZonalFilterError (n + 3) k atoms.base
          (packingSphereSymmetricIncrement (fun z ↦ atoms.root i z.1) x) y -
        packingNormalizedZonalFilterError (n + 3) k atoms.base
          (packingSphereSymmetricIncrement (fun z ↦ atoms.root i z.1) x) x| ≤
      (2 * ((atoms.jetBound / atoms.radius i ^ 2) / (k : ℝ) ^ 2)) *
        sphereChordalSq y.1 x.1
  farShellCount : ℕ
  farShell : sphereSet n → Fin atoms.N → Fin farShellCount
  scale_far_shell_distance : ∀ x (hx : x ∈ sphereSet n),
      ∀ (j : Fin atoms.J) (q : Fin farShellCount) i,
    i ∈ (Finset.univ.filter (fun i ↦ atoms.scale i = j ∧
        ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
          (fun i ↦ farShell ⟨x, hx⟩ i = q) →
      (2 : ℝ) ^ (q : ℕ) * atoms.radius i ≤
        Real.sqrt (sphereChordalSq x (atoms.center i).1)
  scale_far_shell_card_budget : ∀ x (hx : x ∈ sphereSet n),
      ∀ (j : Fin atoms.J) (q : Fin farShellCount),
    (((Finset.univ.filter (fun i ↦ atoms.scale i = j ∧
        ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
          (fun i ↦ farShell ⟨x, hx⟩ i = q)).card : ℝ) *
        (1 + (2 : ℝ) ^ (q : ℕ))⁻¹ ^ (2 * (n + 3)) ≤
      D * (1 / 2 : ℝ) ^ (q : ℕ)


/-- The two genuinely quantitative estimates left after the dyadic shell labels themselves have
been constructed.  This separates Archimedean shell existence from packing and filter analysis. -/
structure FiniteSphereAtomUpgradeCore {n : ℕ} {A : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin n) ℝ} (atoms : FiniteSphereAtomTruncation n A k F)
    (hk : 1 ≤ k) (D : ℝ) where
  filter_increment_oscillation : ∀ (i : Fin atoms.N) (x y : sphereSet n),
    |packingNormalizedZonalFilterError (n + 3) k atoms.base
          (packingSphereSymmetricIncrement (fun z ↦ atoms.root i z.1) x) y -
        packingNormalizedZonalFilterError (n + 3) k atoms.base
          (packingSphereSymmetricIncrement (fun z ↦ atoms.root i z.1) x) x| ≤
      (2 * ((atoms.jetBound / atoms.radius i ^ 2) / (k : ℝ) ^ 2)) *
        sphereChordalSq y.1 x.1
  scale_far_shell_card_budget : ∀ x (hx : x ∈ sphereSet n),
      ∀ (j : Fin atoms.J)
        (q : Fin (canonicalUniformFiniteSphereDistanceShellData atoms hk).shellCount),
    (((Finset.univ.filter (fun i ↦ atoms.scale i = j ∧
        ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
          (fun i ↦
            (canonicalUniformFiniteSphereDistanceShellData atoms hk).shell ⟨x, hx⟩ i =
              q)).card : ℝ) *
        (1 + (2 : ℝ) ^ (q : ℕ))⁻¹ ^ (2 * (n + 3)) ≤
      D * (1 / 2 : ℝ) ^ (q : ℕ)

/-- Add the already constructed canonical shell labels to the quantitative upgrade core. -/
noncomputable def FiniteSphereAtomUpgradeCore.toUpgrade
    {n : ℕ} {A : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteSphereAtomTruncation n A k F} {hk : 1 ≤ k} {D : ℝ}
    (core : FiniteSphereAtomUpgradeCore atoms hk D) :
    FiniteSphereAtomUpgrade atoms D := by
  let shells := canonicalUniformFiniteSphereDistanceShellData atoms hk
  refine {
    filter_increment_oscillation := core.filter_increment_oscillation
    farShellCount := shells.shellCount
    farShell := shells.shell
    scale_far_shell_distance := ?_
    scale_far_shell_card_budget := ?_
  }
  · intro x hx j q i hi
    have hiOuter := (Finset.mem_filter.mp hi).1
    have hfar := (Finset.mem_filter.mp hiOuter).2.2
    have hq := (Finset.mem_filter.mp hi).2
    rw [← hq]
    exact shells.lower ⟨x, hx⟩ i hfar
  · exact core.scale_far_shell_card_budget

/-- Uniform existence of just the filter-oscillation and shell-cardinality estimates. -/
def HasUniformFiniteSphereAtomUpgradeCore (n : ℕ) : Prop :=
  ∃ A J D : ℝ, ∃ B : ℕ,
    0 < A ∧ 0 ≤ J ∧ 0 ≤ D ∧ 0 < B ∧
      ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
        ∀ k, ∀ hk : 1 ≤ k, ∃ atoms : FiniteSphereAtomTruncation n A k F,
          atoms.jetBound ≤ J ∧ atoms.overlapBound ≤ B ∧
            Nonempty (FiniteSphereAtomUpgradeCore atoms hk D)
/-- Uniform shell packing and filtered-increment regularity for finite truncations. -/
def HasUniformFiniteSphereAtomUpgrade (n : ℕ) : Prop :=
  ∃ A J D : ℝ, ∃ B : ℕ,
    0 < A ∧ 0 ≤ J ∧ 0 ≤ D ∧ 0 < B ∧
      ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
        ∀ k, 1 ≤ k → ∃ atoms : FiniteSphereAtomTruncation n A k F,
          atoms.jetBound ≤ J ∧ atoms.overlapBound ≤ B ∧
            Nonempty (FiniteSphereAtomUpgrade atoms D)

/-- Enlarging only the declared jet constant preserves a finite truncation. -/
def FiniteSphereAtomTruncation.enlargeJetBound
    {n : ℕ} {A : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteSphereAtomTruncation n A k F) (J : ℝ)
    (hJ : 0 ≤ J) (hmono : atoms.jetBound ≤ J) :
    FiniteSphereAtomTruncation n A k F where
  N := atoms.N
  J := atoms.J
  root := atoms.root
  base := atoms.base
  center := atoms.center
  radius := atoms.radius
  scale := atoms.scale
  overlapBound := atoms.overlapBound
  jetBound := J
  jetBound_nonneg := hJ
  radius_pos := atoms.radius_pos
  radius_lower := atoms.radius_lower
  radius_upper := atoms.radius_upper
  supported := atoms.supported
  cap_overlap_card := atoms.cap_overlap_card
  remainder := atoms.remainder
  root_contDiff := atoms.root_contDiff
  scaled_jet := by
    intro i j hj x
    exact (atoms.scaled_jet i j hj x).trans
      (mul_le_mul_of_nonneg_right hmono (sq_nonneg (atoms.radius i)))
  scale_lower := atoms.scale_lower
  scale_upper := atoms.scale_upper

/-- The scaled jet hypotheses imply a common ambient C4 bound at the inverse-square atom scale. -/
theorem FiniteSphereAtomTruncation.iteratedFDeriv_norm_le_jetBound_div_radius_sq
    {n : ℕ} {A : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (atoms : FiniteSphereAtomTruncation n A k F)
    (i : Fin atoms.N) (j : ℕ) (hj : j ≤ 4) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ j (atoms.root i) x‖ ≤
      atoms.jetBound / atoms.radius i ^ 2 := by
  have hrpos := atoms.radius_pos i
  have hrle := atoms.radius_upper i
  have hpow : atoms.radius i ^ 4 ≤ atoms.radius i ^ j :=
    pow_le_pow_of_le_one hrpos.le hrle hj
  have hscaled := atoms.scaled_jet i j hj x
  have hfour :
      ‖iteratedFDeriv ℝ j (atoms.root i) x‖ * atoms.radius i ^ 4 ≤
        atoms.jetBound * atoms.radius i ^ 2 := by
    exact (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans hscaled
  have hrsqpos : 0 < atoms.radius i ^ 2 := sq_pos_of_pos hrpos
  apply (le_div_iff₀ hrsqpos).2
  apply le_of_mul_le_mul_right _ hrsqpos
  calc
    (‖iteratedFDeriv ℝ j (atoms.root i) x‖ * atoms.radius i ^ 2) *
        atoms.radius i ^ 2 =
      ‖iteratedFDeriv ℝ j (atoms.root i) x‖ * atoms.radius i ^ 4 := by ring
    _ ≤ atoms.jetBound * atoms.radius i ^ 2 := hfour

/-- A continuous sphere function times a zonal-kernel section is integrable. -/
theorem packing_integrable_continuous_mul_sphereDirichletZonalKernel_section
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (v : sphereSet n → ℝ)
    (hv : Continuous v) (x : Fin n → ℝ) :
    Integrable (fun y : sphereSet n ↦ v y *
      MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x))
      (normalizedSphereMeasure n) := by
  letI : CompactSpace (sphereSet n) :=
    isCompact_iff_compactSpace.mp sphereSet_compact
  letI : IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n hn
  apply Continuous.integrable_of_hasCompactSupport
  · exact hv.mul (continuous_sphereDirichletZonalKernel_section p k x)
  · exact (isCompact_univ : IsCompact (Set.univ : Set (sphereSet n))).of_isClosed_subset
      (isClosed_tsupport _) (Set.subset_univ _)

/-- The normalized continuous zonal operator preserves addition on continuous inputs. -/
theorem packing_normalizedFunctionZonalKernelValue_add
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (u v : sphereSet n → ℝ) (hu : Continuous u) (hv : Continuous v)
    (x : Fin n → ℝ) :
    normalizedFunctionZonalKernelValue p k base (fun y ↦ u y + v y) x =
      normalizedFunctionZonalKernelValue p k base u x +
        normalizedFunctionZonalKernelValue p k base v x := by
  have huI := packing_integrable_continuous_mul_sphereDirichletZonalKernel_section
    hn p k u hu x
  have hvI := packing_integrable_continuous_mul_sphereDirichletZonalKernel_section
    hn p k v hv x
  have huI' : Integrable (fun y : sphereSet n ↦ u y *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1))
      (normalizedSphereMeasure n) := by
    convert huI using 1
    funext y
    rw [eval_sphereDirichletZonalKernel_comm]
  have hvI' : Integrable (fun y : sphereSet n ↦ v y *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1))
      (normalizedSphereMeasure n) := by
    convert hvI using 1
    funext y
    rw [eval_sphereDirichletZonalKernel_comm]
  unfold normalizedFunctionZonalKernelValue
  rw [show (fun y : sphereSet n ↦ (u y + v y) *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1)) =
      (fun y ↦ u y * MvPolynomial.eval x
        (sphereDirichletZonalKernel p k y.1) +
        v y * MvPolynomial.eval x
          (sphereDirichletZonalKernel p k y.1)) by
      funext y
      ring]
  rw [integral_add huI' hvI']
  ring

/-- The normalized continuous zonal operator preserves subtraction on continuous inputs. -/
theorem packing_normalizedFunctionZonalKernelValue_sub
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (u v : sphereSet n → ℝ) (hu : Continuous u) (hv : Continuous v)
    (x : Fin n → ℝ) :
    normalizedFunctionZonalKernelValue p k base (fun y ↦ u y - v y) x =
      normalizedFunctionZonalKernelValue p k base u x -
        normalizedFunctionZonalKernelValue p k base v x := by
  have huI := packing_integrable_continuous_mul_sphereDirichletZonalKernel_section
    hn p k u hu x
  have hvI := packing_integrable_continuous_mul_sphereDirichletZonalKernel_section
    hn p k v hv x
  have huI' : Integrable (fun y : sphereSet n ↦ u y *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1))
      (normalizedSphereMeasure n) := by
    convert huI using 1
    funext y
    rw [eval_sphereDirichletZonalKernel_comm]
  have hvI' : Integrable (fun y : sphereSet n ↦ v y *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1))
      (normalizedSphereMeasure n) := by
    convert hvI using 1
    funext y
    rw [eval_sphereDirichletZonalKernel_comm]
  unfold normalizedFunctionZonalKernelValue
  rw [show (fun y : sphereSet n ↦ (u y - v y) *
      MvPolynomial.eval x (sphereDirichletZonalKernel p k y.1)) =
      (fun y ↦ u y * MvPolynomial.eval x
        (sphereDirichletZonalKernel p k y.1) -
        v y * MvPolynomial.eval x
          (sphereDirichletZonalKernel p k y.1)) by
      funext y
      ring]
  rw [integral_sub huI' hvI']
  ring

/-- Center-independent normalization makes the continuous zonal operator reproduce constants. -/
theorem packing_normalizedFunctionZonalKernelValue_const
    {n : ℕ} (hn : 2 ≤ n) (p k : ℕ) (base x : sphereSet n) (c : ℝ) :
    normalizedFunctionZonalKernelValue p k base (fun _ ↦ c) x.1 = c := by
  have hmass := continuousZonalKernelMass_eq_on_sphere hn p k x base
  have hZpos := continuousZonalKernelMass_pos (by omega) p k base.1 base.2
  have horient :
      (∫ y : sphereSet n, c *
          MvPolynomial.eval x.1 (sphereDirichletZonalKernel p k y.1)
            ∂normalizedSphereMeasure n) =
        ∫ y : sphereSet n, c *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x.1)
            ∂normalizedSphereMeasure n := by
    apply integral_congr_ae
    filter_upwards with y
    rw [eval_sphereDirichletZonalKernel_comm]
  unfold normalizedFunctionZonalKernelValue
  rw [horient, integral_const_mul]
  change c * continuousZonalKernelMass p k x.1 /
      continuousZonalKernelMass p k base.1 = c
  rw [hmass]
  field_simp [hZpos.ne']

/-- The normalized continuous zonal operator is equivariant under axial reflection. -/
theorem packing_normalizedFunctionZonalKernelValue_sphereAxialReflection
    {n : ℕ} (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (a x : sphereSet n) :
    normalizedFunctionZonalKernelValue p k base v
        (sphereAxialReflection a x).1 =
      normalizedFunctionZonalKernelValue p k base
        (fun y ↦ v (sphereAxialReflection a y)) x.1 := by
  unfold normalizedFunctionZonalKernelValue
  congr 1
  calc
    (∫ y : sphereSet n, v y *
        MvPolynomial.eval (sphereAxialReflection a x).1
          (sphereDirichletZonalKernel p k y.1)
          ∂normalizedSphereMeasure n) =
      ∫ y : sphereSet n, v (sphereAxialReflection a y) *
        MvPolynomial.eval (sphereAxialReflection a x).1
          (sphereDirichletZonalKernel p k (sphereAxialReflection a y).1)
          ∂normalizedSphereMeasure n :=
      (integral_comp_sphereAxialReflection a _).symm
    _ = ∫ y : sphereSet n, v (sphereAxialReflection a y) *
        MvPolynomial.eval x.1 (sphereDirichletZonalKernel p k y.1)
          ∂normalizedSphereMeasure n := by
      apply integral_congr_ae
      filter_upwards with y
      rw [eval_sphereDirichletZonalKernel_map_sphereAxialReflection]

/-- The one-step filter error preserves addition. -/
theorem packingNormalizedZonalFilterError_add
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (u v : sphereSet n → ℝ) (hu : Continuous u) (hv : Continuous v)
    (x : sphereSet n) :
    packingNormalizedZonalFilterError p k base (fun y ↦ u y + v y) x =
      packingNormalizedZonalFilterError p k base u x +
        packingNormalizedZonalFilterError p k base v x := by
  unfold packingNormalizedZonalFilterError
  rw [packing_normalizedFunctionZonalKernelValue_add hn p k base u v hu hv x.1]
  ring

/-- The one-step filter error preserves subtraction. -/
theorem packingNormalizedZonalFilterError_sub
    {n : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (u v : sphereSet n → ℝ) (hu : Continuous u) (hv : Continuous v)
    (x : sphereSet n) :
    packingNormalizedZonalFilterError p k base (fun y ↦ u y - v y) x =
      packingNormalizedZonalFilterError p k base u x -
        packingNormalizedZonalFilterError p k base v x := by
  unfold packingNormalizedZonalFilterError
  rw [packing_normalizedFunctionZonalKernelValue_sub hn p k base u v hu hv x.1]
  ring

/-- The one-step filter error vanishes on constants. -/
theorem packingNormalizedZonalFilterError_const
    {n : ℕ} (hn : 2 ≤ n) (p k : ℕ) (base x : sphereSet n) (c : ℝ) :
    packingNormalizedZonalFilterError p k base (fun _ ↦ c) x = 0 := by
  unfold packingNormalizedZonalFilterError
  rw [packing_normalizedFunctionZonalKernelValue_const hn]
  ring

/-- The one-step filter error is equivariant under axial reflection. -/
theorem packingNormalizedZonalFilterError_sphereAxialReflection
    {n : ℕ} (p k : ℕ) (base : sphereSet n) (v : sphereSet n → ℝ)
    (a x : sphereSet n) :
    packingNormalizedZonalFilterError p k base v (sphereAxialReflection a x) =
      packingNormalizedZonalFilterError p k base
        (fun y ↦ v (sphereAxialReflection a y)) x := by
  unfold packingNormalizedZonalFilterError
  rw [packing_normalizedFunctionZonalKernelValue_sphereAxialReflection]

/-- Linearity, constant reproduction, and reflection equivariance identify the filtered symmetric
increment oscillation with the axial second difference of the original filter error. -/
theorem packing_filterError_symmetricIncrement_sub
    {n : ℕ} (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    (v : sphereSet n → ℝ) (hv : Continuous v) (x y : sphereSet n) :
    packingNormalizedZonalFilterError p k base
        (packingSphereSymmetricIncrement v x) y -
      packingNormalizedZonalFilterError p k base
        (packingSphereSymmetricIncrement v x) x =
      packingNormalizedZonalFilterError p k base v y +
        packingNormalizedZonalFilterError p k base v (sphereAxialReflection x y) -
          2 * packingNormalizedZonalFilterError p k base v x := by
  have hvR : Continuous (fun z : sphereSet n ↦ v (sphereAxialReflection x z)) :=
    hv.comp (continuous_sphereAxialReflection x)
  have hsum : Continuous (fun z : sphereSet n ↦
      v z + v (sphereAxialReflection x z)) := hv.add hvR
  have hconst : Continuous (fun _ : sphereSet n ↦ 2 * v x) := continuous_const
  have herror (z : sphereSet n) :
      packingNormalizedZonalFilterError p k base
          (packingSphereSymmetricIncrement v x) z =
        packingNormalizedZonalFilterError p k base v z +
          packingNormalizedZonalFilterError p k base
            (fun q ↦ v (sphereAxialReflection x q)) z := by
    unfold packingSphereSymmetricIncrement
    rw [packingNormalizedZonalFilterError_sub (by omega) p k base
      (fun q ↦ v q + v (sphereAxialReflection x q))
      (fun _ ↦ 2 * v x) hsum hconst z]
    rw [packingNormalizedZonalFilterError_add (by omega) p k base v
      (fun q ↦ v (sphereAxialReflection x q)) hv hvR z]
    rw [packingNormalizedZonalFilterError_const hn]
    ring
  rw [herror y, herror x]
  rw [← packingNormalizedZonalFilterError_sphereAxialReflection p k base v x y]
  rw [← packingNormalizedZonalFilterError_sphereAxialReflection p k base v x x]
  simp
  ring

/-- Reflection equivariance moves an axial second difference of the filter error to the
filter error of a centered pair of inverse-rotation pullbacks based at `x`. -/
theorem packingNormalizedZonalFilterError_centeredRotation
    {n : ℕ} (hn : 2 ≤ n) (p k : ℕ) (base : sphereSet n)
    (v : (Fin n → ℝ) → ℝ) (hv : Continuous v)
    (a x y : sphereSet n) (hmap : sphereAxialReflection a x = y) :
    packingNormalizedZonalFilterError p k base (fun z ↦ v z.1) y +
        packingNormalizedZonalFilterError p k base (fun z ↦ v z.1)
          (sphereAxialReflection x y) -
        2 * packingNormalizedZonalFilterError p k base (fun z ↦ v z.1) x =
      packingNormalizedZonalFilterError p k base
        (fun z ↦ centeredLinearPullback v (sphereForwardRotationCLM a x)
          (sphereReverseRotationCLM a x) z.1) x := by
  let vs : sphereSet n → ℝ := fun z ↦ v z.1
  let va : sphereSet n → ℝ := fun z ↦ vs (sphereAxialReflection a z)
  let vx : sphereSet n → ℝ := fun z ↦ vs (sphereAxialReflection x z)
  let vforward : sphereSet n → ℝ := fun z ↦ va (sphereAxialReflection x z)
  let vreverse : sphereSet n → ℝ := fun z ↦ vx (sphereAxialReflection a z)
  have hvs : Continuous vs := hv.comp continuous_subtype_val
  have hva : Continuous va := hvs.comp (continuous_sphereAxialReflection a)
  have hvx : Continuous vx := hvs.comp (continuous_sphereAxialReflection x)
  have hvforward : Continuous vforward :=
    hva.comp (continuous_sphereAxialReflection x)
  have hvreverse : Continuous vreverse :=
    hvx.comp (continuous_sphereAxialReflection a)
  have hforward (z : sphereSet n) :
      vforward z = v (sphereForwardRotationCLM a x z.1) := by
    simp [vforward, va, vs, sphereForwardRotationCLM,
      sphereAxialReflection_coe]
  have hreverse (z : sphereSet n) :
      vreverse z = v (sphereReverseRotationCLM a x z.1) := by
    simp [vreverse, vx, vs, sphereReverseRotationCLM,
      sphereAxialReflection_coe]
  have hEy : packingNormalizedZonalFilterError p k base vs y =
      packingNormalizedZonalFilterError p k base vforward x := by
    calc
      packingNormalizedZonalFilterError p k base vs y =
          packingNormalizedZonalFilterError p k base vs
            (sphereAxialReflection a x) := by rw [hmap]
      _ = packingNormalizedZonalFilterError p k base va x := by
        exact packingNormalizedZonalFilterError_sphereAxialReflection p k base vs a x
      _ = packingNormalizedZonalFilterError p k base va
          (sphereAxialReflection x x) := by simp
      _ = packingNormalizedZonalFilterError p k base vforward x := by
        exact packingNormalizedZonalFilterError_sphereAxialReflection p k base va x x
  have hEr : packingNormalizedZonalFilterError p k base vs
      (sphereAxialReflection x y) =
      packingNormalizedZonalFilterError p k base vreverse x := by
    calc
      packingNormalizedZonalFilterError p k base vs
          (sphereAxialReflection x y) =
        packingNormalizedZonalFilterError p k base vx y := by
          exact packingNormalizedZonalFilterError_sphereAxialReflection p k base vs x y
      _ = packingNormalizedZonalFilterError p k base vx
          (sphereAxialReflection a x) := by rw [hmap]
      _ = packingNormalizedZonalFilterError p k base vreverse x := by
        exact packingNormalizedZonalFilterError_sphereAxialReflection p k base vx a x
  have hsum := packingNormalizedZonalFilterError_add (by omega) p k base
    vforward vreverse hvforward hvreverse x
  have hdouble := packingNormalizedZonalFilterError_add (by omega) p k base
    vs vs hvs hvs x
  have hsub := packingNormalizedZonalFilterError_sub (by omega) p k base
    (fun z ↦ vforward z + vreverse z) (fun z ↦ vs z + vs z)
    (hvforward.add hvreverse) (hvs.add hvs) x
  rw [hEy, hEr]
  calc
    packingNormalizedZonalFilterError p k base vforward x +
          packingNormalizedZonalFilterError p k base vreverse x -
        2 * packingNormalizedZonalFilterError p k base vs x =
      packingNormalizedZonalFilterError p k base
          (fun z ↦ vforward z + vreverse z) x -
        packingNormalizedZonalFilterError p k base
          (fun z ↦ vs z + vs z) x := by rw [hsum, hdouble]; ring
    _ = packingNormalizedZonalFilterError p k base
        (fun z ↦ vforward z + vreverse z - (vs z + vs z)) x := hsub.symm
    _ = packingNormalizedZonalFilterError p k base
        (fun z ↦ centeredLinearPullback v (sphereForwardRotationCLM a x)
          (sphereReverseRotationCLM a x) z.1) x := by
      congr 1
      funext z
      rw [hforward, hreverse]
      dsimp [centeredLinearPullback, vs]
      ring


/-- The normalized zonal-filter error of an ambient C4 function has axial second differences
bounded by its C4 jet norm times `k⁻²`. The proof uses centered inverse rotations, unit-ball
Taylor cancellation, and the normalized kernel second-moment bound. -/
theorem exists_normalizedFilterError_axial_secondDifference_c4
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (base : sphereSet n)
        (v : (Fin n → ℝ) → ℝ) (M : ℝ), 0 ≤ M → ContDiff ℝ 4 v →
        (∀ j, j ≤ 4 → ∀ z, ‖iteratedFDeriv ℝ j v z‖ ≤ M) →
        ∀ x y : sphereSet n,
          |packingNormalizedZonalFilterError (n + 3) k base (fun z ↦ v z.1) y +
              packingNormalizedZonalFilterError (n + 3) k base (fun z ↦ v z.1)
                (sphereAxialReflection x y) -
              2 * packingNormalizedZonalFilterError (n + 3) k base
                (fun z ↦ v z.1) x| ≤
            (2 * ((K * M) / (k : ℝ) ^ 2)) * sphereChordalSq y.1 x.1 := by
  obtain ⟨Ckernel, hCkernel, hfilter⟩ :=
    packingContinuous_exists_fixedPower_filterError_bound hn
  let J := 6 * sphereRotationJetConstant n ^ 3
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans
      (sphereRotationJetConstant_one_le n)) 3)
  let K := max 1 (J * Ckernel)
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨K, hK, ?_⟩
  intro k hk base v M hM hv hjet x y
  obtain ⟨a, hmap, hg, hgjets⟩ :=
    exists_centeredRotationPullback_c2_jet_bound (by omega) v M hM hv hjet x y
  let g := centeredLinearPullback v (sphereForwardRotationCLM a x)
    (sphereReverseRotationCLM a x)
  let Mg := J * M * sphereChordalSq y.1 x.1
  have hMg : 0 ≤ Mg := by
    dsimp [Mg]
    exact mul_nonneg (mul_nonneg hJ hM) (sphereChordalSq_nonneg _ _)
  have hg' : ContDiff ℝ 2 g := by simpa [g] using hg
  have hgOne : ∀ z, ‖z‖ ≤ 1 → ‖fderiv ℝ g z‖ ≤ Mg := by
    intro z hz
    rw [← norm_iteratedFDeriv_one]
    simpa [g, Mg, J] using hgjets 1 (by norm_num) z hz
  have hgTwo : ∀ z, ‖z‖ ≤ 1 → ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ Mg := by
    intro z hz
    calc
      ‖fderiv ℝ (fderiv ℝ g) z‖ =
          ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) z‖ := by
        symm
        exact norm_iteratedFDeriv_one (fderiv ℝ g)
      _ = ‖iteratedFDeriv ℝ 2 g z‖ := norm_iteratedFDeriv_fderiv
      _ ≤ Mg := by simpa [g, Mg, J] using hgjets 2 (by norm_num) z hz
  have hsymmetric : ∀ q : sphereSet n,
      |g q.1 + g (sphereAxialReflection x q).1 - 2 * g x.1| ≤
        (2 * (2 * Mg)) * sphereChordalSq q.1 x.1 := by
    intro q
    convert abs_ambient_sphereAxial_secondDifference_le hMg hg' hgOne hgTwo x q using 1;
      ring
  have hgContinuous : Continuous (fun q : sphereSet n ↦ g q.1) :=
    hg'.continuous.comp continuous_subtype_val
  have herr := hfilter k hk base (fun q : sphereSet n ↦ g q.1)
    hgContinuous x (2 * Mg) (mul_nonneg (by norm_num) hMg) hsymmetric
  rw [packingNormalizedZonalFilterError_centeredRotation (by omega)
    (n + 3) k base v hv.continuous a x y hmap]
  change |packingContinuousZonalFilterError (n + 3) k base
    (fun q : sphereSet n ↦ g q.1) x| ≤ _
  apply herr.trans
  have hKC : J * Ckernel ≤ K := le_max_right _ _
  have hkpos : 0 < (k : ℝ) ^ 2 := by positivity
  have hkinv : 0 ≤ ((k : ℝ) ^ 2)⁻¹ := inv_nonneg.mpr hkpos.le
  have hchord : 0 ≤ sphereChordalSq y.1 x.1 := sphereChordalSq_nonneg _ _
  dsimp [Mg]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (2 * (J * M * sphereChordalSq y.1 x.1)) *
        (Ckernel * ((k : ℝ) ^ 2)⁻¹) =
      2 * (J * Ckernel) * M * ((k : ℝ) ^ 2)⁻¹ *
        sphereChordalSq y.1 x.1 := by ring
    _ ≤ 2 * K * M * ((k : ℝ) ^ 2)⁻¹ * sphereChordalSq y.1 x.1 := by
      gcongr
    _ = (2 * (K * M * ((k : ℝ) ^ 2)⁻¹)) *
        sphereChordalSq y.1 x.1 := by ring

/-- The derivative-commutation estimate implies the exact symmetric-increment oscillation used
by the finite-packing stage. -/
theorem exists_normalizedFilter_symmetricIncrement_oscillation_c4
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (base : sphereSet n)
        (v : (Fin n → ℝ) → ℝ) (M : ℝ), 0 ≤ M → ContDiff ℝ 4 v →
        (∀ j, j ≤ 4 → ∀ z, ‖iteratedFDeriv ℝ j v z‖ ≤ M) →
        ∀ x y : sphereSet n,
          |packingNormalizedZonalFilterError (n + 3) k base
              (packingSphereSymmetricIncrement (fun z ↦ v z.1) x) y -
            packingNormalizedZonalFilterError (n + 3) k base
              (packingSphereSymmetricIncrement (fun z ↦ v z.1) x) x| ≤
            (2 * ((K * M) / (k : ℝ) ^ 2)) * sphereChordalSq y.1 x.1 := by
  obtain ⟨K, hK, hsecond⟩ :=
    exists_normalizedFilterError_axial_secondDifference_c4 hn
  refine ⟨K, hK, ?_⟩
  intro k hk base v M hM hv hjet x y
  rw [packing_filterError_symmetricIncrement_sub (by omega) (n + 3) k base
    (fun z ↦ v z.1) (hv.continuous.comp continuous_subtype_val) x y]
  exact hsecond k hk base v M hM hv hjet x y

/-- The cap-overlap bound and sharp cap volumes give a shell-cardinality budget uniform over
all finite truncations whose overlap constant is bounded by B. -/
theorem exists_uniform_scale_far_shell_card_budget {n : ℕ} (hn : 3 ≤ n) (B : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ {A : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
        (atoms : FiniteSphereAtomTruncation n A k F) (hk : 1 ≤ k),
        atoms.overlapBound ≤ B →
        ∀ x (hx : x ∈ sphereSet n), ∀ (j : Fin atoms.J)
          (q : Fin (canonicalUniformFiniteSphereDistanceShellData atoms hk).shellCount),
        (((Finset.univ.filter (fun i ↦ atoms.scale i = j ∧
            ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
              (fun i ↦
                (canonicalUniformFiniteSphereDistanceShellData atoms hk).shell
                  ⟨x, hx⟩ i = q)).card : ℝ) *
            (1 + (2 : ℝ) ^ (q : ℕ))⁻¹ ^ (2 * (n + 3)) ≤
          D * (1 / 2 : ℝ) ^ (q : ℕ) := by
  classical
  obtain ⟨c, V, hc, hV, hcapLower, hcapUpper⟩ :=
    exists_uniform_chordalCap_power_bounds_global hn
  let D : ℝ := (B : ℝ) * V * c⁻¹ * 8 ^ (n - 1)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro A k F atoms hk hoverlap x hx j q
  let shells := canonicalUniformFiniteSphereDistanceShellData atoms hk
  let s : Finset (Fin atoms.N) :=
    (Finset.univ.filter (fun i ↦ atoms.scale i = j ∧
      ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2)).filter
        (fun i ↦ shells.shell ⟨x, hx⟩ i = q)
  let t : ℝ := (2 : ℝ) ^ (q : ℕ)
  let r₀ : ℝ := (2 : ℝ) ^ (j : ℕ) / (k : ℝ)
  let R : ℝ := 8 * t * r₀
  have hkreal : 0 < (k : ℝ) := by positivity
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have htone : 1 ≤ t := by
    dsimp [t]
    exact one_le_pow₀ (by norm_num)
  have hr₀pos : 0 < r₀ := by
    dsimp [r₀]
    positivity
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hiData (i : Fin atoms.N) (hi : i ∈ s) :
      atoms.scale i = j ∧
        ¬ sphereChordalSq x (atoms.center i).1 ≤ atoms.radius i ^ 2 ∧
          shells.shell ⟨x, hx⟩ i = q := by
    dsimp only [s] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨hi.1.1, hi.1.2, hi.2⟩
  have hr₀le (i : Fin atoms.N) (hi : i ∈ s) : r₀ ≤ atoms.radius i := by
    have h := atoms.scale_lower i
    rw [(hiData i hi).1] at h
    simpa only [r₀] using h
  have hri_lt_two_r₀ (i : Fin atoms.N) (hi : i ∈ s) :
      atoms.radius i < 2 * r₀ := by
    have h := atoms.scale_upper i
    rw [(hiData i hi).1] at h
    calc
      atoms.radius i < (2 : ℝ) ^ ((j : ℕ) + 1) / (k : ℝ) := h
      _ = 2 * r₀ := by
        dsimp [r₀]
        rw [pow_succ]
        ring
  have hcenterDistance (i : Fin atoms.N) (hi : i ∈ s) :
      Real.sqrt (sphereChordalSq x (atoms.center i).1) <
        2 * t * atoms.radius i := by
    have h := shells.upper ⟨x, hx⟩ i (hiData i hi).2.1
    rw [(hiData i hi).2.2] at h
    calc
      Real.sqrt (sphereChordalSq x (atoms.center i).1) <
          (2 : ℝ) ^ ((q : ℕ) + 1) * atoms.radius i := h
      _ = 2 * t * atoms.radius i := by
        dsimp [t]
        rw [pow_succ]
        ring
  have hcapSubset (i : Fin atoms.N) (hi : i ∈ s) :
      sphereChordalCap (atoms.center i) (atoms.radius i) ⊆
        sphereChordalCap ⟨x, hx⟩ R := by
    intro z hz
    have hzsq :
        sphereChordalSq z.1 (atoms.center i).1 ≤ atoms.radius i ^ 2 := by
      simpa only [sphereChordalCap, Set.mem_setOf_eq] using hz
    have hzroot :
        Real.sqrt (sphereChordalSq (atoms.center i).1 z.1) ≤ atoms.radius i := by
      rw [Real.sqrt_le_iff]
      refine ⟨(atoms.radius_pos i).le, ?_⟩
      rwa [packing_sphereChordalSq_comm]
    have hdist : Real.sqrt (sphereChordalSq x z.1) < R := by
      calc
        Real.sqrt (sphereChordalSq x z.1) ≤
            Real.sqrt (sphereChordalSq x (atoms.center i).1) +
              Real.sqrt (sphereChordalSq (atoms.center i).1 z.1) :=
          packing_sqrt_sphereChordalSq_triangle ⟨x, hx⟩ (atoms.center i) z
        _ < 2 * t * atoms.radius i + atoms.radius i :=
          add_lt_add_of_lt_of_le (hcenterDistance i hi) hzroot
        _ = (2 * t + 1) * atoms.radius i := by ring
        _ < (2 * t + 1) * (2 * r₀) := by
          exact mul_lt_mul_of_pos_left (hri_lt_two_r₀ i hi) (by nlinarith)
        _ ≤ R := by
          dsimp [R]
          nlinarith
    change sphereChordalSq z.1 x ≤ R ^ 2
    calc
      sphereChordalSq z.1 x =
          Real.sqrt (sphereChordalSq z.1 x) ^ 2 :=
        (Real.sq_sqrt (sphereChordalSq_nonneg _ _)).symm
      _ ≤ R ^ 2 := by
        apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
        rw [packing_sphereChordalSq_comm]
        exact hdist.le
  have hlowerSum :
      (s.card : ℝ) * (c * r₀ ^ (n - 1)) ≤
        ∑ i ∈ s, (normalizedSphereMeasure n).real
          (sphereChordalCap (atoms.center i) (atoms.radius i)) := by
    calc
      (s.card : ℝ) * (c * r₀ ^ (n - 1)) =
          ∑ _i ∈ s, c * r₀ ^ (n - 1) := by simp
      _ ≤ ∑ i ∈ s, (normalizedSphereMeasure n).real
          (sphereChordalCap (atoms.center i) (atoms.radius i)) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          c * r₀ ^ (n - 1) ≤ c * atoms.radius i ^ (n - 1) := by
            gcongr
            exact hr₀le i hi
          _ ≤ (normalizedSphereMeasure n).real
              (sphereChordalCap (atoms.center i) (atoms.radius i)) :=
            hcapLower (atoms.center i) (atoms.radius i) (atoms.radius_pos i).le
              (atoms.radius_upper i)
  have hupperSum :
      ∑ i ∈ s, (normalizedSphereMeasure n).real
          (sphereChordalCap (atoms.center i) (atoms.radius i)) ≤
        (B : ℝ) * (V * R ^ (n - 1)) := by
    calc
      ∑ i ∈ s, (normalizedSphereMeasure n).real
          (sphereChordalCap (atoms.center i) (atoms.radius i)) ≤
          (atoms.overlapBound : ℝ) *
            (normalizedSphereMeasure n).real (sphereChordalCap ⟨x, hx⟩ R) :=
        atoms.sum_cap_measure_le_overlap_mul_outer (by omega) s
          (sphereChordalCap ⟨x, hx⟩ R)
          (measurableSet_sphereChordalCap _ _) hcapSubset
      _ ≤ (B : ℝ) *
          (normalizedSphereMeasure n).real (sphereChordalCap ⟨x, hx⟩ R) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hoverlap
        · exact measureReal_nonneg
      _ ≤ (B : ℝ) * (V * R ^ (n - 1)) := by
        apply mul_le_mul_of_nonneg_left
        · exact hcapUpper ⟨x, hx⟩ R hRnonneg
        · positivity
  have hmass :
      (s.card : ℝ) * (c * r₀ ^ (n - 1)) ≤
        (B : ℝ) * (V * R ^ (n - 1)) :=
    hlowerSum.trans hupperSum
  have hRpow :
      R ^ (n - 1) = 8 ^ (n - 1) * t ^ (n - 1) * r₀ ^ (n - 1) := by
    dsimp [R]
    rw [mul_pow, mul_pow]
  have hr₀powpos : 0 < r₀ ^ (n - 1) := pow_pos hr₀pos _
  have hcancel :
      (s.card : ℝ) * c ≤
        (B : ℝ) * V * 8 ^ (n - 1) * t ^ (n - 1) := by
    apply le_of_mul_le_mul_right _ hr₀powpos
    calc
      ((s.card : ℝ) * c) * r₀ ^ (n - 1) =
          (s.card : ℝ) * (c * r₀ ^ (n - 1)) := by ring
      _ ≤ (B : ℝ) * (V * R ^ (n - 1)) := hmass
      _ = ((B : ℝ) * V * 8 ^ (n - 1) * t ^ (n - 1)) *
          r₀ ^ (n - 1) := by rw [hRpow]; ring
  have hcard : (s.card : ℝ) ≤ D * t ^ (n - 1) := by
    calc
      (s.card : ℝ) = ((s.card : ℝ) * c) * c⁻¹ := by
        field_simp
      _ ≤ ((B : ℝ) * V * 8 ^ (n - 1) * t ^ (n - 1)) * c⁻¹ :=
        mul_le_mul_of_nonneg_right hcancel (inv_nonneg.mpr hc.le)
      _ = D * t ^ (n - 1) := by
        dsimp [D]
        ring
  have hdenpow : t ^ n ≤ (1 + t) ^ (2 * (n + 3)) := by
    calc
      t ^ n ≤ (1 + t) ^ n :=
        pow_le_pow_left₀ htpos.le (by linarith) n
      _ ≤ (1 + t) ^ (2 * (n + 3)) :=
        pow_le_pow_right₀ (by linarith) (by omega)
  have hweight :
      t ^ (n - 1) * (1 + t)⁻¹ ^ (2 * (n + 3)) ≤ t⁻¹ := by
    rw [inv_pow]
    calc
      t ^ (n - 1) * ((1 + t) ^ (2 * (n + 3)))⁻¹ =
          t ^ (n - 1) / (1 + t) ^ (2 * (n + 3)) := by
            rw [div_eq_mul_inv]
      _ ≤ t ^ (n - 1) / t ^ n :=
        div_le_div_of_nonneg_left (pow_nonneg htpos.le _) (pow_pos htpos _)
          hdenpow
      _ = t⁻¹ := by
        rw [show n = (n - 1) + 1 by omega, pow_succ]
        field_simp
        congr 1
  change (s.card : ℝ) * (1 + t)⁻¹ ^ (2 * (n + 3)) ≤
    D * (1 / 2 : ℝ) ^ (q : ℕ)
  calc
    (s.card : ℝ) * (1 + t)⁻¹ ^ (2 * (n + 3)) ≤
        (D * t ^ (n - 1)) * (1 + t)⁻¹ ^ (2 * (n + 3)) :=
      mul_le_mul_of_nonneg_right hcard
        (pow_nonneg (inv_nonneg.mpr (by linarith)) _)
    _ = D * (t ^ (n - 1) * (1 + t)⁻¹ ^ (2 * (n + 3))) := by ring
    _ ≤ D * t⁻¹ := mul_le_mul_of_nonneg_left hweight hD
    _ = D * (1 / 2 : ℝ) ^ (q : ℕ) := by
      congr 1
      dsimp [t]
      rw [← inv_pow]
      norm_num

/-- The normalized filter-increment estimate and the canonical dyadic shell-cardinality budget
assemble the complete finite-packing upgrade. -/
theorem finiteSphereAtomUpgradeCore_of_truncation {n : ℕ} (hn : 3 ≤ n)
    (htrunc : HasUniformFiniteSphereAtomTruncation n) :
    HasUniformFiniteSphereAtomUpgradeCore n := by
  classical
  obtain ⟨A, J, B, hA, hJ, hB, hfamilies⟩ := htrunc
  obtain ⟨K, hK, hfilter⟩ :=
    exists_normalizedFilter_symmetricIncrement_oscillation_c4 hn
  obtain ⟨D, hD, hshell⟩ := exists_uniform_scale_far_shell_card_budget hn B
  have hKnonneg : 0 ≤ K := zero_le_one.trans hK
  refine ⟨A, K * J, D, B, hA, mul_nonneg hKnonneg hJ, hD, hB, ?_⟩
  intro F hF hnorm k hk
  let chosen := Classical.choice (hfamilies F hF hnorm k hk)
  let raw : FiniteSphereAtomTruncation n A k F := chosen.1
  have hrawJet : raw.jetBound ≤ J := chosen.2.1
  have hrawOverlap : raw.overlapBound ≤ B := chosen.2.2
  have hnewJetNonneg : 0 ≤ K * raw.jetBound :=
    mul_nonneg hKnonneg raw.jetBound_nonneg
  have hrawJetMono : raw.jetBound ≤ K * raw.jetBound := by
    nlinarith [raw.jetBound_nonneg]
  let atoms := raw.enlargeJetBound (K * raw.jetBound) hnewJetNonneg hrawJetMono
  have hatomsJet : atoms.jetBound ≤ K * J := by
    change K * raw.jetBound ≤ K * J
    exact mul_le_mul_of_nonneg_left hrawJet hKnonneg
  have hatomsOverlap : atoms.overlapBound ≤ B := by
    exact hrawOverlap
  refine ⟨atoms, hatomsJet, hatomsOverlap, ⟨{
    filter_increment_oscillation := ?_
    scale_far_shell_card_budget := ?_
  }⟩⟩
  · intro i x y
    have hM : 0 ≤ raw.jetBound / raw.radius i ^ 2 :=
      div_nonneg raw.jetBound_nonneg (sq_nonneg _)
    have h := hfilter k hk raw.base (raw.root i)
      (raw.jetBound / raw.radius i ^ 2) hM (raw.root_contDiff i)
      (fun j hj z ↦ raw.iteratedFDeriv_norm_le_jetBound_div_radius_sq i j hj z) x y
    change
      |packingNormalizedZonalFilterError (n + 3) k raw.base
          (packingSphereSymmetricIncrement (fun z ↦ raw.root i z.1) x) y -
        packingNormalizedZonalFilterError (n + 3) k raw.base
          (packingSphereSymmetricIncrement (fun z ↦ raw.root i z.1) x) x| ≤
        (2 * (((K * raw.jetBound) / raw.radius i ^ 2) / (k : ℝ) ^ 2)) *
          sphereChordalSq y.1 x.1
    convert h using 1
    all_goals ring
  · exact hshell atoms hk hatomsOverlap

/-- Canonical shell construction turns the quantitative core into the original upgrade payload. -/
theorem finiteSphereAtomUpgrade_of_truncation {n : ℕ} (hn : 3 ≤ n)
    (htrunc : HasUniformFiniteSphereAtomTruncation n) :
    HasUniformFiniteSphereAtomUpgrade n := by
  obtain ⟨A, J, D, B, hA, hJ, hD, hB, hfamilies⟩ :=
    finiteSphereAtomUpgradeCore_of_truncation hn htrunc
  refine ⟨A, J, D, B, hA, hJ, hD, hB, ?_⟩
  intro F hF hnorm k hk
  obtain ⟨atoms, hjet, hoverlap, hcore⟩ := hfamilies F hF hnorm k hk
  exact ⟨atoms, hjet, hoverlap,
    ⟨(Classical.choice hcore).toUpgrade⟩⟩

/-- The complete finite atom-side payload consumed by `FiniteAtomFilter`. -/
structure FiniteSphereAtomPackage (n : ℕ) (E C : ℝ) (k : ℕ)
    (F : MvPolynomial (Fin n) ℝ) extends FiniteSphereAtomTruncation n C k F where
  filter_increment_oscillation : ∀ (i : Fin N) (x y : sphereSet n),
    |packingNormalizedZonalFilterError (n + 3) k base
          (packingSphereSymmetricIncrement (fun z ↦ root i z.1) x) y -
        packingNormalizedZonalFilterError (n + 3) k base
          (packingSphereSymmetricIncrement (fun z ↦ root i z.1) x) x| ≤
      (2 * ((jetBound / radius i ^ 2) / (k : ℝ) ^ 2)) * sphereChordalSq y.1 x.1
  farShellCount : ℕ
  farShell : sphereSet n → Fin N → Fin farShellCount
  farShellConstant : ℝ
  farShellConstant_nonneg : 0 ≤ farShellConstant
  scale_far_shell_distance : ∀ x (hx : x ∈ sphereSet n),
      ∀ (j : Fin J) (q : Fin farShellCount) i,
    i ∈ (Finset.univ.filter (fun i ↦ scale i = j ∧
        ¬ sphereChordalSq x (center i).1 ≤ radius i ^ 2)).filter
          (fun i ↦ farShell ⟨x, hx⟩ i = q) →
      (2 : ℝ) ^ (q : ℕ) * radius i ≤ Real.sqrt (sphereChordalSq x (center i).1)
  scale_far_shell_card_budget : ∀ x (hx : x ∈ sphereSet n),
      ∀ (j : Fin J) (q : Fin farShellCount),
    (((Finset.univ.filter (fun i ↦ scale i = j ∧
        ¬ sphereChordalSq x (center i).1 ≤ radius i ^ 2)).filter
          (fun i ↦ farShell ⟨x, hx⟩ i = q)).card : ℝ) *
        (1 + (2 : ℝ) ^ (q : ℕ))⁻¹ ^ (2 * (n + 3)) ≤
      farShellConstant * (1 / 2 : ℝ) ^ (q : ℕ)
  cross_constant_budget :
    (overlapBound : ℝ) * (jetBound * (jetBound * E)) ≤ C / 4
  square_constant_budget :
    (16 / 15 : ℝ) * ((jetBound * E) ^ 2 *
      ((overlapBound : ℝ) + 2 * farShellConstant)) ≤ C / 4

/-- Uniform existence of the concrete finite package. -/
def HasFiniteSphereAtomPackage (n : ℕ) (E C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
    ∀ k, k₀ ≤ k → Nonempty (FiniteSphereAtomPackage n E C k F)

/-- Uniform upgrade data assemble into the final package after enlarging one constant. -/
theorem finiteSphereAtomPackage_of_upgrade {n : ℕ}
    (hupgrade : HasUniformFiniteSphereAtomUpgrade n) :
    ∀ E : ℝ, 0 ≤ E →
      ∃ C : ℝ, ∃ k₀ : ℕ,
        0 < C ∧ 1 ≤ k₀ ∧ HasFiniteSphereAtomPackage n E C k₀ := by
  obtain ⟨A, J, D, B, hA, hJ, hD, hB, hfamilies⟩ := hupgrade
  intro E hE
  let cross : ℝ := (B : ℝ) * (J * (J * E))
  let square : ℝ := (16 / 15 : ℝ) * ((J * E) ^ 2 * ((B : ℝ) + 2 * D))
  let C : ℝ := A + 4 * cross + 4 * square + 1
  have hcross : 0 ≤ cross := by dsimp [cross]; positivity
  have hsquare : 0 ≤ square := by dsimp [square]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith
  refine ⟨C, 1, hC, le_rfl, ?_⟩
  intro F hF hnorm k hk
  obtain ⟨atoms, hjet, hoverlap, hupNonempty⟩ := hfamilies F hF hnorm k hk
  let up := Classical.choice hupNonempty
  let enlarged := atoms.mono hAC hk
  have hjet_nonneg : 0 ≤ atoms.jetBound := atoms.jetBound_nonneg
  have hoverlapReal : (atoms.overlapBound : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hoverlap
  have hcrossActual :
      (atoms.overlapBound : ℝ) * (atoms.jetBound * (atoms.jetBound * E)) ≤ cross := by
    dsimp [cross]
    gcongr
  have hsquareActual :
      (16 / 15 : ℝ) * ((atoms.jetBound * E) ^ 2 *
        ((atoms.overlapBound : ℝ) + 2 * D)) ≤ square := by
    dsimp [square]
    gcongr
  exact ⟨{
    toFiniteSphereAtomTruncation := enlarged
    filter_increment_oscillation := up.filter_increment_oscillation
    farShellCount := up.farShellCount
    farShell := up.farShell
    farShellConstant := D
    farShellConstant_nonneg := hD
    scale_far_shell_distance := up.scale_far_shell_distance
    scale_far_shell_card_budget := up.scale_far_shell_card_budget
    cross_constant_budget := by
      calc
        (atoms.overlapBound : ℝ) * (atoms.jetBound * (atoms.jetBound * E)) ≤ cross :=
          hcrossActual
        _ ≤ C / 4 := by dsimp [C]; linarith
    square_constant_budget := by
      calc
        (16 / 15 : ℝ) * ((atoms.jetBound * E) ^ 2 *
            ((atoms.overlapBound : ℝ) + 2 * D)) ≤ square := hsquareActual
        _ ≤ C / 4 := by dsimp [C]; linarith }⟩

/-- Discarding radii below `1 / k` gives a finite family with a quartic remainder. -/
theorem finiteSphereAtomTruncation_of_sphereAtoms {n : ℕ} (hn : 3 ≤ n)
    (hatoms : HasUniformSphereAtomDecomposition n) :
    HasUniformFiniteSphereAtomTruncation n := by
  obtain ⟨C, B, hC, hB, hfamilies⟩ := hatoms
  refine ⟨4 * (B : ℝ) * C ^ 2, C, B, ?_, hC.le, hB, ?_⟩
  · positivity
  · intro F hF hnorm k hk
    let atoms := Classical.choice (hfamilies F hF hnorm)
    let truncation := atoms.toFiniteTruncation (by omega) hC.le k hk
    exact ⟨⟨truncation, le_rfl, le_rfl⟩⟩

/-- Dyadic shell packing and root-filter regularity upgrade a truncation to the final package. -/
theorem finiteSphereAtomPackage_of_truncation {n : ℕ} (hn : 3 ≤ n)
    (htrunc : HasUniformFiniteSphereAtomTruncation n) :
    ∀ E : ℝ, 0 ≤ E →
      ∃ C : ℝ, ∃ k₀ : ℕ,
        0 < C ∧ 1 ≤ k₀ ∧ HasFiniteSphereAtomPackage n E C k₀ := by
  exact finiteSphereAtomPackage_of_upgrade (finiteSphereAtomUpgrade_of_truncation hn htrunc)

/-- The finite-packing stage assembled from countable sphere atoms. -/
theorem finiteSphereAtomPackage_of_sphereAtoms {n : ℕ} (hn : 3 ≤ n)
    (hatoms : HasUniformSphereAtomDecomposition n) :
    ∀ E : ℝ, 0 ≤ E →
      ∃ C : ℝ, ∃ k₀ : ℕ,
        0 < C ∧ 1 ≤ k₀ ∧ HasFiniteSphereAtomPackage n E C k₀ := by
  exact finiteSphereAtomPackage_of_truncation hn
    (finiteSphereAtomTruncation_of_sphereAtoms hn hatoms)

end QuarticConvergence
end OptimalConvergenceRates

end

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- The zero polynomial satisfies the complete finite atom package. -/
def zeroFiniteSphereAtomPackage {n : ℕ} (hn : 0 < n) (E C : ℝ) (hC : 0 ≤ C)
    (k : ℕ) : FiniteSphereAtomPackage n E C k 0 where
  toFiniteSphereAtomTruncation := zeroFiniteSphereAtomTruncation hn C hC k
  filter_increment_oscillation := by
    intro i
    exact Fin.elim0 i
  farShellCount := 1
  farShell := fun x i ↦ Fin.elim0 i
  farShellConstant := 0
  farShellConstant_nonneg := le_rfl
  scale_far_shell_distance := by
    intro x hx j q i
    exact Fin.elim0 i
  scale_far_shell_card_budget := by
    intro x hx j q
    simp
  cross_constant_budget := by
    simp only [CharP.cast_eq_zero, zero_mul]
    positivity
  square_constant_budget := by
    simp only [CharP.cast_eq_zero, mul_zero, add_zero]
    positivity

/-- The complete finite package is nonempty for the zero polynomial. -/
theorem zero_hasFiniteSphereAtomPackage {n : ℕ} (hn : 0 < n) (E C : ℝ)
    (hC : 0 ≤ C) (k : ℕ) : Nonempty (FiniteSphereAtomPackage n E C k 0) := by
  exact ⟨zeroFiniteSphereAtomPackage hn E C hC k⟩

end QuarticConvergence
end OptimalConvergenceRates

end
