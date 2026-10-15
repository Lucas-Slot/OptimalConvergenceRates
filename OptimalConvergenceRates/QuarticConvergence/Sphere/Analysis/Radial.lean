/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/Radial.lean

  Compact radial extension and restriction of Euclidean atoms to the sphere.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.AtomInduction
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Localization

open MvPolynomial Set
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

-- Sphere-membership proofs in the fields intentionally express the domain of each assertion.
set_option linter.unusedVariables false in
/-- A countable scale-resolved square decomposition on the repository's algebraic sphere. -/
structure SphereAtomFamily (n : ℕ) (F : MvPolynomial (Fin n) ℝ) (C : ℝ) (B : ℕ) where
  active : Set ℕ
  root : ℕ → ((Fin n → ℝ) → ℝ)
  center : ℕ → sphereSet n
  radius : ℕ → ℝ
  root_eq_zero_of_not_active : ∀ i, i ∉ active → root i = 0
  radius_pos : ∀ i, i ∈ active → 0 < radius i
  radius_le_one : ∀ i, i ∈ active → radius i ≤ 1
  root_contDiff : ∀ i, ContDiff ℝ 4 (root i)
  supported : ∀ i x (hx : x ∈ sphereSet n), root i x ≠ 0 →
    (⟨x, hx⟩ : sphereSet n) ∈ sphereChordalCap (center i) (radius i)
  square_identity : ∀ x (hx : x ∈ sphereSet n),
    HasSum (fun i ↦ root i x ^ 2) (MvPolynomial.eval x F)
  dilated_overlap : ∀ x (hx : x ∈ sphereSet n) (s : Finset ℕ),
    Set.ncard {i | i ∈ s ∧ i ∈ active ∧
      sphereChordalSq x (center i).1 ≤ radius i ^ 2} ≤ B
  scaled_jets : ∀ i j, j ≤ 4 → ∀ x,
    ‖iteratedFDeriv ℝ j (root i) x‖ * radius i ^ j ≤ C * radius i ^ 2
/-- The zero polynomial has the empty active sphere-atom family. -/
def zeroSphereAtomFamily {n : ℕ} (hn : 0 < n) (C : ℝ) (hC : 0 ≤ C) :
    SphereAtomFamily n 0 C 0 where
  root := fun _ _ ↦ 0
  active := ∅
  center := fun _ ↦ sphereNorthPolePoint hn
  radius := fun _ ↦ 1
  root_eq_zero_of_not_active := by
    intro i hi
    rfl
  radius_pos := by
    intro i hi
    simp at hi
  radius_le_one := by
    intro i hi
    simp at hi
  root_contDiff := by
    intro i
    exact contDiff_const
  supported := by
    intro i x hx hroot
    simp at hroot
  square_identity := by
    intro x hx
    simp
  dilated_overlap := by simp
  scaled_jets := by
    intro i j hj x
    rw [iteratedFDeriv_fun_zero]
    simpa using hC

/-- The zero sphere family has the expected pointwise `tsum` identity. -/
@[simp] theorem zeroSphereAtomFamily_tsum_sq {n : ℕ} (hn : 0 < n)
    (C : ℝ) (hC : 0 ≤ C) (x : Fin n → ℝ) :
    ∑' i, (zeroSphereAtomFamily hn C hC).root i x ^ 2 = 0 := by
  simp [zeroSphereAtomFamily]


/-- Any polynomial vanishing on the sphere has the empty active sphere-atom family. -/
def sphereZeroAtomFamily {n : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ)
    (hF : ∀ x, x ∈ sphereSet n → MvPolynomial.eval x F = 0)
    (C : ℝ) (hC : 0 ≤ C) : SphereAtomFamily n F C 0 where
  root := fun _ _ ↦ 0
  active := ∅
  center := fun _ ↦ sphereNorthPolePoint hn
  radius := fun _ ↦ 1
  root_eq_zero_of_not_active := by
    intro i hi
    rfl
  radius_pos := by simp
  radius_le_one := by simp
  root_contDiff := by
    intro i
    exact contDiff_const
  supported := by simp
  square_identity := by
    intro x hx
    simp [hF x hx]
  dilated_overlap := by simp
  scaled_jets := by
    intro i j hj x
    rw [iteratedFDeriv_fun_zero]
    simpa using hC

/-- The sphere geometry needed to reinterpret one Euclidean atom family on the algebraic sphere.
The atom radii are preserved, so the scaled jet bounds transfer definitionally. -/
structure EuclideanAtomSphereGeometry {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {A radiusCap C : ℝ} {B : ℕ} (atoms : EuclideanAtomFamily u A radiusCap C B) where
  center : ℕ → sphereSet n
  radius_pos : ∀ i, i ∈ atoms.active → 0 < atoms.radius i
  radius_le_one : ∀ i, i ∈ atoms.active → atoms.radius i ≤ 1
  supported : ∀ i x (hx : x ∈ sphereSet n), atoms.root i x ≠ 0 →
    (⟨x, hx⟩ : sphereSet n) ∈ sphereChordalCap (center i) (atoms.radius i)
  overlap : ∀ x (_hx : x ∈ sphereSet n) (s : Finset ℕ),
    Set.ncard {i | i ∈ s ∧ i ∈ atoms.active ∧
      sphereChordalSq x (center i).1 ≤ atoms.radius i ^ 2} ≤ B

/-- Exact restriction of a Euclidean square identity, together with sphere support geometry,
produces a `SphereAtomFamily` without changing roots, radii, jet constants, or overlap bound. -/
def EuclideanAtomFamily.toSphereAtomFamily {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {A radiusCap C : ℝ} {B : ℕ} (atoms : EuclideanAtomFamily u A radiusCap C B)
    {F : MvPolynomial (Fin n) ℝ}
    (geometry : EuclideanAtomSphereGeometry atoms)
    (hrestrict : ∀ x, x ∈ sphereSet n → u x = MvPolynomial.eval x F) :
    SphereAtomFamily n F C B where
  active := atoms.active
  root := atoms.root
  center := geometry.center
  radius := atoms.radius
  root_eq_zero_of_not_active := atoms.root_eq_zero_of_not_active
  radius_pos := geometry.radius_pos
  radius_le_one := geometry.radius_le_one
  root_contDiff := atoms.root_contDiff
  supported := geometry.supported
  square_identity := by
    intro x hx
    simpa [hrestrict x hx] using atoms.square_identity x
  dilated_overlap := geometry.overlap
  scaled_jets := atoms.scaled_jets
/-- Uniform scale-resolved sphere atoms obtained from a compact radial extension. -/
def HasUniformSphereAtomDecomposition (n : ℕ) : Prop :=
  ∃ C : ℝ, ∃ B : ℕ, 0 < C ∧ 0 < B ∧
    ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
      Nonempty (SphereAtomFamily n F C B)

/-- The pointwise countable square identity can be read as an ordinary `tsum`. -/
theorem SphereAtomFamily.tsum_sq_eq {n : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {C : ℝ} {B : ℕ} (atoms : SphereAtomFamily n F C B)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    ∑' i, atoms.root i x ^ 2 = MvPolynomial.eval x F := by
  exact (atoms.square_identity x hx).tsum_eq


-- The membership witness intentionally restricts the existential point to the sphere.
set_option linter.unusedVariables false in
/-- An ambient atom is visible when its root is nonzero at some point of the sphere.  Invisible
atoms can be discarded after restriction, even when they are nonzero away from the sphere. -/
def EuclideanAtomFamily.SphereVisible {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    {A radiusCap C : ℝ} {B : ℕ} (atoms : EuclideanAtomFamily u A radiusCap C B)
    (i : ℕ) : Prop :=
  ∃ x : Fin n → ℝ, ∃ hx : x ∈ sphereSet n, atoms.root i x ≠ 0

/-- A chosen sphere point witnessing visibility, with the north pole used only for invisible
indices. -/
noncomputable def EuclideanAtomFamily.sphereCenter {n : ℕ} (hn : 0 < n)
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) (i : ℕ) : sphereSet n := by
  classical
  exact if h : atoms.SphereVisible i then
    ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩
  else sphereNorthPolePoint hn

theorem EuclideanAtomFamily.root_sphereCenter_ne_zero_of_visible {n : ℕ} (hn : 0 < n)
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) {i : ℕ}
    (hi : atoms.SphereVisible i) : atoms.root i (atoms.sphereCenter hn i).1 ≠ 0 := by
  simp only [EuclideanAtomFamily.sphereCenter, dite_eq_left hi]
  exact Classical.choose_spec (Classical.choose_spec hi)

/-- The squared chordal distance is bounded by the dimension times the square of the ambient
sup-norm distance.  This is the explicit norm adapter needed because the Euclidean atom theorem
currently uses the product sup norm on Fin n → ℝ. -/
theorem sphereChordalSq_le_card_mul_dist_sq {n : ℕ} (x y : Fin n → ℝ) :
    sphereChordalSq x y ≤ (n : ℝ) * dist x y ^ 2 := by
  rw [dist_eq_norm]
  unfold sphereChordalSq
  calc
    (∑ i, (x i - y i) ^ 2) ≤ ∑ _i : Fin n, ‖x - y‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoord : |x i - y i| ≤ ‖x - y‖ := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using
          (norm_le_pi_norm (f := x - y) i)
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (x i - y i)) (norm_nonneg (x - y))).2 hcoord
    _ = (n : ℝ) * ‖x - y‖ ^ 2 := by simp

/-- A chordal cap controls the ambient product distance. -/
theorem dist_le_of_sphereChordalSq_le_sq {n : ℕ} {x y : Fin n → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hxy : sphereChordalSq x y ≤ r ^ 2) : dist x y ≤ r := by
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg hr]
  intro i
  rw [Real.norm_eq_abs]
  have hterm : (x i - y i) ^ 2 ≤ sphereChordalSq x y := by
    unfold sphereChordalSq
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j - y j)) (Finset.mem_univ i)
  have hsq : (x i - y i) ^ 2 ≤ r ^ 2 := hterm.trans hxy
  exact (sq_le_sq₀ (abs_nonneg _) hr).mp (by simpa only [Pi.sub_apply, sq_abs] using hsq)



/-- Keep only roots visible on the sphere and multiply them by a common nonnegative scale. -/
noncomputable def EuclideanAtomFamily.sphereFilteredRoot {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) (s : ℝ)
    (i : ℕ) : (Fin n → ℝ) → ℝ := by
  classical
  exact if atoms.SphereVisible i then fun x ↦ s * atoms.root i x else 0

/-- The ambient function represented by the sphere-visible, rescaled subfamily. -/
noncomputable def EuclideanAtomFamily.sphereFilteredFunction {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) (s : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑' i, atoms.sphereFilteredRoot s i x ^ 2

-- Nonnegativity of the scale is retained for the shared filtered-family interface.
set_option linter.unusedVariables false in
theorem EuclideanAtomFamily.summable_sphereFilteredRoot_sq {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) {s : ℝ} (hs : 0 ≤ s)
    (x : Fin n → ℝ) :
    Summable (fun i ↦ atoms.sphereFilteredRoot s i x ^ 2) := by
  apply Summable.of_nonneg_of_le
      (fun i ↦ sq_nonneg (atoms.sphereFilteredRoot s i x))
      (fun i ↦ ?_) ((atoms.square_identity x).mul_left (s ^ 2)).summable
  by_cases hi : atoms.SphereVisible i
  · simp [EuclideanAtomFamily.sphereFilteredRoot, hi, mul_pow]
  · simp only [sphereFilteredRoot, hi, ↓reduceIte, Pi.zero_apply, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

theorem EuclideanAtomFamily.hasSum_sphereFilteredRoot_sq {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) {s : ℝ} (hs : 0 ≤ s)
    (x : Fin n → ℝ) :
    HasSum (fun i ↦ atoms.sphereFilteredRoot s i x ^ 2)
      (atoms.sphereFilteredFunction s x) :=
  (atoms.summable_sphereFilteredRoot_sq hs x).hasSum

/-- At a sphere point, filtering discards only zero terms. -/
theorem EuclideanAtomFamily.hasSum_sphereFilteredRoot_sq_on_sphere {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) {s : ℝ}
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    HasSum (fun i ↦ atoms.sphereFilteredRoot s i x ^ 2) (s ^ 2 * u x) := by
  convert (atoms.square_identity x).mul_left (s ^ 2) using 1
  funext i
  by_cases hi : atoms.SphereVisible i
  · simp [EuclideanAtomFamily.sphereFilteredRoot, hi, mul_pow]
  · have hzero : atoms.root i x = 0 := by
      by_contra hne
      exact hi ⟨x, hx, hne⟩
    simp [EuclideanAtomFamily.sphereFilteredRoot, hi, hzero]

theorem EuclideanAtomFamily.sphereFilteredFunction_eq_on_sphere {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {A radiusCap C : ℝ} {B : ℕ}
    (atoms : EuclideanAtomFamily u A radiusCap C B) {s : ℝ} (hs : 0 ≤ s)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    atoms.sphereFilteredFunction s x = s ^ 2 * u x := by
  rw [← (atoms.hasSum_sphereFilteredRoot_sq_on_sphere (s := s) x hx).tsum_eq]
  exact (atoms.hasSum_sphereFilteredRoot_sq hs x).tsum_eq

-- Positive dimension is retained so this constructor matches the sphere-restriction API.
set_option linter.unusedVariables false in
/-- Filtering, root rescaling, and uniform radius widening preserve all Euclidean atom fields.
The loss s C L² absorbs derivatives of order at most four after radii are multiplied by L. -/
noncomputable def EuclideanAtomFamily.sphereFilteredWidened {n : ℕ}
    (hn : 0 < n) {u : (Fin n → ℝ) → ℝ} {L s C : ℝ} {B : ℕ}
    (hL : 1 ≤ L) (hs : 0 < s) (hC : 0 ≤ C)
    (atoms : EuclideanAtomFamily u (L + 1) L⁻¹ C B) :
    EuclideanAtomFamily (atoms.sphereFilteredFunction s) 1 1 (s * C * L ^ 2) B := by
  classical
  let visible : Set ℕ := {i | atoms.SphereVisible i}
  refine {
    root := atoms.sphereFilteredRoot s
    active := atoms.active ∩ visible
    center := atoms.center
    radius := fun i ↦ L * atoms.radius i
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
  · intro i hi
    by_cases hvis : atoms.SphereVisible i
    · have hia : i ∉ atoms.active := by
        intro hia
        exact hi ⟨hia, hvis⟩
      rw [EuclideanAtomFamily.sphereFilteredRoot, ite_eq_left hvis,
        atoms.root_eq_zero_of_not_active i hia]
      ext x
      simp
    · simp [EuclideanAtomFamily.sphereFilteredRoot, hvis]
  · intro i hi
    exact mul_pos (lt_of_lt_of_le zero_lt_one hL) (atoms.radius_pos i hi.1)
  · intro i hi
    have hr := atoms.radius_le_cap i hi.1
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
    change L * atoms.radius i ≤ 1
    calc
      L * atoms.radius i ≤ L * L⁻¹ := mul_le_mul_of_nonneg_left hr hLpos.le
      _ = 1 := by field_simp
  · intro i
    by_cases hvis : atoms.SphereVisible i
    · simpa [EuclideanAtomFamily.sphereFilteredRoot, hvis, smul_eq_mul] using
        (atoms.root_contDiff i).const_smul s
    · simp only [sphereFilteredRoot, hvis, ↓reduceIte]
      exact contDiff_const
  · intro i
    by_cases hvis : atoms.SphereVisible i
    · rw [EuclideanAtomFamily.sphereFilteredRoot, ite_eq_left hvis]
      change HasCompactSupport (s • atoms.root i)
      exact (atoms.root_compact_support i).smul_left
    · simp [EuclideanAtomFamily.sphereFilteredRoot, hvis, HasCompactSupport]
  · intro i x hx
    have hvis : atoms.SphereVisible i := by
      by_contra hnvis
      simp [EuclideanAtomFamily.sphereFilteredRoot, hnvis] at hx
    have hraw : x ∈ Metric.ball (atoms.center i) (atoms.radius i) := by
      apply atoms.supported i
      change atoms.root i x ≠ 0
      simpa [EuclideanAtomFamily.sphereFilteredRoot, hvis, hs.ne'] using hx
    rw [Metric.mem_ball] at hraw ⊢
    have hroot : atoms.root i x ≠ 0 := by
      simpa [EuclideanAtomFamily.sphereFilteredRoot, hvis, hs.ne'] using hx
    have hia : i ∈ atoms.active := by
      by_contra hnia
      exact hroot (congrFun (atoms.root_eq_zero_of_not_active i hnia) x)
    have hri : 0 < atoms.radius i := atoms.radius_pos i hia
    exact hraw.trans_le (by nlinarith)
  · intro x
    exact atoms.hasSum_sphereFilteredRoot_sq hs.le x
  · intro x t
    let rawSet : Set ℕ :=
      {i | i ∈ t ∧ i ∈ atoms.active ∧
        x ∈ Metric.ball (atoms.center i) ((L + 1) * atoms.radius i)}
    have hsubset :
        {i | i ∈ t ∧ i ∈ atoms.active ∩ visible ∧
          x ∈ Metric.ball (atoms.center i) (1 * (L * atoms.radius i))} ⊆ rawSet := by
      intro i hi
      change i ∈ t ∧ i ∈ atoms.active ∩ visible ∧
        x ∈ Metric.ball (atoms.center i) (1 * (L * atoms.radius i)) at hi
      refine ⟨hi.1, hi.2.1.1, ?_⟩
      rw [Metric.mem_ball] at hi ⊢
      have hri := atoms.radius_pos i hi.2.1.1
      exact hi.2.2.trans (by nlinarith)
    have hrawFinite : rawSet.Finite := by
      apply t.finite_toSet.subset
      intro i hi
      exact hi.1
    exact (Set.ncard_le_ncard hsubset hrawFinite).trans (atoms.dilated_overlap x t)
  · intro i j hj x
    by_cases hvis : atoms.SphereVisible i
    · have hderiv :
          iteratedFDeriv ℝ j (atoms.sphereFilteredRoot s i) x =
            s • iteratedFDeriv ℝ j (atoms.root i) x := by
          rw [show atoms.sphereFilteredRoot s i = s • atoms.root i by
            funext y
            simp [EuclideanAtomFamily.sphereFilteredRoot, hvis, smul_eq_mul]]
          exact iteratedFDeriv_const_smul_apply
            ((atoms.root_contDiff i).contDiffAt.of_le (by exact_mod_cast hj))
      rw [hderiv, norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow]
      have hraw := atoms.scaled_jets i j hj x
      have hpow : L ^ j ≤ L ^ 4 := pow_le_pow_right₀ hL hj
      calc
        (s * ‖iteratedFDeriv ℝ j (atoms.root i) x‖) *
              (L ^ j * atoms.radius i ^ j) =
            s * L ^ j *
              (‖iteratedFDeriv ℝ j (atoms.root i) x‖ * atoms.radius i ^ j) := by
                ring
        _ ≤ s * L ^ j * (C * atoms.radius i ^ 2) := by gcongr
        _ ≤ s * L ^ 4 * (C * atoms.radius i ^ 2) := by gcongr
        _ = (s * C * L ^ 2) * (L * atoms.radius i) ^ 2 := by ring
    · have hz : atoms.sphereFilteredRoot s i = 0 := by
        simp [EuclideanAtomFamily.sphereFilteredRoot, hvis]
      rw [hz]
      change ‖iteratedFDeriv ℝ j (fun _ : Fin n → ℝ ↦ (0 : ℝ)) x‖ *
        (L * atoms.radius i) ^ j ≤ s * C * L ^ 2 * (L * atoms.radius i) ^ 2
      rw [iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply, norm_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg hs.le hC) (sq_nonneg L))
        (sq_nonneg (L * atoms.radius i))



/-- The visible, widened family admits sphere centers with the required cap support and overlap.
The dimension inequality is exactly the finite-product norm loss from sup norm to chordal norm. -/
noncomputable def EuclideanAtomFamily.sphereFilteredWidenedGeometry {n : ℕ}
    (hn : 0 < n) {u : (Fin n → ℝ) → ℝ} {L s C : ℝ} {B : ℕ}
    (hL : 1 ≤ L) (hdim : 4 * (n : ℝ) ≤ L ^ 2) (hs : 0 < s) (hC : 0 ≤ C)
    (atoms : EuclideanAtomFamily u (L + 1) L⁻¹ C B) :
    EuclideanAtomSphereGeometry (atoms.sphereFilteredWidened hn hL hs hC) := by
  classical
  let widened := atoms.sphereFilteredWidened hn hL hs hC
  refine {
    center := atoms.sphereCenter hn
    radius_pos := widened.radius_pos
    radius_le_one := widened.radius_le_cap
    supported := ?_
    overlap := ?_
  }
  · intro i x hx hroot
    change atoms.sphereFilteredRoot s i x ≠ 0 at hroot
    have hvis : atoms.SphereVisible i := by
      by_contra hnvis
      simp [EuclideanAtomFamily.sphereFilteredRoot, hnvis] at hroot
    have hrawRoot : atoms.root i x ≠ 0 := by
      simpa [EuclideanAtomFamily.sphereFilteredRoot, hvis, hs.ne'] using hroot
    have hia : i ∈ atoms.active := by
      by_contra hnia
      exact hrawRoot (congrFun (atoms.root_eq_zero_of_not_active i hnia) x)
    have hri : 0 < atoms.radius i := atoms.radius_pos i hia
    have hxball := atoms.supported i hrawRoot
    have hyroot := atoms.root_sphereCenter_ne_zero_of_visible hn hvis
    have hyball := atoms.supported i hyroot
    have hdist : dist x (atoms.sphereCenter hn i).1 < 2 * atoms.radius i := by
      rw [Metric.mem_ball] at hxball hyball
      calc
        dist x (atoms.sphereCenter hn i).1 ≤
            dist x (atoms.center i) + dist (atoms.center i) (atoms.sphereCenter hn i).1 :=
          dist_triangle _ _ _
        _ < atoms.radius i + atoms.radius i := by
          rw [dist_comm (atoms.center i)]
          gcongr
        _ = 2 * atoms.radius i := by ring
    have hdistSq :
        dist x (atoms.sphereCenter hn i).1 ^ 2 ≤ (2 * atoms.radius i) ^ 2 :=
      (sq_le_sq₀ dist_nonneg (by positivity)).2 hdist.le
    have hchord := sphereChordalSq_le_card_mul_dist_sq
      x (atoms.sphereCenter hn i).1
    have hscaled :
        (n : ℝ) * (2 * atoms.radius i) ^ 2 ≤ (L * atoms.radius i) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hdim (sq_nonneg (atoms.radius i))
      nlinarith
    change sphereChordalSq x (atoms.sphereCenter hn i).1 ≤
      (L * atoms.radius i) ^ 2
    exact hchord.trans <|
      (mul_le_mul_of_nonneg_left hdistSq (Nat.cast_nonneg n)).trans hscaled
  · intro x hx t
    let rawSet : Set ℕ :=
      {i | i ∈ t ∧ i ∈ atoms.active ∧
        x ∈ Metric.ball (atoms.center i) ((L + 1) * atoms.radius i)}
    have hsubset :
        {i | i ∈ t ∧ i ∈ widened.active ∧
          sphereChordalSq x (atoms.sphereCenter hn i).1 ≤ widened.radius i ^ 2} ⊆ rawSet := by
      intro i hi
      change i ∈ t ∧ i ∈ atoms.active ∩ {j | atoms.SphereVisible j} ∧
        sphereChordalSq x (atoms.sphereCenter hn i).1 ≤
          (L * atoms.radius i) ^ 2 at hi
      have hia : i ∈ atoms.active := hi.2.1.1
      have hvis : atoms.SphereVisible i := hi.2.1.2
      have hri : 0 < atoms.radius i := atoms.radius_pos i hia
      have hnear :
          dist x (atoms.sphereCenter hn i).1 ≤ L * atoms.radius i :=
        dist_le_of_sphereChordalSq_le_sq
          (mul_nonneg (lt_of_lt_of_le zero_lt_one hL).le hri.le) hi.2.2
      have hyroot := atoms.root_sphereCenter_ne_zero_of_visible hn hvis
      have hyball := atoms.supported i hyroot
      rw [Metric.mem_ball] at hyball
      refine ⟨hi.1, hia, ?_⟩
      rw [Metric.mem_ball]
      calc
        dist x (atoms.center i) ≤
            dist x (atoms.sphereCenter hn i).1 +
              dist (atoms.sphereCenter hn i).1 (atoms.center i) :=
          dist_triangle _ _ _
        _ < L * atoms.radius i + atoms.radius i := add_lt_add_of_le_of_lt hnear hyball
        _ = (L + 1) * atoms.radius i := by ring
    have hrawFinite : rawSet.Finite := by
      apply t.finite_toSet.subset
      intro i hi
      exact hi.1
    exact (Set.ncard_le_ncard hsubset hrawFinite).trans (atoms.dilated_overlap x t)



/-- Squared Euclidean length, kept separate from the product sup norm used by ambient balls. -/
def radialNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2



/-- Evaluation of a multivariate real polynomial is smooth in its coordinate vector. -/
theorem mvPolynomial_eval_contDiff {n : ℕ} (F : MvPolynomial (Fin n) ℝ) (N : ℕ∞) :
    ContDiff ℝ N (fun x : Fin n → ℝ ↦ MvPolynomial.eval x F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ N (fun _ : Fin n → ℝ ↦ a))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
      simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℝ ℝ i)

/-- Squared Euclidean length is smooth. -/
theorem radialNormSq_contDiff {n : ℕ} (N : ℕ∞) :
    ContDiff ℝ N (radialNormSq : (Fin n → ℝ) → ℝ) := by
  unfold radialNormSq
  fun_prop

/-- Radial projection onto the algebraic sphere.  Its value at the origin is irrelevant because
the annular cutoff below vanishes on a neighborhood of the origin. -/
def radialDirection {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  (Real.sqrt (radialNormSq x))⁻¹ • x

/-- A fixed smooth annular cutoff, equal to one when squared radius is near one and supported
where squared radius lies within one half of one. -/
def radialAnnularCutoff (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  rescaledUnitBump (fun _ : Fin 1 ↦ (1 : ℝ)) (1 / 4)
    (fun _ : Fin 1 ↦ radialNormSq x)

/-- The compact radial extension used here, expressed using an everywhere-defined radial
direction and a cutoff that kills its singularity near the origin. -/
def compactRadialExtension {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  radialAnnularCutoff n x ^ 2 * MvPolynomial.eval (radialDirection x) F

theorem radialNormSq_eq_one_of_mem_sphere {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ sphereSet n) : radialNormSq x = 1 := by
  simpa [sphereSet, sphereQuadratic, radialNormSq, pow_two] using hx

theorem radialDirection_eq_self_of_mem_sphere {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ sphereSet n) : radialDirection x = x := by
  rw [radialDirection, radialNormSq_eq_one_of_mem_sphere hx]
  simp

theorem radialAnnularCutoff_eq_one_of_mem_sphere {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ sphereSet n) : radialAnnularCutoff n x = 1 := by
  unfold radialAnnularCutoff
  apply rescaledUnitBump_eq_one (fun _ : Fin 1 ↦ (1 : ℝ)) (by norm_num)
  have hnorm := radialNormSq_eq_one_of_mem_sphere hx
  simp [Metric.mem_closedBall, hnorm]



theorem radialNormSq_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ radialNormSq x := by
  exact Finset.sum_nonneg fun i hi ↦ sq_nonneg (x i)

theorem radialDirection_mem_sphere {n : ℕ} {x : Fin n → ℝ}
    (hx : 0 < radialNormSq x) : radialDirection x ∈ sphereSet n := by
  have hsqrt : 0 < Real.sqrt (radialNormSq x) := Real.sqrt_pos.2 hx
  change MvPolynomial.eval (radialDirection x) (sphereQuadratic n) = 1
  simp only [sphereQuadratic, map_sum, map_pow, eval_X, radialDirection, Pi.smul_apply,
    smul_eq_mul]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  change (Real.sqrt (radialNormSq x))⁻¹ ^ 2 * radialNormSq x = 1
  rw [inv_pow, Real.sq_sqrt (radialNormSq_nonneg x)]
  exact inv_mul_cancel₀ hx.ne'

theorem radialNormSq_pos_of_radialAnnularCutoff_ne_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : radialAnnularCutoff n x ≠ 0) : 0 < radialNormSq x := by
  have hsupp :
      (fun _ : Fin 1 ↦ radialNormSq x) ∈
        Function.support
          (rescaledUnitBump (fun _ : Fin 1 ↦ (1 : ℝ)) (1 / 4)) := hx
  rw [support_rescaledUnitBump (fun _ : Fin 1 ↦ (1 : ℝ)) (by norm_num)] at hsupp
  have hnorm :
      ‖(fun _ : Fin 1 ↦ radialNormSq x) - (fun _ : Fin 1 ↦ (1 : ℝ))‖ <
        (1 / 2 : ℝ) := by
    rw [Metric.mem_ball, dist_eq_norm] at hsupp
    norm_num at hsupp ⊢
    exact hsupp
  have hcoord := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1 / 2)).1 hnorm (0 : Fin 1)
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoord
  rw [abs_lt] at hcoord
  linarith



theorem radialNormSq_lt_three_halves_of_radialAnnularCutoff_ne_zero
    {n : ℕ} {x : Fin n → ℝ} (hx : radialAnnularCutoff n x ≠ 0) :
    radialNormSq x < 3 / 2 := by
  have hsupp :
      (fun _ : Fin 1 ↦ radialNormSq x) ∈
        Function.support
          (rescaledUnitBump (fun _ : Fin 1 ↦ (1 : ℝ)) (1 / 4)) := hx
  rw [support_rescaledUnitBump (fun _ : Fin 1 ↦ (1 : ℝ)) (by norm_num)] at hsupp
  have hnorm :
      ‖(fun _ : Fin 1 ↦ radialNormSq x) - (fun _ : Fin 1 ↦ (1 : ℝ))‖ <
        (1 / 2 : ℝ) := by
    rw [Metric.mem_ball, dist_eq_norm] at hsupp
    norm_num at hsupp ⊢
    exact hsupp
  have hcoord := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1 / 2)).1 hnorm (0 : Fin 1)
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoord
  rw [abs_lt] at hcoord
  linarith



theorem one_half_lt_radialNormSq_of_radialAnnularCutoff_ne_zero
    {n : ℕ} {x : Fin n → ℝ} (hx : radialAnnularCutoff n x ≠ 0) :
    1 / 2 < radialNormSq x := by
  have hsupp :
      (fun _ : Fin 1 ↦ radialNormSq x) ∈
        Function.support
          (rescaledUnitBump (fun _ : Fin 1 ↦ (1 : ℝ)) (1 / 4)) := hx
  rw [support_rescaledUnitBump (fun _ : Fin 1 ↦ (1 : ℝ)) (by norm_num)] at hsupp
  have hnorm :
      ‖(fun _ : Fin 1 ↦ radialNormSq x) - (fun _ : Fin 1 ↦ (1 : ℝ))‖ <
        (1 / 2 : ℝ) := by
    rw [Metric.mem_ball, dist_eq_norm] at hsupp
    norm_num at hsupp ⊢
    exact hsupp
  have hcoord := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1 / 2)).1 hnorm (0 : Fin 1)
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoord
  rw [abs_lt] at hcoord
  linarith

theorem radialAnnularCutoff_eq_zero_of_le_half {n : ℕ} {x : Fin n → ℝ}
    (hx : radialNormSq x ≤ 1 / 2) : radialAnnularCutoff n x = 0 := by
  by_contra hne
  exact (not_lt_of_ge hx)
    (one_half_lt_radialNormSq_of_radialAnnularCutoff_ne_zero hne)

/-- The fixed annular cutoff is smooth. -/
theorem radialAnnularCutoff_contDiff (n : ℕ) : ContDiff ℝ 6 (radialAnnularCutoff n) := by
  unfold radialAnnularCutoff
  apply (rescaledUnitBump_contDiff (fun _ : Fin 1 ↦ (1 : ℝ)) (1 / 4)).comp
  apply contDiff_pi.mpr
  intro i
  unfold radialNormSq
  fun_prop

/-- Radial projection is smooth at every nonzero-radius point. -/
theorem radialDirection_contDiffAt {n : ℕ} {x : Fin n → ℝ}
    (hx : 0 < radialNormSq x) : ContDiffAt ℝ 6 radialDirection x := by
  have hq : ContDiffAt ℝ 6 (radialNormSq : (Fin n → ℝ) → ℝ) x :=
    (radialNormSq_contDiff 6).contDiffAt
  have hsqrt : ContDiffAt ℝ 6 (fun y ↦ Real.sqrt (radialNormSq y)) x :=
    hq.sqrt hx.ne'
  have hinv :
      ContDiffAt ℝ 6 (fun y ↦ (Real.sqrt (radialNormSq y))⁻¹) x :=
    hsqrt.inv (Real.sqrt_ne_zero'.mpr hx)
  exact hinv.smul contDiffAt_id

/-- The concrete annular extension is globally C6: away from the origin it is an ordinary smooth
composition, while near the origin the annular cutoff makes it identically zero. -/
theorem compactRadialExtension_contDiff {n : ℕ} (F : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ 6 (compactRadialExtension F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  rcases (radialNormSq_nonneg x).eq_or_lt with hzero | hpos
  · have hnhds :
        {y : Fin n → ℝ | radialNormSq y < 1 / 2} ∈ 𝓝 x := by
      apply (isOpen_lt (radialNormSq_contDiff 6).continuous continuous_const).mem_nhds
      change radialNormSq x < 1 / 2
      rw [← hzero]
      norm_num
    have heq :
        compactRadialExtension F =ᶠ[𝓝 x] (fun _ : Fin n → ℝ ↦ (0 : ℝ)) := by
      filter_upwards [hnhds] with y hy
      simp [compactRadialExtension, radialAnnularCutoff_eq_zero_of_le_half hy.le]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hcut : ContDiffAt ℝ 6 (radialAnnularCutoff n) x :=
      (radialAnnularCutoff_contDiff n).contDiffAt
    have heval :
        ContDiffAt ℝ 6 (fun y ↦ MvPolynomial.eval (radialDirection y) F) x :=
      (mvPolynomial_eval_contDiff F 6).contDiffAt.comp x
        (radialDirection_contDiffAt hpos)
    exact (hcut.pow 2).mul heval

/-- The fixed annular cutoff has compact topological support. -/
theorem radialAnnularCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (radialAnnularCutoff n) := by
  have hsupport :
      Function.support (radialAnnularCutoff n) ⊆
        Metric.closedBall (0 : Fin n → ℝ) 2 := by
    intro x hx
    have hq := radialNormSq_lt_three_halves_of_radialAnnularCutoff_ne_zero hx
    rw [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    intro i
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg (x i)) (by norm_num : (0 : ℝ) ≤ 2)).mp
    have hterm : x i ^ 2 ≤ radialNormSq x := by
      unfold radialNormSq
      exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
    rw [sq_abs]
    nlinarith
  exact (isCompact_closedBall (0 : Fin n → ℝ) 2).of_isClosed_subset isClosed_closure
    (closure_minimal hsupport Metric.isClosed_closedBall)

/-- The concrete radial extension has compact topological support. -/
theorem compactRadialExtension_hasCompactSupport {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) : HasCompactSupport (compactRadialExtension F) := by
  have hcut : HasCompactSupport (fun x ↦ radialAnnularCutoff n x ^ 2) := by
    have hbase := radialAnnularCutoff_hasCompactSupport n
    rw [hasCompactSupport_iff_eventuallyEq] at hbase ⊢
    exact hbase.mono fun x hx ↦ by simp [hx]
  exact hcut.mul_right

/-- In each fixed dimension, the squared annular cutoff and all derivatives through order six
have one common finite bound. -/
theorem radialAnnularCutoffSquare_uniform_deriv_bound (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ j, j ≤ 6 → ∀ x,
      ‖iteratedFDeriv ℝ j
        (fun y : Fin n → ℝ ↦ radialAnnularCutoff n y ^ 2) x‖ ≤ A := by
  let cutoffSquare : (Fin n → ℝ) → ℝ := fun y ↦ radialAnnularCutoff n y ^ 2
  have hsmooth : ContDiff ℝ 6 cutoffSquare := (radialAnnularCutoff_contDiff n).pow 2
  have hcompact : HasCompactSupport cutoffSquare := by
    dsimp [cutoffSquare]
    have hbase := radialAnnularCutoff_hasCompactSupport n
    rw [hasCompactSupport_iff_eventuallyEq] at hbase ⊢
    exact hbase.mono fun x hx ↦ by simp [hx]
  let J := {j : ℕ // j ≤ 6}
  letI : Fintype J := Fintype.ofFinite J
  have hbound : ∀ j : J, ∃ M : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ j.1 cutoffSquare x‖ ≤ M := by
    intro j
    have hbdd : BddAbove (Set.range fun x ↦
        ‖iteratedFDeriv ℝ j.1 cutoffSquare x‖) := by
      apply (hsmooth.continuous_iteratedFDeriv
        (by exact_mod_cast j.2)).norm.bddAbove_range_of_hasCompactSupport
      apply HasCompactSupport.comp_left _ norm_zero
      exact hcompact.iteratedFDeriv j.1
    rcases hbdd with ⟨M, hM⟩
    exact ⟨M, fun x ↦ hM (Set.mem_range_self x)⟩
  choose M hM using hbound
  let A := max (((Finset.univ : Finset J).image M).max'
    (by exact ⟨M ⟨0, by omega⟩, Finset.mem_image_of_mem M (Finset.mem_univ _)⟩)) 1
  refine ⟨A, le_max_right _ _, ?_⟩
  intro j hj x
  let j' : J := ⟨j, hj⟩
  change ‖iteratedFDeriv ℝ j'.1 cutoffSquare x‖ ≤ A
  exact (hM j' x).trans <| (Finset.le_max'
    ((Finset.univ : Finset J).image M) (M j')
      (Finset.mem_image_of_mem M (Finset.mem_univ j'))).trans (le_max_left _ _)

/-- Above the outer edge of the annulus, the cutoff vanishes. -/
theorem radialAnnularCutoff_eq_zero_of_three_halves_le {n : ℕ} {x : Fin n → ℝ}
    (hx : 3 / 2 ≤ radialNormSq x) : radialAnnularCutoff n x = 0 := by
  by_contra hne
  exact (not_lt_of_ge hx)
    (radialNormSq_lt_three_halves_of_radialAnnularCutoff_ne_zero hne)

/-- The radial extension vanishes on a neighborhood of every point well inside the inner edge. -/
theorem compactRadialExtension_eventuallyEq_zero_of_radialNormSq_lt_half
    {n : ℕ} (F : MvPolynomial (Fin n) ℝ) {x : Fin n → ℝ}
    (hx : radialNormSq x < 1 / 2) :
    compactRadialExtension F =ᶠ[𝓝 x] (fun _ : Fin n → ℝ ↦ (0 : ℝ)) := by
  have hnhds : {y : Fin n → ℝ | radialNormSq y < 1 / 2} ∈ 𝓝 x :=
    (isOpen_lt (radialNormSq_contDiff 6).continuous continuous_const).mem_nhds hx
  filter_upwards [hnhds] with y hy
  simp [compactRadialExtension, radialAnnularCutoff_eq_zero_of_le_half hy.le]

/-- The radial extension vanishes on a neighborhood of every point well outside the annulus. -/
theorem compactRadialExtension_eventuallyEq_zero_of_three_halves_lt_radialNormSq
    {n : ℕ} (F : MvPolynomial (Fin n) ℝ) {x : Fin n → ℝ}
    (hx : 3 / 2 < radialNormSq x) :
    compactRadialExtension F =ᶠ[𝓝 x] (fun _ : Fin n → ℝ ↦ (0 : ℝ)) := by
  have hnhds : {y : Fin n → ℝ | 3 / 2 < radialNormSq y} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (radialNormSq_contDiff 6).continuous).mem_nhds hx
  filter_upwards [hnhds] with y hy
  simp [compactRadialExtension, radialAnnularCutoff_eq_zero_of_three_halves_le hy.le]

/-- Sphere nonnegativity is preserved by the concrete squared-cutoff radial extension. -/
theorem compactRadialExtension_nonnegative {n : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (hF : SphereNonnegative F) (x : Fin n → ℝ) :
    0 ≤ compactRadialExtension F x := by
  by_cases hcut : radialAnnularCutoff n x = 0
  · simp [compactRadialExtension, hcut]
  · exact mul_nonneg (sq_nonneg _) <|
      hF (radialDirection x) (radialDirection_mem_sphere
        (radialNormSq_pos_of_radialAnnularCutoff_ne_zero hcut))

/-- The compact radial extension is exactly the original representative on the sphere. -/
theorem compactRadialExtension_eq_on_sphere {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    {x : Fin n → ℝ} (hx : x ∈ sphereSet n) :
    compactRadialExtension F x = MvPolynomial.eval x F := by
  simp [compactRadialExtension, radialAnnularCutoff_eq_one_of_mem_sphere hx,
    radialDirection_eq_self_of_mem_sphere hx]

/-- One prescribed rotation derivative is one of the nonnegative summands in the next
rotational norm. -/
theorem sphereRotNorm_rotationDeriv_le_succ {n : ℕ} (hn : 0 < n) (k : ℕ)
    (F : MvPolynomial (Fin n) ℝ) (i j : Fin n) :
    sphereRotNorm k (rotationDeriv i j F) ≤ sphereRotNorm (k + 1) F := by
  rw [sphereRotNorm]
  calc
    sphereRotNorm k (rotationDeriv i j F) ≤
        ∑ b : Fin n, sphereRotNorm k (rotationDeriv i b F) :=
      Finset.single_le_sum
        (fun b _ ↦ sphereRotNorm_nonneg hn k (rotationDeriv i b F))
        (Finset.mem_univ j)
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, sphereRotNorm k (rotationDeriv a b F) :=
      Finset.single_le_sum
        (fun a _ ↦ Finset.sum_nonneg fun b _ ↦
          sphereRotNorm_nonneg hn k (rotationDeriv a b F))
        (Finset.mem_univ i)
    _ ≤ sphereRotNorm k F +
          ∑ a : Fin n, ∑ b : Fin n, sphereRotNorm k (rotationDeriv a b F) :=
      le_add_of_nonneg_left (sphereRotNorm_nonneg hn k F)

/-- The C6 sphere norm controls the value of every first rotation derivative on the sphere. -/
theorem abs_eval_rotationDeriv_le_sphereC6Norm {n : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ) (i j : Fin n) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) :
    |MvPolynomial.eval x (rotationDeriv i j F)| ≤ sphereC6Norm F := by
  calc
    |MvPolynomial.eval x (rotationDeriv i j F)| ≤
        sphereSupNorm (rotationDeriv i j F) := sphereSupNorm_eval_le _ x hx
    _ ≤ sphereRotNorm 5 (rotationDeriv i j F) :=
      sphereSupNorm_le_sphereRotNorm hn 5 _
    _ ≤ sphereRotNorm 6 F := by
      simpa using sphereRotNorm_rotationDeriv_le_succ hn 5 F i j
    _ = sphereC6Norm F := rfl


/-- Zeroth-order ambient control is already a direct consequence of the sphere supremum term in
the rotational C6 norm; only positive derivative orders remain in the analytic comparison leaf. -/
theorem norm_compactRadialExtension_le_sphereC6Norm {n : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    ‖compactRadialExtension F x‖ ≤ sphereC6Norm F := by
  by_cases hcut : radialAnnularCutoff n x = 0
  · simp [compactRadialExtension, hcut, sphereC6Norm_nonneg hn F]
  · have hdir := radialDirection_mem_sphere
      (radialNormSq_pos_of_radialAnnularCutoff_ne_zero hcut)
    have hcutBounds :
        0 ≤ radialAnnularCutoff n x ∧ radialAnnularCutoff n x ≤ 1 :=
      rescaledUnitBump_mem_Icc (fun _ : Fin 1 ↦ (1 : ℝ)) (1 / 4)
        (fun _ : Fin 1 ↦ radialNormSq x)
    rw [compactRadialExtension, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg (radialAnnularCutoff n x))]
    calc
      radialAnnularCutoff n x ^ 2 * |MvPolynomial.eval (radialDirection x) F| ≤
          1 * |MvPolynomial.eval (radialDirection x) F| := by
            gcongr
            nlinarith [sq_nonneg (radialAnnularCutoff n x - 1)]
      _ ≤ sphereSupNorm F := by
        simpa using sphereSupNorm_eval_le F (radialDirection x) hdir
      _ ≤ sphereC6Norm F := sphereSupNorm_le_sphereRotNorm hn 6 F

/-- A Euclidean atom family for an extension whose restriction is the target polynomial, together
with precisely the sphere geometry required by `toSphereAtomFamily`. -/
structure RadialEuclideanAtomRealization {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (C : ℝ) (B : ℕ) where
  function : (Fin n → ℝ) → ℝ
  dilation : ℝ
  radiusCap : ℝ
  atoms : EuclideanAtomFamily function dilation radiusCap C B
  geometry : EuclideanAtomSphereGeometry atoms
  restricts_to_polynomial : ∀ x, x ∈ sphereSet n →
    function x = MvPolynomial.eval x F

/-- Uniform compact-radial realizations of all normalized sphere-nonnegative polynomials. -/
def HasUniformRadialEuclideanAtomRealization (n : ℕ) : Prop :=
  ∃ C : ℝ, ∃ B : ℕ, 0 < C ∧ 0 < B ∧
    ∀ F : MvPolynomial (Fin n) ℝ, SphereNonnegative F → sphereC6Norm F ≤ 1 →
      Nonempty (RadialEuclideanAtomRealization F C B)



/-- The coordinate-gradient continuous linear map for multivariate polynomial evaluation. -/
def mvPolynomialEvalFDeriv {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i F)) •
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

/-- Fréchet differentiation of multivariate evaluation is the expected pderivative gradient. -/
theorem hasFDerivAt_mvPolynomial_eval {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ ↦ MvPolynomial.eval y F)
      (mvPolynomialEvalFDeriv F x) x := by
  induction F using MvPolynomial.induction_on with
  | C a =>
      simpa [mvPolynomialEvalFDeriv] using
        (hasFDerivAt_const a x : HasFDerivAt (fun _ : Fin n → ℝ ↦ a) 0 x)
  | add p q hp hq =>
      convert hp.add hq using 1
      · funext y
        simp
      · ext v
        simp [mvPolynomialEvalFDeriv, map_add, add_smul, Finset.sum_add_distrib]
  | mul_X p i hp =>
      have hi : HasFDerivAt (fun y : Fin n → ℝ ↦ y i)
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) x :=
        hasFDerivAt_apply (𝕜 := ℝ) i x
      convert hp.mul hi using 1
      · funext y
        simp
      · ext v
        simp only [mvPolynomialEvalFDeriv, Derivation.leibniz, pderiv_X, Pi.single_apply,
          smul_eq_mul, mul_ite, mul_one, mul_zero, map_add, map_mul, eval_X,
          FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
          Pi.smul_apply, ContinuousLinearMap.proj_apply, add_mul, Finset.sum_add_distrib,
          add_apply, Finset.mul_sum]
        rw [Finset.sum_eq_single i]
        · simp [mul_assoc]
        · intro b hb hbi
          simp [Ne.symm hbi]
        · simp

/-- The derivative of the sphere quadratic is twice the Euclidean dot product. -/
theorem mvPolynomialEvalFDeriv_sphereQuadratic_apply {n : ℕ}
    (x v : Fin n → ℝ) :
    mvPolynomialEvalFDeriv (sphereQuadratic n) x v = 2 * ∑ i, x i * v i := by
  simp only [mvPolynomialEvalFDeriv, sphereQuadratic, map_sum, Derivation.leibniz_pow,
    Nat.add_one_sub_one, pow_one, pderiv_X, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, smul_ite, nsmul_eq_mul, Nat.cast_ofNat,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, map_mul, eval_ofNat, eval_X,
    FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
    Pi.smul_apply, ContinuousLinearMap.proj_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The differential of radial projection is radial scaling followed by orthogonal tangent
projection, written in coordinates for the product-space model used by the repository. -/
theorem fderiv_radialDirection_apply {n : ℕ} {x : Fin n → ℝ}
    (hx : 0 < radialNormSq x) (v : Fin n → ℝ) :
    fderiv ℝ radialDirection x v =
      (Real.sqrt (radialNormSq x))⁻¹ • v -
        ((Real.sqrt (radialNormSq x) ^ 3)⁻¹ * (∑ i, x i * v i)) • x := by
  have hq : HasFDerivAt radialNormSq
      (mvPolynomialEvalFDeriv (sphereQuadratic n) x) x := by
    convert hasFDerivAt_mvPolynomial_eval (sphereQuadratic n) x using 1
    funext y
    simp [radialNormSq, sphereQuadratic, pow_two]
  have hsqrt := hq.sqrt hx.ne'
  have hsqrt_ne : Real.sqrt (radialNormSq x) ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  have hinv := (hasFDerivAt_inv hsqrt_ne).comp x hsqrt
  have hradial := hinv.smul (hasFDerivAt_id x)
  have hfun :
      (((fun z : ℝ ↦ z⁻¹) ∘ fun y : Fin n → ℝ ↦ Real.sqrt (radialNormSq y)) •
        (id : (Fin n → ℝ) → (Fin n → ℝ))) = radialDirection := by
    funext y
    rfl
  rw [hfun] at hradial
  rw [hradial.fderiv]
  ext i
  simp only [Function.comp_apply, one_div, mul_inv_rev, ContinuousLinearMap.comp_smulₛₗ,
    RingHom.id_apply, id_eq, add_apply, FunLike.coe_smul,
    ContinuousLinearMap.coe_id', Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_comp, mvPolynomialEvalFDeriv_sphereQuadratic_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_neg, neg_smul,
    Pi.add_apply, Pi.neg_apply, Pi.sub_apply]
  rw [Real.sq_sqrt hx.le]
  field_simp
  rw [Real.sq_sqrt hx.le]
  ring

/-- Equivalent tangent-projection form of the radial projection differential. -/
theorem fderiv_radialDirection_eq_scaled_tangent {n : ℕ} {x : Fin n → ℝ}
    (hx : 0 < radialNormSq x) (v : Fin n → ℝ) :
    fderiv ℝ radialDirection x v =
      (Real.sqrt (radialNormSq x))⁻¹ •
        (v - (∑ i, radialDirection x i * v i) • radialDirection x) := by
  rw [fderiv_radialDirection_apply hx]
  have hsqrt_ne : Real.sqrt (radialNormSq x) ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, radialDirection]
  field_simp [hsqrt_ne]
  have hdiv :
      Real.sqrt (radialNormSq x) *
          (x i * (∑ k, x k * v k / Real.sqrt (radialNormSq x))) =
        (∑ k, x k * v k) * x i := by
    rw [← Finset.sum_div]
    field_simp [hsqrt_ne]
  have hfirst :
      Real.sqrt (radialNormSq x) *
          (Real.sqrt (radialNormSq x) * v i) = radialNormSq x * v i := by
    calc
      _ = Real.sqrt (radialNormSq x) ^ 2 * v i := by ring
      _ = _ := by rw [Real.sq_sqrt hx.le]
  rw [mul_sub, hdiv, hfirst, Real.sq_sqrt hx.le]


/-- Evaluating a coordinate rotation derivative gives the corresponding skew-gradient
component. -/
theorem eval_rotationDeriv_eq {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (y : Fin n → ℝ) (i j : Fin n) :
    MvPolynomial.eval y (rotationDeriv i j F) =
      y i * MvPolynomial.eval y (MvPolynomial.pderiv j F) -
        y j * MvPolynomial.eval y (MvPolynomial.pderiv i F) := by
  simp [rotationDeriv]

/-- On the sphere, the tangential gradient is reconstructed from the coordinate rotation
fields. -/
theorem mvPolynomialEvalFDeriv_tangent_eq_rotation_sum {n : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (y v : Fin n → ℝ) (hy : y ∈ sphereSet n) :
    mvPolynomialEvalFDeriv F y (v - (∑ k, y k * v k) • y) =
      ∑ i, ∑ j, v i * y j * MvPolynomial.eval y (rotationDeriv j i F) := by
  let d : Fin n → ℝ := fun i ↦ MvPolynomial.eval y (MvPolynomial.pderiv i F)
  let dot : ℝ := ∑ k, y k * v k
  have hyq : ∑ j, y j ^ 2 = 1 := radialNormSq_eq_one_of_mem_sphere hy
  have hleft :
      mvPolynomialEvalFDeriv F y (v - dot • y) =
        (∑ i, d i * v i) - dot * ∑ i, d i * y i := by
    simp only [mvPolynomialEvalFDeriv, FunLike.coe_sum,
      FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply,
      ContinuousLinearMap.proj_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum, dot, d]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hfirst :
      (∑ i, ∑ j, v i * y j ^ 2 * d i) =
        (∑ i, d i * v i) * ∑ j, y j ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hsecond :
      (∑ i, ∑ j, (v i * y i) * (y j * d j)) =
        (∑ i, v i * y i) * ∑ j, y j * d j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hdot : (∑ i, v i * y i) = dot := by
    dsimp [dot]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdy : (∑ j, y j * d j) = ∑ j, d j * y j := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [show (∑ k, y k * v k) = dot by rfl, hleft]
  simp_rw [eval_rotationDeriv_eq, show ∀ i, MvPolynomial.eval y
    (MvPolynomial.pderiv i F) = d i by intro i; rfl]
  symm
  calc
    (∑ i, ∑ j, v i * y j * (y j * d i - y i * d j)) =
        (∑ i, ∑ j, v i * y j ^ 2 * d i) -
          ∑ i, ∑ j, (v i * y i) * (y j * d j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i, d i * v i) * (∑ j, y j ^ 2) -
          (∑ i, v i * y i) * (∑ j, y j * d j) := by rw [hfirst, hsecond]
    _ = (∑ i, d i * v i) - dot * ∑ i, d i * y i := by
      rw [hyq, hdot, hdy]
      ring

/-- The first derivative of radial pullback is an explicitly scaled finite combination of
coordinate-rotation derivatives. -/
theorem fderiv_radialPullback_apply {n : ℕ} {x : Fin n → ℝ}
    (hx : 0 < radialNormSq x) (F : MvPolynomial (Fin n) ℝ) (v : Fin n → ℝ) :
    fderiv ℝ (fun y ↦ MvPolynomial.eval (radialDirection y) F) x v =
      (Real.sqrt (radialNormSq x))⁻¹ *
        ∑ i, ∑ j, v i * radialDirection x j *
          MvPolynomial.eval (radialDirection x) (rotationDeriv j i F) := by
  change fderiv ℝ ((fun y : Fin n → ℝ ↦ MvPolynomial.eval y F) ∘ radialDirection) x v = _
  rw [fderiv_comp x
    (hasFDerivAt_mvPolynomial_eval F (radialDirection x)).differentiableAt
    ((radialDirection_contDiffAt hx).differentiableAt (by norm_num))]
  rw [(hasFDerivAt_mvPolynomial_eval F (radialDirection x)).fderiv]
  rw [ContinuousLinearMap.comp_apply, fderiv_radialDirection_eq_scaled_tangent hx, map_smul]
  rw [mvPolynomialEvalFDeriv_tangent_eq_rotation_sum F _ _
    (radialDirection_mem_sphere hx)]
  rfl

/-- Scalar coefficients of the coordinate tangent frame used by radial pullback. -/
def radialTangentCoefficient {n : ℕ} (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  (Real.sqrt (radialNormSq x))⁻¹ * radialDirection x j

/-- Operator-valued finite expansion of the first radial-pullback derivative. -/
def radialPullbackFirstExpansion {n : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, ∑ j,
    (radialTangentCoefficient j x *
      MvPolynomial.eval (radialDirection x) (rotationDeriv j i F)) •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

/-- The operator expansion agrees with the actual derivative at every positive-radius point. -/
theorem fderiv_radialPullback_eq_firstExpansion {n : ℕ} {x : Fin n → ℝ}
    (hx : 0 < radialNormSq x) (F : MvPolynomial (Fin n) ℝ) :
    fderiv ℝ (fun y ↦ MvPolynomial.eval (radialDirection y) F) x =
      radialPullbackFirstExpansion F x := by
  ext v
  rw [fderiv_radialPullback_apply hx F v]
  simp only [radialPullbackFirstExpansion, _root_.sum_apply,
    FunLike.coe_smul, radialTangentCoefficient]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

/-- Each tangent-frame coefficient is C6 at every positive-radius point. -/
theorem radialTangentCoefficient_contDiffAt {n : ℕ} (j : Fin n) {x : Fin n → ℝ}
    (hx : 0 < radialNormSq x) : ContDiffAt ℝ 6 (radialTangentCoefficient j) x := by
  have hq : ContDiffAt ℝ 6 (radialNormSq : (Fin n → ℝ) → ℝ) x :=
    (radialNormSq_contDiff 6).contDiffAt
  have hinv : ContDiffAt ℝ 6 (fun y : Fin n → ℝ ↦
      (Real.sqrt (radialNormSq y))⁻¹) x :=
    (hq.sqrt hx.ne').inv (Real.sqrt_ne_zero'.mpr hx)
  have hcoord : ContDiffAt ℝ 6 (fun y : Fin n → ℝ ↦ radialDirection y j) x :=
    (contDiffAt_apply ℝ ℝ j (radialDirection x)).comp x (radialDirection_contDiffAt hx)
  exact hinv.mul hcoord

/-- The closed buffered annulus used for all local coefficient bounds. -/
def radialClosedAnnulus (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (1 / 4 : ℝ) ≤ radialNormSq x ∧ radialNormSq x ≤ 2}

/-- The buffered radial annulus is compact in the repository product norm. -/
theorem radialClosedAnnulus_isCompact (n : ℕ) : IsCompact (radialClosedAnnulus n) := by
  have hclosed : IsClosed (radialClosedAnnulus n) := by
    exact (isClosed_le continuous_const (radialNormSq_contDiff 6).continuous).inter
      (isClosed_le (radialNormSq_contDiff 6).continuous continuous_const)
  have hsubset : radialClosedAnnulus n ⊆ Metric.closedBall (0 : Fin n → ℝ) 2 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    intro i
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg (x i)) (by norm_num : (0 : ℝ) ≤ 2)).mp
    have hterm : x i ^ 2 ≤ radialNormSq x := by
      unfold radialNormSq
      exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
    rw [sq_abs]
    nlinarith [hterm, hx.2]
  exact (isCompact_closedBall (0 : Fin n → ℝ) 2).of_isClosed_subset hclosed hsubset

-- Positive dimension is retained for consistency with the surrounding radial sphere estimates.
set_option linter.unusedVariables false in
/-- In fixed dimension, all tangent-frame coefficient derivatives through order five have one
uniform bound on the buffered annulus. This is the coefficient half of the higher-order radial
pullback induction. -/
theorem radialTangentCoefficient_uniform_deriv_bound {n : ℕ} (hn : 0 < n) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (j : Fin n) m, m ≤ 5 → ∀ x,
      x ∈ radialClosedAnnulus n →
        ‖iteratedFDeriv ℝ m (radialTangentCoefficient j) x‖ ≤ A := by
  let J := Fin n × {m : ℕ // m ≤ 5}
  letI : Fintype J := Fintype.ofFinite J
  have hbound : ∀ a : J, ∃ M : ℝ, ∀ x ∈ radialClosedAnnulus n,
      ‖iteratedFDeriv ℝ a.2.1 (radialTangentCoefficient a.1) x‖ ≤ M := by
    intro a
    have hcontinuous : ContinuousOn
        (iteratedFDeriv ℝ a.2.1 (radialTangentCoefficient a.1))
        (radialClosedAnnulus n) := by
      intro x hx
      have hxpos : 0 < radialNormSq x := by linarith [hx.1]
      exact ((radialTangentCoefficient_contDiffAt a.1 hxpos).continuousAt_iteratedFDeriv
        (by exact_mod_cast a.2.2.trans (by norm_num : 5 ≤ 6))).continuousWithinAt
    exact (radialClosedAnnulus_isCompact n).exists_bound_of_continuousOn hcontinuous
  choose M hM using hbound
  let A : ℝ := max (∑ a : J, max (M a) 0) 1
  refine ⟨A, le_max_right _ _, ?_⟩
  intro j m hm x hx
  let a : J := (j, ⟨m, hm⟩)
  have hMa : M a ≤ ∑ b : J, max (M b) 0 :=
    (le_max_left (M a) 0).trans <|
      Finset.single_le_sum (fun b _ ↦ le_max_right (M b) 0) (Finset.mem_univ a)
  exact (hM a x hx).trans (hMa.trans (le_max_left _ _))

/-- Every coordinate of a point on the algebraic unit sphere has absolute value at most one. -/
theorem abs_coord_le_one_of_mem_sphere {n : ℕ} {y : Fin n → ℝ}
    (hy : y ∈ sphereSet n) (i : Fin n) : |y i| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  have hterm : y i ^ 2 ≤ radialNormSq y := by
    unfold radialNormSq
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (y j)) (Finset.mem_univ i)
  simpa [radialNormSq_eq_one_of_mem_sphere hy] using hterm

/-- The finite rotation sum in the radial-pullback differential has the expected coarse
`n²` bound in the product sup norm. -/
theorem abs_rotation_sum_le_sphereC6Norm {n : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ) (y v : Fin n → ℝ) (hy : y ∈ sphereSet n) :
    |∑ i, ∑ j, v i * y j * MvPolynomial.eval y (rotationDeriv j i F)| ≤
      (n : ℝ) ^ 2 * ‖v‖ * sphereC6Norm F := by
  have hv (i : Fin n) : |v i| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hterm (i j : Fin n) :
      |v i * y j * MvPolynomial.eval y (rotationDeriv j i F)| ≤
        ‖v‖ * sphereC6Norm F := by
    rw [abs_mul, abs_mul]
    calc
      |v i| * |y j| * |MvPolynomial.eval y (rotationDeriv j i F)| ≤
          ‖v‖ * 1 * sphereC6Norm F := by
        gcongr
        · exact hv i
        · exact abs_coord_le_one_of_mem_sphere hy j
        · exact abs_eval_rotationDeriv_le_sphereC6Norm hn F j i y hy
      _ = ‖v‖ * sphereC6Norm F := by ring
  calc
    |∑ i, ∑ j, v i * y j * MvPolynomial.eval y (rotationDeriv j i F)| ≤
        ∑ i, |∑ j, v i * y j * MvPolynomial.eval y (rotationDeriv j i F)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j,
        |v i * y j * MvPolynomial.eval y (rotationDeriv j i F)| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖v‖ * sphereC6Norm F := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum fun j hj ↦ hterm i j
    _ = (n : ℝ) ^ 2 * ‖v‖ * sphereC6Norm F := by
      simp [nsmul_eq_mul]
      ring

/-- On the buffered annulus, the first ambient derivative of radial pullback is controlled
explicitly by the first rotation derivatives on the sphere. -/
theorem norm_fderiv_radialPullback_le_sphereC6Norm {n : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ) {x : Fin n → ℝ}
    (hx : 1 / 4 < radialNormSq x) :
    ‖fderiv ℝ (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
      (2 * (n : ℝ) ^ 2) * sphereC6Norm F := by
  have hxpos : 0 < radialNormSq x := by linarith
  have hsqrt_pos : 0 < Real.sqrt (radialNormSq x) := Real.sqrt_pos.2 hxpos
  have hsqrt_half : (1 / 2 : ℝ) < Real.sqrt (radialNormSq x) := by
    nlinarith [Real.sq_sqrt (radialNormSq_nonneg x)]
  have hinv : |(Real.sqrt (radialNormSq x))⁻¹| ≤ 2 := by
    rw [abs_of_pos (inv_pos.mpr hsqrt_pos)]
    exact (inv_le_iff_one_le_mul₀ hsqrt_pos).2 (by nlinarith)
  apply (fderiv ℝ (fun y ↦ MvPolynomial.eval (radialDirection y) F) x).opNorm_le_bound
    (mul_nonneg (by positivity) (sphereC6Norm_nonneg hn F))
  intro v
  rw [fderiv_radialPullback_apply hxpos F v, Real.norm_eq_abs, abs_mul]
  calc
    |(Real.sqrt (radialNormSq x))⁻¹| *
          |∑ i, ∑ j, v i * radialDirection x j *
            MvPolynomial.eval (radialDirection x) (rotationDeriv j i F)| ≤
        2 * ((n : ℝ) ^ 2 * ‖v‖ * sphereC6Norm F) := by
      gcongr
      exact abs_rotation_sum_le_sphereC6Norm hn F (radialDirection x) v
        (radialDirection_mem_sphere hxpos)
    _ = (2 * (n : ℝ) ^ 2 * sphereC6Norm F) * ‖v‖ := by ring

/-- Apply a finite word of infinitesimal coordinate rotations to a polynomial. -/
def iteratedRotationDeriv {n : ℕ} :
    List (Fin n × Fin n) → MvPolynomial (Fin n) ℝ → MvPolynomial (Fin n) ℝ
  | [], F => F
  | ij :: word, F => iteratedRotationDeriv word (rotationDeriv ij.1 ij.2 F)

/-- A rotation word of length m is one of the nonnegative contributions to the rotation norm
with m additional levels. -/
theorem sphereRotNorm_iteratedRotationDeriv_le_add {n : ℕ} (hn : 0 < n)
    (word : List (Fin n × Fin n)) (k : ℕ) (F : MvPolynomial (Fin n) ℝ) :
    sphereRotNorm k (iteratedRotationDeriv word F) ≤
      sphereRotNorm (k + word.length) F := by
  induction word generalizing F k with
  | nil => simp [iteratedRotationDeriv]
  | cons ij word ih =>
      rw [iteratedRotationDeriv, List.length_cons]
      calc
        sphereRotNorm k (iteratedRotationDeriv word (rotationDeriv ij.1 ij.2 F)) ≤
            sphereRotNorm (k + word.length) (rotationDeriv ij.1 ij.2 F) :=
          ih (k := k) (F := rotationDeriv ij.1 ij.2 F)
        _ ≤ sphereRotNorm (k + word.length + 1) F :=
          sphereRotNorm_rotationDeriv_le_succ hn (k + word.length) F ij.1 ij.2
        _ = sphereRotNorm (k + (word.length + 1)) F := by rw [Nat.add_assoc]

/-- Rotational norms are monotone in their word-length cutoff. -/
theorem sphereRotNorm_le_succ {n : ℕ} (hn : 0 < n) (k : ℕ)
    (F : MvPolynomial (Fin n) ℝ) : sphereRotNorm k F ≤ sphereRotNorm (k + 1) F := by
  rw [sphereRotNorm]
  exact le_add_of_nonneg_right <|
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      sphereRotNorm_nonneg hn k (rotationDeriv i j F)

/-- Monotonicity of rotational norms over any finite increase in word length. -/
theorem sphereRotNorm_mono {n : ℕ} (hn : 0 < n) {k ell : ℕ} (h : k ≤ ell)
    (F : MvPolynomial (Fin n) ℝ) : sphereRotNorm k F ≤ sphereRotNorm ell F := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
      exact (ih (by omega)).trans (sphereRotNorm_le_succ hn (k + d) F)

/-- Every rotation word of length at most six has pointwise sphere value bounded by the C6 norm. -/
theorem abs_eval_iteratedRotationDeriv_le_sphereC6Norm {n : ℕ} (hn : 0 < n)
    (word : List (Fin n × Fin n)) (hword : word.length ≤ 6)
    (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) (hx : x ∈ sphereSet n) :
    |MvPolynomial.eval x (iteratedRotationDeriv word F)| ≤ sphereC6Norm F := by
  calc
    |MvPolynomial.eval x (iteratedRotationDeriv word F)| ≤
        sphereSupNorm (iteratedRotationDeriv word F) := sphereSupNorm_eval_le _ x hx
    _ ≤ sphereRotNorm (6 - word.length) (iteratedRotationDeriv word F) :=
      sphereSupNorm_le_sphereRotNorm hn _ _
    _ ≤ sphereRotNorm (6 - word.length + word.length) F :=
      sphereRotNorm_iteratedRotationDeriv_le_add hn word (6 - word.length) F
    _ = sphereC6Norm F := by rw [Nat.sub_add_cancel hword]; rfl

/-- Two prescribed coordinate rotations are controlled pointwise by the C6 sphere norm. -/
theorem abs_eval_twoRotationDeriv_le_sphereC6Norm {n : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ) (a b i j : Fin n) (y : Fin n → ℝ)
    (hy : y ∈ sphereSet n) :
    |MvPolynomial.eval y (rotationDeriv a b (rotationDeriv i j F))| ≤ sphereC6Norm F := by
  simpa [iteratedRotationDeriv] using
    abs_eval_iteratedRotationDeriv_le_sphereC6Norm hn [(i, j), (a, b)] (by simp) F y hy

/-- The rotation sum occurring in the derivative of a once-rotated pullback only uses rotation
words of length two. -/
theorem abs_rotation_sum_rotationDeriv_le_sphereC6Norm {n : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ) (a b : Fin n)
    (y v : Fin n → ℝ) (hy : y ∈ sphereSet n) :
    |∑ i, ∑ j, v i * y j *
        MvPolynomial.eval y (rotationDeriv j i (rotationDeriv a b F))| ≤
      (n : ℝ) ^ 2 * ‖v‖ * sphereC6Norm F := by
  have hv (i : Fin n) : |v i| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hterm (i j : Fin n) :
      |v i * y j * MvPolynomial.eval y (rotationDeriv j i (rotationDeriv a b F))| ≤
        ‖v‖ * sphereC6Norm F := by
    rw [abs_mul, abs_mul]
    calc
      |v i| * |y j| *
          |MvPolynomial.eval y (rotationDeriv j i (rotationDeriv a b F))| ≤
          ‖v‖ * 1 * sphereC6Norm F := by
        gcongr
        · exact hv i
        · exact abs_coord_le_one_of_mem_sphere hy j
        · exact abs_eval_twoRotationDeriv_le_sphereC6Norm hn F j i a b y hy
      _ = ‖v‖ * sphereC6Norm F := by ring
  calc
    |∑ i, ∑ j, v i * y j *
        MvPolynomial.eval y (rotationDeriv j i (rotationDeriv a b F))| ≤
        ∑ i, |∑ j, v i * y j *
          MvPolynomial.eval y (rotationDeriv j i (rotationDeriv a b F))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j,
        |v i * y j * MvPolynomial.eval y
          (rotationDeriv j i (rotationDeriv a b F))| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖v‖ * sphereC6Norm F := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum fun j hj ↦ hterm i j
    _ = (n : ℝ) ^ 2 * ‖v‖ * sphereC6Norm F := by
      simp [nsmul_eq_mul]
      ring

/-- First derivatives of once-rotated pullbacks are controlled by length-two rotation words. -/
theorem norm_fderiv_radialPullback_rotationDeriv_le_sphereC6Norm {n : ℕ} (hn : 0 < n)
    (F : MvPolynomial (Fin n) ℝ) (a b : Fin n) {x : Fin n → ℝ}
    (hx : 1 / 4 < radialNormSq x) :
    ‖fderiv ℝ (fun y ↦ MvPolynomial.eval (radialDirection y) (rotationDeriv a b F)) x‖ ≤
      (2 * (n : ℝ) ^ 2) * sphereC6Norm F := by
  have hxpos : 0 < radialNormSq x := by linarith
  have hsqrt_pos : 0 < Real.sqrt (radialNormSq x) := Real.sqrt_pos.2 hxpos
  have hsqrt_half : (1 / 2 : ℝ) < Real.sqrt (radialNormSq x) := by
    nlinarith [Real.sq_sqrt (radialNormSq_nonneg x)]
  have hinv : |(Real.sqrt (radialNormSq x))⁻¹| ≤ 2 := by
    rw [abs_of_pos (inv_pos.mpr hsqrt_pos)]
    exact (inv_le_iff_one_le_mul₀ hsqrt_pos).2 (by nlinarith)
  apply (fderiv ℝ (fun y ↦ MvPolynomial.eval (radialDirection y)
    (rotationDeriv a b F)) x).opNorm_le_bound
      (mul_nonneg (by positivity) (sphereC6Norm_nonneg hn F))
  intro v
  rw [fderiv_radialPullback_apply hxpos (rotationDeriv a b F) v,
    Real.norm_eq_abs, abs_mul]
  calc
    |(Real.sqrt (radialNormSq x))⁻¹| *
          |∑ i, ∑ j, v i * radialDirection x j *
            MvPolynomial.eval (radialDirection x)
              (rotationDeriv j i (rotationDeriv a b F))| ≤
        2 * ((n : ℝ) ^ 2 * ‖v‖ * sphereC6Norm F) := by
      gcongr
      exact abs_rotation_sum_rotationDeriv_le_sphereC6Norm hn F a b
        (radialDirection x) v (radialDirection_mem_sphere hxpos)
    _ = (2 * (n : ℝ) ^ 2 * sphereC6Norm F) * ‖v‖ := by ring

/-- One derivative of a tangent coefficient times a once-rotated pullback is uniformly
controlled on the buffered annulus. -/
theorem norm_iteratedFDeriv_one_tangentCoefficient_mul_rotationPullback
    {n : ℕ} (hn : 0 < n) {A : ℝ}
    (hA : ∀ (j : Fin n) m, m ≤ 5 → ∀ x, x ∈ radialClosedAnnulus n →
      ‖iteratedFDeriv ℝ m (radialTangentCoefficient j) x‖ ≤ A)
    (F : MvPolynomial (Fin n) ℝ) (a b j : Fin n) {x : Fin n → ℝ}
    (hxinner : 1 / 4 < radialNormSq x) (hxouter : radialNormSq x < 2) :
    ‖iteratedFDeriv ℝ 1 (fun y ↦ radialTangentCoefficient j y *
      MvPolynomial.eval (radialDirection y) (rotationDeriv a b F)) x‖ ≤
      2 * A * max 1 (2 * (n : ℝ) ^ 2) * sphereC6Norm F := by
  let pullback : (Fin n → ℝ) → ℝ := fun y ↦
    MvPolynomial.eval (radialDirection y) (rotationDeriv a b F)
  let K1 : ℝ := 2 * (n : ℝ) ^ 2
  let Kp : ℝ := max 1 K1
  have hxpos : 0 < radialNormSq x := by linarith
  have hxann : x ∈ radialClosedAnnulus n := ⟨hxinner.le, hxouter.le⟩
  have hC : 0 ≤ sphereC6Norm F := sphereC6Norm_nonneg hn F
  have hK1 : 0 ≤ K1 := by dsimp [K1]; positivity
  have hKp : 1 ≤ Kp := le_max_left _ _
  have hc0 : ‖radialTangentCoefficient j x‖ ≤ A := by
    simpa using hA j 0 (by norm_num) x hxann
  have hc1 : ‖fderiv ℝ (radialTangentCoefficient j) x‖ ≤ A := by
    simpa [norm_iteratedFDeriv_one] using hA j 1 (by norm_num) x hxann
  have hAnonneg : 0 ≤ A := (norm_nonneg _).trans hc0
  have hp0 : ‖pullback x‖ ≤ Kp * sphereC6Norm F := by
    dsimp [pullback]
    calc
      |MvPolynomial.eval (radialDirection x) (rotationDeriv a b F)| ≤
          sphereC6Norm F :=
        abs_eval_rotationDeriv_le_sphereC6Norm hn F a b (radialDirection x)
          (radialDirection_mem_sphere hxpos)
      _ = 1 * sphereC6Norm F := by ring
      _ ≤ Kp * sphereC6Norm F := mul_le_mul_of_nonneg_right hKp hC
  have hp1 : ‖fderiv ℝ pullback x‖ ≤ Kp * sphereC6Norm F := by
    calc
      ‖fderiv ℝ pullback x‖ ≤ K1 * sphereC6Norm F := by
        exact norm_fderiv_radialPullback_rotationDeriv_le_sphereC6Norm hn F a b hxinner
      _ ≤ Kp * sphereC6Norm F :=
        mul_le_mul_of_nonneg_right (le_max_right 1 K1) hC
  have hcoeffDiff : ContDiffAt ℝ 6 (radialTangentCoefficient j) x :=
    radialTangentCoefficient_contDiffAt j hxpos
  have hpullDiff : ContDiffAt ℝ 6 pullback x := by
    exact (mvPolynomial_eval_contDiff (rotationDeriv a b F) 6).contDiffAt.comp x
      (radialDirection_contDiffAt hxpos)
  have hbase := norm_iteratedFDeriv_mul_le_of_contDiffAt
    hcoeffDiff hpullDiff (n := 1) (by norm_num)
  have hbase' :
      ‖iteratedFDeriv ℝ 1 (fun y ↦ radialTangentCoefficient j y * pullback y) x‖ ≤
        ‖radialTangentCoefficient j x‖ * ‖fderiv ℝ pullback x‖ +
          ‖fderiv ℝ (radialTangentCoefficient j) x‖ * ‖pullback x‖ := by
    simpa [Finset.sum_range_succ, norm_iteratedFDeriv_zero,
      norm_iteratedFDeriv_one, add_comm] using hbase
  change ‖iteratedFDeriv ℝ 1
    (fun y ↦ radialTangentCoefficient j y * pullback y) x‖ ≤ _
  calc
    ‖iteratedFDeriv ℝ 1
        (fun y ↦ radialTangentCoefficient j y * pullback y) x‖ ≤
        ‖radialTangentCoefficient j x‖ * ‖fderiv ℝ pullback x‖ +
          ‖fderiv ℝ (radialTangentCoefficient j) x‖ * ‖pullback x‖ := hbase'
    _ ≤ A * (Kp * sphereC6Norm F) + A * (Kp * sphereC6Norm F) := by
      gcongr
    _ = 2 * A * Kp * sphereC6Norm F := by ring

/-- Local finite sums commute with iterated Fréchet derivatives under pointwise Ck
hypotheses. -/
theorem iteratedFDeriv_finset_sum_apply_of_contDiffAt
    {n m : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {ι : Type*} {u : Finset ι} {f : ι → (Fin n → ℝ) → G} {x : Fin n → ℝ}
    (h : ∀ i ∈ u, ContDiffAt ℝ m (f i) x) :
    iteratedFDeriv ℝ m (fun y ↦ ∑ i ∈ u, f i y) x =
      ∑ i ∈ u, iteratedFDeriv ℝ m (f i) x := by
  simp_rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_fun_sum_apply uniqueDiffOn_univ (Set.mem_univ x)
    (fun i hi ↦ (h i hi).contDiffWithinAt)

/-- Coordinate projection has operator norm at most one for the product sup norm. -/
theorem norm_continuousLinearMap_proj_le_one {n : ℕ} (i : Fin n) :
    ‖(ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm v i

/-- Scalar multiplication by a fixed coordinate projection does not enlarge a first derivative. -/
theorem norm_iteratedFDeriv_one_smul_proj_le {n : ℕ} (i : Fin n)
    {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : ContDiffAt ℝ 6 f x) :
    ‖iteratedFDeriv ℝ 1 (fun y ↦ f y •
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x‖ ≤
      ‖iteratedFDeriv ℝ 1 f x‖ := by
  let L : ℝ →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toSpanSingleton ℝ
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)
  have hL : ‖L‖ ≤ 1 := by
    simpa [L] using norm_continuousLinearMap_proj_le_one i
  change ‖iteratedFDeriv ℝ 1 (L ∘ f) x‖ ≤ _
  calc
    ‖iteratedFDeriv ℝ 1 (L ∘ f) x‖ ≤
        ‖L‖ * ‖iteratedFDeriv ℝ 1 f x‖ :=
      L.norm_iteratedFDeriv_comp_left hf (by norm_num)
    _ ≤ 1 * ‖iteratedFDeriv ℝ 1 f x‖ :=
      mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = _ := one_mul _

/-- The second ambient derivative of radial pullback is completely controlled by the compact
coefficient bounds and rotation words of length at most two. -/
theorem exists_norm_iteratedFDeriv_two_radialPullback_le_sphereC6Norm
    {n : ℕ} (hn : 0 < n) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ),
      1 / 4 < radialNormSq x → radialNormSq x < 2 →
        ‖iteratedFDeriv ℝ 2
          (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
          K * sphereC6Norm F := by
  obtain ⟨A, hAone, hA⟩ := radialTangentCoefficient_uniform_deriv_bound hn
  let Kp : ℝ := max 1 (2 * (n : ℝ) ^ 2)
  let B : ℝ := 2 * A * Kp
  let Kraw : ℝ := (n : ℝ) ^ 2 * B
  let K : ℝ := max 1 Kraw
  refine ⟨K, le_max_left _ _, ?_⟩
  intro F x hxinner hxouter
  have hxpos : 0 < radialNormSq x := by linarith
  have hC : 0 ≤ sphereC6Norm F := sphereC6Norm_nonneg hn F
  let scalar : Fin n → Fin n → (Fin n → ℝ) → ℝ := fun i j y ↦
    radialTangentCoefficient j y *
      MvPolynomial.eval (radialDirection y) (rotationDeriv j i F)
  let term : Fin n → Fin n → (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) :=
    fun i j y ↦ scalar i j y •
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)
  have hscalarDiff (i j : Fin n) : ContDiffAt ℝ 6 (scalar i j) x := by
    exact (radialTangentCoefficient_contDiffAt j hxpos).mul <|
      (mvPolynomial_eval_contDiff (rotationDeriv j i F) 6).contDiffAt.comp x
        (radialDirection_contDiffAt hxpos)
  have htermDiff (i j : Fin n) : ContDiffAt ℝ 1 (term i j) x := by
    exact ((hscalarDiff i j).smul contDiffAt_const).of_le (by norm_num)
  have hinnerDiff (i : Fin n) : ContDiffAt ℝ 1 (fun y ↦ ∑ j, term i j y) x := by
    exact ContDiffAt.sum fun j hj ↦ htermDiff i j
  have hexpand :
      iteratedFDeriv ℝ 1 (radialPullbackFirstExpansion F) x =
        ∑ i, ∑ j, iteratedFDeriv ℝ 1 (term i j) x := by
    have hfun : radialPullbackFirstExpansion F = fun y ↦ ∑ i, ∑ j, term i j y := by
      funext y
      rfl
    rw [hfun]
    calc
      iteratedFDeriv ℝ 1 (fun y ↦ ∑ i, ∑ j, term i j y) x =
          ∑ i, iteratedFDeriv ℝ 1 (fun y ↦ ∑ j, term i j y) x :=
        iteratedFDeriv_finset_sum_apply_of_contDiffAt
          (u := Finset.univ) (fun i hi ↦ hinnerDiff i)
      _ = ∑ i, ∑ j, iteratedFDeriv ℝ 1 (term i j) x := by
        apply Finset.sum_congr rfl
        intro i hi
        exact iteratedFDeriv_finset_sum_apply_of_contDiffAt
          (u := Finset.univ) (fun j hj ↦ htermDiff i j)
  have hpositiveNhd : {y : Fin n → ℝ | 0 < radialNormSq y} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (radialNormSq_contDiff 6).continuous).mem_nhds hxpos
  have heq :
      (fun y ↦ fderiv ℝ (fun z ↦ MvPolynomial.eval (radialDirection z) F) y) =ᶠ[𝓝 x]
        radialPullbackFirstExpansion F := by
    filter_upwards [hpositiveNhd] with y hy
    exact fderiv_radialPullback_eq_firstExpansion hy F
  have hderivEq :
      iteratedFDeriv ℝ 1
          (fun y ↦ fderiv ℝ (fun z ↦ MvPolynomial.eval (radialDirection z) F) y) x =
        iteratedFDeriv ℝ 1 (radialPullbackFirstExpansion F) x :=
    (heq.iteratedFDeriv ℝ 1).self_of_nhds
  have htermBound (i j : Fin n) :
      ‖iteratedFDeriv ℝ 1 (term i j) x‖ ≤ B * sphereC6Norm F := by
    calc
      ‖iteratedFDeriv ℝ 1 (term i j) x‖ ≤
          ‖iteratedFDeriv ℝ 1 (scalar i j) x‖ := by
        exact norm_iteratedFDeriv_one_smul_proj_le i (hscalarDiff i j)
      _ ≤ B * sphereC6Norm F := by
        exact norm_iteratedFDeriv_one_tangentCoefficient_mul_rotationPullback
          hn hA F j i j hxinner hxouter
  have hraw :
      ‖iteratedFDeriv ℝ 2
        (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
        Kraw * sphereC6Norm F := by
    calc
      ‖iteratedFDeriv ℝ 2
          (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ =
          ‖iteratedFDeriv ℝ 1
            (fun y ↦ fderiv ℝ
              (fun z ↦ MvPolynomial.eval (radialDirection z) F) y) x‖ := by
        symm
        exact norm_iteratedFDeriv_fderiv
      _ = ‖iteratedFDeriv ℝ 1 (radialPullbackFirstExpansion F) x‖ :=
        congrArg norm hderivEq
      _ = ‖∑ i, ∑ j, iteratedFDeriv ℝ 1 (term i j) x‖ :=
        congrArg norm hexpand
      _ ≤ ∑ i, ‖∑ j, iteratedFDeriv ℝ 1 (term i j) x‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖iteratedFDeriv ℝ 1 (term i j) x‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, B * sphereC6Norm F := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.sum_le_sum fun j hj ↦ htermBound i j
      _ = Kraw * sphereC6Norm F := by
        simp [Kraw, nsmul_eq_mul]
        ring
  exact hraw.trans <|
    mul_le_mul_of_nonneg_right (le_max_right 1 Kraw) hC

/-- Scalar multiplication by a fixed coordinate projection does not enlarge any derivative
through order six. -/
theorem norm_iteratedFDeriv_smul_proj_le {n m : ℕ} (i : Fin n)
    {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : ContDiffAt ℝ 6 f x)
    (hm : m ≤ 6) :
    ‖iteratedFDeriv ℝ m (fun y ↦ f y •
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ := by
  let L : ℝ →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toSpanSingleton ℝ
      (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)
  have hL : ‖L‖ ≤ 1 := by
    simpa [L] using norm_continuousLinearMap_proj_le_one i
  change ‖iteratedFDeriv ℝ m (L ∘ f) x‖ ≤ _
  calc
    ‖iteratedFDeriv ℝ m (L ∘ f) x‖ ≤
        ‖L‖ * ‖iteratedFDeriv ℝ m f x‖ :=
      L.norm_iteratedFDeriv_comp_left hf (by exact_mod_cast hm)
    _ ≤ 1 * ‖iteratedFDeriv ℝ m f x‖ :=
      mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = _ := one_mul _

/-- Uniform induction for radial pullback: every derivative up to a prescribed order is
controlled by the rotational norm with the same word-length cutoff. -/
theorem exists_radialPullback_deriv_le_sphereRotNorm_up_to {n : ℕ} (hn : 0 < n) :
    ∀ m, m ≤ 6 → ∃ K : ℝ, 1 ≤ K ∧
      ∀ r, r ≤ m → ∀ (F : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ),
        x ∈ radialClosedAnnulus n →
          ‖iteratedFDeriv ℝ r
            (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
            K * sphereRotNorm r F := by
  obtain ⟨A, hAone, hA⟩ := radialTangentCoefficient_uniform_deriv_bound hn
  intro m hm
  induction m with
  | zero =>
      refine ⟨1, le_rfl, ?_⟩
      intro r hr F x hx
      have hrzero : r = 0 := by omega
      subst r
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hxpos : 0 < radialNormSq x := by linarith [hx.1]
      calc
        |MvPolynomial.eval (radialDirection x) F| ≤ sphereSupNorm F :=
          sphereSupNorm_eval_le F (radialDirection x) (radialDirection_mem_sphere hxpos)
        _ = sphereRotNorm 0 F := rfl
        _ = 1 * sphereRotNorm 0 F := by ring
  | succ m ih =>
      have hmfive : m ≤ 5 := by omega
      obtain ⟨Kold, hKold, hold⟩ := ih (by omega)
      let S : ℝ := ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ)
      let B : ℝ := S * A * Kold
      let Kstep : ℝ := (n : ℝ) ^ 2 * B
      let Knew : ℝ := max Kold Kstep
      refine ⟨Knew, hKold.trans (le_max_left _ _), ?_⟩
      intro r hr F x hx
      have hxpos : 0 < radialNormSq x := by linarith [hx.1]
      have hKold0 : 0 ≤ Kold := zero_le_one.trans hKold
      have hrotNonneg (q : ℕ) (G : MvPolynomial (Fin n) ℝ) :
          0 ≤ sphereRotNorm q G := sphereRotNorm_nonneg hn q G
      by_cases hrle : r ≤ m
      · calc
          ‖iteratedFDeriv ℝ r
              (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
              Kold * sphereRotNorm r F := hold r hrle F x hx
          _ ≤ Knew * sphereRotNorm r F :=
            mul_le_mul_of_nonneg_right (le_max_left Kold Kstep) (hrotNonneg r F)
      · have hre : r = m + 1 := by omega
        subst r
        let scalar : Fin n → Fin n → (Fin n → ℝ) → ℝ := fun i j y ↦
          radialTangentCoefficient j y *
            MvPolynomial.eval (radialDirection y) (rotationDeriv j i F)
        let term : Fin n → Fin n → (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) :=
          fun i j y ↦ scalar i j y •
            (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)
        have hscalarDiff (i j : Fin n) : ContDiffAt ℝ 6 (scalar i j) x := by
          exact (radialTangentCoefficient_contDiffAt j hxpos).mul <|
            (mvPolynomial_eval_contDiff (rotationDeriv j i F) 6).contDiffAt.comp x
              (radialDirection_contDiffAt hxpos)
        have htermDiff (i j : Fin n) : ContDiffAt ℝ m (term i j) x := by
          exact ((hscalarDiff i j).smul contDiffAt_const).of_le (by
            exact_mod_cast hmfive.trans (by norm_num : 5 ≤ 6))
        have hinnerDiff (i : Fin n) : ContDiffAt ℝ m (fun y ↦ ∑ j, term i j y) x := by
          exact ContDiffAt.sum fun j hj ↦ htermDiff i j
        have hexpand :
            iteratedFDeriv ℝ m (radialPullbackFirstExpansion F) x =
              ∑ i, ∑ j, iteratedFDeriv ℝ m (term i j) x := by
          have hfun : radialPullbackFirstExpansion F = fun y ↦ ∑ i, ∑ j, term i j y := by
            funext y
            rfl
          rw [hfun]
          calc
            iteratedFDeriv ℝ m (fun y ↦ ∑ i, ∑ j, term i j y) x =
                ∑ i, iteratedFDeriv ℝ m (fun y ↦ ∑ j, term i j y) x :=
              iteratedFDeriv_finset_sum_apply_of_contDiffAt
                (u := Finset.univ) (fun i hi ↦ hinnerDiff i)
            _ = ∑ i, ∑ j, iteratedFDeriv ℝ m (term i j) x := by
              apply Finset.sum_congr rfl
              intro i hi
              exact iteratedFDeriv_finset_sum_apply_of_contDiffAt
                (u := Finset.univ) (fun j hj ↦ htermDiff i j)
        have hpositiveNhd : {y : Fin n → ℝ | 0 < radialNormSq y} ∈ 𝓝 x :=
          (isOpen_lt continuous_const (radialNormSq_contDiff 6).continuous).mem_nhds hxpos
        have heq :
            (fun y ↦ fderiv ℝ
              (fun z ↦ MvPolynomial.eval (radialDirection z) F) y) =ᶠ[𝓝 x]
              radialPullbackFirstExpansion F := by
          filter_upwards [hpositiveNhd] with y hy
          exact fderiv_radialPullback_eq_firstExpansion hy F
        have hderivEq :
            iteratedFDeriv ℝ m
                (fun y ↦ fderiv ℝ
                  (fun z ↦ MvPolynomial.eval (radialDirection z) F) y) x =
              iteratedFDeriv ℝ m (radialPullbackFirstExpansion F) x :=
          (heq.iteratedFDeriv ℝ m).self_of_nhds
        have hpull (i j : Fin n) (q : ℕ) (hq : q ≤ m) :
            ‖iteratedFDeriv ℝ q
              (fun y ↦ MvPolynomial.eval (radialDirection y) (rotationDeriv j i F)) x‖ ≤
              Kold * sphereRotNorm (m + 1) F := by
          calc
            ‖iteratedFDeriv ℝ q
                (fun y ↦ MvPolynomial.eval (radialDirection y)
                  (rotationDeriv j i F)) x‖ ≤
                Kold * sphereRotNorm q (rotationDeriv j i F) :=
              hold q hq (rotationDeriv j i F) x hx
            _ ≤ Kold * sphereRotNorm (m + 1) F := by
              apply mul_le_mul_of_nonneg_left _ hKold0
              exact (sphereRotNorm_rotationDeriv_le_succ hn q F j i).trans
                (sphereRotNorm_mono hn (by omega) F)
        have hscalarBound (i j : Fin n) :
            ‖iteratedFDeriv ℝ m (scalar i j) x‖ ≤
              B * sphereRotNorm (m + 1) F := by
          have hbase := norm_iteratedFDeriv_mul_le_of_contDiffAt
            (radialTangentCoefficient_contDiffAt j hxpos)
            ((mvPolynomial_eval_contDiff (rotationDeriv j i F) 6).contDiffAt.comp x
              (radialDirection_contDiffAt hxpos))
            (n := m) (hmfive.trans (by norm_num))
          calc
            ‖iteratedFDeriv ℝ m (scalar i j) x‖ ≤
                ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ) *
                  ‖iteratedFDeriv ℝ q (radialTangentCoefficient j) x‖ *
                    ‖iteratedFDeriv ℝ (m - q)
                      (fun y ↦ MvPolynomial.eval (radialDirection y)
                        (rotationDeriv j i F)) x‖ := hbase
            _ ≤ ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ) * A *
                  (Kold * sphereRotNorm (m + 1) F) := by
              apply Finset.sum_le_sum
              intro q hqmem
              have hq : q ≤ m := Finset.mem_range_succ_iff.mp hqmem
              have hchoose : 0 ≤ (m.choose q : ℝ) := by positivity
              gcongr
              · exact hA j q (hq.trans hmfive) x hx
              · exact hpull i j (m - q) (Nat.sub_le m q)
            _ = B * sphereRotNorm (m + 1) F := by
              simp only [B, S]
              rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro q hq
              ring
        have htermBound (i j : Fin n) :
            ‖iteratedFDeriv ℝ m (term i j) x‖ ≤
              B * sphereRotNorm (m + 1) F := by
          exact (norm_iteratedFDeriv_smul_proj_le i (hscalarDiff i j)
            (hmfive.trans (by norm_num))).trans (hscalarBound i j)
        have hraw :
            ‖iteratedFDeriv ℝ (m + 1)
              (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
              Kstep * sphereRotNorm (m + 1) F := by
          calc
            ‖iteratedFDeriv ℝ (m + 1)
                (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ =
                ‖iteratedFDeriv ℝ m
                  (fun y ↦ fderiv ℝ
                    (fun z ↦ MvPolynomial.eval (radialDirection z) F) y) x‖ := by
              symm
              exact norm_iteratedFDeriv_fderiv
            _ = ‖iteratedFDeriv ℝ m (radialPullbackFirstExpansion F) x‖ :=
              congrArg norm hderivEq
            _ = ‖∑ i, ∑ j, iteratedFDeriv ℝ m (term i j) x‖ :=
              congrArg norm hexpand
            _ ≤ ∑ i, ‖∑ j, iteratedFDeriv ℝ m (term i j) x‖ := norm_sum_le _ _
            _ ≤ ∑ i, ∑ j, ‖iteratedFDeriv ℝ m (term i j) x‖ := by
              apply Finset.sum_le_sum
              intro i hi
              exact norm_sum_le _ _
            _ ≤ ∑ _i : Fin n, ∑ _j : Fin n,
                B * sphereRotNorm (m + 1) F := by
              apply Finset.sum_le_sum
              intro i hi
              exact Finset.sum_le_sum fun j hj ↦ htermBound i j
            _ = Kstep * sphereRotNorm (m + 1) F := by
              simp [Kstep, nsmul_eq_mul]
              ring
        exact hraw.trans <|
          mul_le_mul_of_nonneg_right (le_max_right Kold Kstep)
            (hrotNonneg (m + 1) F)

/-- The remaining higher-order adapter: on a fixed annulus, derivative orders three
through six of radial pullback are controlled by rotation words on the sphere. The complete
first- and second-order tangent-frame calculations are proved above. -/
theorem radialPullback_higher_deriv_le_sphereC6Norm_on_annulus {n : ℕ} (hn : 3 ≤ n) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (F : MvPolynomial (Fin n) ℝ) j, 3 ≤ j → j ≤ 6 → ∀ x,
        1 / 4 < radialNormSq x → radialNormSq x < 2 →
          ‖iteratedFDeriv ℝ j
            (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
            K * sphereC6Norm F := by
  have hnpos : 0 < n := by omega
  obtain ⟨K, hK, hall⟩ :=
    exists_radialPullback_deriv_le_sphereRotNorm_up_to hnpos 6 (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro F j hjlow hj x hxinner hxouter
  have hxann : x ∈ radialClosedAnnulus n := ⟨hxinner.le, hxouter.le⟩
  calc
    ‖iteratedFDeriv ℝ j
        (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
        K * sphereRotNorm j F := hall j hj F x hxann
    _ ≤ K * sphereRotNorm 6 F :=
      mul_le_mul_of_nonneg_left (sphereRotNorm_mono hnpos hj F)
        (zero_le_one.trans hK)
    _ = K * sphereC6Norm F := rfl

/-- On a fixed annulus, all positive-order ambient derivatives of radial pullback are controlled
by rotation derivatives on the sphere. Orders one and two are the explicit tangent-frame
estimates above; only orders three through six use the higher-order adapter. -/
theorem radialPullback_deriv_le_sphereC6Norm_on_annulus {n : ℕ} (hn : 3 ≤ n) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (F : MvPolynomial (Fin n) ℝ) j, 1 ≤ j → j ≤ 6 → ∀ x,
        1 / 4 < radialNormSq x → radialNormSq x < 2 →
          ‖iteratedFDeriv ℝ j
            (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
            K * sphereC6Norm F := by
  have hnpos : 0 < n := by omega
  obtain ⟨Kh, hKh, hhigh⟩ :=
    radialPullback_higher_deriv_le_sphereC6Norm_on_annulus hn
  obtain ⟨K2, hK2, hsecond⟩ :=
    exists_norm_iteratedFDeriv_two_radialPullback_le_sphereC6Norm hnpos
  let K1 : ℝ := 2 * (n : ℝ) ^ 2
  let K : ℝ := max Kh (max K2 K1)
  refine ⟨K, hKh.trans (le_max_left _ _), ?_⟩
  intro F j hjpos hj x hxinner hxouter
  by_cases hjone : j = 1
  · subst j
    rw [norm_iteratedFDeriv_one]
    calc
      ‖fderiv ℝ (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
          K1 * sphereC6Norm F :=
        norm_fderiv_radialPullback_le_sphereC6Norm hnpos F hxinner
      _ ≤ K * sphereC6Norm F :=
        mul_le_mul_of_nonneg_right
          ((le_max_right K2 K1).trans (le_max_right Kh (max K2 K1)))
          (sphereC6Norm_nonneg hnpos F)
  · by_cases hjtwo : j = 2
    · subst j
      calc
        ‖iteratedFDeriv ℝ 2
            (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
            K2 * sphereC6Norm F := hsecond F x hxinner hxouter
        _ ≤ K * sphereC6Norm F :=
          mul_le_mul_of_nonneg_right
            ((le_max_left K2 K1).trans (le_max_right Kh (max K2 K1)))
            (sphereC6Norm_nonneg hnpos F)
    · calc
        ‖iteratedFDeriv ℝ j
            (fun y ↦ MvPolynomial.eval (radialDirection y) F) x‖ ≤
            Kh * sphereC6Norm F := hhigh F j (by omega) hj x hxinner hxouter
        _ ≤ K * sphereC6Norm F :=
          mul_le_mul_of_nonneg_right (le_max_left Kh (max K2 K1))
            (sphereC6Norm_nonneg hnpos F)

/-- Ambient derivatives of the fixed annular extension are controlled by the rotational C6 norm.
The proof below supplies all cutoff bounds, locally-zero regions, product-rule constants, and
zeroth-order pullback control; only the annular tangent-frame comparison above is assumed. -/
theorem compactRadialExtension_deriv_le_sphereC6Norm {n : ℕ} (hn : 3 ≤ n) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (F : MvPolynomial (Fin n) ℝ) j, 1 ≤ j → j ≤ 6 → ∀ x,
        ‖iteratedFDeriv ℝ j (compactRadialExtension F) x‖ ≤
          M * sphereC6Norm F := by
  have hnpos : 0 < n := by omega
  obtain ⟨A, hA, hcutoff⟩ := radialAnnularCutoffSquare_uniform_deriv_bound n
  obtain ⟨K, hK, hpullback⟩ := radialPullback_deriv_le_sphereC6Norm_on_annulus hn
  let M : ℝ := max 1 (64 * A * K)
  refine ⟨M, le_max_left _ _, ?_⟩
  intro F j hjpos hj x
  by_cases hinner : radialNormSq x ≤ 1 / 4
  · have hxhalf : radialNormSq x < 1 / 2 := by linarith
    have heq :=
      compactRadialExtension_eventuallyEq_zero_of_radialNormSq_lt_half F hxhalf
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_fun_zero]
    simp only [Pi.zero_apply, norm_zero]
    exact mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (sphereC6Norm_nonneg hnpos F)
  · by_cases houter : 2 ≤ radialNormSq x
    · have hxouter : 3 / 2 < radialNormSq x := by linarith
      have heq :=
        compactRadialExtension_eventuallyEq_zero_of_three_halves_lt_radialNormSq F hxouter
      rw [(heq.iteratedFDeriv ℝ j).self_of_nhds, iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg (zero_le_one.trans (le_max_left _ _))
        (sphereC6Norm_nonneg hnpos F)
    · have hxinner : 1 / 4 < radialNormSq x := lt_of_not_ge hinner
      have hxouter : radialNormSq x < 2 := lt_of_not_ge houter
      have hxpos : 0 < radialNormSq x := by linarith
      let cutoffSquare : (Fin n → ℝ) → ℝ :=
        fun y ↦ radialAnnularCutoff n y ^ 2
      let pullback : (Fin n → ℝ) → ℝ :=
        fun y ↦ MvPolynomial.eval (radialDirection y) F
      have hcutoffSmooth : ContDiffAt ℝ 6 cutoffSquare x :=
        ((radialAnnularCutoff_contDiff n).pow 2).contDiffAt
      have hpullbackSmooth : ContDiffAt ℝ 6 pullback x := by
        exact (mvPolynomial_eval_contDiff F 6).contDiffAt.comp x
          (radialDirection_contDiffAt hxpos)
      have hcutoffBound : ∀ q, q ≤ 6 →
          ‖iteratedFDeriv ℝ q cutoffSquare x‖ * 1 ^ q ≤ A := by
        intro q hq
        simpa [cutoffSquare] using hcutoff q hq x
      have hpullbackBound : ∀ q, q ≤ 6 →
          ‖iteratedFDeriv ℝ q pullback x‖ * 1 ^ q ≤ K * sphereC6Norm F := by
        intro q hq
        rcases q with _ | q
        · have hdir : radialDirection x ∈ sphereSet n := radialDirection_mem_sphere hxpos
          have heval : ‖MvPolynomial.eval (radialDirection x) F‖ ≤ sphereC6Norm F := by
            rw [Real.norm_eq_abs]
            exact (sphereSupNorm_eval_le F (radialDirection x) hdir).trans
              (sphereSupNorm_le_sphereRotNorm hnpos 6 F)
          have hscale : sphereC6Norm F ≤ K * sphereC6Norm F := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hK
              (sphereC6Norm_nonneg hnpos F)
          simpa [pullback, iteratedFDeriv_zero_apply] using heval.trans hscale
        · simpa [pullback] using
            hpullback F (q + 1) (by omega) hq x hxinner hxouter
      have hproduct := norm_iteratedFDeriv_mul_scaled_le_of_contDiffAt
        (r := (1 : ℝ)) (Mf := A) (Mg := K * sphereC6Norm F)
        zero_lt_one (zero_le_one.trans hA)
        (mul_nonneg (zero_le_one.trans hK) (sphereC6Norm_nonneg hnpos F))
        hcutoffSmooth hpullbackSmooth hcutoffBound hpullbackBound hj
      have hraw :
          ‖iteratedFDeriv ℝ j (compactRadialExtension F) x‖ ≤
            64 * A * (K * sphereC6Norm F) := by
        change ‖iteratedFDeriv ℝ j (fun y ↦
          radialAnnularCutoff n y ^ 2 * MvPolynomial.eval (radialDirection y) F) x‖ ≤ _
        simpa [cutoffSquare, pullback] using hproduct
      calc
        ‖iteratedFDeriv ℝ j (compactRadialExtension F) x‖ ≤
            64 * A * (K * sphereC6Norm F) := hraw
        _ = (64 * A * K) * sphereC6Norm F := by ring
        _ ≤ M * sphereC6Norm F :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (sphereC6Norm_nonneg hnpos F)

/-- The remaining radial analytic leaf: construct a compact normalized radial extension and
prove that its Euclidean atom centers and supports induce the required sphere-cap geometry. -/
theorem uniformRadialEuclideanAtomRealization_of_euclidean {n : ℕ} (hn : 3 ≤ n)
    (hatoms : HasUniformEuclideanAtomDecomposition n) :
    HasUniformRadialEuclideanAtomRealization n := by
  let L : ℝ := 2 * (n : ℝ)
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hL : 1 ≤ L := by
    dsimp [L]
    nlinarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdim : 4 * (n : ℝ) ≤ L ^ 2 := by
    have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) :=
      mul_nonneg (zero_le_one.trans hnR) (sub_nonneg.mpr hnR)
    dsimp [L]
    nlinarith
  obtain ⟨M, hM, hradial⟩ := compactRadialExtension_deriv_le_sphereC6Norm hn
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  obtain ⟨C₀, B, hC₀, hB, hfamilies⟩ :=
    hatoms (L + 1) L⁻¹ (by linarith) (inv_pos.mpr hLpos)
      (inv_le_one_of_one_le₀ hL)
  let C : ℝ := Real.sqrt M * C₀ * L ^ 2
  refine ⟨C, B, ?_, hB, ?_⟩
  · dsimp [C]
    exact mul_pos (mul_pos (Real.sqrt_pos.2 hMpos) hC₀) (sq_pos_of_pos hLpos)
  · intro F hF hnorm
    let U : (Fin n → ℝ) → ℝ := compactRadialExtension F
    let uNorm : (Fin n → ℝ) → ℝ := fun x ↦ M⁻¹ * U x
    have hUderiv : ∀ j, j ≤ 6 → ∀ x,
        ‖iteratedFDeriv ℝ j U x‖ ≤ M := by
      intro j hj x
      have hfirst : ‖iteratedFDeriv ℝ j U x‖ ≤ M * sphereC6Norm F := by
        rcases j with _ | j
        · have hzero := norm_compactRadialExtension_le_sphereC6Norm hnpos F x
          have hscale : sphereC6Norm F ≤ M * sphereC6Norm F := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hM
              (sphereC6Norm_nonneg hnpos F)
          simpa [U, iteratedFDeriv_zero_apply] using hzero.trans hscale
        · exact hradial F (j + 1) (by omega) hj x
      calc
        ‖iteratedFDeriv ℝ j U x‖ ≤ M * sphereC6Norm F := hfirst
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left hnorm hMpos.le
        _ = M := mul_one M
    have huNorm : NormalizedNonnegativeC6 uNorm := by
      exact normalizedNonnegativeC6_of_bound
        (u := U) (fun x ↦ compactRadialExtension_nonnegative hF x)
        (compactRadialExtension_contDiff F)
        (compactRadialExtension_hasCompactSupport F) M hMpos hUderiv
    let raw := Classical.choice (hfamilies uNorm huNorm)
    let widened := raw.sphereFilteredWidened hnpos hL (Real.sqrt_pos.2 hMpos) hC₀.le
    refine ⟨{
      function := raw.sphereFilteredFunction (Real.sqrt M)
      dilation := 1
      radiusCap := 1
      atoms := widened
      geometry := raw.sphereFilteredWidenedGeometry hnpos hL hdim
        (Real.sqrt_pos.2 hMpos) hC₀.le
      restricts_to_polynomial := ?_
    }⟩
    intro x hx
    rw [raw.sphereFilteredFunction_eq_on_sphere (Real.sqrt_nonneg M) x hx]
    dsimp [uNorm, U]
    rw [Real.sq_sqrt hMpos.le, compactRadialExtension_eq_on_sphere F hx]
    field_simp
/-- Radial extension and recentering transport the uniform Euclidean atoms to the sphere. -/
theorem uniformSphereAtoms_of_euclidean {n : ℕ} (hn : 3 ≤ n)
    (hatoms : HasUniformEuclideanAtomDecomposition n) :
    HasUniformSphereAtomDecomposition n := by
  obtain ⟨C, B, hC, hB, hfamilies⟩ :=
    uniformRadialEuclideanAtomRealization_of_euclidean hn hatoms
  refine ⟨C, B, hC, hB, ?_⟩
  intro F hF hnorm
  let realization := Classical.choice (hfamilies F hF hnorm)
  exact ⟨realization.atoms.toSphereAtomFamily realization.geometry
    realization.restricts_to_polynomial⟩

end QuarticConvergence
end OptimalConvergenceRates

end
