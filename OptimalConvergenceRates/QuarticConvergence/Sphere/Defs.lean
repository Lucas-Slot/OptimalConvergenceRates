/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Defs.lean

  Algebraic definitions for quartic convergence of the sphere SOS hierarchy.

-/
import OptimalConvergenceRates.BasicNotions.SphereSOS
import OptimalConvergenceRates.BasicNotions.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

variable {n : ℕ}

/-- The north pole in a positive ambient dimension. -/
def sphereNorthPole (hn : 0 < n) : Fin n → ℝ :=
  fun i ↦ if i = ⟨0, hn⟩ then 1 else 0


/-- The coordinate north pole satisfies the algebraic unit-sphere equation. -/
theorem sphereNorthPole_mem_sphereSet (hn : 0 < n) :
    sphereNorthPole hn ∈ sphereSet n := by
  simp only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X, Set.mem_ofPred_eq]
  rw [Finset.sum_eq_single ⟨0, hn⟩]
  · simp [sphereNorthPole]
  · intro i _ hi
    simp [sphereNorthPole, hi]
  · simp

/-- The north pole as a point of the repository's algebraic sphere. -/
def sphereNorthPolePoint (hn : 0 < n) : sphereSet n :=
  ⟨sphereNorthPole hn, sphereNorthPole_mem_sphereSet hn⟩

/-- The algebraically defined unit sphere is nonempty in positive dimension. -/
theorem sphereSet_nonempty (hn : 0 < n) : (sphereSet n).Nonempty := by
  exact ⟨sphereNorthPole hn, sphereNorthPole_mem_sphereSet hn⟩


/-- A fixed reference point on the sphere, used after reducing center-dependent
statements by orthogonal invariance. -/
noncomputable def sphereReferencePoint (n : ℕ) (hn : 0 < n) : sphereSet n :=
  Classical.choice (sphereSet_nonempty hn).to_subtype

/-- A polynomial is nonnegative on the unit sphere. -/
def SphereNonnegative (p : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ x ∈ sphereSet n, 0 ≤ MvPolynomial.eval x p

/-- Values of a polynomial on the unit sphere. -/
def sphereValueSet (p : MvPolynomial (Fin n) ℝ) : Set ℝ :=
  (fun x ↦ MvPolynomial.eval x p) '' sphereSet n

/-- The infimum of a polynomial on the unit sphere. -/
def spherePolyMin (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  sInf (sphereValueSet p)

/-- The supremum of a polynomial on the unit sphere. -/
def spherePolyMax (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  sSup (sphereValueSet p)

/-- The oscillation of a polynomial on the unit sphere. -/
def spherePolyOscillation (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  spherePolyMax p - spherePolyMin p

/-- The supremum norm of the restriction of a polynomial to the unit sphere. -/
def sphereSupNorm (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  sSup (abs '' ((fun x ↦ MvPolynomial.eval x p) '' sphereSet n))

/-- The algebraic unit sphere is closed in coordinate space. -/
theorem sphereSet_isClosed : IsClosed (sphereSet n) := by
  unfold sphereSet
  exact isClosed_eq (MvPolynomial.continuous_eval _) continuous_const

/-- Every point on the unit sphere belongs to the repository's standard hypercube. -/
theorem sphereSet_subset_hypercube : sphereSet n ⊆ Hypercube n := by
  intro x hx
  rw [Hypercube_mem_iff]
  intro i
  have hsum : ∑ j : Fin n, x j ^ 2 = 1 := by
    simpa [sphereSet, sphereQuadratic] using hx
  have hi : x i ^ 2 ≤ ∑ j : Fin n, x j ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
  rw [hsum] at hi
  constructor <;> nlinarith [sq_nonneg (x i)]

/-- Compactness of the algebraically defined unit sphere. -/
theorem sphereSet_compact : IsCompact (sphereSet n) :=
  Hypercube_compact.of_isClosed_subset sphereSet_isClosed sphereSet_subset_hypercube

/-- The range of a polynomial on the sphere is compact. -/
theorem sphereValueSet_compact (p : MvPolynomial (Fin n) ℝ) :
    IsCompact (sphereValueSet p) :=
  sphereSet_compact.image (MvPolynomial.continuous_eval p)

/-- The range of a polynomial on a positive-dimensional sphere is nonempty. -/
theorem sphereValueSet_nonempty (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    (sphereValueSet p).Nonempty :=
  Set.Nonempty.image _ (sphereSet_nonempty hn)

/-- A polynomial attains its sphere infimum in positive ambient dimension. -/
theorem spherePolyMin_mem (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    ∃ x ∈ sphereSet n, MvPolynomial.eval x p = spherePolyMin p := by
  have h := (sphereValueSet_compact p).sInf_mem (sphereValueSet_nonempty hn p)
  exact h

/-- A polynomial attains its sphere supremum in positive ambient dimension. -/
theorem spherePolyMax_mem (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    ∃ x ∈ sphereSet n, MvPolynomial.eval x p = spherePolyMax p := by
  have h := (sphereValueSet_compact p).sSup_mem (sphereValueSet_nonempty hn p)
  exact h

/-- The sphere infimum is below every value on the sphere. -/
theorem spherePolyMin_le_eval (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) : spherePolyMin p ≤ MvPolynomial.eval x p := by
  exact csInf_le (sphereValueSet_compact p).bddBelow ⟨x, hx, rfl⟩

/-- Every value on the sphere is below the sphere supremum. -/
theorem eval_le_spherePolyMax (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) : MvPolynomial.eval x p ≤ spherePolyMax p := by
  exact le_csSup (sphereValueSet_compact p).bddAbove ⟨x, hx, rfl⟩

/-- On a positive-dimensional sphere, the minimum is at most the maximum. -/
theorem spherePolyMin_le_spherePolyMax (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) : spherePolyMin p ≤ spherePolyMax p := by
  exact csInf_le_csSup (sphereValueSet_nonempty hn p)
    (sphereValueSet_compact p).bddBelow (sphereValueSet_compact p).bddAbove

/-- Pointwise control by the restriction sup norm. -/
theorem sphereSupNorm_eval_le (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) : |MvPolynomial.eval x p| ≤ sphereSupNorm p := by
  unfold sphereSupNorm
  exact le_csSup
    ((sphereValueSet_compact p).image continuous_abs).bddAbove
    ⟨MvPolynomial.eval x p, ⟨x, hx, rfl⟩, rfl⟩

/-- The restriction sup norm is nonnegative in positive ambient dimension. -/
theorem sphereSupNorm_nonneg (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    0 ≤ sphereSupNorm p := by
  obtain ⟨x, hx⟩ := sphereSet_nonempty hn
  exact (abs_nonneg (MvPolynomial.eval x p)).trans (sphereSupNorm_eval_le p x hx)

/-- A uniform pointwise estimate bounds the restriction sup norm. -/
theorem sphereSupNorm_le_of_bound (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) (c : ℝ)
    (h : ∀ x ∈ sphereSet n, |MvPolynomial.eval x p| ≤ c) :
    sphereSupNorm p ≤ c := by
  unfold sphereSupNorm
  apply csSup_le
  · exact (sphereSet_nonempty hn).image _ |>.image _
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact h x hx

/-- The sphere sup norm is attained in positive ambient dimension. -/
theorem sphereSupNorm_mem (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    ∃ x ∈ sphereSet n, |MvPolynomial.eval x p| = sphereSupNorm p := by
  have hcompact := (sphereValueSet_compact p).image continuous_abs
  have hnonempty := (sphereValueSet_nonempty hn p).image abs
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hcompact.sSup_mem hnonempty
  exact ⟨x, hx, hy⟩

/-- The zero polynomial has zero sphere sup norm. -/
@[simp] theorem sphereSupNorm_zero (hn : 0 < n) :
    sphereSupNorm (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  apply le_antisymm
  · apply sphereSupNorm_le_of_bound hn
    simp
  · exact sphereSupNorm_nonneg hn 0

/-- Negating an ambient polynomial does not change its sphere sup norm. -/
@[simp] theorem sphereSupNorm_neg (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm (-p) = sphereSupNorm p := by
  apply le_antisymm
  · apply sphereSupNorm_le_of_bound hn
    intro x hx
    simpa using sphereSupNorm_eval_le p x hx
  · apply sphereSupNorm_le_of_bound hn
    intro x hx
    simpa using sphereSupNorm_eval_le (-p) x hx

/-- Triangle inequality for the sphere restriction sup norm. -/
theorem sphereSupNorm_add_le (hn : 0 < n) (p q : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm (p + q) ≤ sphereSupNorm p + sphereSupNorm q := by
  apply sphereSupNorm_le_of_bound hn
  intro x hx
  calc
    |MvPolynomial.eval x (p + q)| = |MvPolynomial.eval x p + MvPolynomial.eval x q| := by
      rw [map_add]
    _ ≤ |MvPolynomial.eval x p| + |MvPolynomial.eval x q| := abs_add_le _ _
    _ ≤ sphereSupNorm p + sphereSupNorm q :=
      add_le_add (sphereSupNorm_eval_le p x hx) (sphereSupNorm_eval_le q x hx)

/-- Subadditivity for polynomial differences. -/
theorem sphereSupNorm_sub_le (hn : 0 < n) (p q : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm (p - q) ≤ sphereSupNorm p + sphereSupNorm q := by
  rw [sub_eq_add_neg]
  exact (sphereSupNorm_add_le hn p (-q)).trans_eq (congrArg (sphereSupNorm p + ·)
    (sphereSupNorm_neg hn q))

/-- Absolute homogeneity of the sphere restriction sup norm. -/
theorem sphereSupNorm_smul (hn : 0 < n) (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm (c • p) = |c| * sphereSupNorm p := by
  apply le_antisymm
  · apply sphereSupNorm_le_of_bound hn
    intro x hx
    rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, abs_mul]
    exact mul_le_mul_of_nonneg_left (sphereSupNorm_eval_le p x hx) (abs_nonneg c)
  · obtain ⟨x, hx, hmax⟩ := sphereSupNorm_mem hn p
    have h := sphereSupNorm_eval_le (c • p) x hx
    simpa only [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, abs_mul, hmax] using h

/-- The sphere restriction supremum is packaged as a genuine seminorm on ambient
polynomials.  Its kernel consists of polynomials vanishing on the sphere. -/
def sphereSupSeminorm (hn : 0 < n) : Seminorm ℝ (MvPolynomial (Fin n) ℝ) :=
  Seminorm.of sphereSupNorm (sphereSupNorm_add_le hn) fun c p ↦ by
    simpa only [Real.norm_eq_abs] using sphereSupNorm_smul hn c p

@[simp] theorem sphereSupSeminorm_apply (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    sphereSupSeminorm hn p = sphereSupNorm p := rfl


/-- Sphere nonnegativity is equivalent to nonnegativity of the attained minimum. -/
theorem sphereNonnegative_iff_min_nonnegative (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    SphereNonnegative p ↔ 0 ≤ spherePolyMin p := by
  constructor
  · intro hp
    obtain ⟨x, hx, hmin⟩ := spherePolyMin_mem hn p
    rw [← hmin]
    exact hp x hx
  · intro hmin x hx
    exact hmin.trans (spherePolyMin_le_eval p x hx)

/-- Centering at the sphere minimum produces a sphere-nonnegative polynomial. -/
theorem centerAtSphereMin_nonnegative (p : MvPolynomial (Fin n) ℝ) :
    SphereNonnegative (p - MvPolynomial.C (spherePolyMin p)) := by
  intro x hx
  simp only [map_sub, eval_C]
  exact sub_nonneg.mpr (spherePolyMin_le_eval p x hx)

/-- The sup norm after centering at the minimum is exactly the sphere oscillation. -/
theorem sphereSupNorm_center_eq_oscillation (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm (p - MvPolynomial.C (spherePolyMin p)) =
      spherePolyOscillation p := by
  apply le_antisymm
  · apply sphereSupNorm_le_of_bound hn
    intro x hx
    simp only [map_sub, eval_C]
    rw [abs_of_nonneg (sub_nonneg.mpr (spherePolyMin_le_eval p x hx))]
    exact sub_le_sub_right (eval_le_spherePolyMax p x hx) _
  · obtain ⟨x, hx, hmax⟩ := spherePolyMax_mem hn p
    have h := sphereSupNorm_eval_le
      (p - MvPolynomial.C (spherePolyMin p)) x hx
    simp only [map_sub, eval_C, hmax] at h
    rw [abs_of_nonneg (sub_nonneg.mpr (spherePolyMin_le_spherePolyMax hn p))] at h
    exact h

/-- Sphere oscillation is nonnegative in positive ambient dimension. -/
theorem spherePolyOscillation_nonneg (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) : 0 ≤ spherePolyOscillation p := by
  exact sub_nonneg.mpr (spherePolyMin_le_spherePolyMax hn p)

/-- Adding a constant translates the sphere minimum by that constant. -/
theorem spherePolyMin_add_const (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    spherePolyMin (p + MvPolynomial.C c) = spherePolyMin p + c := by
  obtain ⟨xmin, hxmin, hpmin⟩ := spherePolyMin_mem hn p
  obtain ⟨ymin, hymin, hpcmin⟩ := spherePolyMin_mem hn (p + MvPolynomial.C c)
  apply le_antisymm
  · have h := spherePolyMin_le_eval (p + MvPolynomial.C c) xmin hxmin
    simpa only [map_add, eval_C, hpmin] using h
  · have h := spherePolyMin_le_eval p ymin hymin
    simp only [map_add, eval_C] at hpcmin
    linarith

/-- Adding a constant translates the sphere maximum by that constant. -/
theorem spherePolyMax_add_const (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    spherePolyMax (p + MvPolynomial.C c) = spherePolyMax p + c := by
  obtain ⟨xmax, hxmax, hpmax⟩ := spherePolyMax_mem hn p
  obtain ⟨ymax, hymax, hpcmax⟩ := spherePolyMax_mem hn (p + MvPolynomial.C c)
  apply le_antisymm
  · have h := eval_le_spherePolyMax p ymax hymax
    simp only [map_add, eval_C] at hpcmax
    linarith
  · have h := eval_le_spherePolyMax (p + MvPolynomial.C c) xmax hxmax
    simpa only [map_add, eval_C, hpmax] using h

/-- Sphere oscillation is invariant under addition of constants. -/
@[simp] theorem spherePolyOscillation_add_const (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    spherePolyOscillation (p + MvPolynomial.C c) = spherePolyOscillation p := by
  rw [spherePolyOscillation, spherePolyMin_add_const hn, spherePolyMax_add_const hn,
    spherePolyOscillation]
  ring

/-- Centering at the minimum removes any previously added constant exactly. -/
theorem centerAtSphereMin_add_const (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    p + MvPolynomial.C c -
        MvPolynomial.C (spherePolyMin (p + MvPolynomial.C c)) =
      p - MvPolynomial.C (spherePolyMin p) := by
  rw [spherePolyMin_add_const hn]
  simp only [map_add]
  ring




/-- The partial derivative of the sphere quadratic has the expected linear form. -/
theorem pderiv_sphereQuadratic (i : Fin n) :
    pderiv i (sphereQuadratic n) = 2 * X i := by
  classical
  unfold sphereQuadratic
  simp only [map_sum, pderiv_pow, Nat.cast_ofNat, pderiv_X]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The constant term in the sphere relation has zero partial derivative. -/
@[simp] theorem pderiv_sphereRelation (i : Fin n) :
    pderiv i (sphereRelation n) = 2 * X i := by
  rw [sphereRelation, map_sub, pderiv_sphereQuadratic]
  simp

/-- A partial derivative lowers total degree by one (with truncated subtraction for
constants).  This support-level lemma is absent from the pinned Mathlib API. -/
theorem totalDegree_pderiv_le_pred (i : Fin n)
    (p : MvPolynomial (Fin n) ℝ) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, pderiv_monomial]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  by_cases hsi : s i = 0
  · simp [hsi]
  · calc
      (monomial (s - Finsupp.single i 1) (p.coeff s * ↑(s i))).totalDegree
          ≤ (s - Finsupp.single i 1).sum fun _ e ↦ e :=
        MvPolynomial.totalDegree_monomial_le _ _
      _ ≤ p.totalDegree - 1 := by
        have hsumlt :
            (s - Finsupp.single i 1).sum (fun _ e ↦ e) <
              s.sum (fun _ e ↦ e) := by
          rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl),
            Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
          apply Finset.sum_lt_sum
          · intro j _
            exact Nat.sub_le _ _
          · refine ⟨i, Finset.mem_univ _, ?_⟩
            have hpos : 0 < s i := by omega
            have hsub : s i - 1 < s i := Nat.sub_lt hpos (by omega)
            simpa using hsub
        have hsdeg : s.sum (fun _ e ↦ e) ≤ p.totalDegree :=
          MvPolynomial.le_totalDegree hs
        omega

/-- The infinitesimal coordinate rotation `x_i ∂_j - x_j ∂_i`. -/
def rotationDeriv (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  X i * pderiv j p - X j * pderiv i p
@[simp] theorem rotationDeriv_zero (i j : Fin n) :
    rotationDeriv i j (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  simp [rotationDeriv]

@[simp] theorem rotationDeriv_add (i j : Fin n) (p q : MvPolynomial (Fin n) ℝ) :
    rotationDeriv i j (p + q) = rotationDeriv i j p + rotationDeriv i j q := by
  simp only [rotationDeriv, map_add]
  ring

@[simp] theorem rotationDeriv_neg (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    rotationDeriv i j (-p) = -rotationDeriv i j p := by
  simp only [rotationDeriv, map_neg]
  ring

@[simp] theorem rotationDeriv_smul (i j : Fin n) (c : ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    rotationDeriv i j (c • p) = c • rotationDeriv i j p := by
  simp only [MvPolynomial.smul_eq_C_mul, rotationDeriv, pderiv_mul, pderiv_C, zero_mul,
    zero_add]
  ring

/-- Coordinate rotation derivations preserve the ambient total-degree bound. -/
theorem rotationDeriv_totalDegree_le (i j : Fin n)
    (p : MvPolynomial (Fin n) ℝ) :
    (rotationDeriv i j p).totalDegree ≤ p.totalDegree := by
  by_cases hp : p.totalDegree = 0
  · have hpC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp
    rw [hpC]
    simp [rotationDeriv]
  · have hdegree : 1 ≤ p.totalDegree := by omega
    have hleft :
        (X i * pderiv j p).totalDegree ≤ p.totalDegree := by
      calc
        (X i * pderiv j p).totalDegree
            ≤ (X i : MvPolynomial (Fin n) ℝ).totalDegree +
                (pderiv j p).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ 1 + (p.totalDegree - 1) := by
          rw [MvPolynomial.totalDegree_X]
          exact Nat.add_le_add_left (totalDegree_pderiv_le_pred j p) 1
        _ = p.totalDegree := by omega
    have hright :
        (X j * pderiv i p).totalDegree ≤ p.totalDegree := by
      calc
        (X j * pderiv i p).totalDegree
            ≤ (X j : MvPolynomial (Fin n) ℝ).totalDegree +
                (pderiv i p).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
        _ ≤ 1 + (p.totalDegree - 1) := by
          rw [MvPolynomial.totalDegree_X]
          exact Nat.add_le_add_left (totalDegree_pderiv_le_pred i p) 1
        _ = p.totalDegree := by omega
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le hleft hright)


/-- Coordinate rotations annihilate the defining equation of the sphere. -/
@[simp] theorem rotationDeriv_sphereRelation (i j : Fin n) :
    rotationDeriv i j (sphereRelation n) = 0 := by
  unfold rotationDeriv
  rw [pderiv_sphereRelation, pderiv_sphereRelation]
  ring

/-- Coordinate rotations preserve the ideal generated by the sphere relation. -/
theorem rotationDeriv_relation_mul (i j : Fin n) (a : MvPolynomial (Fin n) ℝ) :
    rotationDeriv i j (sphereRelation n * a) = sphereRelation n * rotationDeriv i j a := by
  unfold rotationDeriv
  simp only [pderiv_mul, pderiv_sphereRelation]
  ring

/-- Applying a coordinate rotation to congruent sphere polynomials preserves congruence. -/
theorem rotationDeriv_add_relation_mul (i j : Fin n) (p a : MvPolynomial (Fin n) ℝ) :
    rotationDeriv i j (p + sphereRelation n * a) =
      rotationDeriv i j p + sphereRelation n * rotationDeriv i j a := by
  unfold rotationDeriv
  simp only [map_add, pderiv_mul, pderiv_sphereRelation]
  ring

/-- The restriction sup norm is unchanged by a multiple of the sphere relation. -/
theorem sphereSupNorm_add_relation_mul (p a : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm (p + sphereRelation n * a) = sphereSupNorm p := by
  unfold sphereSupNorm
  apply congrArg sSup
  apply congrArg (Set.image abs)
  apply Set.image_congr
  intro x hx
  simp [map_add, map_mul, eval_sphereRelation_of_mem hx]

/-- Every multiple of the sphere equation vanishes in the restriction sup seminorm. -/
@[simp] theorem sphereSupNorm_relation_mul (hn : 0 < n)
    (a : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm (sphereRelation n * a) = 0 := by
  have h := sphereSupNorm_add_relation_mul
    (0 : MvPolynomial (Fin n) ℝ) a
  simpa only [zero_add, sphereSupNorm_zero hn] using h

/-- A finite rotation-derivative norm containing all words of length at most `k`.

The recursive sum convention keeps all rotation words of length at most `k`. -/
def sphereRotNorm : ℕ → MvPolynomial (Fin n) ℝ → ℝ
  | 0, p => sphereSupNorm p
  | k + 1, p =>
      sphereRotNorm k p + ∑ i : Fin n, ∑ j : Fin n, sphereRotNorm k (rotationDeriv i j p)

/-- Every rotation norm is nonnegative on a positive-dimensional sphere. -/
theorem sphereRotNorm_nonneg (hn : 0 < n) (k : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    0 ≤ sphereRotNorm k p := by
  induction k generalizing p with
  | zero => exact sphereSupNorm_nonneg hn p
  | succ k ih =>
      exact add_nonneg (ih p)
        (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ih (rotationDeriv i j p))


/-- The zeroth-order sphere sup norm is one of the nonnegative summands in
every iterated rotational norm. -/
theorem sphereSupNorm_le_sphereRotNorm (hn : 0 < n) (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm p ≤ sphereRotNorm k p := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [sphereRotNorm]
      exact ih.trans (le_add_of_nonneg_right
        (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
          sphereRotNorm_nonneg hn k (rotationDeriv i j p)))

/-- Every rotation norm vanishes on the zero polynomial. -/
@[simp] theorem sphereRotNorm_zero (hn : 0 < n) (k : ℕ) :
    sphereRotNorm k (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  induction k with
  | zero => exact sphereSupNorm_zero hn
  | succ k ih =>
      simp [sphereRotNorm, ih]

/-- Triangle inequality for every finite rotation norm. -/
theorem sphereRotNorm_add_le (hn : 0 < n) (k : ℕ)
    (p q : MvPolynomial (Fin n) ℝ) :
    sphereRotNorm k (p + q) ≤ sphereRotNorm k p + sphereRotNorm k q := by
  induction k generalizing p q with
  | zero => exact sphereSupNorm_add_le hn p q
  | succ k ih =>
      simp only [sphereRotNorm, rotationDeriv_add]
      calc
        sphereRotNorm k (p + q) +
              ∑ i : Fin n, ∑ j : Fin n,
                sphereRotNorm k (rotationDeriv i j p + rotationDeriv i j q)
            ≤ (sphereRotNorm k p + sphereRotNorm k q) +
              ∑ i : Fin n, ∑ j : Fin n,
                (sphereRotNorm k (rotationDeriv i j p) +
                  sphereRotNorm k (rotationDeriv i j q)) := by
                apply add_le_add (ih p q)
                apply Finset.sum_le_sum
                intro i _
                apply Finset.sum_le_sum
                intro j _
                exact ih _ _
        _ = (sphereRotNorm k p +
              ∑ i : Fin n, ∑ j : Fin n, sphereRotNorm k (rotationDeriv i j p)) +
            (sphereRotNorm k q +
              ∑ i : Fin n, ∑ j : Fin n, sphereRotNorm k (rotationDeriv i j q)) := by
                simp only [Finset.sum_add_distrib]
                ring

/-- Negation leaves every finite rotation norm unchanged. -/
@[simp] theorem sphereRotNorm_neg (hn : 0 < n) (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ) : sphereRotNorm k (-p) = sphereRotNorm k p := by
  induction k generalizing p with
  | zero => exact sphereSupNorm_neg hn p
  | succ k ih =>
      simp [sphereRotNorm, ih]

/-- Absolute homogeneity of every finite rotation norm. -/
theorem sphereRotNorm_smul (hn : 0 < n) (k : ℕ) (c : ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    sphereRotNorm k (c • p) = |c| * sphereRotNorm k p := by
  induction k generalizing p with
  | zero => exact sphereSupNorm_smul hn c p
  | succ k ih =>
      simp only [sphereRotNorm, rotationDeriv_smul, ih]
      rw [mul_add]
      apply congrArg (|c| * sphereRotNorm k p + ·)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]


/-- Every iterated rotation norm depends only on the restriction to the sphere. -/
theorem sphereRotNorm_add_relation_mul (k : ℕ) (p a : MvPolynomial (Fin n) ℝ) :
    sphereRotNorm k (p + sphereRelation n * a) = sphereRotNorm k p := by
  induction k generalizing p a with
  | zero => exact sphereSupNorm_add_relation_mul p a
  | succ k ih =>
      simp only [sphereRotNorm]
      rw [ih]
      apply congrArg (sphereRotNorm k p + ·)
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [rotationDeriv_add_relation_mul, ih]


/-- The explicit sphere `C⁶` norm used in the formal certificate theorem. -/
def sphereC6Norm (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  sphereRotNorm 6 p

/-- The explicit sphere C6 norm is nonnegative. -/
theorem sphereC6Norm_nonneg (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    0 ≤ sphereC6Norm p :=
  sphereRotNorm_nonneg hn 6 p

@[simp] theorem sphereC6Norm_zero (hn : 0 < n) :
    sphereC6Norm (0 : MvPolynomial (Fin n) ℝ) = 0 :=
  sphereRotNorm_zero hn 6

@[simp] theorem sphereC6Norm_neg (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    sphereC6Norm (-p) = sphereC6Norm p :=
  sphereRotNorm_neg hn 6 p

theorem sphereC6Norm_add_le (hn : 0 < n) (p q : MvPolynomial (Fin n) ℝ) :
    sphereC6Norm (p + q) ≤ sphereC6Norm p + sphereC6Norm q :=
  sphereRotNorm_add_le hn 6 p q

theorem sphereC6Norm_sub_le (hn : 0 < n) (p q : MvPolynomial (Fin n) ℝ) :
    sphereC6Norm (p - q) ≤ sphereC6Norm p + sphereC6Norm q := by
  rw [sub_eq_add_neg]
  exact (sphereC6Norm_add_le hn p (-q)).trans_eq
    (congrArg (sphereC6Norm p + ·) (sphereC6Norm_neg hn q))

theorem sphereC6Norm_smul (hn : 0 < n) (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    sphereC6Norm (c • p) = |c| * sphereC6Norm p :=
  sphereRotNorm_smul hn 6 c p

/-- The explicit rotational C6 quantity is a seminorm, allowing the
finite-dimensional comparison layer to use Mathlib's seminorm API directly. -/
def sphereC6Seminorm (hn : 0 < n) : Seminorm ℝ (MvPolynomial (Fin n) ℝ) :=
  Seminorm.of sphereC6Norm (sphereC6Norm_add_le hn) fun c p ↦ by
    simpa only [Real.norm_eq_abs] using sphereC6Norm_smul hn c p

@[simp] theorem sphereC6Seminorm_apply (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    sphereC6Seminorm hn p = sphereC6Norm p := rfl


/-- The formal `C⁶` norm is independent of the ambient representative modulo the sphere. -/
theorem sphereC6Norm_add_relation_mul (p a : MvPolynomial (Fin n) ℝ) :
    sphereC6Norm (p + sphereRelation n * a) = sphereC6Norm p :=
  sphereRotNorm_add_relation_mul 6 p a

/-- Every multiple of the sphere equation vanishes in the rotational C6 seminorm. -/
@[simp] theorem sphereC6Norm_relation_mul (hn : 0 < n)
    (a : MvPolynomial (Fin n) ℝ) :
    sphereC6Norm (sphereRelation n * a) = 0 := by
  have h := sphereC6Norm_add_relation_mul
    (0 : MvPolynomial (Fin n) ℝ) a
  simpa only [zero_add, sphereC6Norm_zero hn] using h

/-- A sphere SOS certificate implies sphere nonnegativity. -/
theorem SphereSOSMod.sphereNonnegative {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : SphereSOSMod p r) : SphereNonnegative p := by
  intro x hx
  exact hp.nonnegOnSphere hx

end QuarticConvergence
end OptimalConvergenceRates

end
