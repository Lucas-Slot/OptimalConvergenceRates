/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/FiniteDegree.lean

  Finite-dimensional polynomial functions on the sphere.  The codomain stores
  restrictions as functions, so the sphere sup norm is no longer confused with
  a norm on an arbitrary ambient representative.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact

open MvPolynomial

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

/-- Every seminorm on a finite-dimensional real normed space is bounded by the
ambient norm.  This elementary basis estimate is useful when the seminorm is
defined algebraically and continuity has not been packaged separately. -/
theorem seminorm_bound_of_finiteDimensional
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (q : Seminorm ℝ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : V, q x ≤ C * ‖x‖ := by
  classical
  let b := Module.Free.chooseBasis ℝ V
  letI := FiniteDimensional.fintypeBasisIndex b
  let e : V →ₗ[ℝ] (Module.Free.ChooseBasisIndex ℝ V → ℝ) := b.equivFun
  let eCLM : V →L[ℝ] (Module.Free.ChooseBasisIndex ℝ V → ℝ) :=
    ⟨e, e.continuous_of_finiteDimensional⟩
  let S : ℝ := ∑ i, q (b i)
  let C : ℝ := max 1 (S * ‖eCLM‖)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  have hsum (s : Finset (Module.Free.ChooseBasisIndex ℝ V))
      (f : Module.Free.ChooseBasisIndex ℝ V → V) :
      q (∑ i ∈ s, f i) ≤ ∑ i ∈ s, q (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [ha, not_false_eq_true, Finset.sum_insert]
        exact (map_add_le_add q _ _).trans (add_le_add_right ih _)
  calc
    q x = q (∑ i, (b.repr x i) • b i) := by rw [b.sum_repr]
    _ ≤ ∑ i, q ((b.repr x i) • b i) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
        hsum Finset.univ (fun i ↦ (b.repr x i) • b i)
    _ = ∑ i, |b.repr x i| * q (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul_eq_mul, Real.norm_eq_abs]
    _ ≤ ∑ i, ‖eCLM x‖ * q (b i) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right
      · change |(eCLM x) i| ≤ ‖eCLM x‖
        exact norm_le_pi_norm (eCLM x) i
      · exact apply_nonneg q _
    _ = ‖eCLM x‖ * S := by rw [Finset.mul_sum]
    _ ≤ (‖eCLM‖ * ‖x‖) * S := by
      apply mul_le_mul_of_nonneg_right (eCLM.le_opNorm x)
      dsimp only [S]
      positivity
    _ = (S * ‖eCLM‖) * ‖x‖ := by ring
    _ ≤ C * ‖x‖ := by
      dsimp only [C]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg x)

/-- The algebraic sphere carries the compact-space instance used for continuous-function norms. -/
noncomputable instance sphereSetCompactSpace (n : ℕ) : CompactSpace (sphereSet n) :=
  isCompact_iff_compactSpace.mp sphereSet_compact


/-- Restriction/evaluation of ambient polynomials as continuous functions on the sphere. -/
def sphereRestrictionLinear (n : ℕ) :
    MvPolynomial (Fin n) ℝ →ₗ[ℝ] C(sphereSet n, ℝ) where
  toFun p :=
    ⟨fun x ↦ MvPolynomial.eval x.1 p,
      (MvPolynomial.continuous_eval p).comp continuous_subtype_val⟩
  map_add' p q := by
    ext x
    simp
  map_smul' c p := by
    ext x
    simp

@[simp] theorem sphereRestrictionLinear_apply (n : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (x : sphereSet n) :
    sphereRestrictionLinear n p x = MvPolynomial.eval x.1 p := rfl

/-- The ambient sphere sup norm is exactly the genuine norm of the restricted continuous
function. -/
theorem norm_sphereRestrictionLinear_eq (hn : 0 < n)
    (p : MvPolynomial (Fin n) ℝ) :
    ‖sphereRestrictionLinear n p‖ = sphereSupNorm p := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le _ (sphereSupNorm_nonneg hn p)]
    intro x
    simpa [Real.norm_eq_abs] using sphereSupNorm_eval_le p x.1 x.2
  · apply sphereSupNorm_le_of_bound hn
    intro x hx
    simpa [Real.norm_eq_abs] using
      ContinuousMap.norm_coe_le_norm (sphereRestrictionLinear n p) ⟨x, hx⟩

/-- Vanishing of the sphere seminorm is exactly pointwise vanishing on the sphere. -/
theorem sphereSupNorm_eq_zero_iff (hn : 0 < n) (p : MvPolynomial (Fin n) ℝ) :
    sphereSupNorm p = 0 ↔ ∀ x ∈ sphereSet n, MvPolynomial.eval x p = 0 := by
  constructor
  · intro hp x hx
    have h := sphereSupNorm_eval_le p x hx
    rw [hp] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  · intro hp
    apply le_antisymm
    · apply sphereSupNorm_le_of_bound hn
      intro x hx
      simp [hp x hx]
    · exact sphereSupNorm_nonneg hn p


/-- Two ambient polynomials define the same sphere function exactly when their evaluations
agree at every point of the sphere. -/
theorem sphereRestrictionLinear_eq_iff {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    sphereRestrictionLinear n p = sphereRestrictionLinear n q ↔
      ∀ x ∈ sphereSet n, MvPolynomial.eval x p = MvPolynomial.eval x q := by
  constructor
  · intro h x hx
    exact DFunLike.congr_fun h ⟨x, hx⟩
  · intro h
    ext x
    exact h x.1 x.2

/-- Equality of sphere functions is detected by the sup seminorm of the ambient difference. -/
theorem sphereRestrictionLinear_eq_iff_supNorm_sub_eq_zero {n : ℕ} (hn : 0 < n)
    (p q : MvPolynomial (Fin n) ℝ) :
    sphereRestrictionLinear n p = sphereRestrictionLinear n q ↔
      sphereSupNorm (p - q) = 0 := by
  rw [sphereRestrictionLinear_eq_iff, sphereSupNorm_eq_zero_iff hn]
  constructor
  · intro h x hx
    simp [h x hx]
  · intro h x hx
    have hzero := h x hx
    simp only [map_sub] at hzero
    linarith


/-- Multiples of the sphere equation restrict to the zero function. -/
@[simp] theorem sphereRestrictionLinear_relation_mul {n : ℕ}
    (a : MvPolynomial (Fin n) ℝ) :
    sphereRestrictionLinear n (sphereRelation n * a) = 0 := by
  ext x
  simp [eval_sphereRelation_of_mem x.2]

/-- Restriction is unchanged after adding a multiple of the sphere equation. -/
@[simp] theorem sphereRestrictionLinear_add_relation_mul {n : ℕ}
    (p a : MvPolynomial (Fin n) ℝ) :
    sphereRestrictionLinear n (p + sphereRelation n * a) = sphereRestrictionLinear n p := by
  simp

/-- Rotation derivations act internally on ambient polynomials of total degree at most
`D`.  This is the finite-dimensional operator used by the C6 norm and kernel arguments. -/
def restrictedRotationDeriv (D : ℕ) (i j : Fin n) :
    Module.End ℝ (MvPolynomial.restrictTotalDegree (Fin n) ℝ D) where
  toFun p :=
    ⟨rotationDeriv i j p.1,
      (MvPolynomial.mem_restrictTotalDegree (Fin n) D _).mpr
        ((rotationDeriv_totalDegree_le i j p.1).trans
          ((MvPolynomial.mem_restrictTotalDegree (Fin n) D p.1).mp p.2))⟩
  map_add' p q := by
    apply Subtype.ext
    exact rotationDeriv_add i j p.1 q.1
  map_smul' c p := by
    apply Subtype.ext
    exact rotationDeriv_smul i j c p.1

@[simp] theorem restrictedRotationDeriv_apply (D : ℕ) (i j : Fin n)
    (p : MvPolynomial.restrictTotalDegree (Fin n) ℝ D) :
    (restrictedRotationDeriv D i j p).1 = rotationDeriv i j p.1 := rfl

/-- The sphere sup seminorm restricted to ambient degree at most `D`. -/
def restrictedSphereSupSeminorm (hn : 0 < n) (D : ℕ) :
    Seminorm ℝ (MvPolynomial.restrictTotalDegree (Fin n) ℝ D) :=
  (sphereSupSeminorm hn).comp
    (MvPolynomial.restrictTotalDegree (Fin n) ℝ D).subtype

@[simp] theorem restrictedSphereSupSeminorm_apply (hn : 0 < n) (D : ℕ)
    (p : MvPolynomial.restrictTotalDegree (Fin n) ℝ D) :
    restrictedSphereSupSeminorm hn D p = sphereSupNorm p.1 := rfl

/-- The rotational C6 seminorm restricted to ambient degree at most `D`. -/
def restrictedSphereC6Seminorm (hn : 0 < n) (D : ℕ) :
    Seminorm ℝ (MvPolynomial.restrictTotalDegree (Fin n) ℝ D) :=
  (sphereC6Seminorm hn).comp
    (MvPolynomial.restrictTotalDegree (Fin n) ℝ D).subtype

@[simp] theorem restrictedSphereC6Seminorm_apply (hn : 0 < n) (D : ℕ)
    (p : MvPolynomial.restrictTotalDegree (Fin n) ℝ D) :
    restrictedSphereC6Seminorm hn D p = sphereC6Norm p.1 := rfl

/-- The space of sphere restrictions of ambient polynomials of total degree at most `D`. -/
def spherePolynomialSpace (n D : ℕ) : Submodule ℝ C(sphereSet n, ℝ) :=
  (MvPolynomial.restrictTotalDegree (Fin n) ℝ D).map (sphereRestrictionLinear n)

/-- Restriction from bounded-degree ambient representatives onto the actual space of
bounded-degree polynomial functions on the sphere. -/
def boundedSphereRestriction (n D : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin n) ℝ D →ₗ[ℝ]
      spherePolynomialSpace n D where
  toFun p :=
    ⟨sphereRestrictionLinear n p.1, by
      exact ⟨p.1, p.2, rfl⟩⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (sphereRestrictionLinear n) p.1 q.1
  map_smul' c p := by
    apply Subtype.ext
    exact map_smul (sphereRestrictionLinear n) c p.1

@[simp] theorem boundedSphereRestriction_apply (n D : ℕ)
    (p : MvPolynomial.restrictTotalDegree (Fin n) ℝ D) :
    (boundedSphereRestriction n D p).1 = sphereRestrictionLinear n p.1 := rfl

/-- Every bounded-degree polynomial function has a bounded-degree ambient
representative. -/
theorem boundedSphereRestriction_surjective (n D : ℕ) :
    Function.Surjective (boundedSphereRestriction n D) := by
  intro F
  rcases F.2 with ⟨p, hp, hrestr⟩
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  exact hrestr

/-- A noncomputably chosen linear bounded-degree representative of each sphere
polynomial function. This is a right inverse to bounded restriction. -/
noncomputable def boundedSphereRepresentative (n D : ℕ) :
    spherePolynomialSpace n D →ₗ[ℝ]
      MvPolynomial.restrictTotalDegree (Fin n) ℝ D :=
  Classical.choose <|
    (boundedSphereRestriction n D).exists_rightInverse_of_surjective <|
      LinearMap.range_eq_top.mpr (boundedSphereRestriction_surjective n D)

@[simp] theorem boundedSphereRestriction_boundedSphereRepresentative
    (n D : ℕ) (v : spherePolynomialSpace n D) :
    boundedSphereRestriction n D (boundedSphereRepresentative n D v) = v := by
  have h :=
    Classical.choose_spec <|
      (boundedSphereRestriction n D).exists_rightInverse_of_surjective <|
        LinearMap.range_eq_top.mpr (boundedSphereRestriction_surjective n D)
  exact LinearMap.congr_fun h v

/-- Membership in the bounded-degree sphere polynomial space is represented by an ambient
polynomial with the same degree bound. -/
theorem mem_spherePolynomialSpace_iff {n D : ℕ} (F : C(sphereSet n, ℝ)) :
    F ∈ spherePolynomialSpace n D ↔
      ∃ p : MvPolynomial (Fin n) ℝ,
        p.totalDegree ≤ D ∧ sphereRestrictionLinear n p = F := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) D p).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) D p).mpr hp, rfl⟩

/-- Constant functions belong to every bounded-degree sphere polynomial space. -/
def spherePolynomialConst (n D : ℕ) (c : ℝ) : spherePolynomialSpace n D :=
  ⟨ContinuousMap.const (sphereSet n) c, by
    rw [mem_spherePolynomialSpace_iff]
    refine ⟨MvPolynomial.C c, by simp, ?_⟩
    ext x
    simp⟩

@[simp] theorem spherePolynomialConst_apply (n D : ℕ) (c : ℝ)
    (x : sphereSet n) :
    (spherePolynomialConst n D c).1 x = c := rfl

@[simp] theorem spherePolynomialConst_zero (n D : ℕ) :
    spherePolynomialConst n D 0 = 0 := by
  apply Subtype.ext
  ext x
  simp [spherePolynomialConst]

@[simp] theorem spherePolynomialConst_add (n D : ℕ) (a b : ℝ) :
    spherePolynomialConst n D (a + b) =
      spherePolynomialConst n D a + spherePolynomialConst n D b := by
  apply Subtype.ext
  ext x
  simp [spherePolynomialConst]

@[simp] theorem spherePolynomialConst_smul (n D : ℕ) (a b : ℝ) :
    spherePolynomialConst n D (a * b) =
      a • spherePolynomialConst n D b := by
  apply Subtype.ext
  ext x
  simp [spherePolynomialConst]

/-- The bounded-degree sphere polynomial space is finite-dimensional. -/
instance spherePolynomialSpace_finiteDimensional (n D : ℕ) :
    FiniteDimensional ℝ (spherePolynomialSpace n D) :=
  Module.Finite.map (MvPolynomial.restrictTotalDegree (Fin n) ℝ D)
    (sphereRestrictionLinear n)

/-- An injective operator on the bounded-degree sphere polynomial space is surjective. -/
theorem spherePolynomialEnd_surjective {n D : ℕ}
    (T : Module.End ℝ (spherePolynomialSpace n D))
    (hT : Function.Injective T) : Function.Surjective T :=
  LinearMap.surjective_of_injective hT

end QuarticConvergence
end OptimalConvergenceRates

end
