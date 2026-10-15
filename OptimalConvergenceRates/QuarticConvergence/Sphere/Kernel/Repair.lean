/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/Repair.lean

  Finite-dimensional near-identity repair lemmas for positive spherical kernel operators.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.FiniteDegree
import OptimalConvergenceRates.QuarticConvergence.Sphere.SphereIdeal
import OptimalConvergenceRates.QuarticConvergence.Sphere.Assembly
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.TrigDerivative
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.PolynomialMoments
import OptimalConvergenceRates.QuarticConvergence.Sphere.Kernel.Cancellation
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Normed.Module.Normalize

noncomputable section
open MeasureTheory
open scoped Pointwise

namespace OptimalConvergenceRates
namespace QuarticConvergence

section NearIdentity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A linear endomorphism whose error is strictly smaller than every nonzero input is
injective. -/
theorem linearEnd_injective_of_norm_sub_lt (T : Module.End ℝ V)
    (hT : ∀ v, v ≠ 0 → ‖v - T v‖ < ‖v‖) : Function.Injective T := by
  intro x y hxy
  by_contra hne
  have hv : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hstrict := hT (x - y) hv
  have hzero : T (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [hzero, sub_zero] at hstrict
  exact (lt_irrefl ‖x - y‖) hstrict

/-- The usual operator-error estimate with constant below one implies injectivity. -/
theorem linearEnd_injective_of_error_le (T : Module.End ℝ V) (c : ℝ) (hc : c < 1)
    (hT : ∀ v, ‖v - T v‖ ≤ c * ‖v‖) : Function.Injective T := by
  apply linearEnd_injective_of_norm_sub_lt T
  intro v hv
  calc
    ‖v - T v‖ ≤ c * ‖v‖ := hT v
    _ < 1 * ‖v‖ := mul_lt_mul_of_pos_right hc (norm_pos_iff.mpr hv)
    _ = ‖v‖ := one_mul _

/-- In finite dimension, a near-identity endomorphism is onto; no Neumann-series
construction is needed. -/
theorem linearEnd_surjective_of_error_le [FiniteDimensional ℝ V]
    (T : Module.End ℝ V) (c : ℝ) (hc : c < 1)
    (hT : ∀ v, ‖v - T v‖ ≤ c * ‖v‖) : Function.Surjective T :=
  LinearMap.surjective_of_injective (linearEnd_injective_of_error_le T c hc hT)
/-- A finite-dimensional near-identity map has a preimage whose norm is controlled by
1 / (1-c). -/
theorem linearEnd_exists_preimage_norm_le [FiniteDimensional ℝ V]
    (T : Module.End ℝ V) (c : ℝ) (hc : c < 1)
    (hT : ∀ v, ‖v - T v‖ ≤ c * ‖v‖) (y : V) :
    ∃ x : V, T x = y ∧ ‖x‖ ≤ ‖y‖ / (1 - c) := by
  obtain ⟨x, hx⟩ := linearEnd_surjective_of_error_le T c hc hT y
  refine ⟨x, hx, ?_⟩
  have hnorm : ‖x‖ ≤ c * ‖x‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - T x) + T x‖ := by
        congr 1
        abel
      _ ≤ ‖x - T x‖ + ‖T x‖ := norm_add_le _ _
      _ ≤ c * ‖x‖ + ‖T x‖ := add_le_add (hT x) le_rfl
      _ = c * ‖x‖ + ‖y‖ := by rw [hx]
  apply (le_div_iff₀ (sub_pos.mpr hc)).2
  nlinarith

/-- The same preimage differs from the target by at most c / (1-c) times the
target norm. -/
theorem linearEnd_exists_preimage_correction_le [FiniteDimensional ℝ V]
    (T : Module.End ℝ V) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hT : ∀ v, ‖v - T v‖ ≤ c * ‖v‖) (y : V) :
    ∃ x : V, T x = y ∧
      ‖x‖ ≤ ‖y‖ / (1 - c) ∧ ‖x - y‖ ≤ c / (1 - c) * ‖y‖ := by
  obtain ⟨x, hx, hxnorm⟩ := linearEnd_exists_preimage_norm_le T c hc1 hT y
  refine ⟨x, hx, hxnorm, ?_⟩
  calc
    ‖x - y‖ = ‖x - T x‖ := by rw [hx]
    _ ≤ c * ‖x‖ := hT x
    _ ≤ c * (‖y‖ / (1 - c)) := mul_le_mul_of_nonneg_left hxnorm hc0
    _ = c / (1 - c) * ‖y‖ := by ring

end NearIdentity
open SphereBallTransfers
open SpherePolynomialQuadrature

/-- A bounded-degree sphere function has an SOS certificate at root degree `R` if one
ambient representative has a certificate using the repository-wide `SphereSOSMod`
definition. -/
def SpherePolynomialSOS {n D : ℕ} (v : spherePolynomialSpace n D) (R : ℕ) : Prop :=
  ∃ p : MvPolynomial (Fin n) ℝ,
    SphereSOSMod p R ∧ sphereRestrictionLinear n p = v.1
namespace SpherePolynomialSOS

/-- Raising the root-degree bound preserves a certificate for a sphere polynomial
function. -/
theorem mono {n D R S : ℕ} {v : spherePolynomialSpace n D}
    (hRS : R ≤ S) (hv : SpherePolynomialSOS v R) : SpherePolynomialSOS v S := by
  obtain ⟨p, hp, hpv⟩ := hv
  exact ⟨p, hp.mono hRS, hpv⟩

/-- The zero sphere polynomial function has a certificate at every order. -/
theorem zero (n D R : ℕ) :
    SpherePolynomialSOS (0 : spherePolynomialSpace n D) R := by
  refine ⟨0, sphereSOSMod_zero n R, ?_⟩
  simp

/-- Nonnegative constant sphere polynomial functions have certificates at every order. -/
theorem const {n D R : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    SpherePolynomialSOS (spherePolynomialConst n D c) R := by
  refine ⟨MvPolynomial.C c, sphereSOSMod_const hc, ?_⟩
  ext x
  simp

/-- Function-level sphere SOS certificates are closed under addition. -/
theorem add {n D R : ℕ} {v w : spherePolynomialSpace n D}
    (hv : SpherePolynomialSOS v R) (hw : SpherePolynomialSOS w R) :
    SpherePolynomialSOS (v + w) R := by
  obtain ⟨p, hp, hpv⟩ := hv
  obtain ⟨q, hq, hqw⟩ := hw
  refine ⟨p + q, hp.add hq, ?_⟩
  rw [map_add, hpv, hqw]
  rfl

/-- Function-level sphere SOS certificates are closed under multiplication by a
nonnegative scalar. -/
theorem nonneg_smul {n D R : ℕ} {v : spherePolynomialSpace n D}
    (hv : SpherePolynomialSOS v R) {c : ℝ} (hc : 0 ≤ c) :
    SpherePolynomialSOS (c • v) R := by
  obtain ⟨p, hp, hpv⟩ := hv
  refine ⟨MvPolynomial.C c * p, hp.nonneg_scale hc, ?_⟩
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, hpv]
  rfl

end SpherePolynomialSOS
/-- Algebraic completeness of the defining sphere equation: every ambient polynomial
whose restriction vanishes is a multiple of `sphereRelation`.  This is the precise
bridge between polynomial functions on the sphere and ambient certificates modulo the
sphere equation. -/
def SphereRestrictionKernelPrincipal (n : ℕ) : Prop :=
  ∀ p : MvPolynomial (Fin n) ℝ,
    sphereRestrictionLinear n p = 0 →
      ∃ a : MvPolynomial (Fin n) ℝ, p = sphereRelation n * a

/-- Under algebraic completeness of the sphere relation, a function-level certificate
can be transferred to any ambient representative of that function. -/
theorem SpherePolynomialSOS.toSphereSOSMod
    {n D R : ℕ} (hkernel : SphereRestrictionKernelPrincipal n)
    {v : spherePolynomialSpace n D} (hv : SpherePolynomialSOS v R)
    (p : MvPolynomial (Fin n) ℝ) (hpv : sphereRestrictionLinear n p = v.1) :
    SphereSOSMod p R := by
  obtain ⟨q, hq, hqv⟩ := hv
  have hzero : sphereRestrictionLinear n (p - q) = 0 := by
    rw [map_sub, hpv, hqv, sub_self]
  obtain ⟨a, ha⟩ := hkernel (p - q) hzero
  have hp : p = q + sphereRelation n * a := by
    calc
      p = (p - q) + q := by ring
      _ = sphereRelation n * a + q := by rw [ha]
      _ = q + sphereRelation n * a := add_comm _ _
  rw [hp]
  exact hq.add_relation_mul a
/-- Quantitative finite-dimensional repair for any contraction factor below one.  The
additive safety margin is the sharp preimage bound supplied by the elementary
injectivity-surjectivity argument. -/
theorem spherePolynomial_repair_of_error_le
    {n D R : ℕ} {c : ℝ}
    (K : Module.End ℝ (spherePolynomialSpace n D))
    (hc : c < 1)
    (hfix : K (spherePolynomialConst n D 1) = spherePolynomialConst n D 1)
    (hnear : ∀ v, ‖v - K v‖ ≤ c * ‖v‖)
    (hpositive : ∀ v : spherePolynomialSpace n D,
      (∀ x : sphereSet n, 0 ≤ v.1 x) → SpherePolynomialSOS (K v) R)
    (h : spherePolynomialSpace n D) :
    SpherePolynomialSOS
      (h + spherePolynomialConst n D (‖h‖ / (1 - c))) R := by
  obtain ⟨w, hw, hwnorm⟩ :=
    linearEnd_exists_preimage_norm_le K c hc hnear h
  let B : ℝ := ‖h‖ / (1 - c)
  have hwnorm' : ‖w‖ ≤ B := by
    simpa only [B] using hwnorm
  let v := w + spherePolynomialConst n D B
  have hvnonnegative : ∀ x : sphereSet n, 0 ≤ v.1 x := by
    intro x
    have hwpoint : |w.1 x| ≤ ‖w‖ := by
      simpa only [Real.norm_eq_abs, Submodule.norm_coe] using
        ContinuousMap.norm_coe_le_norm w.1 x
    have hwlower : -‖w‖ ≤ w.1 x := neg_le_of_abs_le hwpoint
    change 0 ≤ w.1 x + B
    linarith
  have hconst :
      spherePolynomialConst n D B =
        B • spherePolynomialConst n D 1 := by
    simpa using spherePolynomialConst_smul n D B 1
  have hKv :
      K v = h + spherePolynomialConst n D B := by
    calc
      K v = K w + K (spherePolynomialConst n D B) := by
        simp only [v, map_add]
      _ = h + spherePolynomialConst n D B := by
        rw [hw, hconst, map_smul, hfix, ← hconst]
  have hvSOS := hpositive v hvnonnegative
  simpa only [B] using hKv ▸ hvSOS

/-- Finite-dimensional repair on the space of polynomial functions on the sphere. A
half-contraction from the identity, preservation of constants, and positivity-to-SOS
mapping imply that adding `2 * ‖h‖∞` repairs every input. -/
theorem spherePolynomial_repair
    {n D R : ℕ}
    (K : Module.End ℝ (spherePolynomialSpace n D))
    (hfix : K (spherePolynomialConst n D 1) = spherePolynomialConst n D 1)
    (hnear : ∀ v, ‖v - K v‖ ≤ (1 / 2 : ℝ) * ‖v‖)
    (hpositive : ∀ v : spherePolynomialSpace n D,
      (∀ x : sphereSet n, 0 ≤ v.1 x) → SpherePolynomialSOS (K v) R)
    (h : spherePolynomialSpace n D) :
    SpherePolynomialSOS
      (h + spherePolynomialConst n D (2 * ‖h‖)) R := by
  have hgeneral :=
    spherePolynomial_repair_of_error_le K (c := (1 / 2 : ℝ))
      (by norm_num) hfix hnear hpositive h
  convert hgeneral using 1
  ring_nf
/-- Concrete kernel formulation of degree-linear repair on polynomial functions on the
sphere. -/
def HasSpherePolynomialKernelRepair {n : ℕ} (A : ℕ) : Prop :=
  ∀ D : ℕ, 1 ≤ D →
    ∃ K : Module.End ℝ (spherePolynomialSpace n D),
      K (spherePolynomialConst n D 1) = spherePolynomialConst n D 1 ∧
      (∀ v, ‖v - K v‖ ≤ (1 / 2 : ℝ) * ‖v‖) ∧
      ∀ v : spherePolynomialSpace n D,
        (∀ x : sphereSet n, 0 ≤ v.1 x) →
          SpherePolynomialSOS (K v) (A * D)
/-- The quantitative interface for normalized polynomial-square kernels. The operator at
bandwidth `k` preserves constants,
has relative error `C D² / k²` on `Π_D`, and maps nonnegative inputs to
sphere SOS certificates at root degree `p k`. -/
def HasPositiveSphereKernelEstimates {n : ℕ} (p : ℕ) (C : ℝ) : Prop :=
  ∀ D k : ℕ, 1 ≤ D → 1 ≤ k →
    ∃ K : Module.End ℝ (spherePolynomialSpace n D),
      K (spherePolynomialConst n D 1) = spherePolynomialConst n D 1 ∧
      (∀ v, ‖v - K v‖ ≤
        (C * (D : ℝ) ^ 2 / (k : ℝ) ^ 2) * ‖v‖) ∧
      ∀ v : spherePolynomialSpace n D,
        (∀ x : sphereSet n, 0 ≤ v.1 x) →
          SpherePolynomialSOS (K v) (p * k)

/-- Evaluation at the chosen quadrature nodes, as a linear map on bounded-degree
sphere polynomial functions. -/
noncomputable def sphereSamplingLinear {n D N : ℕ}
    (y : Fin N → Fin n → ℝ) (hy : ∀ i, y i ∈ sphereSet n) :
    spherePolynomialSpace n D →ₗ[ℝ] (Fin N → ℝ) where
  toFun v i := v.1 ⟨y i, hy i⟩
  map_add' v z := by
    ext i
    rfl
  map_smul' c v := by
    ext i
    rfl

/-- The ambient polynomial obtained by sampling a sphere polynomial and applying
the finite positive zonal-kernel transform. -/
noncomputable def finiteZonalSpherePolynomialMap {n D N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (hy : ∀ i, y i ∈ sphereSet n) :
    spherePolynomialSpace n D →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  (finiteZonalKernelOperator p k w y).comp (sphereSamplingLinear y hy)

@[simp] theorem finiteZonalSpherePolynomialMap_apply {n D N : ℕ}
    (p k : ℕ) (w : Fin N → ℝ) (y : Fin N → Fin n → ℝ)
    (hy : ∀ i, y i ∈ sphereSet n) (v : spherePolynomialSpace n D) :
    finiteZonalSpherePolynomialMap p k w y hy v =
      finiteZonalKernelOperator p k w y (fun i ↦ v.1 ⟨y i, hy i⟩) := rfl

/-- A fixed exact positive quadrature, chosen noncomputably at each requested
polynomial degree. -/
noncomputable def chosenSpherePolynomialQuadrature (n L : ℕ) (hn : 0 < n) :
    Σ N : ℕ, SpherePolynomialQuadrature n L N := by
  let N := Classical.choose (SpherePolynomialQuadrature.exists_exact n L hn)
  have hQ := Classical.choose_spec
    (SpherePolynomialQuadrature.exists_exact n L hn)
  exact ⟨N, Classical.choice hQ⟩

/-- A concrete ambient-polynomial representative of the normalized continuous
zonal-kernel operator. Exact quadrature is used only to integrate its finitely
many polynomial coefficients. -/
noncomputable def continuousZonalKernelPolynomialMap
    (n D p k : ℕ) (hn : 0 < n) (base : sphereSet n) :
    spherePolynomialSpace n D →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  let Q := (chosenSpherePolynomialQuadrature n (D + 2 * (p * k)) hn).2
  finiteZonalSpherePolynomialMap p k
    (fun i ↦ Q.weight i / continuousZonalKernelMass p k base.1)
    Q.coordinates Q.coordinates_mem_sphereSet

/-- Evaluation of the chosen polynomial representative is exactly the
normalized continuous kernel integral. -/
theorem eval_continuousZonalKernelPolynomialMap
    {n D : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (v : spherePolynomialSpace n D) (x : Fin n → ℝ) :
    MvPolynomial.eval x (continuousZonalKernelPolynomialMap n D p k hn base v) =
      (∫ y : sphereSet n, v.1 y *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n) /
        continuousZonalKernelMass p k base.1 := by
  let Q := (chosenSpherePolynomialQuadrature n (D + 2 * (p * k)) hn).2
  change MvPolynomial.eval x
      (finiteZonalKernelOperator p k
        (fun i ↦ Q.weight i / continuousZonalKernelMass p k base.1)
        Q.coordinates (fun i ↦ v.1 (Q.node i))) = _
  exact Q.eval_finiteZonalKernelOperator_div_eq_integral p k le_rfl
    (continuousZonalKernelMass p k base.1) v x

/-- Before the harmonic degree-preservation argument, the chosen representative
has the immediate ambient degree bound supplied by its kernel sections. -/
theorem continuousZonalKernelPolynomialMap_totalDegree_le
    {n D : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (v : spherePolynomialSpace n D) :
    (continuousZonalKernelPolynomialMap n D p k hn base v).totalDegree ≤
      2 * (p * k) := by
  let Q := (chosenSpherePolynomialQuadrature n (D + 2 * (p * k)) hn).2
  change (finiteZonalKernelOperator p k
    (fun i ↦ Q.weight i / continuousZonalKernelMass p k base.1)
      Q.coordinates (fun i ↦ v.1 (Q.node i))).totalDegree ≤ _
  exact finiteZonalKernelOperator_totalDegree_le' p k _ _ _

/-- Choose a degree-D ambient representative, linearly, for the output of an
endomorphism of degree-D sphere polynomial functions. -/
noncomputable def boundedAmbientMapOfSphereEnd {n D : ℕ}
    (K : Module.End ℝ (spherePolynomialSpace n D)) :
    spherePolynomialSpace n D →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  (MvPolynomial.restrictTotalDegree (Fin n) ℝ D).subtype.comp
    ((boundedSphereRepresentative n D).comp K)

/-- The chosen ambient representative has the requested total-degree bound. -/
theorem boundedAmbientMapOfSphereEnd_totalDegree_le {n D : ℕ}
    (K : Module.End ℝ (spherePolynomialSpace n D))
    (v : spherePolynomialSpace n D) :
    (boundedAmbientMapOfSphereEnd K v).totalDegree ≤ D :=
  (MvPolynomial.mem_restrictTotalDegree (Fin n) D _).mp
    (boundedSphereRepresentative n D (K v)).2

/-- Choosing a representative does not change the underlying sphere function. -/
@[simp] theorem sphereRestriction_boundedAmbientMapOfSphereEnd {n D : ℕ}
    (K : Module.End ℝ (spherePolynomialSpace n D))
    (v : spherePolynomialSpace n D) :
    sphereRestrictionLinear n (boundedAmbientMapOfSphereEnd K v) = (K v).1 := by
  change sphereRestrictionLinear n
    (boundedSphereRepresentative n D (K v)).1 = (K v).1
  exact congrArg Subtype.val (boundedSphereRestriction_boundedSphereRepresentative n D (K v))
/-- Constancy of the continuous kernel mass makes the concrete normalized
polynomial map reproduce the constant-one sphere function. -/
theorem sphereRestriction_continuousZonalKernelPolynomialMap_one
    {n D : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n)
    (hmass : ∀ x ∈ sphereSet n,
      continuousZonalKernelMass p k x =
        continuousZonalKernelMass p k base.1) :
    sphereRestrictionLinear n
        (continuousZonalKernelPolynomialMap n D p k hn base
          (spherePolynomialConst n D 1)) =
      (spherePolynomialConst n D 1).1 := by
  ext x
  rw [sphereRestrictionLinear_apply]
  rw [eval_continuousZonalKernelPolynomialMap]
  simp only [spherePolynomialConst_apply, one_mul]
  change continuousZonalKernelMass p k x.1 /
      continuousZonalKernelMass p k base.1 = 1
  rw [hmass x.1 x.2, div_self]
  exact (continuousZonalKernelMass_pos hn p k base.1 base.2).ne'

/-- Under the same mass-constancy hypothesis, the normalized operator
reproduces every constant sphere polynomial, not only the unit constant. -/
theorem sphereRestriction_continuousZonalKernelPolynomialMap_const
    {n D : ℕ} (hn : 0 < n) (p k : ℕ) (base : sphereSet n) (c : ℝ)
    (hmass : ∀ x ∈ sphereSet n,
      continuousZonalKernelMass p k x =
        continuousZonalKernelMass p k base.1) :
    sphereRestrictionLinear n
        (continuousZonalKernelPolynomialMap n D p k hn base
          (spherePolynomialConst n D c)) =
      (spherePolynomialConst n D c).1 := by
  have hone :=
    sphereRestriction_continuousZonalKernelPolynomialMap_one
      (D := D) hn p k base hmass
  have hconst :
      spherePolynomialConst n D c =
        c • spherePolynomialConst n D 1 := by
    simpa using spherePolynomialConst_smul n D c 1
  rw [hconst, map_smul, map_smul, hone]
  rfl

/-- Continuous normalized-kernel data before moment discretization.  The
bounded map records preservation of the degree filtration, while `eval_eq`
identifies it with the normalized integral operator on the sphere. -/
structure ContinuousPositiveSphereKernelData
    (n D p k : ℕ) (c : ℝ) where
  Z : ℝ
  Z_pos : 0 < Z
  mass : ∀ x ∈ sphereSet n,
    continuousZonalKernelMass p k x = Z
  boundedMap :
    spherePolynomialSpace n D →ₗ[ℝ] MvPolynomial (Fin n) ℝ
  boundedMap_degree : ∀ v : spherePolynomialSpace n D,
    (boundedMap v).totalDegree ≤ D
  eval_eq : ∀ (v : spherePolynomialSpace n D) (x : Fin n → ℝ),
    x ∈ sphereSet n →
      MvPolynomial.eval x (boundedMap v) =
        (∫ y : sphereSet n, v.1 y *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
            ∂normalizedSphereMeasure n) / Z
  near : ∀ v : spherePolynomialSpace n D,
    ‖v.1 - sphereRestrictionLinear n (boundedMap v)‖ ≤ c * ‖v‖

/-- Continuous kernel data before positivity of its common mass is packaged.
The base point records the normalization mass; strict positivity is proved
from the full support of normalized sphere measure rather than assumed. -/
structure ContinuousPositiveSphereKernelCandidate
    (n D p k : ℕ) (c : ℝ) where
  base : sphereSet n
  mass : ∀ x ∈ sphereSet n,
    continuousZonalKernelMass p k x =
      continuousZonalKernelMass p k base.1
  boundedMap :
    spherePolynomialSpace n D →ₗ[ℝ] MvPolynomial (Fin n) ℝ
  boundedMap_degree : ∀ v : spherePolynomialSpace n D,
    (boundedMap v).totalDegree ≤ D
  eval_eq : ∀ (v : spherePolynomialSpace n D) (x : Fin n → ℝ),
    x ∈ sphereSet n →
      MvPolynomial.eval x (boundedMap v) =
        (∫ y : sphereSet n, v.1 y *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
            ∂normalizedSphereMeasure n) /
          continuousZonalKernelMass p k base.1
  near : ∀ v : spherePolynomialSpace n D,
    ‖v.1 - sphereRestrictionLinear n (boundedMap v)‖ ≤ c * ‖v‖

/-- Build continuous candidate data from a strong pointwise chordal increment
bound and a normalized
chordal second-moment bound. -/
noncomputable def ContinuousPositiveSphereKernelCandidate.ofChordalSq
    {n D p k : ℕ} {A B : ℝ} (hn : 0 < n) (hA : 0 ≤ A)
    (base : sphereSet n)
    (mass : ∀ x ∈ sphereSet n,
      continuousZonalKernelMass p k x =
        continuousZonalKernelMass p k base.1)
    (boundedMap :
      spherePolynomialSpace n D →ₗ[ℝ] MvPolynomial (Fin n) ℝ)
    (boundedMap_degree : ∀ v : spherePolynomialSpace n D,
      (boundedMap v).totalDegree ≤ D)
    (eval_eq : ∀ (v : spherePolynomialSpace n D) (x : Fin n → ℝ),
      x ∈ sphereSet n →
        MvPolynomial.eval x (boundedMap v) =
          (∫ y : sphereSet n, v.1 y *
            MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
              ∂normalizedSphereMeasure n) /
            continuousZonalKernelMass p k base.1)
    (increment : ∀ (v : spherePolynomialSpace n D) (x : Fin n → ℝ)
      (hx : x ∈ sphereSet n) (y : sphereSet n),
        |v.1 y - v.1 ⟨x, hx⟩| ≤
          (A * ‖v‖) * sphereChordalSq y.1 x)
    (secondMoment : ∀ x ∈ sphereSet n,
      continuousZonalKernelSecondMoment p k x /
        continuousZonalKernelMass p k base.1 ≤ B) :
    ContinuousPositiveSphereKernelCandidate n D p k (A * B) where
  base := base
  mass := mass
  boundedMap := boundedMap
  boundedMap_degree := boundedMap_degree
  eval_eq := eval_eq
  near := norm_sub_sphereRestrictionLinear_le_of_chordalSq
    hn p k (continuousZonalKernelMass p k base.1) A B hA boundedMap
      mass eval_eq increment secondMoment

/-- Analytic inputs before the standard integration argument combines them.
This separates degree preservation and mass invariance from the integrated
second-order cancellation and Dirichlet-kernel localization estimates. -/
structure ContinuousPositiveSphereKernelLocalization
    (n D p k : ℕ) (A B : ℝ) where
  hn : 0 < n
  base : sphereSet n
  mass : ∀ x ∈ sphereSet n,
    continuousZonalKernelMass p k x =
      continuousZonalKernelMass p k base.1
  boundedMap_degree : ∀ v : spherePolynomialSpace n D,
    (continuousZonalKernelPolynomialMap n D p k hn base v).totalDegree ≤ D
  integralRemainder : ∀ (v : spherePolynomialSpace n D)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n),
      |∫ y : sphereSet n, (v.1 y - v.1 ⟨x, hx⟩) *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n| ≤
        (A * ‖v‖) * continuousZonalKernelSecondMoment p k x
  secondMoment : ∀ x ∈ sphereSet n,
    continuousZonalKernelSecondMoment p k x /
      continuousZonalKernelMass p k base.1 ≤ B

/-- Symmetric-localization inputs. The first-order term is exposed through the
axial-reflection symmetric second difference; the integration argument converting it to
`integralRemainder` is proved separately. -/
structure ContinuousPositiveSphereKernelSymmetricLocalization
    (n D p k : ℕ) (A B : ℝ) where
  hn : 0 < n
  base : sphereSet n
  mass : ∀ x ∈ sphereSet n,
    continuousZonalKernelMass p k x =
      continuousZonalKernelMass p k base.1
  range_mem : ∀ v : spherePolynomialSpace n D,
    sphereRestrictionLinear n (continuousZonalKernelPolynomialMap n D p k hn base v) ∈
      spherePolynomialSpace n D
  symmetricIncrement : ∀ (v : spherePolynomialSpace n D)
    (x : Fin n → ℝ) (hx : x ∈ sphereSet n) (y : sphereSet n),
      |v.1 y + v.1 (sphereAxialReflection ⟨x, hx⟩ y) -
        2 * v.1 ⟨x, hx⟩| ≤
        (2 * (A * ‖v‖)) * sphereChordalSq y.1 x
  secondMoment : ∀ x ∈ sphereSet n,
    continuousZonalKernelSecondMoment p k x /
      continuousZonalKernelMass p k base.1 ≤ B

/-- The continuous kernel restriction, packaged as an endomorphism of Π_D(S). -/
noncomputable def ContinuousPositiveSphereKernelSymmetricLocalization.sphereEnd
    {n D p k : ℕ} {A B : ℝ}
    (S : ContinuousPositiveSphereKernelSymmetricLocalization n D p k A B) :
    Module.End ℝ (spherePolynomialSpace n D) where
  toFun v :=
    ⟨sphereRestrictionLinear n
        (continuousZonalKernelPolynomialMap n D p k S.hn S.base v),
      S.range_mem v⟩
  map_add' v w := by
    apply Subtype.ext
    simp
  map_smul' c v := by
    apply Subtype.ext
    simp

/-- The chosen degree-D representative evaluates to the normalized continuous
kernel integral. -/
theorem eval_boundedAmbientMapOfSymmetricLocalization
    {n D p k : ℕ} {A B : ℝ}
    (S : ContinuousPositiveSphereKernelSymmetricLocalization n D p k A B)
    (v : spherePolynomialSpace n D) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n) :
    MvPolynomial.eval x (boundedAmbientMapOfSphereEnd S.sphereEnd v) =
      (∫ y : sphereSet n, v.1 y *
        MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
          ∂normalizedSphereMeasure n) /
        continuousZonalKernelMass p k S.base.1 := by
  have h := DFunLike.congr_fun
    (sphereRestriction_boundedAmbientMapOfSphereEnd S.sphereEnd v) ⟨x, hx⟩
  change MvPolynomial.eval x (boundedAmbientMapOfSphereEnd S.sphereEnd v) =
    MvPolynomial.eval x
      (continuousZonalKernelPolynomialMap n D p k S.hn S.base v) at h
  rw [eval_continuousZonalKernelPolynomialMap] at h
  exact h

/-- Axial-reflection pairing and the linear representative section convert the
symmetric-localization data into a bounded-degree candidate. -/
noncomputable def
    ContinuousPositiveSphereKernelSymmetricLocalization.toCandidate
    {n D p k : ℕ} {A B : ℝ}
    (S : ContinuousPositiveSphereKernelSymmetricLocalization n D p k A B)
    (hA : 0 ≤ A) :
    ContinuousPositiveSphereKernelCandidate n D p k (A * B) where
  base := S.base
  mass := S.mass
  boundedMap := boundedAmbientMapOfSphereEnd S.sphereEnd
  boundedMap_degree := boundedAmbientMapOfSphereEnd_totalDegree_le S.sphereEnd
  eval_eq := eval_boundedAmbientMapOfSymmetricLocalization S
  near := norm_sub_sphereRestrictionLinear_le_of_integralRemainder
    S.hn p k (continuousZonalKernelMass p k S.base.1) A B hA
      (boundedAmbientMapOfSphereEnd S.sphereEnd) S.mass
      (eval_boundedAmbientMapOfSymmetricLocalization S)
      (fun v x hx ↦
        abs_integral_kernel_increment_le_of_symmetricIncrement
          S.hn p k A v ⟨x, hx⟩ (S.symmetricIncrement v x hx))
      S.secondMoment
/-- The universal normalized second-moment bound supplies localization data
with constant four whenever the other analytic fields are available. -/
noncomputable def ContinuousPositiveSphereKernelLocalization.ofCrudeMoment
    {n D p k : ℕ} {A : ℝ} (hn : 0 < n) (base : sphereSet n)
    (mass : ∀ x ∈ sphereSet n,
      continuousZonalKernelMass p k x =
        continuousZonalKernelMass p k base.1)
    (boundedMap_degree : ∀ v : spherePolynomialSpace n D,
      (continuousZonalKernelPolynomialMap n D p k hn base v).totalDegree ≤ D)
    (integralRemainder : ∀ (v : spherePolynomialSpace n D)
      (x : Fin n → ℝ) (hx : x ∈ sphereSet n),
        |∫ y : sphereSet n, (v.1 y - v.1 ⟨x, hx⟩) *
          MvPolynomial.eval y.1 (sphereDirichletZonalKernel p k x)
            ∂normalizedSphereMeasure n| ≤
          (A * ‖v‖) * continuousZonalKernelSecondMoment p k x) :
    ContinuousPositiveSphereKernelLocalization n D p k A 4 where
  hn := hn
  base := base
  mass := mass
  boundedMap_degree := boundedMap_degree
  integralRemainder := integralRemainder
  secondMoment := by
    intro x hx
    rw [← mass x hx]
    exact continuousZonalKernelSecondMoment_div_mass_le_four hn p k x hx

/-- The integration argument converts the separated analytic inputs into the
bundled candidate interface. -/
noncomputable def ContinuousPositiveSphereKernelLocalization.toCandidate
    {n D p k : ℕ} {A B : ℝ}
    (L : ContinuousPositiveSphereKernelLocalization n D p k A B)
    (hA : 0 ≤ A) :
    ContinuousPositiveSphereKernelCandidate n D p k (A * B) where
  base := L.base
  mass := L.mass
  boundedMap := continuousZonalKernelPolynomialMap n D p k L.hn L.base
  boundedMap_degree := L.boundedMap_degree
  eval_eq := fun v x _ ↦
    eval_continuousZonalKernelPolynomialMap L.hn p k L.base v x
  near := norm_sub_sphereRestrictionLinear_le_of_integralRemainder
    L.hn p k (continuousZonalKernelMass p k L.base.1) A B hA
      (continuousZonalKernelPolynomialMap n D p k L.hn L.base)
      L.mass
      (fun v x _ ↦
        eval_continuousZonalKernelPolynomialMap L.hn p k L.base v x)
      L.integralRemainder L.secondMoment

/-- A candidate becomes normalized continuous kernel data because its common
mass is strictly positive at the recorded sphere point. -/
noncomputable def ContinuousPositiveSphereKernelCandidate.toData
    {n D p k : ℕ} {c : ℝ}
    (A : ContinuousPositiveSphereKernelCandidate n D p k c)
    (hn : 0 < n) : ContinuousPositiveSphereKernelData n D p k c where
  Z := continuousZonalKernelMass p k A.base.1
  Z_pos := continuousZonalKernelMass_pos hn p k A.base.1 A.base.2
  mass := A.mass
  boundedMap := A.boundedMap
  boundedMap_degree := A.boundedMap_degree
  eval_eq := A.eval_eq
  near := A.near

/-- Finite quadrature data carrying the analytic properties used below: positive weights
and sphere nodes, normalization, preservation of the degree filtration, and the
quantitative near-identity estimate. -/
structure FinitePositiveSphereKernelData
    (n D p k : ℕ) (c : ℝ) where
  N : ℕ
  w : Fin N → ℝ
  y : Fin N → Fin n → ℝ
  y_mem : ∀ i, y i ∈ sphereSet n
  w_nonneg : ∀ i, 0 ≤ w i
  normalized : FiniteZonalKernelNormalized p k w y
  boundedMap :
    spherePolynomialSpace n D →ₗ[ℝ] MvPolynomial (Fin n) ℝ
  boundedMap_degree : ∀ v : spherePolynomialSpace n D,
    (boundedMap v).totalDegree ≤ D
  boundedMap_eq : ∀ v : spherePolynomialSpace n D,
    sphereRestrictionLinear n (boundedMap v) =
      sphereRestrictionLinear n
        (finiteZonalSpherePolynomialMap p k w y y_mem v)
  near : ∀ v : spherePolynomialSpace n D,
    ‖v.1 - sphereRestrictionLinear n
      (finiteZonalSpherePolynomialMap p k w y y_mem v)‖ ≤ c * ‖v‖

/-- Exact polynomial quadrature turns continuous kernel estimates into the
finite positive data used by the Gram/SOS and repair constructions. -/
noncomputable def finitePositiveSphereKernelDataOfContinuous
    {n D p k L N : ℕ} {c : ℝ}
    (A : ContinuousPositiveSphereKernelData n D p k c)
    (Q : SpherePolynomialQuadrature n L N)
    (hdeg : D + 2 * (p * k) ≤ L) :
    FinitePositiveSphereKernelData n D p k c := by
  let hy : ∀ i, Q.coordinates i ∈ sphereSet n :=
    Q.coordinates_mem_sphereSet
  have heq : ∀ v : spherePolynomialSpace n D,
      sphereRestrictionLinear n (A.boundedMap v) =
        sphereRestrictionLinear n
          (finiteZonalSpherePolynomialMap p k
            (fun i ↦ Q.weight i / A.Z) Q.coordinates hy v) := by
    intro v
    ext x
    change MvPolynomial.eval x.1 (A.boundedMap v) =
      MvPolynomial.eval x.1
        (finiteZonalKernelOperator p k (fun i ↦ Q.weight i / A.Z)
          Q.coordinates (fun i ↦ v.1 ⟨Q.coordinates i, hy i⟩))
    rw [A.eval_eq v x.1 x.2]
    symm
    have hsamp :
        (fun i ↦ v.1 ⟨Q.coordinates i, hy i⟩) =
          (fun i ↦ v.1 (Q.node i)) := by
      funext i
      apply congrArg v.1
      apply Subtype.ext
      rfl
    rw [hsamp]
    exact Q.eval_finiteZonalKernelOperator_div_eq_integral
      p k hdeg A.Z v x.1
  exact
    { N := N
      w := fun i ↦ Q.weight i / A.Z
      y := Q.coordinates
      y_mem := hy
      w_nonneg := Q.div_weight_nonneg A.Z_pos
      normalized := Q.finiteZonalKernelNormalized_of_exact_div
        p k (by omega) A.Z A.Z_pos.ne' A.mass
      boundedMap := A.boundedMap
      boundedMap_degree := A.boundedMap_degree
      boundedMap_eq := heq
      near := by
        intro v
        rw [← heq v]
        exact A.near v }
/-- Finite quadrature data defines an endomorphism of the actual bounded-degree
space of polynomial functions on the sphere. -/
noncomputable def finitePositiveSphereKernelEnd
    {n D p k : ℕ} {c : ℝ}
    (data : FinitePositiveSphereKernelData n D p k c) :
    Module.End ℝ (spherePolynomialSpace n D) where
  toFun v :=
    ⟨sphereRestrictionLinear n (data.boundedMap v),
      (mem_spherePolynomialSpace_iff _).2
        ⟨data.boundedMap v, data.boundedMap_degree v, rfl⟩⟩
  map_add' v z := by
    apply Subtype.ext
    simp
  map_smul' a v := by
    apply Subtype.ext
    simp

/-- The continuous analytic interface at every polynomial degree and
bandwidth, before the finite moment discretization. -/
def HasContinuousPositiveSphereKernelEstimates
    {n : ℕ} (p : ℕ) (C : ℝ) : Prop :=
  ∀ D k : ℕ, 1 ≤ D → 1 ≤ k →
    Nonempty (ContinuousPositiveSphereKernelData n D p k
      (C * (D : ℝ) ^ 2 / (k : ℝ) ^ 2))

/-- The narrowed continuous interface before strict positivity of the
normalization mass is inferred. -/
def HasContinuousPositiveSphereKernelCandidates
    {n : ℕ} (p : ℕ) (C : ℝ) : Prop :=
  ∀ D k : ℕ, 1 ≤ D → 1 ≤ k →
    Nonempty (ContinuousPositiveSphereKernelCandidate n D p k
      (C * (D : ℝ) ^ 2 / (k : ℝ) ^ 2))

/-- Full-support positivity converts the candidate family into the original
continuous estimate interface. -/
theorem hasContinuousPositiveSphereKernelEstimates_of_candidates
    {n p : ℕ} {C : ℝ} (hn : 0 < n)
    (h : HasContinuousPositiveSphereKernelCandidates (n := n) p C) :
    HasContinuousPositiveSphereKernelEstimates (n := n) p C := by
  intro D k hD hk
  obtain ⟨A⟩ := h D k hD hk
  exact ⟨A.toData hn⟩

/-- The finite analytic interface at all polynomial degrees and bandwidths. -/
def HasFinitePositiveSphereKernelEstimates {n : ℕ} (p : ℕ) (C : ℝ) : Prop :=
  ∀ D k : ℕ, 1 ≤ D → 1 ≤ k →
    Nonempty (FinitePositiveSphereKernelData n D p k
      (C * (D : ℝ) ^ 2 / (k : ℝ) ^ 2))

/-- Tchakaloff discretization converts the continuous estimate family into
the finite data family without changing the kernel constants. -/
theorem hasFinitePositiveSphereKernelEstimates_of_continuous
    {n p : ℕ} {C : ℝ} (hn : 0 < n)
    (hcontinuous :
      HasContinuousPositiveSphereKernelEstimates (n := n) p C) :
    HasFinitePositiveSphereKernelEstimates (n := n) p C := by
  intro D k hD hk
  obtain ⟨A⟩ := hcontinuous D k hD hk
  obtain ⟨N, ⟨Q⟩⟩ :=
    SpherePolynomialQuadrature.exists_exact n (D + 2 * (p * k)) hn
  exact ⟨finitePositiveSphereKernelDataOfContinuous A Q le_rfl⟩

/-- Finite positive quadrature data supplies the abstract positive sphere-kernel estimate
through the Gram/SOS conversion and endomorphism packaging. -/
theorem hasPositiveSphereKernelEstimates_of_finite
    {n p : ℕ} {C : ℝ}
    (hfinite : HasFinitePositiveSphereKernelEstimates (n := n) p C) :
    HasPositiveSphereKernelEstimates (n := n) p C := by
  intro D k hD hk
  obtain ⟨data⟩ := hfinite D k hD hk
  let K := finitePositiveSphereKernelEnd data
  refine ⟨K, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change sphereRestrictionLinear n
        (data.boundedMap (spherePolynomialConst n D 1)) =
      (spherePolynomialConst n D 1).1
    rw [data.boundedMap_eq]
    ext x
    change MvPolynomial.eval x.1
      (finiteZonalKernelOperator p k data.w data.y (fun _ ↦ 1)) = 1
    exact eval_finiteZonalKernelOperator_one p k data.w data.y
      data.normalized x.1 x.2
  · intro v
    change ‖v.1 - sphereRestrictionLinear n (data.boundedMap v)‖ ≤
      (C * (D : ℝ) ^ 2 / (k : ℝ) ^ 2) * ‖v‖
    rw [data.boundedMap_eq]
    exact data.near v
  · intro v hv
    refine ⟨finiteZonalSpherePolynomialMap p k data.w data.y data.y_mem v, ?_, ?_⟩
    · exact finiteZonalKernelOperator_sphereSOSMod p k data.w data.y
        (fun i ↦ v.1 ⟨data.y i, data.y_mem i⟩) data.w_nonneg
        (fun i ↦ hv ⟨data.y i, data.y_mem i⟩)
    · exact (data.boundedMap_eq v).symm

/-- The dimension-dependent even-power parameter for the Dirichlet kernel. For an
ambient sphere in `ℝⁿ`, the sphere dimension is `n - 1`; choosing
`p = n + 3` leaves ample room in the angular second-moment estimate. -/
def sphereKernelPower (n : ℕ) : ℕ := n + 3

theorem sphereKernelPower_pos (n : ℕ) : 1 ≤ sphereKernelPower n := by
  simp [sphereKernelPower]

/-- Arithmetic form of the strict integrability margin `2p > s + 2`, with
`s = n - 1`. The slightly stronger right-hand side avoids truncated
subtraction in later uses. -/
theorem sphereKernelPower_moment_margin (n : ℕ) :
    n + 2 < 2 * sphereKernelPower n := by
  unfold sphereKernelPower
  omega

/-- Rotation invariance makes the continuous zonal-kernel mass constant on the
unit sphere. -/
theorem continuousZonalKernelMass_eq_on_sphere
    {n : ℕ} (hn : 2 ≤ n) (p k : ℕ) (x z : sphereSet n) :
    continuousZonalKernelMass p k x.1 =
      continuousZonalKernelMass p k z.1 := by
  obtain ⟨a, ha⟩ := exists_sphereAxialReflection_eq hn x z
  have h := continuousZonalKernelMass_sphereAxialReflection p k a x
  rw [ha] at h
  exact h.symm

/-- The polynomial zonal operator preserves the degree-zero filtration. This
is the constant test case of the full polynomial-moment argument. -/
theorem continuousZonalKernelPolynomialMap_range_mem_zero
    {n p k : ℕ} (hn : 2 ≤ n) (base : sphereSet n)
    (v : spherePolynomialSpace n 0) :
    sphereRestrictionLinear n
      (continuousZonalKernelPolynomialMap n 0 p k (by omega) base v) ∈
        spherePolynomialSpace n 0 := by
  obtain ⟨q, hqdeg, hqv⟩ :=
    (mem_spherePolynomialSpace_iff v.1).1 v.2
  have hqzero : q.totalDegree = 0 := Nat.eq_zero_of_le_zero hqdeg
  have hqconst := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).1 hqzero
  let c := legacyMvCoeff 0 q
  have hvconst : v = spherePolynomialConst n 0 c := by
    apply Subtype.ext
    change v.1 = (spherePolynomialConst n 0 c).1
    rw [← hqv, hqconst]
    ext x
    simp [c]
  rw [hvconst]
  have hmass : ∀ x ∈ sphereSet n,
      continuousZonalKernelMass p k x =
        continuousZonalKernelMass p k base.1 := by
    intro x hx
    exact continuousZonalKernelMass_eq_on_sphere hn p k ⟨x, hx⟩ base
  rw [sphereRestriction_continuousZonalKernelPolynomialMap_const
    (D := 0) (by omega) p k base c hmass]
  exact (spherePolynomialConst n 0 c).2

/-- Convolution by any member of the polynomial Dirichlet zonal-kernel family
preserves the degree filtration of sphere polynomial functions. The proof uses
polynomial moments in place of the Funk--Hecke formula. -/
theorem continuousZonalKernelPolynomialMap_range_mem
    {n D p k : ℕ} (hn : 0 < n) (base : sphereSet n)
    (v : spherePolynomialSpace n D) :
    sphereRestrictionLinear n
      (continuousZonalKernelPolynomialMap n D p k hn base v) ∈
        spherePolynomialSpace n D := by
  obtain ⟨q, hqdeg, hqeval⟩ :=
    exists_degree_le_integral_mul_sphereDirichletZonalKernel hn p k v
  rw [mem_spherePolynomialSpace_iff]
  refine ⟨(continuousZonalKernelMass p k base.1)⁻¹ • q, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_smul_le _ q).trans hqdeg
  · ext x
    change MvPolynomial.eval x
        ((continuousZonalKernelMass p k base.1)⁻¹ • q) =
      MvPolynomial.eval x
        (continuousZonalKernelPolynomialMap n D p k hn base v)
    rw [eval_continuousZonalKernelPolynomialMap]
    rw [MvPolynomial.smul_eval, hqeval x x.2, div_eq_mul_inv]
    ring

/-- Convolution with the fixed-power zonal kernel preserves the degree-D
sphere-polynomial filtration. -/
theorem continuousZonalKernelPolynomialMap_fixedPower_range_mem
    {n D k : ℕ} (hn : 3 ≤ n)
    (base : sphereSet n) (v : spherePolynomialSpace n D) :
    sphereRestrictionLinear n
      (continuousZonalKernelPolynomialMap n D (sphereKernelPower n) k
        (by omega) base v) ∈ spherePolynomialSpace n D := by
  exact continuousZonalKernelPolynomialMap_range_mem (by omega) base v

/-- The real volume of a Euclidean coordinate box is the product of its side
lengths. This packages the volume-preserving `WithLp.ofLp` coordinate map for
reuse by both the outer and inner north-pole cylinders. -/
theorem volume_real_euclideanCoordinateBox
    {n : ℕ} (lower upper : Fin n → ℝ) (hlu : lower ≤ upper) :
    volume.real
        ((@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹' Set.Icc lower upper) =
      ∏ i, (upper i - lower i) := by
  rw [MeasureTheory.measureReal_def]
  let f : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ) :=
    @WithLp.ofLp 2 (Fin n → ℝ)
  have hpres : MeasurePreserving f := by
    simpa only [f, sphereEuclideanMeasurableSpace] using
      PiLp.volume_preserving_ofLp (Fin n)
  have hvolume :
      volume (f ⁻¹' Set.Icc lower upper) = volume (Set.Icc lower upper) := by
    rw [← hpres.map_eq]
    exact (Measure.map_apply hpres.measurable measurableSet_Icc).symm
  change (volume (f ⁻¹' Set.Icc lower upper)).toReal = _
  rw [hvolume, Real.volume_Icc_pi_toReal]
  exact hlu
/-- The coordinate cylinder containing the radial cone over a north-pole cap. -/
def euclideanNorthPoleCoordinateCylinder {n : ℕ}
    (hn : 0 < n) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | 0 ≤ z ⟨0, hn⟩ ∧ z ⟨0, hn⟩ ≤ 1 ∧
    ∀ i, i ≠ ⟨0, hn⟩ → |z i| ≤ r}

/-- Lower coordinate endpoints of the north-pole cylinder. -/
def euclideanNorthPoleCylinderLower {n : ℕ}
    (hn : 0 < n) (r : ℝ) : Fin n → ℝ :=
  fun i ↦ if i = ⟨0, hn⟩ then 0 else -r

/-- Upper coordinate endpoints of the north-pole cylinder. -/
def euclideanNorthPoleCylinderUpper {n : ℕ}
    (hn : 0 < n) (r : ℝ) : Fin n → ℝ :=
  fun i ↦ if i = ⟨0, hn⟩ then 1 else r

/-- The coordinate cylinder is the inverse image of the corresponding product
interval under the canonical Euclidean-to-coordinate map. -/
theorem euclideanNorthPoleCoordinateCylinder_eq_preimage_Icc
    {n : ℕ} (hn : 0 < n) (r : ℝ) :
    euclideanNorthPoleCoordinateCylinder hn r =
      (@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹'
        Set.Icc (euclideanNorthPoleCylinderLower hn r)
          (euclideanNorthPoleCylinderUpper hn r) := by
  ext z
  constructor
  · rintro ⟨hz0, hz1, hztrans⟩
    constructor
    · intro i
      by_cases hi : i = ⟨0, hn⟩
      · simpa [euclideanNorthPoleCylinderLower, hi] using hz0
      · simpa [euclideanNorthPoleCylinderLower, hi] using
          (neg_le_of_abs_le (hztrans i hi))
    · intro i
      by_cases hi : i = ⟨0, hn⟩
      · simpa [euclideanNorthPoleCylinderUpper, hi] using hz1
      · simpa [euclideanNorthPoleCylinderUpper, hi] using
          (le_of_abs_le (hztrans i hi))
  · rintro ⟨hzlower, hzupper⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [euclideanNorthPoleCylinderLower] using hzlower ⟨0, hn⟩
    · simpa [euclideanNorthPoleCylinderUpper] using hzupper ⟨0, hn⟩
    · intro i hi
      exact abs_le.mpr ⟨by simpa [euclideanNorthPoleCylinderLower, hi] using hzlower i,
        by simpa [euclideanNorthPoleCylinderUpper, hi] using hzupper i⟩

/-- The lower endpoints of the coordinate cylinder do not exceed the upper
endpoints when the radius is nonnegative. -/
theorem euclideanNorthPoleCylinderLower_le_upper
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    euclideanNorthPoleCylinderLower hn r ≤
      euclideanNorthPoleCylinderUpper hn r := by
  intro i
  by_cases hi : i = ⟨0, hn⟩
  · simp [euclideanNorthPoleCylinderLower, euclideanNorthPoleCylinderUpper, hi]
  · simp [euclideanNorthPoleCylinderLower, euclideanNorthPoleCylinderUpper, hi, hr]

/-- The product of coordinate widths has the expected codimension-one power. -/
theorem prod_euclideanNorthPoleCylinder_width
    {n : ℕ} (hn : 0 < n) (r : ℝ) :
    ∏ i : Fin n,
        (euclideanNorthPoleCylinderUpper hn r i -
          euclideanNorthPoleCylinderLower hn r i) =
      (2 * r) ^ (n - 1) := by
  classical
  rw [Fintype.prod_eq_mul_prod_compl ⟨0, hn⟩]
  simp only [euclideanNorthPoleCylinderUpper,
    euclideanNorthPoleCylinderLower, ite_eq_left, sub_zero, one_mul]
  have hprod :
      (∏ x ∈ ({⟨0, hn⟩}ᶜ : Finset (Fin n)),
          ((if x = ⟨0, hn⟩ then 1 else r) -
            if x = ⟨0, hn⟩ then 0 else -r)) =
        ∏ _x ∈ ({⟨0, hn⟩}ᶜ : Finset (Fin n)), (2 * r) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hine : i ≠ ⟨0, hn⟩ := by
      simpa using (Finset.mem_compl.mp hi)
    simp [hine] ; ring
  rw [hprod, Finset.prod_const]
  congr 1
  rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]

/-- The coordinate cylinder has volume `(2r)^(n-1)`: the longitudinal
coordinate contributes width one and the remaining coordinates width `2r`. -/
theorem volume_real_euclideanNorthPoleCoordinateCylinder
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (euclideanNorthPoleCoordinateCylinder hn r) =
      (2 * r) ^ (n - 1) := by
  rw [euclideanNorthPoleCoordinateCylinder_eq_preimage_Icc,
    volume_real_euclideanCoordinateBox _ _
      (euclideanNorthPoleCylinderLower_le_upper hn hr),
    prod_euclideanNorthPoleCylinder_width]

/-- The coordinate cylinder has finite ambient volume. -/
theorem volume_euclideanNorthPoleCoordinateCylinder_ne_top
    {n : ℕ} (hn : 0 < n) (r : ℝ) :
    volume (euclideanNorthPoleCoordinateCylinder hn r) ≠ ⊤ := by
  rw [euclideanNorthPoleCoordinateCylinder_eq_preimage_Icc]
  let lower := euclideanNorthPoleCylinderLower hn r
  let upper := euclideanNorthPoleCylinderUpper hn r
  let f : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ) :=
    @WithLp.ofLp 2 (Fin n → ℝ)
  have hpres : MeasurePreserving f := by
    simpa only [f, sphereEuclideanMeasurableSpace] using
      PiLp.volume_preserving_ofLp (Fin n)
  have hvolume :
      volume (f ⁻¹' Set.Icc lower upper) = volume (Set.Icc lower upper) := by
    rw [← hpres.map_eq]
    exact (Measure.map_apply hpres.measurable measurableSet_Icc).symm
  change volume (f ⁻¹' Set.Icc lower upper) ≠ ⊤
  rw [hvolume, Real.volume_Icc_pi]
  exact ENNReal.prod_ne_top fun _i _hi ↦
    ENNReal.ofReal_ne_top

-- The nonnegative-radius hypothesis is kept explicit as part of the geometric API.
set_option linter.unusedVariables false in
/-- The radial cone over a radius-at-most-one north-pole cap lies in the
coordinate cylinder with longitudinal interval `[0,1]` and transverse
coordinate intervals `[-r,r]`. -/
theorem radialCone_closedBall_northPole_subset_coordinateCylinder
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Set.Ioo (0 : ℝ) 1 •
        ((↑) '' Metric.closedBall (euclideanSphereNorthPole hn) r :
          Set (EuclideanSpace ℝ (Fin n))) ⊆
      euclideanNorthPoleCoordinateCylinder hn r := by
  rintro z ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
  have hydist : dist y (euclideanSphereNorthPole hn) ≤ r :=
    Metric.mem_closedBall.mp hy
  have hcoord (i : Fin n) :
      |y.1 i - (euclideanSphereNorthPole hn).1 i| ≤ r := by
    calc
      |y.1 i - (euclideanSphereNorthPole hn).1 i| =
          ‖(y.1 - (euclideanSphereNorthPole hn).1) i‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖y.1 - (euclideanSphereNorthPole hn).1‖ :=
        PiLp.norm_apply_le _ i
      _ = dist y (euclideanSphereNorthPole hn) := by
        rw [Subtype.dist_eq, dist_eq_norm]
      _ ≤ r := hydist
  have hynorm : ‖y.1‖ = 1 := by
    simp
  have hy0abs : |y.1 ⟨0, hn⟩| ≤ 1 := by
    calc
      |y.1 ⟨0, hn⟩| = ‖y.1 ⟨0, hn⟩‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ‖y.1‖ := PiLp.norm_apply_le _ _
      _ = 1 := hynorm
  have hy0dist : |y.1 ⟨0, hn⟩ - 1| ≤ r := by
    simpa using hcoord ⟨0, hn⟩
  have hy0nonneg : 0 ≤ y.1 ⟨0, hn⟩ := by
    have := (abs_le.mp hy0dist).1
    linarith
  have hy0le : y.1 ⟨0, hn⟩ ≤ 1 :=
    (le_abs_self _).trans hy0abs
  change 0 ≤ (a • y.1) ⟨0, hn⟩ ∧
    (a • y.1) ⟨0, hn⟩ ≤ 1 ∧
      ∀ i, i ≠ ⟨0, hn⟩ → |(a • y.1) i| ≤ r
  constructor
  · simp only [PiLp.smul_apply, smul_eq_mul]
    exact mul_nonneg ha.1.le hy0nonneg
  constructor
  · simp only [PiLp.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.2.le) hy0nonneg,
      mul_nonneg ha.1.le (sub_nonneg.mpr hy0le)]
  · intro i hi
    have hiCoord : |y.1 i| ≤ r := by
      simpa [euclideanSphereNorthPole_apply hn i, hi] using hcoord i
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ha.1]
    calc
      a * |y.1 i| ≤ 1 * |y.1 i| :=
        mul_le_mul_of_nonneg_right ha.2.le (abs_nonneg _)
      _ = |y.1 i| := one_mul _
      _ ≤ r := hiCoord

-- Positive dimension is retained so this statement shares the surrounding sphere API.
set_option linter.unusedVariables false in
/-- Every radial cone over a subset of the unit sphere lies in the open unit
ball, since its radial parameter belongs to `(0,1)`. -/
theorem radialCone_sphere_subset_unitBall
    {n : ℕ} (hn : 0 < n) (s : Set (euclideanUnitSphere n)) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' s : Set (EuclideanSpace ℝ (Fin n))) ⊆
      Metric.ball 0 1 := by
  rintro z ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩
  have hynorm : ‖y.1‖ = 1 := by
    simp
  rw [Metric.mem_ball, dist_zero_right, norm_smul, hynorm, mul_one,
    Real.norm_eq_abs, abs_of_pos ha.1]
  exact ha.2

/-- A north-pole radial cone has finite ambient volume. -/
theorem volume_radialCone_closedBall_northPole_ne_top
    {n : ℕ} (hn : 0 < n) (r : ℝ) :
    volume (Set.Ioo (0 : ℝ) 1 •
        ((↑) '' Metric.closedBall (euclideanSphereNorthPole hn) r :
          Set (EuclideanSpace ℝ (Fin n)))) ≠ ⊤ := by
  apply ne_of_lt
  calc
    volume (Set.Ioo (0 : ℝ) 1 •
        ((↑) '' Metric.closedBall (euclideanSphereNorthPole hn) r :
          Set (EuclideanSpace ℝ (Fin n)))) ≤
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      measure_mono (radialCone_sphere_subset_unitBall hn _)
    _ < ⊤ := measure_ball_lt_top

/-- The radial cone inherits the sharp codimension-one upper bound from its
coordinate cylinder. -/
theorem radialCone_closedBall_northPole_volume_upper
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    volume.real (Set.Ioo (0 : ℝ) 1 •
        ((↑) '' Metric.closedBall (euclideanSphereNorthPole hn) r :
          Set (EuclideanSpace ℝ (Fin n)))) ≤
      2 ^ (n - 1) * r ^ (n - 1) := by
  calc
    _ ≤ volume.real (euclideanNorthPoleCoordinateCylinder hn r) :=
      measureReal_mono
        (radialCone_closedBall_northPole_subset_coordinateCylinder hn hr0 hr1)
        (volume_euclideanNorthPoleCoordinateCylinder_ne_top hn r)
    _ = (2 * r) ^ (n - 1) :=
      volume_real_euclideanNorthPoleCoordinateCylinder hn hr0
    _ = 2 ^ (n - 1) * r ^ (n - 1) := mul_pow 2 r (n - 1)

/-- A dimension of at least three is positive. -/
theorem dimension_pos_of_three_le {n : ℕ} (hn : 3 ≤ n) : 0 < n :=
  lt_of_lt_of_le (by norm_num) hn

/-- Lower coordinate endpoints for the reverse cylinder used in the cap lower
bound. Its longitudinal coordinate starts at `1/4`, away from the origin. -/
def euclideanNorthPoleReverseCylinderLower {n : ℕ}
    (hn : 0 < n) (r : ℝ) : Fin n → ℝ :=
  fun i ↦ if i = ⟨0, hn⟩ then 1 / 4 else -(r / (16 * n))

/-- Upper coordinate endpoints for the reverse cylinder used in the cap lower
bound. -/
def euclideanNorthPoleReverseCylinderUpper {n : ℕ}
    (hn : 0 < n) (r : ℝ) : Fin n → ℝ :=
  fun i ↦ if i = ⟨0, hn⟩ then 1 / 2 else r / (16 * n)

/-- A thin box pointing toward the north pole. The transverse scale is chosen
conservatively so normalization sends the box into the radius-`r` cap. -/
def euclideanNorthPoleReverseCoordinateCylinder {n : ℕ}
    (hn : 0 < n) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  (@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹'
    Set.Icc (euclideanNorthPoleReverseCylinderLower hn r)
      (euclideanNorthPoleReverseCylinderUpper hn r)

/-- The reverse-cylinder endpoints are ordered for nonnegative radii. -/
theorem euclideanNorthPoleReverseCylinderLower_le_upper
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    euclideanNorthPoleReverseCylinderLower hn r ≤
      euclideanNorthPoleReverseCylinderUpper hn r := by
  intro i
  by_cases hi : i = ⟨0, hn⟩
  · norm_num [euclideanNorthPoleReverseCylinderLower,
      euclideanNorthPoleReverseCylinderUpper, hi]
  · simp only [euclideanNorthPoleReverseCylinderLower,
      euclideanNorthPoleReverseCylinderUpper, hi, ite_false]
    have hq : 0 ≤ r / (16 * n) :=
      div_nonneg hr (by positivity)
    exact (neg_nonpos.mpr hq).trans hq

/-- The reverse cylinder has one fixed longitudinal width and `n-1`
transverse widths proportional to the cap radius. -/
theorem prod_euclideanNorthPoleReverseCylinder_width
    {n : ℕ} (hn : 0 < n) (r : ℝ) :
    ∏ i : Fin n,
        (euclideanNorthPoleReverseCylinderUpper hn r i -
          euclideanNorthPoleReverseCylinderLower hn r i) =
      (1 / 4) * (r / (8 * n)) ^ (n - 1) := by
  classical
  rw [Fintype.prod_eq_mul_prod_compl ⟨0, hn⟩]
  simp only [euclideanNorthPoleReverseCylinderUpper,
    euclideanNorthPoleReverseCylinderLower, ite_eq_left]
  have hprod :
      (∏ x ∈ ({⟨0, hn⟩}ᶜ : Finset (Fin n)),
          ((if x = ⟨0, hn⟩ then 1 / 2 else r / (16 * n)) -
            if x = ⟨0, hn⟩ then 1 / 4 else -(r / (16 * n)))) =
        ∏ _x ∈ ({⟨0, hn⟩}ᶜ : Finset (Fin n)),
          (r / (8 * n)) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hine : i ≠ ⟨0, hn⟩ := by
      simpa using (Finset.mem_compl.mp hi)
    simp [hine] ; ring
  rw [hprod, Finset.prod_const, Finset.card_compl, Fintype.card_fin,
    Finset.card_singleton]
  norm_num

/-- Exact ambient volume of the reverse coordinate cylinder. -/
theorem volume_real_euclideanNorthPoleReverseCoordinateCylinder
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (euclideanNorthPoleReverseCoordinateCylinder hn r) =
      (1 / 4) * (r / (8 * n)) ^ (n - 1) := by
  rw [euclideanNorthPoleReverseCoordinateCylinder,
    volume_real_euclideanCoordinateBox _ _
      (euclideanNorthPoleReverseCylinderLower_le_upper hn hr),
    prod_euclideanNorthPoleReverseCylinder_width]

/-- The longitudinal coordinate of a reverse-cylinder point lies in the fixed
interval `[1/4,1/2]`. -/
theorem euclideanNorthPoleReverseCoordinateCylinder_head_bounds
    {n : ℕ} (hn : 0 < n) {r : ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ euclideanNorthPoleReverseCoordinateCylinder hn r) :
    (1 / 4 : ℝ) ≤ z ⟨0, hn⟩ ∧ z ⟨0, hn⟩ ≤ 1 / 2 := by
  change euclideanNorthPoleReverseCylinderLower hn r ≤
      (@WithLp.ofLp 2 (Fin n → ℝ)) z ∧
    (@WithLp.ofLp 2 (Fin n → ℝ)) z ≤
      euclideanNorthPoleReverseCylinderUpper hn r at hz
  constructor
  · simpa [euclideanNorthPoleReverseCylinderLower] using hz.1 ⟨0, hn⟩
  · simpa [euclideanNorthPoleReverseCylinderUpper] using hz.2 ⟨0, hn⟩

/-- Every transverse coordinate of a reverse-cylinder point is bounded by its
chosen transverse scale. -/
theorem euclideanNorthPoleReverseCoordinateCylinder_transverse_abs_le
    {n : ℕ} (hn : 0 < n) {r : ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ euclideanNorthPoleReverseCoordinateCylinder hn r)
    (i : Fin n) (hi : i ≠ ⟨0, hn⟩) :
    |z i| ≤ r / (16 * n) := by
  change euclideanNorthPoleReverseCylinderLower hn r ≤
      (@WithLp.ofLp 2 (Fin n → ℝ)) z ∧
    (@WithLp.ofLp 2 (Fin n → ℝ)) z ≤
      euclideanNorthPoleReverseCylinderUpper hn r at hz
  exact abs_le.mpr
    ⟨by
      simpa [euclideanNorthPoleReverseCylinderLower, hi] using hz.1 i,
    by
      simpa [euclideanNorthPoleReverseCylinderUpper, hi] using hz.2 i⟩

/-- A reverse-cylinder point is nonzero because its north-pole coordinate is
at least `1/4`. -/
theorem euclideanNorthPoleReverseCoordinateCylinder_ne_zero
    {n : ℕ} (hn : 0 < n) {r : ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ euclideanNorthPoleReverseCoordinateCylinder hn r) :
    z ≠ 0 := by
  intro hzero
  have hzhead :=
    euclideanNorthPoleReverseCoordinateCylinder_head_bounds hn hz
  rw [hzero] at hzhead
  norm_num at hzhead

/-- Reverse-cylinder points lie strictly inside the ambient unit ball. -/
theorem euclideanNorthPoleReverseCoordinateCylinder_norm_lt_one
    {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ euclideanNorthPoleReverseCoordinateCylinder
      (dimension_pos_of_three_le hn) r) :
    ‖z‖ < 1 := by
  classical
  let hn0 := dimension_pos_of_three_le hn
  let q : ℝ := r / (16 * n)
  have hzhead :=
    euclideanNorthPoleReverseCoordinateCylinder_head_bounds hn0 hz
  have hzhead0 : 0 ≤ z ⟨0, hn0⟩ := by
    linarith [hzhead.1]
  have hzheadsq : ‖z ⟨0, hn0⟩‖ ^ 2 ≤ (1 / 4 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hzhead0]
    nlinarith [sq_nonneg (z ⟨0, hn0⟩ - 1 / 2)]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hr0 (by positivity)
  have hncast : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * n)).2
    nlinarith
  have htranscoord (i : Fin n) (hi : i ≠ ⟨0, hn0⟩) :
      |z i| ≤ q := by
    exact euclideanNorthPoleReverseCoordinateCylinder_transverse_abs_le
      hn0 hz i hi
  have htranssq (i : Fin n) (hi : i ≠ ⟨0, hn0⟩) :
      ‖z i‖ ^ 2 ≤ q := by
    have hiabs := htranscoord i hi
    have hiabs0 : 0 ≤ |z i| := abs_nonneg _
    have hiabs1 : |z i| ≤ 1 := hiabs.trans hq1
    rw [Real.norm_eq_abs]
    calc
      |z i| ^ 2 ≤ |z i| := by
        nlinarith [mul_nonneg hiabs0 (sub_nonneg.mpr hiabs1)]
      _ ≤ q := hiabs
  have htranssum :
      ∑ i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), ‖z i‖ ^ 2 ≤
        ∑ _i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), q := by
    apply Finset.sum_le_sum
    intro i hi
    exact htranssq i (by simpa using (Finset.mem_compl.mp hi))
  have hcardle :
      (({⟨0, hn0⟩}ᶜ : Finset (Fin n)).card : ℝ) ≤ n := by
    exact_mod_cast
      (show ({⟨0, hn0⟩}ᶜ : Finset (Fin n)).card ≤ n by
        simpa using Finset.card_le_univ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)))
  have htrans :
      ∑ i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), ‖z i‖ ^ 2 ≤
        (1 / 16 : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), q :=
        htranssum
      _ = (({⟨0, hn0⟩}ᶜ : Finset (Fin n)).card : ℝ) * q := by
        simp
      _ ≤ (n : ℝ) * q :=
        mul_le_mul_of_nonneg_right hcardle hq0
      _ = r / 16 := by
        dsimp [q]
        field_simp [ne_of_gt (Nat.cast_pos.mpr hn0)]
      _ ≤ 1 / 16 := by linarith
  have hnormsq : ‖z‖ ^ 2 < 1 := by
    calc
      ‖z‖ ^ 2 =
          ‖z ⟨0, hn0⟩‖ ^ 2 +
            ∑ i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), ‖z i‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2,
          Fintype.sum_eq_add_sum_compl ⟨0, hn0⟩]
      _ ≤ 1 / 4 + 1 / 16 := add_le_add hzheadsq htrans
      _ < 1 := by norm_num
  nlinarith [norm_nonneg z]

/-- Projection onto the north-pole coordinate axis. -/
def euclideanNorthPoleAxisProjection {n : ℕ} (hn : 0 < n)
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  z ⟨0, hn⟩ • (euclideanSphereNorthPole hn).1

/-- Coordinates of the north-pole axis projection. -/
@[simp] theorem euclideanNorthPoleAxisProjection_apply
    {n : ℕ} (hn : 0 < n) (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    euclideanNorthPoleAxisProjection hn z i =
      if i = ⟨0, hn⟩ then z ⟨0, hn⟩ else 0 := by
  simp [euclideanNorthPoleAxisProjection, euclideanSphereNorthPole_apply]

/-- The transverse part of a reverse-cylinder point has norm at most `r/16`. -/
theorem euclideanNorthPoleReverseCoordinateCylinder_transverse_norm_le
    {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 ≤ r)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ euclideanNorthPoleReverseCoordinateCylinder
      (dimension_pos_of_three_le hn) r) :
    ‖z - euclideanNorthPoleAxisProjection
        (dimension_pos_of_three_le hn) z‖ ≤ r / 16 := by
  classical
  let hn0 := dimension_pos_of_three_le hn
  let q : ℝ := r / (16 * n)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hr0 (by positivity)
  have htranssq (i : Fin n) (hi : i ≠ ⟨0, hn0⟩) :
      ‖z i‖ ^ 2 ≤ q ^ 2 := by
    have hiabs :
        |z i| ≤ q :=
      euclideanNorthPoleReverseCoordinateCylinder_transverse_abs_le
        hn0 hz i hi
    rw [Real.norm_eq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hq0).2 hiabs
  have hsum :
      ∑ i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), ‖z i‖ ^ 2 ≤
        ∑ _i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), q ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact htranssq i (by simpa using (Finset.mem_compl.mp hi))
  have hcardle :
      (({⟨0, hn0⟩}ᶜ : Finset (Fin n)).card : ℝ) ≤ n := by
    exact_mod_cast
      (show ({⟨0, hn0⟩}ᶜ : Finset (Fin n)).card ≤ n by
        simpa using Finset.card_le_univ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)))
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hnrealone : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by omega)
  have hscale : (n : ℝ) * q ^ 2 ≤ (r / 16) ^ 2 := by
    have hrscale : r ^ 2 ≤ r ^ 2 * (n : ℝ) := by
      nlinarith [sq_nonneg r]
    calc
      (n : ℝ) * q ^ 2 = r ^ 2 / (256 * n) := by
        dsimp [q]
        field_simp [ne_of_gt hnreal]
        all_goals ring
      _ ≤ r ^ 2 / 256 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 256 * n)).2
        calc
          r ^ 2 ≤ r ^ 2 * n := hrscale
          _ = (r ^ 2 / 256) * (256 * n) := by ring
      _ = (r / 16) ^ 2 := by ring
  have htranssqtotal :
      ∑ i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), ‖z i‖ ^ 2 ≤
        (r / 16) ^ 2 := by
    calc
      _ ≤ ∑ _i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), q ^ 2 := hsum
      _ = (({⟨0, hn0⟩}ᶜ : Finset (Fin n)).card : ℝ) * q ^ 2 := by
        simp
      _ ≤ (n : ℝ) * q ^ 2 :=
        mul_le_mul_of_nonneg_right hcardle (sq_nonneg q)
      _ ≤ (r / 16) ^ 2 := hscale
  have hnormsq :
      ‖z - euclideanNorthPoleAxisProjection hn0 z‖ ^ 2 ≤
        (r / 16) ^ 2 := by
    calc
      _ = ‖(z - euclideanNorthPoleAxisProjection hn0 z) ⟨0, hn0⟩‖ ^ 2 +
          ∑ i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)),
            ‖(z - euclideanNorthPoleAxisProjection hn0 z) i‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2,
          Fintype.sum_eq_add_sum_compl ⟨0, hn0⟩]
      _ = ∑ i ∈ ({⟨0, hn0⟩}ᶜ : Finset (Fin n)), ‖z i‖ ^ 2 := by
        rw [show
          ‖(z - euclideanNorthPoleAxisProjection hn0 z) ⟨0, hn0⟩‖ ^ 2 = 0 by
            simp]
        simp only [zero_add]
        apply Finset.sum_congr rfl
        intro i hi
        have hine : i ≠ ⟨0, hn0⟩ := by
          simpa using (Finset.mem_compl.mp hi)
        simp [hine]
      _ ≤ (r / 16) ^ 2 := htranssqtotal
  have hrdiv0 : 0 ≤ r / 16 := div_nonneg hr0 (by norm_num)
  nlinarith [norm_nonneg
    (z - euclideanNorthPoleAxisProjection hn0 z)]

/-- Normalization is Lipschitz with constant `2 / ‖y‖` when the comparison
vector `y` is nonzero. -/
theorem norm_normalize_sub_normalize_le_two_mul_div
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x y : V) (hx : x ≠ 0) (hy : 0 < ‖y‖) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤
      2 * ‖x - y‖ / ‖y‖ := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hid :
      ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
        ‖y‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • x := by
    module
  have hcoeff :
      |‖x‖⁻¹ - ‖y‖⁻¹| * ‖x‖ =
        |‖x‖ - ‖y‖| / ‖y‖ := by
    rw [inv_sub_inv hxnorm.ne' hy.ne', abs_div, abs_mul,
      abs_of_pos hxnorm, abs_of_pos hy, abs_sub_comm]
    field_simp [hxnorm.ne', hy.ne']
  rw [NormedSpace.normalize, NormedSpace.normalize, hid]
  calc
    ‖‖y‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • x‖ ≤
        ‖‖y‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • x‖ :=
      norm_add_le _ _
    _ = ‖y‖⁻¹ * ‖x - y‖ + |‖x‖⁻¹ - ‖y‖⁻¹| * ‖x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy)]
    _ = ‖x - y‖ / ‖y‖ + |‖x‖ - ‖y‖| / ‖y‖ := by
      rw [hcoeff]
      ring
    _ ≤ ‖x - y‖ / ‖y‖ + ‖x - y‖ / ‖y‖ := by
      gcongr
      exact abs_norm_sub_norm_le x y
    _ = 2 * ‖x - y‖ / ‖y‖ := by ring

/-- A unit vector normalizes to itself. -/
theorem normalize_eq_self_of_mem_euclideanUnitSphere
    {n : ℕ} (y : euclideanUnitSphere n) :
    NormedSpace.normalize y.1 = y.1 := by
  apply NormedSpace.normalize_eq_self_of_norm_eq_one
  simp

/-- A reverse-cylinder direction normalizes into the north-pole chordal cap. The
preceding transverse bound supplies the
`r/16` numerator and the head-coordinate bound supplies the denominator. -/
theorem euclideanNorthPoleReverseCoordinateCylinder_normalize_dist_le
    {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 ≤ r)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ euclideanNorthPoleReverseCoordinateCylinder
      (dimension_pos_of_three_le hn) r) :
    ‖NormedSpace.normalize z -
        (euclideanSphereNorthPole (dimension_pos_of_three_le hn)).1‖ ≤ r := by
  let hn0 := dimension_pos_of_three_le hn
  have hz_ne :
      z ≠ 0 :=
    euclideanNorthPoleReverseCoordinateCylinder_ne_zero hn0 hz
  have hzhead :=
    euclideanNorthPoleReverseCoordinateCylinder_head_bounds hn0 hz
  have hzheadpos : 0 < z ⟨0, hn0⟩ := by
    linarith [hzhead.1]
  have hnorthnorm :
      ‖(euclideanSphereNorthPole hn0).1‖ = 1 := by
    simp
  have haxisnorm :
      ‖euclideanNorthPoleAxisProjection hn0 z‖ = z ⟨0, hn0⟩ := by
    rw [euclideanNorthPoleAxisProjection, norm_smul, hnorthnorm, mul_one,
      Real.norm_eq_abs, abs_of_pos hzheadpos]
  have haxispos :
      0 < ‖euclideanNorthPoleAxisProjection hn0 z‖ := by
    rw [haxisnorm]
    exact hzheadpos
  have hnormalizeAxis :
      NormedSpace.normalize (euclideanNorthPoleAxisProjection hn0 z) =
        (euclideanSphereNorthPole hn0).1 := by
    rw [euclideanNorthPoleAxisProjection,
      NormedSpace.normalize_smul_of_pos hzheadpos,
      normalize_eq_self_of_mem_euclideanUnitSphere]
  rw [← hnormalizeAxis]
  apply (norm_normalize_sub_normalize_le_two_mul_div z
    (euclideanNorthPoleAxisProjection hn0 z) hz_ne haxispos).trans
  apply (div_le_iff₀ haxispos).2
  have htrans :=
    euclideanNorthPoleReverseCoordinateCylinder_transverse_norm_le
      hn hr0 hz
  have hleft :
      2 * ‖z - euclideanNorthPoleAxisProjection hn0 z‖ ≤ r / 8 := by
    linarith
  have hright : r / 8 ≤ r * ‖euclideanNorthPoleAxisProjection hn0 z‖ := by
    rw [haxisnorm]
    nlinarith [mul_le_mul_of_nonneg_left hzhead.1 hr0]
  exact hleft.trans hright

/-- The geometric inclusion underlying the lower cap-volume estimate:
normalizing any point of the reverse cylinder produces a point in the
north-pole chordal cap, with radial parameter in `(0,1)`. -/
theorem euclideanNorthPoleReverseCoordinateCylinder_subset_radialCone
    {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    euclideanNorthPoleReverseCoordinateCylinder
        (dimension_pos_of_three_le hn) r ⊆
      Set.Ioo (0 : ℝ) 1 •
        ((↑) '' Metric.closedBall
          (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r :
          Set (EuclideanSpace ℝ (Fin n))) := by
  intro z hz
  let hn0 := dimension_pos_of_three_le hn
  have hz_ne :
      z ≠ 0 :=
    euclideanNorthPoleReverseCoordinateCylinder_ne_zero hn0 hz
  have hnormpos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
  have hnormlt : ‖z‖ < 1 :=
    euclideanNorthPoleReverseCoordinateCylinder_norm_lt_one
      hn hr0 hr1 hz
  let y : euclideanUnitSphere n :=
    ⟨NormedSpace.normalize z, by
      rw [Metric.mem_sphere, dist_zero_right]
      exact NormedSpace.norm_normalize hz_ne⟩
  have hycap :
      y ∈ Metric.closedBall (euclideanSphereNorthPole hn0) r := by
    rw [Metric.mem_closedBall, Subtype.dist_eq, dist_eq_norm]
    exact
      euclideanNorthPoleReverseCoordinateCylinder_normalize_dist_le
        hn hr0 hz
  refine ⟨‖z‖, ⟨hnormpos, hnormlt⟩, y.1, ⟨y, hycap, rfl⟩, ?_⟩
  change ‖z‖ • NormedSpace.normalize z = z
  exact NormedSpace.norm_smul_normalize z

/-- The fixed positive coefficient obtained from the reverse cylinder. -/
def euclideanNorthPoleReverseCylinderCoefficient (n : ℕ) : ℝ :=
  (1 / 4) * (1 / (8 * n)) ^ (n - 1)

/-- The reverse-cylinder coefficient is positive in positive dimension. -/
theorem euclideanNorthPoleReverseCylinderCoefficient_pos
    {n : ℕ} (hn : 0 < n) :
    0 < euclideanNorthPoleReverseCylinderCoefficient n := by
  unfold euclideanNorthPoleReverseCylinderCoefficient
  positivity

/-- Reverse-cylinder volume is its fixed coefficient times `r^(n-1)`. -/
theorem volume_real_euclideanNorthPoleReverseCoordinateCylinder_eq_coeff_mul
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (euclideanNorthPoleReverseCoordinateCylinder hn r) =
      euclideanNorthPoleReverseCylinderCoefficient n * r ^ (n - 1) := by
  rw [volume_real_euclideanNorthPoleReverseCoordinateCylinder hn hr]
  unfold euclideanNorthPoleReverseCylinderCoefficient
  ring

/-- A reverse coordinate cylinder supplies enough volume inside the radial
cone over the north-pole cap. -/
theorem euclideanSphereNorthPole_radialCone_volume_lower
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ c : ℝ, 0 < c ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        c * r ^ (n - 1) ≤
          volume.real (Set.Ioo (0 : ℝ) 1 •
            ((↑) '' Metric.closedBall
              (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r :
              Set (EuclideanSpace ℝ (Fin n)))) := by
  let hn0 := dimension_pos_of_three_le hn
  refine ⟨euclideanNorthPoleReverseCylinderCoefficient n,
    euclideanNorthPoleReverseCylinderCoefficient_pos hn0, ?_⟩
  intro r hr0 hr1
  rw [← volume_real_euclideanNorthPoleReverseCoordinateCylinder_eq_coeff_mul
    hn0 hr0]
  exact measureReal_mono
    (euclideanNorthPoleReverseCoordinateCylinder_subset_radialCone hn hr0 hr1)
    (volume_radialCone_closedBall_northPole_ne_top hn0 r)

/-- The geometric core: ambient volume of the radial cone over a closed chordal ball at
the coordinate north pole has sphere-dimensional power bounds, by cylinder inclusion. -/
theorem euclideanSphereNorthPole_radialCone_volume_small_power_bounds
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        c * r ^ (n - 1) ≤
            volume.real (Set.Ioo (0 : ℝ) 1 •
              ((↑) '' Metric.closedBall
                (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r :
                Set (EuclideanSpace ℝ (Fin n)))) ∧
          volume.real (Set.Ioo (0 : ℝ) 1 •
              ((↑) '' Metric.closedBall
                (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r :
                Set (EuclideanSpace ℝ (Fin n)))) ≤ C * r ^ (n - 1) := by
  obtain ⟨c, hc, hlower⟩ :=
    euclideanSphereNorthPole_radialCone_volume_lower hn
  refine ⟨c, 2 ^ (n - 1), hc, by positivity, ?_⟩
  intro r hr0 hr1
  exact ⟨hlower r hr0 hr1,
    radialCone_closedBall_northPole_volume_upper
      (by omega) hr0 hr1⟩

/-- The ambient radial-cone estimate implies the corresponding normalized
surface-measure estimate at the Euclidean north pole. -/
theorem normalizedEuclideanSphereMeasure_closedBall_small_power_bounds_northPole
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        c * r ^ (n - 1) ≤
            (normalizedEuclideanSphereMeasure n).real
              (Metric.closedBall (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r) ∧
          (normalizedEuclideanSphereMeasure n).real
              (Metric.closedBall (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r) ≤
            C * r ^ (n - 1) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  let Z : ℝ := ((μ Set.univ)⁻¹).toReal * (n : ℝ)
  have hμ : μ ≠ 0 := by
    dsimp [μ]
    exact Measure.toSphere_ne_zero volume
  have hμuniv0 : μ Set.univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr hμ
  have hμunivtop : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  have hZ : 0 < Z := by
    dsimp [Z]
    exact mul_pos
      (ENNReal.toReal_pos
        (ENNReal.inv_ne_zero.mpr hμunivtop)
        (ENNReal.inv_ne_top.mpr hμuniv0))
      (Nat.cast_pos.mpr (by omega))
  obtain ⟨c, C, hc, hC, hcone⟩ :=
    euclideanSphereNorthPole_radialCone_volume_small_power_bounds hn
  refine ⟨Z * c, Z * C, mul_pos hZ hc, mul_nonneg hZ.le hC, ?_⟩
  intro r hr0 hr1
  have hb := hcone r hr0 hr1
  have hformula :
      (normalizedEuclideanSphereMeasure n).real
          (Metric.closedBall (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r) =
        Z * volume.real (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' Metric.closedBall (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r :
            Set (EuclideanSpace ℝ (Fin n)))) := by
    simpa only [Z, μ] using
      (normalizedEuclideanSphereMeasure_real_apply
        (n := n) (s := Metric.closedBall
          (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r)
        measurableSet_closedBall)
  constructor
  · calc
      (Z * c) * r ^ (n - 1) = Z * (c * r ^ (n - 1)) := by ring
      _ ≤ Z * volume.real (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' Metric.closedBall (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r :
            Set (EuclideanSpace ℝ (Fin n)))) :=
        mul_le_mul_of_nonneg_left hb.1 hZ.le
      _ = _ := hformula.symm
  · calc
      _ = Z * volume.real (Set.Ioo (0 : ℝ) 1 •
          ((↑) '' Metric.closedBall (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r :
            Set (EuclideanSpace ℝ (Fin n)))) := hformula
      _ ≤ Z * (C * r ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hb.2 hZ.le
      _ = (Z * C) * r ^ (n - 1) := by ring

/-- Sharp codimension-one regularity for metric closed balls under normalized
Haar measure on mathlib's Euclidean unit sphere. This is the elementary
cone/cylinder volume estimate isolated from the repository-level cap API. -/
theorem normalizedEuclideanSphereMeasure_closedBall_small_power_bounds_at
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        c * r ^ (n - 1) ≤
            (normalizedEuclideanSphereMeasure n).real
              (Metric.closedBall (sphereSetEuclideanCoordinates
                (sphereReferencePoint n (dimension_pos_of_three_le hn))) r) ∧
          (normalizedEuclideanSphereMeasure n).real
              (Metric.closedBall (sphereSetEuclideanCoordinates
                (sphereReferencePoint n (dimension_pos_of_three_le hn))) r) ≤
            C * r ^ (n - 1) := by
  obtain ⟨c, C, hc, hC, hnorth⟩ :=
    normalizedEuclideanSphereMeasure_closedBall_small_power_bounds_northPole hn
  refine ⟨c, C, hc, hC, ?_⟩
  intro r hr0 hr1
  have hb := hnorth r hr0 hr1
  have htransport :
      (normalizedEuclideanSphereMeasure n).real
          (Metric.closedBall (sphereSetEuclideanCoordinates
            (sphereReferencePoint n (dimension_pos_of_three_le hn))) r) =
        (normalizedEuclideanSphereMeasure n).real
          (Metric.closedBall (euclideanSphereNorthPole (dimension_pos_of_three_le hn)) r) := by
    calc
      _ = (normalizedSphereMeasure n).real
          (sphereChordalCap (sphereReferencePoint n (dimension_pos_of_three_le hn)) r) :=
        congrArg ENNReal.toReal
          (normalizedSphereMeasure_sphereChordalCap_eq_closedBall
            (sphereReferencePoint n (dimension_pos_of_three_le hn)) hr0).symm
      _ = (normalizedSphereMeasure n).real
          (sphereChordalCap (sphereNorthPolePoint (by omega)) r) :=
        normalizedSphereMeasureReal_sphereChordalCap_eq_on_sphere
          (by omega) r _ _
      _ = _ := congrArg ENNReal.toReal
        (normalizedSphereMeasure_sphereChordalCap_eq_closedBall
          (sphereNorthPolePoint (by omega)) hr0)
  rwa [htransport]

/-- Sharp local regularity for chordal caps, after separating the angular/chordal
comparison and scaling arguments. -/
theorem normalizedSphereMeasure_chordalCap_small_power_bounds_at
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        c * r ^ (n - 1) ≤
            (normalizedSphereMeasure n).real (sphereChordalCap base r) ∧
          (normalizedSphereMeasure n).real (sphereChordalCap base r) ≤
            C * r ^ (n - 1) := by
  obtain ⟨c, C, hc, hC, hclosed⟩ :=
    normalizedEuclideanSphereMeasure_closedBall_small_power_bounds_at hn
  refine ⟨c, C, hc, hC, ?_⟩
  intro r hr0 hr1
  have hb := hclosed r hr0 hr1
  have htransport :
      (normalizedSphereMeasure n).real (sphereChordalCap base r) =
        (normalizedEuclideanSphereMeasure n).real
          (Metric.closedBall (sphereSetEuclideanCoordinates
            (sphereReferencePoint n (dimension_pos_of_three_le hn))) r) := by
    calc
      _ = (normalizedSphereMeasure n).real
          (sphereChordalCap (sphereReferencePoint n (dimension_pos_of_three_le hn)) r) :=
        normalizedSphereMeasureReal_sphereChordalCap_eq_on_sphere
          (by omega) r base
            (sphereReferencePoint n (dimension_pos_of_three_le hn))
      _ = _ := congrArg ENNReal.toReal
        (normalizedSphereMeasure_sphereChordalCap_eq_closedBall
          (sphereReferencePoint n (dimension_pos_of_three_le hn)) hr0)
  rwa [htransport]

/-- Sharp local Ahlfors regularity of normalized sphere measure. Unlike mathlib's generic
`Measure.toSphereBallBound`, its exponent is the sphere dimension `n - 1`. It follows
from the sharp chordal-cap bound and Jordan's sine inequality. -/
theorem normalizedSphereMeasure_angularCap_small_power_bounds_at
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        c * r ^ (n - 1) ≤
            (normalizedSphereMeasure n).real (sphereAngularCap base r) ∧
          (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤
            C * r ^ (n - 1) := by
  letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
    normalizedSphereMeasure_isProbability n (by omega)
  letI : MeasureTheory.IsFiniteMeasure (normalizedSphereMeasure n) := inferInstance
  obtain ⟨c, C, hc, hC, hchordal⟩ :=
    normalizedSphereMeasure_chordalCap_small_power_bounds_at hn base
  let α : ℝ := 2 / Real.pi
  have hαpos : 0 < α := by
    dsimp [α]
    positivity
  have hαle : α ≤ 1 := by
    dsimp [α]
    rw [div_le_one Real.pi_pos]
    exact Real.two_le_pi
  refine ⟨c * α ^ (n - 1), C, mul_pos hc (pow_pos hαpos _), hC, ?_⟩
  intro r hr0 hr1
  have hαr0 : 0 ≤ α * r := mul_nonneg hαpos.le hr0
  have hαr1 : α * r ≤ 1 := by
    calc
      α * r ≤ 1 * r := mul_le_mul_of_nonneg_right hαle hr0
      _ = r := one_mul r
      _ ≤ 1 := hr1
  have hscaled := hchordal (α * r) hαr0 hαr1
  constructor
  · calc
      (c * α ^ (n - 1)) * r ^ (n - 1) =
          c * (α * r) ^ (n - 1) := by
        rw [mul_pow]
        ring
      _ ≤ (normalizedSphereMeasure n).real
          (sphereChordalCap base (α * r)) := hscaled.1
      _ ≤ (normalizedSphereMeasure n).real
          (sphereAngularCap base r) := by
        exact MeasureTheory.measureReal_mono
          (by simpa only [α] using
            sphereChordalCap_two_div_pi_mul_subset_sphereAngularCap base hr0)
          (MeasureTheory.measure_ne_top _ _)
  · calc
      (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤
          (normalizedSphereMeasure n).real (sphereChordalCap base r) := by
        exact MeasureTheory.measureReal_mono
          (sphereAngularCap_subset_sphereChordalCap base hr0)
          (MeasureTheory.measure_ne_top _ _)
      _ ≤ C * r ^ (n - 1) := (hchordal r hr0 hr1).2

/-- Quantitative lower volume of an angular cap at the `1/k` scale, obtained from the
cone/cylinder geometric estimate. -/
theorem normalizedSphereMeasure_angularCap_lower_bound_at
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      c / (k : ℝ) ^ (n - 1) ≤
        (normalizedSphereMeasure n).real
          (sphereAngularCap base (1 / (k : ℝ))) := by
  obtain ⟨c, _C, hc, _hC, hsmall⟩ :=
    normalizedSphereMeasure_angularCap_small_power_bounds_at hn base
  refine ⟨c, hc, ?_⟩
  intro k hk
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hr0 : 0 ≤ 1 / (k : ℝ) := by positivity
  have hr1 : 1 / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkpos]
    exact_mod_cast hk
  have hlower := (hsmall (1 / (k : ℝ)) hr0 hr1).1
  calc
    c / (k : ℝ) ^ (n - 1) =
        c * (1 / (k : ℝ)) ^ (n - 1) := by
      rw [one_div, inv_pow, div_eq_mul_inv]
    _ ≤ (normalizedSphereMeasure n).real
        (sphereAngularCap base (1 / (k : ℝ))) := hlower

/-- The quantitative angular-cap lower bound is uniform in its center. -/
theorem normalizedSphereMeasure_angularCap_lower_bound
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ x : sphereSet n,
      c / (k : ℝ) ^ (n - 1) ≤
        (normalizedSphereMeasure n).real
          (sphereAngularCap x (1 / (k : ℝ))) := by
  obtain ⟨x₀, hx₀⟩ := sphereSet_nonempty (by omega : 0 < n)
  let base : sphereSet n := ⟨x₀, hx₀⟩
  obtain ⟨c, hc, hbase⟩ :=
    normalizedSphereMeasure_angularCap_lower_bound_at hn base
  refine ⟨c, hc, ?_⟩
  intro k hk x
  exact (hbase k hk).trans_eq
    (normalizedSphereMeasureReal_sphereAngularCap_eq_on_sphere
      (by omega) (1 / (k : ℝ)) base x)

/-- Quantitative upper volume of angular caps, obtained from the upper half of the
cone/cylinder geometric estimate. -/
theorem normalizedSphereMeasure_angularCap_upper_bound_at
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r ≤ Real.pi →
      (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤
        C * r ^ (n - 1) := by
  obtain ⟨_c, C, _hc, _hC, hsmall⟩ :=
    normalizedSphereMeasure_angularCap_small_power_bounds_at hn base
  let C' := max C 1
  have hC' : 0 ≤ C' := le_trans zero_le_one (le_max_right C 1)
  refine ⟨C', hC', ?_⟩
  intro r hr _hrPi
  by_cases hrsmall : r ≤ 1
  · have hlocal := (hsmall r hr hrsmall).2
    exact hlocal.trans
      (mul_le_mul_of_nonneg_right (le_max_left C 1) (pow_nonneg hr _))
  · have hrone : 1 ≤ r := (lt_of_not_ge hrsmall).le
    have hmeasure :
        (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤ 1 := by
      letI : MeasureTheory.IsProbabilityMeasure (normalizedSphereMeasure n) :=
        normalizedSphereMeasure_isProbability n (by omega)
      calc
        (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤
            (normalizedSphereMeasure n).real Set.univ :=
          MeasureTheory.measureReal_mono (Set.subset_univ _)
        _ = 1 := MeasureTheory.probReal_univ
    have hpow : 1 ≤ r ^ (n - 1) := one_le_pow₀ hrone
    have hC'one : 1 ≤ C' := le_max_right C 1
    calc
      (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤ 1 :=
        hmeasure
      _ ≤ C' * r ^ (n - 1) :=
        one_le_mul_of_one_le_of_one_le hC'one hpow

/-- The quantitative angular-cap upper bound is uniform in its center. -/
theorem normalizedSphereMeasure_angularCap_upper_bound
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r ≤ Real.pi →
      ∀ x : sphereSet n,
        (normalizedSphereMeasure n).real (sphereAngularCap x r) ≤
          C * r ^ (n - 1) := by
  obtain ⟨x₀, hx₀⟩ := sphereSet_nonempty (by omega : 0 < n)
  let base : sphereSet n := ⟨x₀, hx₀⟩
  obtain ⟨C, hC, hbase⟩ :=
    normalizedSphereMeasure_angularCap_upper_bound_at hn base
  refine ⟨C, hC, ?_⟩
  intro r hr hrPi x
  calc
    (normalizedSphereMeasure n).real (sphereAngularCap x r) =
        (normalizedSphereMeasure n).real (sphereAngularCap base r) :=
      (normalizedSphereMeasureReal_sphereAngularCap_eq_on_sphere
        (by omega) r base x).symm
    _ ≤ C * r ^ (n - 1) := hbase r hr hrPi

/-- A nonnegative cap-volume constant valid up to pi also gives the same
power bound at larger radii, where the cap is already the whole sphere. -/
theorem normalizedSphereMeasure_angularCap_upper_bound_at_all_radii
    {n : ℕ} (base : sphereSet n) {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ r : ℝ, 0 ≤ r → r ≤ Real.pi →
      (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤
        C * r ^ (n - 1))
    (r : ℝ) (hr : 0 ≤ r) :
    (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤
      C * r ^ (n - 1) := by
  by_cases hrPi : r ≤ Real.pi
  · exact hcap r hr hrPi
  · have hPiR : Real.pi ≤ r := le_of_not_ge hrPi
    calc
      (normalizedSphereMeasure n).real (sphereAngularCap base r) =
          (normalizedSphereMeasure n).real
            (sphereAngularCap base Real.pi) := by
        rw [sphereAngularCap_eq_univ_of_pi_le base hPiR,
          sphereAngularCap_eq_univ_of_pi_le base le_rfl]
      _ ≤ C * Real.pi ^ (n - 1) :=
        hcap Real.pi Real.pi_pos.le le_rfl
      _ ≤ C * r ^ (n - 1) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ Real.pi_pos.le hPiR _) hC

/-- The all-radii cap upper bound can be chosen uniformly over every center. -/
theorem normalizedSphereMeasure_angularCap_upper_bound_all_radii
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ x : sphereSet n,
      (normalizedSphereMeasure n).real (sphereAngularCap x r) ≤
        C * r ^ (n - 1) := by
  obtain ⟨C, hC, hcap⟩ :=
    normalizedSphereMeasure_angularCap_upper_bound hn
  refine ⟨C, hC, ?_⟩
  intro r hr x
  exact normalizedSphereMeasure_angularCap_upper_bound_at_all_radii
    x hC (fun t ht htPi ↦ hcap t ht htPi x) r hr
/-- Under the sharp cap upper bound, the inner `1/k` cap contributes at
most order `k^(n+5)` to the unnormalized angular second moment. -/
theorem continuousZonalKernel_fixedPower_innerCap_raw_upper_at_of_cap
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n)
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ r : ℝ, 0 ≤ r → r ≤ Real.pi →
      (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤
        C * r ^ (n - 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k →
      (∫ y : sphereSet n in sphereAngularCap base (1 / (k : ℝ)),
          sphereAngularDistance y base ^ 2 *
            MvPolynomial.eval y.1
              (sphereDirichletZonalKernel
                (sphereKernelPower n) k base.1)
          ∂normalizedSphereMeasure n) ≤
        B * (k : ℝ) ^ (n + 5) := by
  let B := C * 3 ^ (2 * (n + 3))
  refine ⟨B, mul_nonneg hC (pow_nonneg (by norm_num) _), ?_⟩
  intro k hk
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hkone : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hinvPi : 1 / (k : ℝ) ≤ Real.pi := by
    have hinvOne : 1 / (k : ℝ) ≤ 1 :=
      (div_le_one hkpos).2 hkone
    linarith [Real.two_le_pi]
  have hinner :=
    setIntegral_angularSecondMoment_le_of_angularCap
      (by omega : 0 < n) (sphereKernelPower n) k base
      (by positivity : 0 ≤ 1 / (k : ℝ))
  have hcapk := hcap (1 / (k : ℝ)) (by positivity) hinvPi
  have hcapNonneg :
      0 ≤ C * (1 / (k : ℝ)) ^ (n - 1) :=
    mul_nonneg hC (pow_nonneg (by positivity) _)
  have hpeak : 2 * (k : ℝ) + 1 ≤ 3 * (k : ℝ) := by
    linarith
  have hpeakPow :
      (2 * (k : ℝ) + 1) ^ (2 * sphereKernelPower n) ≤
        (3 * (k : ℝ)) ^ (2 * sphereKernelPower n) :=
    pow_le_pow_left₀ (by positivity) hpeak _
  calc
    (∫ y : sphereSet n in sphereAngularCap base (1 / (k : ℝ)),
        sphereAngularDistance y base ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel
              (sphereKernelPower n) k base.1)
        ∂normalizedSphereMeasure n) ≤
      ((1 / (k : ℝ)) ^ 2 *
          (2 * (k : ℝ) + 1) ^ (2 * sphereKernelPower n)) *
        (normalizedSphereMeasure n).real
          (sphereAngularCap base (1 / (k : ℝ))) := hinner
    _ ≤ ((1 / (k : ℝ)) ^ 2 *
          (2 * (k : ℝ) + 1) ^ (2 * sphereKernelPower n)) *
        (C * (1 / (k : ℝ)) ^ (n - 1)) := by
      exact mul_le_mul_of_nonneg_left hcapk
        (mul_nonneg (sq_nonneg _)
          (pow_nonneg (by positivity) _))
    _ ≤ ((1 / (k : ℝ)) ^ 2 *
          (3 * (k : ℝ)) ^ (2 * sphereKernelPower n)) *
        (C * (1 / (k : ℝ)) ^ (n - 1)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpeakPow (sq_nonneg _))
        hcapNonneg
    _ = B * (k : ℝ) ^ (n + 5) := by
      rw [sphereKernelPower, mul_pow]
      dsimp [B]
      rw [show 2 * (n + 3) = (2 + (n - 1)) + (n + 5) by omega]
      rw [pow_add, pow_add]
      rw [one_div_pow]
      field_simp [hkpos.ne']
      rw [one_div, inv_pow]
      field_simp [hkpos.ne']
      rw [pow_add, pow_add]
      ring

/-- Under a sharp outer-cap volume bound, one angular annulus has the
corresponding explicit contribution bound. -/
theorem setIntegral_fixedPower_angularAnnulus_le_of_cap_upper
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n) (k : ℕ)
    {C r s : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hs : 0 ≤ s)
    (hcap : ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi →
      (normalizedSphereMeasure n).real (sphereAngularCap base t) ≤
        C * t ^ (n - 1)) :
    (∫ y : sphereSet n in sphereAngularAnnulus base r s,
        sphereAngularDistance y base ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel
              (sphereKernelPower n) k base.1)
        ∂normalizedSphereMeasure n) ≤
      (s ^ 2 *
          (Real.pi / r) ^ (2 * sphereKernelPower n)) *
        (C * s ^ (n - 1)) := by
  calc
    (∫ y : sphereSet n in sphereAngularAnnulus base r s,
        sphereAngularDistance y base ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel
              (sphereKernelPower n) k base.1)
        ∂normalizedSphereMeasure n) ≤
      (s ^ 2 * (Real.pi / r) ^ (2 * sphereKernelPower n)) *
        (normalizedSphereMeasure n).real
          (sphereAngularCap base s) :=
      setIntegral_angularSecondMoment_le_of_angularAnnulus
        (by omega) (sphereKernelPower n) k base hr
    _ ≤ (s ^ 2 *
          (Real.pi / r) ^ (2 * sphereKernelPower n)) *
        (C * s ^ (n - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (normalizedSphereMeasure_angularCap_upper_bound_at_all_radii
          base hC hcap s hs)
        (mul_nonneg (sq_nonneg s)
          (pow_nonneg (div_nonneg Real.pi_pos.le hr.le) _))

/-- A convenient elementary bound showing that the dyadic chain with
twice as many shells as the bandwidth reaches beyond every fixed radius. -/
theorem four_mul_natCast_le_two_pow_two_mul (k : ℕ) :
    4 * (k : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
  rcases k with _ | k
  · norm_num
  rcases k with _ | k
  · norm_num
  have hnat := Nat.two_mul_sq_add_one_le_two_pow_two_mul (k + 2)
  have hcast :
      (2 : ℝ) * (k + 2 : ℕ) ^ 2 + 1 ≤
        (2 : ℝ) ^ (2 * (k + 2)) := by
    exact_mod_cast hnat
  norm_num [Nat.cast_add] at hcast ⊢
  nlinarith [sq_nonneg (k : ℝ)]
/-- At positive bandwidth, the terminal dyadic radius after twice as many
shells as the bandwidth is at least pi. -/
theorem pi_le_two_pow_two_mul_mul_inv_natCast
    {k : ℕ} (hk : 1 ≤ k) :
    Real.pi ≤ (2 : ℝ) ^ (2 * k) * (1 / (k : ℝ)) := by
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hscaled :=
    mul_le_mul_of_nonneg_right
      (four_mul_natCast_le_two_pow_two_mul k)
      (by positivity : 0 ≤ 1 / (k : ℝ))
  calc
    Real.pi ≤ 4 := Real.pi_le_four
    _ = (4 * (k : ℝ)) * (1 / (k : ℝ)) := by
      field_simp
    _ ≤ (2 : ℝ) ^ (2 * k) * (1 / (k : ℝ)) := hscaled

/-- The dyadic weights produced by the annular moment estimate have a
dimension-independent finite geometric-series bound. -/
theorem sum_range_dyadicMomentWeights_le_two (n J : ℕ) :
    (∑ j ∈ Finset.range J,
        (1 / (2 : ℝ)) ^ (j * (n + 5))) ≤ 2 := by
  calc
    (∑ j ∈ Finset.range J,
        (1 / (2 : ℝ)) ^ (j * (n + 5))) ≤
        ∑ j ∈ Finset.range J, (1 / (2 : ℝ)) ^ j := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [Nat.mul_comm j (n + 5), pow_mul]
      apply pow_le_pow_left₀ (by positivity)
      rw [show n + 5 = 1 + (n + 4) by omega, pow_add, pow_one]
      have htail : (1 / (2 : ℝ)) ^ (n + 4) ≤ 1 :=
        pow_le_one₀ (by positivity) (by norm_num)
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2) (n + 4)]
    _ ≤ 2 := sum_geometric_two_le J

/-- Exact exponent bookkeeping for one dyadic shell at a fixed bandwidth. -/
theorem fixedPower_dyadicAnnulus_bound_identity
    {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k) (C : ℝ) (j : ℕ) :
    ((((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))) ^ 2 *
        (Real.pi / ((2 : ℝ) ^ j * (1 / (k : ℝ)))) ^
          (2 * sphereKernelPower n)) *
      (C * ((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))) ^ (n - 1))) =
      (C * 2 ^ (n + 1) * Real.pi ^ (2 * (n + 3))) *
        (k : ℝ) ^ (n + 5) *
          (1 / (2 : ℝ)) ^ (j * (n + 5)) := by
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have htwo :
      (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 := by
    rw [pow_succ]
  have hweight :
      (1 / (2 : ℝ)) ^ (j * (n + 5)) =
        (1 / (2 : ℝ) ^ j) ^ (n + 5) := by
    rw [pow_mul, one_div_pow]
  rw [sphereKernelPower, htwo, hweight]
  rw [show 2 * (n + 3) = (2 + (n - 1)) + (n + 5) by omega]
  rw [pow_add, pow_add]
  rw [show n + 1 = 2 + (n - 1) by omega, pow_add]
  simp only [mul_pow, div_pow, one_div, inv_pow]
  field_simp [hkpos.ne']
  ring

/-- Each dyadic annulus contributes the expected geometric weight times
the common bandwidth factor. -/
theorem setIntegral_fixedPower_dyadicAnnulus_le_of_cap_upper
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n)
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ r : ℝ, 0 ≤ r → r ≤ Real.pi →
      (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤
        C * r ^ (n - 1))
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    (∫ y : sphereSet n in
        sphereAngularAnnulus base
          ((2 : ℝ) ^ j * (1 / (k : ℝ)))
          ((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))),
        sphereAngularDistance y base ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel
              (sphereKernelPower n) k base.1)
        ∂normalizedSphereMeasure n) ≤
      (C * 2 ^ (n + 1) * Real.pi ^ (2 * (n + 3))) *
        (k : ℝ) ^ (n + 5) *
          (1 / (2 : ℝ)) ^ (j * (n + 5)) := by
  calc
    (∫ y : sphereSet n in
        sphereAngularAnnulus base
          ((2 : ℝ) ^ j * (1 / (k : ℝ)))
          ((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))),
        sphereAngularDistance y base ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel
              (sphereKernelPower n) k base.1)
        ∂normalizedSphereMeasure n) ≤
      ((((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))) ^ 2 *
          (Real.pi / ((2 : ℝ) ^ j * (1 / (k : ℝ)))) ^
            (2 * sphereKernelPower n)) *
        (C * ((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))) ^ (n - 1))) :=
      setIntegral_fixedPower_angularAnnulus_le_of_cap_upper
        hn base k hC (by positivity) (by positivity) hcap
    _ = (C * 2 ^ (n + 1) * Real.pi ^ (2 * (n + 3))) *
        (k : ℝ) ^ (n + 5) *
          (1 / (2 : ℝ)) ^ (j * (n + 5)) :=
      fixedPower_dyadicAnnulus_bound_identity hn hk C j
/-- Given sharp angular-cap volume, the scalar reciprocal-angle estimate and
finite dyadic angular annuli give the raw angular-square moment exponent `n+5`. -/
theorem continuousZonalKernel_fixedPower_angularSecondMoment_raw_upper_at_of_cap
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n)
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ r : ℝ, 0 ≤ r → r ≤ Real.pi →
      (normalizedSphereMeasure n).real (sphereAngularCap base r) ≤
        C * r ^ (n - 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k →
      continuousZonalKernelAngularSecondMoment
          (sphereKernelPower n) k base ≤
        B * (k : ℝ) ^ (n + 5) := by
  obtain ⟨Binner, hBinner, hinner⟩ :=
    continuousZonalKernel_fixedPower_innerCap_raw_upper_at_of_cap
      hn base hC hcap
  let A := C * 2 ^ (n + 1) * Real.pi ^ (2 * (n + 3))
  have hA : 0 ≤ A := by
    exact mul_nonneg
      (mul_nonneg hC (pow_nonneg (by norm_num) _))
      (pow_nonneg Real.pi_pos.le _)
  let B := Binner + 2 * A
  refine ⟨B, add_nonneg hBinner (mul_nonneg (by norm_num) hA), ?_⟩
  intro k hk
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hterminal :=
    pi_le_two_pow_two_mul_mul_inv_natCast hk
  have hdecomp :=
    setIntegral_angularSecondMoment_dyadicCap_eq
      (by omega : 0 < n) (sphereKernelPower n) k base
      (by positivity : 0 ≤ 1 / (k : ℝ)) (2 * k)
  rw [sphereAngularCap_eq_univ_of_pi_le base hterminal] at hdecomp
  have hdecomp' :
      continuousZonalKernelAngularSecondMoment
          (sphereKernelPower n) k base =
        (∫ y : sphereSet n in sphereAngularCap base (1 / (k : ℝ)),
            sphereAngularDistance y base ^ 2 *
              MvPolynomial.eval y.1
                (sphereDirichletZonalKernel
                  (sphereKernelPower n) k base.1)
            ∂normalizedSphereMeasure n) +
          ∑ j ∈ Finset.range (2 * k),
            ∫ y : sphereSet n in
                sphereAngularAnnulus base
                  ((2 : ℝ) ^ j * (1 / (k : ℝ)))
                  ((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))),
              sphereAngularDistance y base ^ 2 *
                MvPolynomial.eval y.1
                  (sphereDirichletZonalKernel
                    (sphereKernelPower n) k base.1)
              ∂normalizedSphereMeasure n := by
    simpa [continuousZonalKernelAngularSecondMoment] using hdecomp
  have hshells :
      (∑ j ∈ Finset.range (2 * k),
          ∫ y : sphereSet n in
              sphereAngularAnnulus base
                ((2 : ℝ) ^ j * (1 / (k : ℝ)))
                ((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))),
            sphereAngularDistance y base ^ 2 *
              MvPolynomial.eval y.1
                (sphereDirichletZonalKernel
                  (sphereKernelPower n) k base.1)
            ∂normalizedSphereMeasure n) ≤
        2 * A * (k : ℝ) ^ (n + 5) := by
    calc
      (∑ j ∈ Finset.range (2 * k),
          ∫ y : sphereSet n in
              sphereAngularAnnulus base
                ((2 : ℝ) ^ j * (1 / (k : ℝ)))
                ((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))),
            sphereAngularDistance y base ^ 2 *
              MvPolynomial.eval y.1
                (sphereDirichletZonalKernel
                  (sphereKernelPower n) k base.1)
            ∂normalizedSphereMeasure n) ≤
          ∑ j ∈ Finset.range (2 * k),
            A * (k : ℝ) ^ (n + 5) *
              (1 / (2 : ℝ)) ^ (j * (n + 5)) := by
        apply Finset.sum_le_sum
        intro j _hj
        exact
          setIntegral_fixedPower_dyadicAnnulus_le_of_cap_upper
            hn base hC hcap hk j
      _ = (A * (k : ℝ) ^ (n + 5)) *
          (∑ j ∈ Finset.range (2 * k),
            (1 / (2 : ℝ)) ^ (j * (n + 5))) := by
        rw [Finset.mul_sum]
      _ ≤ (A * (k : ℝ) ^ (n + 5)) * 2 := by
        exact mul_le_mul_of_nonneg_left
          (sum_range_dyadicMomentWeights_le_two n (2 * k))
          (mul_nonneg hA (pow_nonneg hkpos.le _))
      _ = 2 * A * (k : ℝ) ^ (n + 5) := by ring
  rw [hdecomp']
  calc
    (∫ y : sphereSet n in sphereAngularCap base (1 / (k : ℝ)),
        sphereAngularDistance y base ^ 2 *
          MvPolynomial.eval y.1
            (sphereDirichletZonalKernel
              (sphereKernelPower n) k base.1)
        ∂normalizedSphereMeasure n) +
        ∑ j ∈ Finset.range (2 * k),
          ∫ y : sphereSet n in
              sphereAngularAnnulus base
                ((2 : ℝ) ^ j * (1 / (k : ℝ)))
                ((2 : ℝ) ^ (j + 1) * (1 / (k : ℝ))),
            sphereAngularDistance y base ^ 2 *
              MvPolynomial.eval y.1
                (sphereDirichletZonalKernel
                  (sphereKernelPower n) k base.1)
            ∂normalizedSphereMeasure n ≤
      Binner * (k : ℝ) ^ (n + 5) +
        2 * A * (k : ℝ) ^ (n + 5) :=
      add_le_add (hinner k hk) hshells
    _ = B * (k : ℝ) ^ (n + 5) := by
      dsimp [B]
      ring

/-- The scalar off-peak Dirichlet estimate and dyadic angular annuli give
the raw angular-square moment exponent `n+5`. -/
theorem continuousZonalKernel_fixedPower_angularSecondMoment_raw_upper_at
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k →
      continuousZonalKernelAngularSecondMoment
          (sphereKernelPower n) k base ≤
        B * (k : ℝ) ^ (n + 5) := by
  obtain ⟨C, hC, hcap⟩ :=
    normalizedSphereMeasure_angularCap_upper_bound_at hn base
  exact
    continuousZonalKernel_fixedPower_angularSecondMoment_raw_upper_at_of_cap
      hn base hC hcap

/-- The raw angular second-moment estimate is uniform in the zonal center. -/
theorem continuousZonalKernel_fixedPower_angularSecondMoment_raw_upper
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k → ∀ x : sphereSet n,
      continuousZonalKernelAngularSecondMoment
          (sphereKernelPower n) k x ≤
        B * (k : ℝ) ^ (n + 5) := by
  obtain ⟨x₀, hx₀⟩ := sphereSet_nonempty (by omega : 0 < n)
  let base : sphereSet n := ⟨x₀, hx₀⟩
  obtain ⟨B, hB, hbase⟩ :=
    continuousZonalKernel_fixedPower_angularSecondMoment_raw_upper_at hn base
  refine ⟨B, hB, ?_⟩
  intro k hk x
  obtain ⟨a, ha⟩ := exists_sphereAxialReflection_eq (by omega) base x
  have hinvariant :=
    continuousZonalKernelAngularSecondMoment_sphereAxialReflection
      (sphereKernelPower n) k a base
  rw [ha] at hinvariant
  rw [hinvariant]
  exact hbase k hk

/-- The off-peak Dirichlet estimate and dyadic angular annuli give the raw
chordal-square numerator exponent `n+5`. -/
theorem continuousZonalKernel_fixedPower_secondMoment_raw_upper_at
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, 1 ≤ k →
      continuousZonalKernelSecondMoment (sphereKernelPower n) k base.1 ≤
        B * (k : ℝ) ^ (n + 5) := by
  obtain ⟨B, hB, hangular⟩ :=
    continuousZonalKernel_fixedPower_angularSecondMoment_raw_upper_at hn base
  refine ⟨B, hB, ?_⟩
  intro k hk
  exact (continuousZonalKernelSecondMoment_le_angularSecondMoment
    (by omega) (sphereKernelPower n) k base).trans (hangular k hk)

/-- The raw analytic estimates behind the normalized second moment.
The exponents are `2(n+3) - (n-1) = n+7` for mass and two less for
the chordal-square numerator. -/
theorem continuousZonalKernel_fixedPower_rawMomentBounds_at
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n) :
    ∃ c B : ℝ, 0 < c ∧ 0 ≤ B ∧
      ∀ k : ℕ, 1 ≤ k →
        c * (k : ℝ) ^ (n + 7) ≤
            continuousZonalKernelMass (sphereKernelPower n) k base.1 ∧
          continuousZonalKernelSecondMoment (sphereKernelPower n) k base.1 ≤
            B * (k : ℝ) ^ (n + 5) := by
  obtain ⟨c, hc, hcap⟩ :=
    normalizedSphereMeasure_angularCap_lower_bound_at hn base
  obtain ⟨B, hB, hmoment⟩ :=
    continuousZonalKernel_fixedPower_secondMoment_raw_upper_at hn base
  refine ⟨c, B, hc, hB, ?_⟩
  intro k hk
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  constructor
  · have hmass := angularCap_mass_lower_bound
      (n := n) (by omega) (sphereKernelPower n) k hk base
    calc
      c * (k : ℝ) ^ (n + 7) =
          (k : ℝ) ^ (2 * sphereKernelPower n) *
            (c / (k : ℝ) ^ (n - 1)) := by
        rw [sphereKernelPower]
        rw [show 2 * (n + 3) = (n + 7) + (n - 1) by omega, pow_add]
        field_simp [hkpos.ne']
        ring
      _ ≤ (k : ℝ) ^ (2 * sphereKernelPower n) *
          (normalizedSphereMeasure n).real
            (sphereAngularCap base (1 / (k : ℝ))) := by
        exact mul_le_mul_of_nonneg_left (hcap k hk) (pow_nonneg hkpos.le _)
      _ ≤ continuousZonalKernelMass (sphereKernelPower n) k base.1 := hmass
  · exact hmoment k hk

/-- The genuinely analytic second-moment estimate at one fixed sphere center.
Reflection covariance will make the bound uniform in the center. -/
theorem continuousZonalKernel_fixedPower_secondMoment_at
    {n : ℕ} (hn : 3 ≤ n) (base : sphereSet n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, 1 ≤ k →
        continuousZonalKernelSecondMoment (sphereKernelPower n) k base.1 /
          continuousZonalKernelMass (sphereKernelPower n) k base.1 ≤
            C / (k : ℝ) ^ 2 := by
  obtain ⟨c, B, hc, hB, hraw⟩ :=
    continuousZonalKernel_fixedPower_rawMomentBounds_at hn base
  refine ⟨B / c, div_nonneg hB hc.le, ?_⟩
  intro k hk
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hmasspos :
      0 < continuousZonalKernelMass (sphereKernelPower n) k base.1 :=
    continuousZonalKernelMass_pos (by omega) _ _ base.1 base.2
  obtain ⟨hmass, hmoment⟩ := hraw k hk
  apply (div_le_iff₀ hmasspos).2
  calc
    continuousZonalKernelSecondMoment (sphereKernelPower n) k base.1 ≤
        B * (k : ℝ) ^ (n + 5) := hmoment
    _ = ((B / c) / (k : ℝ) ^ 2) *
        (c * (k : ℝ) ^ (n + 7)) := by
      rw [show n + 7 = (n + 5) + 2 by omega, pow_add]
      field_simp [hc.ne', hkpos.ne']
      ring
    _ ≤ ((B / c) / (k : ℝ) ^ 2) *
        continuousZonalKernelMass (sphereKernelPower n) k base.1 := by
      exact mul_le_mul_of_nonneg_left hmass
        (div_nonneg (div_nonneg hB hc.le) (sq_nonneg _))
/-- The fixed-power Dirichlet-square kernel has normalized chordal second
moment O(k⁻²), uniformly in its center. -/
theorem continuousZonalKernel_fixedPower_secondMoment
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, 1 ≤ k → ∀ x : sphereSet n,
        continuousZonalKernelSecondMoment (sphereKernelPower n) k x.1 /
          continuousZonalKernelMass (sphereKernelPower n) k x.1 ≤
            C / (k : ℝ) ^ 2 := by
  have hnpos : 0 < n := by omega
  obtain ⟨x₀, hx₀⟩ := sphereSet_nonempty hnpos
  let base : sphereSet n := ⟨x₀, hx₀⟩
  obtain ⟨C, hC, hbase⟩ :=
    continuousZonalKernel_fixedPower_secondMoment_at hn base
  refine ⟨C, hC, ?_⟩
  intro k hk x
  obtain ⟨a, ha⟩ := exists_sphereAxialReflection_eq (by omega) base x
  have hinvariant :=
    continuousZonalKernelSecondMoment_div_mass_sphereAxialReflection
      (sphereKernelPower n) k a base
  rw [ha] at hinvariant
  rw [hinvariant]
  exact hbase k hk
/-- The fixed-power localization package at `p = n + 3`: rotation-invariance of kernel
mass, preservation of the degree filtration, the axial-reflection second-order remainder
bound, and the normalized `C / k²` chordal second-moment bound. -/
theorem continuousPositiveSphereKernelLocalizations_fixedPower
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ D k : ℕ, 1 ≤ D → 1 ≤ k →
        Nonempty (ContinuousPositiveSphereKernelSymmetricLocalization
          n D (sphereKernelPower n) k ((D : ℝ) ^ 2)
            (C / (k : ℝ) ^ 2)) := by
  obtain ⟨C, hC, hmoment⟩ :=
    continuousZonalKernel_fixedPower_secondMoment hn
  refine ⟨C, hC, ?_⟩
  intro D k hD hk
  have hnpos : 0 < n := by omega
  obtain ⟨x₀, hx₀⟩ := sphereSet_nonempty hnpos
  let base : sphereSet n := ⟨x₀, hx₀⟩
  have hmass : ∀ x ∈ sphereSet n,
      continuousZonalKernelMass (sphereKernelPower n) k x =
        continuousZonalKernelMass (sphereKernelPower n) k base.1 := by
    intro x hx
    exact continuousZonalKernelMass_eq_on_sphere (by omega)
      (sphereKernelPower n) k ⟨x, hx⟩ base
  refine ⟨{
    hn := hnpos
    base := base
    mass := hmass
    range_mem := ?_
    symmetricIncrement := ?_
    secondMoment := ?_ }⟩
  · intro v
    exact continuousZonalKernelPolynomialMap_fixedPower_range_mem hn base v
  · intro v x hx y
    exact spherePolynomial_axialReflection_secondDifference_le
      hn hD v ⟨x, hx⟩ y
  · intro x hx
    rw [← hmass x hx]
    exact hmoment k hk ⟨x, hx⟩

/-- The separated localization estimates imply the bundled continuous
candidate family. The sup-norm integration step is discharged by
`ContinuousPositiveSphereKernelLocalization.toCandidate`. -/
theorem continuousPositiveSphereKernelCandidates_fixedPower
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasContinuousPositiveSphereKernelCandidates
        (n := n) (sphereKernelPower n) C := by
  obtain ⟨C, hC, hlocal⟩ :=
    continuousPositiveSphereKernelLocalizations_fixedPower hn
  refine ⟨C, hC, ?_⟩
  intro D k hD hk
  obtain ⟨L⟩ := hlocal D k hD hk
  have hcandidate := L.toCandidate (sq_nonneg (D : ℝ))
  exact ⟨by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hcandidate⟩

/-- The candidate kernel family has positive normalization automatically, so
it supplies the original continuous data interface. -/
theorem continuousPositiveSphereKernelData_fixedPower
    {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasContinuousPositiveSphereKernelEstimates
        (n := n) (sphereKernelPower n) C := by
  obtain ⟨C, hC, hdata⟩ :=
    continuousPositiveSphereKernelCandidates_fixedPower hn
  have hnpos : 0 < n := by omega
  exact ⟨C, hC,
    hasContinuousPositiveSphereKernelEstimates_of_candidates hnpos hdata⟩

/-- Package the fixed-power continuous kernel construction in the existential
parameter format consumed by the repair pipeline. -/
theorem continuousPositiveSphereKernelEstimates {n : ℕ} (hn : 3 ≤ n) :
    ∃ (p : ℕ) (C : ℝ), 1 ≤ p ∧ 0 ≤ C ∧
      HasContinuousPositiveSphereKernelEstimates (n := n) p C := by
  obtain ⟨C, hC, hdata⟩ := continuousPositiveSphereKernelData_fixedPower hn
  exact ⟨sphereKernelPower n, C, sphereKernelPower_pos n, hC, hdata⟩

/-- Exact positive quadrature discretizes the continuous kernel estimates,
giving the finite data required by the Gram/SOS construction. -/
theorem finitePositiveSphereKernelEstimates {n : ℕ} (hn : 3 ≤ n) :
    ∃ (p : ℕ) (C : ℝ), 1 ≤ p ∧ 0 ≤ C ∧
      HasFinitePositiveSphereKernelEstimates (n := n) p C := by
  obtain ⟨p, C, hp, hC, hcontinuous⟩ :=
    continuousPositiveSphereKernelEstimates hn
  have hnpos : 0 < n := by omega
  exact ⟨p, C, hp, hC,
    hasFinitePositiveSphereKernelEstimates_of_continuous hnpos hcontinuous⟩

/-- The abstract positive-kernel estimate follows from finite quadrature through the
endomorphism and Gram/SOS bridge. -/
theorem positiveSphereKernelEstimates {n : ℕ} (hn : 3 ≤ n) :
    ∃ (p : ℕ) (C : ℝ), 1 ≤ p ∧ 0 ≤ C ∧
      HasPositiveSphereKernelEstimates (n := n) p C := by
  obtain ⟨p, C, hp, hC, hfinite⟩ := finitePositiveSphereKernelEstimates hn
  exact ⟨p, C, hp, hC, hasPositiveSphereKernelEstimates_of_finite hfinite⟩

/-- Quantitative `C D² / k²` kernel estimates imply a uniform degree-linear
half-contraction after choosing one bandwidth multiplier independent of `D`. -/
theorem hasSpherePolynomialKernelRepair_of_estimates
    {n p : ℕ} {C : ℝ} (hp : 1 ≤ p) (_hC : 0 ≤ C)
    (hK : HasPositiveSphereKernelEstimates (n := n) p C) :
    ∃ A : ℕ, 1 ≤ A ∧ HasSpherePolynomialKernelRepair (n := n) A := by
  obtain ⟨a, ha⟩ := exists_nat_gt (max (2 * C) 1)
  have hp0 : 0 < p := lt_of_lt_of_le Nat.zero_lt_one hp
  have ha1 : 1 ≤ a := by
    have : (1 : ℝ) < a := (le_max_right _ _).trans_lt ha
    exact_mod_cast this.le
  have ha0 : 0 < a := lt_of_lt_of_le Nat.zero_lt_one ha1
  refine ⟨p * a, Nat.mul_pos hp0 ha0, ?_⟩
  intro D hD
  have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  obtain ⟨K, hfix, hnear, hpositive⟩ :=
    hK D (a * D) hD (Nat.mul_pos ha0 hDpos)
  refine ⟨K, hfix, ?_, ?_⟩
  · intro v
    apply (hnear v).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    have haR : 0 < (a : ℝ) := Nat.cast_pos.mpr ha0
    have haR1 : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hDR : 0 < (D : ℝ) := Nat.cast_pos.mpr hDpos
    have htwoC : 2 * C < (a : ℝ) := (le_max_left _ _).trans_lt ha
    have haa : (a : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith
    have hCa : 2 * C ≤ (a : ℝ) ^ 2 := (htwoC.trans_le haa).le
    rw [Nat.cast_mul]
    apply (div_le_iff₀ (sq_pos_of_pos (mul_pos haR hDR))).2
    nlinarith [sq_pos_of_pos hDR]
  · intro v hv
    simpa [Nat.mul_assoc] using hpositive v hv

/-- In dimensions at least three, the defining quadratic generates the kernel of
restriction to the real sphere. -/
theorem sphereRestrictionKernelPrincipal_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    SphereRestrictionKernelPrincipal n := by
  intro p hp
  cases n with
  | zero => omega
  | succ m =>
      apply sphere_vanishing_dvd_relation m p
      intro x hx
      have h := DFunLike.congr_fun hp ⟨x, hx⟩
      simpa using h

/-- The positive polynomial kernel supplies uniformly degree-linear repair operators on
every bounded-degree sphere polynomial space. -/
theorem spherePolynomialKernelRepair {n : ℕ} (hn : 3 ≤ n) :
    ∃ A : ℕ, 1 ≤ A ∧ HasSpherePolynomialKernelRepair (n := n) A := by
  obtain ⟨p, C, hp, hC, hK⟩ := positiveSphereKernelEstimates hn
  exact hasSpherePolynomialKernelRepair_of_estimates hp hC hK
/-- A family of positive, near-identity operators on bounded-degree sphere polynomial
functions supplies the degree-linear repair interface used by the certificate assembly.
The only additional algebraic input is that the restriction kernel is generated by the
sphere equation. -/
theorem hasDegreeLinearRepair_of_spherePolynomialKernels
    {n A : ℕ} (hn : 0 < n)
    (hkernel : SphereRestrictionKernelPrincipal n)
    (hK : HasSpherePolynomialKernelRepair (n := n) A) :
    HasDegreeLinearRepair (n := n) A := by
  intro D h hD hdeg
  obtain ⟨K, hfix, hnear, hpositive⟩ := hK D hD
  let v : spherePolynomialSpace n D :=
    ⟨sphereRestrictionLinear n h,
      (mem_spherePolynomialSpace_iff (D := D) _).2 ⟨h, hdeg, rfl⟩⟩
  have hvSOS :
      SpherePolynomialSOS
        (v + spherePolynomialConst n D (2 * ‖v‖)) (A * D) :=
    spherePolynomial_repair K hfix hnear hpositive v
  have hvnorm : ‖v‖ = sphereSupNorm h := by
    change ‖sphereRestrictionLinear n h‖ = sphereSupNorm h
    exact norm_sphereRestrictionLinear_eq hn h
  apply hvSOS.toSphereSOSMod hkernel
    (h + MvPolynomial.C (2 * sphereSupNorm h))
  ext x
  simp [v, hvnorm]

end QuarticConvergence
end OptimalConvergenceRates

end
