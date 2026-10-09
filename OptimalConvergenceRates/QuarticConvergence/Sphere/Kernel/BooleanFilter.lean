/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Kernel/BooleanFilter.lean

  Algebra of the Booleanized kernel S = 2K - K² and its squared approximation error.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Defs
import Mathlib.Analysis.Normed.Module.Basic

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

section LinearAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The Boolean polynomial `2K - K²` applied to a linear operator `K`. -/
def booleanFilter (K : Module.End R V) : Module.End R V :=
  K + K - K.comp K

@[simp] theorem booleanFilter_apply (K : Module.End R V) (v : V) :
    booleanFilter K v = K v + K v - K (K v) := rfl

/-- The one-step approximation error associated to `K`. -/
def filterError (K : Module.End R V) (v : V) : V :=
  v - K v

/-- The key Boolean identity `I - (2K-K²) = (I-K)²`, pointwise. -/
theorem sub_booleanFilter_apply (K : Module.End R V) (v : V) :
    v - booleanFilter K v = filterError K (filterError K v) := by
  simp only [booleanFilter_apply, filterError, map_sub]
  abel

/-- A vector fixed by `K` is also fixed by its Booleanization. -/
theorem booleanFilter_eq_of_fixed (K : Module.End R V) {v : V} (hv : K v = v) :
    booleanFilter K v = v := by
  simp [booleanFilter_apply, hv]

/-- If the range of `K` lies in a submodule, so does the range of `2K-K²`. -/
theorem booleanFilter_mem_of_forall_mem (K : Module.End R V) (W : Submodule R V)
    (hK : ∀ v, K v ∈ W) (v : V) : booleanFilter K v ∈ W := by
  rw [booleanFilter_apply]
  exact W.sub_mem (W.add_mem (hK v) (hK v)) (hK (K v))

/-- Range formulation of `booleanFilter_mem_of_forall_mem`. -/
theorem booleanFilter_range_le (K : Module.End R V) (W : Submodule R V)
    (hK : LinearMap.range K ≤ W) : LinearMap.range (booleanFilter K) ≤ W := by
  rintro _ ⟨v, rfl⟩
  exact booleanFilter_mem_of_forall_mem K W (fun u ↦ hK ⟨u, rfl⟩) v

/-- Booleanization preserves commutation with another linear operator. -/
theorem booleanFilter_comp_of_commute (K L : Module.End R V)
    (hKL : K.comp L = L.comp K) :
    (booleanFilter K).comp L = L.comp (booleanFilter K) := by
  ext v
  have h₁ : K (L v) = L (K v) := LinearMap.congr_fun hKL v
  have h₂ : K (L (K v)) = L (K (K v)) := LinearMap.congr_fun hKL (K v)
  simp only [LinearMap.comp_apply, booleanFilter_apply, map_add, map_sub, h₁, h₂]

end LinearAlgebra
section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Booleanization squares a uniform relative error estimate. In the kernel application,
a bound of order k⁻² therefore becomes a bound of order k⁻⁴. -/
theorem norm_sub_booleanFilter_le (K : Module.End ℝ V) (c : ℝ) (hc : 0 ≤ c)
    (hK : ∀ v, ‖filterError K v‖ ≤ c * ‖v‖) (v : V) :
    ‖v - booleanFilter K v‖ ≤ c ^ 2 * ‖v‖ := by
  rw [sub_booleanFilter_apply]
  calc
    ‖filterError K (filterError K v)‖ ≤ c * ‖filterError K v‖ := hK _
    _ ≤ c * (c * ‖v‖) := mul_le_mul_of_nonneg_left (hK v) hc
    _ = c ^ 2 * ‖v‖ := by ring

end Normed

end QuarticConvergence
end OptimalConvergenceRates

end
