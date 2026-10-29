import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
/-! Exact closed-cone separation with continuous linear functionals.
No inner-product choice on a coefficient normed space is required. -/

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace ClosedConeDuality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_of_nonneg_duals (K : ProperCone ℝ E) (x : E)
    (hx : ∀ f:E→L[ℝ]ℝ,(∀ y∈K,0≤f y)→0≤f x) : x∈K:=by
  by_contra hnot
  let C:ConvexCone ℝ E:=PointedCone.toConvexCone (R:=ℝ) (E:=E) K.toPointedCone
  have hconv:Convex ℝ (K:Set E):=C.convex
  obtain ⟨f,c,hfc,hsep⟩:=geometric_hahn_banach_point_closed hconv K.isClosed hnot
  have hz:(0:E)∈K:=K.toPointedCone.zero_mem
  have hc:c<0:=by simpa only [map_zero] using hsep 0 hz
  have hf:∀ y∈K,0≤f y:=by
    intro y hy
    by_contra hn
    have hneg:f y<0:=lt_of_not_ge hn
    have ht:0<c/(f y)+1:=by have hh:=div_pos_of_neg_of_neg hc hneg;linarith
    have hmem:(c/(f y)+1)•y∈K:=C.smul_mem ht hy
    have hh:=hsep _ hmem
    rw [map_smul,smul_eq_mul] at hh
    have he:(c/(f y)+1)*f y=c+f y:=by
      rw [add_mul,div_mul_cancel₀ _ hneg.ne,one_mul]
    rw [he] at hh
    linarith
  have hh:=hx f hf
  linarith

end ClosedConeDuality
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
