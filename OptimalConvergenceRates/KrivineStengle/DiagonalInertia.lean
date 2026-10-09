/-
  OptimalConvergenceRates/KrivineStengle/DiagonalInertia.lean

  Inertia of diagonal quadratic forms.
-/
import OptimalConvergenceRates.KrivineStengle.Inertia
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.Pi

noncomputable section

open QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {I : Type v} [Fintype I] [DecidableEq I]

/-- The coordinate subspace consisting of vectors supported on `s`. -/
def coordinateSubspace (s : Finset I) : Submodule F (I → F) :=
  (Finsupp.supported F F (s : Set I)).map
    (Finsupp.linearEquivFunOnFinite F F I).toLinearMap

@[simp] theorem mem_coordinateSubspace_iff (s : Finset I) (x : I → F) :
    x ∈ coordinateSubspace (F := F) s ↔ ∀ i, i ∉ s → x i = 0 := by
  classical
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro i hi
    have hsupp := (Finsupp.mem_supported' F y).mp hy i
    simpa using hsupp (by simpa using hi)
  · intro hx
    let y : I →₀ F := (Finsupp.linearEquivFunOnFinite F F I).symm x
    have hy : y ∈ Finsupp.supported F F (s : Set I) := by
      rw [Finsupp.mem_supported']
      intro i hi
      simpa [y] using hx i (by simpa using hi)
    refine ⟨y, hy, ?_⟩
    exact (Finsupp.linearEquivFunOnFinite F F I).apply_symm_apply x

/-- The dimension of a coordinate subspace is the number of enabled coordinates. -/
theorem finrank_coordinateSubspace (s : Finset I) :
    Module.finrank F (coordinateSubspace (F := F) s) = s.card := by
  classical
  rw [coordinateSubspace, LinearEquiv.finrank_map_eq]
  calc
    Module.finrank F (Finsupp.supported F F (s : Set I)) =
        Module.finrank F ((s : Set I) →₀ F) :=
      (Finsupp.supportedEquivFinsupp (R := F) (M := F) (s : Set I)).finrank_eq
    _ = Fintype.card (s : Set I) := Module.finrank_finsupp_self F
    _ = s.card := Fintype.card_coe s

end OptimalConvergenceRates.KrivineStengle

end
