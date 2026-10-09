/-
  OptimalConvergenceRates/KrivineStengle/HermiteTrace.lean

  Hermite trace matrices for root-sign counting.
-/
import OptimalConvergenceRates.KrivineStengle.DegreeBranches
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Trace.Basic

noncomputable section

open Matrix Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]

/-- The Hermite matrix `H(f,h)`. Its `(i,j)` entry is the trace, in `F[X]/(f)`, of
multiplication by `h(X) X^(i+j)`. The quotient is finite free because `f` is monic. -/
def hermiteTraceMatrix (f h : F[X]) (hf : f.Monic) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) F := by
  letI : Module.Free F (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  exact fun i j ↦ Algebra.trace F (AdjoinRoot f)
    (aeval (AdjoinRoot.root f) h *
      AdjoinRoot.root f ^ ((i : ℕ) + (j : ℕ)))

/-- Hermite trace matrices are symmetric over every field. -/
theorem hermiteTraceMatrix_isSymm (f h : F[X]) (hf : f.Monic) :
    (hermiteTraceMatrix f h hf).IsSymm := by
  ext i j
  simp [hermiteTraceMatrix, add_comm]

/-- The empty quotient-basis case produces the unique empty matrix. -/
theorem hermiteTraceMatrix_eq_of_natDegree_eq_zero (f h : F[X]) (hf : f.Monic)
    (hdegree : f.natDegree = 0) :
    hermiteTraceMatrix f h hf = 0 := by
  ext i
  exact Fin.elim0 (hdegree ▸ i)

end OptimalConvergenceRates.KrivineStengle

end
