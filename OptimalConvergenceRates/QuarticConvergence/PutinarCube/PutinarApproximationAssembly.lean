/-
  Last-mile assembly for quartic Putinar approximations.

  This file deliberately treats the existence of the approximant as an
  input.  It packages the two generic consequences needed by a future
  controlled-root approximation theorem: repair of the signed residual and
  the resulting finite Lasserre value with an O(m^-4) gap.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarRepair
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.CenteredBounds
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.OrderConventions

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n Aq B m d : ℕ}
variable {h f : MvPolynomial (Fin n) ℝ} {L : ℝ}

/-! ## Approximation input and degree bookkeeping -/

/-- Membership in the canonical truncated quadratic module bounds the total
degree of the represented polynomial.  Here the order is the repository's
total-certificate-degree order, not an SOS-root-degree order. -/
theorem totalDegree_le_of_mem_BoxQuadraticModule
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : p ∈ BoxQuadraticModule n r) :
    p.totalDegree ≤ r := by
  obtain ⟨σ₀, σ, _, _, hσ₀, hσ, hp⟩ := hp
  rw [hp]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le hσ₀
  exact MvPolynomial.totalDegree_finsetSum_le fun i _ ↦ hσ i

/-- The exact approximation datum needed by the assembly argument at scale
`m`: a nonnegative target `h`, a quadratic-module approximant at order
`B * m`, and a cube-sup-norm residual of size at most `L / m^4`.

No existence statement is asserted here.  In particular, a future
controlled-root theorem can construct this record without changing any of
the downstream repair or hierarchy arguments. -/
structure HasQuarticBoxQMApproximationAt
    (h : MvPolynomial (Fin n) ℝ) (B m : ℕ) (L : ℝ) : Prop where
  nonnegative : IsNonnegOn h (Hypercube n)
  approximant_exists :
    ∃ b : MvPolynomial (Fin n) ℝ,
      b ∈ BoxQuadraticModule n (B * m) ∧
        polySupNorm (h - b) ≤ L / (m : ℝ) ^ 4

/-! ## Residual repair -/

/-- A quartic approximant plus the degree-linear Putinar repair yields a
certificate for `h` after adding twice the approximation error.  The output
order `(Aq * B) * m` is linear in the approximation scale and is expressed
in the canonical total-certificate-degree convention. -/
theorem quarticBoxQMApproximation_repaired_mem
    (hAq : 1 ≤ Aq) (hrepair : HasPutinarDegreeLinearRepair (n := n) Aq)
    (hB : 1 ≤ B) (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hDegree : h.totalDegree ≤ B * m)
    (happrox : HasQuarticBoxQMApproximationAt h B m L) :
    h + MvPolynomial.C (2 * (L / (m : ℝ) ^ 4)) ∈
      BoxQuadraticModule n ((Aq * B) * m) := by
  obtain ⟨b, hb, herror⟩ := happrox.approximant_exists
  have hBm : 1 ≤ B * m :=
    Nat.mul_pos (show 0 < B by omega) (show 0 < m by omega)
  have hbDegree : b.totalDegree ≤ B * m :=
    totalDegree_le_of_mem_BoxQuadraticModule hb
  have hresidualDegree : (h - b).totalDegree ≤ B * m :=
    (MvPolynomial.totalDegree_sub _ _).trans
      (max_le hDegree hbDegree)
  have herrorNonneg : 0 ≤ L / (m : ℝ) ^ 4 := by positivity
  have hresidual :
      (h - b) + MvPolynomial.C (2 * (L / (m : ℝ) ^ 4)) ∈
        BoxQuadraticModule n (Aq * (B * m)) :=
    hrepair (B * m) (h - b) (L / (m : ℝ) ^ 4)
      hBm hresidualDegree herrorNonneg herror
  have horder : B * m ≤ Aq * (B * m) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (B * m) hAq
  have hbLarge : b ∈ BoxQuadraticModule n (Aq * (B * m)) :=
    BoxQuadraticModule_mono horder hb
  have hadd := BoxQuadraticModule_add hresidual hbLarge
  have hpoly :
      ((h - b) + MvPolynomial.C (2 * (L / (m : ℝ) ^ 4))) + b =
        h + MvPolynomial.C (2 * (L / (m : ℝ) ^ 4)) := by
    ring
  rw [hpoly] at hadd
  simpa only [Nat.mul_assoc] using hadd

/-- Degree-threshold form: it is enough that `m` dominate an advertised
objective degree `d`; the factor `B ≥ 1` then supplies the degree hypothesis
needed by `quarticBoxQMApproximation_repaired_mem`. -/
theorem quarticBoxQMApproximation_repaired_mem_of_degree_le_scale
    (hAq : 1 ≤ Aq) (hrepair : HasPutinarDegreeLinearRepair (n := n) Aq)
    (hB : 1 ≤ B) (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hDegree : h.totalDegree ≤ d) (hdm : d ≤ m)
    (happrox : HasQuarticBoxQMApproximationAt h B m L) :
    h + MvPolynomial.C (2 * (L / (m : ℝ) ^ 4)) ∈
      BoxQuadraticModule n ((Aq * B) * m) := by
  apply quarticBoxQMApproximation_repaired_mem
    hAq hrepair hB hm hL ?_ happrox
  exact hDegree.trans <| hdm.trans <| by
    simpa only [one_mul] using Nat.mul_le_mul_right m hB

/-! ## Centering and the hierarchy gap -/

/-- Centered certificate form used directly as a feasible Lasserre value. -/
theorem centered_quarticBoxQMApproximation_feasible
    (hAq : 1 ≤ Aq) (hrepair : HasPutinarDegreeLinearRepair (n := n) Aq)
    (hB : 1 ≤ B) (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hfDegree : f.totalDegree ≤ d) (hdm : d ≤ m)
    (happrox : HasQuarticBoxQMApproximationAt
      (f - MvPolynomial.C (polyMin f)) B m L) :
    f - MvPolynomial.C (polyMin f - 2 * (L / (m : ℝ) ^ 4)) ∈
      BoxQuadraticModule n ((Aq * B) * m) := by
  have hcenterDegree :
      (f - MvPolynomial.C (polyMin f)).totalDegree ≤ d :=
    centerAtPolyMin_totalDegree_le_of_le hfDegree
  have hcert := quarticBoxQMApproximation_repaired_mem_of_degree_le_scale
    hAq hrepair hB hm hL hcenterDegree hdm happrox
  convert hcert using 1
  simp only [map_sub]
  ring

/-- Generic quartic hierarchy-gap assembly.  Once an approximation record is
available for the centered objective, the quadratic-module Lasserre bound at
the canonical order `(Aq * B) * m` is a finite real number, lies below the
true cube minimum, and has gap at most `2 * L / m^4`.

The theorem does not claim that the approximation record exists; that is the
remaining controlled-root approximation input. -/
theorem lasserre_bound_box_qm_gap_of_quarticApproximation
    (hAq : 1 ≤ Aq) (hrepair : HasPutinarDegreeLinearRepair (n := n) Aq)
    (hB : 1 ≤ B) (hm : 1 ≤ m) (hL : 0 ≤ L)
    (hfDegree : f.totalDegree ≤ d) (hdm : d ≤ m)
    (happrox : HasQuarticBoxQMApproximationAt
      (f - MvPolynomial.C (polyMin f)) B m L) :
    ∃ ℓ : ℝ,
      lasserre_bound_box_qm f ((Aq * B) * m) = (ℓ : WithBot ℝ) ∧
        0 ≤ polyMin f - ℓ ∧
          polyMin f - ℓ ≤ 2 * L / (m : ℝ) ^ 4 := by
  have hfeasible := centered_quarticBoxQMApproximation_feasible
    hAq hrepair hB hm hL hfDegree hdm happrox
  obtain ⟨ℓ, hℓ⟩ :=
    exists_real_lasserre_bound_box_qm_of_feasible
      f ((Aq * B) * m) hfeasible
  have hlower := lasserre_bound_box_qm_ge_feasible
    f ((Aq * B) * m) hfeasible
  have hupper := lasserre_bound_box_qm_le_polyMin
    f ((Aq * B) * m)
  rw [hℓ, WithBot.coe_le_coe] at hlower hupper
  refine ⟨ℓ, hℓ, by linarith, ?_⟩
  have herrorForm :
      2 * L / (m : ℝ) ^ 4 = 2 * (L / (m : ℝ) ^ 4) := by
    ring
  rw [herrorForm]
  linarith

end QuarticConvergence
end OptimalConvergenceRates

end
