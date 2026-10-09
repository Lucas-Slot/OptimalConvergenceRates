/-
  OptimalConvergenceRates/KrivineStengle/Refutation.lean

  The purely algebraic fixed-seed preordering refutation.
-/
import OptimalConvergenceRates.KrivineStengle.PreorderingMinimality
import OptimalConvergenceRates.KrivineStengle.RateSeed

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

variable {R : Type*} [CommRing R]

theorem IsSquareCone.pow_mem {C : Set R} (hC : IsSquareCone C)
    {x : R} (hx : x ∈ C) (N : ℕ) : x ^ N ∈ C := by
  induction N with
  | zero => simpa using hC.one_mem
  | succ N ih => simpa [pow_succ] using hC.mul_mem ih hx

/-- A subtraction-free recurrence proving positivity of a power difference. -/
theorem IsSquareCone.add_pow_sub_pow_mem {C : Set R} (hC : IsSquareCone C)
    {c h : R} (hc : c ∈ C) (hh : h ∈ C) (N : ℕ) :
    (c + h) ^ N - c ^ N ∈ C := by
  induction N with
  | zero => simpa using hC.zero_mem
  | succ N ih =>
      have hmem := hC.add_mem (hC.mul_mem (hC.add_mem hc hh) ih)
        (hC.mul_mem hh (hC.pow_mem hc N))
      convert hmem using 1; ring

variable {n m : ℕ}

/-- Append one distinguished generator at the final `Fin` index. -/
def appendGenerator (g : Fin m → MvPolynomial (Fin n) ℝ)
    (h : MvPolynomial (Fin n) ℝ) : Fin (m + 1) → MvPolynomial (Fin n) ℝ :=
  Fin.lastCases h g

@[simp]
theorem appendGenerator_castSucc (g : Fin m → MvPolynomial (Fin n) ℝ)
    (h : MvPolynomial (Fin n) ℝ) (i : Fin m) :
    appendGenerator g h i.castSucc = g i := by
  simp [appendGenerator]

@[simp]
theorem appendGenerator_last (g : Fin m → MvPolynomial (Fin n) ℝ)
    (h : MvPolynomial (Fin n) ℝ) :
    appendGenerator g h (Fin.last m) = h := by
  simp [appendGenerator]

theorem PreorderingMem.lift_appendGenerator {g : Fin m → MvPolynomial (Fin n) ℝ}
    {q h : MvPolynomial (Fin n) ℝ} (hq : PreorderingMem g q) :
    PreorderingMem
      (OptimalConvergenceRates.KrivineStengle.appendGenerator g h) q := by
  apply hq.mono_generators
  intro i
  simpa using
    preorderingMem_generator
      (OptimalConvergenceRates.KrivineStengle.appendGenerator g h) i.castSucc

private theorem constant_nonneg_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ} {ε : ℝ} (hε : 0 ≤ ε) :
    PreorderingMem g (C ε) := by
  have hsquare := preorderingMem_sq g (C (Real.sqrt ε))
  simpa only [← C_pow, Real.sq_sqrt hε] using hsquare

/-- A fixed Krivine--Stengle witness gives an untruncated preordering refutation after adjoining
`-p-ε`.  Degree and coefficient-norm estimates are layered on top of this theorem. -/
theorem KSWitness.perturbation_refutation
    {g : Fin m → MvPolynomial (Fin n) ℝ} {p : MvPolynomial (Fin n) ℝ}
    (w : KSWitness g p) {ε : ℝ} (hε : 0 < ε) :
    PreorderingMem (appendGenerator g (perturbationGenerator p ε)) (-1) := by
  let h := perturbationGenerator p ε
  let g' := appendGenerator g h
  have hcone : IsSquareCone {q | PreorderingMem g' q} := preorderingMem_isSquareCone g'
  have hT : PreorderingMem g' w.T := w.hT.lift_appendGenerator
  have hS : PreorderingMem g' w.S := w.hS.lift_appendGenerator
  have hc : PreorderingMem g' (C ε) := constant_nonneg_mem hε.le
  have hh : PreorderingMem g' h := by
    simpa [g'] using preorderingMem_generator g' (Fin.last m)
  have hdiff :
      PreorderingMem g' ((C ε + h) ^ (2 * w.k) - C ε ^ (2 * w.k)) :=
    hcone.add_pow_sub_pow_mem hc hh (2 * w.k)
  have hrhs : PreorderingMem g'
      (w.T + (C ε + h) * w.S +
        ((C ε + h) ^ (2 * w.k) - C ε ^ (2 * w.k))) :=
    preorderingMem_add (preorderingMem_add hT
      (preorderingMem_mul (preorderingMem_add hc hh) hS)) hdiff
  have hneg : PreorderingMem g' (-(C (ε ^ (2 * w.k)))) := by
    rw [w.perturbation_identity ε]
    simpa [h, C_pow] using hrhs
  have ha : ε ^ (2 * w.k) ≠ 0 := pow_ne_zero _ hε.ne'
  have hinv : PreorderingMem g' (C ((ε ^ (2 * w.k))⁻¹)) :=
    constant_nonneg_mem (inv_nonneg.mpr (pow_nonneg hε.le _))
  have hprod := preorderingMem_mul hneg hinv
  have hscalar : -(ε ^ (2 * w.k)) * (ε ^ (2 * w.k))⁻¹ = -1 := by
    field_simp
  have heq : -(C (ε ^ (2 * w.k))) * C ((ε ^ (2 * w.k))⁻¹) =
      (-1 : MvPolynomial (Fin n) ℝ) := by
    rw [← C_neg, ← C_mul, hscalar]
    simp
  rw [← heq]
  exact hprod

end OptimalConvergenceRates.KrivineStengle

end
