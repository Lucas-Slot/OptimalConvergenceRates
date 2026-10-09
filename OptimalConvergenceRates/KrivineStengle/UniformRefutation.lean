/-
  OptimalConvergenceRates/KrivineStengle/UniformRefutation.lean

  A single truncation order, independent of the perturbation parameter, for
  the refutation supplied by a fixed Krivine--Stengle witness.
-/
import OptimalConvergenceRates.KrivineStengle.BoundedRefutation

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle

variable {n m : ℕ}

/-- A fixed Krivine--Stengle witness supplies one truncation order that works
for every positive perturbation parameter. -/
theorem KSWitness.exists_perturbation_refutation_order
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} (w : KSWitness g p) :
    ∃ r, ∀ {ε : ℝ}, 0 < ε →
      (-1 : MvPolynomial (Fin n) ℝ) ∈
        GenPreordering (appendGenerator g (perturbationGenerator p ε)) r := by
  obtain ⟨rS, hSbase⟩ := w.hS
  obtain ⟨rT, hTbase⟩ := w.hT
  let r := max (max rT (p.totalDegree + rS))
    ((2 * w.k) * p.totalDegree)
  refine ⟨r, ?_⟩
  intro ε hε
  let h := perturbationGenerator p ε
  let g' := appendGenerator g h
  have hT : w.T ∈ GenPreordering g' rT := by
    exact genPreordering_lift_appendGenerator hTbase
  have hS : w.S ∈ GenPreordering g' rS := by
    exact genPreordering_lift_appendGenerator hSbase
  have hc : C ε ∈ GenPreordering g' 0 :=
    genPreordering_C_nonneg g' hε.le
  have hh0 : h ∈ GenPreordering g' h.totalDegree := by
    simpa [g'] using genPreordering_generator g' (Fin.last m)
  have hdeg : h.totalDegree ≤ p.totalDegree := by
    simpa [h] using perturbationGenerator_totalDegree_le p ε
  have hh : h ∈ GenPreordering g' p.totalDegree :=
    GenPreordering_mono hdeg hh0
  have hch : C ε + h ∈ GenPreordering g' p.totalDegree := by
    simpa using genPreordering_add hc hh
  have hmul : (C ε + h) * w.S ∈
      GenPreordering g' (p.totalDegree + rS) :=
    genPreordering_mul hch hS
  have hdiff : (C ε + h) ^ (2 * w.k) - C ε ^ (2 * w.k) ∈
      GenPreordering g' ((2 * w.k) * p.totalDegree) :=
    genPreordering_add_pow_sub_pow hc hh (2 * w.k)
  have hsum : w.T + (C ε + h) * w.S ∈
      GenPreordering g' (max rT (p.totalDegree + rS)) :=
    genPreordering_add hT hmul
  have hrhs :
      w.T + (C ε + h) * w.S +
          ((C ε + h) ^ (2 * w.k) - C ε ^ (2 * w.k)) ∈
        GenPreordering g' r := by
    simpa [r] using genPreordering_add hsum hdiff
  have hneg : -(C (ε ^ (2 * w.k))) ∈ GenPreordering g' r := by
    rw [w.perturbation_identity ε]
    simpa [h, C_pow] using hrhs
  have hinv : C ((ε ^ (2 * w.k))⁻¹) ∈ GenPreordering g' 0 :=
    genPreordering_C_nonneg g'
      (inv_nonneg.mpr (pow_nonneg hε.le _))
  have hprod :
      -(C (ε ^ (2 * w.k))) * C ((ε ^ (2 * w.k))⁻¹) ∈
        GenPreordering g' r := by
    simpa using genPreordering_mul hneg hinv
  have ha : ε ^ (2 * w.k) ≠ 0 := pow_ne_zero _ hε.ne'
  have hscalar : -(ε ^ (2 * w.k)) * (ε ^ (2 * w.k))⁻¹ = -1 := by
    field_simp
  have heq :
      -(C (ε ^ (2 * w.k))) * C ((ε ^ (2 * w.k))⁻¹) =
        (-1 : MvPolynomial (Fin n) ℝ) := by
    rw [← C_neg, ← C_mul, hscalar]
    simp
  rw [← heq]
  exact hprod

end OptimalConvergenceRates.KrivineStengle

end
