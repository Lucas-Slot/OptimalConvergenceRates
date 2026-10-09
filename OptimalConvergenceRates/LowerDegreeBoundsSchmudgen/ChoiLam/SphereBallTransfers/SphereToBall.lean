/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/SphereBallTransfers/SphereToBall.lean

  Normal-form proof that sphere SOS certificates induce ball certificates.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.SphereBallTransfers.NormalForm

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace SphereBallTransfers

/-- Equality gives congruence modulo the sphere relation. -/
theorem OptionSphereCongruent.of_eq {p q : SphereOptionRing} (h : p = q) :
    OptionSphereCongruent p q := by
  subst h
  exact OptionSphereCongruent.refl _

/-- Adding a multiple of the sphere relation does not change the congruence class. -/
theorem OptionSphereCongruent.add_relation_mul (p r : SphereOptionRing) :
    OptionSphereCongruent (p + optionSphereRelation * r) p := by
  refine ⟨r, ?_⟩
  ring

/-- The option-presentation sphere perturbation is congruent to the ball perturbation. -/
theorem spherePerturbed_congruent_ballPerturbed (epsilon : ℝ) :
    OptionSphereCongruent (finSphereToOption (sphereChoiLamPerturbed epsilon))
      (ballToOption (choiLamPerturbed epsilon)) := by
  refine ⟨MvPolynomial.C epsilon * (optionSphereRho + 1), ?_⟩
  rw [finSphereToOption_sphereChoiLamPerturbed]
  unfold choiLamPerturbed
  rw [map_add]
  simp
  ring

/-- Linear remainders subtract coefficientwise. -/
theorem linearRemainder_sub (a b c d : BallRing) :
    linearRemainder a b - linearRemainder c d = linearRemainder (a - c) (b - d) := by
  unfold linearRemainder
  simp [map_sub]
  ring

/-- Squaring after normal-form reduction gives the expected even and odd coefficients. -/
theorem OptionSphereCongruent.square_to_normalRange (k : ℕ) (p : SphereOptionRing)
    (hp : p.totalDegree ≤ k) :
    OptionSphereCongruent (p ^ 2)
      (linearRemainder
        ((evenRemainderRange k p) ^ 2 + ballGenerator4 * (oddRemainderRange k p) ^ 2)
        (2 * evenRemainderRange k p * oddRemainderRange k p)) := by
  have hnorm := OptionSphereCongruent.normalRemainderRange_congruent k p hp
  have hlin := OptionSphereCongruent.of_eq (normalRemainderRange_eq_linearRemainder k p)
  have hp_lin : OptionSphereCongruent p
      (linearRemainder (evenRemainderRange k p) (oddRemainderRange k p)) :=
    hnorm.trans hlin
  have hsq := hp_lin.mul hp_lin
  have hsq_pow : OptionSphereCongruent (p ^ 2)
      ((linearRemainder (evenRemainderRange k p) (oddRemainderRange k p)) ^ 2) := by
    simpa [pow_two] using hsq
  exact hsq_pow.trans (OptionSphereCongruent.linearRemainder_sq
    (evenRemainderRange k p) (oddRemainderRange k p))

/-- A finite sum of normalized squares collects into one linear normal form. -/
theorem OptionSphereCongruent.sum_square_to_normalRange {N k : ℕ}
    (p : Fin N → SphereOptionRing) (hp : ∀ j, (p j).totalDegree ≤ k) :
    OptionSphereCongruent (∑ j : Fin N, (p j) ^ 2)
      (linearRemainder
        (∑ j : Fin N,
          ((evenRemainderRange k (p j)) ^ 2 +
            ballGenerator4 * ((oddRemainderRange k (p j)) ^ 2)))
        (∑ j : Fin N,
          (2 * (evenRemainderRange k (p j)) * (oddRemainderRange k (p j))))) := by
  have hsum := OptionSphereCongruent.finset_sum Finset.univ
    (fun j : Fin N => (p j) ^ 2)
    (fun j : Fin N =>
      linearRemainder
        ((evenRemainderRange k (p j)) ^ 2 +
          ballGenerator4 * ((oddRemainderRange k (p j)) ^ 2))
        (2 * (evenRemainderRange k (p j)) * (oddRemainderRange k (p j))))
    (fun j _ => OptionSphereCongruent.square_to_normalRange k (p j) (hp j))
  simpa only [Finset.mem_univ] using hsum.trans (OptionSphereCongruent.of_eq <|
    sum_linearRemainder
      (fun j : Fin N =>
        (evenRemainderRange k (p j)) ^ 2 +
          ballGenerator4 * ((oddRemainderRange k (p j)) ^ 2))
      (fun j : Fin N =>
        2 * (evenRemainderRange k (p j)) * (oddRemainderRange k (p j))))

/-- A congruence between two linear remainders identifies their coefficients. -/
theorem linearRemainder_congruent_iff_eq {a b c d : BallRing} :
    OptionSphereCongruent (linearRemainder a b) (linearRemainder c d) ↔ a = c ∧ b = d := by
  constructor
  · intro h
    rcases h with ⟨r, hr⟩
    have hz : OptionSphereCongruent (linearRemainder (a - c) (b - d)) 0 := by
      refine ⟨r, ?_⟩
      rw [← linearRemainder_sub]
      simpa using hr
    have hzero := linearRemainder_congruent_zero_iff.mp hz
    exact ⟨sub_eq_zero.mp hzero.1, sub_eq_zero.mp hzero.2⟩
  · rintro ⟨rfl, rfl⟩
    exact OptionSphereCongruent.refl _

/-- Every sphere certificate yields the corresponding two-block ball certificate. -/
theorem sphereToBallTransfer : SphereToBallTransfer := by
  intro k epsilon hk hcert
  rcases hcert with ⟨N, q, h, hdecomp, hdeg⟩
  let p : Fin N → SphereOptionRing := fun j => finSphereToOption (q j)
  let a : Fin N → BallRing := fun j => evenRemainderRange k (p j)
  let b : Fin N → BallRing := fun j => oddRemainderRange k (p j)
  refine ⟨{
    N := N
    a := a
    b := b
    decomp := ?_
    degree_a := ?_
    degree_b := ?_ }⟩
  · have hmap := congrArg finSphereToOption hdecomp
    simp only [map_add, map_mul, map_sum, map_pow, finSphereToOption_sphereRelation] at hmap
    have hcert_congr : OptionSphereCongruent
        (finSphereToOption (sphereChoiLamPerturbed epsilon)) (∑ j : Fin N, (p j) ^ 2) := by
      rw [hmap]
      exact OptionSphereCongruent.add_relation_mul _ _
    have hsum : OptionSphereCongruent (∑ j : Fin N, (p j) ^ 2)
        (linearRemainder
          (∑ j : Fin N,
            ((a j) ^ 2 + ballGenerator4 * ((b j) ^ 2)))
          (∑ j : Fin N, (2 * (a j) * (b j)))) := by
      dsimp [a, b]
      exact OptionSphereCongruent.sum_square_to_normalRange p (fun j => by
        exact (finSphereToOption_totalDegree_le (q j)).trans (hdeg j))
    have htarget : OptionSphereCongruent (ballToOption (choiLamPerturbed epsilon))
        (linearRemainder
          (∑ j : Fin N,
            ((a j) ^ 2 + ballGenerator4 * ((b j) ^ 2)))
          (∑ j : Fin N, (2 * (a j) * (b j)))) :=
      (spherePerturbed_congruent_ballPerturbed epsilon).symm.trans (hcert_congr.trans hsum)
    have htarget_lin : OptionSphereCongruent
        (linearRemainder (choiLamPerturbed epsilon) 0)
        (linearRemainder
          (∑ j : Fin N,
            ((a j) ^ 2 + ballGenerator4 * ((b j) ^ 2)))
          (∑ j : Fin N, (2 * (a j) * (b j)))) := by
      simpa [linearRemainder] using htarget
    have hcoeff := linearRemainder_congruent_iff_eq.mp htarget_lin
    have hA : (∑ j : Fin N, ((a j) ^ 2 + ballGenerator4 * ((b j) ^ 2))) =
        (∑ j : Fin N, (a j) ^ 2) + ballGenerator4 * ∑ j : Fin N, (b j) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hcoeff.1, hA]
  · intro j
    exact evenRemainderRange_totalDegree_le k (p j)
      ((finSphereToOption_totalDegree_le (q j)).trans (hdeg j))
  · intro j
    exact oddRemainderRange_totalDegree_le k (p j) (by omega)
      ((finSphereToOption_totalDegree_le (q j)).trans (hdeg j))


/-- The complete algebraic sphere-to-box transfer. -/
theorem sphereToBoxTransfer : SphereToBoxTransfer :=
  sphereToBoxTransfer_of_sphereToBall sphereToBallTransfer

end SphereBallTransfers
end OptimalConvergenceRates

end
