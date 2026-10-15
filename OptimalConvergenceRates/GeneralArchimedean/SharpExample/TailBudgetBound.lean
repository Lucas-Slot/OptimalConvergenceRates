/-
  From scalar Gaussian decay to a uniform bound for every shifted SOS tail.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.TailMoment

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- The scalar estimate needed after coefficient extraction.  It is isolated
so that the exponential arithmetic is independent of the polynomial proof. -/
def SharpTailDecay (eta : Real) (D d : Nat) (E : Real) : Prop :=
  ∀ L s : Nat, D <= L -> L + s <= 2 * D -> s <= 2 ->
    (8 : Real) ^ L * (d : Real) ^ (2 * L) * eta ^ (L + s) *
        Real.exp (4 * ((L + s : Nat) : Real) ^ 2) <= E

def sharpTailPenalty (D d : Nat) (M E : Real) : Real :=
  3 * ((2 * D + 1 : Nat) : Real) ^ 2 *
    ((2 * d + 1 : Nat) : Real) ^ 2 * M ^ 2 * E

/-- A bivariate polynomial of total degree at most `r` has at most
`(r+1)^2` monomials. -/
theorem card_support_bivar_le_sq {p : MvPolynomial (Fin 2) Real} {r : Nat}
    (hdeg : p.totalDegree <= r) :
    p.support.card <= (r + 1) ^ 2 := by
  let f : {alpha // alpha ∈ p.support} → Fin (r + 1) × Fin (r + 1) :=
    fun alpha =>
      (⟨alpha.1 0, Nat.lt_succ_of_le <|
          (MvPolynomial.monomial_le_degreeOf (0 : Fin 2) alpha.2).trans
            ((MvPolynomial.degreeOf_le_totalDegree p 0).trans hdeg)⟩,
       ⟨alpha.1 1, Nat.lt_succ_of_le <|
          (MvPolynomial.monomial_le_degreeOf (1 : Fin 2) alpha.2).trans
            ((MvPolynomial.degreeOf_le_totalDegree p 1).trans hdeg)⟩)
  have hf : Function.Injective f := by
    intro alpha beta hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    fin_cases i
    · exact congr_arg (fun z => z.1.1) hab
    · exact congr_arg (fun z => z.2.1) hab
  simpa [f, pow_two] using Fintype.card_le_of_injective f hf

theorem sharpTailMomentBudget_nonneg {N : Nat}
    {eta M : Real} (heta : 0 <= eta) (D d u v : Nat)
    (q : Fin N -> MvPolynomial (Fin 2) Real) :
    0 <= sharpTailMomentBudget eta D d M u v q := by
  apply Finset.sum_nonneg
  intro alpha _halpha
  split_ifs
  · unfold sharpTailCoefficientEnvelope sharpShiftedMomentEnvelope
    positivity
  · exact le_rfl

/-- A scalar tail-decay estimate gives a uniform bound for every monomial
shift of degree at most two. -/
theorem sharpTailMomentBudget_le_penalty
    {N D d u v : Nat} {eta M E : Real}
    (heta : 0 <= eta) (hM : 0 <= M) (hE : 0 <= E)
    (huv : u + v <= 2) (hdecay : SharpTailDecay eta D d E)
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d) :
    sharpTailMomentBudget eta D d M u v q <=
      sharpTailPenalty D d M E := by
  let Amax : Real := 3 * ((2 * D + 1 : Nat) : Real) ^ 2 * M ^ 2
  have hAmax : 0 <= Amax := by
    dsimp [Amax]
    positivity
  calc
    sharpTailMomentBudget eta D d M u v q <=
        ∑ _alpha ∈ (sharpTailPolynomial D q).support, Amax * E := by
      apply Finset.sum_le_sum
      intro alpha halpha
      by_cases hcut : bivarTotal alpha + u + v <= 2 * D
      · rw [ite_eq_left hcut]
        have hlower := sharpTailPolynomial_support_degree q halpha
        have hdec := hdecay (bivarTotal alpha) (u + v) hlower
          (by omega) huv
        let A : Real :=
          3 * ((bivarTotal alpha + 1 : Nat) : Real) ^ 2 * M ^ 2
        have hA : 0 <= A := by
          dsimp [A]
          positivity
        have hAle : A <= Amax := by
          have hL : bivarTotal alpha <= 2 * D := by omega
          have hcast :
              ((bivarTotal alpha + 1 : Nat) : Real) <=
                ((2 * D + 1 : Nat) : Real) := by exact_mod_cast Nat.add_le_add_right hL 1
          dsimp [A, Amax]
          gcongr
        have hbase : 0 <=
            (8 : Real) ^ bivarTotal alpha *
              (d : Real) ^ (2 * bivarTotal alpha) *
              eta ^ (bivarTotal alpha + (u + v)) *
              Real.exp
                (4 * ((bivarTotal alpha + (u + v) : Nat) : Real) ^ 2) := by
          positivity
        have hprod := mul_le_mul hAle hdec hbase hAmax
        change
          (3 * ((bivarTotal alpha + 1 : Nat) : Real) ^ 2 *
              (8 : Real) ^ bivarTotal alpha *
              (d : Real) ^ (2 * bivarTotal alpha) * M ^ 2) *
            (eta ^ (bivarTotal alpha + u + v) *
              Real.exp
                (4 * ((bivarTotal alpha + u + v : Nat) : Real) ^ 2)) <=
            Amax * E
        calc
          _ = A * ((8 : Real) ^ bivarTotal alpha *
              (d : Real) ^ (2 * bivarTotal alpha) *
              eta ^ (bivarTotal alpha + (u + v)) *
              Real.exp (4 * ((bivarTotal alpha + (u + v) : Nat) : Real) ^ 2)) := by
                dsimp [A]
                ring
          _ <= Amax * E := hprod
      · rw [ite_eq_right hcut]
        exact mul_nonneg hAmax hE
    _ = ((sharpTailPolynomial D q).support.card : Real) * (Amax * E) := by
      simp
    _ <= (((2 * d + 1 : Nat) : Real) ^ 2) * (Amax * E) := by
      gcongr
      exact_mod_cast card_support_bivar_le_sq
        (sharpTailPolynomial_totalDegree_le q hdeg)
    _ = sharpTailPenalty D d M E := by
      simp [sharpTailPenalty, Amax]
      ring

end OptimalConvergenceRates.GeneralArchimedean

end
