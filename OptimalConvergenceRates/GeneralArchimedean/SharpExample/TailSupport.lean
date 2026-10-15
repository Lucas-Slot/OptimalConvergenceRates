/-
  Combinatorial support and cardinality bounds for the high-degree SOS tail.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.TailCoefficientBound
import Mathlib.Data.Finsupp.Interval

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Total degree of a bivariate exponent, written without a finite sum. -/
abbrev bivarTotal (alpha : Fin 2 →₀ Nat) : Nat := alpha 0 + alpha 1

theorem finsupp_sum_fin_two (alpha : Fin 2 →₀ Nat) :
    alpha.sum (fun _ e => e) = bivarTotal alpha := by
  classical
  rw [Finsupp.sum_fintype]
  all_goals simp [Fin.sum_univ_two, bivarTotal]

/-- The convolution antidiagonal of a bivariate exponent has at most the
number of coordinatewise choices for its first summand. -/
theorem card_antidiagonal_bivar_le (gamma : Fin 2 →₀ Nat) :
    (Finset.antidiagonal gamma).card <=
      (gamma 0 + 1) * (gamma 1 + 1) := by
  let f : {x // x ∈ Finset.antidiagonal gamma} →
      Fin (gamma 0 + 1) × Fin (gamma 1 + 1) := fun x =>
    (⟨x.1.1 0, Nat.lt_succ_of_le <| by
        have hx := Finset.mem_antidiagonal.mp x.2
        have h : x.1.1 0 + x.1.2 0 = gamma 0 := by simpa using DFunLike.congr_fun hx (0 : Fin 2)
        omega⟩,
     ⟨x.1.1 1, Nat.lt_succ_of_le <| by
        have hx := Finset.mem_antidiagonal.mp x.2
        have h : x.1.1 1 + x.1.2 1 = gamma 1 := by simpa using DFunLike.congr_fun hx (1 : Fin 2)
        omega⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hfst : x.1.1 = y.1.1 := by
      apply Finsupp.ext
      intro i
      fin_cases i
      · exact congr_arg (fun z => z.1.1) hxy
      · exact congr_arg (fun z => z.2.1) hxy
    apply Prod.ext hfst
    apply Finsupp.ext
    intro i
    have hx := DFunLike.congr_fun (Finset.mem_antidiagonal.mp x.2) i
    have hy := DFunLike.congr_fun (Finset.mem_antidiagonal.mp y.2) i
    have hi := DFunLike.congr_fun hfst i
    dsimp at hx hy hi
    omega
  simpa [f] using Fintype.card_le_of_injective f hf

theorem card_antidiagonal_bivar_le_sq (gamma : Fin 2 →₀ Nat) :
    (Finset.antidiagonal gamma).card <= (bivarTotal gamma + 1) ^ 2 := by
  refine (card_antidiagonal_bivar_le gamma).trans ?_
  have hzero : gamma 0 + 1 <= bivarTotal gamma + 1 := by
    dsimp [bivarTotal]
    omega
  have hone : gamma 1 + 1 <= bivarTotal gamma + 1 := by
    dsimp [bivarTotal]
    omega
  simpa [pow_two] using Nat.mul_le_mul hzero hone

/-- Filtering monomials cannot increase total degree. -/
theorem sharpLowPart_totalDegree_le (D : Nat)
    (p : MvPolynomial (Fin 2) Real) :
    (sharpLowPart D p).totalDegree <= p.totalDegree := by
  unfold MvPolynomial.totalDegree sharpLowPart
  apply Finset.sup_mono
  intro alpha halpha
  exact (Finset.mem_filter.mp halpha).1

/-- Filtering monomials cannot increase total degree. -/
theorem sharpHighPart_totalDegree_le (D : Nat)
    (p : MvPolynomial (Fin 2) Real) :
    (sharpHighPart D p).totalDegree <= p.totalDegree := by
  unfold MvPolynomial.totalDegree sharpHighPart
  apply Finset.sup_mono
  intro alpha halpha
  exact (Finset.mem_filter.mp halpha).1

/-- Every monomial surviving in the SOS tail has total degree at least the
splitting threshold. -/
theorem sharpTailPolynomial_support_degree {N D : Nat}
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    {gamma : Fin 2 →₀ Nat}
    (hgamma : gamma ∈ (sharpTailPolynomial D q).support) :
    D <= bivarTotal gamma := by
  by_contra hnot
  have hlt : bivarTotal gamma < D := Nat.lt_of_not_ge hnot
  have hcoeff := MvPolynomial.mem_support_iff.mp hgamma
  rw [sharpTailPolynomial_coeff_eq] at hcoeff
  apply hcoeff
  apply Finset.sum_eq_zero
  intro x hx
  have hxadd := Finset.mem_antidiagonal.mp hx
  have hxzero : x.1 0 + x.2 0 = gamma 0 := by
    exact DFunLike.congr_fun hxadd (0 : Fin 2)
  have hxone : x.1 1 + x.2 1 = gamma 1 := by
    exact DFunLike.congr_fun hxadd (1 : Fin 2)
  have hxoneDegree : bivarTotal x.1 < D := by
    dsimp [bivarTotal] at *
    omega
  have hxtwoDegree : bivarTotal x.2 < D := by
    dsimp [bivarTotal] at *
    omega
  have hhighOne : (fun k => (sharpHighPart D (q k)).coeff x.1) =
      fun _ => 0 := by
    funext k
    rw [sharpHighPart_coeff, finsupp_sum_fin_two, ite_eq_right]
    omega
  have hhighTwo : (fun k => (sharpHighPart D (q k)).coeff x.2) =
      fun _ => 0 := by
    funext k
    rw [sharpHighPart_coeff, finsupp_sum_fin_two, ite_eq_right]
    omega
  rw [hhighOne, hhighTwo]
  simp [OptimalConvergenceRates.vecDot]

/-- The tail of roots of degree at most `d` has degree at most `2*d`. -/
theorem sharpTailPolynomial_totalDegree_le {N D d : Nat}
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hdeg : forall k, (q k).totalDegree <= d) :
    (sharpTailPolynomial D q).totalDegree <= 2 * d := by
  rw [sharpTailPolynomial]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _hk
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · calc
      (C (2 : Real) *
          (sharpLowPart D (q k) * sharpHighPart D (q k))).totalDegree
          <= (sharpLowPart D (q k) * sharpHighPart D (q k)).totalDegree := by
            simpa only [MvPolynomial.C_mul'] using
              MvPolynomial.totalDegree_smul_le (2 : Real)
                (sharpLowPart D (q k) * sharpHighPart D (q k))
      _ <= (sharpLowPart D (q k)).totalDegree +
          (sharpHighPart D (q k)).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ <= d + d := Nat.add_le_add
            ((sharpLowPart_totalDegree_le D (q k)).trans (hdeg k))
            ((sharpHighPart_totalDegree_le D (q k)).trans (hdeg k))
      _ = 2 * d := by omega
  · calc
      ((sharpHighPart D (q k)) ^ 2).totalDegree
          <= 2 * (sharpHighPart D (q k)).totalDegree :=
            MvPolynomial.totalDegree_pow _ 2
      _ <= 2 * d := Nat.mul_le_mul_left 2
            ((sharpHighPart_totalDegree_le D (q k)).trans (hdeg k))

/-- Closed form of the tail coefficient estimate. -/
theorem abs_sharpTailPolynomial_coeff_le_closed {N D d : Nat} {M : Real}
    (q : Fin N -> MvPolynomial (Fin 2) Real)
    (hM : 0 <= M) (hdeg : forall k, (q k).totalDegree <= d)
    (hbound : forall a b : Real,
      0 <= a -> a <= (1 : Real) / 4 ->
      0 <= b -> b <= (1 : Real) / 4 ->
      OptimalConvergenceRates.interiorVecNorm
        (fun k => MvPolynomial.eval ![a, b] (q k)) <= M)
    (gamma : Fin 2 →₀ Nat) :
    |(sharpTailPolynomial D q).coeff gamma| <=
      3 * (bivarTotal gamma + 1 : Nat) ^ 2 *
        (8 : Real) ^ bivarTotal gamma *
        (d : Real) ^ (2 * bivarTotal gamma) * M ^ 2 := by
  calc
    |(sharpTailPolynomial D q).coeff gamma| <=
        ∑ _x ∈ Finset.antidiagonal gamma,
          3 * (8 : Real) ^ bivarTotal gamma *
            (d : Real) ^ (2 * bivarTotal gamma) * M ^ 2 := by
      simpa [bivarTotal] using
        abs_sharpTailPolynomial_coeff_le q hM hdeg hbound gamma
    _ = ((Finset.antidiagonal gamma).card : Real) *
          (3 * (8 : Real) ^ bivarTotal gamma *
            (d : Real) ^ (2 * bivarTotal gamma) * M ^ 2) := by
      simp
    _ <= ((bivarTotal gamma + 1 : Nat) ^ 2 : Real) *
          (3 * (8 : Real) ^ bivarTotal gamma *
            (d : Real) ^ (2 * bivarTotal gamma) * M ^ 2) := by
      gcongr
      exact_mod_cast card_antidiagonal_bivar_le_sq gamma
    _ = _ := by ring

end OptimalConvergenceRates.GeneralArchimedean

end
