/-
  Localized-product certificates for the Putinar extension.

  This file formalizes the finite auxiliary-cube identity from the manuscript
  and substitutes the localized Chebyshev factors into it.  The result works
  for an arbitrary finite family of coordinates and records canonical total
  certificate degree.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarPair
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.ConeWitnesses

open MvPolynomial Finset Polynomial
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

variable {n j : ℕ}

/-! ## The finite auxiliary-cube certificate -/

/-- The square-free coordinate monomial indexed by `L`. -/
def cubeVariableProduct (L : Finset (Fin j)) : MvPolynomial (Fin j) ℝ :=
  ∏ i ∈ L, X i

/-- The product of the coordinates of `L` preceding `i` in the canonical
linear order. -/
def cubeVariablePrefix (L : Finset (Fin j)) (i : Fin j) :
    MvPolynomial (Fin j) ℝ :=
  ∏ t ∈ L.filter (fun t ↦ t < i), X t

/-- The coordinate monomial has degree at most the size of its support. -/
theorem cubeVariableProduct_totalDegree_le_card (L : Finset (Fin j)) :
    (cubeVariableProduct L).totalDegree ≤ L.card := by
  unfold cubeVariableProduct
  calc
    (∏ i ∈ L, (X i : MvPolynomial (Fin j) ℝ)).totalDegree ≤
        ∑ i ∈ L, (X i : MvPolynomial (Fin j) ℝ).totalDegree :=
      MvPolynomial.totalDegree_finsetProd L _
    _ = L.card := by simp

/-- The ordered telescoping identity for a square-free coordinate monomial. -/
theorem one_sub_cubeVariableProduct_sq (L : Finset (Fin j)) :
    1 - cubeVariableProduct L ^ 2 =
      ∑ i ∈ L,
        cubeVariablePrefix L i ^ 2 * BoxSemialgebraicGenerator i := by
  classical
  have h := Finset.prod_one_sub_ordered L
    (fun i ↦ (1 - (X i : MvPolynomial (Fin j) ℝ) ^ 2))
  simp only [sub_sub_cancel] at h
  unfold cubeVariableProduct cubeVariablePrefix BoxSemialgebraicGenerator
  simp_rw [← Finset.prod_pow]
  have hsum :
      ∑ i ∈ L, (1 - (X i : MvPolynomial (Fin j) ℝ) ^ 2) *
          ∏ t ∈ L.filter (fun t ↦ t < i), X t ^ 2 =
        ∑ i ∈ L, (∏ t ∈ L.filter (fun t ↦ t < i), X t ^ 2) *
          (1 - X i ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [← hsum, h]
  ring

/-- For every square-free monomial `z_L`, the polynomial `1 + z_L` has an
explicit quadratic-module certificate of canonical order `2j`. -/
theorem one_add_cubeVariableProduct_mem_BoxQuadraticModule
    (L : Finset (Fin j)) :
    1 + cubeVariableProduct L ∈ BoxQuadraticModule j (2 * j) := by
  classical
  let z := cubeVariableProduct L
  let free : MvPolynomial (Fin j) ℝ :=
    MvPolynomial.C (1 / 2 : ℝ) * (1 + z) ^ 2
  let term : Fin j → MvPolynomial (Fin j) ℝ := fun i ↦
    if i ∈ L then
      MvPolynomial.C (1 / 2 : ℝ) *
        (cubeVariablePrefix L i ^ 2 * BoxSemialgebraicGenerator i)
    else 0
  have hzdegree : z.totalDegree ≤ j := by
    exact (cubeVariableProduct_totalDegree_le_card L).trans (by
      simpa using Finset.card_le_card (Finset.subset_univ L))
  have hfree_degree : free.totalDegree ≤ 2 * j := by
    dsimp [free]
    have hadd : (1 + z).totalDegree ≤ j := by
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le (by simp) hzdegree)
    have hpow : ((1 + z) ^ 2).totalDegree ≤ 2 * j :=
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hadd)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hpow)
  have hfree : free ∈ BoxQuadraticModule j (2 * j) := by
    apply isSOS_mem_BoxQuadraticModule
    · dsimp [free]
      exact IsSOS_nonneg_scale (IsSOS_sq _) (1 / 2 : ℝ) (by norm_num)
    · exact hfree_degree
  have hterm (i : Fin j) : term i ∈ BoxQuadraticModule j (2 * j) := by
    by_cases hi : i ∈ L
    · rw [show term i = MvPolynomial.C (1 / 2 : ℝ) *
          (cubeVariablePrefix L i ^ 2 * BoxSemialgebraicGenerator i) by
            simp [term, hi]]
      have hprefix :
          (cubeVariablePrefix L i).totalDegree ≤
            (L.filter (fun t ↦ t < i)).card := by
        simpa [cubeVariablePrefix, cubeVariableProduct] using
          cubeVariableProduct_totalDegree_le_card
            (L.filter (fun t ↦ t < i))
      have hprefix_sq :
          (cubeVariablePrefix L i ^ 2).totalDegree ≤
            2 * (L.filter (fun t ↦ t < i)).card :=
        (MvPolynomial.totalDegree_pow _ _).trans
          (Nat.mul_le_mul_left 2 hprefix)
      have hmultiplier :
          (MvPolynomial.C (1 / 2 : ℝ) *
            cubeVariablePrefix L i ^ 2).totalDegree ≤
              2 * (L.filter (fun t ↦ t < i)).card :=
        (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hprefix_sq)
      have hproper : (L.filter (fun t ↦ t < i)).card < L.card :=
        Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨i, hi, by simp⟩)
      have hLj : L.card ≤ j := by
        simpa using Finset.card_le_card (Finset.subset_univ L)
      have hdegree :
          ((MvPolynomial.C (1 / 2 : ℝ) * cubeVariablePrefix L i ^ 2) *
            BoxSemialgebraicGenerator i).totalDegree ≤ 2 * j := by
        calc
          ((MvPolynomial.C (1 / 2 : ℝ) * cubeVariablePrefix L i ^ 2) *
              BoxSemialgebraicGenerator i).totalDegree ≤
              (MvPolynomial.C (1 / 2 : ℝ) *
                cubeVariablePrefix L i ^ 2).totalDegree +
                (BoxSemialgebraicGenerator i).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ ≤ 2 * (L.filter (fun t ↦ t < i)).card + 2 :=
            Nat.add_le_add hmultiplier
              (boxSemialgebraicGenerator_totalDegree_le_two i)
          _ ≤ 2 * j := by omega
      have hmem := sos_mul_boxSemialgebraicGenerator_mem_BoxQuadraticModule i
        (MvPolynomial.C (1 / 2 : ℝ) * cubeVariablePrefix L i ^ 2)
        (IsSOS_nonneg_scale (IsSOS_sq _) (1 / 2 : ℝ) (by norm_num)) hdegree
      simpa only [mul_assoc] using hmem
    · simp [term, hi, zero_mem_BoxQuadraticModule]
  have hsum : ∑ i, term i ∈ BoxQuadraticModule j (2 * j) :=
    BoxQuadraticModule_sum term hterm
  have hadd := BoxQuadraticModule_add hfree hsum
  have hidentity : free + ∑ i, term i = 1 + z := by
    have hsumterm :
        (∑ i : Fin j, if i ∈ L then
            MvPolynomial.C (1 / 2 : ℝ) *
              (cubeVariablePrefix L i ^ 2 * BoxSemialgebraicGenerator i)
          else 0) =
          MvPolynomial.C (1 / 2 : ℝ) *
            ∑ i ∈ L, cubeVariablePrefix L i ^ 2 *
              BoxSemialgebraicGenerator i := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.mul_sum]
    dsimp [free, term]
    rw [hsumterm, ← one_sub_cubeVariableProduct_sq L]
    dsimp [z]
    have hc :
        MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.C 2 =
          (1 : MvPolynomial (Fin j) ℝ) := by
      rw [← MvPolynomial.C_mul]
      norm_num
    ring_nf
    change MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.C 2 +
      MvPolynomial.C (1 / 2 : ℝ) * z * MvPolynomial.C 2 = 1 + z
    calc
      _ = (MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.C 2) +
          (MvPolynomial.C (1 / 2 : ℝ) * MvPolynomial.C 2) * z := by ring
      _ = 1 + z := by rw [hc]; ring
  rw [hidentity] at hadd
  exact hadd

/-- The auxiliary polynomial used for localized products. -/
def putinarAuxiliaryPolynomial (j : ℕ) : MvPolynomial (Fin j) ℝ :=
  1 + MvPolynomial.C ((2 : ℝ)⁻¹ ^ j) * ∏ i : Fin j, (1 + X i)

/-- The finite auxiliary-cube identity is a quadratic-module certificate of
canonical order `2j`. -/
theorem putinarAuxiliaryPolynomial_mem_BoxQuadraticModule (j : ℕ) :
    putinarAuxiliaryPolynomial j ∈ BoxQuadraticModule j (2 * j) := by
  have hsum :
      (∑ L : Finset (Fin j), (1 + cubeVariableProduct L)) ∈
        BoxQuadraticModule j (2 * j) :=
    BoxQuadraticModule_sum _ (fun L ↦
      one_add_cubeVariableProduct_mem_BoxQuadraticModule L)
  have hscaled := BoxQuadraticModule_nonneg_scale ((2 : ℝ)⁻¹ ^ j)
    (by positivity) hsum
  have hidentity :
      MvPolynomial.C ((2 : ℝ)⁻¹ ^ j) *
          (∑ L : Finset (Fin j), (1 + cubeVariableProduct L)) =
        putinarAuxiliaryPolynomial j := by
    rw [Finset.sum_add_distrib]
    rw [show (∑ _L : Finset (Fin j), (1 : MvPolynomial (Fin j) ℝ)) =
        (2 : MvPolynomial (Fin j) ℝ) ^ j by simp]
    rw [show (∑ L : Finset (Fin j), cubeVariableProduct L) =
        ∏ i : Fin j, (1 + X i : MvPolynomial (Fin j) ℝ) by
          rw [Finset.prod_one_add]
          simp [cubeVariableProduct]]
    unfold putinarAuxiliaryPolynomial
    rw [mul_add]
    have hcoeff : (2 : ℝ)⁻¹ ^ j * 2 ^ j = 1 := by
      rw [← mul_pow]
      norm_num
    have htwoPoly : (2 : MvPolynomial (Fin j) ℝ) ^ j =
        MvPolynomial.C ((2 : ℝ) ^ j) := by
      change MvPolynomial.C 2 ^ j = MvPolynomial.C (2 ^ j)
      rw [map_pow]
    rw [htwoPoly, ← MvPolynomial.C_mul, hcoeff]
    simp
  rw [hidentity] at hscaled
  exact hscaled

/-! ## Localized Chebyshev substitution -/

/-- The auxiliary variable `z_t` is replaced by `1 - 2 T_k(X_{i_t})²`. -/
def putinarLocalizedSubstitution (k : ℕ) (target : Fin j → Fin n) :
    Fin j → MvPolynomial (Fin n) ℝ := fun t ↦
  1 - MvPolynomial.C 2 * embedUnivariate (target t) (chebyshevT k) ^ 2

/-- Each localized substitution polynomial has degree at most `2k`. -/
theorem putinarLocalizedSubstitution_totalDegree_le
    (k : ℕ) (target : Fin j → Fin n) (t : Fin j) :
    (putinarLocalizedSubstitution k target t).totalDegree ≤ 2 * k := by
  unfold putinarLocalizedSubstitution
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp
  · have hT :
        (embedUnivariate (target t) (chebyshevT k)).totalDegree ≤ k := by
      exact (totalDegree_embedUnivariate _ _).trans (by
        rw [natDegree_chebyshevT])
    have hpow :
        (embedUnivariate (target t) (chebyshevT k) ^ 2).totalDegree ≤
          2 * k :=
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hT)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hpow)

/-- Each source generator maps to an explicit SOS multiple of the selected
target generator. -/
theorem aeval_generator_putinarLocalizedSubstitution
    (k : ℕ) (hk : 1 ≤ k) (target : Fin j → Fin n) (t : Fin j) :
    MvPolynomial.aeval (putinarLocalizedSubstitution k target)
        (BoxSemialgebraicGenerator t) =
      (MvPolynomial.C 4 *
          (embedUnivariate (target t) (chebyshevT k) *
            putinarPairU k (target t)) ^ 2) *
        BoxSemialgebraicGenerator (target t) := by
  simp only [BoxSemialgebraicGenerator, map_sub, map_one, map_pow,
    MvPolynomial.aeval_X]
  change
    1 - (1 - 2 * embedUnivariate (target t) (chebyshevT k) ^ 2) ^ 2 =
      (4 * (embedUnivariate (target t) (chebyshevT k) *
        putinarPairU k (target t)) ^ 2) *
        (1 - X (target t) ^ 2)
  have hpell := one_sub_embed_chebyshevT_sq k hk (target t)
  simp only [BoxSemialgebraicGenerator] at hpell
  calc
    1 - (1 - 2 * embedUnivariate (target t) (chebyshevT k) ^ 2) ^ 2 =
        4 * embedUnivariate (target t) (chebyshevT k) ^ 2 *
          (1 - embedUnivariate (target t) (chebyshevT k) ^ 2) := by ring
    _ = (4 * (embedUnivariate (target t) (chebyshevT k) *
          putinarPairU k (target t)) ^ 2) * (1 - X (target t) ^ 2) := by
      rw [hpell]
      ring

/-- The left side of the substituted auxiliary certificate is exactly the
localized product plus its correction. -/
theorem scale_aeval_putinarAuxiliaryPolynomial
    (k : ℕ) (hk : 1 ≤ k) (target : Fin j → Fin n) :
    MvPolynomial.C (putinarPairMu k ^ j) *
        MvPolynomial.aeval (putinarLocalizedSubstitution k target)
          (putinarAuxiliaryPolynomial j) =
      (∏ t : Fin j, putinarPairFactor k (target t)) +
        MvPolynomial.C (putinarPairMu k ^ j) := by
  let b : Fin j → MvPolynomial (Fin n) ℝ := fun t ↦
    BoxSemialgebraicGenerator (target t) * putinarPairU k (target t) ^ 2
  have hone (t : Fin j) :
      1 + putinarLocalizedSubstitution k target t = MvPolynomial.C 2 * b t := by
    change 1 + (1 - 2 * embedUnivariate (target t) (chebyshevT k) ^ 2) =
      2 * (BoxSemialgebraicGenerator (target t) *
        putinarPairU k (target t) ^ 2)
    have hpell := one_sub_embed_chebyshevT_sq k hk (target t)
    calc
      1 + (1 - 2 * embedUnivariate (target t) (chebyshevT k) ^ 2) =
          2 * (1 - embedUnivariate (target t) (chebyshevT k) ^ 2) := by ring
      _ = 2 * (BoxSemialgebraicGenerator (target t) *
          putinarPairU k (target t) ^ 2) := by rw [hpell]; ring
  have hprod_one :
      (∏ t : Fin j, (1 + putinarLocalizedSubstitution k target t)) =
        MvPolynomial.C ((2 : ℝ) ^ j) * ∏ t : Fin j, b t := by
    calc
      (∏ t : Fin j, (1 + putinarLocalizedSubstitution k target t)) =
          ∏ t : Fin j, (MvPolynomial.C 2 * b t) := by
        apply Finset.prod_congr rfl
        intro t ht
        exact hone t
      _ = (∏ _t : Fin j, (MvPolynomial.C 2 : MvPolynomial (Fin n) ℝ)) *
          ∏ t : Fin j, b t := Finset.prod_mul_distrib
      _ = MvPolynomial.C ((2 : ℝ) ^ j) * ∏ t : Fin j, b t := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [MvPolynomial.C_pow]
  have hprod_factor :
      (∏ t : Fin j, putinarPairFactor k (target t)) =
        MvPolynomial.C (putinarPairMu k ^ j) * ∏ t : Fin j, b t := by
    simp only [putinarPairFactor]
    change (∏ t : Fin j, MvPolynomial.C (putinarPairMu k) * b t) = _
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [MvPolynomial.C_pow]
  simp only [putinarAuxiliaryPolynomial, map_add, map_one, map_mul, map_prod,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [hprod_one, hprod_factor]
  have hcoeff : (2 : ℝ)⁻¹ ^ j * 2 ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have hcoeffC :
      MvPolynomial.C ((2 : ℝ)⁻¹ ^ j) * MvPolynomial.C ((2 : ℝ) ^ j) =
        (1 : MvPolynomial (Fin n) ℝ) := by
    rw [← MvPolynomial.C_mul, hcoeff]
    simp
  calc
    MvPolynomial.C (putinarPairMu k ^ j) *
        (1 + MvPolynomial.C ((2 : ℝ)⁻¹ ^ j) *
          (MvPolynomial.C ((2 : ℝ) ^ j) * ∏ t : Fin j, b t)) =
      MvPolynomial.C (putinarPairMu k ^ j) +
        MvPolynomial.C (putinarPairMu k ^ j) *
          (MvPolynomial.C ((2 : ℝ)⁻¹ ^ j) *
            MvPolynomial.C ((2 : ℝ) ^ j)) * ∏ t : Fin j, b t := by ring
    _ = MvPolynomial.C (putinarPairMu k ^ j) * ∏ t : Fin j, b t +
        MvPolynomial.C (putinarPairMu k ^ j) := by rw [hcoeffC]; ring

/-- The manuscript's arbitrary finite localized-product certificate.

For `j ≥ 2`, this is `A_J + μ^j ∈ Q` with every complete certificate
term of total degree at most `4jk`.  The proof actually holds for every `j`;
the lower bound is retained in the public statement to match its downstream
use, where empty and singleton products are handled more sharply. -/
theorem putinarLocalizedProduct_mem_BoxQuadraticModule
    (k : ℕ) (hk : 1 ≤ k) (target : Fin j → Fin n) (_hj : 2 ≤ j) :
    (∏ t : Fin j, putinarPairFactor k (target t)) +
        MvPolynomial.C (putinarPairMu k ^ j) ∈
      BoxQuadraticModule n (4 * j * k) := by
  let multiplier : Fin j → MvPolynomial (Fin n) ℝ := fun t ↦
    MvPolynomial.C 4 *
      (embedUnivariate (target t) (chebyshevT k) *
        putinarPairU k (target t)) ^ 2
  have hmapped :
      MvPolynomial.aeval (putinarLocalizedSubstitution k target)
          (putinarAuxiliaryPolynomial j) ∈
        BoxQuadraticModule n ((2 * k) * (2 * j)) := by
    apply aeval_mem_BoxQuadraticModule_of_generator_sos_mul
      (d := 2 * k) (r := 2 * j) (putinarLocalizedSubstitution k target)
      (putinarLocalizedSubstitution_totalDegree_le k target) target multiplier
    · intro t
      dsimp [multiplier]
      exact IsSOS_nonneg_scale (IsSOS_sq _) 4 (by norm_num)
    · intro t
      exact aeval_generator_putinarLocalizedSubstitution k hk target t
    · exact putinarAuxiliaryPolynomial_mem_BoxQuadraticModule j
  have hmu : 0 ≤ putinarPairMu k ^ j := by
    unfold putinarPairMu delta
    positivity
  have hscaled := BoxQuadraticModule_nonneg_scale (putinarPairMu k ^ j)
    hmu hmapped
  rw [scale_aeval_putinarAuxiliaryPolynomial k hk target] at hscaled
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled

/-- Finite-set form of the localized-product certificate.  This is the form
used by the preordering-to-quadratic-module conversion: for every coordinate
set `J` of size at least two, `A_J + μ^{|J|}` has canonical order
`4 * |J| * k`. -/
theorem putinarLocalizedProduct_finset_mem_BoxQuadraticModule
    (k : ℕ) (hk : 1 ≤ k) (J : Finset (Fin n)) (hJ : 2 ≤ J.card) :
    (∏ i ∈ J, putinarPairFactor k i) +
        MvPolynomial.C (putinarPairMu k ^ J.card) ∈
      BoxQuadraticModule n (4 * J.card * k) := by
  let e : Fin J.card ≃ {i // i ∈ J} := (J.orderIsoOfFin rfl).toEquiv
  let target : Fin J.card → Fin n := fun t ↦ (e t).1
  have hcert := putinarLocalizedProduct_mem_BoxQuadraticModule k hk target hJ
  have hprod :
      (∏ t : Fin J.card, putinarPairFactor k (target t)) =
        ∏ i ∈ J, putinarPairFactor k i := by
    calc
      (∏ t : Fin J.card, putinarPairFactor k (target t)) =
          ∏ x : {i // i ∈ J}, putinarPairFactor k x.1 := by
        apply Fintype.prod_equiv e
        intro t
        rfl
      _ = ∏ i ∈ J, putinarPairFactor k i := by
        symm
        exact Finset.prod_subtype J (fun _ ↦ Iff.rfl) _
  rw [hprod] at hcert
  exact hcert

end QuarticConvergence
end OptimalConvergenceRates

end
