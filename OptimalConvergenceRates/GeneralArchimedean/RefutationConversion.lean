/-
  Algebraic infrastructure for converting fixed preordering refutations to
  ordinary quadratic-module refutations.
-/
import OptimalConvergenceRates.GeneralArchimedean.ModuleOrder
import OptimalConvergenceRates.GeneralArchimedean.PositiveCoefficientCertificate
import OptimalConvergenceRates.GeneralArchimedean.RationalSquareRootPackage
import OptimalConvergenceRates.GeneralArchimedean.IntervalCertificateSubstitution

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates
namespace GeneralArchimedean
namespace RationalSquareRoot
namespace Package

variable {n m : ℕ}

abbrev substP {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  polynomialSubst a pkg.P

abbrev substV {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  polynomialSubst a pkg.V

abbrev substE {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  polynomialSubst a pkg.E


/-- Uniform coefficient envelope after substituting a polynomial of norm at
most `G` into any of the three package polynomials. -/
def substitutionCoefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta) (G : ℝ) : ℝ :=
  pkg.coefficientBound * G ^ pkg.degreeBound

theorem one_le_substitutionCoefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta)
    {G : ℝ} (hG : 1 ≤ G) :
    1 ≤ pkg.substitutionCoefficientBound G := by
  unfold substitutionCoefficientBound
  exact one_le_mul_of_one_le_of_one_le pkg.one_le_coefficientBound
    (one_le_pow₀ hG)

private theorem P_degree_le_degreeBound
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    pkg.P.natDegree ≤ pkg.degreeBound := by
  calc
    pkg.P.natDegree ≤ 2 * pkg.ell * (pkg.J + 1) := pkg.P_degree_le
    _ ≤ 4 * pkg.ell * (pkg.J + 1) :=
      Nat.mul_le_mul_right (pkg.J + 1)
        (Nat.mul_le_mul_right pkg.ell (by norm_num))
    _ = pkg.degreeBound := rfl

private theorem V_degree_le_degreeBound
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    pkg.V.natDegree ≤ pkg.degreeBound := by
  calc
    pkg.V.natDegree ≤ 2 * pkg.ell * (pkg.J + 1) := pkg.V_degree_le
    _ ≤ 4 * pkg.ell * (pkg.J + 1) :=
      Nat.mul_le_mul_right (pkg.J + 1)
        (Nat.mul_le_mul_right pkg.ell (by norm_num))
    _ = pkg.degreeBound := rfl

theorem substP_coeffL1Norm_le
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (pkg.substP a) ≤ pkg.substitutionCoefficientBound G := by
  calc
    coeffL1Norm (pkg.substP a) ≤
        embeddedPolynomialCoeffL1Norm pkg.P * G ^ pkg.P.natDegree :=
      polynomialSubst_coeffL1Norm_le_embedded a pkg.P hG ha
    _ ≤ pkg.coefficientBound * G ^ pkg.degreeBound := by
      exact mul_le_mul pkg.P_coeffL1Norm_le_coefficientBound
        (pow_le_pow_right₀ hG pkg.P_degree_le_degreeBound)
        (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans hG) _)
        ((by norm_num : (0 : ℝ) ≤ 1).trans pkg.one_le_coefficientBound)
    _ = pkg.substitutionCoefficientBound G := rfl

theorem substV_coeffL1Norm_le
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (pkg.substV a) ≤ pkg.substitutionCoefficientBound G := by
  calc
    coeffL1Norm (pkg.substV a) ≤
        embeddedPolynomialCoeffL1Norm pkg.V * G ^ pkg.V.natDegree :=
      polynomialSubst_coeffL1Norm_le_embedded a pkg.V hG ha
    _ ≤ pkg.coefficientBound * G ^ pkg.degreeBound := by
      exact mul_le_mul pkg.V_coeffL1Norm_le_coefficientBound
        (pow_le_pow_right₀ hG pkg.V_degree_le_degreeBound)
        (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans hG) _)
        ((by norm_num : (0 : ℝ) ≤ 1).trans pkg.one_le_coefficientBound)
    _ = pkg.substitutionCoefficientBound G := rfl

theorem substE_coeffL1Norm_le
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (pkg.substE a) ≤ pkg.substitutionCoefficientBound G := by
  calc
    coeffL1Norm (pkg.substE a) ≤
        embeddedPolynomialCoeffL1Norm pkg.E * G ^ pkg.E.natDegree :=
      polynomialSubst_coeffL1Norm_le_embedded a pkg.E hG ha
    _ ≤ pkg.coefficientBound * G ^ pkg.degreeBound := by
      exact mul_le_mul pkg.E_coeffL1Norm_le_coefficientBound
        (pow_le_pow_right₀ hG pkg.E_degree_le)
        (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans hG) _)
        ((by norm_num : (0 : ℝ) ≤ 1).trans pkg.one_le_coefficientBound)
    _ = pkg.substitutionCoefficientBound G := rfl

theorem substP_sq_coeffL1Norm_le
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (pkg.substP a ^ 2) ≤
      pkg.substitutionCoefficientBound G ^ 2 :=
  (coeffL1Norm_pow_le (pkg.substP a) 2).trans
    (pow_le_pow_left₀ (coeffL1Norm_nonneg _) (pkg.substP_coeffL1Norm_le a hG ha) 2)

theorem substV_sq_coeffL1Norm_le
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) {G : ℝ}
    (hG : 1 ≤ G) (ha : coeffL1Norm a ≤ G) :
    coeffL1Norm (pkg.substV a ^ 2) ≤
      pkg.substitutionCoefficientBound G ^ 2 :=
  (coeffL1Norm_pow_le (pkg.substV a) 2).trans
    (pow_le_pow_left₀ (coeffL1Norm_nonneg _) (pkg.substV_coeffL1Norm_le a hG ha) 2)
theorem subst_identity
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) (hδ : 0 < δ) :
    pkg.substP a ^ 2 - a * pkg.substV a ^ 2 = pkg.substE a :=
  normalizedRationalSquareRoot_subst_identity
    a hδ pkg.ell_pos pkg.J

theorem substE_isSOS
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) (hδ : 0 < δ) :
    IsSOS (pkg.substE a) :=
  normalizedError_subst_isSOS a hδ.le pkg.ell pkg.J

theorem substV_sq_isSOS
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) :
    IsSOS (pkg.substV a ^ 2) :=
  IsSOS_sq _

/-- Exact replacement after multiplying a preordering identity by the
common denominator. -/
theorem generator_mul_substV_sq
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) (hδ : 0 < δ) :
    a * pkg.substV a ^ 2 = pkg.substP a ^ 2 - pkg.substE a := by
  have h := pkg.subst_identity a hδ
  linear_combination -h

/-- The normalized denominator square is above one in the module order
whenever the substituted generator itself belongs to the module. -/
theorem one_le_substV_sq
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    {a : MvPolynomial (Fin n) ℝ}
    (ha : QuadraticModuleMem g a) (hδ : 0 < δ) :
    ModuleLE g 1 (pkg.substV a ^ 2) := by
  change QuadraticModuleMem g (pkg.substV a ^ 2 - 1)
  exact normalizedDenominator_subst_sq_sub_one_mem
    ha hδ pkg.ell_pos pkg.J

theorem substV_sq_totalDegree_le
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) :
    (pkg.substV a ^ 2).totalDegree ≤
      pkg.degreeBound * a.totalDegree := by
  rw [← polynomialSubst_pow]
  exact (polynomialSubst_totalDegree_le a (pkg.V ^ 2)).trans
    (Nat.mul_le_mul_right a.totalDegree pkg.V_sq_degree_le)


theorem substP_sq_totalDegree_le
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) :
    (pkg.substP a ^ 2).totalDegree ≤
      pkg.degreeBound * a.totalDegree := by
  rw [← polynomialSubst_pow]
  exact (polynomialSubst_totalDegree_le a (pkg.P ^ 2)).trans
    (Nat.mul_le_mul_right a.totalDegree pkg.P_sq_degree_le)

theorem substE_totalDegree_le
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : MvPolynomial (Fin n) ℝ) :
    (pkg.substE a).totalDegree ≤
      pkg.degreeBound * a.totalDegree :=
  (polynomialSubst_totalDegree_le a pkg.E).trans
    (Nat.mul_le_mul_right a.totalDegree pkg.E_degree_le)

/-- Degree-tracked denominator-square order relation. -/
theorem one_le_substV_sq_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    {a : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (ha : a ∈ GenQuadraticModule g r) (hδ : 0 < δ) :
    ModuleLEAt g (r + pkg.degreeBound * a.totalDegree)
      1 (pkg.substV a ^ 2) := by
  change pkg.substV a ^ 2 - 1 ∈
    GenQuadraticModule g (r + pkg.degreeBound * a.totalDegree)
  simpa [degreeBound] using
    normalizedDenominator_subst_sq_sub_one_mem_at
      ha hδ pkg.ell_pos pkg.J


end Package
end RationalSquareRoot

open RationalSquareRoot RationalSquareRoot.Package

/-- Product of all squared rational-square-root denominators. -/
def denominatorProduct {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∏ i : Fin s, (pkg i).substV (a i) ^ 2

theorem denominatorProduct_isSOS
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ) :
    IsSOS (denominatorProduct pkg a) := by
  apply IsSOS_finset_prod
  intro i hi
  exact (pkg i).substV_sq_isSOS (a i)

/-- Telescoping the individual denominator relations proves that the common
denominator is above one in module order. -/
theorem one_le_denominatorProduct
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hδ : 0 < δ) :
    ModuleLE g 1 (denominatorProduct pkg a) := by
  apply ModuleLE.one_le_prod Finset.univ
  · intro i hi
    exact (pkg i).substV_sq_isSOS (a i)
  · intro i hi
    exact (pkg i).one_le_substV_sq (ha i) hδ


/-- Explicit common order for a denominator product built from one package. -/
theorem one_le_denominatorProduct_const
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ) {r d : ℕ}
    (ha : ∀ i, a i ∈ GenQuadraticModule g r)
    (hdegree : ∀ i, (a i).totalDegree ≤ d)
    (hδ : 0 < δ) :
    ModuleLEAt g
      (s * ((r + pkg.degreeBound * d) + pkg.degreeBound * d))
      1 (denominatorProduct (fun _ => pkg) a) := by
  have hrel : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      ModuleLEAt g (r + pkg.degreeBound * d) 1
        (pkg.substV (a i) ^ 2) := by
    intro i hi
    exact (pkg.one_le_substV_sq_at (ha i) hδ).mono
      (Nat.add_le_add_left
        (Nat.mul_le_mul_left pkg.degreeBound (hdegree i)) r)
  have hfactorDegree : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      (pkg.substV (a i) ^ 2).totalDegree ≤
        pkg.degreeBound * d := by
    intro i hi
    exact (pkg.substV_sq_totalDegree_le (a i)).trans
      (Nat.mul_le_mul_left pkg.degreeBound (hdegree i))
  simpa [denominatorProduct] using
    ModuleLEAt.one_le_prod (Finset.univ : Finset (Fin s))
      (fun i => pkg.substV (a i) ^ 2)
      (r + pkg.degreeBound * d) (pkg.degreeBound * d)
      (fun i hi => pkg.substV_sq_isSOS (a i))
      hfactorDegree hrel

theorem denominatorProduct_sub_one_mem
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hδ : 0 < δ) :
    QuadraticModuleMem g (denominatorProduct pkg a - 1) := by
  simpa [ModuleLE] using one_le_denominatorProduct pkg a ha hδ

/-- The common denominator splits into the factors indexed by a subset and
its complement. -/
theorem denominatorProduct_eq_subset_mul_compl
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    denominatorProduct pkg a =
      (∏ i ∈ I, (pkg i).substV (a i) ^ 2) *
        ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2 := by
  classical
  exact (Finset.prod_mul_prod_compl I
    (fun i => (pkg i).substV (a i) ^ 2)).symm

/-- One term in the exact common-denominator expansion. -/
def convertedTerm
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  sigma I *
      (∏ i ∈ I,
        ((pkg i).substP (a i) ^ 2 - (pkg i).substE (a i))) *
    ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2

/-- Multiplying a preordering identity by the common squared denominator and
using a_i V_i^2 = P_i^2-E_i gives the exact converted expansion. -/
theorem multiply_preordering_identity
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hδ : 0 < δ)
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i) :
    -(denominatorProduct pkg a) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        convertedTerm pkg a sigma I := by
  classical
  calc
    -(denominatorProduct pkg a) =
        (-1 : MvPolynomial (Fin n) ℝ) * denominatorProduct pkg a := by ring
    _ = (∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i) * denominatorProduct pkg a := by
          rw [← hidentity]
    _ = ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        (sigma I * ∏ i ∈ I, a i) * denominatorProduct pkg a := by
          rw [Finset.sum_mul]
    _ = ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        convertedTerm pkg a sigma I := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [denominatorProduct_eq_subset_mul_compl pkg a I]
          dsimp [convertedTerm]
          have hrepl :
              ∏ i ∈ I, (a i * (pkg i).substV (a i) ^ 2) =
                ∏ i ∈ I,
                  ((pkg i).substP (a i) ^ 2 -
                    (pkg i).substE (a i)) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact (pkg i).generator_mul_substV_sq (a i) hδ
          calc
            (sigma I * ∏ i ∈ I, a i) *
                ((∏ i ∈ I, (pkg i).substV (a i) ^ 2) *
                  ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2) =
              sigma I *
                ((∏ i ∈ I, a i) *
                  ∏ i ∈ I, (pkg i).substV (a i) ^ 2) *
                ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2 := by ring
            _ = sigma I *
                (∏ i ∈ I, (a i * (pkg i).substV (a i) ^ 2)) *
                  ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2 := by
                    rw [Finset.prod_mul_distrib]
            _ = sigma I *
                (∏ i ∈ I,
                  ((pkg i).substP (a i) ^ 2 -
                    (pkg i).substE (a i))) *
                  ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2 := by
                    rw [hrepl]

/-- An unsigned summand in the expansion of the P_i^2-E_i factors. -/
def errorExpansionTerm
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I K : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  sigma I *
      (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2) *
      (∏ i ∈ K, (pkg i).substE (a i)) *
    ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2

/-- Every unsigned error-expansion term is SOS when the original
preordering multiplier is SOS. -/
theorem errorExpansionTerm_isSOS
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hδ : 0 < δ) (I K : Finset (Fin s)) :
    IsSOS (errorExpansionTerm pkg a sigma I K) := by
  classical
  have hP : IsSOS (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_sq _
  have hE : IsSOS (∏ i ∈ K, (pkg i).substE (a i)) := by
    apply IsSOS_finset_prod
    intro i hi
    exact (pkg i).substE_isSOS (a i) hδ
  have hV : IsSOS (∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_sq _
  exact IsSOS_mul (IsSOS_mul (IsSOS_mul (hsigma I) hP) hE) hV

/-- Exact signed powerset expansion of one converted preordering term. -/
theorem convertedTerm_eq_errorExpansion
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    convertedTerm pkg a sigma I =
      ∑ K ∈ I.powerset,
        (-1 : MvPolynomial (Fin n) ℝ) ^ K.card *
          errorExpansionTerm pkg a sigma I K := by
  classical
  dsimp [convertedTerm, errorExpansionTerm]
  rw [Finset.prod_sub]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro K hK
  ring

/-- Sum of the even-cardinality error terms for one original subset. -/
def evenErrorSum
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ K ∈ I.powerset.filter (fun K => Even K.card),
    errorExpansionTerm pkg a sigma I K

/-- Sum of the odd-cardinality error terms for one original subset. -/
def oddErrorSum
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
    errorExpansionTerm pkg a sigma I K

theorem evenErrorSum_isSOS
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hδ : 0 < δ) (I : Finset (Fin s)) :
    IsSOS (evenErrorSum pkg a sigma I) := by
  classical
  apply IsSOS_sum_finset
  intro K hK
  exact errorExpansionTerm_isSOS pkg a sigma hsigma hδ I K

theorem oddErrorSum_isSOS
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hδ : 0 < δ) (I : Finset (Fin s)) :
    IsSOS (oddErrorSum pkg a sigma I) := by
  classical
  apply IsSOS_sum_finset
  intro K hK
  exact errorExpansionTerm_isSOS pkg a sigma hsigma hδ I K

theorem convertedTerm_eq_even_sub_odd
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    convertedTerm pkg a sigma I =
      evenErrorSum pkg a sigma I - oddErrorSum pkg a sigma I := by
  classical
  rw [convertedTerm_eq_errorExpansion]
  let term := fun K : Finset (Fin s) =>
    errorExpansionTerm pkg a sigma I K
  let signed := fun K : Finset (Fin s) =>
    (-1 : MvPolynomial (Fin n) ℝ) ^ K.card * term K
  have heven :
      ∑ K ∈ I.powerset.filter (fun K => Even K.card), signed K =
        evenErrorSum pkg a sigma I := by
    dsimp [evenErrorSum]
    apply Finset.sum_congr rfl
    intro K hK
    have hparity : Even K.card := (Finset.mem_filter.mp hK).2
    have hsign :
        (-1 : MvPolynomial (Fin n) ℝ) ^ K.card = 1 :=
      hparity.neg_one_pow
    dsimp [signed, term]
    rw [hsign, one_mul]
  have hodd :
      ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card), signed K =
        -(oddErrorSum pkg a sigma I) := by
    calc
      ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card), signed K =
          ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card), -(term K) := by
            apply Finset.sum_congr rfl
            intro K hK
            have hparity : Odd K.card :=
              Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hK).2
            have hsign :
                (-1 : MvPolynomial (Fin n) ℝ) ^ K.card = -1 :=
              (neg_one_pow_eq_neg_one_iff_odd
                (by
                  intro h
                  have h' := congrArg
                    (MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))) h
                  norm_num at h')).mpr hparity
            dsimp [signed]
            rw [hsign]
            ring
      _ = -(oddErrorSum pkg a sigma I) := by
            dsimp [oddErrorSum, term]
            rw [Finset.sum_neg_distrib]
  calc
    ∑ K ∈ I.powerset,
        (-1 : MvPolynomial (Fin n) ℝ) ^ K.card *
          errorExpansionTerm pkg a sigma I K =
      (∑ K ∈ I.powerset.filter (fun K => Even K.card), signed K) +
        ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card), signed K := by
          exact (Finset.sum_filter_add_sum_filter_not
            I.powerset (fun K => Even K.card) signed).symm
    _ = evenErrorSum pkg a sigma I - oddErrorSum pkg a sigma I := by
          rw [heven, hodd]
          ring

/-- Global even and odd SOS aggregates in the converted refutation. -/
def convertedEven
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
    evenErrorSum pkg a sigma I

def convertedOdd
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
    oddErrorSum pkg a sigma I

theorem convertedEven_isSOS
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I)) (hδ : 0 < δ) :
    IsSOS (convertedEven pkg a sigma) := by
  classical
  apply IsSOS_sum_finset
  intro I hI
  exact evenErrorSum_isSOS pkg a sigma hsigma hδ I

theorem convertedOdd_isSOS
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I)) (hδ : 0 < δ) :
    IsSOS (convertedOdd pkg a sigma) := by
  classical
  apply IsSOS_sum_finset
  intro I hI
  exact oddErrorSum_isSOS pkg a sigma hsigma hδ I

/-- The denominator-cleared refutation is exactly even SOS minus odd SOS. -/
theorem multiplied_refutation_eq_even_sub_odd
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hδ : 0 < δ)
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i) :
    -(denominatorProduct pkg a) =
      convertedEven pkg a sigma - convertedOdd pkg a sigma := by
  rw [multiply_preordering_identity pkg a sigma hδ hidentity]
  dsimp [convertedEven, convertedOdd]
  simp_rw [convertedTerm_eq_even_sub_odd]
  rw [Finset.sum_sub_distrib]

/-- The final algebraic step of refutation conversion.  Any absorption bound
with coefficients strictly below one turns the denominator-cleared identity
into a quadratic-module refutation of -1. -/
theorem refutation_of_absorption
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta alpha beta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hδ : 0 < δ)
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i)
    (halpha : alpha ≤ 1) (hbeta : beta < 1)
    (habsorb : ModuleLE g (convertedOdd pkg a sigma)
      (C alpha * convertedEven pkg a sigma +
        C beta * denominatorProduct pkg a)) :
    QuadraticModuleMem g (-1) := by
  let D := denominatorProduct pkg a
  let E := convertedEven pkg a sigma
  let O := convertedOdd pkg a sigma
  have hEO : -D = E - O := by
    exact multiplied_refutation_eq_even_sub_odd pkg a sigma hδ hidentity
  have hO : O = E + D := by
    linear_combination hEO
  have hE : IsSOS E := convertedEven_isSOS pkg a sigma hsigma hδ
  have hscaleE : IsSOS (C (1 - alpha) * E) :=
    IsSOS_mul (IsSOS_C_nonneg (1 - alpha) (sub_nonneg.mpr halpha)) hE
  have hscaleEmem : QuadraticModuleMem g (C (1 - alpha) * E) :=
    QuadraticModuleMem.of_isSOS g hscaleE
  change QuadraticModuleMem g
    ((C alpha * E + C beta * D) - O) at habsorb
  have hcombined := habsorb.add hscaleEmem
  have hnegScaled : QuadraticModuleMem g (-(C (1 - beta) * D)) := by
    convert hcombined using 1
    rw [hO]
    simp only [map_sub, map_one]
    ring
  let gamma : ℝ := 1 - beta
  have hgamma : 0 < gamma := sub_pos.mpr hbeta
  have hinvSOS : IsSOS (C gamma⁻¹ : MvPolynomial (Fin n) ℝ) :=
    IsSOS_C_nonneg gamma⁻¹ (inv_nonneg.mpr hgamma.le)
  have hscaled := QuadraticModuleMem.sos_mul hinvSOS hnegScaled
  have hscalar :
      (C gamma⁻¹ : MvPolynomial (Fin n) ℝ) * C gamma = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hgamma.ne', map_one]
  have hminusD : QuadraticModuleMem g (-D) := by
    have heq :
        (C gamma⁻¹ : MvPolynomial (Fin n) ℝ) *
            (-(C gamma * D)) = -D := by
      calc
        C gamma⁻¹ * (-(C gamma * D)) =
            -(C gamma⁻¹ * C gamma) * D := by ring
        _ = -D := by rw [hscalar]; ring
    rw [← heq]
    simpa [gamma] using hscaled
  have hDminusOne : QuadraticModuleMem g (D - 1) := by
    exact denominatorProduct_sub_one_mem pkg a ha hδ
  have hfinal := hminusD.add hDminusOne
  convert hfinal using 1
  ring
/-- Replace every error factor by its certified upper bound inside a
finite product. -/
theorem error_prod_le_bound_prod
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hδ : 0 < δ) (hB : 0 < B) (htheta : 0 ≤ theta)
    (K : Finset (Fin s)) :
    ModuleLE g
      (∏ i ∈ K, (pkg i).substE (a i))
      (∏ i ∈ K,
        (C theta * (pkg i).substP (a i) ^ 2 +
          C δ * (pkg i).substV (a i) ^ 2)) := by
  apply ModuleLE.prod K
  · intro i hi
    exact (pkg i).substE_isSOS (a i) hδ
  · intro i hi
    exact IsSOS_add
      (IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
      (IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _))
  · intro i hi
    exact (pkg i).substE_le_thetaP_sq_add_deltaV_sq
      hδ hB (ha i) (hBa i)

/-- The corresponding bounded expansion term. -/
def errorBoundTerm
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I K : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  sigma I *
      (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2) *
      (∏ i ∈ K,
        (C theta * (pkg i).substP (a i) ^ 2 +
          C δ * (pkg i).substV (a i) ^ 2)) *
    ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2

/-- Multiplication by all unchanged SOS factors lifts the product estimate
to each full error-expansion term. -/
theorem errorExpansionTerm_le_errorBoundTerm
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hδ : 0 < δ) (hB : 0 < B) (htheta : 0 ≤ theta)
    (I K : Finset (Fin s)) :
    ModuleLE g (errorExpansionTerm pkg a sigma I K)
      (errorBoundTerm pkg a sigma I K) := by
  classical
  have hP : IsSOS (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_sq _
  have hV : IsSOS (∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_sq _
  have hcontext : IsSOS
      (sigma I *
        (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2) *
        ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2) :=
    IsSOS_mul (IsSOS_mul (hsigma I) hP) hV
  have hprod := error_prod_le_bound_prod pkg a ha hBa
    hδ hB htheta K
  have hmul := ModuleLE.sos_mul_left hcontext hprod
  convert hmul using 1 <;>
    dsimp [errorExpansionTerm, errorBoundTerm] <;> ring

/-- The summand containing no error factors. -/
def zeroErrorTerm
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  errorExpansionTerm pkg a sigma I ∅

/-- The positive even-error remainder for one original subset. -/
def positiveEvenErrorSum
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ K ∈ (I.powerset.filter (fun K => Even K.card)).erase ∅,
    errorExpansionTerm pkg a sigma I K

theorem evenErrorSum_eq_zero_add_positive
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (I : Finset (Fin s)) :
    evenErrorSum pkg a sigma I =
      zeroErrorTerm pkg a sigma I +
        positiveEvenErrorSum pkg a sigma I := by
  classical
  have hempty :
      (∅ : Finset (Fin s)) ∈
        I.powerset.filter (fun K => Even K.card) := by simp
  have hsum := Finset.sum_erase_add
    (s := I.powerset.filter (fun K => Even K.card))
    (f := fun K => errorExpansionTerm pkg a sigma I K) hempty
  dsimp [evenErrorSum, zeroErrorTerm, positiveEvenErrorSum]
  rw [← hsum]
  ring

/-- Global zero-error and positive-even-error aggregates. -/
def convertedZero
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
    zeroErrorTerm pkg a sigma I

def convertedPositiveEven
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
    positiveEvenErrorSum pkg a sigma I

theorem convertedEven_eq_zero_add_positive
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ) :
    convertedEven pkg a sigma =
      convertedZero pkg a sigma + convertedPositiveEven pkg a sigma := by
  dsimp [convertedEven, convertedZero, convertedPositiveEven]
  simp_rw [evenErrorSum_eq_zero_add_positive]
  rw [Finset.sum_add_distrib]

theorem convertedPositiveEven_isSOS
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I)) (hδ : 0 < δ) :
    IsSOS (convertedPositiveEven pkg a sigma) := by
  classical
  apply IsSOS_sum_finset
  intro I hI
  apply IsSOS_sum_finset
  intro K hK
  exact errorExpansionTerm_isSOS pkg a sigma hsigma hδ I K

/-- The zero-error aggregate lies below the full even aggregate in module
order; their difference is exactly the positive even-error SOS remainder. -/
theorem convertedZero_le_convertedEven
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I)) (hδ : 0 < δ) :
    ModuleLE g (convertedZero pkg a sigma)
      (convertedEven pkg a sigma) := by
  have hrest : QuadraticModuleMem g
      (convertedPositiveEven pkg a sigma) :=
    QuadraticModuleMem.of_isSOS g
      (convertedPositiveEven_isSOS pkg a sigma hsigma hδ)
  change QuadraticModuleMem g
    (convertedEven pkg a sigma - convertedZero pkg a sigma)
  convert hrest using 1
  rw [convertedEven_eq_zero_add_positive]
  ring


/-- A completely scalar upper bound for one expanded error term. -/
def scalarBoundTerm
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (H Bprime : ℝ) (I K : Finset (Fin s)) :
    MvPolynomial (Fin n) ℝ :=
  C H *
      (∏ i ∈ I \ K,
        C Bprime * (pkg i).substV (a i) ^ 2) *
      (∏ i ∈ K,
        C (theta * Bprime + δ) *
          (pkg i).substV (a i) ^ 2) *
    ∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2

/-- After the interval comparisons and a scalar envelope for the original
SOS multiplier, each bounded error term is below a scalar multiple of the
common denominator. -/
theorem errorBoundTerm_le_scalarBoundTerm
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaBound : ∀ I, ModuleLE g (sigma I) (C H))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime)
    (hH : 0 ≤ H) (I K : Finset (Fin s)) :
    ModuleLE g (errorBoundTerm pkg a sigma I K)
      (scalarBoundTerm pkg a H Bprime I K) := by
  classical
  have hP (i : Fin s) :
      ModuleLE g ((pkg i).substP (a i) ^ 2)
        (C Bprime * (pkg i).substV (a i) ^ 2) :=
    (pkg i).substP_sq_le_B_mul_substV_sq hδ hB htheta1
      hBcondition (ha i) (hBa i)
  have herror (i : Fin s) :
      ModuleLE g
        (C theta * (pkg i).substP (a i) ^ 2 +
          C δ * (pkg i).substV (a i) ^ 2)
        (C (theta * Bprime + δ) *
          (pkg i).substV (a i) ^ 2) := by
    have hscaled := ModuleLE.sos_mul_left
      (IsSOS_C_nonneg theta htheta) (hP i)
    have hrefl := ModuleLE.refl g
      (C δ * (pkg i).substV (a i) ^ 2)
    have hadd := ModuleLE.add hscaled hrefl
    convert hadd using 1
    all_goals simp only [map_add, map_mul]
    all_goals ring
  have hPprod :
      ModuleLE g
        (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2)
        (∏ i ∈ I \ K,
          C Bprime * (pkg i).substV (a i) ^ 2) := by
    apply ModuleLE.prod (I \ K)
    · intro i hi
      exact IsSOS_sq _
    · intro i hi
      exact IsSOS_mul (IsSOS_C_nonneg Bprime hBprime) (IsSOS_sq _)
    · intro i hi
      exact hP i
  have hEprod :
      ModuleLE g
        (∏ i ∈ K,
          (C theta * (pkg i).substP (a i) ^ 2 +
            C δ * (pkg i).substV (a i) ^ 2))
        (∏ i ∈ K,
          C (theta * Bprime + δ) *
            (pkg i).substV (a i) ^ 2) := by
    apply ModuleLE.prod K
    · intro i hi
      exact IsSOS_add
        (IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
        (IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _))
    · intro i hi
      exact IsSOS_mul
        (IsSOS_C_nonneg (theta * Bprime + δ)
          (add_nonneg (mul_nonneg htheta hBprime) hδ.le))
        (IsSOS_sq _)
    · intro i hi
      exact herror i
  have hPupper : IsSOS
      (∏ i ∈ I \ K,
        C Bprime * (pkg i).substV (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_mul (IsSOS_C_nonneg Bprime hBprime) (IsSOS_sq _)
  have hEupper : IsSOS
      (∏ i ∈ K,
        C (theta * Bprime + δ) *
          (pkg i).substV (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_mul
      (IsSOS_C_nonneg (theta * Bprime + δ)
        (add_nonneg (mul_nonneg htheta hBprime) hδ.le))
      (IsSOS_sq _)
  have hPlower : IsSOS
      (∏ i ∈ I \ K, (pkg i).substP (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_sq _
  have hElower : IsSOS
      (∏ i ∈ K,
        (C theta * (pkg i).substP (a i) ^ 2 +
          C δ * (pkg i).substV (a i) ^ 2)) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_add
      (IsSOS_mul (IsSOS_C_nonneg theta htheta) (IsSOS_sq _))
      (IsSOS_mul (IsSOS_C_nonneg δ hδ.le) (IsSOS_sq _))
  have hVprod : IsSOS
      (∏ i ∈ Iᶜ, (pkg i).substV (a i) ^ 2) := by
    apply IsSOS_finset_prod
    intro i hi
    exact IsSOS_sq _
  have hfirst := ModuleLE.mul (hsigma I) hPupper
    (hsigmaBound I) hPprod
  have hsecond := ModuleLE.mul
    (IsSOS_mul (hsigma I) hPlower) hEupper hfirst hEprod
  have hthird := ModuleLE.mul
    (IsSOS_mul (IsSOS_mul (hsigma I) hPlower) hElower)
    hVprod hsecond (ModuleLE.refl g _)
  convert hthird using 1

/-- The numerical coefficient multiplying the common denominator in the
scalar bound for one pair `K ⊆ I`. -/
def scalarErrorCoefficient
    (H Bprime theta δ : ℝ)
    (I K : Finset (Fin s)) : ℝ :=
  H * Bprime ^ (I \ K).card *
    (theta * Bprime + δ) ^ K.card

theorem scalarBoundTerm_eq_coefficient_mul_denominator
    {s : ℕ} {δ B theta : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (H Bprime : ℝ) (I K : Finset (Fin s))
    (hKI : K ⊆ I) :
    scalarBoundTerm pkg a H Bprime I K =
      C (scalarErrorCoefficient H Bprime theta δ I K) *
        denominatorProduct pkg a := by
  classical
  let Vsq : Fin s → MvPolynomial (Fin n) ℝ :=
    fun i => (pkg i).substV (a i) ^ 2
  have hprod (S : Finset (Fin s)) (c : ℝ) :
      (∏ i ∈ S, C c * Vsq i) =
        C (c ^ S.card) * ∏ i ∈ S, Vsq i := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,
      map_pow]
  have hsplit :
      (∏ i ∈ I \ K, Vsq i) * (∏ i ∈ K, Vsq i) =
        ∏ i ∈ I, Vsq i :=
    Finset.prod_sdiff hKI
  have hden :
      (∏ i ∈ I, Vsq i) * (∏ i ∈ Iᶜ, Vsq i) =
        denominatorProduct pkg a := by
    exact (denominatorProduct_eq_subset_mul_compl pkg a I).symm
  dsimp [scalarBoundTerm]
  change C H *
      (∏ i ∈ I \ K, C Bprime * Vsq i) *
      (∏ i ∈ K, C (theta * Bprime + δ) * Vsq i) *
        ∏ i ∈ Iᶜ, Vsq i =
    C (scalarErrorCoefficient H Bprime theta δ I K) *
      denominatorProduct pkg a
  rw [hprod, hprod, ← hden, ← hsplit]
  dsimp [scalarErrorCoefficient]
  simp only [map_mul, map_pow]
  ring

/-- Total scalar error coefficient over all odd error subsets. -/
def oddAbsorptionCoefficient
    (s : ℕ) (H Bprime theta δ : ℝ) : ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
    ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
      scalarErrorCoefficient H Bprime theta δ I K

/-- All odd error terms are bounded by a single scalar multiple of the common
denominator. -/
theorem convertedOdd_le_oddAbsorptionCoefficient
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaBound : ∀ I, ModuleLE g (sigma I) (C H))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime)
    (hH : 0 ≤ H) :
    ModuleLE g (convertedOdd pkg a sigma)
      (C (oddAbsorptionCoefficient s H Bprime theta δ) *
        denominatorProduct pkg a) := by
  classical
  have houter := ModuleLE.sum
    (s := (Finset.univ : Finset (Fin s)).powerset)
    (p := fun I => oddErrorSum pkg a sigma I)
    (q := fun I =>
      ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
        C (scalarErrorCoefficient H Bprime theta δ I K) *
          denominatorProduct pkg a)
    (fun I hI => by
      apply ModuleLE.sum
      intro K hK
      have hKI : K ⊆ I :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hK).1
      have h₁ := errorExpansionTerm_le_errorBoundTerm
        pkg a sigma hsigma ha hBa hδ hB htheta I K
      have h₂ := errorBoundTerm_le_scalarBoundTerm
        pkg a sigma hsigma hsigmaBound ha hBa hδ hB htheta
        htheta1 hBprime hBcondition hH I K
      have h₃ := h₁.trans h₂
      rw [scalarBoundTerm_eq_coefficient_mul_denominator
        pkg a H Bprime I K hKI] at h₃
      exact h₃)
  convert houter using 1
  simp only [oddAbsorptionCoefficient, map_sum,
    Finset.sum_mul]

/-- The scalar absorption inequality closes the converted refutation. -/
theorem refutation_of_oddAbsorptionCoefficient
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta H Bprime : ℝ}
    (pkg : Fin s → Package δ B theta)
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaBound : ∀ I, ModuleLE g (sigma I) (C H))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hBprime : 0 ≤ Bprime)
    (hBcondition : B + δ ≤ (1 - theta) * Bprime)
    (hH : 0 ≤ H)
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i)
    (hsmall :
      oddAbsorptionCoefficient s H Bprime theta δ < 1) :
    QuadraticModuleMem g (-1) := by
  apply refutation_of_absorption pkg a sigma hsigma ha hδ hidentity
    (alpha := 0)
    (beta := oddAbsorptionCoefficient s H Bprime theta δ)
    (by norm_num) hsmall
  have hodd := convertedOdd_le_oddAbsorptionCoefficient
    pkg a sigma hsigma hsigmaBound ha hBa hδ hB htheta htheta1
    hBprime hBcondition hH
  simpa using hodd

/-- Number of odd pairs `K ⊆ I ⊆ Fin s` occurring in the expansion. -/
def oddPairCount (s : ℕ) : ℕ :=
  ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
    (I.powerset.filter (fun K => ¬ Even K.card)).card

/-- A positive common value of `theta` and `delta` that makes the total
scalar error strictly smaller than one. -/
def absorptionScale (s : ℕ) (H Bprime : ℝ) : ℝ :=
  (2 * ((oddPairCount s : ℝ) + 1) * (H + 1) *
    (Bprime + 1) ^ (s + 1))⁻¹

theorem absorptionScale_pos
    {s : ℕ} {H Bprime : ℝ} (hH : 0 ≤ H)
    (hBprime : 0 ≤ Bprime) :
    0 < absorptionScale s H Bprime := by
  dsimp [absorptionScale]
  positivity

/-- The explicit absorption scale makes the finite odd-error sum strictly
smaller than one. -/
theorem oddAbsorptionCoefficient_scale_lt_one
    {s : ℕ} {H Bprime : ℝ} (hH : 0 ≤ H)
    (hBprime : 0 ≤ Bprime) :
    oddAbsorptionCoefficient s H Bprime
      (absorptionScale s H Bprime)
      (absorptionScale s H Bprime) < 1 := by
  classical
  let count : ℝ := oddPairCount s
  let M : ℝ := Bprime + 1
  let eta : ℝ := absorptionScale s H Bprime
  have hcount : 0 ≤ count := by positivity
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have heta : 0 < eta :=
    absorptionScale_pos hH hBprime
  have hdenpos :
      0 < 2 * (count + 1) * (H + 1) * M ^ s := by
    positivity
  have hetaM :
      eta * M =
        1 / (2 * (count + 1) * (H + 1) * M ^ s) := by
    dsimp [eta, absorptionScale, count, M]
    rw [inv_eq_one_div]
    field_simp
    ring
  have hdenone :
      1 ≤ 2 * (count + 1) * (H + 1) * M ^ s := by
    have hc1 : 1 ≤ count + 1 := by linarith
    have hH1 : 1 ≤ H + 1 := by linarith
    have hMs : 1 ≤ M ^ s := one_le_pow₀ hM
    calc
      1 ≤ (2 : ℝ) := by norm_num
      _ ≤ 2 * (count + 1) := by nlinarith
      _ = (2 * (count + 1)) * 1 := by ring
      _ ≤ (2 * (count + 1)) * (H + 1) :=
        mul_le_mul_of_nonneg_left hH1 (by positivity)
      _ = (2 * (count + 1) * (H + 1)) * 1 := by ring
      _ ≤ (2 * (count + 1) * (H + 1)) * M ^ s :=
        mul_le_mul_of_nonneg_left hMs (by positivity)
  have hetaM0 : 0 ≤ eta * M := mul_nonneg heta.le (zero_le_one.trans hM)
  have hetaM1 : eta * M ≤ 1 := by
    rw [hetaM]
    exact (div_le_one hdenpos).mpr hdenone
  have hterm :
      ∀ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        ∀ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
          scalarErrorCoefficient H Bprime eta eta I K ≤
            H * M ^ s * (eta * M) := by
    intro I hI K hK
    have hcard : (I \ K).card ≤ s := by
      have hsub :
          I \ K ⊆ (Finset.univ : Finset (Fin s)) :=
        Finset.subset_univ _
      simpa using Finset.card_le_card hsub
    have hpowB :
        Bprime ^ (I \ K).card ≤ M ^ s := by
      calc
        Bprime ^ (I \ K).card ≤ M ^ (I \ K).card :=
          pow_le_pow_left₀ hBprime (by dsimp [M]; linarith) _
        _ ≤ M ^ s := pow_le_pow_right₀ hM hcard
    have hodd : Odd K.card :=
      Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hK).2
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hodd.pos.ne'
    have hpowQ : (eta * M) ^ K.card ≤ eta * M := by
      rw [hj, pow_succ']
      exact (mul_le_mul_of_nonneg_left
        (pow_le_one₀ hetaM0 hetaM1) hetaM0).trans_eq (mul_one _)
    have hq :
        eta * Bprime + eta = eta * M := by
      dsimp [M]
      ring
    dsimp [scalarErrorCoefficient]
    rw [hq]
    gcongr
  have hsum :
      oddAbsorptionCoefficient s H Bprime eta eta ≤
        count * (H * M ^ s * (eta * M)) := by
    dsimp [oddAbsorptionCoefficient]
    calc
      (∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        ∑ K ∈ I.powerset.filter (fun K => ¬ Even K.card),
          scalarErrorCoefficient H Bprime eta eta I K)
          ≤ ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
              ∑ _K ∈ I.powerset.filter (fun K => ¬ Even K.card),
                H * M ^ s * (eta * M) := by
            apply Finset.sum_le_sum
            intro I hI
            apply Finset.sum_le_sum
            intro K hK
            exact hterm I hI K hK
      _ = count * (H * M ^ s * (eta * M)) := by
            dsimp [count, oddPairCount]
            simp only [Finset.sum_const, nsmul_eq_mul]
            push_cast
            rw [Finset.sum_mul]
  have hvalue :
      count * (H * M ^ s * (eta * M)) =
        count * H / (2 * (count + 1) * (H + 1)) := by
    rw [hetaM]
    field_simp
  have hratio :
      count * H / (2 * (count + 1) * (H + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [mul_nonneg hcount hH]
  exact hsum.trans_lt (hvalue.trans_lt hratio)

theorem absorptionScale_le_half
    {s : ℕ} {H Bprime : ℝ} (hH : 0 ≤ H)
    (hBprime : 0 ≤ Bprime) :
    absorptionScale s H Bprime ≤ 1 / 2 := by
  let count : ℝ := oddPairCount s
  let M : ℝ := Bprime + 1
  have hcount : 0 ≤ count := by positivity
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hc1 : 1 ≤ count + 1 := by linarith
  have hH1 : 1 ≤ H + 1 := by linarith
  have hMpow : 1 ≤ M ^ (s + 1) := one_le_pow₀ hM
  have hden :
      2 ≤ 2 * (count + 1) * (H + 1) * M ^ (s + 1) := by
    calc
      (2 : ℝ) = 2 * 1 := by ring
      _ ≤ 2 * (count + 1) :=
        mul_le_mul_of_nonneg_left hc1 (by norm_num)
      _ = (2 * (count + 1)) * 1 := by ring
      _ ≤ (2 * (count + 1)) * (H + 1) :=
        mul_le_mul_of_nonneg_left hH1 (by positivity)
      _ = (2 * (count + 1) * (H + 1)) * 1 := by ring
      _ ≤ (2 * (count + 1) * (H + 1)) * M ^ (s + 1) :=
        mul_le_mul_of_nonneg_left hMpow (by positivity)
  dsimp [absorptionScale, count, M]
  apply (inv_le_iff_one_le_mul₀'
    (by positivity :
      0 < 2 * (count + 1) * (H + 1) * M ^ (s + 1))).2
  nlinarith

/-- A bounded preordering refutation over module-bounded artificial
generators converts to a refutation in the original quadratic module.  All
small parameters and rational-square-root packages are chosen explicitly. -/
theorem bounded_preordering_refutation_to_module
    {s : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    (a : Fin s → MvPolynomial (Fin n) ℝ)
    (sigma : Finset (Fin s) → MvPolynomial (Fin n) ℝ)
    (B H : ℝ)
    (hB : 0 < B) (hH : 0 ≤ H)
    (hsigma : ∀ I, IsSOS (sigma I))
    (hsigmaBound : ∀ I, ModuleLE g (sigma I) (C H))
    (ha : ∀ i, QuadraticModuleMem g (a i))
    (hBa : ∀ i, QuadraticModuleMem g (C B - a i))
    (hidentity : (-1 : MvPolynomial (Fin n) ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Fin s)).powerset,
        sigma I * ∏ i ∈ I, a i) :
    QuadraticModuleMem g (-1) := by
  let Bprime : ℝ := 2 * (B + 1)
  have hBprime : 0 ≤ Bprime := by
    dsimp [Bprime]
    positivity
  let eta : ℝ := absorptionScale s H Bprime
  have heta : 0 < eta :=
    absorptionScale_pos hH hBprime
  have hetahalf : eta ≤ 1 / 2 :=
    absorptionScale_le_half hH hBprime
  have hetaone : eta ≤ 1 := hetahalf.trans (by norm_num)
  have htheta1 : eta < 1 := lt_of_le_of_lt hetahalf (by norm_num)
  have hcondition : B + eta ≤ (1 - eta) * Bprime := by
    have hfactor : 1 ≤ 2 * (1 - eta) := by linarith
    have hB1 : 0 ≤ B + 1 := by linarith
    calc
      B + eta ≤ B + 1 := by linarith
      _ = 1 * (B + 1) := by ring
      _ ≤ (2 * (1 - eta)) * (B + 1) :=
        mul_le_mul_of_nonneg_right hfactor hB1
      _ = (1 - eta) * Bprime := by dsimp [Bprime]; ring
  obtain ⟨pkg0⟩ :=
    RationalSquareRoot.package_nonempty heta hB.le heta
  let pkg : Fin s → Package eta B eta := fun _ => pkg0
  exact refutation_of_oddAbsorptionCoefficient
    pkg a sigma hsigma hsigmaBound ha hBa heta hB heta.le
    htheta1 hBprime hcondition hH hidentity
    (oddAbsorptionCoefficient_scale_lt_one hH hBprime)

/-- A uniform scalar coefficient envelope for a finite family. -/
def finiteFamilyEnvelope
    {ι : Type*} (R : ℝ) (S : Finset ι)
    (q : ι → MvPolynomial (Fin n) ℝ) : ℝ :=
  1 + ∑ i ∈ S, weightedCoeffEnvelope R (q i)

theorem one_le_finiteFamilyEnvelope
    {ι : Type*} {R : ℝ} (hR : 0 ≤ R)
    (S : Finset ι) (q : ι → MvPolynomial (Fin n) ℝ) :
    1 ≤ finiteFamilyEnvelope R S q := by
  dsimp [finiteFamilyEnvelope]
  exact le_add_of_nonneg_right <|
    Finset.sum_nonneg fun i _ => weightedCoeffEnvelope_nonneg hR (q i)

/-- Every member of a finite polynomial family lies below the common
coefficient envelope in the Archimedean module order. -/
theorem family_member_le_finiteFamilyEnvelope
    {ι : Type*} [DecidableEq ι]
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {R : ℝ} (hR : 0 ≤ R)
    (hcoord : ∀ i : Fin n,
      QuadraticModuleMem g (C R - X i ^ 2))
    (S : Finset ι) (q : ι → MvPolynomial (Fin n) ℝ)
    {i : ι} (hi : i ∈ S) :
    ModuleLE g (q i) (C (finiteFamilyEnvelope R S q)) := by
  let e : ι → ℝ := fun j => weightedCoeffEnvelope R (q j)
  have hbase : ModuleLE g (q i) (C (e i)) := by
    change QuadraticModuleMem g (C (e i) - q i)
    exact weightedCoeffEnvelope_minus_mem hR hcoord (q i)
  have hei :
      e i ≤ finiteFamilyEnvelope R S q := by
    have hsingle :
        e i ≤ ∑ j ∈ S, e j :=
      Finset.single_le_sum
        (fun j _ => weightedCoeffEnvelope_nonneg hR (q j)) hi
    dsimp [finiteFamilyEnvelope]
    linarith
  exact hbase.trans (ModuleLE.constant hei)

/-- In an Archimedean quadratic module, every preordering refutation of
minus one can be converted to an ordinary quadratic-module refutation. -/
theorem archimedean_preordering_refutation_to_module
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (harch : IsArchimedean g)
    (hrefute : KrivineStengle.PreorderingMem g
      (-1 : MvPolynomial (Fin n) ℝ)) :
    QuadraticModuleMem g (-1) := by
  classical
  obtain ⟨r, sigma, hsigma, hdegree, hidentity⟩ := hrefute
  obtain ⟨R, hR, hcoord⟩ :=
    harch.exists_coordinate_square_bound
  let generatorSet : Finset (Fin m) := Finset.univ
  let sigmaSet : Finset (Finset (Fin m)) := Finset.univ
  let B : ℝ := finiteFamilyEnvelope R generatorSet g
  let H : ℝ := finiteFamilyEnvelope R sigmaSet sigma
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hB1 : 1 ≤ B :=
    one_le_finiteFamilyEnvelope hR0 generatorSet g
  have hH1 : 1 ≤ H :=
    one_le_finiteFamilyEnvelope hR0 sigmaSet sigma
  have ha : ∀ i, QuadraticModuleMem g (g i) := by
    intro i
    exact ⟨(g i).totalDegree, genQuadraticModule_generator g i⟩
  have hBa : ∀ i, QuadraticModuleMem g (C B - g i) := by
    intro i
    have hle := family_member_le_finiteFamilyEnvelope
      hR0 hcoord generatorSet g (i := i) (by simp [generatorSet])
    exact hle
  have hsigmaBound : ∀ I, ModuleLE g (sigma I) (C H) := by
    intro I
    exact family_member_le_finiteFamilyEnvelope
      hR0 hcoord sigmaSet sigma (i := I) (by simp [sigmaSet])
  exact bounded_preordering_refutation_to_module
    g sigma B H (lt_of_lt_of_le zero_lt_one hB1) (zero_le_one.trans hH1)
    hsigma hsigmaBound ha hBa hidentity

end GeneralArchimedean
end OptimalConvergenceRates

end
