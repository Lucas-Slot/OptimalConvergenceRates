/-
  OptimalConvergenceRates/GeneralArchimedean/Certificates.lean

  Explicit quantitative wrappers around the repository's existing cone definitions.
-/
import OptimalConvergenceRates.GeneralArchimedean.Defs
import OptimalConvergenceRates.BasicNotions.CoefficientNorm
import OptimalConvergenceRates.KrivineStengle.TruncatedPreordering
import OptimalConvergenceRates.KrivineStengle.TruncatedRefutation
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}

/-- An explicit witness for membership in a truncated preordering. -/
structure PreorderingCertificate (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ) where
  sigma : Finset (Fin m) → MvPolynomial (Fin n) ℝ
  isSOS : ∀ I, IsSOS (sigma I)
  degree_le : ∀ I, (sigma I * ∏ i ∈ I, g i).totalDegree ≤ r
  identity : p = ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
    sigma I * ∏ i ∈ I, g i

namespace PreorderingCertificate

/-- Forget the named certificate and retain ordinary truncated membership. -/
theorem toMem {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : PreorderingCertificate g p r) :
    p ∈ GenPreordering g r :=
  ⟨c.sigma, c.isSOS, c.degree_le, c.identity⟩

/-- Total coefficient size of all SOS multipliers in a preordering certificate. -/
def coeffSize {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : PreorderingCertificate g p r) : ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset, coeffL1Norm (c.sigma I)

theorem coeffSize_nonneg {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : PreorderingCertificate g p r) :
    0 ≤ c.coeffSize :=
  Finset.sum_nonneg fun _ _ ↦ coeffL1Norm_nonneg _

theorem coeff_le_coeffSize {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : PreorderingCertificate g p r) (I : Finset (Fin m)) :
    coeffL1Norm (c.sigma I) ≤ c.coeffSize := by
  classical
  exact Finset.single_le_sum
    (f := fun J ↦ coeffL1Norm (c.sigma J))
    (fun J _ ↦ coeffL1Norm_nonneg (c.sigma J)) (by simp)


/-- Raising the truncation order does not alter an explicit certificate or
its coefficient size. -/
def mono {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : PreorderingCertificate g p r) (hrs : r ≤ s) :
    PreorderingCertificate g p s where
  sigma := c.sigma
  isSOS := c.isSOS
  degree_le := fun I => (c.degree_le I).trans hrs
  identity := c.identity

@[simp]
theorem coeffSize_mono {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : PreorderingCertificate g p r) (hrs : r ≤ s) :
    (c.mono hrs).coeffSize = c.coeffSize :=
  rfl

/-- Addition of named certificates, retaining the common maximum order. -/
def add {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : PreorderingCertificate g p r)
    (d : PreorderingCertificate g q s) :
    PreorderingCertificate g (p + q) (max r s) where
  sigma := fun I => c.sigma I + d.sigma I
  isSOS := fun I => IsSOS_add (c.isSOS I) (d.isSOS I)
  degree_le := fun I => by
    calc
      ((c.sigma I + d.sigma I) * ∏ i ∈ I, g i).totalDegree =
          (c.sigma I * ∏ i ∈ I, g i +
            d.sigma I * ∏ i ∈ I, g i).totalDegree := by ring_nf
      _ ≤ max (c.sigma I * ∏ i ∈ I, g i).totalDegree
          (d.sigma I * ∏ i ∈ I, g i).totalDegree :=
        MvPolynomial.totalDegree_add _ _
      _ ≤ max r s := max_le_max (c.degree_le I) (d.degree_le I)
  identity := calc
    p + q =
        (∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          c.sigma I * ∏ i ∈ I, g i) + q :=
      congrArg (fun z => z + q) c.identity
    _ = (∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          c.sigma I * ∏ i ∈ I, g i) +
        ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          d.sigma I * ∏ i ∈ I, g i :=
      congrArg (fun z => (∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
        c.sigma I * ∏ i ∈ I, g i) + z) d.identity
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro I _
      ring

theorem coeffSize_add_le {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : PreorderingCertificate g p r)
    (d : PreorderingCertificate g q s) :
    (c.add d).coeffSize ≤ c.coeffSize + d.coeffSize := by
  classical
  unfold coeffSize add
  calc
    ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
        coeffL1Norm (c.sigma I + d.sigma I) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
        (coeffL1Norm (c.sigma I) + coeffL1Norm (d.sigma I)) := by
          apply Finset.sum_le_sum
          intro I _
          exact coeffL1Norm_add_le _ _
    _ = c.coeffSize + d.coeffSize := by
      rw [Finset.sum_add_distrib]
      rfl

/-- Nonnegative scalar multiplication of an explicit preordering
certificate. -/
def scaleNonneg {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : PreorderingCertificate g p r) (a : ℝ) (ha : 0 ≤ a) :
    PreorderingCertificate g (C a * p) r where
  sigma := fun I => C a * c.sigma I
  isSOS := fun I => IsSOS_mul (IsSOS_C_nonneg a ha) (c.isSOS I)
  degree_le := fun I => by
    calc
      ((C a * c.sigma I) * ∏ i ∈ I, g i).totalDegree =
          (C a * (c.sigma I * ∏ i ∈ I, g i)).totalDegree := by ring_nf
      _ ≤ (C a : MvPolynomial (Fin n) ℝ).totalDegree +
          (c.sigma I * ∏ i ∈ I, g i).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ r := by simpa using c.degree_le I
  identity := calc
    C a * p = C a *
        ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          c.sigma I * ∏ i ∈ I, g i :=
      congrArg (fun z => C a * z) c.identity
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      ring

theorem coeffSize_scaleNonneg_le
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : PreorderingCertificate g p r) (a : ℝ) (ha : 0 ≤ a) :
    (c.scaleNonneg a ha).coeffSize ≤ a * c.coeffSize := by
  classical
  unfold coeffSize scaleNonneg
  calc
    ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
        coeffL1Norm (C a * c.sigma I) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
        a * coeffL1Norm (c.sigma I) := by
          apply Finset.sum_le_sum
          intro I _
          simpa [abs_of_nonneg ha] using
            coeffL1Norm_C_mul_le a (c.sigma I)
    _ = a * c.coeffSize := by
      change (∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
        a * coeffL1Norm (c.sigma I)) =
        a * ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          coeffL1Norm (c.sigma I)
      rw [Finset.mul_sum]


/-- Explicit degree-zero certificate for a nonnegative constant. -/
def constantNonneg
    (g : Fin m → MvPolynomial (Fin n) ℝ) (a : ℝ) (ha : 0 ≤ a) :
    PreorderingCertificate g (C a) 0 where
  sigma := Function.update 0 ∅ (C a)
  isSOS := by
    intro I
    by_cases hI : I = ∅
    · subst I
      simpa using IsSOS_C_nonneg a ha
    · simp [Function.update_of_ne hI, IsSOS_zero]
  degree_le := by
    intro I
    by_cases hI : I = ∅
    · subst I
      simp [MvPolynomial.totalDegree_C]
    · simp [Function.update_of_ne hI]
  identity := by
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro I _ hI
      simp [Function.update_of_ne hI]
    · simp

theorem coeffSize_constantNonneg_le
    (g : Fin m → MvPolynomial (Fin n) ℝ) (a : ℝ) (ha : 0 ≤ a) :
    (constantNonneg g a ha).coeffSize ≤ a := by
  classical
  unfold coeffSize constantNonneg
  rw [Finset.sum_eq_single ∅]
  · simpa [abs_of_nonneg ha] using coeffL1Norm_C_le (n := n) a
  · intro I _ hI
    simp [Function.update_of_ne hI]
  · simp

/-- Explicit certificate for one of the preordering generators. -/
def generator (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    PreorderingCertificate g (g i) (g i).totalDegree where
  sigma := Function.update 0 {i} 1
  isSOS := by
    intro I
    by_cases hI : I = {i}
    · subst I
      simpa using IsSOS_sq (1 : MvPolynomial (Fin n) ℝ)
    · simp [Function.update_of_ne hI, IsSOS_zero]
  degree_le := by
    intro I
    by_cases hI : I = {i}
    · subst I
      simp
    · simp [Function.update_of_ne hI]
  identity := by
    rw [Finset.sum_eq_single {i}]
    · simp
    · intro I _ hI
      simp [Function.update_of_ne hI]
    · simp

theorem coeffSize_generator_le
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    (generator g i).coeffSize ≤ 1 := by
  classical
  unfold coeffSize generator
  rw [Finset.sum_eq_single {i}]
  · simpa using coeffL1Norm_C_le (n := n) (1 : ℝ)
  · intro I _ hI
    simp [Function.update_of_ne hI]
  · simp

/-- Lift a named certificate after adjoining one generator. -/
def liftAppendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : PreorderingCertificate g p r)
    (h : MvPolynomial (Fin n) ℝ) :
    PreorderingCertificate (KrivineStengle.appendGenerator g h) p r where
  sigma := KrivineStengle.liftPreorderingCoefficient c.sigma
  isSOS := KrivineStengle.liftPreorderingCoefficient_isSOS c.sigma c.isSOS
  degree_le := KrivineStengle.liftPreorderingCoefficient_totalDegree_le
    g h c.sigma c.degree_le
  identity := calc
    p = ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          c.sigma I * ∏ i ∈ I, g i := c.identity
    _ = ∑ J ∈ (Finset.univ : Finset (Fin (m + 1))).powerset,
          KrivineStengle.liftPreorderingCoefficient c.sigma J *
            ∏ j ∈ J, KrivineStengle.appendGenerator g h j := by
      simpa [KrivineStengle.generatorProduct] using
        (KrivineStengle.liftPreorderingCoefficient_sum g h c.sigma).symm

theorem coeffL1Norm_liftPreorderingCoefficient_le
    (sigma : Finset (Fin m) → MvPolynomial (Fin n) ℝ)
    (J : Finset (Fin (m + 1))) :
    coeffL1Norm (KrivineStengle.liftPreorderingCoefficient sigma J) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
        coeffL1Norm (sigma I) := by
  classical
  calc
    coeffL1Norm (KrivineStengle.liftPreorderingCoefficient sigma J) ≤
        ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          coeffL1Norm
            (if I.map Fin.castSuccEmb = J then sigma I else 0) := by
      simpa [KrivineStengle.liftPreorderingCoefficient] using
        coeffL1Norm_sum_le
          ((Finset.univ : Finset (Fin m)).powerset)
          (fun I => if I.map Fin.castSuccEmb = J then sigma I else 0)
    _ ≤ ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          coeffL1Norm (sigma I) := by
      apply Finset.sum_le_sum
      intro I hI
      by_cases hIJ : I.map Fin.castSuccEmb = J
      · simp [hIJ]
      · simp [hIJ, coeffL1Norm_nonneg]

theorem coeffSize_liftAppendGenerator_le
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p h : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : PreorderingCertificate g p r) :
    (c.liftAppendGenerator h).coeffSize ≤
      (((Finset.univ : Finset (Fin (m + 1))).powerset.card : ℕ) : ℝ) *
        c.coeffSize := by
  classical
  unfold coeffSize liftAppendGenerator
  calc
    (∑ J ∈ (Finset.univ : Finset (Fin (m + 1))).powerset,
      coeffL1Norm
        (KrivineStengle.liftPreorderingCoefficient c.sigma J)) ≤
        ∑ J ∈ (Finset.univ : Finset (Fin (m + 1))).powerset,
          c.coeffSize := by
      apply Finset.sum_le_sum
      intro J hJ
      exact coeffL1Norm_liftPreorderingCoefficient_le c.sigma J
    _ = (((Finset.univ : Finset (Fin (m + 1))).powerset.card : ℕ) : ℝ) *
        c.coeffSize := by
      simp only [Finset.sum_const, nsmul_eq_mul]
/-- Multiplication of named preordering certificates, with additive
truncation order. -/
def mul {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : PreorderingCertificate g p r)
    (d : PreorderingCertificate g q s) :
    PreorderingCertificate g (p * q) (r + s) where
  sigma := KrivineStengle.productCoefficient g c.sigma d.sigma
  isSOS := KrivineStengle.productCoefficient_isSOS
    g c.sigma d.sigma c.isSOS d.isSOS
  degree_le := KrivineStengle.productCoefficient_totalDegree_le
    c.sigma d.sigma c.degree_le d.degree_le
  identity := calc
    p * q =
        (∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          c.sigma I * ∏ i ∈ I, g i) * q :=
      congrArg (fun z => z * q) c.identity
    _ = (∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          c.sigma I * ∏ i ∈ I, g i) *
        ∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          d.sigma I * ∏ i ∈ I, g i :=
      congrArg
        (fun z => (∑ I ∈ (Finset.univ : Finset (Fin m)).powerset,
          c.sigma I * ∏ i ∈ I, g i) * z) d.identity
    _ = _ := by
      simpa [KrivineStengle.generatorProduct] using
        KrivineStengle.productCoefficient_sum g c.sigma d.sigma

/-- The fixed coefficient-growth factor contributed by squarefree
products of the generators when two preordering certificates are
multiplied. -/
def mulFactor (g : Fin m → MvPolynomial (Fin n) ℝ) : ℝ :=
  let subsets := (Finset.univ : Finset (Fin m)).powerset
  let pairs := subsets.product subsets
  ∑ K ∈ subsets,
    ∑ IJ ∈ pairs.filter
        (fun IJ => KrivineStengle.subsetParity IJ.1 IJ.2 = K),
      coeffL1Norm ((∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2)

theorem mulFactor_nonneg (g : Fin m → MvPolynomial (Fin n) ℝ) :
    0 ≤ mulFactor g := by
  classical
  simp only [mulFactor]
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => coeffL1Norm_nonneg _

/-- Multiplication grows the total coefficient size by at most the fixed
generator multiplication factor. -/
theorem coeffSize_mul_le {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : PreorderingCertificate g p r)
    (d : PreorderingCertificate g q s) :
    (c.mul d).coeffSize ≤ c.coeffSize * d.coeffSize * mulFactor g := by
  classical
  let subsets := (Finset.univ : Finset (Fin m)).powerset
  let pairs := subsets.product subsets
  change
    (∑ K ∈ subsets,
      coeffL1Norm (KrivineStengle.productCoefficient g c.sigma d.sigma K)) ≤
      c.coeffSize * d.coeffSize *
        ∑ K ∈ subsets,
          ∑ IJ ∈ pairs.filter
              (fun IJ => KrivineStengle.subsetParity IJ.1 IJ.2 = K),
            coeffL1Norm ((∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2)
  calc
    (∑ K ∈ subsets,
      coeffL1Norm (KrivineStengle.productCoefficient g c.sigma d.sigma K)) ≤
        ∑ K ∈ subsets,
          ∑ IJ ∈ pairs.filter
              (fun IJ => KrivineStengle.subsetParity IJ.1 IJ.2 = K),
            coeffL1Norm
              ((c.sigma IJ.1 * d.sigma IJ.2) *
                (∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2) := by
      apply Finset.sum_le_sum
      intro K hK
      simpa [KrivineStengle.productCoefficient, subsets, pairs] using
        coeffL1Norm_sum_le
          (pairs.filter
            (fun IJ => KrivineStengle.subsetParity IJ.1 IJ.2 = K))
          (fun IJ =>
            (c.sigma IJ.1 * d.sigma IJ.2) *
              (∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2)
    _ ≤ ∑ K ∈ subsets,
          ∑ IJ ∈ pairs.filter
              (fun IJ => KrivineStengle.subsetParity IJ.1 IJ.2 = K),
            (c.coeffSize * d.coeffSize) *
              coeffL1Norm ((∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2) := by
      apply Finset.sum_le_sum
      intro K hK
      apply Finset.sum_le_sum
      intro IJ hIJ
      have hcoeff :
          coeffL1Norm (c.sigma IJ.1) * coeffL1Norm (d.sigma IJ.2) ≤
            c.coeffSize * d.coeffSize :=
        mul_le_mul (c.coeff_le_coeffSize IJ.1)
          (d.coeff_le_coeffSize IJ.2)
          (coeffL1Norm_nonneg _) c.coeffSize_nonneg
      calc
        coeffL1Norm
            ((c.sigma IJ.1 * d.sigma IJ.2) *
              (∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2) ≤
            coeffL1Norm (c.sigma IJ.1 * d.sigma IJ.2) *
              coeffL1Norm ((∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2) :=
          coeffL1Norm_mul_le _ _
        _ ≤ (coeffL1Norm (c.sigma IJ.1) *
              coeffL1Norm (d.sigma IJ.2)) *
              coeffL1Norm ((∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2) :=
          mul_le_mul_of_nonneg_right
            (coeffL1Norm_mul_le _ _) (coeffL1Norm_nonneg _)
        _ ≤ (c.coeffSize * d.coeffSize) *
              coeffL1Norm ((∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2) :=
          mul_le_mul_of_nonneg_right hcoeff (coeffL1Norm_nonneg _)
    _ = c.coeffSize * d.coeffSize *
        ∑ K ∈ subsets,
          ∑ IJ ∈ pairs.filter
              (fun IJ => KrivineStengle.subsetParity IJ.1 IJ.2 = K),
            coeffL1Norm ((∏ i ∈ IJ.1 ∩ IJ.2, g i) ^ 2) := by
      simp only [Finset.mul_sum]
end PreorderingCertificate

/-- A preordering certificate together with a numerical coefficient-size bound. -/
structure BoundedPreorderingCertificate
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ) (H : ℝ) where
  certificate : PreorderingCertificate g p r
  size_le : certificate.coeffSize ≤ H

namespace BoundedPreorderingCertificate

theorem toMem {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedPreorderingCertificate g p r H) :
    p ∈ GenPreordering g r :=
  c.certificate.toMem

theorem coeff_le {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedPreorderingCertificate g p r H) (I : Finset (Fin m)) :
    coeffL1Norm (c.certificate.sigma I) ≤ H :=
  (c.certificate.coeff_le_coeffSize I).trans c.size_le

theorem bound_nonneg {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedPreorderingCertificate g p r H) :
    0 ≤ H :=
  c.certificate.coeffSize_nonneg.trans c.size_le


/-- A nonnegative constant with its sharp scalar coefficient bound. -/
def constantNonneg
    (g : Fin m → MvPolynomial (Fin n) ℝ) (a : ℝ) (ha : 0 ≤ a) :
    BoundedPreorderingCertificate g (C a) 0 a where
  certificate := PreorderingCertificate.constantNonneg g a ha
  size_le := PreorderingCertificate.coeffSize_constantNonneg_le g a ha

/-- A generator with coefficient-size bound one. -/
def generator (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    BoundedPreorderingCertificate g (g i) (g i).totalDegree 1 where
  certificate := PreorderingCertificate.generator g i
  size_le := PreorderingCertificate.coeffSize_generator_le g i

/-- Lift a bounded certificate after adjoining one generator. -/
def liftAppendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedPreorderingCertificate g p r H)
    (h : MvPolynomial (Fin n) ℝ) :
    BoundedPreorderingCertificate
      (KrivineStengle.appendGenerator g h) p r
      ((((Finset.univ : Finset (Fin (m + 1))).powerset.card : ℕ) : ℝ) * H) where
  certificate := c.certificate.liftAppendGenerator h
  size_le := c.certificate.coeffSize_liftAppendGenerator_le.trans
    (mul_le_mul_of_nonneg_left c.size_le (by positivity))

/-- Enlarge a numerical coefficient bound without changing the certificate. -/
def weakenBound {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H K : ℝ}
    (c : BoundedPreorderingCertificate g p r H) (hHK : H ≤ K) :
    BoundedPreorderingCertificate g p r K where
  certificate := c.certificate
  size_le := c.size_le.trans hHK
/-- Raising the order preserves a numerical coefficient bound. -/
def mono {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r s : ℕ} {H : ℝ}
    (c : BoundedPreorderingCertificate g p r H) (hrs : r ≤ s) :
    BoundedPreorderingCertificate g p s H where
  certificate := c.certificate.mono hrs
  size_le := by simpa using c.size_le

/-- Add bounded preordering certificates. -/
def add {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ} {H K : ℝ}
    (c : BoundedPreorderingCertificate g p r H)
    (d : BoundedPreorderingCertificate g q s K) :
    BoundedPreorderingCertificate g (p + q) (max r s) (H + K) where
  certificate := c.certificate.add d.certificate
  size_le := (c.certificate.coeffSize_add_le d.certificate).trans
    (add_le_add c.size_le d.size_le)

/-- Scale a bounded preordering certificate by a nonnegative scalar. -/
def scaleNonneg {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedPreorderingCertificate g p r H) (a : ℝ) (ha : 0 ≤ a) :
    BoundedPreorderingCertificate g (C a * p) r (a * H) where
  certificate := c.certificate.scaleNonneg a ha
  size_le := (c.certificate.coeffSize_scaleNonneg_le a ha).trans
    (mul_le_mul_of_nonneg_left c.size_le ha)


/-- Multiply bounded preordering certificates.  The only extra loss is
the fixed generator-dependent multiplication factor. -/
def mul {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ} {H K : ℝ}
    (c : BoundedPreorderingCertificate g p r H)
    (d : BoundedPreorderingCertificate g q s K) :
    BoundedPreorderingCertificate g (p * q) (r + s)
      (H * K * PreorderingCertificate.mulFactor g) where
  certificate := c.certificate.mul d.certificate
  size_le := c.certificate.coeffSize_mul_le d.certificate |>.trans <|
    mul_le_mul_of_nonneg_right
      (mul_le_mul c.size_le d.size_le
        d.certificate.coeffSize_nonneg c.bound_nonneg)
      (PreorderingCertificate.mulFactor_nonneg g)

/-- Multiply using any chosen upper bound for the fixed generator factor. -/
def mulOfFactorLe {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ} {H K F : ℝ}
    (c : BoundedPreorderingCertificate g p r H)
    (d : BoundedPreorderingCertificate g q s K)
    (hfactor : PreorderingCertificate.mulFactor g ≤ F) :
    BoundedPreorderingCertificate g (p * q) (r + s) (H * K * F) :=
  (c.mul d).weakenBound <|
    mul_le_mul_of_nonneg_left hfactor (mul_nonneg c.bound_nonneg d.bound_nonneg)
/-- Every ordinary truncated certificate has some finite coefficient bound. -/
theorem exists_of_mem {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (h : p ∈ GenPreordering g r) :
    ∃ H, Nonempty (BoundedPreorderingCertificate g p r H) := by
  obtain ⟨sigma, hsos, hdegree, hidentity⟩ := h
  let c : PreorderingCertificate g p r := ⟨sigma, hsos, hdegree, hidentity⟩
  exact ⟨c.coeffSize, ⟨c, le_rfl⟩⟩

end BoundedPreorderingCertificate

/-- An explicit witness for membership in a truncated quadratic module. -/
structure QuadraticModuleCertificate (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ) where
  sigmaZero : MvPolynomial (Fin n) ℝ
  sigma : Fin m → MvPolynomial (Fin n) ℝ
  isSOSZero : IsSOS sigmaZero
  isSOS : ∀ i, IsSOS (sigma i)
  degreeZero_le : sigmaZero.totalDegree ≤ r
  degree_le : ∀ i, (sigma i * g i).totalDegree ≤ r
  identity : p = sigmaZero + ∑ i : Fin m, sigma i * g i

namespace QuadraticModuleCertificate

theorem toMem {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r) :
    p ∈ GenQuadraticModule g r :=
  ⟨c.sigmaZero, c.sigma, c.isSOSZero, c.isSOS, c.degreeZero_le, c.degree_le,
    c.identity⟩

/-- Total coefficient size of all SOS multipliers in a quadratic-module certificate. -/
def coeffSize {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r) : ℝ :=
  coeffL1Norm c.sigmaZero + ∑ i : Fin m, coeffL1Norm (c.sigma i)

theorem coeffSize_nonneg {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r) :
    0 ≤ c.coeffSize :=
  add_nonneg (coeffL1Norm_nonneg _) (Finset.sum_nonneg fun _ _ ↦ coeffL1Norm_nonneg _)

theorem sigmaZero_le_coeffSize {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r) :
    coeffL1Norm c.sigmaZero ≤ c.coeffSize := by
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ coeffL1Norm_nonneg _)

theorem sigma_le_coeffSize {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r) (i : Fin m) :
    coeffL1Norm (c.sigma i) ≤ c.coeffSize := by
  apply le_trans _ (le_add_of_nonneg_left (coeffL1Norm_nonneg c.sigmaZero))
  exact Finset.single_le_sum
    (f := fun j ↦ coeffL1Norm (c.sigma j))
    (fun j _ ↦ coeffL1Norm_nonneg (c.sigma j)) (Finset.mem_univ i)


/-- Raising the truncation order preserves a named certificate exactly. -/
def mono {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : QuadraticModuleCertificate g p r) (hrs : r ≤ s) :
    QuadraticModuleCertificate g p s where
  sigmaZero := c.sigmaZero
  sigma := c.sigma
  isSOSZero := c.isSOSZero
  isSOS := c.isSOS
  degreeZero_le := c.degreeZero_le.trans hrs
  degree_le := fun i => (c.degree_le i).trans hrs
  identity := c.identity

@[simp]
theorem coeffSize_mono {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : QuadraticModuleCertificate g p r) (hrs : r ≤ s) :
    (c.mono hrs).coeffSize = c.coeffSize := rfl

/-- A named certificate for an SOS free term. -/
def ofSOS (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hp : IsSOS p) (hdegree : p.totalDegree ≤ r) :
    QuadraticModuleCertificate g p r where
  sigmaZero := p
  sigma := 0
  isSOSZero := hp
  isSOS := fun _ => IsSOS_zero
  degreeZero_le := hdegree
  degree_le := by intro i; simp
  identity := by simp

@[simp]
theorem coeffSize_ofSOS
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hp : IsSOS p) (hdegree : p.totalDegree ≤ r) :
    (ofSOS g p hp hdegree).coeffSize = coeffL1Norm p := by
  simp [coeffSize, ofSOS]

/-- A named quadratic-module certificate for one generator. -/
def generator (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    QuadraticModuleCertificate g (g i) (g i).totalDegree where
  sigmaZero := 0
  sigma := Function.update 0 i 1
  isSOSZero := IsSOS_zero
  isSOS := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using IsSOS_C_nonneg (n := n) 1 zero_le_one
    · simp [Function.update_of_ne hji, IsSOS_zero]
  degreeZero_le := by simp
  degree_le := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji]
  identity := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Function.update_of_ne hji]
    · simp

theorem coeffSize_generator_le
    (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    (generator g i).coeffSize ≤ 1 := by
  classical
  unfold coeffSize generator
  rw [Finset.sum_eq_single i]
  · simpa using coeffL1Norm_C_le (n := n) (1 : ℝ)
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

/-- Addition of named quadratic-module certificates. -/
def add {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : QuadraticModuleCertificate g p r)
    (d : QuadraticModuleCertificate g q s) :
    QuadraticModuleCertificate g (p + q) (max r s) where
  sigmaZero := c.sigmaZero + d.sigmaZero
  sigma := fun i => c.sigma i + d.sigma i
  isSOSZero := IsSOS_add c.isSOSZero d.isSOSZero
  isSOS := fun i => IsSOS_add (c.isSOS i) (d.isSOS i)
  degreeZero_le :=
    (MvPolynomial.totalDegree_add _ _).trans
      (max_le_max c.degreeZero_le d.degreeZero_le)
  degree_le := by
    intro i
    calc
      ((c.sigma i + d.sigma i) * g i).totalDegree =
          (c.sigma i * g i + d.sigma i * g i).totalDegree := by ring_nf
      _ ≤ max (c.sigma i * g i).totalDegree
          (d.sigma i * g i).totalDegree := MvPolynomial.totalDegree_add _ _
      _ ≤ max r s := max_le_max (c.degree_le i) (d.degree_le i)
  identity := calc
    p + q =
        (c.sigmaZero + ∑ i : Fin m, c.sigma i * g i) +
          (d.sigmaZero + ∑ i : Fin m, d.sigma i * g i) := by
      rw [← c.identity, ← d.identity]
    _ = (c.sigmaZero + d.sigmaZero) +
        ∑ i : Fin m, (c.sigma i + d.sigma i) * g i := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      ring

theorem coeffSize_add_le {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (c : QuadraticModuleCertificate g p r)
    (d : QuadraticModuleCertificate g q s) :
    (c.add d).coeffSize ≤ c.coeffSize + d.coeffSize := by
  unfold coeffSize add
  calc
    coeffL1Norm (c.sigmaZero + d.sigmaZero) +
        ∑ i : Fin m, coeffL1Norm (c.sigma i + d.sigma i) ≤
      (coeffL1Norm c.sigmaZero + coeffL1Norm d.sigmaZero) +
        ∑ i : Fin m,
          (coeffL1Norm (c.sigma i) + coeffL1Norm (d.sigma i)) := by
      gcongr with i
      · exact coeffL1Norm_add_le _ _
      · exact coeffL1Norm_add_le _ _
    _ = c.coeffSize + d.coeffSize := by
      rw [Finset.sum_add_distrib]
      change
        _ = (coeffL1Norm c.sigmaZero + ∑ i, coeffL1Norm (c.sigma i)) +
          (coeffL1Norm d.sigmaZero + ∑ i, coeffL1Norm (d.sigma i))
      ring

/-- Multiplication of every multiplier by an SOS polynomial. -/
def sosMul {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r) (hq : IsSOS q) :
    QuadraticModuleCertificate g (q * p) (q.totalDegree + r) where
  sigmaZero := q * c.sigmaZero
  sigma := fun i => q * c.sigma i
  isSOSZero := IsSOS_mul hq c.isSOSZero
  isSOS := fun i => IsSOS_mul hq (c.isSOS i)
  degreeZero_le :=
    (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add_left c.degreeZero_le q.totalDegree)
  degree_le := by
    intro i
    calc
      ((q * c.sigma i) * g i).totalDegree =
          (q * (c.sigma i * g i)).totalDegree := by ring_nf
      _ ≤ q.totalDegree + (c.sigma i * g i).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ q.totalDegree + r := Nat.add_le_add_left (c.degree_le i) _
  identity := calc
    q * p = q * (c.sigmaZero + ∑ i : Fin m, c.sigma i * g i) := by
      rw [← c.identity]
    _ = q * c.sigmaZero + ∑ i : Fin m, (q * c.sigma i) * g i := by
      rw [mul_add]
      rw [Finset.mul_sum]
      apply congrArg (fun z => q * c.sigmaZero + z)
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem coeffSize_sosMul_le {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r) (hq : IsSOS q) :
    (c.sosMul hq).coeffSize ≤ coeffL1Norm q * c.coeffSize := by
  unfold coeffSize sosMul
  calc
    coeffL1Norm (q * c.sigmaZero) +
        ∑ i : Fin m, coeffL1Norm (q * c.sigma i) ≤
      coeffL1Norm q * coeffL1Norm c.sigmaZero +
        ∑ i : Fin m, coeffL1Norm q * coeffL1Norm (c.sigma i) := by
      gcongr with i
      · exact coeffL1Norm_mul_le _ _
      · exact coeffL1Norm_mul_le _ _
    _ = coeffL1Norm q * c.coeffSize := by
      change
        _ = coeffL1Norm q *
          (coeffL1Norm c.sigmaZero + ∑ i, coeffL1Norm (c.sigma i))
      rw [mul_add, Finset.mul_sum]

/-- Transport a named certificate across equality of its represented
polynomial. -/
def congr {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r) (hpq : p = q) :
    QuadraticModuleCertificate g q r where
  sigmaZero := c.sigmaZero
  sigma := c.sigma
  isSOSZero := c.isSOSZero
  isSOS := c.isSOS
  degreeZero_le := c.degreeZero_le
  degree_le := c.degree_le
  identity := hpq.symm.trans c.identity


/-- Lift a named quadratic-module certificate after adjoining one generator,
using the zero SOS multiplier for the new generator. -/
def liftAppendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r)
    (h : MvPolynomial (Fin n) ℝ) :
    QuadraticModuleCertificate
      (KrivineStengle.appendGenerator g h) p r where
  sigmaZero := c.sigmaZero
  sigma := Fin.snoc c.sigma 0
  isSOSZero := c.isSOSZero
  isSOS := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [IsSOS_zero]
    · simpa using c.isSOS i
  degreeZero_le := c.degreeZero_le
  degree_le := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp
    · simpa [KrivineStengle.appendGenerator_castSucc] using c.degree_le i
  identity := c.identity.trans <| by
    rw [Fin.sum_univ_castSucc]
    simp [KrivineStengle.appendGenerator_castSucc,
      KrivineStengle.appendGenerator_last]

@[simp]
theorem coeffSize_liftAppendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p h : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : QuadraticModuleCertificate g p r) :
    (c.liftAppendGenerator h).coeffSize = c.coeffSize := by
  unfold coeffSize liftAppendGenerator
  rw [Fin.sum_univ_castSucc]
  simp
end QuadraticModuleCertificate


/-- A quadratic-module certificate together with a coefficient-size bound. -/
structure BoundedQuadraticModuleCertificate
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ) (H : ℝ) where
  certificate : QuadraticModuleCertificate g p r
  size_le : certificate.coeffSize ≤ H

namespace BoundedQuadraticModuleCertificate

theorem toMem {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H) :
    p ∈ GenQuadraticModule g r :=
  c.certificate.toMem

theorem bound_nonneg {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H) :
    0 ≤ H :=
  c.certificate.coeffSize_nonneg.trans c.size_le

theorem exists_of_mem {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (h : p ∈ GenQuadraticModule g r) :
    ∃ H, Nonempty (BoundedQuadraticModuleCertificate g p r H) := by
  obtain ⟨sigmaZero, sigma, hsosZero, hsos, hdegreeZero, hdegree, hidentity⟩ := h
  let c : QuadraticModuleCertificate g p r :=
    ⟨sigmaZero, sigma, hsosZero, hsos, hdegreeZero, hdegree, hidentity⟩
  exact ⟨c.coeffSize, ⟨c, le_rfl⟩⟩


/-- Raising the truncation order does not change a bounded certificate's
coefficient budget. -/
def mono {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r s : ℕ} {H : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H) (hrs : r ≤ s) :
    BoundedQuadraticModuleCertificate g p s H where
  certificate := c.certificate.mono hrs
  size_le := by simpa using c.size_le

/-- An explicitly bounded SOS free-term certificate. -/
def ofSOS (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hp : IsSOS p) (hdegree : p.totalDegree ≤ r) :
    BoundedQuadraticModuleCertificate g p r (coeffL1Norm p) where
  certificate := QuadraticModuleCertificate.ofSOS g p hp hdegree
  size_le := by simp

/-- A quadratic-module generator with coefficient budget one. -/
def generator (g : Fin m → MvPolynomial (Fin n) ℝ) (i : Fin m) :
    BoundedQuadraticModuleCertificate g (g i) (g i).totalDegree 1 where
  certificate := QuadraticModuleCertificate.generator g i
  size_le := QuadraticModuleCertificate.coeffSize_generator_le g i


/-- A bounded quadratic-module certificate remains bounded by the same
coefficient budget after adjoining one generator. -/
def liftAppendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p h : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H) :
    BoundedQuadraticModuleCertificate
      (KrivineStengle.appendGenerator g h) p r H where
  certificate := c.certificate.liftAppendGenerator h
  size_le := by simpa using c.size_le
/-- Addition with the sum of coefficient budgets. -/
def add {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ} {H K : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H)
    (d : BoundedQuadraticModuleCertificate g q s K) :
    BoundedQuadraticModuleCertificate g (p + q) (max r s) (H + K) where
  certificate := c.certificate.add d.certificate
  size_le := (c.certificate.coeffSize_add_le d.certificate).trans
    (add_le_add c.size_le d.size_le)

/-- SOS multiplication with the product coefficient budget. -/
def sosMul {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H)
    (hq : IsSOS q) :
    BoundedQuadraticModuleCertificate g (q * p)
      (q.totalDegree + r) (coeffL1Norm q * H) where
  certificate := c.certificate.sosMul hq
  size_le := (c.certificate.coeffSize_sosMul_le hq).trans
    (mul_le_mul_of_nonneg_left c.size_le (coeffL1Norm_nonneg q))

/-- Enlarge only the coefficient budget. -/
def weakenBound {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ} {H K : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H) (hHK : H ≤ K) :
    BoundedQuadraticModuleCertificate g p r K where
  certificate := c.certificate
  size_le := c.size_le.trans hHK

/-- SOS multiplication using any chosen upper bound for the SOS factor. -/
def sosMulOfNormLe {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ} {H K : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H)
    (hq : IsSOS q) (hqNorm : coeffL1Norm q ≤ K) :
    BoundedQuadraticModuleCertificate g (q * p)
      (q.totalDegree + r) (K * H) :=
  (c.sosMul hq).weakenBound <|
    mul_le_mul_of_nonneg_right hqNorm c.bound_nonneg

/-- Addition followed by any chosen upper bound for the summed budgets. -/
def addOfBoundLe {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r s : ℕ} {H K L : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H)
    (d : BoundedQuadraticModuleCertificate g q s K)
    (hHKL : H + K ≤ L) :
    BoundedQuadraticModuleCertificate g (p + q) (max r s) L :=
  (c.add d).weakenBound hHKL
/-- Transport a bounded certificate across equality of its represented
polynomial without changing either budget. -/
def congr {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (c : BoundedQuadraticModuleCertificate g p r H) (hpq : p = q) :
    BoundedQuadraticModuleCertificate g q r H where
  certificate := c.certificate.congr hpq
  size_le := c.size_le

/-- Proposition-safe finite summation of bounded quadratic-module
certificates at a common order and coefficient budget. -/
theorem sum_nonempty {ι : Type*}
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (p : ι → MvPolynomial (Fin n) ℝ)
    {r : ℕ} {H : ℝ}
    (hcert : ∀ i ∈ s,
      Nonempty (BoundedQuadraticModuleCertificate g (p i) r H)) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (∑ i ∈ s, p i) r (s.card * H)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨by
        simpa using BoundedQuadraticModuleCertificate.ofSOS g
          (0 : MvPolynomial (Fin n) ℝ) IsSOS_zero (Nat.zero_le r)⟩
  | @insert a s ha ih =>
      obtain ⟨chead⟩ := hcert a (Finset.mem_insert_self a s)
      obtain ⟨ctail⟩ := ih fun i hi =>
        hcert i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have csum := chead.add ctail
      exact ⟨by
        simpa [max_self, Nat.cast_add, Nat.cast_one, add_mul, add_comm]
          using csum⟩

/-- Proposition-safe finite summation with a separate coefficient budget for
each summand. -/
theorem sum_nonempty_of_bounds {ι : Type*}
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (p : ι → MvPolynomial (Fin n) ℝ)
    (H : ι → ℝ) {r : ℕ}
    (hcert : ∀ i ∈ s,
      Nonempty (BoundedQuadraticModuleCertificate g (p i) r (H i))) :
    Nonempty (BoundedQuadraticModuleCertificate g
      (∑ i ∈ s, p i) r (∑ i ∈ s, H i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨by
        simpa using BoundedQuadraticModuleCertificate.ofSOS g
          (0 : MvPolynomial (Fin n) ℝ) IsSOS_zero (Nat.zero_le r)⟩
  | @insert a s ha ih =>
      obtain ⟨chead⟩ := hcert a (Finset.mem_insert_self a s)
      obtain ⟨ctail⟩ := ih fun i hi =>
        hcert i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have csum := chead.add ctail
      exact ⟨by simpa [max_self] using csum⟩

/-- Split a bounded certificate after adjoining one nonzero generator while
retaining the coefficient bound on its distinguished SOS multiplier. -/
theorem split_appendGenerator_refutation_at_degree
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {h : MvPolynomial (Fin n) ℝ} {r : ℕ} {H : ℝ}
    (hh : h ≠ 0)
    (c : BoundedQuadraticModuleCertificate
      (KrivineStengle.appendGenerator g h)
      (-1 : MvPolynomial (Fin n) ℝ) r H) :
    ∃ s t : MvPolynomial (Fin n) ℝ,
      s ∈ GenQuadraticModule g r ∧
        IsSOS t ∧
        t.totalDegree ≤ r ∧
        coeffL1Norm t ≤ H ∧
        (-1 : MvPolynomial (Fin n) ℝ) = s + h * t := by
  let s : MvPolynomial (Fin n) ℝ :=
    c.certificate.sigmaZero +
      ∑ i : Fin m, c.certificate.sigma i.castSucc * g i
  let t : MvPolynomial (Fin n) ℝ :=
    c.certificate.sigma (Fin.last m)
  have hs : s ∈ GenQuadraticModule g r := by
    refine ⟨c.certificate.sigmaZero,
      fun i => c.certificate.sigma i.castSucc,
      c.certificate.isSOSZero,
      fun i => c.certificate.isSOS i.castSucc,
      c.certificate.degreeZero_le, ?_, rfl⟩
    intro i
    simpa [KrivineStengle.appendGenerator_castSucc] using
      c.certificate.degree_le i.castSucc
  have ht : IsSOS t := c.certificate.isSOS (Fin.last m)
  have htTerm : (t * h).totalDegree ≤ r := by
    simpa [t, KrivineStengle.appendGenerator_last] using
      c.certificate.degree_le (Fin.last m)
  have htDegree : t.totalDegree ≤ r := by
    by_cases htzero : t = 0
    · simp [htzero]
    · rw [totalDegree_mul_of_isDomain htzero hh] at htTerm
      omega
  have htNorm : coeffL1Norm t ≤ H := by
    exact (c.certificate.sigma_le_coeffSize (Fin.last m)).trans c.size_le
  refine ⟨s, t, hs, ht, htDegree, htNorm, ?_⟩
  calc
    (-1 : MvPolynomial (Fin n) ℝ) =
        c.certificate.sigmaZero +
          ∑ j : Fin (m + 1),
            c.certificate.sigma j *
              KrivineStengle.appendGenerator g h j :=
      c.certificate.identity
    _ = s + h * t := by
      rw [Fin.sum_univ_castSucc]
      simp only [KrivineStengle.appendGenerator_castSucc,
        KrivineStengle.appendGenerator_last]
      dsimp [s, t]
      ring


end BoundedQuadraticModuleCertificate

end OptimalConvergenceRates.GeneralArchimedean

end
