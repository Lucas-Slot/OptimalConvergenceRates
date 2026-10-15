/-
  Substitution of interval SOS certificates into an arbitrary quadratic
  module.
-/
import OptimalConvergenceRates.GeneralArchimedean.QuantitativeIntervalCertificate
import OptimalConvergenceRates.GeneralArchimedean.ModuleOrder
import OptimalConvergenceRates.GeneralArchimedean.BoundedModuleOrder
import OptimalConvergenceRates.GeneralArchimedean.Certificates
import OptimalConvergenceRates.GeneralArchimedean.PositiveCoefficientCertificate
import OptimalConvergenceRates.GeneralArchimedean.RationalSquareRootPackage

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace GeneralArchimedean

variable {n m : ℕ}

/-- An interval certificate can be substituted into a quadratic module that
contains both interval generators a and B-a. -/
theorem IntervalCertificate.subst_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {p : Polynomial ℝ}
    (cert : IntervalCertificate B p)
    (a : MvPolynomial (Fin n) ℝ)
    (ha : QuadraticModuleMem g a)
    (hBa : QuadraticModuleMem g (C B - a)) :
    QuadraticModuleMem g (polynomialSubst a p) := by
  have hzero : QuadraticModuleMem g
      (polynomialSubst a cert.sigmaZero) :=
    QuadraticModuleMem.of_isSOS g
      (isSOS_polynomialSubst a cert.isSOSZero)
  have hleftSOS : IsSOS (polynomialSubst a cert.sigmaLeft) :=
    isSOS_polynomialSubst a cert.isSOSLeft
  have hrightSOS : IsSOS (polynomialSubst a cert.sigmaRight) :=
    isSOS_polynomialSubst a cert.isSOSRight
  have hleft : QuadraticModuleMem g
      (a * polynomialSubst a cert.sigmaLeft) := by
    simpa [mul_comm] using QuadraticModuleMem.sos_mul hleftSOS ha
  have hright : QuadraticModuleMem g
      ((C B - a) * polynomialSubst a cert.sigmaRight) := by
    simpa [mul_comm] using QuadraticModuleMem.sos_mul hrightSOS hBa
  have hsum := hzero.add (hleft.add hright)
  convert hsum using 1
  have hid := congrArg (Polynomial.aeval a) cert.identity
  calc
    polynomialSubst a p =
        polynomialSubst a cert.sigmaZero +
          a * polynomialSubst a cert.sigmaLeft +
          (C B - a) * polynomialSubst a cert.sigmaRight := by
      simpa [polynomialSubst, map_add, map_mul, map_sub] using hid
    _ = _ := by ring

/-- Degree-controlled substitution of an interval certificate. -/
theorem IntervalCertificate.subst_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {p : Polynomial ℝ}
    (cert : IntervalCertificate B p)
    (a : MvPolynomial (Fin n) ℝ) {r s : ℕ}
    (ha : a ∈ GenQuadraticModule g r)
    (hBa : C B - a ∈ GenQuadraticModule g s) :
    polynomialSubst a p ∈ GenQuadraticModule g
      (max r s + (p.natDegree + 3) * a.totalDegree) := by
  let d := (p.natDegree + 3) * a.totalDegree
  have hzeroDegree :
      (polynomialSubst a cert.sigmaZero).totalDegree ≤ d := by
    exact (polynomialSubst_totalDegree_le a cert.sigmaZero).trans
      (Nat.mul_le_mul_right a.totalDegree
        (cert.degreeZero_le.trans (by omega)))
  have hleftDegree :
      (polynomialSubst a cert.sigmaLeft).totalDegree ≤ d := by
    exact (polynomialSubst_totalDegree_le a cert.sigmaLeft).trans
      (Nat.mul_le_mul_right a.totalDegree cert.degreeLeft_le)
  have hrightDegree :
      (polynomialSubst a cert.sigmaRight).totalDegree ≤ d := by
    exact (polynomialSubst_totalDegree_le a cert.sigmaRight).trans
      (Nat.mul_le_mul_right a.totalDegree cert.degreeRight_le)
  have hzeroRaw : polynomialSubst a cert.sigmaZero ∈
      GenQuadraticModule g d :=
    genQuadraticModule_sos g
      (isSOS_polynomialSubst a cert.isSOSZero) hzeroDegree
  have hzero : polynomialSubst a cert.sigmaZero ∈
      GenQuadraticModule g (max r s + d) :=
    GenQuadraticModule_mono (Nat.le_add_left d (max r s)) hzeroRaw
  have hleftRaw : polynomialSubst a cert.sigmaLeft * a ∈
      GenQuadraticModule g
        (r + (polynomialSubst a cert.sigmaLeft).totalDegree) :=
    genQuadraticModule_sos_mul
      (isSOS_polynomialSubst a cert.isSOSLeft) ha
  have hleft : polynomialSubst a cert.sigmaLeft * a ∈
      GenQuadraticModule g (max r s + d) :=
    GenQuadraticModule_mono
      (Nat.add_le_add (le_max_left r s) hleftDegree) hleftRaw
  have hrightRaw : polynomialSubst a cert.sigmaRight * (C B - a) ∈
      GenQuadraticModule g
        (s + (polynomialSubst a cert.sigmaRight).totalDegree) :=
    genQuadraticModule_sos_mul
      (isSOS_polynomialSubst a cert.isSOSRight) hBa
  have hright : polynomialSubst a cert.sigmaRight * (C B - a) ∈
      GenQuadraticModule g (max r s + d) :=
    GenQuadraticModule_mono
      (Nat.add_le_add (le_max_right r s) hrightDegree) hrightRaw
  have hsum := GenQuadraticModule_add hzero
    (GenQuadraticModule_add hleft hright)
  convert hsum using 1
  have hid := congrArg (Polynomial.aeval a) cert.identity
  calc
    polynomialSubst a p =
        polynomialSubst a cert.sigmaZero +
          a * polynomialSubst a cert.sigmaLeft +
          (C B - a) * polynomialSubst a cert.sigmaRight := by
      simpa [polynomialSubst, map_add, map_mul, map_sub] using hid
    _ = _ := by ring


namespace RationalSquareRoot
namespace Package

/-- The polynomial measuring the first interval inequality. -/
def errorGap {δ B theta : ℝ} (pkg : Package δ B theta) : Polynomial ℝ :=
  Polynomial.C theta * pkg.P ^ 2 +
    Polynomial.C δ * pkg.V ^ 2 - pkg.E

/-- The polynomial measuring a chosen numerator-square upper bound. -/
def numeratorGap {δ B theta : ℝ} (pkg : Package δ B theta)
    (B' : ℝ) : Polynomial ℝ :=
  Polynomial.C B' * pkg.V ^ 2 - pkg.P ^ 2

theorem errorGap_degree_le
    {δ B theta : ℝ} (pkg : Package δ B theta) :
    pkg.errorGap.natDegree ≤ pkg.degreeBound := by
  dsimp [errorGap]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans pkg.P_sq_degree_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans pkg.V_sq_degree_le
  · exact pkg.E_degree_le

theorem numeratorGap_degree_le
    {δ B theta B' : ℝ} (pkg : Package δ B theta) :
    (pkg.numeratorGap B').natDegree ≤ pkg.degreeBound := by
  dsimp [numeratorGap]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans pkg.V_sq_degree_le
  · exact pkg.P_sq_degree_le


theorem errorGap_nonnegOn
    {δ B theta : ℝ} (pkg : Package δ B theta) (hδ : 0 < δ) :
    ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) B → 0 ≤ (pkg.errorGap).eval u := by
  intro u hu
  have h := pkg.error_le hδ hu.1 hu.2
  simp only [errorGap, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
  linarith

theorem numeratorGap_nonnegOn
    {δ B theta B' : ℝ} (pkg : Package δ B theta) (hδ : 0 < δ)
    (htheta1 : theta < 1)
    (hB' : B + δ ≤ (1 - theta) * B') :
    ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) B →
      0 ≤ (pkg.numeratorGap B').eval u := by
  intro u hu
  have h := pkg.numerator_sq_le hδ htheta1 hB' hu.1 hu.2
  simp only [numeratorGap, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow]
  linarith

/-- The first pointwise dyadic estimate becomes a genuine module-order
inequality after an interval certificate and substitution. -/
theorem substE_le_thetaP_sq_add_deltaV_sq
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 0 < B)
    {a : MvPolynomial (Fin n) ℝ}
    (ha : QuadraticModuleMem g a)
    (hBa : QuadraticModuleMem g (C B - a)) :
    ModuleLE g (polynomialSubst a pkg.E)
      (C theta * polynomialSubst a pkg.P ^ 2 +
        C δ * polynomialSubst a pkg.V ^ 2) := by
  obtain ⟨cert⟩ :=
    intervalCertificate_nonempty hB pkg.errorGap
      (pkg.errorGap_nonnegOn hδ)
  have hmem := cert.subst_mem a ha hBa
  change QuadraticModuleMem g
    ((C theta * polynomialSubst a pkg.P ^ 2 +
      C δ * polynomialSubst a pkg.V ^ 2) -
        polynomialSubst a pkg.E)
  simpa [errorGap, polynomialSubst, map_sub, map_add, map_mul, map_pow]
    using hmem

/-- The numerator-square estimate likewise becomes a module-order
inequality. -/
theorem substP_sq_le_B_mul_substV_sq
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta1 : theta < 1)
    (hB' : B + δ ≤ (1 - theta) * B')
    {a : MvPolynomial (Fin n) ℝ}
    (ha : QuadraticModuleMem g a)
    (hBa : QuadraticModuleMem g (C B - a)) :
    ModuleLE g (polynomialSubst a pkg.P ^ 2)
      (C B' * polynomialSubst a pkg.V ^ 2) := by
  obtain ⟨cert⟩ :=
    intervalCertificate_nonempty hB (pkg.numeratorGap B')
      (pkg.numeratorGap_nonnegOn hδ htheta1 hB')
  have hmem := cert.subst_mem a ha hBa
  change QuadraticModuleMem g
    (C B' * polynomialSubst a pkg.V ^ 2 -
      polynomialSubst a pkg.P ^ 2)
  simpa [numeratorGap, polynomialSubst, map_sub, map_mul, map_pow]
    using hmem


/-- Degree-tracked form of the first rational-square-root interval
inequality. -/
theorem substE_le_thetaP_sq_add_deltaV_sq_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 0 < B)
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (ha : a ∈ GenQuadraticModule g r)
    (hBa : C B - a ∈ GenQuadraticModule g s) :
    ModuleLEAt g
      (max r s + (pkg.degreeBound + 3) * a.totalDegree)
      (polynomialSubst a pkg.E)
      (C theta * polynomialSubst a pkg.P ^ 2 +
        C δ * polynomialSubst a pkg.V ^ 2) := by
  obtain ⟨cert⟩ :=
    intervalCertificate_nonempty hB pkg.errorGap
      (pkg.errorGap_nonnegOn hδ)
  have hmem := cert.subst_mem_at a ha hBa
  have horder :
      max r s + (pkg.errorGap.natDegree + 3) * a.totalDegree ≤
        max r s + (pkg.degreeBound + 3) * a.totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree
        (Nat.add_le_add_right pkg.errorGap_degree_le 3)) _
  have hmem' := GenQuadraticModule_mono horder hmem
  change (C theta * polynomialSubst a pkg.P ^ 2 +
      C δ * polynomialSubst a pkg.V ^ 2) -
        polynomialSubst a pkg.E ∈ GenQuadraticModule g _
  simpa [errorGap, polynomialSubst, map_sub, map_add, map_mul, map_pow]
    using hmem'

/-- Degree-tracked form of the numerator-square interval inequality. -/
theorem substP_sq_le_B_mul_substV_sq_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta1 : theta < 1)
    (hB' : B + δ ≤ (1 - theta) * B')
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (ha : a ∈ GenQuadraticModule g r)
    (hBa : C B - a ∈ GenQuadraticModule g s) :
    ModuleLEAt g
      (max r s + (pkg.degreeBound + 3) * a.totalDegree)
      (polynomialSubst a pkg.P ^ 2)
      (C B' * polynomialSubst a pkg.V ^ 2) := by
  obtain ⟨cert⟩ :=
    intervalCertificate_nonempty hB (pkg.numeratorGap B')
      (pkg.numeratorGap_nonnegOn hδ htheta1 hB')
  have hmem := cert.subst_mem_at a ha hBa
  have horder :
      max r s + ((pkg.numeratorGap B').natDegree + 3) * a.totalDegree ≤
        max r s + (pkg.degreeBound + 3) * a.totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree
        (Nat.add_le_add_right pkg.numeratorGap_degree_le 3)) _
  have hmem' := GenQuadraticModule_mono horder hmem
  change C B' * polynomialSubst a pkg.V ^ 2 -
      polynomialSubst a pkg.P ^ 2 ∈ GenQuadraticModule g _
  simpa [numeratorGap, polynomialSubst, map_sub, map_mul, map_pow]
    using hmem'

end Package
end RationalSquareRoot

/-- Common coefficient envelope for each substituted SOS multiplier in a
bounded interval certificate. -/
def intervalSubstitutionMultiplierBound
    {B : ℝ} {p : Polynomial ℝ} {H : ℝ}
    (_cert : BoundedIntervalCertificate B p H) (G : ℝ) : ℝ :=
  H * G ^ (p.natDegree + 3)

/-- Substitution of a bounded interval certificate into bounded certificates
for the two interval generators, retaining both degree and coefficient-size
bounds. -/
def BoundedIntervalCertificate.subst_bounded
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {B : ℝ} {p : Polynomial ℝ} {H Ha Hb G : ℝ}
    (cert : BoundedIntervalCertificate B p H)
    (a : MvPolynomial (Fin n) ℝ) {r s : ℕ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    BoundedQuadraticModuleCertificate g (polynomialSubst a p)
      (max r s + (p.natDegree + 3) * a.totalDegree)
      (intervalSubstitutionMultiplierBound cert G +
        (intervalSubstitutionMultiplierBound cert G * Ha +
          intervalSubstitutionMultiplierBound cert G * Hb)) := by
  let K : ℝ := intervalSubstitutionMultiplierBound cert G
  let D : ℕ := (p.natDegree + 3) * a.totalDegree
  let R : ℕ := max r s + D
  have hH : 0 ≤ H := cert.bound_nonneg
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hcomponent
      (q : Polynomial ℝ)
      (hqNorm : embeddedPolynomialCoeffL1Norm q ≤ H)
      (hqDegree : q.natDegree ≤ p.natDegree + 3) :
      coeffL1Norm (polynomialSubst a q) ≤ K := by
    calc
      coeffL1Norm (polynomialSubst a q) ≤
          embeddedPolynomialCoeffL1Norm q * G ^ q.natDegree :=
        polynomialSubst_coeffL1Norm_le_embedded a q hG haNorm
      _ ≤ H * G ^ (p.natDegree + 3) := by
        exact mul_le_mul hqNorm (pow_le_pow_right₀ hG hqDegree)
          (pow_nonneg hG0 _) hH
      _ = K := rfl
  have hzeroNorm :
      coeffL1Norm (polynomialSubst a cert.certificate.sigmaZero) ≤ K :=
    hcomponent cert.certificate.sigmaZero
      (cert.certificate.sigmaZero_norm_le_coeffSize.trans cert.size_le)
      (cert.certificate.degreeZero_le.trans (by omega))
  have hleftNorm :
      coeffL1Norm (polynomialSubst a cert.certificate.sigmaLeft) ≤ K :=
    hcomponent cert.certificate.sigmaLeft
      (cert.certificate.sigmaLeft_norm_le_coeffSize.trans cert.size_le)
      cert.certificate.degreeLeft_le
  have hrightNorm :
      coeffL1Norm (polynomialSubst a cert.certificate.sigmaRight) ≤ K :=
    hcomponent cert.certificate.sigmaRight
      (cert.certificate.sigmaRight_norm_le_coeffSize.trans cert.size_le)
      cert.certificate.degreeRight_le
  have hzeroDegree :
      (polynomialSubst a cert.certificate.sigmaZero).totalDegree ≤ D := by
    calc
      (polynomialSubst a cert.certificate.sigmaZero).totalDegree ≤
          cert.certificate.sigmaZero.natDegree * a.totalDegree :=
        polynomialSubst_totalDegree_le _ _
      _ ≤ (p.natDegree + 3) * a.totalDegree :=
        Nat.mul_le_mul_right a.totalDegree
          (cert.certificate.degreeZero_le.trans (by omega))
      _ = D := rfl
  have hleftDegree :
      (polynomialSubst a cert.certificate.sigmaLeft).totalDegree ≤ D := by
    exact (polynomialSubst_totalDegree_le _ _).trans
      (Nat.mul_le_mul_right a.totalDegree cert.certificate.degreeLeft_le)
  have hrightDegree :
      (polynomialSubst a cert.certificate.sigmaRight).totalDegree ≤ D := by
    exact (polynomialSubst_totalDegree_le _ _).trans
      (Nat.mul_le_mul_right a.totalDegree cert.certificate.degreeRight_le)
  have hzeroOrder : D ≤ R := Nat.le_add_left D (max r s)
  have hleftOrder :
      (polynomialSubst a cert.certificate.sigmaLeft).totalDegree + r ≤ R := by
    calc
      _ ≤ D + r := Nat.add_le_add_right hleftDegree r
      _ ≤ D + max r s := Nat.add_le_add_left (le_max_left r s) D
      _ = R := by simp [R, Nat.add_comm]
  have hrightOrder :
      (polynomialSubst a cert.certificate.sigmaRight).totalDegree + s ≤ R := by
    calc
      _ ≤ D + s := Nat.add_le_add_right hrightDegree s
      _ ≤ D + max r s := Nat.add_le_add_left (le_max_right r s) D
      _ = R := by simp [R, Nat.add_comm]
  let cZero : BoundedQuadraticModuleCertificate g
      (polynomialSubst a cert.certificate.sigmaZero) D K :=
    (BoundedQuadraticModuleCertificate.ofSOS g
      (polynomialSubst a cert.certificate.sigmaZero)
      (isSOS_polynomialSubst a cert.certificate.isSOSZero) hzeroDegree).weakenBound
        hzeroNorm
  let cLeft : BoundedQuadraticModuleCertificate g
      (polynomialSubst a cert.certificate.sigmaLeft * a)
      ((polynomialSubst a cert.certificate.sigmaLeft).totalDegree + r)
      (K * Ha) :=
    ca.sosMulOfNormLe
      (isSOS_polynomialSubst a cert.certificate.isSOSLeft) hleftNorm
  let cRight : BoundedQuadraticModuleCertificate g
      (polynomialSubst a cert.certificate.sigmaRight * (C B - a))
      ((polynomialSubst a cert.certificate.sigmaRight).totalDegree + s)
      (K * Hb) :=
    cBa.sosMulOfNormLe
      (isSOS_polynomialSubst a cert.certificate.isSOSRight) hrightNorm
  let cZero' := cZero.mono hzeroOrder
  let cLeft' := cLeft.mono hleftOrder
  let cRight' := cRight.mono hrightOrder
  let combined := cZero'.add (cLeft'.add cRight')
  have combinedAt : BoundedQuadraticModuleCertificate g
      (polynomialSubst a cert.certificate.sigmaZero +
        (polynomialSubst a cert.certificate.sigmaLeft * a +
          polynomialSubst a cert.certificate.sigmaRight * (C B - a)))
      R (K + (K * Ha + K * Hb)) := by
    simpa only [max_self] using combined
  have hpoly :
      polynomialSubst a p =
        polynomialSubst a cert.certificate.sigmaZero +
          (polynomialSubst a cert.certificate.sigmaLeft * a +
            polynomialSubst a cert.certificate.sigmaRight * (C B - a)) := by
    have hid := congrArg (Polynomial.aeval a) cert.certificate.identity
    calc
      polynomialSubst a p =
          polynomialSubst a cert.certificate.sigmaZero +
            a * polynomialSubst a cert.certificate.sigmaLeft +
              (C B - a) * polynomialSubst a cert.certificate.sigmaRight := by
        simpa only [polynomialSubst, map_add, map_mul, map_sub,
          Polynomial.aeval_X, Polynomial.aeval_C, MvPolynomial.C_eq_algebraMap] using hid
      _ = polynomialSubst a cert.certificate.sigmaZero +
          (polynomialSubst a cert.certificate.sigmaLeft * a +
            polynomialSubst a cert.certificate.sigmaRight * (C B - a)) := by
        ring
  simpa [R, D, K, intervalSubstitutionMultiplierBound] using
    combinedAt.congr hpoly.symm

namespace RationalSquareRoot
namespace Package

/-- Coefficient-bounded first rational-square-root interval comparison.
Its existential bound records the actual Markov--Lukács certificate size;
the quantitative envelope is supplied independently of this conversion API. -/
theorem exists_bounded_substE_comparison
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 0 < B)
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ} {Ha Hb G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    ∃ K : ℝ, Nonempty
      (BoundedModuleLEAt g
        (max r s + (pkg.degreeBound + 3) * a.totalDegree)
        (K + (K * Ha + K * Hb))
        (polynomialSubst a pkg.E)
        (C theta * polynomialSubst a pkg.P ^ 2 +
          C δ * polynomialSubst a pkg.V ^ 2)) := by
  obtain ⟨_, ⟨cert⟩⟩ :=
    boundedIntervalCertificate_exists hB pkg.errorGap
      (pkg.errorGap_nonnegOn hδ)
  let K := intervalSubstitutionMultiplierBound cert G
  let c := cert.subst_bounded a ca cBa hG haNorm
  have horder :
      max r s + (pkg.errorGap.natDegree + 3) * a.totalDegree ≤
        max r s + (pkg.degreeBound + 3) * a.totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree
        (Nat.add_le_add_right pkg.errorGap_degree_le 3)) _
  have hpoly :
      polynomialSubst a pkg.errorGap =
        (C theta * polynomialSubst a pkg.P ^ 2 +
          C δ * polynomialSubst a pkg.V ^ 2) -
            polynomialSubst a pkg.E := by
    simp [errorGap, polynomialSubst, map_sub, map_add, map_mul, map_pow]
  refine ⟨K, ⟨?_⟩⟩
  simpa [K] using (c.mono horder).congr hpoly

/-- Coefficient-bounded version of the numerator-square interval
comparison. -/
theorem exists_bounded_substP_sq_comparison
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 0 < B)
    (htheta1 : theta < 1)
    (hB' : B + δ ≤ (1 - theta) * B')
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ} {Ha Hb G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    ∃ K : ℝ, Nonempty
      (BoundedModuleLEAt g
        (max r s + (pkg.degreeBound + 3) * a.totalDegree)
        (K + (K * Ha + K * Hb))
        (polynomialSubst a pkg.P ^ 2)
        (C B' * polynomialSubst a pkg.V ^ 2)) := by
  obtain ⟨_, ⟨cert⟩⟩ :=
    boundedIntervalCertificate_exists hB (pkg.numeratorGap B')
      (pkg.numeratorGap_nonnegOn hδ htheta1 hB')
  let K := intervalSubstitutionMultiplierBound cert G
  let c := cert.subst_bounded a ca cBa hG haNorm
  have horder :
      max r s + ((pkg.numeratorGap B').natDegree + 3) * a.totalDegree ≤
        max r s + (pkg.degreeBound + 3) * a.totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree
        (Nat.add_le_add_right pkg.numeratorGap_degree_le 3)) _
  have hpoly :
      polynomialSubst a (pkg.numeratorGap B') =
        C B' * polynomialSubst a pkg.V ^ 2 -
          polynomialSubst a pkg.P ^ 2 := by
    simp [numeratorGap, polynomialSubst, map_sub, map_mul, map_pow]
  refine ⟨K, ⟨?_⟩⟩
  simpa [K] using (c.mono horder).congr hpoly

/-- Explicit coefficient budget for the error-polynomial interval
comparison after substitution. -/
def errorComparisonCoefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta) (G : ℝ) : ℝ :=
  intervalCertificateCoefficientBound B pkg.errorGap *
    G ^ (pkg.errorGap.natDegree + 3)

/-- Explicit coefficient budget for the numerator-square interval
comparison after substitution. -/
def numeratorComparisonCoefficientBound
    {δ B theta : ℝ} (pkg : Package δ B theta) (B' G : ℝ) : ℝ :=
  intervalCertificateCoefficientBound B (pkg.numeratorGap B') *
    G ^ ((pkg.numeratorGap B').natDegree + 3)

/-- Explicitly bounded version of the first rational-square-root interval
comparison. -/
theorem bounded_substE_comparison
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 1 ≤ B)
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ} {Ha Hb G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    Nonempty (BoundedModuleLEAt g
      (max r s + (pkg.degreeBound + 3) * a.totalDegree)
      (pkg.errorComparisonCoefficientBound G +
        (pkg.errorComparisonCoefficientBound G * Ha +
          pkg.errorComparisonCoefficientBound G * Hb))
      (polynomialSubst a pkg.E)
      (C theta * polynomialSubst a pkg.P ^ 2 +
        C δ * polynomialSubst a pkg.V ^ 2)) := by
  obtain ⟨cert⟩ := boundedIntervalCertificate_nonempty_explicit
    hB pkg.errorGap (pkg.errorGap_nonnegOn hδ)
  let c := cert.subst_bounded a ca cBa hG haNorm
  have horder :
      max r s + (pkg.errorGap.natDegree + 3) * a.totalDegree ≤
        max r s + (pkg.degreeBound + 3) * a.totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree
        (Nat.add_le_add_right pkg.errorGap_degree_le 3)) _
  have hpoly :
      polynomialSubst a pkg.errorGap =
        (C theta * polynomialSubst a pkg.P ^ 2 +
          C δ * polynomialSubst a pkg.V ^ 2) -
            polynomialSubst a pkg.E := by
    simp [errorGap, polynomialSubst, map_sub, map_add, map_mul, map_pow]
  exact ⟨by simpa [c, errorComparisonCoefficientBound,
    intervalSubstitutionMultiplierBound] using (c.mono horder).congr hpoly⟩

/-- Explicitly bounded version of the numerator-square interval comparison. -/
theorem bounded_substP_sq_comparison
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {δ B theta B' : ℝ} (pkg : Package δ B theta)
    (hδ : 0 < δ) (hB : 1 ≤ B)
    (htheta1 : theta < 1)
    (hB' : B + δ ≤ (1 - theta) * B')
    {a : MvPolynomial (Fin n) ℝ} {r s : ℕ} {Ha Hb G : ℝ}
    (ca : BoundedQuadraticModuleCertificate g a r Ha)
    (cBa : BoundedQuadraticModuleCertificate g (C B - a) s Hb)
    (hG : 1 ≤ G) (haNorm : coeffL1Norm a ≤ G) :
    Nonempty (BoundedModuleLEAt g
      (max r s + (pkg.degreeBound + 3) * a.totalDegree)
      (pkg.numeratorComparisonCoefficientBound B' G +
        (pkg.numeratorComparisonCoefficientBound B' G * Ha +
          pkg.numeratorComparisonCoefficientBound B' G * Hb))
      (polynomialSubst a pkg.P ^ 2)
      (C B' * polynomialSubst a pkg.V ^ 2)) := by
  obtain ⟨cert⟩ := boundedIntervalCertificate_nonempty_explicit
    hB (pkg.numeratorGap B')
      (pkg.numeratorGap_nonnegOn hδ htheta1 hB')
  let c := cert.subst_bounded a ca cBa hG haNorm
  have horder :
      max r s + ((pkg.numeratorGap B').natDegree + 3) * a.totalDegree ≤
        max r s + (pkg.degreeBound + 3) * a.totalDegree :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_right a.totalDegree
        (Nat.add_le_add_right pkg.numeratorGap_degree_le 3)) _
  have hpoly :
      polynomialSubst a (pkg.numeratorGap B') =
        C B' * polynomialSubst a pkg.V ^ 2 -
          polynomialSubst a pkg.P ^ 2 := by
    simp [numeratorGap, polynomialSubst, map_sub, map_mul, map_pow]
  exact ⟨by simpa [c, numeratorComparisonCoefficientBound,
    intervalSubstitutionMultiplierBound] using (c.mono horder).congr hpoly⟩

end Package
end RationalSquareRoot
end GeneralArchimedean
end OptimalConvergenceRates

end
