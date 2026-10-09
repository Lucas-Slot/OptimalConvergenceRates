/-
  Explicit coefficient bounds for the interval certificates used in the
  general Archimedean conversion.
-/
import OptimalConvergenceRates.GeneralArchimedean.IntervalCertificateBounds
import OptimalConvergenceRates.GeneralArchimedean.UnivariateSupNorm

noncomputable section

open Polynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

/-- The affine parametrization of the middle half of `[0,B]`. -/
def middleToInterval (B : ℝ) : Polynomial ℝ :=
  Polynomial.C (B / 4) * Polynomial.X + Polynomial.C (B / 2)

/-- The inverse affine coordinate on the middle half of `[0,B]`. -/
def intervalToMiddle (B : ℝ) : Polynomial ℝ :=
  Polynomial.C (4 / B) * Polynomial.X + Polynomial.C (-2)

theorem affine_natDegree_le (c d : ℝ) :
    (Polynomial.C c * Polynomial.X + Polynomial.C d).natDegree ≤ 1 := by
  exact (Polynomial.natDegree_add_le _ _).trans (by
    apply max_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · simp)

theorem middleToInterval_natDegree_le (B : ℝ) :
    (middleToInterval B).natDegree ≤ 1 :=
  affine_natDegree_le _ _

theorem intervalToMiddle_natDegree_le (B : ℝ) :
    (intervalToMiddle B).natDegree ≤ 1 :=
  affine_natDegree_le _ _

theorem middleToInterval_eval_mem
    {B x : ℝ} (hB : 0 ≤ B) (hx : |x| ≤ 1) :
    (middleToInterval B).eval x ∈ Set.Icc (B / 4) (3 * B / 4) := by
  simp only [middleToInterval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  constructor <;> nlinarith [abs_le.mp hx]

theorem middle_affine_inverse_eval
    {B : ℝ} (hB : B ≠ 0) (u : ℝ) :
    (middleToInterval B).eval ((intervalToMiddle B).eval u) = u := by
  simp only [middleToInterval, intervalToMiddle, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  field_simp [hB]
  ring

theorem intervalToUnit_embedded_norm_le_three
    {B : ℝ} (hB : 1 ≤ B) :
    embeddedPolynomialCoeffL1Norm (intervalToUnit B) ≤ 3 := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hdiv : |2 / B| ≤ (2 : ℝ) := by
    rw [abs_of_pos (div_pos (by norm_num) hBpos)]
    exact (div_le_iff₀ hBpos).2 (by nlinarith)
  have heq : intervalToUnit B =
      Polynomial.C (2 / B) * Polynomial.X + Polynomial.C (-1) := by
    dsimp [intervalToUnit]
    simp [sub_eq_add_neg]
  rw [heq]
  calc
    embeddedPolynomialCoeffL1Norm
        (Polynomial.C (2 / B) * Polynomial.X + Polynomial.C (-1)) ≤
        |2 / B| + |-1| :=
      embeddedPolynomialCoeffL1Norm_C_mul_X_add_C_le _ _
    _ ≤ 3 := by norm_num at *; linarith

theorem intervalToMiddle_embedded_norm_le_six
    {B : ℝ} (hB : 1 ≤ B) :
    embeddedPolynomialCoeffL1Norm (intervalToMiddle B) ≤ 6 := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hdiv : |4 / B| ≤ (4 : ℝ) := by
    rw [abs_of_pos (div_pos (by norm_num) hBpos)]
    exact (div_le_iff₀ hBpos).2 (by nlinarith)
  unfold intervalToMiddle
  calc
    embeddedPolynomialCoeffL1Norm
        (Polynomial.C (4 / B) * Polynomial.X + Polynomial.C (-2)) ≤
        |4 / B| + |-2| :=
      embeddedPolynomialCoeffL1Norm_C_mul_X_add_C_le _ _
    _ ≤ 6 := by norm_num at *; linarith

/-- A common degree parameter for both SOS polynomials in the interval
product certificate. -/
def intervalCertificateDegree (p : Polynomial ℝ) : ℕ := p.natDegree + 3

/-- A uniform upper bound for the values of `p` on `[0,B]`, when `B ≥ 1`. -/
def intervalValueBound (B : ℝ) (p : Polynomial ℝ) : ℝ :=
  polynomialCoeffL1Norm p * B ^ p.natDegree

/-- The common Markov coefficient bound after rescaling an interval to the
unit interval. -/
def intervalMarkovCoefficientBound (B : ℝ) (p : Polynomial ℝ) : ℝ :=
  let D := intervalCertificateDegree p
  (D + 1 : ℕ) * (D : ℝ) ^ (2 * D) * intervalValueBound B p

theorem intervalValueBound_nonneg {B : ℝ} (hB : 1 ≤ B)
    (p : Polynomial ℝ) : 0 ≤ intervalValueBound B p := by
  exact mul_nonneg (polynomialCoeffL1Norm_nonneg p)
    (pow_nonneg (hB.trans' (by norm_num)) _)

theorem intervalMarkovCoefficientBound_nonneg {B : ℝ} (hB : 1 ≤ B)
    (p : Polynomial ℝ) : 0 ≤ intervalMarkovCoefficientBound B p := by
  unfold intervalMarkovCoefficientBound
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (intervalValueBound_nonneg hB p)

theorem abs_eval_le_intervalValueBound
    {B u : ℝ} (hB : 1 ≤ B) (p : Polynomial ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) B) :
    |p.eval u| ≤ intervalValueBound B p := by
  apply abs_eval_le_polynomialCoeffL1Norm_mul_pow p hB
  rw [abs_of_nonneg hu.1]
  exact hu.2

/-- The middle-half factor is uniformly separated from zero. -/
theorem one_sixteenth_le_interval_product
    {B u : ℝ} (hB : 1 ≤ B)
    (hu : u ∈ Set.Icc (B / 4) (3 * B / 4)) :
    (1 : ℝ) / 16 ≤ u * (B - u) := by
  have hquarter : 0 ≤ B / 4 := by positivity
  have hu0 : 0 ≤ u := hquarter.trans hu.1
  have hother : B / 4 ≤ B - u := by linarith [hu.2]
  have hmul : (B / 4) * (B / 4) ≤ u * (B - u) :=
    mul_le_mul hu.1 hother hquarter hu0
  have hsq : (1 : ℝ) / 16 ≤ (B / 4) * (B / 4) := by
    nlinarith
  exact hsq.trans hmul

/-- Coefficient bound for the free SOS polynomial in an interval product
certificate. -/
theorem IntervalProductCertificate.sigmaZero_norm_le
    {B : ℝ} (hB : 1 ≤ B) {p : Polynomial ℝ}
    (cert : IntervalProductCertificate B p) :
    embeddedPolynomialCoeffL1Norm cert.sigmaZero ≤
      intervalMarkovCoefficientBound B p *
        3 ^ intervalCertificateDegree p := by
  let D := intervalCertificateDegree p
  let s := cert.sigmaZero.comp (unitToInterval B)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hD : 1 ≤ D := by simp [D, intervalCertificateDegree]
  have hsDegree : s.natDegree ≤ D := by
    calc
      s.natDegree ≤ cert.sigmaZero.natDegree *
          (unitToInterval B).natDegree := Polynomial.natDegree_comp_le
      _ ≤ (p.natDegree + 1) * 1 :=
        Nat.mul_le_mul cert.degreeZero_le (unitToInterval_natDegree_le B)
      _ ≤ D := by simp [D, intervalCertificateDegree]
  have hsBound : ∀ x : ℝ, |x| ≤ 1 →
      |s.eval x| ≤ intervalValueBound B p := by
    intro x hx
    let u := (unitToInterval B).eval x
    have hu : u ∈ Set.Icc (0 : ℝ) B :=
      unitToInterval_eval_mem hBpos.le (abs_le.mp hx)
    have hzero : 0 ≤ cert.sigmaZero.eval u := cert.isSOSZero.eval_nonneg u
    have hproduct : 0 ≤ cert.sigmaProduct.eval u :=
      cert.isSOSProduct.eval_nonneg u
    have hfactor : 0 ≤ u * (B - u) :=
      mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
    have hid := congrArg (fun z : Polynomial ℝ => z.eval u) cert.identity
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hid
    have hzero_le : cert.sigmaZero.eval u ≤ p.eval u := by
      rw [hid]
      exact le_add_of_nonneg_right (mul_nonneg hfactor hproduct)
    dsimp [s]
    rw [Polynomial.eval_comp, abs_of_nonneg hzero]
    exact hzero_le.trans ((le_abs_self _).trans
      (abs_eval_le_intervalValueBound hB p hu))
  have hsDirect : polynomialCoeffL1Norm s ≤
      intervalMarkovCoefficientBound B p := by
    have h := polynomialCoeffL1Norm_le_of_unit_interval_bound
      s D hD hsDegree hsBound
    simpa [intervalMarkovCoefficientBound, D] using h
  have hsEmbedded : embeddedPolynomialCoeffL1Norm s ≤
      intervalMarkovCoefficientBound B p :=
    (embeddedPolynomialCoeffL1Norm_le_polynomialCoeffL1Norm s).trans hsDirect
  have hrecover : s.comp (intervalToUnit B) = cert.sigmaZero := by
    apply Polynomial.funext
    intro u
    dsimp [s]
    simp only [Polynomial.eval_comp]
    rw [affine_interval_inverse_eval hBpos.ne' u]
  have hcomp := embeddedPolynomialCoeffL1Norm_comp_le
    s (intervalToUnit B) (G := 3) (by norm_num)
      (intervalToUnit_embedded_norm_le_three hB)
  rw [hrecover] at hcomp
  calc
    embeddedPolynomialCoeffL1Norm cert.sigmaZero ≤
        embeddedPolynomialCoeffL1Norm s * 3 ^ s.natDegree := hcomp
    _ ≤ intervalMarkovCoefficientBound B p * 3 ^ s.natDegree := by
      exact mul_le_mul_of_nonneg_right hsEmbedded (by positivity)
    _ ≤ intervalMarkovCoefficientBound B p * 3 ^ D := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hsDegree)
        (intervalMarkovCoefficientBound_nonneg hB p)

/-- Coefficient bound for the product SOS polynomial.  Restricting to the
middle half of the interval makes the factor `u(B-u)` uniformly positive. -/
theorem IntervalProductCertificate.sigmaProduct_norm_le
    {B : ℝ} (hB : 1 ≤ B) {p : Polynomial ℝ}
    (cert : IntervalProductCertificate B p) :
    embeddedPolynomialCoeffL1Norm cert.sigmaProduct ≤
      (16 * intervalMarkovCoefficientBound B p) *
        6 ^ intervalCertificateDegree p := by
  let D := intervalCertificateDegree p
  let s := cert.sigmaProduct.comp (middleToInterval B)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hD : 1 ≤ D := by simp [D, intervalCertificateDegree]
  have hsDegree : s.natDegree ≤ D := by
    calc
      s.natDegree ≤ cert.sigmaProduct.natDegree *
          (middleToInterval B).natDegree := Polynomial.natDegree_comp_le
      _ ≤ (p.natDegree + 1) * 1 :=
        Nat.mul_le_mul cert.degreeProduct_le (middleToInterval_natDegree_le B)
      _ ≤ D := by simp [D, intervalCertificateDegree]
  have hsBound : ∀ x : ℝ, |x| ≤ 1 →
      |s.eval x| ≤ 16 * intervalValueBound B p := by
    intro x hx
    let u := (middleToInterval B).eval x
    have huMiddle : u ∈ Set.Icc (B / 4) (3 * B / 4) :=
      middleToInterval_eval_mem hBpos.le hx
    have hu : u ∈ Set.Icc (0 : ℝ) B := by
      constructor <;> linarith [huMiddle.1, huMiddle.2]
    have hzero : 0 ≤ cert.sigmaZero.eval u := cert.isSOSZero.eval_nonneg u
    have hproduct : 0 ≤ cert.sigmaProduct.eval u :=
      cert.isSOSProduct.eval_nonneg u
    have hfactor : (1 : ℝ) / 16 ≤ u * (B - u) :=
      one_sixteenth_le_interval_product hB huMiddle
    have hid := congrArg (fun z : Polynomial ℝ => z.eval u) cert.identity
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hid
    have hterm_le : u * (B - u) * cert.sigmaProduct.eval u ≤ p.eval u := by
      rw [hid]
      exact le_add_of_nonneg_left hzero
    have hscaled : (1 / 16 : ℝ) * cert.sigmaProduct.eval u ≤
        u * (B - u) * cert.sigmaProduct.eval u :=
      mul_le_mul_of_nonneg_right hfactor hproduct
    have hproduct_le : cert.sigmaProduct.eval u ≤ 16 * p.eval u := by
      nlinarith
    dsimp [s]
    rw [Polynomial.eval_comp, abs_of_nonneg hproduct]
    calc
      cert.sigmaProduct.eval u ≤ 16 * p.eval u := hproduct_le
      _ ≤ 16 * |p.eval u| := by gcongr; exact le_abs_self _
      _ ≤ 16 * intervalValueBound B p := by
        gcongr
        exact abs_eval_le_intervalValueBound hB p hu
  have hsDirect : polynomialCoeffL1Norm s ≤
      16 * intervalMarkovCoefficientBound B p := by
    have h := polynomialCoeffL1Norm_le_of_unit_interval_bound
      s D hD hsDegree hsBound
    convert h using 1
    all_goals
      simp [intervalMarkovCoefficientBound, D]
    all_goals ring
  have hsEmbedded : embeddedPolynomialCoeffL1Norm s ≤
      16 * intervalMarkovCoefficientBound B p :=
    (embeddedPolynomialCoeffL1Norm_le_polynomialCoeffL1Norm s).trans hsDirect
  have hrecover : s.comp (intervalToMiddle B) = cert.sigmaProduct := by
    apply Polynomial.funext
    intro u
    dsimp [s]
    simp only [Polynomial.eval_comp]
    rw [middle_affine_inverse_eval hBpos.ne' u]
  have hcomp := embeddedPolynomialCoeffL1Norm_comp_le
    s (intervalToMiddle B) (G := 6) (by norm_num)
      (intervalToMiddle_embedded_norm_le_six hB)
  rw [hrecover] at hcomp
  calc
    embeddedPolynomialCoeffL1Norm cert.sigmaProduct ≤
        embeddedPolynomialCoeffL1Norm s * 6 ^ s.natDegree := hcomp
    _ ≤ (16 * intervalMarkovCoefficientBound B p) * 6 ^ s.natDegree := by
      exact mul_le_mul_of_nonneg_right hsEmbedded (by positivity)
    _ ≤ (16 * intervalMarkovCoefficientBound B p) * 6 ^ D := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num) hsDegree)
        (mul_nonneg (by norm_num) (intervalMarkovCoefficientBound_nonneg hB p))

def intervalLeftFactor (B : ℝ) : Polynomial ℝ :=
  Polynomial.C (Real.sqrt B)⁻¹ * (Polynomial.C B - Polynomial.X)

def intervalRightFactor (B : ℝ) : Polynomial ℝ :=
  Polynomial.C (Real.sqrt B)⁻¹ * Polynomial.X

theorem IntervalProductCertificate.toIntervalCertificate_sigmaZero
    {B : ℝ} (hB : 0 < B) {p : Polynomial ℝ}
    (cert : IntervalProductCertificate B p) :
    (cert.toIntervalCertificate hB).sigmaZero = cert.sigmaZero := rfl

theorem IntervalProductCertificate.toIntervalCertificate_sigmaLeft
    {B : ℝ} (hB : 0 < B) {p : Polynomial ℝ}
    (cert : IntervalProductCertificate B p) :
    (cert.toIntervalCertificate hB).sigmaLeft =
      intervalLeftFactor B ^ 2 * cert.sigmaProduct := rfl

theorem IntervalProductCertificate.toIntervalCertificate_sigmaRight
    {B : ℝ} (hB : 0 < B) {p : Polynomial ℝ}
    (cert : IntervalProductCertificate B p) :
    (cert.toIntervalCertificate hB).sigmaRight =
      intervalRightFactor B ^ 2 * cert.sigmaProduct := rfl

theorem intervalLeftFactor_embedded_norm_le
    {B : ℝ} (hB : 1 ≤ B) :
    embeddedPolynomialCoeffL1Norm (intervalLeftFactor B) ≤ B + 1 := by
  have hsqrt : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
  have hsqrtpos : 0 < Real.sqrt B := zero_lt_one.trans_le hsqrt
  have hinvnonneg : 0 ≤ (Real.sqrt B)⁻¹ := (inv_pos.mpr hsqrtpos).le
  have hinvle : (Real.sqrt B)⁻¹ ≤ 1 :=
    (inv_le_one₀ hsqrtpos).2 hsqrt
  have hlinear : embeddedPolynomialCoeffL1Norm
      (Polynomial.C B - Polynomial.X) ≤ B + 1 := by
    have heq : Polynomial.C B - Polynomial.X =
        Polynomial.C (-1) * Polynomial.X + Polynomial.C B := by
      simp [sub_eq_add_neg, add_comm]
    rw [heq]
    calc
      embeddedPolynomialCoeffL1Norm
          (Polynomial.C (-1) * Polynomial.X + Polynomial.C B) ≤
          |-1| + |B| :=
        embeddedPolynomialCoeffL1Norm_C_mul_X_add_C_le _ _
      _ = B + 1 := by rw [abs_of_nonneg (zero_le_one.trans hB)]; norm_num; ring
  unfold intervalLeftFactor
  calc
    embeddedPolynomialCoeffL1Norm
        (Polynomial.C (Real.sqrt B)⁻¹ *
          (Polynomial.C B - Polynomial.X)) ≤
        embeddedPolynomialCoeffL1Norm (Polynomial.C (Real.sqrt B)⁻¹) *
          embeddedPolynomialCoeffL1Norm (Polynomial.C B - Polynomial.X) :=
      embeddedPolynomialCoeffL1Norm_mul_le _ _
    _ ≤ (Real.sqrt B)⁻¹ * (B + 1) := by
      apply mul_le_mul
      · simpa [abs_of_nonneg hinvnonneg] using
          embeddedPolynomialCoeffL1Norm_C_le (Real.sqrt B)⁻¹
      · exact hlinear
      · exact embeddedPolynomialCoeffL1Norm_nonneg _
      · exact hinvnonneg
    _ ≤ B + 1 := by
      calc
        (Real.sqrt B)⁻¹ * (B + 1) ≤ 1 * (B + 1) := by
          exact mul_le_mul_of_nonneg_right hinvle (by linarith)
        _ = B + 1 := one_mul _

theorem intervalRightFactor_embedded_norm_le_one
    {B : ℝ} (hB : 1 ≤ B) :
    embeddedPolynomialCoeffL1Norm (intervalRightFactor B) ≤ 1 := by
  have hsqrt : 1 ≤ Real.sqrt B := Real.one_le_sqrt.mpr hB
  have hsqrtpos : 0 < Real.sqrt B := zero_lt_one.trans_le hsqrt
  have hinvnonneg : 0 ≤ (Real.sqrt B)⁻¹ := (inv_pos.mpr hsqrtpos).le
  have hinvle : (Real.sqrt B)⁻¹ ≤ 1 :=
    (inv_le_one₀ hsqrtpos).2 hsqrt
  unfold intervalRightFactor
  calc
    embeddedPolynomialCoeffL1Norm
        (Polynomial.C (Real.sqrt B)⁻¹ * Polynomial.X) ≤
        embeddedPolynomialCoeffL1Norm (Polynomial.C (Real.sqrt B)⁻¹) *
          embeddedPolynomialCoeffL1Norm Polynomial.X :=
      embeddedPolynomialCoeffL1Norm_mul_le _ _
    _ ≤ (Real.sqrt B)⁻¹ * 1 := by
      exact mul_le_mul
        (by simpa [abs_of_nonneg hinvnonneg] using
          embeddedPolynomialCoeffL1Norm_C_le (Real.sqrt B)⁻¹)
        embeddedPolynomialCoeffL1Norm_X_le
        (embeddedPolynomialCoeffL1Norm_nonneg _)
        hinvnonneg
    _ ≤ 1 := by simpa using hinvle

def intervalSigmaZeroCoefficientBound (B : ℝ) (p : Polynomial ℝ) : ℝ :=
  intervalMarkovCoefficientBound B p * 3 ^ intervalCertificateDegree p

def intervalSigmaProductCoefficientBound (B : ℝ) (p : Polynomial ℝ) : ℝ :=
  (16 * intervalMarkovCoefficientBound B p) * 6 ^ intervalCertificateDegree p

/-- Explicit total coefficient budget for the ordinary three-term interval
certificate. -/
def intervalCertificateCoefficientBound (B : ℝ) (p : Polynomial ℝ) : ℝ :=
  intervalSigmaZeroCoefficientBound B p +
    ((B + 1) ^ 2 + 1) * intervalSigmaProductCoefficientBound B p

theorem intervalSigmaZeroCoefficientBound_nonneg
    {B : ℝ} (hB : 1 ≤ B) (p : Polynomial ℝ) :
    0 ≤ intervalSigmaZeroCoefficientBound B p := by
  exact mul_nonneg (intervalMarkovCoefficientBound_nonneg hB p) (by positivity)

theorem intervalSigmaProductCoefficientBound_nonneg
    {B : ℝ} (hB : 1 ≤ B) (p : Polynomial ℝ) :
    0 ≤ intervalSigmaProductCoefficientBound B p := by
  exact mul_nonneg
    (mul_nonneg (by norm_num) (intervalMarkovCoefficientBound_nonneg hB p))
    (by positivity)

theorem intervalCertificateCoefficientBound_nonneg
    {B : ℝ} (hB : 1 ≤ B) (p : Polynomial ℝ) :
    0 ≤ intervalCertificateCoefficientBound B p := by
  unfold intervalCertificateCoefficientBound
  exact add_nonneg
    (intervalSigmaZeroCoefficientBound_nonneg hB p)
    (mul_nonneg
      (add_nonneg (sq_nonneg (B + 1)) zero_le_one)
      (intervalSigmaProductCoefficientBound_nonneg hB p))

theorem IntervalProductCertificate.toIntervalCertificate_coeffSize_le
    {B : ℝ} (hB : 1 ≤ B) {p : Polynomial ℝ}
    (cert : IntervalProductCertificate B p) :
    (cert.toIntervalCertificate (zero_lt_one.trans_le hB)).coeffSize ≤
      intervalCertificateCoefficientBound B p := by
  have hzero := cert.sigmaZero_norm_le hB
  have hproduct := cert.sigmaProduct_norm_le hB
  have hleft : embeddedPolynomialCoeffL1Norm
      (intervalLeftFactor B ^ 2 * cert.sigmaProduct) ≤
      (B + 1) ^ 2 * intervalSigmaProductCoefficientBound B p := by
    calc
      embeddedPolynomialCoeffL1Norm
          (intervalLeftFactor B ^ 2 * cert.sigmaProduct) ≤
          embeddedPolynomialCoeffL1Norm (intervalLeftFactor B ^ 2) *
            embeddedPolynomialCoeffL1Norm cert.sigmaProduct :=
        embeddedPolynomialCoeffL1Norm_mul_le _ _
      _ ≤ embeddedPolynomialCoeffL1Norm (intervalLeftFactor B) ^ 2 *
            embeddedPolynomialCoeffL1Norm cert.sigmaProduct := by
        exact mul_le_mul_of_nonneg_right (embeddedPolynomialCoeffL1Norm_pow_le _ _)
          (embeddedPolynomialCoeffL1Norm_nonneg _)
      _ ≤ (B + 1) ^ 2 * intervalSigmaProductCoefficientBound B p := by
        exact mul_le_mul
          (pow_le_pow_left₀ (embeddedPolynomialCoeffL1Norm_nonneg _)
            (intervalLeftFactor_embedded_norm_le hB) 2)
          hproduct
          (embeddedPolynomialCoeffL1Norm_nonneg _)
          (sq_nonneg (B + 1))
  have hright : embeddedPolynomialCoeffL1Norm
      (intervalRightFactor B ^ 2 * cert.sigmaProduct) ≤
      intervalSigmaProductCoefficientBound B p := by
    calc
      embeddedPolynomialCoeffL1Norm
          (intervalRightFactor B ^ 2 * cert.sigmaProduct) ≤
          embeddedPolynomialCoeffL1Norm (intervalRightFactor B ^ 2) *
            embeddedPolynomialCoeffL1Norm cert.sigmaProduct :=
        embeddedPolynomialCoeffL1Norm_mul_le _ _
      _ ≤ embeddedPolynomialCoeffL1Norm (intervalRightFactor B) ^ 2 *
            embeddedPolynomialCoeffL1Norm cert.sigmaProduct := by
        exact mul_le_mul_of_nonneg_right (embeddedPolynomialCoeffL1Norm_pow_le _ _)
          (embeddedPolynomialCoeffL1Norm_nonneg _)
      _ ≤ 1 ^ 2 * intervalSigmaProductCoefficientBound B p := by
        exact mul_le_mul
          (pow_le_pow_left₀ (embeddedPolynomialCoeffL1Norm_nonneg _)
            (intervalRightFactor_embedded_norm_le_one hB) 2)
          hproduct
          (embeddedPolynomialCoeffL1Norm_nonneg _)
          (by norm_num)
      _ = intervalSigmaProductCoefficientBound B p := by ring
  change embeddedPolynomialCoeffL1Norm cert.sigmaZero ≤
      intervalSigmaZeroCoefficientBound B p at hzero
  change embeddedPolynomialCoeffL1Norm cert.sigmaProduct ≤
      intervalSigmaProductCoefficientBound B p at hproduct
  unfold IntervalCertificate.coeffSize
  rw [cert.toIntervalCertificate_sigmaZero,
    cert.toIntervalCertificate_sigmaLeft,
    cert.toIntervalCertificate_sigmaRight]
  unfold intervalCertificateCoefficientBound
  calc
    embeddedPolynomialCoeffL1Norm cert.sigmaZero +
          embeddedPolynomialCoeffL1Norm
            (intervalLeftFactor B ^ 2 * cert.sigmaProduct) +
        embeddedPolynomialCoeffL1Norm
          (intervalRightFactor B ^ 2 * cert.sigmaProduct) ≤
        intervalSigmaZeroCoefficientBound B p +
          (B + 1) ^ 2 * intervalSigmaProductCoefficientBound B p +
            intervalSigmaProductCoefficientBound B p :=
      add_le_add (add_le_add hzero hleft) hright
    _ = intervalSigmaZeroCoefficientBound B p +
        ((B + 1) ^ 2 + 1) * intervalSigmaProductCoefficientBound B p := by ring

/-- Every nonnegative polynomial on `[0,B]`, for `B ≥ 1`, has an ordinary
interval certificate with the displayed explicit coefficient budget. -/
theorem boundedIntervalCertificate_nonempty_explicit
    {B : ℝ} (hB : 1 ≤ B) (p : Polynomial ℝ)
    (hp : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) B → 0 ≤ p.eval u) :
    Nonempty (BoundedIntervalCertificate B p
      (intervalCertificateCoefficientBound B p)) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  obtain ⟨productCert⟩ := intervalProductCertificate_nonempty hBpos p hp
  let cert := productCert.toIntervalCertificate hBpos
  refine ⟨{
    certificate := cert
    size_le := ?_
  }⟩
  dsimp [cert]
  exact productCert.toIntervalCertificate_coeffSize_le hB

end OptimalConvergenceRates.GeneralArchimedean

end
