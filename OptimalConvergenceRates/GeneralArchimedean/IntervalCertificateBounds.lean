/-
  SOS certificates for polynomials nonnegative on a compact interval.
-/
import OptimalConvergenceRates.MarkovLukacz.MarkovLukacz
import OptimalConvergenceRates.MarkovLukacz.UnivariateSOS

import OptimalConvergenceRates.GeneralArchimedean.UnivariateCoefficientNorm
noncomputable section

open Polynomial

namespace OptimalConvergenceRates
namespace GeneralArchimedean

/-- The affine map from [-1,1] to [0,B]. -/
def unitToInterval (B : ℝ) : Polynomial ℝ :=
  Polynomial.C (B / 2) * (Polynomial.X + 1)

/-- The inverse affine map from [0,B] to [-1,1]. -/
def intervalToUnit (B : ℝ) : Polynomial ℝ :=
  Polynomial.C (2 / B) * Polynomial.X - 1

/-- The product form obtained directly from Markov--Lukacs. -/
structure IntervalProductCertificate (B : ℝ) (p : Polynomial ℝ) where
  sigmaZero : Polynomial ℝ
  sigmaProduct : Polynomial ℝ
  isSOSZero : IsSOSUni sigmaZero
  isSOSProduct : IsSOSUni sigmaProduct
  identity :
    p = sigmaZero +
      Polynomial.X * (Polynomial.C B - Polynomial.X) * sigmaProduct
  degreeZero_le : sigmaZero.natDegree ≤ p.natDegree + 1
  degreeProduct_le : sigmaProduct.natDegree ≤ p.natDegree + 1

/-- The ordinary quadratic-module form for the two interval generators. -/
structure IntervalCertificate (B : ℝ) (p : Polynomial ℝ) where
  sigmaZero : Polynomial ℝ
  sigmaLeft : Polynomial ℝ
  sigmaRight : Polynomial ℝ
  isSOSZero : IsSOSUni sigmaZero
  isSOSLeft : IsSOSUni sigmaLeft
  isSOSRight : IsSOSUni sigmaRight
  identity :
    p = sigmaZero + Polynomial.X * sigmaLeft +
      (Polynomial.C B - Polynomial.X) * sigmaRight
  degreeZero_le : sigmaZero.natDegree ≤ p.natDegree + 1
  degreeLeft_le : sigmaLeft.natDegree ≤ p.natDegree + 3
  degreeRight_le : sigmaRight.natDegree ≤ p.natDegree + 3


namespace IntervalCertificate

/-- Total coefficient size of the three SOS polynomials in an interval
certificate. -/
def coeffSize {B : ℝ} {p : Polynomial ℝ}
    (cert : IntervalCertificate B p) : ℝ :=
  embeddedPolynomialCoeffL1Norm cert.sigmaZero +
    embeddedPolynomialCoeffL1Norm cert.sigmaLeft +
      embeddedPolynomialCoeffL1Norm cert.sigmaRight

theorem coeffSize_nonneg {B : ℝ} {p : Polynomial ℝ}
    (cert : IntervalCertificate B p) : 0 ≤ cert.coeffSize := by
  unfold coeffSize
  exact add_nonneg
    (add_nonneg (embeddedPolynomialCoeffL1Norm_nonneg cert.sigmaZero)
      (embeddedPolynomialCoeffL1Norm_nonneg cert.sigmaLeft))
    (embeddedPolynomialCoeffL1Norm_nonneg cert.sigmaRight)

theorem sigmaZero_norm_le_coeffSize {B : ℝ} {p : Polynomial ℝ}
    (cert : IntervalCertificate B p) :
    embeddedPolynomialCoeffL1Norm cert.sigmaZero ≤ cert.coeffSize := by
  unfold coeffSize
  have hleft := embeddedPolynomialCoeffL1Norm_nonneg cert.sigmaLeft
  have hright := embeddedPolynomialCoeffL1Norm_nonneg cert.sigmaRight
  linarith

theorem sigmaLeft_norm_le_coeffSize {B : ℝ} {p : Polynomial ℝ}
    (cert : IntervalCertificate B p) :
    embeddedPolynomialCoeffL1Norm cert.sigmaLeft ≤ cert.coeffSize := by
  unfold coeffSize
  have hzero := embeddedPolynomialCoeffL1Norm_nonneg cert.sigmaZero
  have hright := embeddedPolynomialCoeffL1Norm_nonneg cert.sigmaRight
  linarith

theorem sigmaRight_norm_le_coeffSize {B : ℝ} {p : Polynomial ℝ}
    (cert : IntervalCertificate B p) :
    embeddedPolynomialCoeffL1Norm cert.sigmaRight ≤ cert.coeffSize := by
  unfold coeffSize
  have hzero := embeddedPolynomialCoeffL1Norm_nonneg cert.sigmaZero
  have hleft := embeddedPolynomialCoeffL1Norm_nonneg cert.sigmaLeft
  linarith

end IntervalCertificate

/-- An interval certificate together with an explicit total coefficient-size
bound. -/
structure BoundedIntervalCertificate (B : ℝ) (p : Polynomial ℝ) (H : ℝ) where
  certificate : IntervalCertificate B p
  size_le : certificate.coeffSize ≤ H

namespace BoundedIntervalCertificate

theorem bound_nonneg {B H : ℝ} {p : Polynomial ℝ}
    (cert : BoundedIntervalCertificate B p H) : 0 ≤ H :=
  cert.certificate.coeffSize_nonneg.trans cert.size_le

/-- Every named interval certificate has its actual finite coefficient size
as a valid bound. -/
def ofCertificate {B : ℝ} {p : Polynomial ℝ}
    (cert : IntervalCertificate B p) :
    BoundedIntervalCertificate B p cert.coeffSize where
  certificate := cert
  size_le := le_rfl

/-- Enlarge an interval certificate's coefficient budget. -/
def weakenBound {B H K : ℝ} {p : Polynomial ℝ}
    (cert : BoundedIntervalCertificate B p H) (hHK : H ≤ K) :
    BoundedIntervalCertificate B p K where
  certificate := cert.certificate
  size_le := cert.size_le.trans hHK

end BoundedIntervalCertificate

theorem unitToInterval_natDegree_le (B : ℝ) :
    (unitToInterval B).natDegree ≤ 1 := by
  dsimp [unitToInterval]
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_add_le _ _).trans (by simp))

theorem intervalToUnit_natDegree_le (B : ℝ) :
    (intervalToUnit B).natDegree ≤ 1 := by
  dsimp [intervalToUnit]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  · simp

/-- Squaring after affine substitution and scalar multiplication does not
increase degree. -/
theorem C_mul_comp_affine_sq_natDegree_le
    (c : ℝ) (P t : Polynomial ℝ) (ht : t.natDegree ≤ 1) :
    ((Polynomial.C c * P.comp t) ^ 2).natDegree ≤ (P ^ 2).natDegree := by
  by_cases hP : P = 0
  · subst P
    simp
  have hcomp : (P.comp t).natDegree ≤ P.natDegree := by
    calc
      (P.comp t).natDegree ≤ P.natDegree * t.natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left P.natDegree ht
      _ = P.natDegree := by simp
  have hscaled : (Polynomial.C c * P.comp t).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_C_mul_le _ _).trans hcomp
  calc
    ((Polynomial.C c * P.comp t) ^ 2).natDegree ≤
        2 * (Polynomial.C c * P.comp t).natDegree :=
      Polynomial.natDegree_pow_le
    _ ≤ 2 * P.natDegree := Nat.mul_le_mul_left 2 hscaled
    _ = (P ^ 2).natDegree := by rw [Polynomial.natDegree_pow]

theorem unitToInterval_eval_mem
    {B x : ℝ} (hB : 0 ≤ B) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (unitToInterval B).eval x ∈ Set.Icc (0 : ℝ) B := by
  simp only [unitToInterval, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have hhalf : 0 ≤ B / 2 := div_nonneg hB (by norm_num)
  constructor
  · exact mul_nonneg hhalf (by linarith [hx.1])
  · calc
      B / 2 * (x + 1) ≤ B / 2 * 2 :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2]) hhalf
      _ = B := by ring

theorem affine_interval_inverse_eval
    {B : ℝ} (hB : B ≠ 0) (u : ℝ) :
    (unitToInterval B).eval ((intervalToUnit B).eval u) = u := by
  simp only [unitToInterval, intervalToUnit, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one]
  field_simp
  ring

/-- Qualitative interval product certificate, with an explicit affine
transport of the repository's Markov--Lukacs theorem. -/
theorem intervalProductCertificate_nonempty
    {B : ℝ} (hB : 0 < B) (p : Polynomial ℝ)
    (hp : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) B → 0 ≤ p.eval u) :
    Nonempty (IntervalProductCertificate B p) := by
  let f := unitToInterval B
  let t := intervalToUnit B
  let q := p.comp f
  have hq : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → 0 ≤ q.eval x := by
    intro x hx
    dsimp [q]
    rw [Polynomial.eval_comp]
    exact hp _ (unitToInterval_eval_mem hB.le hx)
  obtain ⟨alpha, beta, hdecomp, halpha, hbeta⟩ :=
    lukacs_decomposition_raw q q.natDegree le_rfl hq
  have hfDegree : f.natDegree ≤ 1 := unitToInterval_natDegree_le B
  have htDegree : t.natDegree ≤ 1 := intervalToUnit_natDegree_le B
  have hqDegree : q.natDegree ≤ p.natDegree := by
    dsimp [q]
    calc
      (p.comp f).natDegree ≤ p.natDegree * f.natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left p.natDegree hfDegree
      _ = p.natDegree := by simp
  have hbetaBase : (beta ^ 2).natDegree ≤ q.natDegree + 1 := by
    by_cases hbeta0 : beta = 0
    · subst beta
      simp
    have hfactor :
        (1 - Polynomial.X ^ 2 : Polynomial ℝ) ≠ 0 := by
      intro hzero
      have heval := congrArg (fun z : Polynomial ℝ => z.eval 0) hzero
      norm_num at heval
    have hbetaSq : beta ^ 2 ≠ 0 := pow_ne_zero _ hbeta0
    calc
      (beta ^ 2).natDegree ≤
          ((1 - Polynomial.X ^ 2) * beta ^ 2).natDegree := by
        rw [Polynomial.natDegree_mul hfactor hbetaSq]
        exact Nat.le_add_left _ _
      _ ≤ q.natDegree + 1 := hbeta
  let beta' := Polynomial.C (2 / B) * beta.comp t
  refine ⟨⟨(alpha.comp t) ^ 2, beta' ^ 2,
    IsSOSUni_sq _, IsSOSUni_sq _, ?_, ?_, ?_⟩⟩
  · apply Polynomial.funext
    intro u
    have hdec := congrArg (fun z : Polynomial ℝ => z.eval (t.eval u)) hdecomp
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X] at hdec
    have hinv : f.eval (t.eval u) = u := by
      exact affine_interval_inverse_eval hB.ne' u
    have ht :
        1 - (t.eval u) ^ 2 =
          u * (B - u) * (2 / B) ^ 2 := by
      dsimp [t, intervalToUnit]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one]
      field_simp
      ring
    dsimp [q] at hdec
    rw [Polynomial.eval_comp, hinv, ht] at hdec
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    dsimp [beta']
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
    rw [hdec]
    ring
  · calc
      ((alpha.comp t) ^ 2).natDegree ≤ (alpha ^ 2).natDegree := by
        simpa using
          C_mul_comp_affine_sq_natDegree_le (1 : ℝ) alpha t htDegree
      _ ≤ q.natDegree + 1 := halpha
      _ ≤ p.natDegree + 1 := Nat.add_le_add_right hqDegree 1
  · dsimp [beta']
    calc
      ((Polynomial.C (2 / B) * beta.comp t) ^ 2).natDegree ≤
          (beta ^ 2).natDegree :=
        C_mul_comp_affine_sq_natDegree_le (2 / B) beta t htDegree
      _ ≤ q.natDegree + 1 := hbetaBase
      _ ≤ p.natDegree + 1 := Nat.add_le_add_right hqDegree 1

/-- Remove the interval product using
u(B-u)=B^{-1}(u(B-u)^2+(B-u)u^2). -/
noncomputable def IntervalProductCertificate.toIntervalCertificate
    {B : ℝ} (hB : 0 < B) {p : Polynomial ℝ}
    (cert : IntervalProductCertificate B p) :
    IntervalCertificate B p := by
  let c : ℝ := (Real.sqrt B)⁻¹
  let leftFactor : Polynomial ℝ :=
    Polynomial.C c * (Polynomial.C B - Polynomial.X)
  let rightFactor : Polynomial ℝ :=
    Polynomial.C c * Polynomial.X
  have hleftFactor : leftFactor.natDegree ≤ 1 := by
    dsimp [leftFactor]
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_sub_le _ _).trans (by simp))
  have hrightFactor : rightFactor.natDegree ≤ 1 := by
    dsimp [rightFactor]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  have hleftDegree :
      (leftFactor ^ 2 * cert.sigmaProduct).natDegree ≤
        p.natDegree + 3 := by
    calc
      (leftFactor ^ 2 * cert.sigmaProduct).natDegree ≤
          (leftFactor ^ 2).natDegree + cert.sigmaProduct.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 2 * leftFactor.natDegree + cert.sigmaProduct.natDegree :=
        Nat.add_le_add_right Polynomial.natDegree_pow_le _
      _ ≤ 2 * 1 + (p.natDegree + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 hleftFactor)
          cert.degreeProduct_le
      _ = p.natDegree + 3 := by omega
  have hrightDegree :
      (rightFactor ^ 2 * cert.sigmaProduct).natDegree ≤
        p.natDegree + 3 := by
    calc
      (rightFactor ^ 2 * cert.sigmaProduct).natDegree ≤
          (rightFactor ^ 2).natDegree + cert.sigmaProduct.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 2 * rightFactor.natDegree + cert.sigmaProduct.natDegree :=
        Nat.add_le_add_right Polynomial.natDegree_pow_le _
      _ ≤ 2 * 1 + (p.natDegree + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 hrightFactor)
          cert.degreeProduct_le
      _ = p.natDegree + 3 := by omega
  refine ⟨cert.sigmaZero,
    leftFactor ^ 2 * cert.sigmaProduct,
    rightFactor ^ 2 * cert.sigmaProduct,
    cert.isSOSZero,
    IsSOSUni_sq_mul cert.isSOSProduct,
    IsSOSUni_sq_mul cert.isSOSProduct, ?_,
    cert.degreeZero_le, hleftDegree, hrightDegree⟩
  calc
    p = cert.sigmaZero +
        Polynomial.X * (Polynomial.C B - Polynomial.X) *
          cert.sigmaProduct := cert.identity
    _ = _ := by
      have hsqrt : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB.le
      have hsqrt_ne : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hB)
      dsimp [leftFactor, rightFactor, c]
      apply Polynomial.funext
      intro u
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      field_simp [hsqrt_ne]
      rw [hsqrt]
      ring

/-- Every polynomial nonnegative on [0,B] has an ordinary interval
quadratic-module certificate. -/
theorem intervalCertificate_nonempty
    {B : ℝ} (hB : 0 < B) (p : Polynomial ℝ)
    (hp : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) B → 0 ≤ p.eval u) :
    Nonempty (IntervalCertificate B p) := by
  obtain ⟨cert⟩ := intervalProductCertificate_nonempty hB p hp
  exact ⟨cert.toIntervalCertificate hB⟩


/-- Qualitative Markov--Lukács supplies a finite coefficient budget.
The explicit refinement is `boundedIntervalCertificate_nonempty_explicit`. -/
theorem boundedIntervalCertificate_exists
    {B : ℝ} (hB : 0 < B) (p : Polynomial ℝ)
    (hp : ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) B → 0 ≤ p.eval u) :
    ∃ H : ℝ, Nonempty (BoundedIntervalCertificate B p H) := by
  obtain ⟨cert⟩ := intervalCertificate_nonempty hB p hp
  exact ⟨cert.coeffSize, ⟨BoundedIntervalCertificate.ofCertificate cert⟩⟩
end GeneralArchimedean
end OptimalConvergenceRates

end
