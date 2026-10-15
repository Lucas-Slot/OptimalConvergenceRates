/-
  OptimalConvergenceRates/ScaledRobinson/HomogenizationCriticalBinary.lean

  Binary real/imaginary parity pieces used in the general critical SOS construction.
-/
import OptimalConvergenceRates.ScaledRobinson.HomogenizationCore

open MvPolynomial Finset


noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- Substitute bivariate polynomials in `R,T` into the critical ternary variables. -/
def criticalRTSubst : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval ![criticalR, criticalT]

/-- The bivariate `R` variable. -/
def criticalRVar : MvPolynomial (Fin 2) ℝ :=
  X 0

/-- The bivariate `T` variable. -/
def criticalTVar : MvPolynomial (Fin 2) ℝ :=
  X 1

theorem criticalRTSubst_R : criticalRTSubst criticalRVar = criticalR := by
  simp [criticalRTSubst, criticalRVar]

theorem criticalRTSubst_T : criticalRTSubst criticalTVar = criticalT := by
  simp [criticalRTSubst, criticalTVar]

/-- A bivariate polynomial is divisible by `R` if its constant coefficient as a
polynomial in `R` vanishes. -/
theorem criticalRVar_dvd_of_coeff_zero (p : MvPolynomial (Fin 2) ℝ)
    (h0 : ((MvPolynomial.finSuccEquiv ℝ 1) p).coeff 0 = 0) :
    criticalRVar ∣ p := by
  have hdiv : Polynomial.X ∣ (MvPolynomial.finSuccEquiv ℝ 1) p := by
    rw [Polynomial.X_dvd_iff]
    exact h0
  rcases hdiv with ⟨q, hq⟩
  refine ⟨(MvPolynomial.finSuccEquiv ℝ 1).symm q, ?_⟩
  apply (MvPolynomial.finSuccEquiv ℝ 1).injective
  rw [map_mul, AlgEquiv.apply_symm_apply, hq]
  simp [criticalRVar, MvPolynomial.finSuccEquiv_X_zero]

/-- A bivariate polynomial is divisible by `R^2` if its constant and linear coefficients
as a polynomial in `R` vanish. -/
theorem criticalRVar_sq_dvd_of_coeff_zero_one (p : MvPolynomial (Fin 2) ℝ)
    (h0 : ((MvPolynomial.finSuccEquiv ℝ 1) p).coeff 0 = 0)
    (h1 : ((MvPolynomial.finSuccEquiv ℝ 1) p).coeff 1 = 0) :
    criticalRVar ^ 2 ∣ p := by
  have hdiv : Polynomial.X ^ 2 ∣ (MvPolynomial.finSuccEquiv ℝ 1) p := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d <;> simp [h0, h1]
  rcases hdiv with ⟨q, hq⟩
  refine ⟨(MvPolynomial.finSuccEquiv ℝ 1).symm q, ?_⟩
  apply (MvPolynomial.finSuccEquiv ℝ 1).injective
  rw [map_mul, AlgEquiv.apply_symm_apply, hq]
  simp [criticalRVar, MvPolynomial.finSuccEquiv_X_zero]

/-- The coefficient ring variable obtained after viewing `ℝ[R,T]` as a polynomial in `R`. -/
def criticalTCoeffVar : MvPolynomial (Fin 1) ℝ :=
  X 0

theorem criticalRPoly_T_coeff_zero :
    ((MvPolynomial.finSuccEquiv ℝ 1) criticalTVar).coeff 0 = criticalTCoeffVar := by
  change ((MvPolynomial.finSuccEquiv ℝ 1) (X (Fin.succ 0))).coeff 0 =
    (X 0 : MvPolynomial (Fin 1) ℝ)
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp

/-- Constants stay constant under the bivariate-as-univariate equivalence. -/
theorem finSuccEquiv_C (c : ℝ) :
    (MvPolynomial.finSuccEquiv ℝ 1) (MvPolynomial.C c : MvPolynomial (Fin 2) ℝ) =
      Polynomial.C (MvPolynomial.C c : MvPolynomial (Fin 1) ℝ) := by
  change (MvPolynomial.finSuccEquiv ℝ 1) (algebraMap ℝ (MvPolynomial (Fin 2) ℝ) c) =
    algebraMap ℝ (Polynomial (MvPolynomial (Fin 1) ℝ)) c
  exact AlgHom.commutes (MvPolynomial.finSuccEquiv ℝ 1).toAlgHom c

/-- Constants stay constant when viewed as polynomials in the leading `R` variable. -/
theorem finSuccEquiv_C_coeff_zero (c : ℝ) :
    ((MvPolynomial.finSuccEquiv ℝ 1)
        (MvPolynomial.C c : MvPolynomial (Fin 2) ℝ)).coeff 0 =
      (MvPolynomial.C c : MvPolynomial (Fin 1) ℝ) := by
  ext mon
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  by_cases hmon : mon = 0
  · subst mon
    simp
  · have hzero : ¬(0 : Fin 1 →₀ ℕ) = mon := by
      intro h
      exact hmon h.symm
    have hcons : ¬(0 : Fin 2 →₀ ℕ) = Finsupp.cons 0 mon := by
      intro h
      apply hmon
      apply Finsupp.ext
      intro i
      have hi := congrArg (fun f : Fin 2 →₀ ℕ => f (Fin.succ i)) h
      simpa using hi.symm
    simp [hzero, hcons]

/-- Coefficient one after multiplying by a linear polynomial in the distinguished `R`
variable. -/
theorem polynomial_coeff_one_linear_mul (a b : MvPolynomial (Fin 1) ℝ)
    (p : Polynomial (MvPolynomial (Fin 1) ℝ)) :
    ((Polynomial.C a * Polynomial.X + Polynomial.C b) * p).coeff 1 =
      a * p.coeff 0 + b * p.coeff 1 := by
  rw [add_mul, Polynomial.coeff_add]
  have hleft : ((Polynomial.C a * Polynomial.X) * p).coeff 1 = a * p.coeff 0 := by
    rw [mul_assoc, Polynomial.coeff_C_mul]
    simp
  have hright : (Polynomial.C b * p).coeff 1 = b * p.coeff 1 := by
    rw [Polynomial.coeff_C_mul]
  rw [hleft, hright]

/-- Coefficient one of `C a * X * p`. -/
theorem polynomial_coeff_one_C_mul_X_mul (a : MvPolynomial (Fin 1) ℝ)
    (p : Polynomial (MvPolynomial (Fin 1) ℝ)) :
    (Polynomial.C a * Polynomial.X * p).coeff 1 = a * p.coeff 0 := by
  rw [mul_assoc]
  simp

/-- Constant coefficient of `C a * X * p`. -/
theorem polynomial_coeff_zero_C_mul_X_mul (a : MvPolynomial (Fin 1) ℝ)
    (p : Polynomial (MvPolynomial (Fin 1) ℝ)) :
    (Polynomial.C a * Polynomial.X * p).coeff 0 = 0 := by
  rw [mul_assoc]
  simp

/-- Coefficient one of `(C b - C a * X) * p`. -/
theorem polynomial_coeff_one_const_sub_C_mul_X_mul (a b : MvPolynomial (Fin 1) ℝ)
    (p : Polynomial (MvPolynomial (Fin 1) ℝ)) :
    ((Polynomial.C b - Polynomial.C a * Polynomial.X) * p).coeff 1 =
      b * p.coeff 1 - a * p.coeff 0 := by
  rw [sub_mul, Polynomial.coeff_sub]
  rw [Polynomial.coeff_C_mul, polynomial_coeff_one_C_mul_X_mul]

/-- Coefficient one of `((C a - 1) * X - C b) * p`. -/
theorem polynomial_coeff_one_C_sub_one_mul_X_sub_const_mul (a b : MvPolynomial (Fin 1) ℝ)
    (p : Polynomial (MvPolynomial (Fin 1) ℝ)) :
    (((Polynomial.C a - 1) * Polynomial.X - Polynomial.C b) * p).coeff 1 =
      (a - 1) * p.coeff 0 - b * p.coeff 1 := by
  rw [sub_mul, Polynomial.coeff_sub]
  have hleft : (((Polynomial.C a - 1) * Polynomial.X) * p).coeff 1 =
      (a - 1) * p.coeff 0 := by
    rw [show (Polynomial.C a - 1 : Polynomial (MvPolynomial (Fin 1) ℝ)) =
        Polynomial.C (a - 1) by
      simp]
    exact polynomial_coeff_one_C_mul_X_mul (a - 1) p
  rw [hleft, Polynomial.coeff_C_mul]

/-- Constant coefficient after multiplying by a linear polynomial in the distinguished `R`
variable. -/
theorem polynomial_coeff_zero_linear_mul (a b : MvPolynomial (Fin 1) ℝ)
    (p : Polynomial (MvPolynomial (Fin 1) ℝ)) :
    ((Polynomial.C a * Polynomial.X + Polynomial.C b) * p).coeff 0 = b * p.coeff 0 := by
  rw [add_mul, Polynomial.coeff_add]
  have hleft : ((Polynomial.C a * Polynomial.X) * p).coeff 0 = 0 := by
    rw [mul_assoc, Polynomial.coeff_C_mul]
    simp
  have hright : (Polynomial.C b * p).coeff 0 = b * p.coeff 0 := by
    rw [Polynomial.coeff_C_mul]
  rw [hleft, hright, zero_add]

/-- Real and `u*z`-imaginary coefficients for `(u + i z)^(2*r)`, written in the
variables `R = u^2` and `T = z^2`.  The pair `(A,B)` represents
`A(R,T) + i*u*z*B(R,T)`. -/
def binaryEvenState {A : Type*} [CommRing A] (R T : A) : ℕ → A × A
  | 0 => (1, 0)
  | r + 1 =>
      let C := (binaryEvenState R T r).1 - T * (binaryEvenState R T r).2
      let D := (binaryEvenState R T r).1 + R * (binaryEvenState R T r).2
      (R * C - T * D, C + D)

/-- Real coefficient of `(u + i z)^(2*r)`. -/
def binaryEvenReal {A : Type*} [CommRing A] (R T : A) (r : ℕ) : A :=
  (binaryEvenState R T r).1

/-- The coefficient of `i*u*z` in `(u + i z)^(2*r)`. -/
def binaryEvenImag {A : Type*} [CommRing A] (R T : A) (r : ℕ) : A :=
  (binaryEvenState R T r).2

/-- The `u`-real coefficient of `(u + i z)^(2*r+1)`. -/
def binaryOddReal {A : Type*} [CommRing A] (R T : A) (r : ℕ) : A :=
  binaryEvenReal R T r - T * binaryEvenImag R T r

/-- The `z`-imaginary coefficient of `(u + i z)^(2*r+1)`. -/
def binaryOddImag {A : Type*} [CommRing A] (R T : A) (r : ℕ) : A :=
  binaryEvenReal R T r + R * binaryEvenImag R T r

/-- The norm identity for the odd parity step follows algebraically from the even one. -/
theorem binaryOdd_norm_identity_of_even {A : Type*} [CommRing A] (R T : A) (r : ℕ)
    (hEven : binaryEvenReal R T r ^ 2 + R * T * binaryEvenImag R T r ^ 2 =
      (R + T) ^ (2 * r)) :
    R * binaryOddReal R T r ^ 2 + T * binaryOddImag R T r ^ 2 =
      (R + T) ^ (2 * r + 1) := by
  unfold binaryOddReal binaryOddImag
  calc
    R * (binaryEvenReal R T r - T * binaryEvenImag R T r) ^ 2 +
          T * (binaryEvenReal R T r + R * binaryEvenImag R T r) ^ 2 =
        (R + T) *
          (binaryEvenReal R T r ^ 2 + R * T * binaryEvenImag R T r ^ 2) := by
          ring
    _ = (R + T) * (R + T) ^ (2 * r) := by rw [hEven]
    _ = (R + T) ^ (2 * r + 1) := by
          rw [pow_succ]
          ring

/-- The norm identity for the next even state follows algebraically from the odd one. -/
theorem binaryEven_succ_norm_identity_of_odd {A : Type*} [CommRing A] (R T : A) (r : ℕ)
    (hOdd : R * binaryOddReal R T r ^ 2 + T * binaryOddImag R T r ^ 2 =
      (R + T) ^ (2 * r + 1)) :
    binaryEvenReal R T (r + 1) ^ 2 + R * T * binaryEvenImag R T (r + 1) ^ 2 =
      (R + T) ^ (2 * (r + 1)) := by
  unfold binaryEvenReal binaryEvenImag binaryEvenState
  dsimp only
  calc
    (R * (binaryOddReal R T r) - T * (binaryOddImag R T r)) ^ 2 +
          R * T * (binaryOddReal R T r + binaryOddImag R T r) ^ 2 =
        (R + T) *
          (R * binaryOddReal R T r ^ 2 + T * binaryOddImag R T r ^ 2) := by
          ring
    _ = (R + T) * (R + T) ^ (2 * r + 1) := by rw [hOdd]
    _ = (R + T) ^ (2 * (r + 1)) := by
          rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega]
          rw [pow_succ]
          ring

/-- Squared norm of the even parity pieces of `(u + i z)^(2*r)`. -/
theorem binaryEven_norm_identity {A : Type*} [CommRing A] (R T : A) (r : ℕ) :
    binaryEvenReal R T r ^ 2 + R * T * binaryEvenImag R T r ^ 2 =
      (R + T) ^ (2 * r) := by
  induction r with
  | zero =>
      unfold binaryEvenReal binaryEvenImag binaryEvenState
      ring
  | succ r ih =>
      exact binaryEven_succ_norm_identity_of_odd R T r
        (binaryOdd_norm_identity_of_even R T r ih)

/-- Squared norm of the odd parity pieces of `(u + i z)^(2*r+1)`. -/
theorem binaryOdd_norm_identity {A : Type*} [CommRing A] (R T : A) (r : ℕ) :
    R * binaryOddReal R T r ^ 2 + T * binaryOddImag R T r ^ 2 =
      (R + T) ^ (2 * r + 1) :=
  binaryOdd_norm_identity_of_even R T r (binaryEven_norm_identity R T r)

/-- Constant term in `R` of the even real binary component. -/
theorem binaryEvenReal_Rcoeff_zero (r : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenReal criticalRVar criticalTVar r)).coeff 0 =
      (-criticalTCoeffVar) ^ r := by
  induction r with
  | zero =>
      simp [binaryEvenReal, binaryEvenState]
  | succ r ih =>
      have hT : ((MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2))).coeff 0 =
          (X 0 : MvPolynomial (Fin 1) ℝ) := by
        change ((MvPolynomial.finSuccEquiv ℝ 1) (X (Fin.succ 0))).coeff 0 =
          (X 0 : MvPolynomial (Fin 1) ℝ)
        rw [MvPolynomial.finSuccEquiv_X_succ]
        simp
      have hA : ((MvPolynomial.finSuccEquiv ℝ 1)
          (binaryEvenState (X 0) (X 1) r).1).coeff 0 =
          (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ r := by
        simpa [binaryEvenReal, criticalRVar, criticalTVar, criticalTCoeffVar] using ih
      simp [binaryEvenReal, binaryEvenState, criticalRVar, criticalTVar,
        MvPolynomial.finSuccEquiv_X_zero, hT, hA, criticalTCoeffVar]
      ring_nf

/-- Constant term in `R` of the even imaginary binary component. -/
theorem binaryEvenImag_Rcoeff_zero (r : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenImag criticalRVar criticalTVar r)).coeff 0 =
      (MvPolynomial.C (2 * (r : ℝ)) : MvPolynomial (Fin 1) ℝ) *
        (-criticalTCoeffVar) ^ (r - 1) := by
  induction r with
  | zero =>
      simp [binaryEvenImag, binaryEvenState]
  | succ r ih =>
      have hT : ((MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2))).coeff 0 =
          (X 0 : MvPolynomial (Fin 1) ℝ) := by
        change ((MvPolynomial.finSuccEquiv ℝ 1) (X (Fin.succ 0))).coeff 0 =
          (X 0 : MvPolynomial (Fin 1) ℝ)
        rw [MvPolynomial.finSuccEquiv_X_succ]
        simp
      have hA := binaryEvenReal_Rcoeff_zero r
      have hA' : ((MvPolynomial.finSuccEquiv ℝ 1)
          (binaryEvenState (X 0) (X 1) r).1).coeff 0 =
          (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ r := by
        simpa [binaryEvenReal, criticalRVar, criticalTVar, criticalTCoeffVar] using hA
      have hB : ((MvPolynomial.finSuccEquiv ℝ 1)
          (binaryEvenState (X 0) (X 1) r).2).coeff 0 =
          (MvPolynomial.C (2 * (r : ℝ)) : MvPolynomial (Fin 1) ℝ) *
            (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (r - 1) := by
        simpa [binaryEvenImag, criticalRVar, criticalTVar, criticalTCoeffVar] using ih
      suffices (-X 0 : MvPolynomial (Fin 1) ℝ) ^ r -
        X 0 * (MvPolynomial.C 2 * (r : MvPolynomial (Fin 1) ℝ) * (-X 0) ^ (r - 1)) +
          (-X 0) ^ r =
      MvPolynomial.C 2 * ((r : MvPolynomial (Fin 1) ℝ) + 1) * (-X 0) ^ r by
        simpa [binaryEvenImag, binaryEvenState, criticalRVar, criticalTVar,
          MvPolynomial.finSuccEquiv_X_zero, hT, hA', hB, criticalTCoeffVar] using this
      by_cases hr : r = 0
      · subst r
        have hC2 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) = 2 :=
          MvPolynomial.C_eq_coe_nat 2
        rw [hC2]
        ring_nf
      · have hpred : r - 1 + 1 = r := by omega
        rw [← hpred]
        rw [pow_succ]
        have hC2 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) = 2 :=
          MvPolynomial.C_eq_coe_nat 2
        rw [hC2]
        have hpow : r - 1 + 1 - 1 = r - 1 := by omega
        rw [hpow]
        ring_nf

theorem binaryOddImag_Rcoeff_zero (r : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddImag criticalRVar criticalTVar r)).coeff 0 =
      (-criticalTCoeffVar) ^ r := by
  unfold binaryOddImag
  have hA := binaryEvenReal_Rcoeff_zero r
  simpa [criticalRVar, criticalTVar, criticalTCoeffVar,
    MvPolynomial.finSuccEquiv_X_zero] using hA

/-- Constant term in `R` of the odd real binary component. -/
theorem binaryOddReal_Rcoeff_zero (r : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddReal criticalRVar criticalTVar r)).coeff 0 =
      (MvPolynomial.C (2 * (r : ℝ) + 1) : MvPolynomial (Fin 1) ℝ) *
        (-criticalTCoeffVar) ^ r := by
  unfold binaryOddReal
  have hA := binaryEvenReal_Rcoeff_zero r
  have hB := binaryEvenImag_Rcoeff_zero r
  have hA' : ((MvPolynomial.finSuccEquiv ℝ 1)
      (binaryEvenReal (X 0) (X 1) r)).coeff 0 =
      (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ r := by
    simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using hA
  have hB' : ((MvPolynomial.finSuccEquiv ℝ 1)
      (binaryEvenImag (X 0) (X 1) r)).coeff 0 =
      (MvPolynomial.C (2 * (r : ℝ)) : MvPolynomial (Fin 1) ℝ) *
        (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (r - 1) := by
    simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using hB
  have hT : ((MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2))).coeff 0 =
      (X 0 : MvPolynomial (Fin 1) ℝ) := by
    change ((MvPolynomial.finSuccEquiv ℝ 1) (X (Fin.succ 0))).coeff 0 =
      (X 0 : MvPolynomial (Fin 1) ℝ)
    rw [MvPolynomial.finSuccEquiv_X_succ]
    simp
  suffices (-X 0 : MvPolynomial (Fin 1) ℝ) ^ r -
      X 0 * (MvPolynomial.C 2 * (r : MvPolynomial (Fin 1) ℝ) * (-X 0) ^ (r - 1)) =
    (MvPolynomial.C 2 * (r : MvPolynomial (Fin 1) ℝ) + 1) * (-X 0) ^ r by
    simpa [criticalRVar, criticalTVar, criticalTCoeffVar, hA', hB', hT] using this
  by_cases hr : r = 0
  · subst r
    ring_nf
  · have hpred : r - 1 + 1 = r := by omega
    rw [← hpred]
    rw [pow_succ]
    have hC2 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) = 2 :=
      MvPolynomial.C_eq_coe_nat 2
    rw [hC2]
    have hpow : r - 1 + 1 - 1 = r - 1 := by omega
    rw [hpow]
    ring_nf

/-- Linear coefficient of the odd imaginary component in terms of the even state. -/
theorem binaryOddImag_Rcoeff_one (r : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddImag criticalRVar criticalTVar r)).coeff 1 =
      ((MvPolynomial.finSuccEquiv ℝ 1)
          (binaryEvenReal criticalRVar criticalTVar r)).coeff 1 +
        ((MvPolynomial.finSuccEquiv ℝ 1)
          (binaryEvenImag criticalRVar criticalTVar r)).coeff 0 := by
  unfold binaryOddImag binaryEvenReal binaryEvenImag
  simp [criticalRVar, criticalTVar,
    MvPolynomial.finSuccEquiv_X_zero]

/-- Linear coefficient of the next even real component in terms of the odd state. -/
theorem binaryEvenReal_succ_Rcoeff_one (r : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenReal criticalRVar criticalTVar (r + 1))).coeff 1 =
      ((MvPolynomial.finSuccEquiv ℝ 1)
          (binaryOddReal criticalRVar criticalTVar r)).coeff 0 -
        criticalTCoeffVar *
          ((MvPolynomial.finSuccEquiv ℝ 1)
            (binaryOddImag criticalRVar criticalTVar r)).coeff 1 := by
  have hTpoly : (MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2)) =
      Polynomial.C criticalTCoeffVar := by
    change (MvPolynomial.finSuccEquiv ℝ 1) (X (Fin.succ 0)) =
      Polynomial.C criticalTCoeffVar
    rw [MvPolynomial.finSuccEquiv_X_succ]
    simp [criticalTCoeffVar]
  unfold binaryEvenReal binaryEvenState binaryOddReal binaryOddImag binaryEvenImag
  simp [criticalRVar, criticalTVar, criticalTCoeffVar, hTpoly,
    Polynomial.coeff_sub,
    MvPolynomial.finSuccEquiv_X_zero]
  simp [binaryEvenReal]

/-- Bivariate version of the axis binary factor component `a`. -/
def criticalBinaryF_aRT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  if m % 2 = 0 then
    let r := m / 2
    MvPolynomial.C (criticalL m) * criticalRVar * binaryEvenImag criticalRVar criticalTVar r -
      binaryEvenReal criticalRVar criticalTVar r
  else
    let r := m / 2
    MvPolynomial.C (criticalL m) * criticalRVar * binaryOddReal criticalRVar criticalTVar r +
      criticalTVar * binaryOddImag criticalRVar criticalTVar r

/-- Bivariate version of the axis binary factor component `b`. -/
def criticalBinaryF_bRT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  if m % 2 = 0 then
    let r := m / 2
    MvPolynomial.C (criticalL m) * binaryEvenReal criticalRVar criticalTVar r +
      criticalTVar * binaryEvenImag criticalRVar criticalTVar r
  else
    let r := m / 2
    MvPolynomial.C (criticalL m) * binaryOddImag criticalRVar criticalTVar r -
      binaryOddReal criticalRVar criticalTVar r

/-- Bivariate version of the diagonal binary factor component `c`. -/
def criticalBinaryG_cRT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  if m % 2 = 0 then
    binaryOddImag criticalRVar criticalTVar (m / 2)
  else
    binaryEvenReal criticalRVar criticalTVar (m / 2 + 1)

/-- Bivariate version of the diagonal binary factor component `d`. -/
def criticalBinaryG_dRT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  if m % 2 = 0 then
    binaryOddReal criticalRVar criticalTVar (m / 2)
  else
    binaryEvenImag criticalRVar criticalTVar (m / 2 + 1)

/-- Common constant term in `R` of the two beta-side binary components. -/
def criticalBDCoeff (m : ℕ) : MvPolynomial (Fin 1) ℝ :=
  MvPolynomial.C ((m : ℝ) + 1) * (-criticalTCoeffVar) ^ (m / 2)

/-- Constant term in `R` of the diagonal beta binary component. -/
theorem criticalBinaryG_dRT_Rcoeff_zero (m : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryG_dRT m)).coeff 0 =
      criticalBDCoeff m := by
  by_cases hm : m % 2 = 0
  · have hD := binaryOddReal_Rcoeff_zero (m / 2)
    unfold criticalBinaryG_dRT criticalBDCoeff
    simp only [hm, ↓reduceIte, Nat.reduceAdd, C_add, map_natCast, C_1]
    rw [hD]
    have hmod := Nat.mod_add_div m 2
    have hmNat : m = 2 * (m / 2) := by omega
    have hreal : (m : ℝ) + 1 = 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
      rw [hmNat]
      norm_num
    rw [← hreal]
    simp
  · have hD := binaryEvenImag_Rcoeff_zero (m / 2 + 1)
    unfold criticalBinaryG_dRT criticalBDCoeff
    simp only [hm, ↓reduceIte, Nat.reduceAdd, C_add, map_natCast, C_1]
    rw [hD]
    have hpow : m / 2 + 1 - 1 = m / 2 := by omega
    rw [hpow]
    have hmod := Nat.mod_add_div m 2
    have hmNat : m = 2 * (m / 2) + 1 := by omega
    have hreal : (m : ℝ) + 1 = 2 * ((m / 2 + 1 : ℕ) : ℝ) := by
      rw [hmNat]
      have hdiv : (2 * (m / 2) + 1) / 2 = m / 2 := by omega
      rw [hdiv]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    rw [← hreal]
    simp

/-- Constant term in `R` of the axis beta binary component. -/
theorem criticalBinaryF_bRT_Rcoeff_zero (m : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryF_bRT m)).coeff 0 =
    criticalBDCoeff m := by
  by_cases hm : m % 2 = 0
  · have hA := binaryEvenReal_Rcoeff_zero (m / 2)
    have hB := binaryEvenImag_Rcoeff_zero (m / 2)
    have hA' : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenReal (X 0) (X 1) (m / 2))).coeff 0 =
        (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using hA
    have hB' : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenImag (X 0) (X 1) (m / 2))).coeff 0 =
        (MvPolynomial.C (2 * ((m / 2 : ℕ) : ℝ)) : MvPolynomial (Fin 1) ℝ) *
          (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2 - 1) := by
      simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using hB
    have hT : ((MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2))).coeff 0 =
        (X 0 : MvPolynomial (Fin 1) ℝ) := by
      change ((MvPolynomial.finSuccEquiv ℝ 1) (X (Fin.succ 0))).coeff 0 =
        (X 0 : MvPolynomial (Fin 1) ℝ)
      rw [MvPolynomial.finSuccEquiv_X_succ]
      simp
    unfold criticalBinaryF_bRT criticalBDCoeff
    suffices ((MvPolynomial.finSuccEquiv ℝ 1) (MvPolynomial.C (criticalL m))).coeff 0 *
          ((MvPolynomial.finSuccEquiv ℝ 1) (binaryEvenReal (X 0) (X 1) (m / 2))).coeff 0 +
        X 0 * ((MvPolynomial.finSuccEquiv ℝ 1) (binaryEvenImag (X 0) (X 1) (m / 2))).coeff 0 =
      ((m : MvPolynomial (Fin 1) ℝ) + 1) * (-X 0) ^ (m / 2) by
      simpa [hm, criticalRVar, criticalTVar, criticalTCoeffVar, hT] using this
    rw [hA', hB']
    rw [finSuccEquiv_C_coeff_zero]
    have hmod := Nat.mod_add_div m 2
    have hmNat : m = 2 * (m / 2) := by omega
    unfold criticalL
    by_cases hr0 : m / 2 = 0
    · have hm0 : m = 0 := by omega
      subst m
      norm_num [MvPolynomial.algebraMap_eq]
    · have hrpred : m / 2 - 1 + 1 = m / 2 := by omega
      have hrpredR : (((m / 2 - 1 : ℕ) : ℝ) + 1) = ((m / 2 : ℕ) : ℝ) := by
        rw [← hrpred]
        norm_num
      rw [← hrpred]
      rw [pow_succ]
      have hpow : m / 2 - 1 + 1 - 1 = m / 2 - 1 := by omega
      rw [hpow]
      have hrm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) := by
        rw [hmNat]
        norm_num
      have hC2 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) = 2 :=
        MvPolynomial.C_eq_coe_nat 2
      simp only [hC2, C_add, C_mul, map_natCast, C_1, Fin.isValue, mul_neg, Nat.cast_add,
        Nat.cast_one]
      have hmn : (m : MvPolynomial (Fin 1) ℝ) =
          2 * ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) := by
        rw [hmNat]
        norm_num
      have hpredPoly :
          ((m / 2 - 1 : ℕ) : MvPolynomial (Fin 1) ℝ) + 1 =
            ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) := by
        rw [← hrpred]
        norm_num
      rw [hmn, hpredPoly]
      ring_nf
  · have hC := binaryOddImag_Rcoeff_zero (m / 2)
    have hD := binaryOddReal_Rcoeff_zero (m / 2)
    have hC' : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddImag (X 0) (X 1) (m / 2))).coeff 0 =
        (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using hC
    have hD' : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddReal (X 0) (X 1) (m / 2))).coeff 0 =
        (MvPolynomial.C (2 * ((m / 2 : ℕ) : ℝ) + 1) : MvPolynomial (Fin 1) ℝ) *
          (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using hD
    unfold criticalBinaryF_bRT criticalBDCoeff
    suffices ((MvPolynomial.finSuccEquiv ℝ 1) (MvPolynomial.C (criticalL m))).coeff 0 *
          ((MvPolynomial.finSuccEquiv ℝ 1) (binaryOddImag (X 0) (X 1) (m / 2))).coeff 0 -
        ((MvPolynomial.finSuccEquiv ℝ 1) (binaryOddReal (X 0) (X 1) (m / 2))).coeff 0 =
      ((m : MvPolynomial (Fin 1) ℝ) + 1) * (-X 0) ^ (m / 2) by
      simpa [hm, criticalRVar, criticalTVar, criticalTCoeffVar] using this
    rw [hC', hD']
    rw [finSuccEquiv_C_coeff_zero]
    have hmod := Nat.mod_add_div m 2
    have hmNat : m = 2 * (m / 2) + 1 := by omega
    unfold criticalL
    have hrm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hmNat
    have hmp1 : (m : ℝ) + 1 = 2 * ((m / 2 : ℕ) : ℝ) + 2 := by
      rw [hrm]
      ring
    have hC2 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) = 2 :=
      MvPolynomial.C_eq_coe_nat 2
    simp only [hC2, C_add, C_mul, map_natCast, C_1, Fin.isValue]
    have hmn : (m : MvPolynomial (Fin 1) ℝ) =
        ((2 * (m / 2) + 1 : ℕ) : MvPolynomial (Fin 1) ℝ) := by
      exact congrArg (fun n : ℕ => (n : MvPolynomial (Fin 1) ℝ)) hmNat
    rw [hmn]
    norm_num
    ring_nf

/-- The axis binary factor `F_m = (L*u - i*z)*(u+i*z)^m`: its real component. -/
def criticalBinaryF_a (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  if _hm : m % 2 = 0 then
    let r := m / 2
    MvPolynomial.C (criticalL m) * criticalR * binaryEvenImag criticalR criticalT r -
      binaryEvenReal criticalR criticalT r
  else
    let r := m / 2
    MvPolynomial.C (criticalL m) * criticalR * binaryOddReal criticalR criticalT r +
      criticalT * binaryOddImag criticalR criticalT r

/-- The axis binary factor `F_m`: its imaginary component. -/
def criticalBinaryF_b (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  if _hm : m % 2 = 0 then
    let r := m / 2
    MvPolynomial.C (criticalL m) * binaryEvenReal criticalR criticalT r +
      criticalT * binaryEvenImag criticalR criticalT r
  else
    let r := m / 2
    MvPolynomial.C (criticalL m) * binaryOddImag criticalR criticalT r -
      binaryOddReal criticalR criticalT r

/-- The diagonal binary factor `G_m = (u+i*z)^(m+1)`: its `c` component. -/
def criticalBinaryG_c (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  if _hm : m % 2 = 0 then
    binaryOddImag criticalR criticalT (m / 2)
  else
    binaryEvenReal criticalR criticalT (m / 2 + 1)

/-- The diagonal binary factor `G_m = (u+i*z)^(m+1)`: its `d` component. -/
def criticalBinaryG_d (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  if _hm : m % 2 = 0 then
    binaryOddReal criticalR criticalT (m / 2)
  else
    binaryEvenImag criticalR criticalT (m / 2 + 1)

theorem criticalRTSubst_binaryEvenState (r : ℕ) :
    (criticalRTSubst (binaryEvenState criticalRVar criticalTVar r).1,
        criticalRTSubst (binaryEvenState criticalRVar criticalTVar r).2) =
      binaryEvenState criticalR criticalT r := by
  induction r with
  | zero =>
      simp [binaryEvenState]
  | succ r ih =>
      unfold binaryEvenState
      dsimp only
      rw [← ih]
      simp [criticalRTSubst_R, criticalRTSubst_T]

theorem criticalRTSubst_binaryEvenReal (r : ℕ) :
    criticalRTSubst (binaryEvenReal criticalRVar criticalTVar r) =
      binaryEvenReal criticalR criticalT r := by
  simpa [binaryEvenReal] using congrArg Prod.fst (criticalRTSubst_binaryEvenState r)

theorem criticalRTSubst_binaryEvenImag (r : ℕ) :
    criticalRTSubst (binaryEvenImag criticalRVar criticalTVar r) =
      binaryEvenImag criticalR criticalT r := by
  simpa [binaryEvenImag] using congrArg Prod.snd (criticalRTSubst_binaryEvenState r)

theorem criticalRTSubst_binaryOddReal (r : ℕ) :
    criticalRTSubst (binaryOddReal criticalRVar criticalTVar r) =
      binaryOddReal criticalR criticalT r := by
  simp [binaryOddReal, criticalRTSubst_binaryEvenReal, criticalRTSubst_binaryEvenImag,
    criticalRTSubst_T]

theorem criticalRTSubst_binaryOddImag (r : ℕ) :
    criticalRTSubst (binaryOddImag criticalRVar criticalTVar r) =
      binaryOddImag criticalR criticalT r := by
  simp [binaryOddImag, criticalRTSubst_binaryEvenReal, criticalRTSubst_binaryEvenImag,
    criticalRTSubst_R]

theorem criticalRTSubst_binaryF_aRT (m : ℕ) :
    criticalRTSubst (criticalBinaryF_aRT m) = criticalBinaryF_a m := by
  by_cases hm : m % 2 = 0
  · simp [criticalBinaryF_aRT, criticalBinaryF_a, hm, criticalRTSubst_R,
      criticalRTSubst_binaryEvenReal, criticalRTSubst_binaryEvenImag]
  · simp [criticalBinaryF_aRT, criticalBinaryF_a, hm, criticalRTSubst_R,
      criticalRTSubst_T, criticalRTSubst_binaryOddReal, criticalRTSubst_binaryOddImag]

theorem criticalRTSubst_binaryF_bRT (m : ℕ) :
    criticalRTSubst (criticalBinaryF_bRT m) = criticalBinaryF_b m := by
  by_cases hm : m % 2 = 0
  · simp [criticalBinaryF_bRT, criticalBinaryF_b, hm, criticalRTSubst_T,
      criticalRTSubst_binaryEvenReal, criticalRTSubst_binaryEvenImag]
  · simp [criticalBinaryF_bRT, criticalBinaryF_b, hm, criticalRTSubst_binaryOddReal,
      criticalRTSubst_binaryOddImag]

theorem criticalRTSubst_binaryG_cRT (m : ℕ) :
    criticalRTSubst (criticalBinaryG_cRT m) = criticalBinaryG_c m := by
  by_cases hm : m % 2 = 0
  · simp [criticalBinaryG_cRT, criticalBinaryG_c, hm, criticalRTSubst_binaryOddImag]
  · simp [criticalBinaryG_cRT, criticalBinaryG_c, hm, criticalRTSubst_binaryEvenReal]

theorem criticalRTSubst_binaryG_dRT (m : ℕ) :
    criticalRTSubst (criticalBinaryG_dRT m) = criticalBinaryG_d m := by
  by_cases hm : m % 2 = 0
  · simp [criticalBinaryG_dRT, criticalBinaryG_d, hm, criticalRTSubst_binaryOddReal]
  · simp [criticalBinaryG_dRT, criticalBinaryG_d, hm, criticalRTSubst_binaryEvenImag]

/-- The two-square norm identity for the diagonal binary factor `G_m`. -/
theorem criticalBinaryG_norm_identity (m : ℕ) :
    criticalT ^ criticalEta m * criticalBinaryG_c m ^ 2 +
        criticalR * criticalT ^ criticalDelta m * criticalBinaryG_d m ^ 2 =
      (criticalR + criticalT) ^ (m + 1) := by
  by_cases hm : m % 2 = 0
  · have hmEta : criticalEta m = 1 := criticalEta_eq_one_of_even hm
    have hmDelta : criticalDelta m = 0 := criticalDelta_eq_zero_of_even hm
    have hcast : 2 * (m / 2) + 1 = m + 1 := by
      have hmod := Nat.mod_add_div m 2
      omega
    unfold criticalBinaryG_c criticalBinaryG_d
    simp only [dite_eq_ite, hm, reduceIte, hmEta, hmDelta, pow_one, pow_zero, mul_one]
    rw [← hcast]
    rw [add_comm]
    exact binaryOdd_norm_identity criticalR criticalT (m / 2)
  · have hmEta : criticalEta m = 0 := criticalEta_eq_zero_of_odd hm
    have hmDelta : criticalDelta m = 1 := criticalDelta_eq_one_of_odd hm
    have hcast : 2 * (m / 2 + 1) = m + 1 := by
      have hmod := Nat.mod_add_div m 2
      omega
    unfold criticalBinaryG_c criticalBinaryG_d
    simp only [dite_eq_ite, hm, reduceIte, hmEta, hmDelta, pow_one, pow_zero, one_mul]
    rw [← hcast]
    exact binaryEven_norm_identity criticalR criticalT (m / 2 + 1)


/-- The two-square norm identity for the axis binary factor `F_m`. -/
theorem criticalBinaryF_norm_identity (m : ℕ) :
    criticalT ^ criticalEta m * criticalBinaryF_a m ^ 2 +
        criticalR * criticalT ^ criticalDelta m * criticalBinaryF_b m ^ 2 =
      (criticalR + criticalT) ^ m *
        ((MvPolynomial.C (criticalL m) : MvPolynomial (Fin 3) ℝ) ^ 2 * criticalR +
              criticalT) := by
  by_cases hm : m % 2 = 0
  · have hmEta : criticalEta m = 1 := criticalEta_eq_one_of_even hm
    have hmDelta : criticalDelta m = 0 := criticalDelta_eq_zero_of_even hm
    have hcast : 2 * (m / 2) = m := by
      have hmod := Nat.mod_add_div m 2
      omega
    unfold criticalBinaryF_a criticalBinaryF_b
    simp only [dite_eq_ite, hm, reduceIte, hmEta, hmDelta, pow_one, pow_zero, mul_one]
    have hEven := binaryEven_norm_identity criticalR criticalT (m / 2)
    calc
      criticalT *
            (MvPolynomial.C (criticalL m) * criticalR *
                  binaryEvenImag criticalR criticalT (m / 2) -
                binaryEvenReal criticalR criticalT (m / 2)) ^ 2 +
          criticalR *
            (MvPolynomial.C (criticalL m) * binaryEvenReal criticalR criticalT (m / 2) +
                criticalT * binaryEvenImag criticalR criticalT (m / 2)) ^ 2 =
          (binaryEvenReal criticalR criticalT (m / 2) ^ 2 +
              criticalR * criticalT * binaryEvenImag criticalR criticalT (m / 2) ^ 2) *
            ((MvPolynomial.C (criticalL m) : MvPolynomial (Fin 3) ℝ) ^ 2 * criticalR +
              criticalT) := by
            ring
      _ = (criticalR + criticalT) ^ m *
            ((MvPolynomial.C (criticalL m) : MvPolynomial (Fin 3) ℝ) ^ 2 * criticalR +
              criticalT) := by
            rw [hEven, hcast]
  · have hmEta : criticalEta m = 0 := criticalEta_eq_zero_of_odd hm
    have hmDelta : criticalDelta m = 1 := criticalDelta_eq_one_of_odd hm
    have hcast : 2 * (m / 2) + 1 = m := by
      have hmod := Nat.mod_add_div m 2
      omega
    unfold criticalBinaryF_a criticalBinaryF_b
    simp only [dite_eq_ite, hm, reduceIte, hmEta, hmDelta, pow_one, pow_zero, one_mul]
    have hOdd := binaryOdd_norm_identity criticalR criticalT (m / 2)
    calc
      (MvPolynomial.C (criticalL m) * criticalR * binaryOddReal criticalR criticalT (m / 2) +
              criticalT * binaryOddImag criticalR criticalT (m / 2)) ^ 2 +
          criticalR * criticalT *
            (MvPolynomial.C (criticalL m) * binaryOddImag criticalR criticalT (m / 2) -
                binaryOddReal criticalR criticalT (m / 2)) ^ 2 =
          (criticalR * binaryOddReal criticalR criticalT (m / 2) ^ 2 +
              criticalT * binaryOddImag criticalR criticalT (m / 2) ^ 2) *
            ((MvPolynomial.C (criticalL m) : MvPolynomial (Fin 3) ℝ) ^ 2 * criticalR +
              criticalT) := by
            ring
      _ = (criticalR + criticalT) ^ m *
            ((MvPolynomial.C (criticalL m) : MvPolynomial (Fin 3) ℝ) ^ 2 * criticalR +
              criticalT) := by
            rw [hOdd, hcast]

/-- Bivariate axis endpoint linear factor `ell_0 = (lambda_m - 1) R - T`. -/
def criticalEll0RT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (criticalLambda m - 1) * criticalRVar - criticalTVar

/-- Bivariate diagonal endpoint linear factor `ell_1 = ((lambda_m - 2)/2) R - T`. -/
def criticalEll1RT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C ((criticalLambda m - 2) / 2) * criticalRVar - criticalTVar

/-- Bivariate critical interpolation `alpha_0`. -/
def criticalAlpha0RT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  criticalEll0RT m * criticalBinaryF_aRT m

/-- Bivariate critical interpolation `beta_0`. -/
def criticalBeta0RT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  criticalEll0RT m * criticalBinaryF_bRT m

/-- Bivariate critical interpolation `alpha_1`. -/
def criticalAlpha1RT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  -criticalEll1RT m * criticalBinaryG_cRT m

/-- Bivariate critical interpolation `beta_1`. -/
def criticalBeta1RT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  criticalEll1RT m * criticalBinaryG_dRT m

/-- The two alpha endpoints agree modulo `R` at constant coefficient. -/
theorem criticalAlpha_diff_Rcoeff_zero (m : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1) (criticalAlpha1RT m - criticalAlpha0RT m)).coeff 0 = 0 := by
  have hT : ((MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2))).coeff 0 =
      criticalTCoeffVar := by
    simpa [criticalTVar] using criticalRPoly_T_coeff_zero
  by_cases hm : m % 2 = 0
  · have hC : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddImag (X 0) (X 1) (m / 2))).coeff 0 =
        (-criticalTCoeffVar) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar] using binaryOddImag_Rcoeff_zero (m / 2)
    have hA : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenReal (X 0) (X 1) (m / 2))).coeff 0 =
        (-criticalTCoeffVar) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar] using binaryEvenReal_Rcoeff_zero (m / 2)
    unfold criticalAlpha1RT criticalAlpha0RT criticalEll1RT criticalEll0RT criticalBinaryG_cRT
      criticalBinaryF_aRT
    simp [hm, criticalRVar, criticalTVar, criticalTCoeffVar, MvPolynomial.finSuccEquiv_X_zero,
      hT, hC, hA]
  · have hC : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenReal (X 0) (X 1) (m / 2 + 1))).coeff 0 =
        (-criticalTCoeffVar) ^ (m / 2 + 1) := by
      simpa [criticalRVar, criticalTVar] using binaryEvenReal_Rcoeff_zero (m / 2 + 1)
    have hA : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddImag (X 0) (X 1) (m / 2))).coeff 0 =
        (-criticalTCoeffVar) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar] using binaryOddImag_Rcoeff_zero (m / 2)
    unfold criticalAlpha1RT criticalAlpha0RT criticalEll1RT criticalEll0RT criticalBinaryG_cRT
      criticalBinaryF_aRT
    suffices X 0 * (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2 + 1) +
        X 0 * (X 0 * (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2)) = 0 by
      simpa [hm, criticalRVar, criticalTVar, criticalTCoeffVar,
        MvPolynomial.finSuccEquiv_X_zero, hT, hC, hA] using this
    rw [show (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2 + 1) =
        (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2) * (-(X 0)) by
      rw [pow_succ]]
    ring

/-- The two alpha-side binary components have opposite constant terms. -/
theorem criticalBinaryG_cRT_Rcoeff_zero_eq_neg_F_aRT (m : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryG_cRT m)).coeff 0 =
      -((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryF_aRT m)).coeff 0 := by
  have hT : ((MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2))).coeff 0 =
      criticalTCoeffVar := by
    simpa [criticalTVar] using criticalRPoly_T_coeff_zero
  by_cases hm : m % 2 = 0
  · have hC : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddImag (X 0) (X 1) (m / 2))).coeff 0 =
        (-criticalTCoeffVar) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar] using binaryOddImag_Rcoeff_zero (m / 2)
    have hA : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenReal (X 0) (X 1) (m / 2))).coeff 0 =
        (-criticalTCoeffVar) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar] using binaryEvenReal_Rcoeff_zero (m / 2)
    unfold criticalBinaryG_cRT criticalBinaryF_aRT
    simp [hm, criticalRVar, criticalTVar, MvPolynomial.finSuccEquiv_X_zero, hC, hA]
  · have hC : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenReal (X 0) (X 1) (m / 2 + 1))).coeff 0 =
        (-criticalTCoeffVar) ^ (m / 2 + 1) := by
      simpa [criticalRVar, criticalTVar] using binaryEvenReal_Rcoeff_zero (m / 2 + 1)
    have hA : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddImag (X 0) (X 1) (m / 2))).coeff 0 =
        (-criticalTCoeffVar) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar] using binaryOddImag_Rcoeff_zero (m / 2)
    unfold criticalBinaryG_cRT criticalBinaryF_aRT
    suffices (-criticalTCoeffVar) ^ (m / 2 + 1) =
        -(criticalTCoeffVar * (-criticalTCoeffVar) ^ (m / 2)) by
      simpa [hm, criticalRVar, criticalTVar, MvPolynomial.finSuccEquiv_X_zero, hT, hC,
        hA] using this
    rw [show (-criticalTCoeffVar) ^ (m / 2 + 1) =
        (-criticalTCoeffVar) ^ (m / 2) * (-criticalTCoeffVar) by
      rw [pow_succ]]
    ring

/-- The alpha-side derivative jet from the critical binary construction. -/
theorem criticalBinary_ac_Rcoeff_one_jet (m : ℕ) :
    criticalTCoeffVar *
        (((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryF_aRT m)).coeff 1 +
          ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryG_cRT m)).coeff 1) =
      MvPolynomial.C (criticalLambda m / 2) *
        ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryF_aRT m)).coeff 0 := by
  have hT0 : ((MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2))).coeff 0 =
      criticalTCoeffVar := by
    simpa [criticalTVar] using criticalRPoly_T_coeff_zero
  have hTpoly : (MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2)) =
      Polynomial.C criticalTCoeffVar := by
    change (MvPolynomial.finSuccEquiv ℝ 1) (X (Fin.succ 0)) =
      Polynomial.C criticalTCoeffVar
    rw [MvPolynomial.finSuccEquiv_X_succ]
    simp [criticalTCoeffVar]
  by_cases hm : m % 2 = 0
  · have hB0 : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenImag (X 0) (X 1) (m / 2))).coeff 0 =
        (MvPolynomial.C (2 * ((m / 2 : ℕ) : ℝ)) : MvPolynomial (Fin 1) ℝ) *
          (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2 - 1) := by
      simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using
        binaryEvenImag_Rcoeff_zero (m / 2)
    have hA0 : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenReal (X 0) (X 1) (m / 2))).coeff 0 =
        (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using
        binaryEvenReal_Rcoeff_zero (m / 2)
    have hOdd1 : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddImag (X 0) (X 1) (m / 2))).coeff 1 =
        ((MvPolynomial.finSuccEquiv ℝ 1)
            (binaryEvenReal (X 0) (X 1) (m / 2))).coeff 1 +
          ((MvPolynomial.finSuccEquiv ℝ 1)
            (binaryEvenImag (X 0) (X 1) (m / 2))).coeff 0 := by
      simpa [criticalRVar, criticalTVar] using binaryOddImag_Rcoeff_one (m / 2)
    unfold criticalBinaryF_aRT criticalBinaryG_cRT
    suffices X 0 *
        ((MvPolynomial.C (criticalL m) : MvPolynomial (Fin 1) ℝ) *
            ((MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) *
              ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) *
              (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2 - 1)) -
          ((MvPolynomial.finSuccEquiv ℝ 1) (binaryEvenReal (X 0) (X 1) (m / 2))).coeff 1 +
          (((MvPolynomial.finSuccEquiv ℝ 1) (binaryEvenReal (X 0) (X 1) (m / 2))).coeff 1 +
            (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) *
            ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) *
              (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2 - 1))) =
        -((MvPolynomial.C (criticalLambda m / 2) : MvPolynomial (Fin 1) ℝ) *
          (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2)) by
      simpa [hm, criticalRVar, criticalTVar, criticalTCoeffVar, finSuccEquiv_C,
        MvPolynomial.finSuccEquiv_X_zero, Polynomial.coeff_sub,
        polynomial_coeff_one_C_mul_X_mul, hOdd1, hB0, hA0] using this
    have hmNat : m = 2 * (m / 2) := by
      have hmod := Nat.mod_add_div m 2
      omega
    by_cases hr0 : m / 2 = 0
    · have hm0 : m = 0 := by omega
      subst m
      norm_num [criticalLambda, criticalL]
    · have hrpred : m / 2 - 1 + 1 = m / 2 := by omega
      have hrpredPoly : ((m / 2 - 1 : ℕ) : MvPolynomial (Fin 1) ℝ) + 1 =
          ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) := by
        rw [← hrpred]
        norm_num
      rw [← hrpred]
      rw [pow_succ]
      have hC2 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) = 2 :=
        MvPolynomial.C_eq_coe_nat 2
      rw [hC2]
      unfold criticalLambda criticalL
      have hmnR : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) := by
        rw [hmNat]
        norm_num
      simp only [hmnR, hC2, hrpredPoly, Fin.isValue, C_add, C_mul, map_natCast, C_1,
        Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, Nat.reduceAdd, mul_neg, neg_neg]
      rw [show (MvPolynomial.C
          (4 * (2 * ((m / 2 : ℕ) : ℝ)) * (2 * ((m / 2 : ℕ) : ℝ) + 1) / 2) :
            MvPolynomial (Fin 1) ℝ) =
          (((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) * 4 +
            ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) ^ 2 * 8) by
        rw [show
          4 * (2 * ((m / 2 : ℕ) : ℝ)) * (2 * ((m / 2 : ℕ) : ℝ) + 1) / 2 =
            ((m / 2 : ℕ) : ℝ) * 4 + ((m / 2 : ℕ) : ℝ) ^ 2 * 8 by
          ring_nf]
        norm_cast]
      ring_nf
  · have hD0 : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddReal (X 0) (X 1) (m / 2))).coeff 0 =
        (MvPolynomial.C (2 * ((m / 2 : ℕ) : ℝ) + 1) : MvPolynomial (Fin 1) ℝ) *
          (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using
        binaryOddReal_Rcoeff_zero (m / 2)
    have hC0 : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryOddImag (X 0) (X 1) (m / 2))).coeff 0 =
        (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2) := by
      simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using
        binaryOddImag_Rcoeff_zero (m / 2)
    have hSucc1 : ((MvPolynomial.finSuccEquiv ℝ 1)
        (binaryEvenReal (X 0) (X 1) (m / 2 + 1))).coeff 1 =
        ((MvPolynomial.finSuccEquiv ℝ 1)
            (binaryOddReal (X 0) (X 1) (m / 2))).coeff 0 -
          (X 0 : MvPolynomial (Fin 1) ℝ) *
            ((MvPolynomial.finSuccEquiv ℝ 1)
              (binaryOddImag (X 0) (X 1) (m / 2))).coeff 1 := by
      simpa [criticalRVar, criticalTVar, criticalTCoeffVar] using
        binaryEvenReal_succ_Rcoeff_one (m / 2)
    unfold criticalBinaryF_aRT criticalBinaryG_cRT
    suffices X 0 *
        ((MvPolynomial.C (criticalL m) : MvPolynomial (Fin 1) ℝ) *
            (((MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) *
                ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) + 1) *
              (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2)) +
          (((MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) *
                ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) + 1) *
            (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2))) =
        (MvPolynomial.C (criticalLambda m / 2) : MvPolynomial (Fin 1) ℝ) *
          (X 0 * (-(X 0 : MvPolynomial (Fin 1) ℝ)) ^ (m / 2)) by
      simpa [hm, criticalRVar, criticalTVar, criticalTCoeffVar, finSuccEquiv_C, hTpoly,
        MvPolynomial.finSuccEquiv_X_zero, Polynomial.coeff_add,
        polynomial_coeff_one_C_mul_X_mul, hSucc1, hD0, hC0] using this
    have hmNat : m = 2 * (m / 2) + 1 := by
      have hmod := Nat.mod_add_div m 2
      omega
    unfold criticalLambda criticalL
    have hmnR : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hmNat
    have hC2 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 1) ℝ) = 2 :=
      MvPolynomial.C_eq_coe_nat 2
    simp only [hmnR, hC2, Fin.isValue, C_add, C_mul, map_natCast, C_1]
    rw [show (MvPolynomial.C
        (4 * (2 * ((m / 2 : ℕ) : ℝ) + 1) * (2 * ((m / 2 : ℕ) : ℝ) + 1 + 1) / 2) :
          MvPolynomial (Fin 1) ℝ) =
        (4 + ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) * 12 +
          ((m / 2 : ℕ) : MvPolynomial (Fin 1) ℝ) ^ 2 * 8) by
      rw [show
        4 * (2 * ((m / 2 : ℕ) : ℝ) + 1) * (2 * ((m / 2 : ℕ) : ℝ) + 1 + 1) / 2 =
          4 + ((m / 2 : ℕ) : ℝ) * 12 + ((m / 2 : ℕ) : ℝ) ^ 2 * 8 by
        ring_nf]
      norm_cast]
    ring_nf

/-- The two alpha endpoints agree to first order in `R`. -/
theorem criticalAlpha_diff_Rcoeff_one (m : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1) (criticalAlpha1RT m - criticalAlpha0RT m)).coeff 1 = 0 := by
  have hconst := criticalBinaryG_cRT_Rcoeff_zero_eq_neg_F_aRT m
  have hjet := criticalBinary_ac_Rcoeff_one_jet m
  have hTpoly : (MvPolynomial.finSuccEquiv ℝ 1) (X (1 : Fin 2)) =
      Polynomial.C criticalTCoeffVar := by
    change (MvPolynomial.finSuccEquiv ℝ 1) (X (Fin.succ 0)) =
      Polynomial.C criticalTCoeffVar
    rw [MvPolynomial.finSuccEquiv_X_succ]
    simp [criticalTCoeffVar]
  unfold criticalAlpha1RT criticalAlpha0RT criticalEll1RT criticalEll0RT
  have hjet' : X 0 *
      (((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryF_aRT m)).coeff 1 +
        ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryG_cRT m)).coeff 1) =
    MvPolynomial.C (criticalLambda m / 2) *
      ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryF_aRT m)).coeff 0 := by
    simpa [criticalTCoeffVar] using hjet
  suffices X 0 * ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryG_cRT m)).coeff 1 -
          MvPolynomial.C ((criticalLambda m - 2) / 2) *
            ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryG_cRT m)).coeff 0 -
        ((MvPolynomial.C (criticalLambda m) - 1) *
            ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryF_aRT m)).coeff 0 -
          X 0 * ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryF_aRT m)).coeff 1) =
      0 by
    simpa [criticalRVar, criticalTVar, criticalTCoeffVar, hTpoly, finSuccEquiv_C,
      MvPolynomial.finSuccEquiv_X_zero, polynomial_coeff_one_const_sub_C_mul_X_mul,
      polynomial_coeff_one_C_sub_one_mul_X_sub_const_mul, Polynomial.coeff_sub] using this
  rw [hconst]
  ring_nf at hjet' ⊢
  rw [hjet']
  simp only [one_div, C_mul, C_add, C_neg, C_1]
  set A : MvPolynomial (Fin 1) ℝ :=
    ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBinaryF_aRT m)).coeff 0
  set L : MvPolynomial (Fin 1) ℝ := MvPolynomial.C (criticalLambda m)
  have htwohalf : (2 : MvPolynomial (Fin 1) ℝ) * MvPolynomial.C (2⁻¹ : ℝ) = 1 := by
    change MvPolynomial.C (2 : ℝ) *
        (MvPolynomial.C (2⁻¹ : ℝ) : MvPolynomial (Fin 1) ℝ) = MvPolynomial.C (1 : ℝ)
    rw [← map_mul]
    norm_num
  change L * MvPolynomial.C (2⁻¹ : ℝ) * A + A +
      A * (-1 + L * MvPolynomial.C (2⁻¹ : ℝ)) - A * L = 0
  calc
    L * MvPolynomial.C (2⁻¹ : ℝ) * A + A +
        A * (-1 + L * MvPolynomial.C (2⁻¹ : ℝ)) - A * L =
        A * L * ((2 : MvPolynomial (Fin 1) ℝ) * MvPolynomial.C (2⁻¹ : ℝ) - 1) := by
          ring
    _ = 0 := by
      rw [htwohalf]
      ring

/-- The two alpha endpoints agree modulo `R^2`. -/
theorem criticalAlpha_diff_dvd_R_sq (m : ℕ) :
    criticalRVar ^ 2 ∣ criticalAlpha1RT m - criticalAlpha0RT m :=
  criticalRVar_sq_dvd_of_coeff_zero_one _
    (criticalAlpha_diff_Rcoeff_zero m) (criticalAlpha_diff_Rcoeff_one m)

/-- The bivariate quotient `Q` with `alpha_1 - alpha_0 = R^2 * Q`. -/
noncomputable def criticalQRT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  Classical.choose (criticalAlpha_diff_dvd_R_sq m)

/-- The alpha interpolation endpoint difference, written using the quotient `Q`. -/
theorem criticalAlpha1RT_eq_alpha0RT_add_R_sq_mul_Q (m : ℕ) :
    criticalAlpha1RT m = criticalAlpha0RT m + criticalRVar ^ 2 * criticalQRT m := by
  have h := Classical.choose_spec (criticalAlpha_diff_dvd_R_sq m)
  rw [show criticalAlpha1RT m =
      criticalAlpha0RT m + (criticalAlpha1RT m - criticalAlpha0RT m) by ring]
  rw [h]
  rfl

/-- The two beta endpoints agree modulo `R`. -/
theorem criticalBeta_diff_Rcoeff_zero (m : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ 1) (criticalBeta1RT m - criticalBeta0RT m)).coeff 0 = 0 := by
  have hB := criticalBinaryF_bRT_Rcoeff_zero m
  have hD := criticalBinaryG_dRT_Rcoeff_zero m
  unfold criticalBeta1RT criticalBeta0RT criticalEll1RT criticalEll0RT
  simp [criticalRVar, criticalTVar, MvPolynomial.finSuccEquiv_X_zero, hB, hD]

/-- The first critical interpolation quotient exists: `beta_1 - beta_0` is divisible by `R`. -/
theorem criticalBeta_diff_dvd_R (m : ℕ) :
    criticalRVar ∣ criticalBeta1RT m - criticalBeta0RT m :=
  criticalRVar_dvd_of_coeff_zero _ (criticalBeta_diff_Rcoeff_zero m)

/-- The bivariate quotient `H` with `beta_1 - beta_0 = R * H`. -/
noncomputable def criticalHRT (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  Classical.choose (criticalBeta_diff_dvd_R m)

/-- The beta interpolation endpoint difference, written using the quotient `H`. -/
theorem criticalBeta1RT_eq_beta0RT_add_R_mul_H (m : ℕ) :
    criticalBeta1RT m = criticalBeta0RT m + criticalRVar * criticalHRT m := by
  have h := Classical.choose_spec (criticalBeta_diff_dvd_R m)
  rw [show criticalBeta1RT m =
      criticalBeta0RT m + (criticalBeta1RT m - criticalBeta0RT m) by ring]
  rw [h]
  rfl


/-- The axis endpoint linear factor `ell_0 = (lambda_m - 1) R - T`. -/
def criticalEll0 (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C (criticalLambda m - 1) * criticalR - criticalT

/-- The diagonal endpoint linear factor `ell_1 = ((lambda_m - 2)/2) R - T`. -/
def criticalEll1 (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C ((criticalLambda m - 2) / 2) * criticalR - criticalT

theorem criticalRTSubst_ell0RT (m : ℕ) :
    criticalRTSubst (criticalEll0RT m) = criticalEll0 m := by
  simp [criticalEll0RT, criticalEll0, criticalRTSubst_R, criticalRTSubst_T]

theorem criticalRTSubst_ell1RT (m : ℕ) :
    criticalRTSubst (criticalEll1RT m) = criticalEll1 m := by
  simp [criticalEll1RT, criticalEll1, criticalRTSubst_R, criticalRTSubst_T]

/-- The critical interpolation `alpha_0`. -/
def criticalAlpha0 (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  criticalEll0 m * criticalBinaryF_a m

/-- The critical interpolation `beta_0`. -/
def criticalBeta0 (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  criticalEll0 m * criticalBinaryF_b m

/-- The critical interpolation `alpha_1`. -/
def criticalAlpha1 (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  -criticalEll1 m * criticalBinaryG_c m

/-- The critical interpolation `beta_1`. -/
def criticalBeta1 (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  criticalEll1 m * criticalBinaryG_d m

theorem criticalRTSubst_alpha0RT (m : ℕ) :
    criticalRTSubst (criticalAlpha0RT m) = criticalAlpha0 m := by
  simp [criticalAlpha0RT, criticalAlpha0, criticalRTSubst_ell0RT,
    criticalRTSubst_binaryF_aRT]

theorem criticalRTSubst_beta0RT (m : ℕ) :
    criticalRTSubst (criticalBeta0RT m) = criticalBeta0 m := by
  simp [criticalBeta0RT, criticalBeta0, criticalRTSubst_ell0RT,
    criticalRTSubst_binaryF_bRT]

theorem criticalRTSubst_alpha1RT (m : ℕ) :
    criticalRTSubst (criticalAlpha1RT m) = criticalAlpha1 m := by
  simp [criticalAlpha1RT, criticalAlpha1, criticalRTSubst_ell1RT,
    criticalRTSubst_binaryG_cRT]

theorem criticalRTSubst_beta1RT (m : ℕ) :
    criticalRTSubst (criticalBeta1RT m) = criticalBeta1 m := by
  simp [criticalBeta1RT, criticalBeta1, criticalRTSubst_ell1RT,
    criticalRTSubst_binaryG_dRT]

/-- Ternary version of the quotient `Q`. -/
noncomputable def criticalQ (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  criticalRTSubst (criticalQRT m)

/-- Ternary alpha endpoint difference, written using `Q`. -/
theorem criticalAlpha1_eq_alpha0_add_R_sq_mul_Q (m : ℕ) :
    criticalAlpha1 m = criticalAlpha0 m + criticalR ^ 2 * criticalQ m := by
  rw [← criticalRTSubst_alpha1RT, ← criticalRTSubst_alpha0RT, ← criticalRTSubst_R]
  rw [criticalAlpha1RT_eq_alpha0RT_add_R_sq_mul_Q]
  simp [criticalQ]

/-- Ternary version of the quotient `H`. -/
noncomputable def criticalH (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  criticalRTSubst (criticalHRT m)

/-- Ternary beta endpoint difference, written using `H`. -/
theorem criticalBeta1_eq_beta0_add_R_mul_H (m : ℕ) :
    criticalBeta1 m = criticalBeta0 m + criticalR * criticalH m := by
  rw [← criticalRTSubst_beta1RT, ← criticalRTSubst_beta0RT, ← criticalRTSubst_R]
  rw [criticalBeta1RT_eq_beta0RT_add_R_mul_H]
  simp [criticalH]

/-- Endpoint square identity at `p = 0`. -/
theorem critical_axis_endpoint_square_identity (m : ℕ) :
    criticalT ^ criticalEta m * criticalAlpha0 m ^ 2 +
        criticalR * criticalT ^ criticalDelta m * criticalBeta0 m ^ 2 =
      criticalEll0 m ^ 2 * (criticalR + criticalT) ^ m *
        ((MvPolynomial.C (criticalL m) : MvPolynomial (Fin 3) ℝ) ^ 2 * criticalR +
              criticalT) := by
  unfold criticalAlpha0 criticalBeta0
  calc
    criticalT ^ criticalEta m * (criticalEll0 m * criticalBinaryF_a m) ^ 2 +
        criticalR * criticalT ^ criticalDelta m * (criticalEll0 m * criticalBinaryF_b m) ^ 2 =
      criticalEll0 m ^ 2 *
        (criticalT ^ criticalEta m * criticalBinaryF_a m ^ 2 +
          criticalR * criticalT ^ criticalDelta m * criticalBinaryF_b m ^ 2) := by
        ring
    _ = criticalEll0 m ^ 2 * (criticalR + criticalT) ^ m *
        ((MvPolynomial.C (criticalL m) : MvPolynomial (Fin 3) ℝ) ^ 2 * criticalR +
              criticalT) := by
        rw [criticalBinaryF_norm_identity]
        ring

/-- Endpoint square identity at `p = R^2/4`. -/
theorem critical_diagonal_endpoint_square_identity (m : ℕ) :
    criticalT ^ criticalEta m * criticalAlpha1 m ^ 2 +
        criticalR * criticalT ^ criticalDelta m * criticalBeta1 m ^ 2 =
      criticalEll1 m ^ 2 * (criticalR + criticalT) ^ (m + 1) := by
  unfold criticalAlpha1 criticalBeta1
  rw [← criticalBinaryG_norm_identity m]
  ring

/-- The critical radius polynomial `x^2 + y^2` is nonzero. -/
theorem criticalR_ne_zero : criticalR ≠ 0 := by
  unfold criticalR criticalX criticalY
  intro h
  have hcoeff := congrArg
    (fun p : MvPolynomial (Fin 3) ℝ => legacyMvCoeff (Finsupp.single (0 : Fin 3) 2) p) h
  norm_num [MvPolynomial.coeff_X_pow, Finsupp.single_eq_single_iff] at hcoeff

/-- The interpolating slope is determined by the alpha and beta endpoint quotients. -/
theorem critical_interpolation_slope_identity (m : ℕ) :
    criticalR ^ 2 *
        (8 * criticalT ^ criticalEta m * criticalAlpha0 m * criticalQ m +
              8 * criticalT ^ criticalDelta m * criticalBeta0 m * criticalH m +
            4 * criticalR * criticalT ^ criticalDelta m * criticalH m ^ 2 +
          4 * criticalR ^ 2 * criticalT ^ criticalEta m * criticalQ m ^ 2) =
      4 * ((criticalT ^ criticalEta m * criticalAlpha1 m ^ 2 +
          criticalR * criticalT ^ criticalDelta m * criticalBeta1 m ^ 2) -
        (criticalT ^ criticalEta m * criticalAlpha0 m ^ 2 +
          criticalR * criticalT ^ criticalDelta m * criticalBeta0 m ^ 2)) := by
  rw [criticalAlpha1_eq_alpha0_add_R_sq_mul_Q, criticalBeta1_eq_beta0_add_R_mul_H]
  ring

/-- The affine Robinson expression is the endpoint interpolation after multiplying by `R^2`. -/
theorem critical_four_mul_Pmlambda_endpoint_interpolation (m : ℕ) :
    criticalR ^ 2 *
      ((criticalR + criticalT) ^ m *
        ((criticalR + criticalT) *
            (MvPolynomial.C (criticalLambda m) * criticalR - 2 * (criticalR + criticalT)) ^ 2 +
          (MvPolynomial.C (criticalLambda m) : MvPolynomial (Fin 3) ℝ) ^ 2 *
            (4 * MvPolynomial.C (criticalLambda m) * criticalR - 5 * (criticalR + criticalT)) *
              (criticalR ^ 2 - 4 * criticalP))) =
      4 * (criticalR ^ 2 - 4 * criticalP) *
          (criticalT ^ criticalEta m * criticalAlpha0 m ^ 2 +
            criticalR * criticalT ^ criticalDelta m * criticalBeta0 m ^ 2) +
        16 * criticalP *
          (criticalT ^ criticalEta m * criticalAlpha1 m ^ 2 +
            criticalR * criticalT ^ criticalDelta m * criticalBeta1 m ^ 2) := by
  rw [critical_axis_endpoint_square_identity, critical_diagonal_endpoint_square_identity]
  unfold criticalEll0 criticalEll1 criticalLambda criticalL
  have hdiagCoeff :
      (MvPolynomial.C (((4 * (m : ℝ) * ((m : ℝ) + 1) - 2) / 2)) :
          MvPolynomial (Fin 3) ℝ) =
        -1 + (m : MvPolynomial (Fin 3) ℝ) * 2 +
          (m : MvPolynomial (Fin 3) ℝ) ^ 2 * 2 := by
    rw [show ((4 * (m : ℝ) * ((m : ℝ) + 1) - 2) / 2) =
        -1 + (m : ℝ) * 2 + (m : ℝ) ^ 2 * 2 by ring]
    norm_num [MvPolynomial.C_add, MvPolynomial.C_sub, MvPolynomial.C_neg,
      MvPolynomial.C_mul, MvPolynomial.C_pow, MvPolynomial.C_1,
      MvPolynomial.C_eq_coe_nat]
    rw [show (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 3) ℝ) = 2 from
      MvPolynomial.C_eq_coe_nat 2]
  rw [hdiagCoeff]
  simp only [map_add, map_sub, map_mul, map_one, map_natCast, map_ofNat]
  ring_nf

/-- The critical endpoint data gives the interpolation identity. -/
theorem Pmlambda_critical_interpolation_identity (m : ℕ) :
    Pmlambda m (criticalLambda m) =
      criticalInterpolationFor m (criticalAlpha0 m) (criticalBeta0 m)
        (criticalQ m) (criticalH m) := by
  have hfour : (4 : MvPolynomial (Fin 3) ℝ) ≠ 0 := by
    rw [show (4 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (4 : ℝ) from
      (MvPolynomial.C_eq_coe_nat 4).symm]
    exact MvPolynomial.C_ne_zero.mpr (by norm_num)
  apply mul_left_cancel₀ hfour
  rw [four_mul_Pmlambda_affine_critical_variables]
  unfold criticalInterpolationFor
  rw [criticalInterpolationRhs_affine (show criticalR = criticalX + criticalY by rfl)
    (show criticalP = criticalX * criticalY by rfl)]
  have hR2 : criticalR ^ 2 ≠ 0 := pow_ne_zero 2 criticalR_ne_zero
  apply mul_left_cancel₀ hR2
  rw [critical_four_mul_Pmlambda_endpoint_interpolation]
  set A0 : MvPolynomial (Fin 3) ℝ :=
    criticalT ^ criticalEta m * criticalAlpha0 m ^ 2 +
      criticalR * criticalT ^ criticalDelta m * criticalBeta0 m ^ 2
  set A1 : MvPolynomial (Fin 3) ℝ :=
    criticalT ^ criticalEta m * criticalAlpha1 m ^ 2 +
      criticalR * criticalT ^ criticalDelta m * criticalBeta1 m ^ 2
  set Slope : MvPolynomial (Fin 3) ℝ :=
    8 * criticalT ^ criticalEta m * criticalAlpha0 m * criticalQ m +
          8 * criticalT ^ criticalDelta m * criticalBeta0 m * criticalH m +
        4 * criticalR * criticalT ^ criticalDelta m * criticalH m ^ 2 +
      4 * criticalR ^ 2 * criticalT ^ criticalEta m * criticalQ m ^ 2
  have hSlope : criticalR ^ 2 * Slope = 4 * (A1 - A0) := by
    simpa [A0, A1, Slope] using critical_interpolation_slope_identity m
  change 4 * (criticalR ^ 2 - 4 * criticalP) * A0 + 16 * criticalP * A1 =
    criticalR ^ 2 * (4 * (A0 + criticalP * Slope))
  calc
    4 * (criticalR ^ 2 - 4 * criticalP) * A0 + 16 * criticalP * A1 =
        4 * criticalR ^ 2 * A0 + 16 * criticalP * (A1 - A0) := by
          ring
    _ = 4 * criticalR ^ 2 * A0 + 4 * criticalP * (4 * (A1 - A0)) := by
      ring
    _ = criticalR ^ 2 * (4 * (A0 + criticalP * Slope)) := by
      rw [← hSlope]
      ring

/-- The critical homogeneous Robinson form is a sum of squares at the threshold. -/
theorem Pmlambda_critical_isSOS_binary (m : ℕ) :
    IsSOS (Pmlambda m (criticalLambda m)) :=
  Pmlambda_critical_isSOS_of_criticalInterpolation_identity m
    (criticalAlpha0 m) (criticalBeta0 m) (criticalQ m) (criticalH m)
    (Pmlambda_critical_interpolation_identity m)

end ScaledRobinson
end OptimalConvergenceRates

end
