/- Low and high homogeneous-jet bounds for Motzkin certificates. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.DirectionalRestrictions
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.SymmetricHole

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

/-- A coarse common constant for the three low Motzkin jets. -/
def motzkinLowJetConst : ℝ := 400000

theorem motzkinLowJetConst_pos : 0 < motzkinLowJetConst := by
  norm_num [motzkinLowJetConst]

/-- The constant, linear, and quadratic homogeneous pieces of an SOS root are
controlled by its values on the six zero lines. -/
theorem motzkin_low_jet_bounds
    {N r : ℕ} {epsilon : ℝ}
    (heps : 0 < epsilon) (hr : 1 ≤ r)
    (Q : Fin N → MvPolynomial (Fin 3) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ r)
    (hzeroLines : ∀ zi : Fin 6, ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm
          (fun i : Fin N =>
            MvPolynomial.eval (fun j => t * motzkinZeroDirection zi j) (Q i)) ≤
        schmInteriorLocalControlConst * Real.sqrt epsilon) :
    motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) ≤
        motzkinLowJetConst * Real.sqrt epsilon ∧
      motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) ≤
        motzkinLowJetConst * (r : ℝ) * Real.sqrt epsilon ∧
      motzkinVecCoeffNorm (homogeneousPartVec3 2 Q) ≤
        motzkinLowJetConst * (r : ℝ) ^ 2 * Real.sqrt epsilon := by
  let M : ℝ := schmInteriorLocalControlConst * Real.sqrt epsilon
  have hM : 0 ≤ M := mul_nonneg schmInteriorLocalControlConst_pos.le
    (Real.sqrt_nonneg epsilon)
  have hrestr (zi : Fin 6) :
      let P : Fin N → Polynomial ℝ := fun i =>
        univariateRestriction (Q i) (0 : Fin 3 → ℝ) (motzkinZeroDirection zi)
      (∀ i, (P i).natDegree ≤ r) ∧
      (∀ t : ℝ, |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ M) := by
    dsimp
    constructor
    · intro i
      exact (univariateRestriction_natDegree_le (Q i) (0 : Fin 3 → ℝ)
        (motzkinZeroDirection zi)).trans (hdeg i)
    · intro t ht
      have heval : (fun i : Fin N =>
          (univariateRestriction (Q i) (0 : Fin 3 → ℝ)
            (motzkinZeroDirection zi)).eval t) =
          fun i : Fin N => MvPolynomial.eval
            (fun j => t * motzkinZeroDirection zi j) (Q i) := by
        funext i
        rw [univariateRestriction_eval]
        apply congrArg (fun w : Fin 3 → ℝ => MvPolynomial.eval w (Q i))
        funext j
        simp [Pi.smul_apply, smul_eq_mul]
      rw [heval]
      simpa [M] using hzeroLines zi t ht
  have hzero : motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) ≤ M := by
    have hline := (hrestr 0).2 0 (by simpa using schmInteriorS_nonneg)
    have heval : (fun i : Fin N =>
        (univariateRestriction (Q i) (0 : Fin 3 → ℝ)
          (motzkinZeroDirection 0)).eval 0) =
        fun i : Fin N => MvPolynomial.eval 0 (Q i) := by
      funext i
      simp [univariateRestriction_eval]
    rw [heval] at hline
    calc
      motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) =
          interiorVecNorm (fun i : Fin N => MvPolynomial.eval 0 (Q i)) := by
        unfold motzkinVecCoeffNorm homogeneousPartVec3 interiorVecNorm interiorVecSqNorm
        simp_rw [motzkinCoeffNorm_homogeneousPart3_zero, sq_abs]
      _ ≤ M := hline
  have hlinearEval : ∀ zi : Fin 6,
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval (motzkinZeroDirection zi) (homogeneousPartVec3 1 Q i)) ≤
        8 * (r : ℝ) * M := by
    intro zi
    let P : Fin N → Polynomial ℝ := fun i =>
      univariateRestriction (Q i) (0 : Fin 3 → ℝ) (motzkinZeroDirection zi)
    have hb := interior_bernstein_vector_first_derivative_schm P hM
      (hrestr zi).1 (hrestr zi).2
    have heq : (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) =
        fun i : Fin N =>
          MvPolynomial.eval (motzkinZeroDirection zi) (homogeneousPartVec3 1 Q i) := by
      funext i
      dsimp [P, homogeneousPartVec3]
      simpa using iterateDirectionalDeriv_zero_eq_eval_homogeneousPart
        (Q i) (motzkinZeroDirection zi) 1
    simpa [heq] using hb
  have hlinear := linear_unisolvence (homogeneousPartVec3 1 Q)
    (fun i => homogeneousPart3_idem 1 (Q i)) hlinearEval
  have hquadraticEval : ∀ zi : Fin 6,
      interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval (motzkinZeroDirection zi) (homogeneousPartVec3 2 Q i)) ≤
        32 * (r : ℝ) ^ 2 * M := by
    intro zi
    let P : Fin N → Polynomial ℝ := fun i =>
      univariateRestriction (Q i) (0 : Fin 3 → ℝ) (motzkinZeroDirection zi)
    have hb := interior_bernstein_vector_second_derivative_schm_explicit P hM
      (hrestr zi).1 (hrestr zi).2
    have heq : (fun i : Fin N =>
        (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) =
        fun i : Fin N => 2 *
          MvPolynomial.eval (motzkinZeroDirection zi) (homogeneousPartVec3 2 Q i) := by
      funext i
      dsimp [P, homogeneousPartVec3]
      simpa using iterateDirectionalDeriv_zero_eq_eval_homogeneousPart
        (Q i) (motzkinZeroDirection zi) 2
    rw [heq] at hb
    have hscale : interiorVecNorm (fun i : Fin N => 2 *
        MvPolynomial.eval (motzkinZeroDirection zi) (homogeneousPartVec3 2 Q i)) =
        2 * interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval (motzkinZeroDirection zi) (homogeneousPartVec3 2 Q i)) := by
      simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
        vecNorm_smul_nonneg (N := N) (c := (2 : ℝ)) (by norm_num)
          (fun i : Fin N =>
            MvPolynomial.eval (motzkinZeroDirection zi) (homogeneousPartVec3 2 Q i))
    rw [hscale] at hb
    nlinarith
  have hquadratic := quadratic_unisolvence (homogeneousPartVec3 2 Q)
    (fun i => homogeneousPart3_idem 2 (Q i)) hquadraticEval
  constructor
  · calc
      motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) ≤ M := hzero
      _ ≤ motzkinLowJetConst * Real.sqrt epsilon := by
        dsimp [M, motzkinLowJetConst, schmInteriorLocalControlConst]
        nlinarith [Real.sqrt_nonneg epsilon]
  constructor
  · calc
      motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) ≤ 5 * (8 * (r : ℝ) * M) := hlinear
      _ ≤ motzkinLowJetConst * (r : ℝ) * Real.sqrt epsilon := by
        dsimp [M, motzkinLowJetConst, schmInteriorLocalControlConst]
        have hfac : 0 ≤ (r : ℝ) * Real.sqrt epsilon := by positivity
        nlinarith
  · calc
      motzkinVecCoeffNorm (homogeneousPartVec3 2 Q) ≤
          100 * (32 * (r : ℝ) ^ 2 * M) := hquadratic
      _ ≤ motzkinLowJetConst * (r : ℝ) ^ 2 * Real.sqrt epsilon := by
        dsimp [M, motzkinLowJetConst, schmInteriorLocalControlConst]
        have hfac : 0 ≤ (r : ℝ) ^ 2 * Real.sqrt epsilon := by positivity
        nlinarith

lemma interiorVecNorm_sub_sub_sub_le_add4 {N : ℕ}
    (a b c d : Fin N → ℝ) :
    interiorVecNorm (fun i => a i - b i - c i - d i) ≤
      interiorVecNorm a + interiorVecNorm b + interiorVecNorm c + interiorVecNorm d := by
  calc
    interiorVecNorm (fun i => a i - b i - c i - d i) ≤
        interiorVecNorm (fun i => a i - b i - c i) + interiorVecNorm d := by
      simpa using interiorVecNorm_sub_le (fun i => a i - b i - c i) d
    _ ≤ (interiorVecNorm (fun i => a i - b i) + interiorVecNorm c) +
        interiorVecNorm d := by
      gcongr
      exact interiorVecNorm_sub_le _ _
    _ ≤ interiorVecNorm a + interiorVecNorm b + interiorVecNorm c +
        interiorVecNorm d := by
      gcongr
      exact interiorVecNorm_sub_le _ _

/-- The cubic tail is uniformly bounded outside the sixth-root hole. -/
theorem motzkin_cubic_tail_outer_bound
    {N r : ℕ} {epsilon rho : ℝ}
    (hrho : 0 < rho)
    (hsqrt : Real.sqrt epsilon = rho ^ 3)
    (hsmall : (r : ℝ) * rho ≤ 1 / 8)
    (Q : Fin N → MvPolynomial (Fin 3) ℝ)
    (hlocalCubic : ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      ∀ t : ℝ, |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval (fun j => t * v j) (Q i)) ≤
            schmInteriorLocalControlConst * (Real.sqrt epsilon + |t| ^ 3))
    (hlow :
      motzkinVecCoeffNorm (homogeneousPartVec3 0 Q) ≤
          motzkinLowJetConst * Real.sqrt epsilon ∧
        motzkinVecCoeffNorm (homogeneousPartVec3 1 Q) ≤
          motzkinLowJetConst * (r : ℝ) * Real.sqrt epsilon ∧
        motzkinVecCoeffNorm (homogeneousPartVec3 2 Q) ≤
          motzkinLowJetConst * (r : ℝ) ^ 2 * Real.sqrt epsilon) :
    ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin N =>
          (polynomialTailDivX3
            (univariateRestriction (Q i) (0 : Fin 3 → ℝ) v)).eval t) ≤
          4 * motzkinLowJetConst + 2 * schmInteriorLocalControlConst := by
  intro v hv t ht
  let a : ℝ := |t|
  have ha : 0 ≤ a := abs_nonneg t
  have hrhoA : rho ≤ a := ht.1
  have hrnon : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hrrho : (r : ℝ) * rho ≤ 1 := hsmall.trans (by norm_num)
  have hsqrtA : Real.sqrt epsilon ≤ a ^ 3 := by
    rw [hsqrt]
    exact pow_le_pow_left₀ hrho.le hrhoA 3
  have hlinScale : (r : ℝ) * Real.sqrt epsilon * a ≤ a ^ 3 := by
    rw [hsqrt]
    have hrho2 : rho ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hrho.le hrhoA 2
    calc
      (r : ℝ) * rho ^ 3 * a = ((r : ℝ) * rho) * (rho ^ 2 * a) := by ring
      _ ≤ 1 * (rho ^ 2 * a) :=
        mul_le_mul_of_nonneg_right hrrho (mul_nonneg (sq_nonneg rho) ha)
      _ ≤ 1 * (a ^ 2 * a) := by
        gcongr
      _ = a ^ 3 := by ring
  have hquadScale : (r : ℝ) ^ 2 * Real.sqrt epsilon * a ^ 2 ≤ a ^ 3 := by
    rw [hsqrt]
    have hrrho0 : 0 ≤ (r : ℝ) * rho := mul_nonneg hrnon hrho.le
    have hrrho2 : ((r : ℝ) * rho) ^ 2 ≤ 1 ^ 2 :=
      pow_le_pow_left₀ hrrho0 hrrho 2
    calc
      (r : ℝ) ^ 2 * rho ^ 3 * a ^ 2 =
          ((r : ℝ) * rho) ^ 2 * (rho * a ^ 2) := by ring
      _ ≤ 1 ^ 2 * (rho * a ^ 2) :=
        mul_le_mul_of_nonneg_right hrrho2 (mul_nonneg hrho.le (sq_nonneg a))
      _ ≤ 1 ^ 2 * (a * a ^ 2) := by
        gcongr
      _ = a ^ 3 := by ring
  let P : Fin N → Polynomial ℝ := fun i =>
    univariateRestriction (Q i) (0 : Fin 3 → ℝ) v
  have hcoeff (m : ℕ) : (fun i : Fin N => (P i).coeff m) =
      fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec3 m Q i) := by
    funext i
    dsimp [P, homogeneousPartVec3]
    exact coeff_univariateRestriction_zero_eq_eval_homogeneousPart (Q i) v m
  have heval (i : Fin N) : (P i).eval t =
      MvPolynomial.eval (fun j => t * v j) (Q i) := by
    rw [show P i = univariateRestriction (Q i) (0 : Fin 3 → ℝ) v by rfl]
    rw [univariateRestriction_eval]
    have hx : (0 : Fin 3 → ℝ) + t • v = fun j => t * v j := by
      funext j
      simp [smul_eq_mul]
    rw [hx]
  have hq : interiorVecNorm (fun i : Fin N => (P i).eval t) ≤
      2 * schmInteriorLocalControlConst * a ^ 3 := by
    calc
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤
          schmInteriorLocalControlConst * (Real.sqrt epsilon + a ^ 3) := by
        simpa [heval] using hlocalCubic v hv t ht.2
      _ ≤ 2 * schmInteriorLocalControlConst * a ^ 3 := by
        nlinarith [schmInteriorLocalControlConst_pos.le]
  have h0eval : interiorVecNorm (fun i : Fin N => (P i).coeff 0) ≤
      motzkinLowJetConst * a ^ 3 := by
    rw [hcoeff]
    exact (interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one
      (homogeneousPartVec3 0 Q) hv).trans
        (hlow.1.trans (mul_le_mul_of_nonneg_left hsqrtA motzkinLowJetConst_pos.le))
  have h1eval : interiorVecNorm (fun i : Fin N => (P i).coeff 1 * t) ≤
      motzkinLowJetConst * a ^ 3 := by
    have hev := interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one
      (homogeneousPartVec3 1 Q) hv
    have hcoeff1 : (fun i : Fin N => (P i).coeff 1 * t) =
        fun i : Fin N => t * MvPolynomial.eval v (homogeneousPartVec3 1 Q i) := by
      funext i
      rw [congrFun (hcoeff 1) i]
      ring
    rw [hcoeff1, interiorVecNorm_smul_abs]
    change a * interiorVecNorm (fun i : Fin N =>
      MvPolynomial.eval v (homogeneousPartVec3 1 Q i)) ≤ _
    calc
      a * interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPartVec3 1 Q i)) ≤
          a * (motzkinLowJetConst * (r : ℝ) * Real.sqrt epsilon) :=
        mul_le_mul_of_nonneg_left (hev.trans hlow.2.1) ha
      _ = motzkinLowJetConst * ((r : ℝ) * Real.sqrt epsilon * a) := by ring
      _ ≤ motzkinLowJetConst * a ^ 3 :=
        mul_le_mul_of_nonneg_left hlinScale motzkinLowJetConst_pos.le
  have h2eval : interiorVecNorm (fun i : Fin N => (P i).coeff 2 * t ^ 2) ≤
      motzkinLowJetConst * a ^ 3 := by
    have hev := interiorVecNorm_eval_le_motzkinVecCoeffNorm_of_motzkinSqNorm_eq_one
      (homogeneousPartVec3 2 Q) hv
    have hcoeff2 : (fun i : Fin N => (P i).coeff 2 * t ^ 2) =
        fun i : Fin N => t ^ 2 * MvPolynomial.eval v (homogeneousPartVec3 2 Q i) := by
      funext i
      rw [congrFun (hcoeff 2) i]
      ring
    rw [hcoeff2, interiorVecNorm_smul_abs, abs_pow]
    change a ^ 2 * interiorVecNorm (fun i : Fin N =>
      MvPolynomial.eval v (homogeneousPartVec3 2 Q i)) ≤ _
    calc
      a ^ 2 * interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPartVec3 2 Q i)) ≤
          a ^ 2 * (motzkinLowJetConst * (r : ℝ) ^ 2 * Real.sqrt epsilon) :=
        mul_le_mul_of_nonneg_left (hev.trans hlow.2.2) (sq_nonneg a)
      _ = motzkinLowJetConst * ((r : ℝ) ^ 2 * Real.sqrt epsilon * a ^ 2) := by ring
      _ ≤ motzkinLowJetConst * a ^ 3 :=
        mul_le_mul_of_nonneg_left hquadScale motzkinLowJetConst_pos.le
  apply interiorVecNorm_polynomialTailDivX3_eval_le_of_residual_bound P
  · exact fun h => by subst t; simp at ht; linarith
  · have hres := interiorVecNorm_sub_sub_sub_le_add4
      (fun i : Fin N => (P i).eval t)
      (fun i : Fin N => (P i).coeff 0)
      (fun i : Fin N => (P i).coeff 1 * t)
      (fun i : Fin N => (P i).coeff 2 * t ^ 2)
    calc
      interiorVecNorm (fun i : Fin N =>
          (P i).eval t - (P i).coeff 0 - (P i).coeff 1 * t -
            (P i).coeff 2 * t ^ 2) ≤
          interiorVecNorm (fun i : Fin N => (P i).eval t) +
          interiorVecNorm (fun i : Fin N => (P i).coeff 0) +
          interiorVecNorm (fun i : Fin N => (P i).coeff 1 * t) +
          interiorVecNorm (fun i : Fin N => (P i).coeff 2 * t ^ 2) := hres
      _ ≤ (4 * motzkinLowJetConst + 2 * schmInteriorLocalControlConst) * a ^ 3 := by
        have ha3 : 0 ≤ a ^ 3 := pow_nonneg ha 3
        nlinarith [motzkinLowJetConst_pos.le]
      _ = (4 * motzkinLowJetConst + 2 * schmInteriorLocalControlConst) * |t| ^ 3 := rfl

/-- Symmetric-hole and Bernstein control of the four high homogeneous pieces
from a uniform punctured-interval bound on the cubic tail. -/
theorem motzkin_high_jet_eval_bounds_of_tail_bound
    {N r : ℕ} {rho M : ℝ}
    (hrho : 0 < rho) (hrhoSmall : rho < schmInteriorS / 2)
    (hr2 : 2 ≤ r) (hdegree : ((2 * r : ℕ) : ℝ) * rho ≤ schmInteriorS)
    (hM : 0 ≤ M)
    (Q : Fin N → MvPolynomial (Fin 3) ℝ)
    (hdeg : ∀ i, (Q i).totalDegree ≤ r)
    (houter : ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      ∀ t : ℝ, rho ≤ |t| ∧ |t| ≤ schmInteriorS →
        interiorVecNorm (fun i : Fin N =>
          (polynomialTailDivX3
            (univariateRestriction (Q i) (0 : Fin 3 → ℝ) v)).eval t) ≤ M) :
    ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      let U := 2 * Real.exp 6 * M
      interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPartVec3 3 Q i)) ≤ U ∧
        interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPartVec3 4 Q i)) ≤ 8 * (r : ℝ) * U ∧
        interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPartVec3 5 Q i)) ≤
            32 * (r : ℝ) ^ 2 * U ∧
        interiorVecNorm (fun i : Fin N =>
          MvPolynomial.eval v (homogeneousPartVec3 6 Q i)) ≤
            700 * (r : ℝ) ^ 3 * U := by
  intro v hv
  let P : Fin N → Polynomial ℝ := fun i =>
    polynomialTailDivX3 (univariateRestriction (Q i) (0 : Fin 3 → ℝ) v)
  let U : ℝ := 2 * Real.exp 6 * M
  have hPdeg : ∀ i, (P i).natDegree ≤ r := by
    intro i
    exact (polynomialTailDivX3_natDegree_le _).trans
      ((univariateRestriction_natDegree_le (Q i) (0 : Fin 3 → ℝ) v).trans (hdeg i))
  have hfull : ∀ t : ℝ, |t| ≤ schmInteriorS →
      interiorVecNorm (fun i : Fin N => (P i).eval t) ≤ U := by
    simpa [P, U] using symmetricHole_vector_bound hrho hrhoSmall hr2 hdegree hM
      P hPdeg (houter v hv)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have h0 := hfull 0 (by simpa using schmInteriorS_nonneg)
  have h0eq : (fun i : Fin N => (P i).eval 0) = fun i : Fin N =>
      MvPolynomial.eval v (homogeneousPartVec3 3 Q i) := by
    funext i
    dsimp [P, homogeneousPartVec3]
    simpa using iterateDerivative_tail3_univariateRestriction_eval_zero_eq_homogeneousPart
      (Q i) v 0
  have hfirst := interior_bernstein_vector_first_derivative_schm P hU hPdeg hfull
  have hfirstEq : (fun i : Fin N => (Polynomial.derivative (P i)).eval 0) =
      fun i : Fin N => MvPolynomial.eval v (homogeneousPartVec3 4 Q i) := by
    funext i
    dsimp [P, homogeneousPartVec3]
    simpa using iterateDerivative_tail3_univariateRestriction_eval_zero_eq_homogeneousPart
      (Q i) v 1
  have hsecond := interior_bernstein_vector_second_derivative_schm_explicit P hU hPdeg hfull
  have hsecondEq : (fun i : Fin N =>
      (Polynomial.derivative (Polynomial.derivative (P i))).eval 0) =
      fun i : Fin N => 2 * MvPolynomial.eval v (homogeneousPartVec3 5 Q i) := by
    funext i
    dsimp [P, homogeneousPartVec3]
    simpa using iterateDerivative_tail3_univariateRestriction_eval_zero_eq_homogeneousPart
      (Q i) v 2
  have hthird := interior_bernstein_vector_third_derivative_schm_explicit P hU hPdeg hfull
  have hthirdEq : (fun i : Fin N =>
      (Polynomial.derivative
        (Polynomial.derivative (Polynomial.derivative (P i)))).eval 0) =
      fun i : Fin N => 6 * MvPolynomial.eval v (homogeneousPartVec3 6 Q i) := by
    funext i
    dsimp [P, homogeneousPartVec3]
    simpa [Nat.factorial] using
      iterateDerivative_tail3_univariateRestriction_eval_zero_eq_homogeneousPart
        (Q i) v 3
  rw [h0eq] at h0
  rw [hfirstEq] at hfirst
  rw [hsecondEq] at hsecond
  rw [hthirdEq] at hthird
  have hscale2 : interiorVecNorm (fun i : Fin N =>
      2 * MvPolynomial.eval v (homogeneousPartVec3 5 Q i)) =
      2 * interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPartVec3 5 Q i)) := by
    rw [interiorVecNorm_smul_abs]
    norm_num
  have hscale6 : interiorVecNorm (fun i : Fin N =>
      6 * MvPolynomial.eval v (homogeneousPartVec3 6 Q i)) =
      6 * interiorVecNorm (fun i : Fin N =>
        MvPolynomial.eval v (homogeneousPartVec3 6 Q i)) := by
    rw [interiorVecNorm_smul_abs]
    norm_num
  rw [hscale2] at hsecond
  rw [hscale6] at hthird
  have hfive : interiorVecNorm (fun i : Fin N =>
      MvPolynomial.eval v (homogeneousPartVec3 5 Q i)) ≤
      32 * (r : ℝ) ^ 2 * U := by nlinarith
  have hfac : 0 ≤ (r : ℝ) ^ 3 * U := by positivity
  have hsix : interiorVecNorm (fun i : Fin N =>
      MvPolynomial.eval v (homogeneousPartVec3 6 Q i)) ≤
      700 * (r : ℝ) ^ 3 * U := by nlinarith
  exact ⟨h0, hfirst, hfive, hsix⟩


end Motzkin

end OptimalConvergenceRates

end
