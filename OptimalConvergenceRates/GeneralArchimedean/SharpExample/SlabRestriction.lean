/-
  Algebraic restriction of a three-variable sharp-example certificate to the
  negative slab `z = -t`.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpExample.SOSMomentObstruction
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.QuadraticModuleSubstitution

noncomputable section

open Finset MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

/-- Substitute the constant `z` while retaining the `a,b` variables. -/
def sharpRestrictZ (z : Real) :
    MvPolynomial (Fin 3) Real →ₐ[Real] MvPolynomial (Fin 2) Real :=
  MvPolynomial.aeval ![obstructionA, obstructionB, C z]
@[simp] theorem sharpRestrictZ_C (z c : Real) :
    sharpRestrictZ z (C c) = C c := by
  simp [sharpRestrictZ]


@[simp] theorem sharpRestrictZ_a (z : Real) :
    sharpRestrictZ z sharpArchimedeanA = obstructionA := by
  simp [sharpRestrictZ, sharpArchimedeanA, KrivineStengle.sharpSeedA,
    obstructionA]

@[simp] theorem sharpRestrictZ_b (z : Real) :
    sharpRestrictZ z sharpArchimedeanB = obstructionB := by
  simp [sharpRestrictZ, sharpArchimedeanB, KrivineStengle.sharpSeedB,
    obstructionB]

@[simp] theorem sharpRestrictZ_z (z : Real) :
    sharpRestrictZ z sharpArchimedeanZ = C z := by
  simp [sharpRestrictZ, sharpArchimedeanZ, KrivineStengle.sharpSeedZ]

@[simp] theorem sharpRestrictZ_w (z : Real) :
    sharpRestrictZ z sharpArchimedeanW =
      C z * obstructionA * obstructionB + C (z ^ 5) := by
  simp [sharpRestrictZ, sharpArchimedeanW, KrivineStengle.sharpSeedW,
    KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB,
    KrivineStengle.sharpSeedZ]

@[simp] theorem sharpRestrictZ_ball (z : Real) :
    sharpRestrictZ z (sharpArchimedeanGenerators (3 : Fin 4)) =
      1 - obstructionA ^ 2 - obstructionB ^ 2 - C (z ^ 2) := by
  simp [sharpRestrictZ, sharpArchimedeanGenerators,
    KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedA,
    KrivineStengle.sharpSeedB, KrivineStengle.sharpSeedZ]

theorem sharpRestrictZ_totalDegree_le (z : Real)
    (p : MvPolynomial (Fin 3) Real) :
    (sharpRestrictZ z p).totalDegree <= p.totalDegree := by
  have h := QuarticConvergence.totalDegree_aeval_le_mul_general
    ![obstructionA, obstructionB, C z]
    (d := 1) (p := p) (by
      intro i
      fin_cases i <;> simp [obstructionA, obstructionB])
  simpa [sharpRestrictZ] using h

/-- Restriction preserves root-degree-bounded SOS witnesses. -/
def degreeBoundedSOS_sharpRestrictZ
    {tau : MvPolynomial (Fin 3) Real} {r : Nat}
    (htau : DegreeBoundedSOS tau r) (z : Real) :
    DegreeBoundedSOS (sharpRestrictZ z tau) r where
  N := htau.N
  P := fun k => sharpRestrictZ z (htau.P k)
  decomp := by
    calc
      sharpRestrictZ z tau = sharpRestrictZ z
          (∑ k : Fin htau.N, (htau.P k) ^ 2) :=
        congrArg (fun p => sharpRestrictZ z p) htau.decomp
      _ = ∑ k : Fin htau.N, (sharpRestrictZ z (htau.P k)) ^ 2 := by
        simp only [map_sum, map_pow]
  degree := fun k => (sharpRestrictZ_totalDegree_le z (htau.P k)).trans
    (htau.degree k)

/-- Nonnegative scalar multiplication preserves a root-degree bound. -/
def degreeBoundedSOS_nonnegScale
    {n r : Nat} {tau : MvPolynomial (Fin n) Real}
    (htau : DegreeBoundedSOS tau r) (c : Real) (hc : 0 <= c) :
    DegreeBoundedSOS (C c * tau) r where
  N := htau.N
  P := fun k => C (Real.sqrt c) * htau.P k
  decomp := by
    calc
      C c * tau = C c * ∑ k : Fin htau.N, (htau.P k) ^ 2 :=
        congrArg (fun p => C c * p) htau.decomp
      _ = ∑ k : Fin htau.N, C c * (htau.P k) ^ 2 := by rw [Finset.mul_sum]
      _ = ∑ k : Fin htau.N, (C (Real.sqrt c) * htau.P k) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [mul_pow]
        congr 1
        calc
          C c = C (Real.sqrt c ^ 2) :=
            congrArg C (Real.sq_sqrt hc).symm
          _ = C (Real.sqrt c) ^ 2 :=
            map_pow (MvPolynomial.C : Real →+* MvPolynomial (Fin n) Real) _ _
  degree := fun k => by
    rw [MvPolynomial.C_mul']
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (htau.degree k)

/-- Package produced by restricting and normalizing a sharp-example
certificate at `z=-t`. -/
structure SharpTwoVariableRefutation (d : Nat) (eta rho : Real) where
  tau0 : MvPolynomial (Fin 2) Real
  tau1 : MvPolynomial (Fin 2) Real
  tau2 : MvPolynomial (Fin 2) Real
  tau3 : MvPolynomial (Fin 2) Real
  tau4 : MvPolynomial (Fin 2) Real
  sos0 : DegreeBoundedSOS tau0 d
  sos1 : DegreeBoundedSOS tau1 d
  sos2 : DegreeBoundedSOS tau2 d
  sos3 : DegreeBoundedSOS tau3 d
  sos4 : DegreeBoundedSOS tau4 d
  identity :
    (-1 : MvPolynomial (Fin 2) Real) =
      tau0 + obstructionA * tau1 + obstructionB * tau2 +
        (-(obstructionA * obstructionB + C (eta ^ 2))) * tau3 +
        (C rho - obstructionA ^ 2 - obstructionB ^ 2) * tau4

/-- Algebraic restriction lemma for explicit SOS multipliers. -/
def sharpTwoVariableRefutation_of_explicit_certificate
    {eps t : Real} {r : Nat}
    (heps : 0 < eps) (ht : t = 2 * eps)
    (sigma0 sigmaA sigmaB sigmaG sigmaBall : MvPolynomial (Fin 3) Real)
    (hsigma0 : DegreeBoundedSOS sigma0 r)
    (hsigmaA : DegreeBoundedSOS sigmaA r)
    (hsigmaB : DegreeBoundedSOS sigmaB r)
    (hsigmaG : DegreeBoundedSOS sigmaG r)
    (hsigmaBall : DegreeBoundedSOS sigmaBall r)
    (hcert :
      sharpArchimedeanObjective + C eps =
        sigma0 + sigmaA * sharpArchimedeanA +
          sigmaB * sharpArchimedeanB + sigmaG * sharpArchimedeanW +
          sigmaBall * sharpArchimedeanGenerators (3 : Fin 4)) :
    SharpTwoVariableRefutation r (t ^ 2) (1 - t ^ 2) := by
  have htpos : 0 < t := by rw [ht]; positivity
  let s0 := sharpRestrictZ (-t) sigma0
  let sA := sharpRestrictZ (-t) sigmaA
  let sB := sharpRestrictZ (-t) sigmaB
  let sG := sharpRestrictZ (-t) sigmaG
  let sBall := sharpRestrictZ (-t) sigmaBall
  let tau0 := C (2 / t) * s0
  let tau1 := C (2 / t) * sA
  let tau2 := C (2 / t) * sB
  let tau3 := C 2 * sG
  let tau4 := C (2 / t) * sBall
  refine
    { tau0 := tau0, tau1 := tau1, tau2 := tau2, tau3 := tau3, tau4 := tau4
      sos0 := degreeBoundedSOS_nonnegScale (degreeBoundedSOS_sharpRestrictZ hsigma0 (-t))
        (2 / t) (by positivity)
      sos1 := degreeBoundedSOS_nonnegScale (degreeBoundedSOS_sharpRestrictZ hsigmaA (-t))
        (2 / t) (by positivity)
      sos2 := degreeBoundedSOS_nonnegScale (degreeBoundedSOS_sharpRestrictZ hsigmaB (-t))
        (2 / t) (by positivity)
      sos3 := degreeBoundedSOS_nonnegScale (degreeBoundedSOS_sharpRestrictZ hsigmaG (-t))
        2 (by norm_num)
      sos4 := degreeBoundedSOS_nonnegScale (degreeBoundedSOS_sharpRestrictZ hsigmaBall (-t))
        (2 / t) (by positivity)
      identity := ?_ }
  have hmapped := congrArg (fun p => sharpRestrictZ (-t) p) hcert
  simp only [map_add, map_mul, map_neg, map_pow,
    sharpRestrictZ_a, sharpRestrictZ_b, sharpRestrictZ_z,
    sharpRestrictZ_w, sharpRestrictZ_ball, sharpRestrictZ_C] at hmapped
  change
    -C t + C eps =
      s0 + sA * obstructionA + sB * obstructionB +
        sG * (-C t * obstructionA * obstructionB + (-C t) ^ 5) +
        sBall * (1 - obstructionA ^ 2 - obstructionB ^ 2 - (-C t) ^ 2)
    at hmapped
  dsimp [tau0, tau1, tau2, tau3, tau4]
  have htne : t ≠ 0 := ne_of_gt htpos
  have hepsEq : eps = t / 2 := by rw [ht]; ring
  rw [hepsEq] at hmapped
  let qconst : MvPolynomial (Fin 2) Real := C (2 / t)
  have hqt : qconst * C t = C 2 := by
    dsimp [qconst]
    rw [← C_mul]
    congr 1
    field_simp [htne]
  have hqhalf : qconst * C (t / 2) = 1 := by
    dsimp [qconst]
    rw [← C_mul]
    rw [show (2 / t) * (t / 2) = 1 by field_simp [htne]]
    simp
  have hwscale :
      qconst * (-C t * obstructionA * obstructionB + (-C t) ^ 5) =
        -(obstructionA * obstructionB + C ((t ^ 2) ^ 2)) * C 2 := by
    calc
      qconst * (-C t * obstructionA * obstructionB + (-C t) ^ 5) =
          -(qconst * C t) * (obstructionA * obstructionB + (C t) ^ 4) := by
            ring
      _ = -(obstructionA * obstructionB + C ((t ^ 2) ^ 2)) * C 2 := by
        rw [hqt]
        have hp : (C t : MvPolynomial (Fin 2) Real) ^ 4 = C ((t ^ 2) ^ 2) := by
          rw [← map_pow]
          congr 1
          ring
        rw [hp]
        ring
  have hballscale :
      qconst * (1 - obstructionA ^ 2 - obstructionB ^ 2 - (-C t) ^ 2) =
        (C (1 - t ^ 2) - obstructionA ^ 2 - obstructionB ^ 2) * qconst := by
    have hcsub : (C (1 - t ^ 2) : MvPolynomial (Fin 2) Real) = 1 - C (t ^ 2) := by
      rw [map_sub, map_one]
    have hpow : (-C t : MvPolynomial (Fin 2) Real) ^ 2 = C (t ^ 2) := by
      rw [neg_sq, ← map_pow]
    rw [hcsub, hpow]
    ring
  calc
    -1 = qconst * (-C t + C (t / 2)) := by
      rw [mul_add, mul_neg, hqt, hqhalf]
      have hc2 : (C 2 : MvPolynomial (Fin 2) Real) = 1 + 1 := by
        rw [show (2 : Real) = 1 + 1 by norm_num, map_add, map_one]
      rw [hc2]
      ring
    _ = qconst *
        (s0 + sA * obstructionA + sB * obstructionB +
          sG * (-C t * obstructionA * obstructionB + (-C t) ^ 5) +
          sBall * (1 - obstructionA ^ 2 - obstructionB ^ 2 - (-C t) ^ 2)) := by
      exact congrArg (fun p => qconst * p) hmapped
    _ = qconst * s0 + (qconst * sA) * obstructionA +
          (qconst * sB) * obstructionB +
          (C 2 * sG) * (-(obstructionA * obstructionB + C ((t ^ 2) ^ 2))) +
          (qconst * sBall) *
            (C (1 - t ^ 2) - obstructionA ^ 2 - obstructionB ^ 2) := by
      calc
        qconst *
            (s0 + sA * obstructionA + sB * obstructionB +
              sG * (-C t * obstructionA * obstructionB + (-C t) ^ 5) +
              sBall * (1 - obstructionA ^ 2 - obstructionB ^ 2 - (-C t) ^ 2)) =
            qconst * s0 + (qconst * sA) * obstructionA +
              (qconst * sB) * obstructionB + sG *
                (qconst * (-C t * obstructionA * obstructionB + (-C t) ^ 5)) +
              sBall * (qconst *
                (1 - obstructionA ^ 2 - obstructionB ^ 2 - (-C t) ^ 2)) := by ring
        _ = _ := by
          rw [hwscale, hballscale]
          ring
    _ = C (2 / t) * s0 + obstructionA * (C (2 / t) * sA) +
          obstructionB * (C (2 / t) * sB) +
          (-(obstructionA * obstructionB + C ((t ^ 2) ^ 2))) * (C 2 * sG) +
          (C (1 - t ^ 2) - obstructionA ^ 2 - obstructionB ^ 2) *
            (C (2 / t) * sBall) := by
      dsimp [qconst]
      ring


/-- Turn an SOS with a coarse total-degree bound into the root-degree-bounded
witness used by the moment argument. -/
theorem nonempty_degreeBoundedSOS_of_isSOS_totalDegree_le
    {n r : Nat} {sigma : MvPolynomial (Fin n) Real}
    (hsigma : IsSOS sigma) (hdegree : sigma.totalDegree <= 2 * r) :
    Nonempty (DegreeBoundedSOS sigma r) := by
  obtain ⟨N, P, hP⟩ := hsigma
  exact ⟨
    { N := N
      P := P
      decomp := hP
      degree := sos_summand_totalDegree_le_of_sum_sq_totalDegree hP hdegree }⟩

/-- None of the four fixed sharp-example generators is the zero polynomial. -/
theorem sharpArchimedeanGenerator_ne_zero (i : Fin 4) :
    sharpArchimedeanGenerators i ≠ 0 := by
  fin_cases i
  all_goals intro hzero
  · have h := congrArg (MvPolynomial.eval ![(1 : Real), 0, 0]) hzero
    simpa [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
      KrivineStengle.sharpSeedA] using h
  · have h := congrArg (MvPolynomial.eval ![(0 : Real), 1, 0]) hzero
    simpa [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
      KrivineStengle.sharpSeedB] using h
  · have h := congrArg (MvPolynomial.eval ![(1 : Real), 1, 1]) hzero
    norm_num [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
      KrivineStengle.sharpSeedW, KrivineStengle.sharpSeedA,
      KrivineStengle.sharpSeedB, KrivineStengle.sharpSeedZ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
  · have h := congrArg (MvPolynomial.eval ![(0 : Real), 0, 0]) hzero
    norm_num [sharpArchimedeanGenerators, KrivineStengle.sharpSeedGenerators,
      KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB,
      KrivineStengle.sharpSeedZ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] at h

/-- Extract all five degree-bounded SOS multipliers from a truncated
quadratic-module certificate and perform the `z=-2 eps` restriction. -/
theorem sharpTwoVariableRefutation_of_certificate
    {eps : Real} {r : Nat} (heps : 0 < eps)
    (hcert : sharpArchimedeanObjective + C eps ∈
      GenQuadraticModule sharpArchimedeanGenerators r) :
    Nonempty (SharpTwoVariableRefutation r ((2 * eps) ^ 2) (1 - (2 * eps) ^ 2)) := by
  obtain ⟨sigma0, sigma, hsigma0, hsigma, hdegree0, hdegree, hidentity⟩ := hcert
  have hsigmaDegree (i : Fin 4) : (sigma i).totalDegree <= r := by
    by_cases hzero : sigma i = 0
    · simp [hzero]
    · have hmul := MvPolynomial.totalDegree_mul_of_isDomain hzero
        (sharpArchimedeanGenerator_ne_zero i)
      have hi := hdegree i
      rw [hmul] at hi
      omega
  have hsigma0Bounded : Nonempty (DegreeBoundedSOS sigma0 r) :=
    nonempty_degreeBoundedSOS_of_isSOS_totalDegree_le hsigma0 (by omega)
  have hsigmaBounded (i : Fin 4) : Nonempty (DegreeBoundedSOS (sigma i) r) :=
    nonempty_degreeBoundedSOS_of_isSOS_totalDegree_le (hsigma i) (by
      have hi := hsigmaDegree i
      omega)
  obtain ⟨hs0⟩ := hsigma0Bounded
  obtain ⟨hsA⟩ := hsigmaBounded 0
  obtain ⟨hsB⟩ := hsigmaBounded 1
  obtain ⟨hsG⟩ := hsigmaBounded 2
  obtain ⟨hsBall⟩ := hsigmaBounded 3
  refine ⟨sharpTwoVariableRefutation_of_explicit_certificate heps rfl
    sigma0 (sigma 0) (sigma 1) (sigma 2) (sigma 3)
    hs0 hsA hsB hsG hsBall ?_⟩
  calc
    sharpArchimedeanObjective + C eps = sigma0 +
        (sigma 0 * sharpArchimedeanA + sigma 1 * sharpArchimedeanB +
          sigma 2 * sharpArchimedeanW + sigma 3 * sharpArchimedeanGenerators 3) := by
      simpa [Fin.sum_univ_four, sharpArchimedeanGenerators,
        KrivineStengle.sharpSeedGenerators] using hidentity
    _ = sigma0 + sigma 0 * sharpArchimedeanA +
          sigma 1 * sharpArchimedeanB + sigma 2 * sharpArchimedeanW +
          sigma 3 * sharpArchimedeanGenerators 3 := by
      ring
end OptimalConvergenceRates.GeneralArchimedean

end
