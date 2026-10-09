import OptimalConvergenceRates.GeneralArchimedean.SharpExample.SlabBounds

noncomputable section
open Finset MvPolynomial Polynomial
open OptimalConvergenceRates

namespace OptimalConvergenceRates.GeneralArchimedean

def sharpRestrictA (b z : Real) (p : MvPolynomial (Fin 3) Real) :
    Polynomial Real :=
  MvPolynomial.aeval ![Polynomial.X, Polynomial.C b, Polynomial.C z] p

@[simp] theorem sharpRestrictA_eval (a b z : Real)
    (p : MvPolynomial (Fin 3) Real) :
    (sharpRestrictA b z p).eval a = MvPolynomial.eval ![a, b, z] p := by
  rw [sharpRestrictA]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
        Polynomial.eval_mul]
      rw [hp]
      congr 1
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]

theorem sharpRestrictA_natDegree_le (b z : Real)
    (p : MvPolynomial (Fin 3) Real) :
    (sharpRestrictA b z p).natDegree <= p.totalDegree := by
  have h := MvPolynomial.aeval_natDegree_le p (le_refl p.totalDegree)
    ![Polynomial.X, Polynomial.C b, Polynomial.C z] (n := 1) (by
      intro i
      fin_cases i <;> simp)
  simpa using h

def sharpRestrictB (a z : Real) (p : MvPolynomial (Fin 3) Real) :
    Polynomial Real :=
  MvPolynomial.aeval ![Polynomial.C a, Polynomial.X, Polynomial.C z] p

@[simp] theorem sharpRestrictB_eval (a b z : Real)
    (p : MvPolynomial (Fin 3) Real) :
    (sharpRestrictB a z p).eval b = MvPolynomial.eval ![a, b, z] p := by
  rw [sharpRestrictB]
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X,
        Polynomial.eval_mul]
      rw [hp]
      congr 1
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]

theorem sharpRestrictB_natDegree_le (a z : Real)
    (p : MvPolynomial (Fin 3) Real) :
    (sharpRestrictB a z p).natDegree <= p.totalDegree := by
  have h := MvPolynomial.aeval_natDegree_le p (le_refl p.totalDegree)
    ![Polynomial.C a, Polynomial.X, Polynomial.C z] (n := 1) (by
      intro i
      fin_cases i <;> simp)
  simpa using h

theorem sharpCertificate_eval
    {eps : Real}
    (sigma0 sigmaA sigmaB sigmaG sigmaBall : MvPolynomial (Fin 3) Real)
    (hcert : sharpArchimedeanObjective + MvPolynomial.C eps =
      sigma0 + sigmaA * sharpArchimedeanA +
        sigmaB * sharpArchimedeanB + sigmaG * sharpArchimedeanW +
        sigmaBall * sharpArchimedeanGenerators (3 : Fin 4))
    (a b z : Real) :
    z + eps =
      MvPolynomial.eval ![a,b,z] sigma0 +
      a * MvPolynomial.eval ![a,b,z] sigmaA +
      b * MvPolynomial.eval ![a,b,z] sigmaB +
      (z*a*b + z^5) * MvPolynomial.eval ![a,b,z] sigmaG +
      (1-a^2-b^2-z^2) * MvPolynomial.eval ![a,b,z] sigmaBall := by
  have h := congrArg (MvPolynomial.eval ![a,b,z]) hcert
  simp only [map_add, map_mul, sharpArchimedeanObjective,
    sharpArchimedeanZ, sharpArchimedeanA, sharpArchimedeanB,
    sharpArchimedeanW, sharpArchimedeanGenerators,
    KrivineStengle.sharpSeedGenerators, KrivineStengle.sharpSeedW,
    KrivineStengle.sharpSeedA, KrivineStengle.sharpSeedB,
    KrivineStengle.sharpSeedZ, MvPolynomial.eval_X, MvPolynomial.eval_C] at h
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h
  convert h using 1 <;> ring

theorem sharpCertificate_slab_weighted_bounds
    {eps t : Real} (ht0 : 0 < t) (htsmall : t <= (1 : Real) / 64)
    (ht : t = 2 * eps)
    (sigma0 sigmaA sigmaB sigmaG sigmaBall : MvPolynomial (Fin 3) Real)
    (hsigma0 : IsSOS sigma0) (hsigmaA : IsSOS sigmaA)
    (hsigmaB : IsSOS sigmaB) (hsigmaG : IsSOS sigmaG)
    (hsigmaBall : IsSOS sigmaBall)
    (hcert : sharpArchimedeanObjective + MvPolynomial.C eps =
      sigma0 + sigmaA * sharpArchimedeanA +
        sigmaB * sharpArchimedeanB + sigmaG * sharpArchimedeanW +
        sigmaBall * sharpArchimedeanGenerators (3 : Fin 4))
    {a b z : Real} (ha0 : 0 <= a) (ha4 : a <= (1 : Real) / 4)
    (hb0 : 0 <= b) (hb4 : b <= (1 : Real) / 4)
    (hz0 : t <= z) (hz4 : z <= (1 : Real) / 4) :
    MvPolynomial.eval ![a,b,z] sigma0 <= 1 /\
    MvPolynomial.eval ![a,b,z] sigmaBall <= 2 /\
    MvPolynomial.eval ![a,b,z] sigmaG <= 2 / t^4 /\
    a * MvPolynomial.eval ![a,b,z] sigmaA <= 1 /\
    b * MvPolynomial.eval ![a,b,z] sigmaB <= 1 := by
  let e0 := MvPolynomial.eval ![a,b,z] sigma0
  let eA := MvPolynomial.eval ![a,b,z] sigmaA
  let eB := MvPolynomial.eval ![a,b,z] sigmaB
  let eG := MvPolynomial.eval ![a,b,z] sigmaG
  let eBall := MvPolynomial.eval ![a,b,z] sigmaBall
  have he0 : 0 <= e0 := by
    dsimp [e0]
    exact IsSOS_nonneg sigma0 hsigma0 ![a,b,z] (Set.mem_univ _)
  have heA : 0 <= eA := by
    dsimp [eA]
    exact IsSOS_nonneg sigmaA hsigmaA ![a,b,z] (Set.mem_univ _)
  have heB : 0 <= eB := by
    dsimp [eB]
    exact IsSOS_nonneg sigmaB hsigmaB ![a,b,z] (Set.mem_univ _)
  have heG : 0 <= eG := by
    dsimp [eG]
    exact IsSOS_nonneg sigmaG hsigmaG ![a,b,z] (Set.mem_univ _)
  have heBall : 0 <= eBall := by
    dsimp [eBall]
    exact IsSOS_nonneg sigmaBall hsigmaBall ![a,b,z] (Set.mem_univ _)
  have hzpos : 0 < z := ht0.trans_le hz0
  have hepsEq : eps = t / 2 := by rw [ht]; ring
  have hobj : z + eps <= 1 := by rw [hepsEq]; linarith
  have hobjz : z + eps <= 2 * z := by rw [hepsEq]; linarith
  have hw0 : 0 <= z * a * b + z^5 := by positivity
  have hballHalf : (1 : Real) / 2 <= 1 - a^2 - b^2 - z^2 := by
    nlinarith [sq_nonneg ((1 : Real) / 4 - a),
      sq_nonneg ((1 : Real) / 4 - b), sq_nonneg ((1 : Real) / 4 - z)]
  have heq := sharpCertificate_eval sigma0 sigmaA sigmaB sigmaG sigmaBall
    hcert a b z
  change z + eps = e0 + a*eA + b*eB +
    (z*a*b+z^5)*eG + (1-a^2-b^2-z^2)*eBall at heq
  have hAterm : 0 <= a * eA := mul_nonneg ha0 heA
  have hBterm : 0 <= b * eB := mul_nonneg hb0 heB
  have hGterm : 0 <= (z*a*b+z^5) * eG := mul_nonneg hw0 heG
  have hBallterm : 0 <= (1-a^2-b^2-z^2) * eBall :=
    mul_nonneg (by linarith : 0 <= 1-a^2-b^2-z^2) heBall
  have he0le : e0 <= z + eps := by linarith
  have hAle : a * eA <= z + eps := by linarith
  have hBle : b * eB <= z + eps := by linarith
  have hGle : (z*a*b+z^5) * eG <= z + eps := by linarith
  have hBallle : (1-a^2-b^2-z^2) * eBall <= z + eps := by linarith
  have heBallTwo : eBall <= 2 := by nlinarith
  have hz5le : eG * z^5 <= z + eps := by
    calc
      eG * z^5 <= eG * (z*a*b+z^5) := by
        apply mul_le_mul_of_nonneg_left _ heG
        nlinarith [mul_nonneg (mul_nonneg hzpos.le ha0) hb0]
      _ = (z*a*b+z^5) * eG := by ring
      _ <= z + eps := hGle
  have hz4le : eG * z^4 <= 2 := by
    have hzmul : z * (eG * z^4) <= z * 2 := by
      calc
        z * (eG * z^4) = eG * z^5 := by ring
        _ <= z + eps := hz5le
        _ <= 2 * z := hobjz
        _ = z * 2 := by ring
    exact le_of_mul_le_mul_left hzmul hzpos
  have ht4z4 : t^4 <= z^4 := by gcongr
  have ht4le : eG * t^4 <= 2 :=
    (mul_le_mul_of_nonneg_left ht4z4 heG).trans hz4le
  have heGbound : eG <= 2 / t^4 := by
    exact (le_div_iff₀ (pow_pos ht0 4)).2 (by simpa [mul_comm] using ht4le)
  exact ⟨he0le.trans hobj, heBallTwo, heGbound,
    hAle.trans hobj, hBle.trans hobj⟩

def sharpSlabEnvelope (t : Real) (r : Nat) : Real :=
  2 + 8 * Real.exp 6 * (r : Real)^2 + 2 / t^4

theorem sharpCertificate_slab_bounds
    {eps t : Real} {r : Nat} (hr : 2 <= r)
    (ht0 : 0 < t) (htsmall : t <= (1 : Real) / 64)
    (ht : t = 2 * eps)
    (sigma0 sigmaA sigmaB sigmaG sigmaBall : MvPolynomial (Fin 3) Real)
    (hsigma0 : IsSOS sigma0) (hsigmaA : IsSOS sigmaA)
    (hsigmaB : IsSOS sigmaB) (hsigmaG : IsSOS sigmaG)
    (hsigmaBall : IsSOS sigmaBall)
    (hdegree0 : sigma0.totalDegree <= r)
    (hdegreeA : sigmaA.totalDegree <= r)
    (hdegreeB : sigmaB.totalDegree <= r)
    (hdegreeG : sigmaG.totalDegree <= r)
    (hdegreeBall : sigmaBall.totalDegree <= r)
    (hcert : sharpArchimedeanObjective + MvPolynomial.C eps =
      sigma0 + sigmaA * sharpArchimedeanA +
        sigmaB * sharpArchimedeanB + sigmaG * sharpArchimedeanW +
        sigmaBall * sharpArchimedeanGenerators (3 : Fin 4))
    {a b z : Real} (ha0 : 0 <= a) (ha4 : a <= (1 : Real) / 4)
    (hb0 : 0 <= b) (hb4 : b <= (1 : Real) / 4)
    (hz0 : t <= z) (hz4 : z <= (1 : Real) / 4) :
    MvPolynomial.eval ![a,b,z] sigma0 <= sharpSlabEnvelope t r /\
    MvPolynomial.eval ![a,b,z] sigmaA <= sharpSlabEnvelope t r /\
    MvPolynomial.eval ![a,b,z] sigmaB <= sharpSlabEnvelope t r /\
    MvPolynomial.eval ![a,b,z] sigmaG <= sharpSlabEnvelope t r /\
    MvPolynomial.eval ![a,b,z] sigmaBall <= sharpSlabEnvelope t r := by
  have hweighted := sharpCertificate_slab_weighted_bounds ht0 htsmall ht
    sigma0 sigmaA sigmaB sigmaG sigmaBall hsigma0 hsigmaA hsigmaB
    hsigmaG hsigmaBall hcert ha0 ha4 hb0 hb4 hz0 hz4
  have hA : MvPolynomial.eval ![a,b,z] sigmaA <=
      8 * Real.exp 6 * (r : Real)^2 := by
    let p := sharpRestrictA b z sigmaA
    have hdeg : p.natDegree <= r := by
      exact (sharpRestrictA_natDegree_le b z sigmaA).trans hdegreeA
    have hnonneg : forall x : Real, 0 <= x -> x <= (1 : Real) / 4 ->
        0 <= p.eval x := by
      intro x hx0 hx4
      rw [sharpRestrictA_eval]
      exact IsSOS_nonneg sigmaA hsigmaA ![x,b,z] (Set.mem_univ _)
    have hweightedA : forall x : Real, 0 <= x -> x <= (1 : Real) / 4 ->
        x * p.eval x <= 1 := by
      intro x hx0 hx4
      rw [sharpRestrictA_eval]
      exact (sharpCertificate_slab_weighted_bounds ht0 htsmall ht
        sigma0 sigmaA sigmaB sigmaG sigmaBall hsigma0 hsigmaA hsigmaB
        hsigmaG hsigmaBall hcert hx0 hx4 hb0 hb4 hz0 hz4).2.2.2.1
    simpa [p] using
      quarterInterval_face_multiplier_bound hr p hdeg hnonneg hweightedA ha0 ha4
  have hB : MvPolynomial.eval ![a,b,z] sigmaB <=
      8 * Real.exp 6 * (r : Real)^2 := by
    let p := sharpRestrictB a z sigmaB
    have hdeg : p.natDegree <= r := by
      exact (sharpRestrictB_natDegree_le a z sigmaB).trans hdegreeB
    have hnonneg : forall x : Real, 0 <= x -> x <= (1 : Real) / 4 ->
        0 <= p.eval x := by
      intro x hx0 hx4
      rw [sharpRestrictB_eval]
      exact IsSOS_nonneg sigmaB hsigmaB ![a,x,z] (Set.mem_univ _)
    have hweightedB : forall x : Real, 0 <= x -> x <= (1 : Real) / 4 ->
        x * p.eval x <= 1 := by
      intro x hx0 hx4
      rw [sharpRestrictB_eval]
      exact (sharpCertificate_slab_weighted_bounds ht0 htsmall ht
        sigma0 sigmaA sigmaB sigmaG sigmaBall hsigma0 hsigmaA hsigmaB
        hsigmaG hsigmaBall hcert ha0 ha4 hx0 hx4 hz0 hz4).2.2.2.2
    simpa [p] using
      quarterInterval_face_multiplier_bound hr p hdeg hnonneg hweightedB hb0 hb4
  have henv0 : (0 : Real) <= sharpSlabEnvelope t r := by
    unfold sharpSlabEnvelope
    positivity
  have hone : (1 : Real) <= sharpSlabEnvelope t r := by
    unfold sharpSlabEnvelope
    have hterm : 0 <= 8 * Real.exp 6 * (r : Real)^2 + 2 / t^4 := by positivity
    linarith
  have htwo : (2 : Real) <= sharpSlabEnvelope t r := by
    unfold sharpSlabEnvelope
    have hrest : 0 <= 8 * Real.exp 6 * (r : Real)^2 + 2 / t^4 := by
      positivity
    linarith
  refine ⟨hweighted.1.trans hone, ?_, ?_, ?_, hweighted.2.1.trans htwo⟩
  · unfold sharpSlabEnvelope
    nlinarith [show 0 <= 2 / t^4 by positivity]
  · unfold sharpSlabEnvelope
    nlinarith [show 0 <= 2 / t^4 by positivity]
  · exact hweighted.2.2.1.trans (by
      unfold sharpSlabEnvelope
      nlinarith [show 0 <= 8 * Real.exp 6 * (r : Real)^2 by positivity])

def sharpNegativeSlabEnvelope (t : Real) (r : Nat) : Real :=
  Real.exp (100 * (r : Real) * Real.sqrt t) * sharpSlabEnvelope t r

theorem sharpCertificate_negative_slab_bounds
    {eps t : Real} {r : Nat} (hr : 2 <= r)
    (ht0 : 0 < t) (htsmall : t <= (1 : Real) / 64)
    (ht : t = 2 * eps)
    (sigma0 sigmaA sigmaB sigmaG sigmaBall : MvPolynomial (Fin 3) Real)
    (hsigma0 : IsSOS sigma0) (hsigmaA : IsSOS sigmaA)
    (hsigmaB : IsSOS sigmaB) (hsigmaG : IsSOS sigmaG)
    (hsigmaBall : IsSOS sigmaBall)
    (hdegree0 : sigma0.totalDegree <= r)
    (hdegreeA : sigmaA.totalDegree <= r)
    (hdegreeB : sigmaB.totalDegree <= r)
    (hdegreeG : sigmaG.totalDegree <= r)
    (hdegreeBall : sigmaBall.totalDegree <= r)
    (hcert : sharpArchimedeanObjective + MvPolynomial.C eps =
      sigma0 + sigmaA * sharpArchimedeanA +
        sigmaB * sharpArchimedeanB + sigmaG * sharpArchimedeanW +
        sigmaBall * sharpArchimedeanGenerators (3 : Fin 4))
    {a b : Real} (ha0 : 0 <= a) (ha4 : a <= (1 : Real) / 4)
    (hb0 : 0 <= b) (hb4 : b <= (1 : Real) / 4) :
    MvPolynomial.eval ![a,b,-t] sigma0 <= sharpNegativeSlabEnvelope t r /\
    MvPolynomial.eval ![a,b,-t] sigmaA <= sharpNegativeSlabEnvelope t r /\
    MvPolynomial.eval ![a,b,-t] sigmaB <= sharpNegativeSlabEnvelope t r /\
    MvPolynomial.eval ![a,b,-t] sigmaG <= sharpNegativeSlabEnvelope t r /\
    MvPolynomial.eval ![a,b,-t] sigmaBall <= sharpNegativeSlabEnvelope t r := by
  have hextrapolate (sigma : MvPolynomial (Fin 3) Real)
      (hsigma : IsSOS sigma) (hdegree : sigma.totalDegree <= r)
      (hslab : forall z : Real, t <= z -> z <= (1 : Real) / 4 ->
        MvPolynomial.eval ![a,b,z] sigma <= sharpSlabEnvelope t r) :
      MvPolynomial.eval ![a,b,-t] sigma <= sharpNegativeSlabEnvelope t r := by
    let p := sharpRestrictAB a b sigma
    have hdeg : p.natDegree <= r :=
      (sharpRestrictAB_natDegree_le a b sigma).trans hdegree
    have hbound : forall z : Real, t <= z -> z <= (1 : Real) / 4 ->
        |p.eval z| <= sharpSlabEnvelope t r := by
      intro z hz0 hz4
      rw [sharpRestrictAB_eval]
      have hnonneg := IsSOS_nonneg sigma hsigma ![a,b,z] (Set.mem_univ _)
      rw [abs_of_nonneg hnonneg]
      exact hslab z hz0 hz4
    have hext := polynomial_extrapolate_negative_slab hr ht0 htsmall
      p hdeg hbound
    rw [sharpRestrictAB_eval] at hext
    exact (le_abs_self _).trans hext
  have hslab (z : Real) (hz0 : t <= z) (hz4 : z <= (1 : Real) / 4) :=
    sharpCertificate_slab_bounds hr ht0 htsmall ht
      sigma0 sigmaA sigmaB sigmaG sigmaBall hsigma0 hsigmaA hsigmaB
      hsigmaG hsigmaBall hdegree0 hdegreeA hdegreeB hdegreeG hdegreeBall
      hcert ha0 ha4 hb0 hb4 hz0 hz4
  refine ⟨hextrapolate sigma0 hsigma0 hdegree0 (fun z hz0 hz4 =>
      (hslab z hz0 hz4).1),
    hextrapolate sigmaA hsigmaA hdegreeA (fun z hz0 hz4 =>
      (hslab z hz0 hz4).2.1),
    hextrapolate sigmaB hsigmaB hdegreeB (fun z hz0 hz4 =>
      (hslab z hz0 hz4).2.2.1),
    hextrapolate sigmaG hsigmaG hdegreeG (fun z hz0 hz4 =>
      (hslab z hz0 hz4).2.2.2.1),
    hextrapolate sigmaBall hsigmaBall hdegreeBall (fun z hz0 hz4 =>
      (hslab z hz0 hz4).2.2.2.2)⟩

@[simp] theorem sharpSlabRestrictZ_eval (a b z : Real)
    (p : MvPolynomial (Fin 3) Real) :
    MvPolynomial.eval ![a,b] (sharpRestrictZ z p) =
      MvPolynomial.eval ![a,b,z] p := by
  rw [sharpRestrictZ, MvPolynomial.map_aeval]
  have hC : (MvPolynomial.eval ![a,b]).comp
      (algebraMap Real (MvPolynomial (Fin 2) Real)) =
      RingHom.id Real := by
    ext c
    simp
  change MvPolynomial.eval₂
    ((MvPolynomial.eval ![a,b]).comp
      (algebraMap Real (MvPolynomial (Fin 2) Real)))
    (fun i => MvPolynomial.eval ![a,b]
      (![obstructionA, obstructionB, MvPolynomial.C z] i)) p = _
  rw [hC, MvPolynomial.eval₂_id]
  apply congrArg (fun v : Fin 3 -> Real => MvPolynomial.eval v p)
  funext i
  fin_cases i <;> simp [obstructionA, obstructionB,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

def sharpRestrictedTauEnvelope (t : Real) (r : Nat) : Real :=
  (2 / t) * sharpNegativeSlabEnvelope t r

theorem sharpCertificate_restricted_tau_bounds
    {eps t : Real} {r : Nat} (hr : 2 <= r)
    (ht0 : 0 < t) (htsmall : t <= (1 : Real) / 64)
    (ht : t = 2 * eps)
    (sigma0 sigmaA sigmaB sigmaG sigmaBall : MvPolynomial (Fin 3) Real)
    (hsigma0 : IsSOS sigma0) (hsigmaA : IsSOS sigmaA)
    (hsigmaB : IsSOS sigmaB) (hsigmaG : IsSOS sigmaG)
    (hsigmaBall : IsSOS sigmaBall)
    (hdegree0 : sigma0.totalDegree <= r)
    (hdegreeA : sigmaA.totalDegree <= r)
    (hdegreeB : sigmaB.totalDegree <= r)
    (hdegreeG : sigmaG.totalDegree <= r)
    (hdegreeBall : sigmaBall.totalDegree <= r)
    (hcert : sharpArchimedeanObjective + MvPolynomial.C eps =
      sigma0 + sigmaA * sharpArchimedeanA +
        sigmaB * sharpArchimedeanB + sigmaG * sharpArchimedeanW +
        sigmaBall * sharpArchimedeanGenerators (3 : Fin 4))
    {a b : Real} (ha0 : 0 <= a) (ha4 : a <= (1 : Real) / 4)
    (hb0 : 0 <= b) (hb4 : b <= (1 : Real) / 4) :
    MvPolynomial.eval ![a,b] (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigma0)
        <= sharpRestrictedTauEnvelope t r /\
    MvPolynomial.eval ![a,b] (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigmaA)
        <= sharpRestrictedTauEnvelope t r /\
    MvPolynomial.eval ![a,b] (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigmaB)
        <= sharpRestrictedTauEnvelope t r /\
    MvPolynomial.eval ![a,b] (MvPolynomial.C 2 * sharpRestrictZ (-t) sigmaG)
        <= sharpRestrictedTauEnvelope t r /\
    MvPolynomial.eval ![a,b] (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigmaBall)
        <= sharpRestrictedTauEnvelope t r := by
  have hneg := sharpCertificate_negative_slab_bounds hr ht0 htsmall ht
    sigma0 sigmaA sigmaB sigmaG sigmaBall hsigma0 hsigmaA hsigmaB
    hsigmaG hsigmaBall hdegree0 hdegreeA hdegreeB hdegreeG hdegreeBall
    hcert ha0 ha4 hb0 hb4
  have hN : 0 <= sharpNegativeSlabEnvelope t r := by
    unfold sharpNegativeSlabEnvelope sharpSlabEnvelope
    positivity
  have hscale : 0 <= 2/t := by positivity
  have htOne : t <= 1 := htsmall.trans (by norm_num)
  have htwoScale : (2 : Real) <= 2/t := by
    rw [le_div_iff₀ ht0]
    nlinarith
  have hscaled (sigma : MvPolynomial (Fin 3) Real)
      (hsigma : MvPolynomial.eval ![a,b,-t] sigma <=
        sharpNegativeSlabEnvelope t r) :
      MvPolynomial.eval ![a,b]
          (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigma) <=
        sharpRestrictedTauEnvelope t r := by
    calc
      MvPolynomial.eval ![a,b]
          (MvPolynomial.C (2/t) * sharpRestrictZ (-t) sigma) =
          (2/t) * MvPolynomial.eval ![a,b,-t] sigma := by
            simp [sharpSlabRestrictZ_eval]
      _ <= (2/t) * sharpNegativeSlabEnvelope t r :=
        mul_le_mul_of_nonneg_left hsigma hscale
      _ = sharpRestrictedTauEnvelope t r := rfl
  refine ⟨hscaled sigma0 hneg.1, hscaled sigmaA hneg.2.1,
    hscaled sigmaB hneg.2.2.1, ?_, hscaled sigmaBall hneg.2.2.2.2⟩
  calc
    MvPolynomial.eval ![a,b]
        (MvPolynomial.C 2 * sharpRestrictZ (-t) sigmaG) =
        2 * MvPolynomial.eval ![a,b,-t] sigmaG := by
          simp [sharpSlabRestrictZ_eval]
    _ <= 2 * sharpNegativeSlabEnvelope t r :=
      mul_le_mul_of_nonneg_left hneg.2.2.2.1 (by norm_num)
    _ <= (2/t) * sharpNegativeSlabEnvelope t r :=
      mul_le_mul_of_nonneg_right htwoScale hN
    _ = sharpRestrictedTauEnvelope t r := rfl

end OptimalConvergenceRates.GeneralArchimedean
