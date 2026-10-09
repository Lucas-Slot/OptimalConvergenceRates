/-
  Algebraic core of Chebyshev elimination of one artificial constraint.
-/
import OptimalConvergenceRates.GeneralArchimedean.HalfLineCertificate
import OptimalConvergenceRates.GeneralArchimedean.ModuleOrder

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates
namespace GeneralArchimedean

variable {n m : ℕ}

/-- The globally nonnegative auxiliary polynomial in the elimination
identity. -/
def eliminationA (epsilon c : ℝ) (w : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.X + Polynomial.C epsilon + Polynomial.C c * w

/-- The half-line nonnegative auxiliary polynomial in the elimination
identity. -/
def eliminationB (epsilon c : ℝ) (w : Polynomial ℝ) : Polynomial ℝ :=
  eliminationA epsilon c w - Polynomial.X * w

theorem eliminationA_natDegree_le
    (epsilon c : ℝ) (w : Polynomial ℝ) :
    (eliminationA epsilon c w).natDegree ≤ 1 + w.natDegree := by
  unfold eliminationA
  calc
    (Polynomial.X + Polynomial.C epsilon +
        Polynomial.C c * w).natDegree ≤
      max (Polynomial.X + Polynomial.C epsilon).natDegree
        (Polynomial.C c * w).natDegree :=
      Polynomial.natDegree_add_le _ _
    _ ≤ 1 + w.natDegree := by
      apply max_le
      · exact (Polynomial.natDegree_add_le _ _).trans (by simp)
      · exact Polynomial.natDegree_mul_le.trans (by simp)

theorem eliminationB_natDegree_le
    (epsilon c : ℝ) (w : Polynomial ℝ) :
    (eliminationB epsilon c w).natDegree ≤ 1 + w.natDegree := by
  unfold eliminationB
  calc
    (eliminationA epsilon c w - Polynomial.X * w).natDegree ≤
        max (eliminationA epsilon c w).natDegree
          (Polynomial.X * w).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ 1 + w.natDegree := by
      apply max_le
      · exact eliminationA_natDegree_le epsilon c w
      · exact Polynomial.natDegree_mul_le.trans (by simp)
/-- The exact analytic interface required by the elimination argument.  A
concrete Chebyshev construction only has to provide an SOS weight bounded by
one on `[0,U]` and growing quickly enough on the negative half-line. -/
structure EliminationWeight (epsilon c U : ℝ) where
  w : Polynomial ℝ
  isSOS : IsSOSUni w
  le_one_on_interval :
    ∀ u : ℝ, u ∈ Set.Icc 0 U → w.eval u ≤ 1
  negative_growth :
    ∀ v : ℝ, epsilon ≤ v → v ≤ epsilon + c * w.eval (-v)

/-- The global sign condition for the first auxiliary polynomial follows
directly from the two defining properties of an elimination weight. -/
theorem EliminationWeight.eliminationA_nonneg
    {epsilon c U : ℝ} (W : EliminationWeight epsilon c U)
    (hepsilon : 0 ≤ epsilon) (hc : 0 ≤ c) :
    ∀ u : ℝ, 0 ≤ (eliminationA epsilon c W.w).eval u := by
  intro u
  have hwu : 0 ≤ W.w.eval u := W.isSOS.eval_nonneg u
  by_cases hu : -epsilon ≤ u
  · have hbase : 0 ≤ u + epsilon := by linarith
    have hcw : 0 ≤ c * W.w.eval u := mul_nonneg hc hwu
    have : 0 ≤ u + epsilon + c * W.w.eval u :=
      add_nonneg hbase hcw
    simpa [eliminationA] using this
  · have hv : epsilon ≤ -u := by linarith
    have hgrowth := W.negative_growth (-u) hv
    have hgrowth' : -u ≤ epsilon + c * W.w.eval u := by
      simpa only [neg_neg] using hgrowth
    have : 0 ≤ u + epsilon + c * W.w.eval u := by linarith
    simpa [eliminationA] using this

/-- The interval upper bound on the weight supplies the half-line sign
condition for the second auxiliary polynomial. -/
theorem EliminationWeight.eliminationB_nonneg
    {epsilon c U : ℝ} (W : EliminationWeight epsilon c U)
    (hepsilon : 0 ≤ epsilon) (hc : 0 ≤ c) :
    ∀ u : ℝ, u ≤ U →
      0 ≤ (eliminationB epsilon c W.w).eval u := by
  intro u huU
  have hwu : 0 ≤ W.w.eval u := W.isSOS.eval_nonneg u
  by_cases hu : u ≤ 0
  · have hA := W.eliminationA_nonneg hepsilon hc u
    have huw : u * W.w.eval u ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hu hwu
    have : 0 ≤ (eliminationA epsilon c W.w).eval u -
        u * W.w.eval u := by
      linarith
    simpa [eliminationB] using this
  · have hu0 : 0 ≤ u := le_of_not_ge hu
    have hwle : W.w.eval u ≤ 1 :=
      W.le_one_on_interval u ⟨hu0, huU⟩
    have hcw : 0 ≤ c * W.w.eval u := mul_nonneg hc hwu
    have huone : 0 ≤ u * (1 - W.w.eval u) :=
      mul_nonneg hu0 (sub_nonneg.mpr hwle)
    have : 0 ≤ u + epsilon + c * W.w.eval u -
        u * W.w.eval u := by
      nlinarith
    simpa [eliminationB, eliminationA] using this


/-- The exact algebraic identity behind Chebyshev elimination. -/
theorem elimination_identity
    (q sigma tau : MvPolynomial (Fin n) ℝ)
    (epsilon c : ℝ) (w : Polynomial ℝ)
    (hrelation : q * tau = C c + sigma) :
    q + C epsilon =
      polynomialSubst q w * sigma +
        polynomialSubst q (eliminationA epsilon c w) * (1 - tau) +
        polynomialSubst q (eliminationB epsilon c w) * tau := by
  let W := polynomialSubst q w
  have hAeval :
      polynomialSubst q (eliminationA epsilon c w) =
        q + C epsilon + C c * W := by
    simp [eliminationA, polynomialSubst, W]
  have hBeval :
      polynomialSubst q (eliminationB epsilon c w) =
        (q + C epsilon + C c * W) - q * W := by
    calc
      polynomialSubst q (eliminationB epsilon c w) =
          polynomialSubst q (eliminationA epsilon c w) -
            polynomialSubst q (Polynomial.X * w) := by
        simp only [eliminationB, polynomialSubst, map_sub]
      _ = (q + C epsilon + C c * W) - q * W := by
        rw [hAeval, polynomialSubst_mul, polynomialSubst_X]
  rw [hAeval, hBeval]
  change q + C epsilon =
    W * sigma + (q + C epsilon + C c * W) * (1 - tau) +
      ((q + C epsilon + C c * W) - q * W) * tau
  calc
    q + C epsilon =
        q + C epsilon + W * (C c + sigma - q * tau) := by
      rw [hrelation]
      ring
    _ = _ := by ring


/-- Degree-tracked version of the algebraic elimination step.  The three
summands are placed at one explicit common truncation order. -/
theorem eliminate_artificial_constraint_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (q sigma tau : MvPolynomial (Fin n) ℝ)
    (epsilon c U : ℝ) (w : Polynomial ℝ)
    {rSigma rTau rU : ℕ}
    (hrelation : q * tau = C c + sigma)
    (hsigma : sigma ∈ GenQuadraticModule g rSigma)
    (htau : IsSOS tau)
    (hone_tau : 1 - tau ∈ GenQuadraticModule g rTau)
    (hUq : C U - q ∈ GenQuadraticModule g rU)
    (hw : IsSOSUni w)
    (hA : ∀ u : ℝ, 0 ≤ (eliminationA epsilon c w).eval u)
    (hB : ∀ u : ℝ, u ≤ U →
      0 ≤ (eliminationB epsilon c w).eval u) :
    q + C epsilon ∈ GenQuadraticModule g
      (max
        (rSigma + w.natDegree * q.totalDegree)
        (max
          (rTau + (eliminationA epsilon c w).natDegree * q.totalDegree)
          (rU + 2 * (eliminationB epsilon c w).natDegree *
              q.totalDegree + tau.totalDegree))) := by
  let rFirst := rSigma + w.natDegree * q.totalDegree
  let rSecond :=
    rTau + (eliminationA epsilon c w).natDegree * q.totalDegree
  let rThird :=
    rU + 2 * (eliminationB epsilon c w).natDegree *
      q.totalDegree + tau.totalDegree
  let R := max rFirst (max rSecond rThird)
  have hwq : IsSOS (polynomialSubst q w) :=
    isSOS_polynomialSubst q hw
  have hwqDegree :
      (polynomialSubst q w).totalDegree ≤
        w.natDegree * q.totalDegree :=
    polynomialSubst_totalDegree_le q w
  have hfirstRaw :=
    genQuadraticModule_sos_mul hwq hsigma
  have hfirst : polynomialSubst q w * sigma ∈
      GenQuadraticModule g R := by
    apply GenQuadraticModule_mono _ hfirstRaw
    exact (Nat.add_le_add_left hwqDegree rSigma).trans
      (le_max_left rFirst (max rSecond rThird))
  have hAqSOS : IsSOS
      (polynomialSubst q (eliminationA epsilon c w)) :=
    isSOS_polynomialSubst q
      (IsSOSUni_of_nonneg (eliminationA epsilon c w) hA)
  have hAqDegree :
      (polynomialSubst q (eliminationA epsilon c w)).totalDegree ≤
        (eliminationA epsilon c w).natDegree * q.totalDegree :=
    polynomialSubst_totalDegree_le q (eliminationA epsilon c w)
  have hsecondRaw :=
    genQuadraticModule_sos_mul hAqSOS hone_tau
  have hsecond :
      polynomialSubst q (eliminationA epsilon c w) * (1 - tau) ∈
        GenQuadraticModule g R := by
    apply GenQuadraticModule_mono _ hsecondRaw
    exact (Nat.add_le_add_left hAqDegree rTau).trans
      ((le_max_left rSecond rThird).trans
        (le_max_right rFirst (max rSecond rThird)))
  obtain ⟨Bcert⟩ :=
    halfLineCertificate_nonempty U (eliminationB epsilon c w) hB
  have hBq := Bcert.subst_mem_at q hUq
  have hthirdRaw := genQuadraticModule_sos_mul htau hBq
  have hthird :
      polynomialSubst q (eliminationB epsilon c w) * tau ∈
        GenQuadraticModule g R := by
    have hraw : tau * polynomialSubst q
          (eliminationB epsilon c w) ∈
        GenQuadraticModule g rThird := by
      simpa [rThird, Nat.add_assoc] using hthirdRaw
    have hmono := GenQuadraticModule_mono
      ((le_max_right rSecond rThird).trans
        (le_max_right rFirst (max rSecond rThird))) hraw
    simpa [mul_comm] using hmono
  have hsum := GenQuadraticModule_add hfirst
    (GenQuadraticModule_add hsecond hthird)
  rw [elimination_identity q sigma tau epsilon c w hrelation]
  simpa [R, rFirst, rSecond, rThird, add_assoc] using hsum
/-- Once the univariate sign facts and the normalized-multiplier envelope are
available, the artificial constraint can be eliminated inside any
Archimedean quadratic module. -/
theorem eliminate_artificial_constraint
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (q sigma tau : MvPolynomial (Fin n) ℝ)
    (epsilon c U : ℝ) (w : Polynomial ℝ)
    (hrelation : q * tau = C c + sigma)
    (hsigma : QuadraticModuleMem g sigma)
    (htau : IsSOS tau)
    (hone_tau : QuadraticModuleMem g (1 - tau))
    (hUq : QuadraticModuleMem g (C U - q))
    (hw : IsSOSUni w)
    (hA : ∀ u : ℝ, 0 ≤ (eliminationA epsilon c w).eval u)
    (hB : ∀ u : ℝ, u ≤ U →
      0 ≤ (eliminationB epsilon c w).eval u) :
    QuadraticModuleMem g (q + C epsilon) := by
  have hwq : IsSOS (polynomialSubst q w) :=
    isSOS_polynomialSubst q hw
  have hfirst : QuadraticModuleMem g
      (polynomialSubst q w * sigma) :=
    QuadraticModuleMem.sos_mul hwq hsigma
  have hAqSOS : IsSOS
      (polynomialSubst q (eliminationA epsilon c w)) :=
    isSOS_polynomialSubst q
      (IsSOSUni_of_nonneg (eliminationA epsilon c w) hA)
  have hsecond : QuadraticModuleMem g
      (polynomialSubst q (eliminationA epsilon c w) * (1 - tau)) :=
    QuadraticModuleMem.sos_mul hAqSOS hone_tau
  obtain ⟨Bcert⟩ :=
    halfLineCertificate_nonempty U (eliminationB epsilon c w) hB
  have hBq : QuadraticModuleMem g
      (polynomialSubst q (eliminationB epsilon c w)) :=
    Bcert.subst_mem q hUq
  have hthird : QuadraticModuleMem g
      (polynomialSubst q (eliminationB epsilon c w) * tau) := by
    simpa [mul_comm] using QuadraticModuleMem.sos_mul htau hBq
  have hsum := hfirst.add (hsecond.add hthird)
  rw [elimination_identity q sigma tau epsilon c w hrelation]
  simpa [add_assoc] using hsum

/-- Reformulation in the variables of a refutation
-1 = s - (p+epsilon)t.  The analytic Chebyshev choice of w and the
coefficient envelope for 1-tau are kept explicit. -/
theorem eliminate_refutation
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (p s t : MvPolynomial (Fin n) ℝ)
    (epsilon Czero U : ℝ) (w : Polynomial ℝ)
    (hCzero : 0 < Czero)
    (hrefute : (-1 : MvPolynomial (Fin n) ℝ) =
      s - (p + C epsilon) * t)
    (hs : QuadraticModuleMem g s)
    (ht : IsSOS t)
    (hone_tau : QuadraticModuleMem g
      (1 - C Czero⁻¹ * t))
    (hUq : QuadraticModuleMem g
      (C U - (p + C epsilon)))
    (hw : IsSOSUni w)
    (hA : ∀ u : ℝ,
      0 ≤ (eliminationA epsilon Czero⁻¹ w).eval u)
    (hB : ∀ u : ℝ, u ≤ U →
      0 ≤ (eliminationB epsilon Czero⁻¹ w).eval u) :
    QuadraticModuleMem g (p + C (2 * epsilon)) := by
  let q := p + C epsilon
  let tau := C Czero⁻¹ * t
  let sigma := C Czero⁻¹ * s
  have hsigma : QuadraticModuleMem g sigma := by
    exact hs.sos_mul (IsSOS_C_nonneg Czero⁻¹ (inv_nonneg.mpr hCzero.le))
  have htau : IsSOS tau :=
    IsSOS_mul (IsSOS_C_nonneg Czero⁻¹ (inv_nonneg.mpr hCzero.le)) ht
  have hqt : (p + C epsilon) * t = s + 1 := by
    linear_combination hrefute
  have hrelation : q * tau = C Czero⁻¹ + sigma := by
    dsimp [q, tau, sigma]
    calc
      (p + C epsilon) * (C Czero⁻¹ * t) =
          C Czero⁻¹ * ((p + C epsilon) * t) := by ring
      _ = C Czero⁻¹ * (s + 1) := by rw [hqt]
      _ = C Czero⁻¹ + C Czero⁻¹ * s := by ring
  have helim := eliminate_artificial_constraint q sigma tau
    epsilon Czero⁻¹ U w hrelation hsigma htau
    (by simpa [tau] using hone_tau) (by simpa [q] using hUq)
    hw hA hB
  have heq : q + C epsilon = p + C (2 * epsilon) := by
    dsimp [q]
    calc
      p + C epsilon + C epsilon = p + (C epsilon + C epsilon) := by ring
      _ = p + C (epsilon + epsilon) := by rw [map_add]
      _ = p + C (2 * epsilon) := by
        rw [show epsilon + epsilon = 2 * epsilon by ring]
  rw [← heq]
  exact helim


/-- Degree-tracked Chebyshev elimination for a normalized refutation. -/
theorem eliminate_refutation_of_weight_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (p s t : MvPolynomial (Fin n) ℝ)
    (epsilon Czero U : ℝ)
    {rS rTau rU : ℕ}
    (hCzero : 0 < Czero)
    (hepsilon : 0 ≤ epsilon)
    (hrefute : (-1 : MvPolynomial (Fin n) ℝ) =
      s - (p + C epsilon) * t)
    (hs : s ∈ GenQuadraticModule g rS)
    (ht : IsSOS t)
    (hone_tau : 1 - C Czero⁻¹ * t ∈ GenQuadraticModule g rTau)
    (hUq : C U - (p + C epsilon) ∈ GenQuadraticModule g rU)
    (W : EliminationWeight epsilon Czero⁻¹ U) :
    p + C (2 * epsilon) ∈ GenQuadraticModule g
      (max
        (rS + W.w.natDegree * (p + C epsilon).totalDegree)
        (max
          (rTau +
            (eliminationA epsilon Czero⁻¹ W.w).natDegree *
              (p + C epsilon).totalDegree)
          (rU + 2 *
              (eliminationB epsilon Czero⁻¹ W.w).natDegree *
              (p + C epsilon).totalDegree +
            (C Czero⁻¹ * t).totalDegree))) := by
  let q := p + C epsilon
  let tau := C Czero⁻¹ * t
  let sigma := C Czero⁻¹ * s
  have hconstSOS : IsSOS
      (C Czero⁻¹ : MvPolynomial (Fin n) ℝ) :=
    IsSOS_C_nonneg Czero⁻¹ (inv_nonneg.mpr hCzero.le)
  have hsigma : sigma ∈ GenQuadraticModule g rS := by
    have hraw := genQuadraticModule_sos_mul hconstSOS hs
    simpa [sigma] using hraw
  have htau : IsSOS tau := by
    exact IsSOS_mul hconstSOS ht
  have hqt : (p + C epsilon) * t = s + 1 := by
    linear_combination hrefute
  have hrelation : q * tau = C Czero⁻¹ + sigma := by
    dsimp [q, tau, sigma]
    calc
      (p + C epsilon) * (C Czero⁻¹ * t) =
          C Czero⁻¹ * ((p + C epsilon) * t) := by ring
      _ = C Czero⁻¹ * (s + 1) := by rw [hqt]
      _ = C Czero⁻¹ + C Czero⁻¹ * s := by ring
  have helim := eliminate_artificial_constraint_at q sigma tau
    epsilon Czero⁻¹ U W.w hrelation hsigma htau
    (by simpa [tau] using hone_tau) (by simpa [q] using hUq)
    W.isSOS
    (W.eliminationA_nonneg hepsilon (inv_nonneg.mpr hCzero.le))
    (W.eliminationB_nonneg hepsilon (inv_nonneg.mpr hCzero.le))
  have heq : q + C epsilon = p + C (2 * epsilon) := by
    dsimp [q]
    calc
      p + C epsilon + C epsilon = p + (C epsilon + C epsilon) := by ring
      _ = p + C (epsilon + epsilon) := by rw [map_add]
      _ = p + C (2 * epsilon) := by
        congr 1
        ring
  rw [← heq]
  simpa [q, tau, sigma] using helim

/-- Coarse degree bound for the tracked elimination theorem. -/
theorem eliminate_refutation_of_weight_at_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (p s t : MvPolynomial (Fin n) ℝ)
    (epsilon Czero U : ℝ)
    {rS rTau rU N d dT : ℕ}
    (hCzero : 0 < Czero)
    (hepsilon : 0 ≤ epsilon)
    (hrefute : (-1 : MvPolynomial (Fin n) ℝ) =
      s - (p + C epsilon) * t)
    (hs : s ∈ GenQuadraticModule g rS)
    (ht : IsSOS t)
    (hone_tau : 1 - C Czero⁻¹ * t ∈ GenQuadraticModule g rTau)
    (hUq : C U - (p + C epsilon) ∈ GenQuadraticModule g rU)
    (W : EliminationWeight epsilon Czero⁻¹ U)
    (hWdegree : W.w.natDegree ≤ 2 * N)
    (hqDegree : (p + C epsilon).totalDegree ≤ d)
    (htDegree : t.totalDegree ≤ dT) :
    p + C (2 * epsilon) ∈ GenQuadraticModule g
      (max
        (rS + 2 * N * d)
        (max
          (rTau + (1 + 2 * N) * d)
          (rU + 2 * (1 + 2 * N) * d + dT))) := by
  have hcert := eliminate_refutation_of_weight_at
    p s t epsilon Czero U hCzero hepsilon hrefute hs ht
    hone_tau hUq W
  apply GenQuadraticModule_mono _ hcert
  apply max_le
  · exact (Nat.add_le_add_left
      (Nat.mul_le_mul hWdegree hqDegree) rS).trans
      (le_max_left _ _)
  · apply max_le
    · have hAdegree :
          (eliminationA epsilon Czero⁻¹ W.w).natDegree ≤
            1 + 2 * N :=
        (eliminationA_natDegree_le _ _ _).trans
          (Nat.add_le_add_left hWdegree 1)
      exact (Nat.add_le_add_left
        (Nat.mul_le_mul hAdegree hqDegree) rTau).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · have hBdegree :
          (eliminationB epsilon Czero⁻¹ W.w).natDegree ≤
            1 + 2 * N :=
        (eliminationB_natDegree_le _ _ _).trans
          (Nat.add_le_add_left hWdegree 1)
      have hsubst :
          2 * (eliminationB epsilon Czero⁻¹ W.w).natDegree *
              (p + C epsilon).totalDegree ≤
            2 * (1 + 2 * N) * d := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_left 2 hBdegree) hqDegree
      have htauDegree :
          (C Czero⁻¹ * t).totalDegree ≤ dT := by
        calc
          (C Czero⁻¹ * t).totalDegree ≤
              (C Czero⁻¹ : MvPolynomial (Fin n) ℝ).totalDegree +
                t.totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ ≤ 0 + dT := Nat.add_le_add
            (MvPolynomial.totalDegree_C _).le htDegree
          _ = dT := Nat.zero_add _
      have hthird :
          rU + 2 * (eliminationB epsilon Czero⁻¹ W.w).natDegree *
                (p + C epsilon).totalDegree +
              (C Czero⁻¹ * t).totalDegree ≤
            rU + 2 * (1 + 2 * N) * d + dT :=
        Nat.add_le_add (Nat.add_le_add_left hsubst rU) htauDegree
      exact hthird.trans
        ((le_max_right _ _).trans (le_max_right _ _))
/-- Chebyshev elimination stated only in terms of the reusable analytic
weight interface. -/
theorem eliminate_refutation_of_weight
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (p s t : MvPolynomial (Fin n) ℝ)
    (epsilon Czero U : ℝ)
    (hCzero : 0 < Czero)
    (hepsilon : 0 ≤ epsilon)
    (hrefute : (-1 : MvPolynomial (Fin n) ℝ) =
      s - (p + C epsilon) * t)
    (hs : QuadraticModuleMem g s)
    (ht : IsSOS t)
    (hone_tau : QuadraticModuleMem g
      (1 - C Czero⁻¹ * t))
    (hUq : QuadraticModuleMem g
      (C U - (p + C epsilon)))
    (W : EliminationWeight epsilon Czero⁻¹ U) :
    QuadraticModuleMem g (p + C (2 * epsilon)) :=
  eliminate_refutation p s t epsilon Czero U W.w hCzero
    hrefute hs ht hone_tau hUq W.isSOS
    (W.eliminationA_nonneg hepsilon (inv_nonneg.mpr hCzero.le))
    (W.eliminationB_nonneg hepsilon (inv_nonneg.mpr hCzero.le))

end GeneralArchimedean
end OptimalConvergenceRates

end
