/-
  Chebyshev elimination performed directly inside a preordering.
-/
import OptimalConvergenceRates.GeneralCompact.DirectRefutation
import OptimalConvergenceRates.GeneralArchimedean.ChebyshevWeight

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralCompact

variable {n m : ℕ}

private theorem sos_mem_preordering_at
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : IsSOS p) (hdegree : p.totalDegree ≤ r) :
    p ∈ GenPreordering g r :=
  GenQuadraticModule_subset_GenPreordering
    (genQuadraticModule_sos g hp hdegree)

/-- Substitute a half-line certificate into a preordering certificate for
its boundary polynomial. -/
theorem halfLine_subst_preordering_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {U : ℝ} {p : Polynomial ℝ}
    (cert : GeneralArchimedean.HalfLineCertificate U p)
    (a : MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hUa : C U - a ∈ GenPreordering g r) :
    GeneralArchimedean.polynomialSubst a p ∈ GenPreordering g
      (r + 2 * p.natDegree * a.totalDegree) := by
  let d := 2 * p.natDegree * a.totalDegree
  have hzeroDegree :
      (GeneralArchimedean.polynomialSubst a cert.sigmaZero).totalDegree ≤ d :=
    (GeneralArchimedean.polynomialSubst_totalDegree_le a cert.sigmaZero).trans
      (Nat.mul_le_mul_right a.totalDegree cert.degreeZero_le)
  have hzero : GeneralArchimedean.polynomialSubst a cert.sigmaZero ∈
      GenPreordering g d :=
    sos_mem_preordering_at g
      (GeneralArchimedean.isSOS_polynomialSubst a cert.isSOSZero) hzeroDegree
  have hboundaryDegree :
      (GeneralArchimedean.polynomialSubst a cert.sigmaBoundary).totalDegree ≤ d :=
    (GeneralArchimedean.polynomialSubst_totalDegree_le a cert.sigmaBoundary).trans
      (Nat.mul_le_mul_right a.totalDegree cert.degreeBoundary_le)
  have hboundarySOS : IsSOS
      (GeneralArchimedean.polynomialSubst a cert.sigmaBoundary) :=
    GeneralArchimedean.isSOS_polynomialSubst a cert.isSOSBoundary
  have hboundaryMultiplier :
      GeneralArchimedean.polynomialSubst a cert.sigmaBoundary ∈
        GenPreordering g d :=
    sos_mem_preordering_at g hboundarySOS hboundaryDegree
  have hboundaryRaw :=
    KrivineStengle.genPreordering_mul hboundaryMultiplier hUa
  have hboundary :
      GeneralArchimedean.polynomialSubst a cert.sigmaBoundary * (C U - a) ∈
        GenPreordering g (r + d) := by
    simpa [Nat.add_comm] using hboundaryRaw
  have hzero' : GeneralArchimedean.polynomialSubst a cert.sigmaZero ∈
      GenPreordering g (r + d) :=
    GenPreordering_mono (Nat.le_add_left d r) hzero
  have hsum := KrivineStengle.genPreordering_add hzero' hboundary
  have hid := congrArg (Polynomial.aeval a) cert.identity
  have hpoly : GeneralArchimedean.polynomialSubst a p =
      GeneralArchimedean.polynomialSubst a cert.sigmaZero +
        GeneralArchimedean.polynomialSubst a cert.sigmaBoundary * (C U - a) := by
    simpa [GeneralArchimedean.polynomialSubst, map_add, map_mul, map_sub,
      mul_comm] using hid
  rw [hpoly]
  exact GenPreordering_mono (by omega) hsum

/-- The algebraic elimination step with all three factors certified in the
same preordering. The last factor uses closure under multiplication, which
is exactly where the Schmüdgen proof saves two logarithms. -/
theorem eliminate_artificial_constraint_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (q sigma tau : MvPolynomial (Fin n) ℝ)
    (epsilon c U : ℝ) (w : Polynomial ℝ)
    {rSigma rTau rOne rU : ℕ}
    (hrelation : q * tau = C c + sigma)
    (hsigma : sigma ∈ GenPreordering g rSigma)
    (htau : tau ∈ GenPreordering g rTau)
    (hone_tau : 1 - tau ∈ GenPreordering g rOne)
    (hUq : C U - q ∈ GenPreordering g rU)
    (hw : IsSOSUni w)
    (hA : ∀ u : ℝ, 0 ≤
      (GeneralArchimedean.eliminationA epsilon c w).eval u)
    (hB : ∀ u : ℝ, u ≤ U → 0 ≤
      (GeneralArchimedean.eliminationB epsilon c w).eval u) :
    q + C epsilon ∈ GenPreordering g
      (max
        (rSigma + w.natDegree * q.totalDegree)
        (max
          (rOne +
            (GeneralArchimedean.eliminationA epsilon c w).natDegree *
              q.totalDegree)
          (rU + 2 *
              (GeneralArchimedean.eliminationB epsilon c w).natDegree *
                q.totalDegree + rTau))) := by
  let dW := w.natDegree * q.totalDegree
  let dA := (GeneralArchimedean.eliminationA epsilon c w).natDegree *
    q.totalDegree
  let dB := 2 * (GeneralArchimedean.eliminationB epsilon c w).natDegree *
    q.totalDegree
  let rFirst := rSigma + dW
  let rSecond := rOne + dA
  let rThird := rU + dB + rTau
  let R := max rFirst (max rSecond rThird)
  have hwqDegree :
      (GeneralArchimedean.polynomialSubst q w).totalDegree ≤ dW :=
    GeneralArchimedean.polynomialSubst_totalDegree_le q w
  have hwq : GeneralArchimedean.polynomialSubst q w ∈
      GenPreordering g dW :=
    sos_mem_preordering_at g
      (GeneralArchimedean.isSOS_polynomialSubst q hw) hwqDegree
  have hfirstRaw := KrivineStengle.genPreordering_mul hwq hsigma
  have hfirst : GeneralArchimedean.polynomialSubst q w * sigma ∈
      GenPreordering g R := by
    exact GenPreordering_mono
      ((le_max_left rFirst (max rSecond rThird)))
      (by simpa [rFirst, dW, Nat.add_comm] using hfirstRaw)
  have hAqSOS : IsSOS (GeneralArchimedean.polynomialSubst q
      (GeneralArchimedean.eliminationA epsilon c w)) :=
    GeneralArchimedean.isSOS_polynomialSubst q
      (IsSOSUni_of_nonneg _ hA)
  have hAqDegree :
      (GeneralArchimedean.polynomialSubst q
        (GeneralArchimedean.eliminationA epsilon c w)).totalDegree ≤ dA :=
    GeneralArchimedean.polynomialSubst_totalDegree_le q _
  have hAq := sos_mem_preordering_at g hAqSOS hAqDegree
  have hsecondRaw := KrivineStengle.genPreordering_mul hAq hone_tau
  have hsecond : GeneralArchimedean.polynomialSubst q
      (GeneralArchimedean.eliminationA epsilon c w) * (1 - tau) ∈
      GenPreordering g R := by
    exact GenPreordering_mono
      ((le_max_left rSecond rThird).trans
        (le_max_right rFirst (max rSecond rThird)))
      (by simpa [rSecond, dA, Nat.add_comm] using hsecondRaw)
  obtain ⟨Bcert⟩ :=
    GeneralArchimedean.halfLineCertificate_nonempty U
      (GeneralArchimedean.eliminationB epsilon c w) hB
  have hBq := halfLine_subst_preordering_at Bcert q hUq
  have hthirdRaw := KrivineStengle.genPreordering_mul hBq htau
  have hthird : GeneralArchimedean.polynomialSubst q
      (GeneralArchimedean.eliminationB epsilon c w) * tau ∈
      GenPreordering g R := by
    exact GenPreordering_mono
      ((le_max_right rSecond rThird).trans
        (le_max_right rFirst (max rSecond rThird)))
      (by simpa [rThird, dB, Nat.add_assoc] using hthirdRaw)
  have hsum := KrivineStengle.genPreordering_add hfirst
    (KrivineStengle.genPreordering_add hsecond hthird)
  rw [GeneralArchimedean.elimination_identity q sigma tau epsilon c w hrelation]
  simpa [R, rFirst, rSecond, rThird, dW, dA, dB, add_assoc] using hsum

/-- Degree-tracked elimination for a normalized direct refutation. -/
theorem eliminate_refutation_of_weight_at_bound
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (p s t : MvPolynomial (Fin n) ℝ)
    (epsilon Czero U : ℝ)
    {rS rT rOne rU N d : ℕ}
    (hCzero : 0 < Czero)
    (hepsilon : 0 ≤ epsilon)
    (hrefute : (-1 : MvPolynomial (Fin n) ℝ) =
      s - (p + C epsilon) * t)
    (hs : s ∈ GenPreordering g rS)
    (ht : t ∈ GenPreordering g rT)
    (hone_tau : 1 - C Czero⁻¹ * t ∈ GenPreordering g rOne)
    (hUq : C U - (p + C epsilon) ∈ GenPreordering g rU)
    (W : GeneralArchimedean.EliminationWeight epsilon Czero⁻¹ U)
    (hWdegree : W.w.natDegree ≤ 2 * N)
    (hqDegree : (p + C epsilon).totalDegree ≤ d) :
    p + C (2 * epsilon) ∈ GenPreordering g
      (max
        (rS + 2 * N * d)
        (max
          (rOne + (1 + 2 * N) * d)
          (rU + 2 * (1 + 2 * N) * d + rT))) := by
  let q := p + C epsilon
  let tau := C Czero⁻¹ * t
  let sigma := C Czero⁻¹ * s
  have hcMem : (C Czero⁻¹ : MvPolynomial (Fin n) ℝ) ∈
      GenPreordering g 0 :=
    KrivineStengle.genPreordering_C_nonneg g
      (inv_nonneg.mpr hCzero.le)
  have hsigma : sigma ∈ GenPreordering g rS := by
    simpa [sigma] using KrivineStengle.genPreordering_mul hcMem hs
  have htau : tau ∈ GenPreordering g rT := by
    simpa [tau] using KrivineStengle.genPreordering_mul hcMem ht
  have hqt : (p + C epsilon) * t = s + 1 := by
    linear_combination hrefute
  have hrelation : q * tau = C Czero⁻¹ + sigma := by
    dsimp [q, tau, sigma]
    calc
      (p + C epsilon) * (C Czero⁻¹ * t) =
          C Czero⁻¹ * ((p + C epsilon) * t) := by ring
      _ = C Czero⁻¹ * (s + 1) := by rw [hqt]
      _ = C Czero⁻¹ + C Czero⁻¹ * s := by ring
  have hcert := eliminate_artificial_constraint_at q sigma tau
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
  apply GenPreordering_mono _ hcert
  apply max_le
  · exact (Nat.add_le_add_left
      (Nat.mul_le_mul hWdegree hqDegree) rS).trans (le_max_left _ _)
  · apply max_le
    · have hAdegree :
          (GeneralArchimedean.eliminationA epsilon Czero⁻¹ W.w).natDegree ≤
            1 + 2 * N :=
        (GeneralArchimedean.eliminationA_natDegree_le _ _ _).trans
          (Nat.add_le_add_left hWdegree 1)
      exact (Nat.add_le_add_left
        (Nat.mul_le_mul hAdegree hqDegree) rOne).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    · have hBdegree :
          (GeneralArchimedean.eliminationB epsilon Czero⁻¹ W.w).natDegree ≤
            1 + 2 * N :=
        (GeneralArchimedean.eliminationB_natDegree_le _ _ _).trans
          (Nat.add_le_add_left hWdegree 1)
      have hsubst :
          2 * (GeneralArchimedean.eliminationB epsilon Czero⁻¹ W.w).natDegree *
              q.totalDegree ≤ 2 * (1 + 2 * N) * d :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hBdegree) hqDegree
      exact (Nat.add_le_add_right
        (Nat.add_le_add_left hsubst rU) rT).trans
        ((le_max_right _ _).trans (le_max_right _ _))

end OptimalConvergenceRates.GeneralCompact

end
