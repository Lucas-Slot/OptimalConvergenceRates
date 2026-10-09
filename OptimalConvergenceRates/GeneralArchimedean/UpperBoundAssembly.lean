/-
  Assembly of the sharp bounded perturbation refutation and Chebyshev
  elimination into the square-root/log-square Putinar degree bound.
-/
import OptimalConvergenceRates.GeneralArchimedean.SharpBoundedPerturbation
import OptimalConvergenceRates.GeneralArchimedean.InputAsymptotics
import OptimalConvergenceRates.GeneralArchimedean.SharpOrderAsymptotics
import OptimalConvergenceRates.GeneralArchimedean.EliminationAsymptotics
import OptimalConvergenceRates.GeneralArchimedean.UpperBound

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralArchimedean

open RationalSquareRoot RationalSquareRoot.Package

variable {n m : ℕ}

set_option maxHeartbeats 1600000 in
-- Elaborating the nested certificate records requires the larger heartbeat budget.
/-- The complete quantitative algebraic input required by the analytic
inversion theorem.  The larger heartbeat budget is for elaborating the
nested explicit certificate records in this assembly. -/
theorem hasPutinarDegreeCostBound_of_archimedean
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hp : IsNonnegOn p (KrivineStengle.basicClosedSet g)) :
    HasPutinarDegreeCostBound g p := by
  obtain ⟨Bcoord, envelopeOrder, hBcoord, hcoord⟩ :=
    harch.exists_truncated_coordinate_square_bound
  obtain ⟨k, r, d, t, A, R, Hcoord, G, B,
      hk, hA, hR, hHcoord, hG, hd, hGdef, hBdef, hrefutations⟩ :=
    exists_sharp_bounded_quantitative_perturbation_module_refutation
      g p harch hp
  let familyCard : ℕ :=
    ((Finset.univ : Finset (Finset (Fin (m + 1)))).card)
  let Cpower : ℝ :=
    finiteFamilyPowerConstant familyCard n d R A
  let Dinput : ℝ := 1 + Real.log Cpower + (4 * k : ℕ)
  let Kbridge : ℝ :=
    max 0 (sharpBridgeLogSquareConstant (m + 1) n d R Hcoord G B)
  let Kbudget : ℝ := Kbridge * Dinput ^ 2
  let Kpackage : ℝ :=
    max 0 (sharpPackageDegreeConstant (m + 1) B (2 * (B + 1)))
  let Rbase : ℝ :=
    (sharpConversionRefutationOrderOfDegree 1 (m + 1) d
      (boundedCoeffEnvelopeOrder n t d) d
      (boundedCoeffEnvelopeOrder n t d) : ℕ)
  let Dr : ℝ := Rbase * (Kpackage * Dinput + 1)
  let Kmultiplier : ℝ :=
    boundedMultiplierLogSquareConstant n Bcoord Dr Kbudget
  let U : ℝ := boundedObjectiveEnvelope n p Bcoord
  let Kn : ℝ :=
    (Real.sqrt (2 / U))⁻¹ *
      chebyshevLogSquareConstant Kmultiplier
  let Kelim : ℝ :=
    perturbationEliminationLogConstant p.totalDegree Dr Kn
  let Dhalf : ℝ := 2 + Real.log 2
  let Kfinal : ℝ := 2 * Kelim * Dhalf ^ 2
  refine ⟨envelopeOrder, Kfinal, by positivity, ?_, ?_⟩
  · have hKbridge : 0 ≤ Kbridge := by dsimp [Kbridge]; positivity
    have hCpower : 1 ≤ Cpower := by
      dsimp [Cpower]
      exact one_le_finiteFamilyPowerConstant familyCard n d
        (zero_le_one.trans hR)
    have hDinput : 0 ≤ Dinput := by
      dsimp [Dinput]
      have := Real.log_nonneg hCpower
      positivity
    have hKbudget : 0 ≤ Kbudget := mul_nonneg hKbridge (sq_nonneg _)
    have hKpackage : 0 ≤ Kpackage := by dsimp [Kpackage]; positivity
    have hDr : 0 ≤ Dr := by
      dsimp [Dr, Rbase]
      positivity
    have hKmultiplier : 0 ≤ Kmultiplier :=
      boundedMultiplierLogSquareConstant_nonneg n hBcoord hDr hKbudget
    have hU : 0 < U := by
      dsimp [U, boundedObjectiveEnvelope, polynomialEnvelopeBound]
      positivity
    have hKn : 0 ≤ Kn := by
      dsimp [Kn, chebyshevLogSquareConstant]
      have hlog5 : 0 ≤ Real.log (5 : ℝ) :=
        Real.log_nonneg (by norm_num)
      positivity
    have hKelim : 0 ≤ Kelim :=
      perturbationEliminationLogConstant_nonneg p.totalDegree hDr hKn
    have hDhalf : 0 ≤ Dhalf := by
      dsimp [Dhalf]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      linarith
    dsimp [Kfinal]
    positivity
  · intro epsilon hepsilon hepsilon1
    let eta : ℝ := epsilon / 2
    let x : ℝ := eta⁻¹
    let H : ℝ := (eta ^ (2 * k))⁻¹ * A
    let Hconvert : ℝ :=
      finiteFamilyEnvelopeBound familyCard n d R H
    let Bprime : ℝ := 2 * (B + 1)
    let theta : ℝ := sharpThetaScale (m + 1)
    let delta : ℝ := sharpDeltaScale (m + 1) Hconvert Bprime
    have heta : 0 < eta := by dsimp [eta]; positivity
    have heta1 : eta ≤ 1 := by dsimp [eta]; linarith
    have hx : 1 ≤ x := by
      dsimp [x]
      exact (one_le_inv₀ heta).2 heta1
    have hx0 : 0 ≤ x := zero_le_one.trans hx
    have hH : H = A * x ^ (2 * k) := by
      dsimp [H, x]
      rw [inv_pow]
      ring
    have hH0 : 0 ≤ H := by
      rw [hH]
      exact mul_nonneg hA (pow_nonneg hx0 _)
    have hfamilyCard : 1 ≤ familyCard := by
      dsimp [familyCard]
      simp only [Fintype.card_finset, Fintype.card_fin]
      exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
    have hHle : H ≤ Hconvert := by
      dsimp [Hconvert]
      exact le_finiteFamilyEnvelopeBound hfamilyCard hR hH0
    have hHconvert0 : 0 ≤ Hconvert := hH0.trans hHle
    have hBfixed : 1 ≤ B := by
      rw [hBdef]
      unfold finiteFamilyEnvelopeBound polynomialEnvelopeBound
      have hterm : 0 ≤
          ((m + 1 : ℕ) : ℝ) * (boundedMonomialCount n d : ℝ) *
            ((G / 2) ^ 2 * R ^ d + 1) := by positivity
      linarith
    have hBprime : 0 ≤ Bprime := by
      dsimp [Bprime]
      positivity
    have hCpower : 1 ≤ Cpower := by
      dsimp [Cpower]
      exact one_le_finiteFamilyPowerConstant familyCard n d
        (zero_le_one.trans hR)
    have hpower :
        Hconvert + 1 ≤ Cpower * x ^ (4 * k) := by
      have hbound :=
        finiteFamilyEnvelopeBound_add_one_le_const_mul_pow
          (familyCard := familyCard) (n := n) (d := d)
          (q := 2 * k) (zero_le_one.trans hR) hH0 hA hx (le_of_eq hH)
      have hexp : 2 * (2 * k) = 4 * k := by omega
      simpa only [Hconvert, Cpower, hexp] using hbound
    have hHconvertOne : 1 ≤ Hconvert + 1 := by linarith
    have hscale :
        1 + Real.log (Hconvert + 1) ≤
          Dinput * (1 + Real.log x) := by
      have hlog := one_add_log_le_of_le_const_mul_pow
        (q := 4 * k) hx hHconvertOne hCpower hpower
      simpa [Dinput] using hlog
    have hDinput : 0 ≤ Dinput := by
      dsimp [Dinput]
      have := Real.log_nonneg hCpower
      positivity
    have hKbridge : 0 ≤ Kbridge := by dsimp [Kbridge]; positivity
    have hKbudget : 0 ≤ Kbudget := mul_nonneg hKbridge (sq_nonneg _)
    obtain ⟨pkg, hell, hJ, hcertNE⟩ :=
      hrefutations heta heta1
    let refutationOrder : ℕ :=
      sharpConversionRefutationOrder pkg (m + 1) d
        (boundedCoeffEnvelopeOrder n t d) d
        (boundedCoeffEnvelopeOrder n t d)
    let Hcert : ℝ :=
      boundedSharpBridgeRefutationBudget pkg (m + 1) n d
        R Hcoord G H Hconvert
    obtain ⟨cert⟩ := hcertNE
    have hcertBoundRaw :
        Hcert ≤ logSquareEnvelope
          (sharpBridgeLogSquareConstant (m + 1) n d R Hcoord G B)
          (Hconvert + 1) := by
      dsimp [Hcert, Bprime, theta, delta] at pkg hell hJ ⊢
      exact boundedSharpBridgeRefutationBudget_le_sharp_log
        hR hHcoord hG hBfixed hH0 hHle pkg hell hJ
    have hcertBoundMiddle :
        Hcert ≤ logSquareEnvelope Kbridge (Hconvert + 1) := by
      exact hcertBoundRaw.trans
        (logSquareEnvelope_mono (le_max_right _ _) hHconvertOne)
    have hcertBound :
        Hcert ≤ logSquareEnvelope Kbudget x := by
      exact hcertBoundMiddle.trans
        (logSquareEnvelope_le_of_logScale_le
          hKbridge hDinput hx hHconvertOne hscale)
    have hdegreeRaw :
        (pkg.degreeBound : ℝ) ≤
          sharpPackageDegreeConstant (m + 1) B Bprime *
            (1 + Real.log (Hconvert + 1)) := by
      dsimp [Bprime, theta, delta] at pkg hell hJ ⊢
      exact package_degreeBound_le_of_sharpDeltaScale
        hHconvert0 (zero_le_one.trans hBfixed) hBprime pkg hell hJ
    have hKpackage : 0 ≤ Kpackage := by dsimp [Kpackage]; positivity
    have hscale0 : 0 ≤ 1 + Real.log (Hconvert + 1) := by
      linarith [Real.log_nonneg hHconvertOne]
    have hdegree :
        (pkg.degreeBound : ℝ) ≤
          Kpackage * Dinput * (1 + Real.log x) := by
      calc
        (pkg.degreeBound : ℝ) ≤
            sharpPackageDegreeConstant (m + 1) B Bprime *
              (1 + Real.log (Hconvert + 1)) := hdegreeRaw
        _ ≤ Kpackage * (1 + Real.log (Hconvert + 1)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hscale0
        _ ≤ Kpackage * (Dinput * (1 + Real.log x)) :=
          mul_le_mul_of_nonneg_left hscale hKpackage
        _ = Kpackage * Dinput * (1 + Real.log x) := by ring
    have hlogx : 1 ≤ 1 + Real.log x := by
      linarith [Real.log_nonneg hx]
    have hdegreeOne :
        (pkg.degreeBound : ℝ) + 1 ≤
          (Kpackage * Dinput + 1) * (1 + Real.log x) := by
      nlinarith
    have hDr : 0 ≤ Dr := by dsimp [Dr, Rbase]; positivity
    have hrefutationOrder :
        (refutationOrder : ℝ) ≤ Dr * (1 + Real.log x) := by
      dsimp [refutationOrder]
      rw [sharpConversionRefutationOrder_eq_ofDegree]
      calc
        (sharpConversionRefutationOrderOfDegree pkg.degreeBound
            (m + 1) d (boundedCoeffEnvelopeOrder n t d) d
            (boundedCoeffEnvelopeOrder n t d) : ℝ) ≤
            Rbase * ((pkg.degreeBound : ℝ) + 1) := by
          simpa [Rbase, mul_comm] using
            sharpConversionRefutationOrderOfDegree_cast_le
              pkg.degreeBound (m + 1) d
                (boundedCoeffEnvelopeOrder n t d) d
                (boundedCoeffEnvelopeOrder n t d)
        _ ≤ Rbase *
            ((Kpackage * Dinput + 1) * (1 + Real.log x)) :=
          mul_le_mul_of_nonneg_left hdegreeOne (by positivity)
        _ = Dr * (1 + Real.log x) := by
          dsimp [Dr]
          ring
    have hHcert0 : 0 ≤ Hcert := cert.bound_nonneg
    let Czero : ℝ :=
      boundedMultiplierEnvelope n refutationOrder Bcoord Hcert
    have hCzero : 1 ≤ Czero := by
      dsimp [Czero, boundedMultiplierEnvelope, polynomialEnvelopeBound]
      have hterm : 0 ≤ (boundedMonomialCount n refutationOrder : ℝ) *
          ((Hcert / 2) ^ 2 * Bcoord ^ refutationOrder + 1) := by
        positivity
      linarith
    have hKmultiplier : 0 ≤ Kmultiplier :=
      boundedMultiplierLogSquareConstant_nonneg n hBcoord hDr hKbudget
    have hCzeroBound :
        Czero ≤ logSquareEnvelope Kmultiplier x := by
      dsimp [Czero, Kmultiplier]
      exact boundedMultiplierEnvelope_le_logSquareEnvelope
        hBcoord hHcert0 hDr hKbudget hx hrefutationOrder hcertBound
    have hcount : (1 : ℝ) ≤ boundedMonomialCount n p.totalDegree := by
      exact_mod_cast one_le_boundedMonomialCount n p.totalDegree
    have hUtwo : 2 ≤ U := by
      dsimp [U, boundedObjectiveEnvelope, polynomialEnvelopeBound]
      have hinside : 1 ≤
          ((coeffL1Norm p + 1) / 2) ^ 2 *
              Bcoord ^ p.totalDegree + 1 := by
        have hpow : 0 ≤ Bcoord ^ p.totalDegree :=
          pow_nonneg (zero_le_one.trans hBcoord) _
        have hprod : 0 ≤
            ((coeffL1Norm p + 1) / 2) ^ 2 *
              Bcoord ^ p.totalDegree := mul_nonneg (sq_nonneg _) hpow
        linarith
      have hprod := mul_le_mul hcount hinside (by norm_num : (0 : ℝ) ≤ 1)
        (zero_le_one.trans hcount)
      norm_num at hprod
      linarith
    have hKn : 0 ≤ Kn := by
      dsimp [Kn, chebyshevLogSquareConstant]
      have hlog5 : 0 ≤ Real.log (5 : ℝ) :=
        Real.log_nonneg (by norm_num)
      positivity
    let chebyshevOrder : ℕ :=
      chebyshevDegree eta Czero⁻¹ U
    have hchebyshevOrder :
        (chebyshevOrder : ℝ) ≤
          Kn / Real.sqrt eta * logSquareScale x + 1 := by
      dsimp [chebyshevOrder, Kn, x]
      exact chebyshevDegree_le_invSqrt_logSquare
        heta heta1 rfl hUtwo hKmultiplier hCzero hCzeroBound
    have hKelim : 0 ≤ Kelim :=
      perturbationEliminationLogConstant_nonneg p.totalDegree hDr hKn
    let outputOrder : ℕ :=
      perturbationEliminationOrder p.totalDegree refutationOrder
        envelopeOrder chebyshevOrder
    have houtputOrder :
        (outputOrder : ℝ) ≤
          envelopeOrder + Kelim / Real.sqrt eta * logSquareScale x := by
      dsimp [outputOrder, Kelim, x]
      exact perturbationEliminationOrder_le_invSqrt_logSquare
        heta heta1 hDr hKn hrefutationOrder hchebyshevOrder
    have hputinar :
        p + C epsilon ∈ GenQuadraticModule g outputOrder := by
      have hbase :=
        putinar_of_bounded_perturbation_refutation_of_coordinate_bounds
          g p hne hp hBcoord hcoord heta heta1 cert
      rw [show outputOrder =
          perturbationEliminationOrder p.totalDegree refutationOrder
            envelopeOrder chebyshevOrder by rfl]
      rw [show chebyshevOrder =
          chebyshevDegree eta Czero⁻¹ U by rfl]
      rw [show Czero =
          boundedMultiplierEnvelope n refutationOrder Bcoord Hcert by rfl]
      rw [show U = boundedObjectiveEnvelope n p Bcoord by rfl]
      have hbase' :
          p + C (2 * eta) ∈
            GenQuadraticModule g
              (perturbationEliminationOrder p.totalDegree refutationOrder
                envelopeOrder
                (chebyshevDegree eta
                  (boundedMultiplierEnvelope n refutationOrder
                    Bcoord Hcert)⁻¹
                  (boundedObjectiveEnvelope n p Bcoord))) := hbase
      convert hbase' using 1
      dsimp [eta]
      ring
    have hxepsilon : 1 ≤ epsilon⁻¹ :=
      (one_le_inv₀ hepsilon).2 hepsilon1
    have hetaInv : eta⁻¹ = 2 * epsilon⁻¹ := by
      dsimp [eta]
      rw [inv_div, div_eq_mul_inv]
    have hscaleHalf :
        1 + Real.log x ≤ Dhalf * (1 + Real.log epsilon⁻¹) := by
      have hbase := one_add_log_le_of_le_const_mul_pow
        (x := epsilon⁻¹) (y := x) (C := 2) (q := 1)
        hxepsilon hx (by norm_num) (by
          dsimp [x]
          rw [hetaInv]
          simp)
      convert hbase using 1
      all_goals dsimp [Dhalf]
      all_goals ring
    have hDhalf : 0 ≤ Dhalf := by
      dsimp [Dhalf]
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
    have hscaleSq :
        logSquareScale x ≤
          Dhalf ^ 2 * logSquareScale epsilon⁻¹ := by
      unfold logSquareScale
      have hleft : 0 ≤ 1 + Real.log x := by
        linarith [Real.log_nonneg hx]
      have hright : 0 ≤ Dhalf * (1 + Real.log epsilon⁻¹) := by
        exact mul_nonneg hDhalf <| by
          linarith [Real.log_nonneg hxepsilon]
      nlinarith [pow_le_pow_left₀ hleft hscaleHalf 2]
    have hsqrtEta :
        Real.sqrt eta = Real.sqrt epsilon / Real.sqrt 2 := by
      dsimp [eta]
      rw [Real.sqrt_div hepsilon.le]
    have hsqrtTwo : Real.sqrt (2 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
        Real.sqrt_nonneg (2 : ℝ)]
    have hinvSqrt :
        (Real.sqrt eta)⁻¹ ≤ 2 * (Real.sqrt epsilon)⁻¹ := by
      rw [hsqrtEta, inv_div]
      exact mul_le_mul_of_nonneg_right hsqrtTwo (inv_nonneg.mpr
        (Real.sqrt_nonneg epsilon))
    have hcostTerm :
        Kelim / Real.sqrt eta * logSquareScale x ≤
          Kfinal / Real.sqrt epsilon *
            logSquareScale epsilon⁻¹ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hprod := mul_le_mul hinvSqrt hscaleSq
        (sq_nonneg (1 + Real.log x))
        (mul_nonneg (by norm_num) (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      dsimp [Kfinal]
      nlinarith [mul_nonneg hKelim
        (sub_nonneg.mpr hprod)]
    have hdegree :
        (outputOrder : ℝ) ≤
          putinarDegreeCost envelopeOrder Kfinal epsilon := by
      unfold putinarDegreeCost
      simpa only [logSquareScale] using houtputOrder.trans
        (add_le_add (le_refl (envelopeOrder : ℝ)) hcostTerm)
    apply GenQuadraticModule_mono _ hputinar
    have hceil := Nat.le_ceil
      (putinarDegreeCost envelopeOrder Kfinal epsilon)
    exact_mod_cast hdegree.trans hceil

end OptimalConvergenceRates.GeneralArchimedean

end
