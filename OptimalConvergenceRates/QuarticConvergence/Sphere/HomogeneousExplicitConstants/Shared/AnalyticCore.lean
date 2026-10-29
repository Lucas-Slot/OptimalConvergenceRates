import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Bounded-half-plane maximum modulus for the sphere-SOS transfer

This module isolates a genuine analytic input of the weighted transfer
argument. Its conclusion has no dependence on the codomain dimension.
The full frequency representation and weighted transfer remain separate
research obligations.
-/

open Set Filter Asymptotics
open scoped Topology

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

/-- A bounded holomorphic function on the right half-plane is controlled by
its imaginary-axis bound. The codomain may be any complex normed space. -/
theorem norm_le_of_bounded_right_half_plane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {B C : ℝ}
    (hd : DiffContOnCl ℂ f {z : ℂ | 0 < z.re})
    (hB : ∀ z : ℂ, 0 ≤ z.re → ‖f z‖ ≤ B)
    (hC : ∀ x : ℝ, ‖f (x * Complex.I)‖ ≤ C)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖f z‖ ≤ C := by
  apply PhragmenLindelof.right_half_plane_of_bounded_on_real hd ?_ ?_ hC hz
  · refine ⟨0, by norm_num, 0, ?_⟩
    apply Asymptotics.IsBigO.of_bound B
    refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall ?_)
    intro w hw
    simpa only [zero_mul, Real.exp_zero, norm_one, mul_one] using hB w hw.le
  · apply Filter.isBoundedUnder_of_eventually_le (a := B)
    filter_upwards [Filter.Ici_mem_atTop (0 : ℝ)] with x hx
    exact hB (x : ℂ) (by simpa only [Complex.ofReal_re, Set.mem_Ici] using hx)

/-- The corresponding upper-half-plane statement, obtained by rotation. -/
theorem norm_le_of_bounded_upper_half_plane
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {B C : ℝ}
    (hd : DiffContOnCl ℂ f {z : ℂ | 0 < z.im})
    (hB : ∀ z : ℂ, 0 ≤ z.im → ‖f z‖ ≤ B)
    (hC : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ C)
    {z : ℂ} (hz : 0 ≤ z.im) : ‖f z‖ ≤ C := by
  have hrot : DiffContOnCl ℂ (fun w : ℂ ↦ f (Complex.I * w))
      {w : ℂ | 0 < w.re} := by
    apply hd.comp (differentiable_id.const_mul Complex.I).diffContOnCl
    intro w hw
    simpa only [Set.mem_ofPred_eq, id_eq, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_add] using hw
  have hBrot : ∀ w : ℂ, 0 ≤ w.re → ‖f (Complex.I * w)‖ ≤ B := by
    intro w hw
    apply hB
    simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add] using hw
  have hCrot : ∀ x : ℝ, ‖f (Complex.I * (x * Complex.I))‖ ≤ C := by
    intro x
    have hident : Complex.I * ((x : ℂ) * Complex.I) = (-x : ℂ) := by
      calc
        Complex.I * ((x : ℂ) * Complex.I) =
            (x : ℂ) * (Complex.I * Complex.I) := by ring
        _ = (-x : ℂ) := by simp
    rw [hident]
    simpa only [Complex.ofReal_neg] using hC (-x)
  have hpoint : 0 ≤ (-Complex.I * z).re := by
    simpa only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, neg_zero, zero_mul, neg_mul, one_mul, sub_neg_eq_add,
      zero_add, zero_sub, neg_neg] using hz
  have hfinal := norm_le_of_bounded_right_half_plane hrot hBrot hCrot hpoint
  have hident : Complex.I * (-Complex.I * z) = z := by
    rw [← mul_assoc]
    simp
  simpa only [hident] using hfinal

/-- The Cauchy coefficient bound in a form with a uniform boundary constant.

No holomorphy hypothesis is needed for this norm estimate on the coefficients
defined by circle integrals. Holomorphy is used separately when identifying
the Cauchy series with the original function. -/
theorem norm_cauchyPowerSeries_le_of_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c : ℂ) {R B : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ B) (n : ℕ) :
    ‖cauchyPowerSeries f c R n‖ ≤ B / R ^ n := by
  have hbound : ∀ z ∈ Metric.sphere c R,
      ‖(z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ ≤ R⁻¹ ^ n * (R⁻¹ * B) := by
    intro z hz
    have hzR : ‖z - c‖ = R := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    rw [norm_smul, norm_smul, norm_pow, norm_inv, hzR]
    gcongr
    exact hf z hz
  calc
    ‖cauchyPowerSeries f c R n‖ =
        ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ z in C(c, R), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ := by
      simp only [cauchyPowerSeries, ContinuousMultilinearMap.norm_mkPiRing]
    _ ≤ R * (R⁻¹ ^ n * (R⁻¹ * B)) :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hbound
    _ = B / R ^ n := by
      rw [div_eq_mul_inv, ← inv_pow]
      calc
        R * (R⁻¹ ^ n * (R⁻¹ * B)) = (R * R⁻¹) * (B * R⁻¹ ^ n) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hR.ne', one_mul]

/-- A quantitative vector-valued geometric tail bound for a convergent series.

The sum through degree `K` contains exactly the indices in `range (K + 1)`.
No completeness assumption is needed because convergence is an explicit
hypothesis. -/
theorem norm_series_tail_le_geometric
    {E : Type*} [NormedAddCommGroup E]
    {a : ℕ → E} {s : E} {B ρ : ℝ}
    (hs : HasSum a s) (hρnonneg : 0 ≤ ρ) (hρ : ρ < 1)
    (hbound : ∀ n : ℕ, ‖a n‖ ≤ B * ρ ^ n) (K : ℕ) :
    ‖s - ∑ j ∈ Finset.range (K + 1), a j‖ ≤ B * ρ ^ (K + 1) / (1 - ρ) := by
  have htail : HasSum (fun n : ℕ ↦ a (n + (K + 1)))
      (s - ∑ j ∈ Finset.range (K + 1), a j) :=
    (hasSum_nat_add_iff' (K + 1)).2 hs
  have hgeom : HasSum (fun n : ℕ ↦ B * ρ ^ (K + 1) * ρ ^ n)
      (B * ρ ^ (K + 1) / (1 - ρ)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hρnonneg hρ).mul_left (B * ρ ^ (K + 1))
  apply htail.norm_le_of_bounded hgeom
  intro n
  calc
    ‖a (n + (K + 1))‖ ≤ B * ρ ^ (n + (K + 1)) := hbound _
    _ = B * ρ ^ (K + 1) * ρ ^ n := by rw [pow_add]; ring

/-- The geometric remainder estimate specialized to a power-series partial sum.
The coefficient hypothesis cleanly separates Cauchy norm estimates from the
series summation step. -/
theorem norm_powerSeries_tail_le_geometric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {R : ENNReal}
    (h : HasFPowerSeriesOnBall f p 0 R) {τ : ℂ}
    (hτ : τ ∈ Metric.eball 0 R) {B ρ : ℝ}
    (hρnonneg : 0 ≤ ρ) (hρ : ρ < 1)
    (hcoef : ∀ n : ℕ, ‖p n‖ * ‖τ‖ ^ n ≤ B * ρ ^ n) (K : ℕ) :
    ‖f τ - p.partialSum (K + 1) τ‖ ≤ B * ρ ^ (K + 1) / (1 - ρ) := by
  have hs : HasSum (fun n : ℕ ↦ p n (fun _ ↦ τ)) (f τ) := by
    simpa only [zero_add] using h.hasSum hτ
  have hbound : ∀ n : ℕ, ‖p n (fun _ ↦ τ)‖ ≤ B * ρ ^ n := by
    intro n
    calc
      ‖p n (fun _ ↦ τ)‖ ≤ ‖p n‖ * ‖τ‖ ^ n := by
        simpa using (p n).le_opNorm (fun _ ↦ τ)
      _ ≤ B * ρ ^ n := hcoef n
  simpa only [FormalMultilinearSeries.partialSum] using
    norm_series_tail_le_geometric hs hρnonneg hρ hbound K

/-- The analytic vanishing order controls every coefficient of any local
representing power series. This bridges the two different order APIs. -/
theorem coefficient_eq_zero_of_lt_analytic_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E} {z : ℂ}
    (hp : HasFPowerSeriesAt f p z) (j : ℕ)
    (hj : (j : ENat) < analyticOrderAt f z) : p.coeff j = 0 := by
  by_cases hzero : p = 0
  · simp [hzero, FormalMultilinearSeries.coeff]
  · have horder : analyticOrderAt f z = (p.order : ENat) := by
      apply (hp.analyticAt.analyticOrderAt_eq_natCast).2
      refine ⟨(Function.swap dslope z)^[p.order] f, ?_, ?_, ?_⟩
      · exact (HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope p.order hp).analyticAt
      · exact hp.iterate_dslope_fslope_ne_zero hzero
      · exact Filter.Eventually.of_forall hp.eq_pow_order_mul_iterate_dslope
    rw [horder] at hj
    have hjnat : j < p.order := by exact_mod_cast hj
    exact FormalMultilinearSeries.coeff_eq_zero.2
      (FormalMultilinearSeries.apply_eq_zero_of_lt_order hjnat)

/-- A monomial containing `ell` sine factors starts at Taylor order at least
`ell`. This is the vanishing fact behind the polynomial degree of the
certificate's Taylor truncation. -/
theorem sin_pow_mul_cos_pow_coefficient_eq_zero
    (ell b j : ℕ) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt
      (fun z : ℂ ↦ Complex.sin z ^ ell * Complex.cos z ^ b) p 0)
    (hj : j < ell) : p.coeff j = 0 := by
  let hsin : AnalyticAt ℂ Complex.sin 0 := Complex.differentiable_sin.analyticAt 0
  let hcos : AnalyticAt ℂ Complex.cos 0 := Complex.differentiable_cos.analyticAt 0
  have hsinne : analyticOrderAt Complex.sin 0 ≠ 0 := by
    intro hzero
    have hne := hsin.analyticOrderAt_eq_zero.1 hzero
    simp at hne
  have hsinone : (1 : ENat) ≤ analyticOrderAt Complex.sin 0 := Order.one_le_iff_ne_zero.2 hsinne
  have hcoszero : analyticOrderAt Complex.cos 0 = 0 := hcos.analyticOrderAt_eq_zero.2 (by simp)
  have hell : (ell : ENat) ≤ ell • analyticOrderAt Complex.sin 0 := by
    simpa using nsmul_le_nsmul_right hsinone ell
  have hporder : (ell : ENat) ≤ analyticOrderAt (fun z : ℂ ↦ Complex.sin z ^ ell * Complex.cos z ^
    b) 0 := by
    change (ell : ENat) ≤ analyticOrderAt (Complex.sin ^ ell * Complex.cos ^ b) 0
    rw [analyticOrderAt_mul (hsin.pow ell) (hcos.pow b), analyticOrderAt_pow hsin,
      analyticOrderAt_pow hcos,
      hcoszero, nsmul_zero, add_zero]
    exact hell
  apply coefficient_eq_zero_of_lt_analytic_order hp j
  exact (show (j : ENat) < (ell : ENat) by exact_mod_cast hj).trans_le hporder

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
