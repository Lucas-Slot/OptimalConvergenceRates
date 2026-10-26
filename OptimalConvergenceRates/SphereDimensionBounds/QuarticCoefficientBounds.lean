import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
/-! Coefficient bounds for actual globally nonnegative real quartics.
No sum-of-squares representation or selector-existence premise is used.
This module does not assert the complete upper-bound theorem. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.QuarticCoefficientBounds

open Filter Topology

/-- The actual scalar quartic, including both odd coefficients. -/
def quartic (a l H B C s : ℝ) : ℝ :=
  a*s^4+l*s^3+H*s^2+B*s+C

private theorem nonneg_zero_of_pos {f : ℝ → ℝ} (hf : ContinuousAt f 0)
    (hpos : ∀ t : ℝ, 0<t → 0≤f t) : 0≤f 0 := by
  have he : ∀ᶠ t in 𝓝[>] (0:ℝ), 0≤f t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpos t ht
  have ht : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 (f 0)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht he

/-- Global nonnegativity forces both extreme coefficients to be nonnegative. -/
theorem extreme_coefficients_nonneg {a l H B C : ℝ}
    (hp : ∀ s : ℝ, 0≤quartic a l H B C s) : 0≤a ∧ 0≤C := by
  have hC : 0≤C := by simpa [quartic] using hp 0
  have hrev : ContinuousAt (fun t : ℝ => a+l*t+H*t^2+B*t^3+C*t^4) 0 := by fun_prop
  have ha := nonneg_zero_of_pos hrev (fun t ht => by
    have hid : a+l*t+H*t^2+B*t^3+C*t^4 = t^4*quartic a l H B C (1/t) := by
      dsimp [quartic]
      field_simp [ht.ne']
    rw [hid]
    exact mul_nonneg (by positivity) (hp (1/t)))
  exact ⟨by simpa using ha,hC⟩

private theorem opposite_roots {alpha beta gamma : ℝ}
    (ha : 0 < alpha) (hc : 0 < gamma) :
    ∃ rp rm : ℝ, 0<rp ∧ rm<0 ∧
      alpha*rp^2-beta*rp-gamma=0 ∧ alpha*rm^2-beta*rm-gamma=0 := by
  let d := Real.sqrt (beta^2+4*alpha*gamma)
  have hd0 : 0≤beta^2+4*alpha*gamma := by positivity
  have hd : discrim alpha (-beta) (-gamma)=d*d := by
    dsimp [discrim,d]
    rw [Real.mul_self_sqrt hd0]
    ring
  have hbeta : beta<d := Real.lt_sqrt_of_sq_lt (by
    nlinarith [mul_pos ha hc])
  have hnbeta : -beta<d := Real.lt_sqrt_of_sq_lt (by
    nlinarith [mul_pos ha hc])
  let rp := (beta+d)/(2*alpha)
  let rm := (beta-d)/(2*alpha)
  refine ⟨rp,rm,div_pos (by linarith) (by positivity),
    div_neg_of_neg_of_pos (by linarith) (by positivity),?_,?_⟩
  · have hr := (quadratic_eq_zero_iff ha.ne' hd rp).2 (Or.inl (by dsimp [rp]; ring))
    simpa only [pow_two,neg_mul,sub_eq_add_neg] using hr
  · have hr := (quadratic_eq_zero_iff ha.ne' hd rm).2 (Or.inr (by dsimp [rm]; ring))
    simpa only [pow_two,neg_mul,sub_eq_add_neg] using hr

private theorem positive_square_coefficients_bound {alpha beta gamma l H : ℝ}
    (ha : 0 < alpha) (hc : 0 < gamma)
    (hp : ∀ s : ℝ, 0≤quartic (alpha^2) l H (2*beta*gamma) (gamma^2) s) :
    beta^2≤H+2*alpha*gamma := by
  obtain ⟨rp,rm,hrp,hrm,hrootp,hrootm⟩ := opposite_roots (beta:=beta) ha hc
  have hid (s : ℝ) : quartic (alpha^2) l H (2*beta*gamma) (gamma^2) s =
      (alpha*s^2-beta*s-gamma)^2+
        s^2*((H-beta^2+2*alpha*gamma)+(l+2*alpha*beta)*s) := by
    dsimp [quartic]
    ring
  have hp' := hp rp
  have hm' := hp rm
  rw [hid,hrootp,zero_pow (by decide),zero_add] at hp'
  rw [hid,hrootm,zero_pow (by decide),zero_add] at hm'
  have hpD : 0≤(H-beta^2+2*alpha*gamma)+(l+2*alpha*beta)*rp :=
    nonneg_of_mul_nonneg_right hp' (sq_pos_of_pos hrp)
  have hmD : 0≤(H-beta^2+2*alpha*gamma)+(l+2*alpha*beta)*rm :=
    nonneg_of_mul_nonneg_right hm' (sq_pos_of_ne_zero hrm.ne)
  by_contra hbound
  have hD : H-beta^2+2*alpha*gamma<0 := by linarith
  have hL : 0<l+2*alpha*beta :=
    pos_of_mul_pos_left (by linarith : 0<(l+2*alpha*beta)*rp) hrp.le
  have hprod : (l+2*alpha*beta)*rm<0 := mul_neg_of_pos_of_neg hL hrm
  linarith

/-- Sharp coefficient estimate when both extreme coefficients are positive. -/
theorem coefficient_bound_of_pos {a l H B C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hp : ∀ s : ℝ, 0≤quartic a l H B C s) :
    B^2≤4*C*(H+2*Real.sqrt (a*C)) := by
  let alpha := Real.sqrt a
  let gamma := Real.sqrt C
  let beta := B/(2*gamma)
  have halpha : 0<alpha := Real.sqrt_pos.2 ha
  have hgamma : 0<gamma := Real.sqrt_pos.2 hC
  have hasq : alpha^2=a := Real.sq_sqrt ha.le
  have hgsq : gamma^2=C := Real.sq_sqrt hC.le
  have hB : 2*beta*gamma=B := by
    dsimp [beta]
    field_simp [hgamma.ne']
  have hnorm := positive_square_coefficients_bound (beta:=beta) halpha hgamma
    (by simpa only [hasq,hgsq,hB] using hp)
  have hsqrt : Real.sqrt (a*C)=alpha*gamma := Real.sqrt_mul ha.le C
  rw [hsqrt]
  have hmul := mul_le_mul_of_nonneg_left hnorm (show 0≤4*gamma^2 by positivity)
  have hbet : 4*gamma^2*beta^2=B^2 := by
    dsimp [beta]
    field_simp
    ring
  rw [hbet,hgsq] at hmul
  simpa only [mul_assoc] using hmul

/-- The sharp bound also covers zero leading or constant coefficients.
The limit uses positive quartics `p(s)+eps*(s^4+1)`. -/
theorem coefficient_bound {a l H B C : ℝ}
    (hp : ∀ s : ℝ, 0≤quartic a l H B C s) :
    B^2≤4*C*(H+2*Real.sqrt (a*C)) := by
  obtain ⟨ha,hC⟩ := extreme_coefficients_nonneg hp
  have hcont : ContinuousAt
      (fun eps : ℝ => 4*(C+eps)*(H+2*Real.sqrt ((a+eps)*(C+eps)))-B^2) 0 := by
    fun_prop
  have hb := nonneg_zero_of_pos hcont (fun eps heps => by
    have hpert (s : ℝ) : 0≤quartic (a+eps) l H B (C+eps) s := by
      have hid : quartic (a+eps) l H B (C+eps) s =
          quartic a l H B C s+eps*(s^4+1) := by dsimp [quartic]; ring
      rw [hid]
      exact add_nonneg (hp s) (mul_nonneg heps.le (by positivity))
    have hbound := coefficient_bound_of_pos (by linarith : 0<a+eps)
      (by linarith : 0<C+eps) hpert
    linarith)
  simpa only [add_zero,sub_nonneg] using hb

/-- The corrected quadratic coefficient is nonnegative, including at `C=0`. -/
theorem corrected_quadratic_nonneg {a l H B C : ℝ}
    (hp : ∀ s : ℝ, 0≤quartic a l H B C s) :
    0≤H+2*Real.sqrt (a*C) := by
  obtain ⟨ha,hC⟩ := extreme_coefficients_nonneg hp
  have hcont : ContinuousAt
      (fun eps : ℝ => H+2*Real.sqrt ((a+eps)*(C+eps))) 0 := by fun_prop
  have hb := nonneg_zero_of_pos hcont (fun eps heps => by
    have hpert (s : ℝ) : 0≤quartic (a+eps) l H B (C+eps) s := by
      have hid : quartic (a+eps) l H B (C+eps) s =
          quartic a l H B C s+eps*(s^4+1) := by dsimp [quartic]; ring
      rw [hid]
      exact add_nonneg (hp s) (mul_nonneg heps.le (by positivity))
    have hbound := coefficient_bound_of_pos (by linarith : 0<a+eps)
      (by linarith : 0<C+eps) hpert
    have hprod : 0≤4*(C+eps)*(H+2*Real.sqrt ((a+eps)*(C+eps))) :=
      (sq_nonneg B).trans hbound
    exact nonneg_of_mul_nonneg_right hprod (by positivity : 0<4*(C+eps)))
  simpa only [add_zero] using hb

/-- All scalar conclusions with the actual constant coefficient. -/
theorem sharp_bounds {a l H B C : ℝ}
    (hp : ∀ s : ℝ, 0≤quartic a l H B C s) :
    0≤a ∧ 0≤C ∧ 0≤H+2*Real.sqrt (a*C) ∧
      B^2≤4*C*(H+2*Real.sqrt (a*C)) :=
  ⟨(extreme_coefficients_nonneg hp).1,(extreme_coefficients_nonneg hp).2,
    corrected_quadratic_nonneg hp,coefficient_bound hp⟩

/-- Replacing the constant coefficient by any nonnegative upper bound. -/
theorem bounds_of_constant_le {a l H B C M : ℝ}
    (hp : ∀ s : ℝ, 0≤quartic a l H B C s) (hM : 0≤M) (hCM : C≤M) :
    0≤a ∧ 0≤H+2*Real.sqrt (a*M) ∧
      B^2≤4*M*(H+2*Real.sqrt (a*M)) := by
  obtain ⟨ha,hC,hA,hB⟩ := sharp_bounds hp
  have hsqrt : Real.sqrt (a*C)≤Real.sqrt (a*M) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hCM ha)
  have hAM : 0≤H+2*Real.sqrt (a*M) := by linarith
  refine ⟨ha,hAM,hB.trans ?_⟩
  exact mul_le_mul (by linarith : 4*C≤4*M) (by linarith)
    hA (by positivity)

/-- The actual radial form used for every fixed transverse point. -/
theorem radial_bounds {a l H B C M R : ℝ}
    (hp : ∀ s : ℝ, 0≤quartic a l H B C s) (hM : 0≤M) (hR : 0≤R)
    (hCM : C≤M*R^2) :
    0≤a ∧ 0≤H+2*Real.sqrt (a*M)*R ∧
      B^2≤4*M*(H+2*Real.sqrt (a*M)*R)*R^2 := by
  obtain ⟨ha,hA,hB⟩ := bounds_of_constant_le hp (by positivity : 0≤M*R^2) hCM
  have hsqrt : Real.sqrt (a*(M*R^2))=Real.sqrt (a*M)*R := by
    rw [show a*(M*R^2)=(a*M)*R^2 by ring,
      Real.sqrt_mul (mul_nonneg ha hM),Real.sqrt_sq hR]
  rw [hsqrt] at hA hB
  refine ⟨ha,by simpa only [mul_assoc] using hA,?_⟩
  nlinarith only [hB]

/-- The same bounds for actual multivariate coefficient polynomials, evaluated
at every transverse point. Global nonnegativity is the full scalar family,
including both odd coefficient polynomials. -/
theorem polynomial_radial_bounds {ι : Type*} (a M : ℝ)
    (l H B C R : MvPolynomial ι ℝ)
    (hp : ∀ (s : ℝ) (x : ι → ℝ), 0 ≤ quartic a
      (MvPolynomial.eval x l) (MvPolynomial.eval x H)
      (MvPolynomial.eval x B) (MvPolynomial.eval x C) s)
    (hM : 0 ≤ M) (hR : ∀ x : ι → ℝ, 0≤MvPolynomial.eval x R)
    (hCM : ∀ x : ι → ℝ, MvPolynomial.eval x C≤M*(MvPolynomial.eval x R)^2) :
    ∀ x : ι → ℝ,
      0≤a ∧ 0≤MvPolynomial.eval x H+2*Real.sqrt (a*M)*MvPolynomial.eval x R ∧
      (MvPolynomial.eval x B)^2≤4*M*
        (MvPolynomial.eval x H+2*Real.sqrt (a*M)*MvPolynomial.eval x R)*
        (MvPolynomial.eval x R)^2 := by
  intro x
  exact radial_bounds (fun s => hp s x) hM (hR x) (hCM x)

end OptimalConvergenceRates.SphereDimensionBounds.QuarticCoefficientBounds
