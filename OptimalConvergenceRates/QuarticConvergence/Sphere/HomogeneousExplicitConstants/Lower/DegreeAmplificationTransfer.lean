import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.DegreeAmplificationPolynomial
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.UniformTransfer

/-! The analytic transfer for the actual Chebyshev-amplified objective. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace DegreeAmplification

open scoped BigOperators
open MvPolynomial Foundation

section
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] {K : ℕ}

theorem functional_amplified_inequality
    (E : TruncatedBooleanPseudoexpectation V K) {L D eps delta t b : ℝ}
    (hbound : TruncatedEvaluationBound E L)
    (q : (V → Bool) → ℝ) (hq : HasBooleanDegree (2 * K) q)
    (hqeval : E.functional ⟨q, hq⟩ = -delta)
    (G : (V → Bool) → EuclideanSpace ℂ J)
    (hre : ∀ j, HasBooleanDegree K (fun z ↦ (G z j).re))
    (him : ∀ j, HasBooleanDegree K (fun z ↦ (G z j).im))
    (herror : ∀ z, |eps + b ^ 4 * q z - ‖G z‖ ^ 2| ≤ 6 * D * (eps + t ^ 4)) :
    delta*b^4-(6*L*D)*t^4≤(1+6*L*D)*eps := by
  let oneE : booleanDegreeSpace (I := V) (2*K) :=
    ⟨fun _ ↦ 1,hasBooleanDegree_one (2*K)⟩
  let qE : booleanDegreeSpace (I := V) (2*K) := ⟨q,hq⟩
  let gE : booleanDegreeSpace (I := V) (2*K) :=
    ⟨fun z ↦ ‖G z‖^2,hasBooleanDegree_norm_sq G K hre him⟩
  let errorE := eps • oneE+b^4 • qE-gE
  have habs := hbound errorE (6*D*(eps+t^4)) (by
    intro z
    change |eps*1+b^4*q z-‖G z‖^2|≤_
    simpa only [mul_one] using herror z)
  have hpos : 0≤E.functional gE := truncatedPseudoexpectation_norm_sq_nonneg E G hre him
  have hone : E.functional oneE=1 := E.normalized
  have hqE : E.functional qE = -delta := hqeval
  have heval : E.functional errorE=eps-delta*b^4-E.functional gE := by
    simp only [errorE,map_sub,map_add,map_smul,hone,hqE,smul_eq_mul]
    ring
  rw [heval] at habs
  have hlow := (abs_le.mp habs).1
  nlinarith
end

section
variable {σ V J : Type*} [Fintype σ] [Fintype V] [DecidableEq V] [Fintype J]
    {r K : ℕ}

theorem amplified_certificate_eps_nonneg (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (k j : ℕ) (eps : ℝ)
    (h : J → MvPolynomial (Option σ) ℝ) (g : MvPolynomial (Option σ) ℝ)
    (certificate : amplified q k j + C eps = (∑ a, h a ^ 2) + (1 - genericRadius) * g) :
    0≤eps := by
  have he := congrArg (eval (paddingPole (σ := σ))) certificate
  have heval : eps=∑ a,eval paddingPole (h a)^2 := by
    simpa [amplified_pole_eval q hq k j,paddingPole] using he
  rw [heval]
  exact Finset.sum_nonneg fun a _ ↦ sq_nonneg _

theorem amplified_certificate_norm_sq (q : MvPolynomial σ ℝ)
    (hq : q.IsHomogeneous 4) (k j : ℕ) (eps : ℝ)
    (h : J → MvPolynomial (Option σ) ℝ) (g : MvPolynomial (Option σ) ℝ)
    (certificate : amplified q k j + C eps = (∑ a, h a ^ 2) + (1 - genericRadius) * g)
    (y : σ → ℝ) (hy : ∑ i, y i ^ 2 = 1) (u : ℝ) :
    ‖angularVector h y (u:ℂ)‖^2=eps+Real.sin ((k+1:ℕ)*u)^4*eval y q := by
  rw [angularVector_real_norm_sq]
  have he := congrArg (eval (realAngularPoint y u)) certificate
  have hs : eval (realAngularPoint y u) genericRadius=1 := by
    rw [genericRadius_eval,realAngularPoint_sphere y hy]
  simpa [amplified_angular_eval q hq k j y hy u,hs,add_comm] using he.symm

omit [Fintype σ] in
theorem scaled_angular_norm_sq (h : J → MvPolynomial (Option σ) ℝ)
    (c : ℝ) (y : σ → ℝ) (u : ℝ) :
    ‖angularVector (fun a ↦ C c*h a) y (u:ℂ)‖^2=
      c^2*‖angularVector h y (u:ℂ)‖^2 := by
  rw [angularVector_real_norm_sq,angularVector_real_norm_sq]
  simp only [eval_mul,eval_C,mul_pow,Finset.mul_sum]

/-- Scaling the entire square family preserves the vector error constant. -/
theorem amplified_certificate_high_order_shift
    (E : TruncatedBooleanPseudoexpectation V K) {delta ρ : ℝ}
    (q : MvPolynomial σ ℝ) (hqhom : q.IsHomogeneous 4)
    (hqdegree : q.totalDegree ≤ 2 * K)
    (hqupper : ∀ y : σ → ℝ, (∑ i,y i^2)=1 → eval y q≤1)
    (a : σ → (V → Bool) → ℝ) (hadegree : ∀ i,HasBooleanDegree 1 (a i))
    (haunit : ∀ z,(∑ i,a i z^2)=1)
    (hqeval : E.functional ⟨fun z ↦ eval (fun i ↦ a i z) q,
      hasBooleanDegree_eval_of_totalDegree_le q a hadegree (2*K) hqdegree⟩ = -delta)
    (k j : ℕ) (eps : ℝ) (h : J → MvPolynomial (Option σ) ℝ)
    (g : MvPolynomial (Option σ) ℝ)
    (certificate : amplified q k j+C eps=(∑ b,h b^2)+(1-genericRadius)*g)
    (hdegree : ∀ b,(h b).totalDegree≤r) (hK : 0<K) (hrK : (k+1)*K≤r)
    (hρ0 : 0≤ρ) (hρhalf : ρ≤1/2) (hscale : 1≤ρ*(K:ℝ))
    (hA : 6*cubeSize V*angularTruncationFactor K ρ≤1)
    (hAdelta : 6*cubeSize V*angularTruncationFactor K ρ≤delta/32) :
    delta*((k+1:ℕ)*ρ*(K:ℝ)/(r:ℝ))^4/64≤eps := by
  let ell : ℝ := (k+1:ℕ)
  let hs : J → MvPolynomial (Option σ) ℝ := fun b ↦ C (ell^2)⁻¹*h b
  let t : ℝ := ρ*(K:ℝ)/(r:ℝ)
  have hell : 0<ell := by dsimp [ell]; positivity
  have hell4 : 0<ell^4 := pow_pos hell 4
  have hr : 0<r := by have : 0<(k+1)*K := Nat.mul_pos (by omega) hK; omega
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have heps := amplified_certificate_eps_nonneg q hqhom k j eps h g certificate
  have hsdegree (b : J) : (hs b).totalDegree≤r :=
    (totalDegree_mul _ _).trans (by simpa [hs,totalDegree_C] using hdegree b)
  have hscaled (y : σ → ℝ) (hy : ∑ i,y i^2=1) (u : ℝ) :
      ‖angularVector hs y (u:ℂ)‖^2=
        eps/ell^4+(Real.sin (ell*u)/ell)^4*eval y q := by
    rw [scaled_angular_norm_sq,amplified_certificate_norm_sq q hqhom k j eps h g certificate y hy]
    change (ell^2)⁻¹^2 * (eps+Real.sin (ell*u)^4*eval y q) = _
    simp only [inv_pow,div_pow,div_eq_mul_inv,←pow_mul]
    ring
  have hreal (z : V → Bool) (u : ℝ) :
      ‖angularVector hs (fun i ↦ a i z) (u:ℂ)‖≤Real.sqrt (eps/ell^4)+u^2 := by
    have hn := hscaled _ (haunit z) u
    have hsin : (Real.sin (ell*u)/ell)^4≤u^4 := by
      have hs2 : (Real.sin (ell*u)/ell)^2≤u^2 := by
        rw [div_pow]
        apply (div_le_iff₀ (pow_pos hell 2)).2
        simpa only [mul_pow,mul_comm] using Real.sin_sq_le_sq (x := ell*u)
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hs2 2
    have hobj : (Real.sin (ell*u)/ell)^4*eval (fun i ↦ a i z) q≤u^4 :=
      (mul_le_of_le_one_right (by positivity) (hqupper _ (haunit z))).trans hsin
    have hsqrt := Real.sq_sqrt (div_nonneg heps hell4.le)
    have hcross : 0≤Real.sqrt (eps/ell^4)*u^2 := by positivity
    have hrhs : 0≤Real.sqrt (eps/ell^4)+u^2 := by positivity
    nlinarith [norm_nonneg (angularVector hs (fun i ↦ a i z) (u:ℂ)),sq_nonneg u]
  have hD := angularTruncationFactor_le_one_of_amplification hρ0 hA
  have herror (z : V → Bool) :
      |eps/ell^4+(Real.sin (ell*t)/ell)^4*eval (fun i ↦ a i z) q-
          ‖angularTaylorVector hs (t:ℂ) K (fun i ↦ a i z)‖^2|≤
        6*angularTruncationFactor K ρ*(eps/ell^4+t^4) := by
    have herr := angularTaylorVector_norm_square_error hs (fun i ↦ a i z) hr hK
      hsdegree (hreal z) hρ0 hρhalf hscale hD
    rw [Real.sq_sqrt (div_nonneg heps hell4.le)] at herr
    change |‖angularVector hs (fun i ↦ a i z) (t:ℂ)‖^2-
      ‖angularTaylorVector hs (t:ℂ) K (fun i ↦ a i z)‖^2|≤
      6*angularTruncationFactor K ρ*(eps/ell^4+t^4) at herr
    rw [hscaled _ (haunit z) t] at herr
    exact herr
  have hinequality := functional_amplified_inequality E
    (truncatedEvaluationBound_of_positive E) _
    (hasBooleanDegree_eval_of_totalDegree_le q a hadegree (2*K) hqdegree) hqeval
    (fun z ↦ angularTaylorVector hs (t:ℂ) K (fun i ↦ a i z))
    (angularTaylorVector_boolean_re_degree hs (t:ℂ) K a hadegree)
    (angularTaylorVector_boolean_im_degree hs (t:ℂ) K a hadegree) herror
  have ht0 : 0≤t := by dsimp [t]; positivity
  have hellt : ell*t≤1/2 := by
    have hcast : ell*(K:ℝ)≤r := by dsimp [ell]; exact_mod_cast hrK
    calc
      ell*t=ρ*(ell*(K:ℝ))/(r:ℝ) := by dsimp [t]; ring
      _≤ρ := (div_le_iff₀ hrR).2 (by nlinarith)
      _≤1/2 := hρhalf
  have hsin : t/2≤Real.sin (ell*t)/ell := by
    apply (le_div_iff₀ hell).2
    have hh := half_le_sin_of_le_half (mul_nonneg hell.le ht0) hellt
    nlinarith
  have hfinal := transfer_scalar_bound _ delta (eps/ell^4) _ t hA hAdelta
    (div_nonneg heps hell4.le) hinequality hsin ht0
  have hmul := (le_div_iff₀ hell4).mp hfinal
  convert hmul using 1
  dsimp [t,ell]
  ring

end
end DegreeAmplification
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
