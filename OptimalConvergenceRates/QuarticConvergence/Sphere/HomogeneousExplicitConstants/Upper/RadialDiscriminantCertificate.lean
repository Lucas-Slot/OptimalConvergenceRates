import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.RadialOperatorTransport

/-! Complete actual quadratic-cubic radial SOS from the discriminant,
including zero M and singular quadratic forms. -/
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace RadialDiscriminantCertificate
open scoped BigOperators InnerProductSpace
open MvPolynomial ChebyshevSOSKernel WeightedQuadraticSplit OrderedCubicExpansion
  RadialSpectralNode RadialOperatorTransport
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

def radialBudget (n : ℕ):ℝ:=15211*((Nat.clog 2 n:ℝ)+2)

theorem unit_discriminant_boundedSOS {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (A Q : Poly n) (hA : A.IsHomogeneous 2) (hQ : Q.IsHomogeneous 3)
    (hA0:∀x:Fin n→ℝ,0≤eval x A)
    (hdisc:∀x:Point (Fin n),(eval (fun i↦x i) Q)^2≤4*eval (fun i↦x i) A*‖x‖^4):
    BoundedSOS (3*s+2) ((lift (Foundation.radiusPolynomial n))^(3*s)*
      ((X (0:Fin (n+1)))^2*lift A+X (0:Fin (n+1))*lift Q+
       C (radialBudget n)*(lift (Foundation.radiusPolynomial n))^2)):=by
  obtain ⟨L,hL,hpos,hLA⟩:=CubicDiscriminantDivision.nonnegative_quadratic_operator A hA hA0
  have hd:∀x:Point (Fin n),|eval (fun i↦x i) Q|≤2*‖L x‖*‖x‖^2:=by
    intro x
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤2*‖L x‖*‖x‖^2)).mp
    rw [sq_abs]
    have hh:=hdisc x
    rw [←hLA] at hh
    convert hh using 1
    ring
  have henergy:operatorEnergy L=A:=by
    apply MvPolynomial.funext
    intro y
    let x:Point (Fin n):=evaluationPoint y
    rw [show y=(fun i↦x i) from rfl,operatorEnergy_eval,hLA]
  have hh:=operator_radial_boundedSOS hn hs L hL hpos Q hQ hd
  rwa [henergy] at hh

/-- Actual radial certificate with the published logarithmic constant
and exact root3s+2. No factorization, eigenbasis, matrix completion,
selector, or SOS certificate is assumed. -/
theorem discriminant_boundedSOS {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (A Q : Poly n) (hA : A.IsHomogeneous 2) (hQ : Q.IsHomogeneous 3)
    (hA0:∀x:Fin n→ℝ,0≤eval x A) {M:ℝ} (hM:0≤M)
    (hdisc:∀x:Point (Fin n),(eval (fun i↦x i) Q)^2≤4*M*eval (fun i↦x i) A*‖x‖^4):
    BoundedSOS (3*s+2) ((lift (Foundation.radiusPolynomial n))^(3*s)*
      ((X (0:Fin (n+1)))^2*lift A+X (0:Fin (n+1))*lift Q+
       C (radialBudget n*M)*(lift (Foundation.radiusPolynomial n))^2)):=by
  by_cases hM0:M=0
  · have hQ0:Q=0:=by
      apply MvPolynomial.funext
      intro y
      let x:Point (Fin n):=evaluationPoint y
      have hh:=hdisc x
      simp only [hM0,mul_zero,zero_mul] at hh
      simp only [map_zero]
      change eval (fun i↦x i) Q=0
      nlinarith [sq_nonneg (eval (fun i↦x i) Q)]
    obtain ⟨b,hb,hid⟩:=QuadraticBoundSOS.nonnegative_quadratic_exists_squares A hA hA0
    have hAsos:BoundedSOS 1 A:=by rw [hid];exact BoundedSOS.of_family b (fun i↦(hb
      i).totalDegree_le)
    have hAz:BoundedSOS 2 ((X (0:Fin (n+1)))^2*lift A):=
      (BoundedSOS.square _ (by simp)).mul (hAsos.rename Fin.succ)
    have hh:=(RadialNodeSOS.radius_power_boundedSOS (s:=3*s) lift_radius_sos).mul hAz
    simpa only [hM0,hQ0,map_zero,mul_zero,zero_mul,add_zero] using hh
  have hMp:0<M:=lt_of_le_of_ne hM (Ne.symm hM0)
  let Ap:Poly n:=C (1/M)*A
  let Qp:Poly n:=C (1/M)*Q
  have hAp:Ap.IsHomogeneous 2:=hA.C_mul _
  have hQp:Qp.IsHomogeneous 3:=hQ.C_mul _
  have hAp0:∀x:Fin n→ℝ,0≤eval x Ap:=by
    intro x
    change 0≤eval x (C (1/M)*A)
    rw [eval_mul,eval_C]
    exact mul_nonneg (by positivity) (hA0 x)
  have hdiscp:∀x:Point (Fin n),(eval (fun i↦x i) Qp)^2≤4*eval (fun i↦x i) Ap*‖x‖^4:=by
    intro x
    calc
      (eval (fun i↦x i) Qp)^2=(1/M)^2*(eval (fun i↦x i) Q)^2:=by simp [Qp,mul_pow]
      _≤(1/M)^2*(4*M*eval (fun i↦x i) A*‖x‖^4):=
        mul_le_mul_of_nonneg_left (hdisc x) (sq_nonneg _)
      _=4*eval (fun i↦x i) Ap*‖x‖^4:=by
        simp only [Ap,eval_mul,eval_C]
        field_simp
  have hh:=(unit_discriminant_boundedSOS hn hs Ap Qp hAp hQp hAp0 hdiscp).scale M hM
  have hi:(C M:Poly (n+1))*C (1/M)=1:=by
    change C M*C (1/M)=C (1:ℝ)
    rw [←map_mul]
    congr 1
    field_simp
  have hid:C M*((lift (Foundation.radiusPolynomial n))^(3*s)*
      ((X (0:Fin (n+1)))^2*lift Ap+X (0:Fin (n+1))*lift Qp+
       C (radialBudget n)*(lift (Foundation.radiusPolynomial n))^2))=
      (lift (Foundation.radiusPolynomial n))^(3*s)*
      ((X (0:Fin (n+1)))^2*lift A+X (0:Fin (n+1))*lift Q+
       C (radialBudget n*M)*(lift (Foundation.radiusPolynomial n))^2):=by
    simp only [Ap,Qp,map_mul,SortedRadialCertificate.lift_constant]
    calc
      _=(lift (Foundation.radiusPolynomial n))^(3*s)*
          (((C M:Poly (n+1))*C (1/M))*((X (0:Fin (n+1)))^2*lift A+X (0:Fin (n+1))*lift Q)+
          (C (radialBudget n)*C M)*(lift (Foundation.radiusPolynomial n))^2):=by ring
      _=_:=by rw [hi];simp
  rwa [hid] at hh

end RadialDiscriminantCertificate
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
