import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.AffineKernelBridge
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.RadialSpectralNode

/-! Exact longitudinal normalization of the actual radial SOS certificate,
with no change to transverse scaleVariables or square-root degree. -/
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace RadialLongitudinalScale
open scoped BigOperators
open MvPolynomial ChebyshevSOSKernel RadialSpectralNode
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

def scaleVariables {n : ℕ} (c : ℝ):Fin (n+1)→Poly (n+1):=
  Fin.cons (C c*X (0:Fin (n+1))) (fun i↦X i.succ)

def scaleMap {n : ℕ} (c : ℝ):Poly (n+1)→+*Poly (n+1):=eval₂Hom C (scaleVariables c)

theorem scaleVariables_degree {n : ℕ} (c : ℝ) (i : Fin (n + 1)):(scaleVariables c
  i).totalDegree≤1:=by
  refine Fin.cases ?_ (fun j↦?_) i
  · change (C c*X (0:Fin (n+1))).totalDegree≤1
    exact (totalDegree_mul _ _).trans (by simp)
  · simp [scaleVariables]

theorem scaleMap_lift {n : ℕ} (c : ℝ) (p : Poly n):scaleMap c (lift p)=lift p:=by
  induction p using MvPolynomial.induction_on with
  | C a=>simp [scaleMap,lift]
  | add p q hp hq=>simp only [map_add,hp,hq]
  | mul_X p i hp=>
    simp only [map_mul,hp]
    congr 1
    simp [scaleMap,lift,scaleVariables]

theorem scaleMap_zero_variable {n : ℕ} (c : ℝ) :
    scaleMap c (X (0:Fin (n+1)))=C c*X (0:Fin (n+1)):=by simp [scaleMap,scaleVariables]

theorem normalize_boundedSOS {n r m : ℕ} (R A Q : Poly n) (k : ℝ)
    (h : BoundedSOS r ((lift R) ^ m * (C 15211 * (X (0 : Fin (n + 1))) ^ 2 * lift A +
      X (0 : Fin (n + 1)) * lift Q + C k * (lift R) ^ 2))) :
    BoundedSOS r ((lift R)^m*((X (0:Fin (n+1)))^2*lift A+
      X (0:Fin (n+1))*lift Q+C (15211*k)*(lift R)^2)):=by
  have hs:=AffineKernelBridge.boundedSOS_affine_substitution (scaleVariables ((1:ℝ)/15211))
    (scaleVariables_degree ((1:ℝ)/15211)) h
  change BoundedSOS r (scaleMap ((1:ℝ)/15211) _) at hs
  simp only [map_mul,map_add,map_pow,scaleMap_lift,scaleMap_zero_variable] at hs
  have hconst(c:ℝ):scaleMap ((1:ℝ)/15211) (C c:Poly (n+1))=C c:=by simp [scaleMap]
  simp only [hconst] at hs
  have hscaled:=hs.scale 15211 (by norm_num)
  have hinv:(C (15211:ℝ):Poly (n+1))*C ((1:ℝ)/15211)=1:=by
    change C (15211:ℝ)*C ((1:ℝ)/15211)=C (1:ℝ)
    rw [←map_mul]
    norm_num
  have hid:C (15211:ℝ)*((lift R)^m*(C 15211*(C ((1:ℝ)/15211)*X (0:Fin (n+1)))^2*lift A+
      (C ((1:ℝ)/15211)*X (0:Fin (n+1)))*lift Q+C k*(lift R)^2))=
      (lift R)^m*((X (0:Fin (n+1)))^2*lift A+X (0:Fin (n+1))*lift Q+C (15211*k)*(lift R)^2):=by
    calc
      _=(lift R)^m*(((C (15211:ℝ):Poly (n+1))*C ((1:ℝ)/15211))^2*(X (0:Fin (n+1)))^2*lift A+
          ((C (15211:ℝ):Poly (n+1))*C ((1:ℝ)/15211))*X (0:Fin (n+1))*lift Q+
          C (15211*k)*(lift R)^2):=by rw [map_mul];ring
      _=_:=by rw [hinv];simp
  rwa [hid] at hscaled

end RadialLongitudinalScale
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
