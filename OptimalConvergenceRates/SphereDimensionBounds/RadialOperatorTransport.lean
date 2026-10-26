import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.SortedRadialCertificate
import OptimalConvergenceRates.SphereDimensionBounds.CubicDiscriminantDivision

/-! Actual isometric eigenbasis transport of the radial certificate.
All spectral data are constructed from the original nonnegative operator. -/
noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.RadialOperatorTransport
open scoped BigOperators InnerProductSpace
open MvPolynomial ChebyshevSOSKernel WeightedQuadraticSplit WeightedCubicSplit
  OrderedCubicExpansion CubicSpectralDivision RadialSpectralNode
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ
local instance (priority := 2000) finOrderDecidableEq (n : ℕ):DecidableEq (Fin n):=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

def transverseVariables {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n)):Fin (n+1)→Poly (n+1):=
  Fin.cons (X (0:Fin (n+1))) (fun i=>lift (coordinatePolynomial F i))

def transverseMap {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n)):Poly (n+1)→+*Poly (n+1):=
  eval₂Hom C (transverseVariables F)

theorem transverseVariables_degree {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n)) (i : Fin (n + 1)) :
    (transverseVariables F i).totalDegree≤1:=by
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [transverseVariables]
  · exact (totalDegree_rename_le _ _).trans (coordinatePolynomial_homogeneous F j).totalDegree_le

theorem transverseMap_lift {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n)) (p : Poly n) :
    transverseMap F (lift p)=lift (composition F p):=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp [transverseMap,lift,composition]
  | add p q hp hq=>simp only [map_add,hp,hq]
  | mul_X p i hp=>
    simp only [map_mul,hp]
    congr 1
    simp [transverseMap,lift,composition,transverseVariables]

theorem transverseMap_zero_variable {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n)) :
    transverseMap F (X (0:Fin (n+1)))=X (0:Fin (n+1)):=by simp [transverseMap,transverseVariables]

def operatorEnergy {n : ℕ} (L : Point (Fin n) →ₗ[ℝ] Point (Fin n)):Poly n:=∑i,coordinatePolynomial L i^2

theorem operatorEnergy_eval {n : ℕ} (L : Point (Fin n) →ₗ[ℝ] Point (Fin n)) (x : Point (Fin n)) :
    eval (fun i=>x i) (operatorEnergy L)=‖L x‖^2:=by
  simp only [operatorEnergy,map_sum,map_pow,coordinatePolynomial_eval]
  exact (norm_sq _).symm

theorem composition_radius_isometry {n : ℕ} (e : Point (Fin n) ≃ₗᵢ[ℝ] Point (Fin n)) :
    composition e.toLinearEquiv.toLinearMap (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)=OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n:=by
  apply MvPolynomial.funext
  intro y
  let x:Point (Fin n):=evaluationPoint y
  rw [show y=(fun i=>x i) from rfl,composition_eval]
  have hval(z:Point (Fin n)):eval (fun i=>z i) (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)=‖z‖^2:=by
    simpa only [OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial,map_sum,map_pow,eval_X] using (norm_sq z).symm
  rw [hval,hval]
  change ‖e x‖^2=‖x‖^2
  rw [e.norm_map]

/-- Complete actual radial certificate for an arbitrary symmetric
nonnegative operator and actual homogeneous source cubic. -/
theorem operator_radial_boundedSOS {n s : ℕ} (hn : 2 ≤ n) (hs : n ≤ 2 * s)
    (L : Point (Fin n) →ₗ[ℝ] Point (Fin n)) (hL : L.IsSymmetric) (hpos : ∀ x, 0 ≤⟪L x, x⟫_ℝ)
    (Q : Poly n) (hQ : Q.IsHomogeneous 3)
    (hdom:∀x:Point (Fin n),|eval (fun i=>x i) Q|≤2*‖L x‖*‖x‖^2):
    BoundedSOS (3*s+2) ((lift (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n))^(3*s)*
      ((X (0:Fin (n+1)))^2*lift (operatorEnergy L)+X (0:Fin (n+1))*lift Q+
       C (15211*((Nat.clog 2 n:ℝ)+2))*(lift (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n))^2)):=by
  obtain ⟨e,a,ha,hmono,he⟩:=exists_ordered_diagonalization L hL hpos
  let U:=e.toLinearEquiv.toLinearMap
  let V:=e.symm.toLinearEquiv.toLinearMap
  let q:=composition V Q
  have hq:q.IsHomogeneous 3:=composition_homogeneous V Q hQ
  obtain ⟨t,ht12,ht23,ht⟩:=SymmetricCubicTensor.exists_symmetric_tensor q hq
  let T:=tensorForm t
  have hTq:cubicFromTri T=q:=by
    apply MvPolynomial.funext
    intro y
    rw [cubicFromTri_eval]
    change diagonalCubic (tensorForm t) (evaluationPoint y)=eval y q
    rw [←cubicPolynomial_eval,ht]
    rfl
  have hd:∀x:Point (Fin n),|diagonalCubic T x|≤2*‖WeightedQuadraticSplit.diagonal a x‖*‖x‖^2:=by
    intro x
    have hx:‖e.symm x‖=‖x‖:=e.symm.norm_map x
    have hdx:‖L (e.symm x)‖=‖WeightedQuadraticSplit.diagonal a x‖:=by
      calc
        ‖L (e.symm x)‖=‖e (L (e.symm x))‖:=(e.norm_map _).symm
        _=_:=by rw [he,e.apply_symm_apply]
    rw [←cubicPolynomial_eval,ht,composition_eval]
    exact (hdom (e.symm x)).trans_eq (by rw [hx,hdx])
  have hcert:=SortedRadialCertificate.sorted_radial_boundedSOS hn hs a ha hmono T
    (tensorForm_symm12 t ht12) (tensorForm_symm23 t ht23) hd
  rw [hTq] at hcert
  have hqback:composition U q=Q:=by
    apply MvPolynomial.funext
    intro y
    let x:Point (Fin n):=evaluationPoint y
    rw [show y=(fun i=>x i) from rfl,composition_eval,composition_eval]
    change eval (fun i=>e.symm (e x) i) Q=eval (fun i=>x i) Q
    rw [e.symm_apply_apply]
  have hAback:composition U (energyBlock a Finset.univ)=operatorEnergy L:=by
    apply MvPolynomial.funext
    intro y
    let x:Point (Fin n):=evaluationPoint y
    rw [show y=(fun i=>x i) from rfl,composition_eval,operatorEnergy_eval]
    have hnorm:‖WeightedQuadraticSplit.diagonal a (e x)‖=‖L x‖:=by rw [←he,e.norm_map]
    have heval:eval (fun i=>e x i) (energyBlock a Finset.univ)=‖WeightedQuadraticSplit.diagonal a (e x)‖^2:=by
      simp only [energyBlock,map_sum,map_mul,map_pow,eval_C,eval_X,norm_sq,diagonal_apply,mul_pow]
    change eval (fun i=>e x i) (energyBlock a Finset.univ)=‖L x‖^2
    rw [heval,hnorm]
  have hRback:composition U (OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n)=OptimalConvergenceRates.SphereDimensionBounds.Foundation.radiusPolynomial n:=
    composition_radius_isometry e
  have hout:=AffineKernelBridge.boundedSOS_affine_substitution (transverseVariables U) (transverseVariables_degree U) hcert
  change BoundedSOS (3*s+2) (transverseMap U _) at hout
  have hc(c:ℝ):transverseMap U (C c:Poly (n+1))=C c:=by simp [transverseMap]
  simpa only [map_mul,map_add,map_pow,transverseMap_lift,transverseMap_zero_variable,
    hRback,hAback,hqback,hc] using hout

end OptimalConvergenceRates.SphereDimensionBounds.RadialOperatorTransport
