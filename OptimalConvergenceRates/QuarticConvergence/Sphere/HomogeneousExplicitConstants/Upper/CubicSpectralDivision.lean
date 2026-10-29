import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicPolynomialDivision
import Mathlib.Data.Fin.Tuple.Sort

/-! Actual sorted orthonormal spectral transport for cubic polynomial
division. The eigenbasis and its ordering are constructed. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace CubicSpectralDivision
open scoped BigOperators InnerProductSpace
open MvPolynomial WeightedQuadraticSplit WeightedCubicSplit OrderedCubicExpansion

local instance (priority := 2000) finOrderDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

/-- An actual symmetric nonnegative operator has an actual isometric
diagonalization with nonnegative antitone eigenvalues. -/
theorem exists_ordered_diagonalization {n : ℕ} (L : Point (Fin n) →ₗ[ℝ] Point (Fin n))
    (hL : L.IsSymmetric) (hpos : ∀ x, 0 ≤⟪L x, x⟫_ℝ) :
    ∃ (e:Point (Fin n)≃ₗᵢ[ℝ]Point (Fin n)) (a:Fin n→ℝ),
      (∀ i,0≤a i) ∧ Antitone a ∧ ∀ x,e (L x)=diagonal a (e x) := by
  have hdim:Module.finrank ℝ (Point (Fin n))=n:=by simp
  let b0:=hL.eigenvectorBasis hdim
  let v:=hL.eigenvalues hdim
  let s:=Tuple.sort (fun i↦-v i)
  let b:=b0.reindex s.symm
  let a:Fin n→ℝ:=fun i↦v (s i)
  have hv:∀ i,0≤v i:=by
    intro i
    have hh:=hpos (b0 i)
    have hnorm:‖b0 i‖=1:=b0.orthonormal.norm_eq_one i
    have he:L (b0 i)=v i • b0 i:=hL.apply_eigenvectorBasis hdim i
    rw [he,inner_smul_left,real_inner_self_eq_norm_sq,hnorm] at hh
    simpa using hh
  refine ⟨b.repr,a,fun i↦hv (s i),?_,?_⟩
  · have hm:=Tuple.monotone_sort (fun i↦-v i)
    intro i j hij
    have hh:=hm hij
    change -v (s i)≤-v (s j) at hh
    exact neg_le_neg_iff.mp hh
  · intro x
    ext i
    rw [diagonal_apply]
    change (b0.reindex s.symm).repr (L x) i=a i*(b0.reindex s.symm).repr x i
    simp only [OrthonormalBasis.repr_reindex,Equiv.symm_symm]
    exact hL.eigenvectorBasis_apply_self_apply hdim x (s i)

def coordinatePolynomial {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n)) (i : Fin n) :
    MvPolynomial (Fin n) ℝ:=∑ j,C (F (coordinateAxis j) i)*X j

theorem coordinatePolynomial_homogeneous {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n)) (i : Fin
  n) :
    (coordinatePolynomial F i).IsHomogeneous 1:=by
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_X ℝ j).C_mul _

theorem coordinatePolynomial_eval {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n))
    (i : Fin n) (x : Point (Fin n)) : eval (fun j↦x j) (coordinatePolynomial F i)=F x i:=by
  have heq:F x=∑ j,x j • F (coordinateAxis j):=by
    conv_lhs=>rw [←sum_coordinatePiece x]
    simp only [map_sum,coordinatePiece,map_smul]
  rw [heq]
  change eval (fun j↦x j) (coordinatePolynomial F i)=
    (EuclideanSpace.proj i) (∑ j,x j • F (coordinateAxis j))
  simp [coordinatePolynomial,map_sum,map_smul,mul_comm]

def composition {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n)) :
    MvPolynomial (Fin n) ℝ→+*MvPolynomial (Fin n) ℝ:=eval₂Hom C (coordinatePolynomial F)

theorem composition_homogeneous {n k : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n))
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous k) : (composition F p).IsHomogeneous k:=
  CubicPrefixPadding.homogeneous_linear_substitution _ (coordinatePolynomial_homogeneous F) p hp

theorem composition_eval {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n))
    (p : MvPolynomial (Fin n) ℝ) (x : Point (Fin n)) :
    eval (fun j↦x j) (composition F p)=eval (fun j↦F x j) p:=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp [composition]
  | add p q hp hq=>simp [map_add,hp,hq]
  | mul_X p i hp=>
    simp only [map_mul,hp,eval_X]
    congr 1
    simpa only [composition,eval₂Hom_X'] using coordinatePolynomial_eval F i x

def vectorPolynomial {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n))
    (b : Fin n → MvPolynomial (Fin n) ℝ) (i : Fin n) : MvPolynomial (Fin n) ℝ:=
  ∑ j,C (F (coordinateAxis j) i)*b j

def polynomialValue {n : ℕ} (b : Fin n → MvPolynomial (Fin n) ℝ) (x : Point (Fin n)) : Point (Fin
  n):=
  (WithLp.equiv 2 (Fin n→ℝ)).symm (fun i↦eval (fun j↦x j) (b i))

theorem vectorPolynomial_homogeneous {n k : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n))
    (b : Fin n → MvPolynomial (Fin n) ℝ) (hb : ∀ i, (b i).IsHomogeneous k) (i : Fin n) :
    (vectorPolynomial F b i).IsHomogeneous k:=by
  apply IsHomogeneous.sum
  intro j _
  exact (hb j).C_mul _

theorem vectorPolynomial_eval {n : ℕ} (F : Point (Fin n) →ₗ[ℝ] Point (Fin n))
    (b : Fin n → MvPolynomial (Fin n) ℝ) (i : Fin n) (x : Point (Fin n)) :
    eval (fun j↦x j) (vectorPolynomial F b i)=F (polynomialValue b x) i:=by
  have hh:=coordinatePolynomial_eval F i (polynomialValue b x)
  simpa only [coordinatePolynomial,vectorPolynomial,map_sum,map_mul,eval_C,eval_X,polynomialValue]
    using! hh

/-- The actual quadratic polynomial division theorem for every symmetric
nonnegative operator, with its spectral data constructed in the proof. -/
theorem exists_quadratic_division {n : ℕ} (hn : 0 < n)
    (L : Point (Fin n) →ₗ[ℝ] Point (Fin n)) (hL : L.IsSymmetric) (hpos : ∀ x, 0 ≤⟪L x, x⟫_ℝ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous 3)
    (hdom : ∀ x:Point (Fin n),|eval (fun i↦x i) p|≤2*‖L x‖*‖x‖^2) :
    ∃ b:Fin n→MvPolynomial (Fin n) ℝ,(∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,coordinatePolynomial L i*b i)=p ∧
      ∀ h:Point (Fin n),‖polynomialValue b h‖≤80*((Nat.clog 2 n:ℝ)+1)*‖h‖^2:=by
  obtain ⟨e,a,ha,hmono,he⟩:=exists_ordered_diagonalization L hL hpos
  let U:=e.toLinearEquiv.toLinearMap
  let V:=e.symm.toLinearEquiv.toLinearMap
  let q:=composition V p
  have hq:q.IsHomogeneous 3:=composition_homogeneous V p hp
  have hd:∀ x:Point (Fin n),|eval (fun i↦x i) q|≤2*‖diagonal a x‖*‖x‖^2:=by
    intro x
    rw [composition_eval]
    have hh:=hdom (e.symm x)
    have hx:‖e.symm x‖=‖x‖:=e.symm.norm_map x
    have hdx:‖L (e.symm x)‖=‖diagonal a x‖:=by
      calc
        ‖L (e.symm x)‖=‖e (L (e.symm x))‖:=(e.norm_map _).symm
        _=‖diagonal a x‖:=by rw [he,e.apply_symm_apply]
    simpa only [hx,hdx] using! hh
  obtain ⟨bn,hbn,hid,hbound⟩:=CubicPolynomialDivision.exists_quadratic_division hn a ha hmono q hq
    hd
  let c:Fin n→MvPolynomial (Fin n) ℝ:=fun j↦composition U (bn j)
  let b:Fin n→MvPolynomial (Fin n) ℝ:=vectorPolynomial V c
  have hb:∀ i,(b i).IsHomogeneous 2:=vectorPolynomial_homogeneous V c
    (fun j↦composition_homogeneous U _ (hbn j))
  have hcval (x:Point (Fin n)) : polynomialValue c x=polynomialValue bn (e x):=by
    ext j
    change eval (fun k↦x k) (composition U (bn j))=_
    exact composition_eval U (bn j) x
  have hbval (x:Point (Fin n)) : polynomialValue b x=e.symm (polynomialValue bn (e x)):=by
    ext i
    change eval (fun j↦x j) (vectorPolynomial V c i)=_
    rw [vectorPolynomial_eval,hcval]
    rfl
  have hpair (x:Point (Fin n)) : ⟪L x,polynomialValue b x⟫_ℝ=eval (fun j↦x j) p:=by
    have hidval:=congrArg (eval (fun j↦e x j)) hid
    simp only [map_sum,map_mul,eval_C,eval_X] at hidval
    have hqval:eval (fun j↦e x j) q=eval (fun j↦x j) p:=by
      rw [composition_eval]
      change eval (fun j↦e.symm (e x) j) p=_
      rw [e.symm_apply_apply]
    rw [hqval] at hidval
    rw [hbval,←e.inner_map_map,he,e.apply_symm_apply]
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,diagonal_apply,polynomialValue]
    convert hidval using 1
    apply Finset.sum_congr rfl
    intro i _
    change eval (fun j↦e x j) (bn i)*(a i*e x i)=a i*e x i*eval (fun j↦e x j) (bn i)
    ring
  refine ⟨b,hb,?_,?_⟩
  · apply MvPolynomial.funext
    intro x
    let xx:Point (Fin n):=evaluationPoint x
    have hh:=hpair xx
    simp only [map_sum,map_mul]
    change (∑ i,eval (fun j↦xx j) (coordinatePolynomial L i)*eval (fun j↦xx j) (b i))=eval (fun
      j↦xx j) p
    simp only [coordinatePolynomial_eval]
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,polynomialValue] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    change L xx i*eval (fun j↦xx j) (b i)=eval (fun j↦xx j) (b i)*L xx i
    ring
  · intro x
    rw [hbval,e.symm.norm_map]
    exact (hbound (e x)).trans (by rw [e.norm_map])

/-- The fully scaled actual polynomial division bound used by selector
centering: squared norm<=6400L²MR². The zeroM case is included. -/
theorem exists_quadratic_division_scaled {n : ℕ} (hn : 0 < n)
    (L : Point (Fin n) →ₗ[ℝ] Point (Fin n)) (hL : L.IsSymmetric) (hpos : ∀ x, 0 ≤⟪L x, x⟫_ℝ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous 3) {M : ℝ} (hM : 0 ≤ M)
    (hdom : ∀ x:Point (Fin n),|eval (fun i↦x i) p|≤2*Real.sqrt M*‖L x‖*‖x‖^2) :
    ∃ b:Fin n→MvPolynomial (Fin n) ℝ,(∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,coordinatePolynomial L i*b i)=p ∧
      ∀ h:Point (Fin n),(∑ i,(eval (fun j↦h j) (b i))^2)≤
        6400*((Nat.clog 2 n:ℝ)+1)^2*M*‖h‖^4:=by
  by_cases hM0:M=0
  · have hp0:p=0:=by
      apply MvPolynomial.funext
      intro x
      have hh:=hdom (evaluationPoint x)
      simp only [hM0,Real.sqrt_zero,mul_zero,zero_mul] at hh
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    refine ⟨fun _↦0,fun _↦isHomogeneous_zero (Fin n) ℝ 2,?_,?_⟩
    · simp [hp0]
    · intro h;simp [hM0]
  have hMp:0<M:=lt_of_le_of_ne hM (Ne.symm hM0)
  let alpha:=Real.sqrt M
  have halpha:0<alpha:=Real.sqrt_pos.mpr hMp
  let q:MvPolynomial (Fin n) ℝ:=C (1/alpha)*p
  have hq:q.IsHomogeneous 3:=hp.C_mul _
  have hd:∀ x:Point (Fin n),|eval (fun i↦x i) q|≤2*‖L x‖*‖x‖^2:=by
    intro x
    have hev:|eval (fun i↦x i) q|=|eval (fun i↦x i) p|/alpha:=by
      simp only [q,map_mul,eval_C,abs_mul,abs_div,abs_one,abs_of_pos halpha]
      ring
    rw [hev]
    apply (div_le_iff₀ halpha).mpr
    have hh:=hdom x
    convert hh using 1;ring
  obtain ⟨c,hc,hid,hbound⟩:=exists_quadratic_division hn L hL hpos q hq hd
  let b:Fin n→MvPolynomial (Fin n) ℝ:=fun i↦C alpha*c i
  have hb:∀ i,(b i).IsHomogeneous 2:=fun i↦(hc i).C_mul alpha
  have hidb:(∑ i,coordinatePolynomial L i*b i)=p:=by
    calc
      _=C alpha*(∑ i,coordinatePolynomial L i*c i):=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [b]
        ring
      _=C alpha*q:=by rw [hid]
      _=p:=by
        dsimp [q]
        rw [←mul_assoc,←map_mul]
        have he:alpha*(1/alpha)=1:=by field_simp [halpha.ne']
        rw [he,map_one,one_mul]
  refine ⟨b,hb,hidb,?_⟩
  intro h
  have heq:polynomialValue b h=alpha•polynomialValue c h:=by
    ext i
    change eval (fun j↦h j) (C alpha*c i)=alpha*eval (fun j↦h j) (c i)
    simp
  have hn:‖polynomialValue b h‖≤80*((Nat.clog 2 n:ℝ)+1)*alpha*‖h‖^2:=by
    rw [heq,norm_smul,Real.norm_eq_abs,abs_of_pos halpha]
    have hh:=mul_le_mul_of_nonneg_left (hbound h) halpha.le
    convert hh using 1;ring
  have hs:=(sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0≤80*((Nat.clog 2 n:ℝ)+1)*alpha*‖h‖^2)).mpr hn
  rw [norm_sq] at hs
  have hasq:alpha^2=M:=Real.sq_sqrt hM
  change (∑ i,(eval (fun j↦h j) (b i))^2)≤_ at hs
  convert hs using 1
  rw [←hasq]
  ring

end CubicSpectralDivision
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
