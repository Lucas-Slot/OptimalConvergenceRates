import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.CubicPrefixSingular

/-! Actual zero tensor padding and polynomial restriction for arbitrary
positive coordinate dimension. The source constant is retained exactly. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace CubicPrefixPadding
open scoped BigOperators
open MvPolynomial WeightedQuadraticSplit WeightedQuadraticPadding WeightedCubicSplit
  OrderedCubicExpansion CubicPrefixTree BalancedCubicTree CubicPrefixSingular

local instance (priority := 2000) finOrderDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  (inferInstance : LinearOrder (Fin n)).toDecidableEq

def restriction {n : ℕ} (m : ℕ) : Point (Fin (n+m))→ₗ[ℝ]Point (Fin n) where
  toFun:=restrict m
  map_add' x y:=by ext i;rfl
  map_smul' r x:=by ext i;rfl

@[simp] theorem restriction_apply {n : ℕ} (m : ℕ) (x : Point (Fin (n + m))) : restriction m
  x=restrict m x:=rfl

def padTri {n : ℕ} (m : ℕ) (T : Tri (Point (Fin n))) : Tri (Point (Fin (n+m))) :=
  LinearMap.mk₂ ℝ (fun x y↦(T (restriction m x) (restriction m y)).comp (restriction m))
    (by intro x y z;ext w;simp [map_add,LinearMap.comp_apply])
    (by intro r x y;ext w;simp [map_smul,LinearMap.comp_apply])
    (by intro x y z;ext w;simp [map_add,LinearMap.comp_apply])
    (by intro r x y;ext w;simp [map_smul,LinearMap.comp_apply])

@[simp] theorem padTri_apply {n : ℕ} (m : ℕ) (T : Tri (Point (Fin n))) (x y z : Point (Fin (n +
  m))) :
    padTri m T x y z=T (restrict m x) (restrict m y) (restrict m z):=rfl

theorem padTri_symm12 {n : ℕ} (m : ℕ) (T : Tri (Point (Fin n)))
    (hT : ∀ x y z, T x y z = T y x z) : ∀ x y z,padTri m T x y z=padTri m T y x z:=by
  intro x y z;exact hT _ _ _

theorem padTri_symm23 {n : ℕ} (m : ℕ) (T : Tri (Point (Fin n)))
    (hT : ∀ x y z, T x y z = T x z y) : ∀ x y z,padTri m T x y z=padTri m T x z y:=by
  intro x y z;exact hT _ _ _

theorem padSpectrum_nonneg {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ) (ha : ∀ i, 0 ≤ a i) :
    ∀ j,0≤padSpectrum a hn m j:=by
  intro j
  refine Fin.addCases (m:=n) (n:=m) (fun j↦?_) (fun j↦?_) j
  · simpa only [padSpectrum,Fin.append_left] using ha j
  · simpa only [padSpectrum,Fin.append_right] using ha (lastIndex hn)

theorem restriction_diagonal {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ) (z : Point (Fin (n +
  m))) :
    restrict m (diagonal (padSpectrum a hn m) z)=diagonal a (restrict m z):=by
  ext i
  simp [restrict,diagonal_apply,padSpectrum]

/-- Padding by zero cubic coefficients retains the original source
constant2, although the additional spectral coordinates may be nonzero. -/
theorem padTri_domination {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) (m : ℕ) (T : Tri (Point (Fin n)))
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) :
    ∀ x,|diagonalCubic (padTri m T) x|≤2*‖diagonal (padSpectrum a hn m) x‖*‖x‖^2:=by
  intro x
  have hdx:=norm_restrict_le (m:=m) (diagonal (padSpectrum a hn m) x)
  rw [restriction_diagonal] at hdx
  have hx:=norm_restrict_le (m:=m) x
  have hb:=hdom (restrict m x)
  change |diagonalCubic T (restrict m x)|≤_
  exact hb.trans (by gcongr)

def restrictionVariables (n m : ℕ) : Fin (n+m)→MvPolynomial (Fin n) ℝ :=
  Fin.append (fun i↦X i) (fun _↦0)

def polynomialRestriction (n m : ℕ) : MvPolynomial (Fin (n+m)) ℝ→+*MvPolynomial (Fin n) ℝ :=
  eval₂Hom C (restrictionVariables n m)

@[simp] theorem polynomialRestriction_eval {n m : ℕ} (p : MvPolynomial (Fin (n + m)) ℝ) (h : Point
  (Fin n)) :
    eval (fun i↦h i) (polynomialRestriction n m p)=eval (fun i↦embed m h i) p:=by
  induction p using MvPolynomial.induction_on with
  | C c=>simp [polynomialRestriction]
  | add p q hp hq=>simp [map_add,hp,hq]
  | mul_X p j hp=>
    simp only [map_mul,hp,eval_X,polynomialRestriction,eval₂Hom_X']
    congr 1
    refine Fin.addCases (m:=n) (n:=m) (fun i↦?_) (fun i↦?_) j
    · simp [restrictionVariables,embed]
    · simp [restrictionVariables,embed]

/-- Homogeneous linear substitution, permitting zero coordinate images,
preserves actual homogeneous degree. -/
theorem homogeneous_linear_substitution {n m k : ℕ} (f : Fin n → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i, (f i).IsHomogeneous 1) (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous k) :
    ((eval₂Hom C f) p).IsHomogeneous k:=by
  classical
  rw [←p.support_sum_monomial_coeff,map_sum]
  apply IsHomogeneous.sum
  intro e he
  rw [eval₂Hom_monomial]
  have hdeg:(∑ i∈e.support,e i)=k:=by
    simpa only [Finsupp.weight_apply,Pi.one_apply,smul_eq_mul,mul_one,Finsupp.sum] using hp
      (mem_support_iff.mp he)
  have hprod:(e.prod (fun i r↦f i^r)).IsHomogeneous (∑ i∈e.support,e i):=by
    apply IsHomogeneous.prod
    intro i hi
    simpa only [Nat.one_mul] using (hf i).pow (e i)
  simpa only [hdeg] using hprod.C_mul (p.coeff e)

theorem polynomialRestriction_homogeneous {n m k : ℕ} (p : MvPolynomial (Fin (n + m)) ℝ)
    (hp : p.IsHomogeneous k) : (polynomialRestriction n m p).IsHomogeneous k:=by
  apply homogeneous_linear_substitution _ _ p hp
  intro j
  refine Fin.addCases (m:=n) (n:=m) (fun i↦?_) (fun i↦?_) j
  · simpa [restrictionVariables] using isHomogeneous_X ℝ i
  · simpa [restrictionVariables] using (isHomogeneous_zero (Fin n) ℝ 1)

@[simp] theorem restrict_embed_point {n : ℕ} (m : ℕ) (h : Point (Fin n)) : restrict m (embed m
  h)=h:=by
  ext i
  simp [restrict,embed]

@[simp] theorem embed_prefix {n : ℕ} (m : ℕ) (h : Point (Fin n)) (i : Fin n) : embed m h
  (Fin.castAdd m i)=h i:=by
  simp [embed]

@[simp] theorem embed_tail {n : ℕ} (m : ℕ) (h : Point (Fin n)) (i : Fin m) : embed m h (Fin.natAdd
  n i)=0:=by
  simp [embed]

/-- Actual arbitrary-dimension cubic division by padding only zero tensor
coefficients and restricting actual polynomial outputs. -/
theorem exists_quadratic_division_of_le_pow {n d : ℕ} (hn : 0 < n) (hnd : n ≤ 2 ^ d)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (T : Tri (Point (Fin n)))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) :
    ∃ b:Fin n→MvPolynomial (Fin n) ℝ,(∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,C (a i)*X i*b i)=cubicFromTri T ∧
      ∀ h:Point (Fin n),‖(WithLp.equiv 2 (Fin n→ℝ)).symm
        (fun i↦eval (fun j↦h j) (b i))‖≤80*((d:ℝ)+1)*‖h‖^2:=by
  let m:=2^d-n
  have heq:n+m=2^d:=Nat.add_sub_of_le hnd
  have hfull:=CubicPrefixSingular.exists_quadratic_division_semidefinite (d:=d)
  rw [←heq] at hfull
  obtain ⟨bp,hbp,hid,hnorm⟩:=hfull (padSpectrum a hn m) (padSpectrum_nonneg a hn m ha)
    (padSpectrum_antitone a hn m hmono) (padTri m T) (padTri_symm12 m T h12) (padTri_symm23 m T h23)
    (padTri_domination a hn m T hdom)
  let b:Fin n→MvPolynomial (Fin n) ℝ:=fun i↦polynomialRestriction n m (bp (Fin.castAdd m i))
  refine ⟨b,fun i↦polynomialRestriction_homogeneous _ (hbp _),?_,?_⟩
  · apply MvPolynomial.funext
    intro x
    let h:Point (Fin n):=evaluationPoint x
    have hiden:=congrArg (eval (fun j↦embed m h j)) hid
    simp only [map_sum,map_mul,eval_C,eval_X,cubicFromTri_eval] at hiden
    change (∑ j,padSpectrum a hn m j*embed m h j*eval (fun k↦embed m h k) (bp j))=
      diagonalCubic (padTri m T) (embed m h) at hiden
    rw [diagonalCubic,padTri_apply,restrict_embed_point] at hiden
    rw [Fin.sum_univ_add] at hiden
    simp only [padSpectrum,Fin.append_left,Fin.append_right,embed_prefix,embed_tail,
      mul_zero,zero_mul,Finset.sum_const_zero,add_zero] at hiden
    simp only [map_sum,map_mul,eval_C,eval_X,cubicFromTri_eval]
    change (∑ i,a i*h i*eval (fun j↦h j) (polynomialRestriction n m (bp (Fin.castAdd m i))))=
      diagonalCubic T h
    simp only [polynomialRestriction_eval]
    exact hiden
  · intro h
    let v:Point (Fin (n+m)):=(WithLp.equiv 2 (Fin (n+m)→ℝ)).symm
      (fun i↦eval (fun j↦embed m h j) (bp i))
    have hsv:(WithLp.equiv 2 (Fin n→ℝ)).symm (fun i↦eval (fun j↦h j) (b i))=restrict m v:=by
      ext i
      change eval (fun j↦h j) (polynomialRestriction n m (bp (Fin.castAdd m i)))=_
      rw [polynomialRestriction_eval]
      rfl
    rw [hsv]
    exact (norm_restrict_le v).trans (by simpa only [norm_embed] using hnorm (embed m h))

/-- The cubic division theorem in every nonzero coordinate dimension,
including every singular nonnegative antitone spectrum. -/
theorem exists_quadratic_division {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hmono : Antitone a) (T : Tri (Point (Fin n)))
    (h12 : ∀ x y z, T x y z = T y x z) (h23 : ∀ x y z, T x y z = T x z y)
    (hdom : ∀ x, |diagonalCubic T x| ≤ 2*‖diagonal a x‖ * ‖x‖ ^ 2) :
    ∃ b:Fin n→MvPolynomial (Fin n) ℝ,(∀ i,(b i).IsHomogeneous 2) ∧
      (∑ i,C (a i)*X i*b i)=cubicFromTri T ∧
      ∀ h:Point (Fin n),‖(WithLp.equiv 2 (Fin n→ℝ)).symm
        (fun i↦eval (fun j↦h j) (b i))‖≤80*((Nat.clog 2 n:ℝ)+1)*‖h‖^2:=
  exists_quadratic_division_of_le_pow hn (Nat.le_pow_clog (by norm_num : 1<2) n) a ha hmono T h12
    h23 hdom

end CubicPrefixPadding
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
