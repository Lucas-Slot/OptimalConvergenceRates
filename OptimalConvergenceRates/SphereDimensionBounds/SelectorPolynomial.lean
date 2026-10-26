import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OptimalConvergenceRates.SphereDimensionBounds.SelectorDual
import OptimalConvergenceRates.SphereDimensionBounds.SelectorFunctional

/-! Actual polynomial realizations of selector coefficient arrays, and the
bridge from coefficient duality to the finite polynomial functional. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.SelectorPolynomial

set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Matrix
open MvPolynomial SelectorCone

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℝ

def linPolynomial {n : ℕ} : Lin n →ₗ[ℝ] Poly n :=
  ∑ i, (LinearMap.proj i).smulRight (X i)

def quadPolynomial {n : ℕ} : Quad n →ₗ[ℝ] Poly n where
  toFun H := ∑ i, ∑ j, C (H i j)*X i*X j
  map_add' H K := by
    simp only [Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c H := by
    simp only [RingHom.id_apply, Matrix.smul_apply, smul_eq_mul, map_mul, smul_eq_C_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

def tensorPolynomial {n d : ℕ} : ((Fin d → Fin n) → ℝ) →ₗ[ℝ] Poly n :=
  ∑ f, (LinearMap.proj f).smulRight (∏ i, X (f i))

theorem linPolynomial_apply {n : ℕ} (l : Lin n) :
    linPolynomial l=∑ i, C (l i)*X i := by
  simp only [linPolynomial,LinearMap.sum_apply,LinearMap.smulRight_apply,
    LinearMap.proj_apply,smul_eq_C_mul]

theorem quadPolynomial_apply {n : ℕ} (H : Quad n) :
    quadPolynomial H=∑ i, ∑ j, C (H i j)*X i*X j := rfl

theorem tensorPolynomial_apply {n d : ℕ} (c : (Fin d → Fin n) → ℝ) :
    tensorPolynomial c=∑ f, C (c f)*∏ i, X (f i) := by
  simp only [tensorPolynomial,LinearMap.sum_apply,LinearMap.smulRight_apply,
    LinearMap.proj_apply,smul_eq_C_mul]

theorem linPolynomial_eval {n : ℕ} (l : Lin n) (h : Fin n → ℝ) :
    eval h (linPolynomial l)=linEval h l := by
  simp [linPolynomial_apply,linEval]

theorem quadPolynomial_eval {n : ℕ} (H : Quad n) (h : Fin n → ℝ) :
    eval h (quadPolynomial H)=quadEval h H := by
  simp [quadPolynomial_apply,quadEval]

theorem tensorPolynomial_eval {n d : ℕ} (c : (Fin d → Fin n) → ℝ) (h : Fin n → ℝ) :
    eval h (tensorPolynomial c)=tensorEval h c := by
  simp [tensorPolynomial_apply,tensorEval]

theorem linPolynomial_homogeneous {n : ℕ} (l : Lin n) :
    (linPolynomial l).IsHomogeneous 1 := by
  rw [linPolynomial_apply]
  exact IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X (l i) i)

theorem quadPolynomial_homogeneous {n : ℕ} (H : Quad n) :
    (quadPolynomial H).IsHomogeneous 2 := by
  rw [quadPolynomial_apply]
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  simpa using ((isHomogeneous_X ℝ i).C_mul (H i j)).mul (isHomogeneous_X ℝ j)

theorem tensorPolynomial_homogeneous {n d : ℕ} (c : (Fin d → Fin n) → ℝ) :
    (tensorPolynomial c).IsHomogeneous d := by
  rw [tensorPolynomial_apply]
  apply IsHomogeneous.sum
  intro f _
  have hprod : (∏ i : Fin d, (X (f i) : Poly n)).IsHomogeneous d := by
    simpa using IsHomogeneous.prod Finset.univ (fun i : Fin d => (X (f i) : Poly n))
      (fun _ => 1) (fun i _ => isHomogeneous_X ℝ (f i))
  exact hprod.C_mul (c f)

theorem linPolynomial_single {n : ℕ} (i : Fin n) (a : ℝ) :
    linPolynomial (Pi.single i a)=C a*X i := by
  classical
  simp [linPolynomial_apply,Pi.single_apply,apply_ite,ite_mul]

theorem tensorPolynomial_single {n d : ℕ} (f : Fin d → Fin n) (a : ℝ) :
    tensorPolynomial (Pi.single f a)=C a*∏ i, X (f i) := by
  classical
  simp [tensorPolynomial_apply,Pi.single_apply,apply_ite,ite_mul]

theorem exists_linPolynomial {n : ℕ} (p : Poly n) (hp : p.IsHomogeneous 1) :
    ∃ l : Lin n, linPolynomial l=p := by
  classical
  have hmem : p ∈ LinearMap.range (linPolynomial (n:=n)) := by
    rw [← p.support_sum_monomial_coeff]
    apply Submodule.sum_mem
    intro e he
    have hd : e.sum (fun _ k => k)=1 := by
      simpa only [Finsupp.weight_apply,Pi.one_apply,smul_eq_mul,mul_one] using
        hp (mem_support_iff.mp he)
    obtain ⟨f,hf⟩ := TensorMomentFunctional.exists_tupleExponent 1 e hd
    refine ⟨Pi.single (f 0) (p.coeff e),?_⟩
    rw [linPolynomial_single,← hf]
    calc
      _ = C (p.coeff (TensorMomentFunctional.tupleExponent f))*
          ∏ i : Fin 1, (X (f i) : Poly n) := by simp [Fin.prod_univ_one]
      _ = _ := by rw [TensorMomentFunctional.prod_X_tupleExponent,C_mul_monomial,mul_one]
  exact hmem

theorem exists_quadPolynomial {n : ℕ} (p : Poly n) (hp : p.IsHomogeneous 2) :
    ∃ H : Quad n, quadPolynomial H=p := by
  obtain ⟨Q,hQ⟩ := TensorMomentFunctional.exists_quadraticPolynomial p hp
  refine ⟨(fun i j => Q (i,j)),?_⟩
  rw [← hQ]
  simp only [quadPolynomial_apply,TensorMomentFunctional.quadraticPolynomial_apply,
    Fintype.sum_prod_type]

theorem exists_tensorPolynomial {n d : ℕ} (p : Poly n) (hp : p.IsHomogeneous d) :
    ∃ c : (Fin d → Fin n) → ℝ, tensorPolynomial c=p := by
  classical
  have hmem : p ∈ LinearMap.range (tensorPolynomial (n:=n) (d:=d)) := by
    rw [← p.support_sum_monomial_coeff]
    apply Submodule.sum_mem
    intro e he
    have hd : e.sum (fun _ k => k)=d := by
      simpa only [Finsupp.weight_apply,Pi.one_apply,smul_eq_mul,mul_one] using
        hp (mem_support_iff.mp he)
    obtain ⟨f,hf⟩ := TensorMomentFunctional.exists_tupleExponent d e hd
    refine ⟨Pi.single f (p.coeff e),?_⟩
    rw [tensorPolynomial_single,TensorMomentFunctional.prod_X_tupleExponent,hf,
      C_mul_monomial,mul_one]
  exact hmem

def modelPolynomial {n : ℕ} : Coeff n →ₗ[ℝ] Poly (n+1) where
  toFun q := C q.1*SelectorFunctional.s n^4 +
    SelectorFunctional.s n^3*SelectorFunctional.transverse (linPolynomial q.2.1) +
    SelectorFunctional.s n^2*SelectorFunctional.transverse (quadPolynomial q.2.2.1) +
    SelectorFunctional.s n*SelectorFunctional.transverse (tensorPolynomial q.2.2.2.1) +
    SelectorFunctional.transverse (tensorPolynomial q.2.2.2.2)
  map_add' q r := by
    simp only [Prod.fst_add,Prod.snd_add,map_add,add_mul,mul_add]
    ring
  map_smul' t q := by
    simp only [Prod.smul_fst,Prod.smul_snd,map_smul,smul_eq_C_mul,
      smul_eq_mul,map_mul,RingHom.id_apply,SelectorFunctional.transverse,rename_C]
    ring

theorem modelPolynomial_apply {n : ℕ} (q : Coeff n) :
    modelPolynomial q=C q.1*SelectorFunctional.s n^4 +
      SelectorFunctional.s n^3*SelectorFunctional.transverse (linPolynomial q.2.1) +
      SelectorFunctional.s n^2*SelectorFunctional.transverse (quadPolynomial q.2.2.1) +
      SelectorFunctional.s n*SelectorFunctional.transverse (tensorPolynomial q.2.2.2.1) +
      SelectorFunctional.transverse (tensorPolynomial q.2.2.2.2) := rfl

theorem modelPolynomial_homogeneous {n : ℕ} (q : Coeff n) :
    (modelPolynomial q).IsHomogeneous 4 := by
  rw [modelPolynomial_apply]
  have hs : (SelectorFunctional.s n).IsHomogeneous 1 := isHomogeneous_X ℝ 0
  exact (((((hs.pow 4).C_mul q.1).add
    (by simpa only [SelectorFunctional.transverse] using
      (hs.pow 3).mul ((linPolynomial_homogeneous q.2.1).rename_isHomogeneous))).add
    (by simpa only [SelectorFunctional.transverse] using
      (hs.pow 2).mul ((quadPolynomial_homogeneous q.2.2.1).rename_isHomogeneous))).add
    (by simpa only [SelectorFunctional.transverse] using
      hs.mul ((tensorPolynomial_homogeneous q.2.2.2.1).rename_isHomogeneous))).add
    ((tensorPolynomial_homogeneous q.2.2.2.2).rename_isHomogeneous)

theorem modelPolynomial_eval {n : ℕ} (q : Coeff n) (x : Fin (n + 1) → ℝ) :
    eval x (modelPolynomial q)=q.1*x 0^4 + linEval (fun i => x i.succ) q.2.1*x 0^3 +
      quadEval (fun i => x i.succ) q.2.2.1*x 0^2 +
      tensorEval (fun i => x i.succ) q.2.2.2.1*x 0 +
      tensorEval (fun i => x i.succ) q.2.2.2.2 := by
  simp only [modelPolynomial_apply,map_add,map_mul,map_pow,eval_C,SelectorFunctional.s,
    eval_X,SelectorFunctional.transverse,eval_rename,Function.comp_def,
    linPolynomial_eval,quadPolynomial_eval,tensorPolynomial_eval]
  ring

theorem finSuccEquiv_transverse {n : ℕ} (p : Poly n) :
    MvPolynomial.finSuccEquiv ℝ n (SelectorFunctional.transverse p)=Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [SelectorFunctional.transverse,MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,SelectorFunctional.transverse,rename_X,finSuccEquiv_X_succ] at hp ⊢
    rw [hp]

/-- Every actual homogeneous quartic has the scalar/transverse split,
including when the transverse dimension is zero. -/
theorem homogeneous_quartic_split {n : ℕ} (p : Poly (n + 1))
    (hp : p.IsHomogeneous 4) :
    ∃ (a : ℝ) (l H B F : Poly n),
      l.IsHomogeneous 1 ∧ H.IsHomogeneous 2 ∧ B.IsHomogeneous 3 ∧ F.IsHomogeneous 4 ∧
      p=C a*SelectorFunctional.s n^4 +
        SelectorFunctional.s n^3*SelectorFunctional.transverse l +
        SelectorFunctional.s n^2*SelectorFunctional.transverse H +
        SelectorFunctional.s n*SelectorFunctional.transverse B +SelectorFunctional.transverse F := by
  let r := MvPolynomial.finSuccEquiv ℝ n p
  have h4 : (r.coeff 4).IsHomogeneous 0 := hp.finSuccEquiv_coeff_isHomogeneous 4 0 (by omega)
  have h4C : r.coeff 4=C ((r.coeff 4).coeff 0) :=
    totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h4.totalDegree_le)
  refine ⟨(r.coeff 4).coeff 0,r.coeff 3,r.coeff 2,r.coeff 1,r.coeff 0,
    hp.finSuccEquiv_coeff_isHomogeneous 3 1 (by omega),
    hp.finSuccEquiv_coeff_isHomogeneous 2 2 (by omega),
    hp.finSuccEquiv_coeff_isHomogeneous 1 3 (by omega),
    hp.finSuccEquiv_coeff_isHomogeneous 0 4 (by omega),?_⟩
  have hdeg : r.natDegree<5 := by
    dsimp [r]
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact lt_of_le_of_lt ((degreeOf_le_totalDegree p 0).trans hp.totalDegree_le) (by omega)
  have hr := r.as_sum_range' 5 hdeg
  rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,
    Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_zero] at hr
  simp only [zero_add] at hr
  have hC (a : ℝ) : MvPolynomial.finSuccEquiv ℝ n (C a)=Polynomial.C (C a) := by
    simp [MvPolynomial.finSuccEquiv_apply]
  apply (MvPolynomial.finSuccEquiv ℝ n).injective
  simp only [map_add,map_mul,map_pow,finSuccEquiv_transverse,SelectorFunctional.s,
    finSuccEquiv_X_zero,hC]
  change r=_
  conv_lhs => rw [hr]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial]
  conv_lhs => rw [h4C]
  ring

/-- Actual homogeneous quartics have coefficient models, with no
polynomial-representation assumption on the input. -/
theorem exists_modelPolynomial {n : ℕ} (p : Poly (n + 1))
    (hp : p.IsHomogeneous 4) : ∃ q : Coeff n, modelPolynomial q=p := by
  obtain ⟨a,l,H,B,F,hl,hH,hB,hF,hdec⟩ := homogeneous_quartic_split p hp
  obtain ⟨lc,hlc⟩ := exists_linPolynomial l hl
  obtain ⟨Hc,hHc⟩ := exists_quadPolynomial H hH
  obtain ⟨Bc,hBc⟩ := exists_tensorPolynomial B hB
  obtain ⟨Fc,hFc⟩ := exists_tensorPolynomial F hF
  refine ⟨(a,(lc,(Hc,(Bc,Fc)))),?_⟩
  rw [modelPolynomial_apply,hlc,hHc,hBc,hFc]
  exact hdec.symm

theorem functional_modelPolynomial {I : Type*} [Fintype I] {n : ℕ}
    (h : I → Fin n → ℝ) (Z : I → Matrix (Fin 3) (Fin 3) ℝ) (q : Coeff n) :
    SelectorFunctional.functional h Z (modelPolynomial q)=
      ∑ t, SelectorDual.marginalValue (h t) (Z t) q := by
  rw [modelPolynomial_apply]
  simp only [map_add,TensorMomentFunctional.linearMap_C_mul,
    SelectorFunctional.functional_scalar_four,
    SelectorFunctional.functional_s3_linear h Z _ (linPolynomial_homogeneous _),
    SelectorFunctional.functional_s2_quadratic h Z _ (quadPolynomial_homogeneous _),
    SelectorFunctional.functional_s1_cubic h Z _ (tensorPolynomial_homogeneous _),
    SelectorFunctional.functional_transverse_quartic h Z _ (tensorPolynomial_homogeneous _),
    linPolynomial_eval,quadPolynomial_eval,tensorPolynomial_eval,SelectorCentering.diagonalMass]
  rw [Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [SelectorDual.marginalValue]
  ring

/-- Positive coefficient duals are actual finite polynomial functionals
on EVERY coefficient model, with the same points and PSD matrices. -/
theorem exists_polynomial_functional_representation {n : ℕ} (hn : 0 < n)
    (E : Coeff n →L[ℝ] ℝ) (hE : ∀ q ∈ quarticSelectorCone n, 0 ≤ E q) :
    ∃ (I : Type) (_ : Fintype I) (h : I → Fin n → ℝ)
      (Z : I → Matrix (Fin 3) (Fin 3) ℝ),
      (∀ t, radius (h t)=1) ∧ (∀ t, (Z t).PosSemidef) ∧
      SelectorFunctional.CoordinateConsistency h Z ∧
      ∀ q : Coeff n, E q=SelectorFunctional.functional h Z (modelPolynomial q) := by
  obtain ⟨I,hI,h,Z,hh,hZ,hcons,hrep⟩ := SelectorDual.exists_finite_psd_representation hn E hE
  refine ⟨I,hI,h,Z,hh,hZ,hcons,?_⟩
  intro q
  rw [functional_modelPolynomial,hrep]

theorem exists_positive_polynomial_functional {n : ℕ} (hn : 0 < n)
    (E : Coeff n →L[ℝ] ℝ) (hE : ∀ q ∈ quarticSelectorCone n, 0 ≤ E q) :
    ∃ L : Poly (n+1) →ₗ[ℝ] ℝ,
      (∀ p : Poly (n+1), p.totalDegree≤2 → 0≤L (p^2)) ∧
      ∀ q : Coeff n, E q=L (modelPolynomial q) := by
  obtain ⟨I,hI,h,Z,_,hZ,hcons,hrep⟩ := exists_polynomial_functional_representation hn E hE
  exact ⟨SelectorFunctional.functional h Z,
    (fun p hp => SelectorFunctional.functional_square_nonneg h Z hZ hcons p hp),hrep⟩

/-- Positivity forces a coefficient dual to ignore every nonunique
ordered-tensor representation of the zero polynomial. -/
theorem modelPolynomial_kernel_annihilated {n : ℕ} (hn : 0 < n)
    (E : Coeff n →L[ℝ] ℝ) (hE : ∀ q ∈ quarticSelectorCone n, 0 ≤ E q)
    (q : Coeff n) (hq : modelPolynomial q = 0) : E q=0 := by
  obtain ⟨L,_,hrep⟩ := exists_positive_polynomial_functional hn E hE
  rw [hrep,hq,map_zero]

end OptimalConvergenceRates.SphereDimensionBounds.SelectorPolynomial
