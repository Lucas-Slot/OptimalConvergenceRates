import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.WeightedQuadraticTraceGeometry
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Borel selection from nonempty compact convex matrix completion fibers.
The minimum Euclidean norm representative is unique. Its value is lower
semicontinuous by compact projection, and its graph is Borel. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace WeightedQuadraticSelection

open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace Topology
open Set MeasureTheory

section GeneralSelection

variable {A E : Type*} [TopologicalSpace A] [PolishSpace A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def IsNormMinimum (R : A → E → Prop) (a : A) (x : E) : Prop :=
  R a x ∧ ∀ y, R a y → ‖x‖≤‖y‖

omit [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem exists_normMinimum (R : A → E → Prop) (a : A)
    (hk : IsCompact {x | R a x}) (hne : ∃ x, R a x) :
    ∃x, IsNormMinimum R a x := by
  obtain ⟨x,hx,hmin⟩ := hk.exists_isMinOn hne continuous_norm.continuousOn
  exact ⟨x,hx,fun y hy ↦ hmin hy⟩

omit [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normMinimum_unique (R : A → E → Prop) (a : A)
    (hc : Convex ℝ {x | R a x}) {x y : E}
    (hx : IsNormMinimum R a x) (hy : IsNormMinimum R a y) : x=y := by
  have hn : ‖x‖=‖y‖ := le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)
  have hmid : R a ((1/2:ℝ) • x+(1/2:ℝ) • y) :=
    hc hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
  have hm := hx.2 _ hmid
  have hhalf : (1/2:ℝ) • x+(1/2:ℝ) • y=(1/2:ℝ) • (x+y) := by module
  rw [hhalf,norm_smul] at hm
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hm
  have hp := parallelogram_law_with_norm ℝ x y
  rw [←hn] at hp
  have hs : ‖x+y‖^2≥4*‖x‖^2 := by nlinarith [norm_nonneg (x+y),norm_nonneg x]
  have hz : ‖x-y‖=0 := by nlinarith [sq_nonneg ‖x-y‖,norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

def normMinimumChoice (R : A → E → Prop)
    (hk : ∀ a, IsCompact {x | R a x}) (hne : ∀ a, ∃ x, R a x) (a : A) : E :=
  (exists_normMinimum R a (hk a) (hne a)).choose

omit [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem normMinimumChoice_spec (R : A → E → Prop)
    (hk : ∀ a, IsCompact {x | R a x}) (hne : ∀ a, ∃ x, R a x) (a : A) :
    IsNormMinimum R a (normMinimumChoice R hk hne a) :=
  (exists_normMinimum R a (hk a) (hne a)).choose_spec

omit [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace E] [BorelSpace E] in
/-- Closed graph and compact Euclidean objective sublevels make the
minimum-norm value lower semicontinuous; no continuity of the fibers is assumed. -/
theorem normMinimumChoice_value_lowerSemicontinuous (R : A → E → Prop)
    (hk : ∀ a, IsCompact {x | R a x}) (hne : ∀ a, ∃ x, R a x)
    (hclosed : IsClosed {p : A×E | R p.1 p.2}) :
    LowerSemicontinuous (fun a ↦ ‖normMinimumChoice R hk hne a‖) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro r
  let K := Metric.closedBall (0:E) r
  have hK : IsCompact K := isCompact_closedBall _ _
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F := {p : A×K | R p.1 p.2.1}
  have hF : IsClosed F := hclosed.preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have himage : IsClosed (Prod.fst '' F) := isClosedMap_fst_of_compactSpace F hF
  convert himage using 1
  ext a
  constructor
  · intro ha
    refine ⟨(a,⟨normMinimumChoice R hk hne a,?_⟩),?_,rfl⟩
    · simpa only [K,Metric.mem_closedBall,dist_zero_right,Set.mem_preimage,Set.mem_Iic] using ha
    · exact (normMinimumChoice_spec R hk hne a).1
  · rintro ⟨⟨b,x⟩,hb,hba⟩
    change b=a at hba
    subst b
    have hx : ‖x.1‖≤r := by simpa only [K,Metric.mem_closedBall,dist_zero_right] using x.2
    exact ((normMinimumChoice_spec R hk hne a).2 x.1 hb).trans hx

theorem measurable_of_borel_graph (f : A → E)
    (hgraph : MeasurableSet {p : A×E | p.2=f p.1}) : Measurable f := by
  apply measurable_of_isOpen
  intro V hV
  let T := {p : A×E | p.2=f p.1} ∩ Prod.snd ⁻¹' V
  have hT : MeasurableSet T := hgraph.inter (hV.measurableSet.preimage measurable_snd)
  have hinj : Set.InjOn Prod.fst T := by
    intro p hp q hq heq
    apply Prod.ext heq
    exact hp.1.trans ((congrArg f heq).trans hq.1.symm)
  have hm := hT.image_of_continuousOn_injOn continuous_fst.continuousOn hinj
  convert hm using 1
  ext a
  constructor
  · intro ha
    exact ⟨(a,f a),⟨rfl,ha⟩,rfl⟩
  · rintro ⟨p,⟨hp,hpV⟩,hpa⟩
    change p.1=a at hpa
    change p.2=f p.1 at hp
    change p.2∈V at hpV
    change f a∈V
    rwa [hp,hpa] at hpV

/-- A genuine Borel selector, obtained from the unique Euclidean minimum
of each nonempty compact convex fiber with a closed joint graph. -/
theorem normMinimumChoice_measurable (R : A → E → Prop)
    (hk : ∀ a, IsCompact {x | R a x}) (hne : ∀ a, ∃ x, R a x)
    (hc : ∀ a, Convex ℝ {x | R a x})
    (hclosed : IsClosed {p : A×E | R p.1 p.2}) :
    Measurable (normMinimumChoice R hk hne) := by
  have hv := (normMinimumChoice_value_lowerSemicontinuous R hk hne hclosed).measurable
  have hnorm : Measurable (fun p : A×E ↦ ‖p.2‖) := continuous_snd.norm.measurable
  have hvalue : Measurable (fun p : A×E ↦ ‖normMinimumChoice R hk hne p.1‖) :=
    hv.comp measurable_fst
  have hR : MeasurableSet {p : A×E | R p.1 p.2 ∧ ‖p.2‖=‖normMinimumChoice R hk hne p.1‖} :=
    hclosed.measurableSet.inter (measurableSet_eq_fun hnorm hvalue)
  apply measurable_of_borel_graph
  convert hR using 1
  ext p
  constructor
  · intro hp
    change p.2=normMinimumChoice R hk hne p.1 at hp
    change R p.1 p.2 ∧ _
    rw [hp]
    exact ⟨(normMinimumChoice_spec R hk hne p.1).1,rfl⟩
  · rintro ⟨hp,hpn⟩
    apply normMinimum_unique R p.1 (hc p.1) _ (normMinimumChoice_spec R hk hne p.1)
    exact ⟨hp,fun y hy ↦ hpn.trans_le ((normMinimumChoice_spec R hk hne p.1).2 y hy)⟩

end GeneralSelection

section MatrixSelection

open WeightedQuadraticExistence
  WeightedQuadraticTraceGeometry

variable {ι U : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]

abbrev MatrixSpace := Matrix ι ι ℝ
abbrev FrobeniusSpace := EuclideanSpace ℝ (ι×ι)

local instance matrixMeasurableSpace : MeasurableSpace (MatrixSpace (ι:=ι)) := borel _
local instance matrixBorelSpace : BorelSpace (MatrixSpace (ι:=ι)) := ⟨rfl⟩

def matrixVectorLinearEquiv : FrobeniusSpace (ι:=ι) ≃ₗ[ℝ] MatrixSpace (ι:=ι) where
  toFun v i j := v (i,j)
  invFun C := (WithLp.equiv 2 ((ι×ι)→ℝ)).symm (fun p ↦ C p.1 p.2)
  left_inv v := by ext p; rfl
  right_inv C := by ext i j; rfl
  map_add' v w := by ext i j; rfl
  map_smul' r v := by ext i j; rfl

def matrixVectorEquiv : FrobeniusSpace (ι:=ι) ≃L[ℝ] MatrixSpace (ι:=ι) :=
  matrixVectorLinearEquiv.toContinuousLinearEquiv

def completionRelation (L : MatrixSpace (ι := ι)) (S : U →ₗ[ℝ] MatrixSpace (ι := ι))
    (d : ℝ) (u : U) (v : FrobeniusSpace (ι := ι)) : Prop :=
  ‖matrixVectorEquiv v‖≤(2*d)*‖u‖ ∧ weightedMap L (matrixVectorEquiv v)=S u

omit [MeasurableSpace U] [BorelSpace U] in
theorem completionRelation_closed (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (d : ℝ) :
    IsClosed {p : U×FrobeniusSpace (ι:=ι) | completionRelation L S d p.1 p.2} := by
  have hnorm : Continuous (fun p : U×FrobeniusSpace (ι:=ι) => ‖matrixVectorEquiv p.2‖) :=
    (matrixVectorEquiv.continuous.comp continuous_snd).norm
  have hbound : Continuous (fun p : U×FrobeniusSpace (ι:=ι) => (2*d)*‖p.1‖) :=
    continuous_const.mul continuous_fst.norm
  exact (isClosed_le hnorm hbound).inter (isClosed_eq
    ((weightedMap L).toContinuousLinearMap.continuous.comp
      (matrixVectorEquiv.continuous.comp continuous_snd))
    (S.toContinuousLinearMap.continuous.comp continuous_fst))

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
theorem completionRelation_compact (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (d : ℝ) (u : U) :
    IsCompact {v | completionRelation L S d u v} := by
  let K := Metric.closedBall (0:MatrixSpace (ι:=ι)) ((2*d)*‖u‖) ∩
    {C | weightedMap L C=S u}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_eq (weightedMap L).toContinuousLinearMap.continuous continuous_const)
  have he := matrixVectorEquiv.toHomeomorph.isCompact_preimage.mpr hK
  have hs : {v | completionRelation L S d u v}=matrixVectorEquiv.toHomeomorph ⁻¹' K := by
    ext v
    change (‖matrixVectorEquiv v‖≤(2*d)*‖u‖ ∧ weightedMap L (matrixVectorEquiv v)=S u) ↔
      (dist (matrixVectorEquiv v) 0≤(2*d)*‖u‖ ∧ weightedMap L (matrixVectorEquiv v)=S u)
    rw [dist_zero_right]
  rw [hs]
  exact he

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
theorem completionRelation_convex (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (d : ℝ) (u : U) :
    Convex ℝ {v | completionRelation L S d u v} := by
  have hball := (convex_closedBall (0:MatrixSpace (ι:=ι)) ((2*d)*‖u‖)).linear_preimage
    matrixVectorEquiv.toLinearMap
  have heq : Convex ℝ {v : FrobeniusSpace (ι:=ι) | weightedMap L (matrixVectorEquiv v)=S u} := by
    intro x hx y hy a b ha hb hab
    change weightedMap L (matrixVectorEquiv (a • x+b • y))=S u
    rw [map_add,map_smul,map_smul,map_add,map_smul,map_smul,hx,hy,←add_smul,hab,one_smul]
  convert hball.inter heq using 1
  ext v
  simp only [completionRelation,Set.mem_inter_iff,Set.mem_preimage,Metric.mem_closedBall,
    dist_zero_right,Set.mem_ofPred_eq]
  rfl

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
theorem completionRelation_nonempty (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (hL : L.PosSemidef)
    (hS : ∀ u, (S u).transpose = S u) {d : ℝ} (hd : 0 ≤ d)
    (hdom : ∀ u x, |quadraticValue (S u) x| ≤ (d * ‖u‖) * ‖Matrix.toEuclideanLin L x‖ * ‖x‖)
    (u : U) : ∃v, completionRelation L S d u v := by
  obtain ⟨C,hC,heq⟩ := exists_bounded_weighted_completion L (S u) hL (hS u)
    (mul_nonneg hd (norm_nonneg u)) (hdom u)
  refine ⟨matrixVectorEquiv.symm C,?_,?_⟩
  · simpa only [matrixVectorEquiv.apply_symm_apply, mul_assoc] using hC
  · rw [matrixVectorEquiv.apply_symm_apply,weightedMap_eq]
    · exact heq
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hL.isHermitian.eq

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
theorem completionRelation_neg (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (d : ℝ) (u : U) (v : FrobeniusSpace (ι := ι)) :
    completionRelation L S d (-u) (-v) ↔ completionRelation L S d u v := by
  simp only [completionRelation,map_neg,norm_neg,neg_inj]

def completionVectorChoice (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (hL : L.PosSemidef)
    (hS : ∀ u, (S u).transpose = S u) {d : ℝ} (hd : 0 ≤ d)
    (hdom : ∀ u x, |quadraticValue (S u) x| ≤ (d * ‖u‖) * ‖Matrix.toEuclideanLin L x‖ * ‖x‖) :
    U→FrobeniusSpace (ι:=ι) :=
  normMinimumChoice (completionRelation L S d) (completionRelation_compact L S d)
    (completionRelation_nonempty L S hL hS hd hdom)

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
theorem completionVectorChoice_minimum (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (hL : L.PosSemidef)
    (hS : ∀ u, (S u).transpose = S u) {d : ℝ} (hd : 0 ≤ d)
    (hdom : ∀ u x, |quadraticValue (S u) x| ≤ (d * ‖u‖) * ‖Matrix.toEuclideanLin L x‖ * ‖x‖) (u :
      U) :
    IsNormMinimum (completionRelation L S d) u (completionVectorChoice L S hL hS hd hdom u) :=
  normMinimumChoice_spec _ _ _ u

theorem completionVectorChoice_measurable (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (hL : L.PosSemidef)
    (hS : ∀ u, (S u).transpose = S u) {d : ℝ} (hd : 0 ≤ d)
    (hdom : ∀ u x, |quadraticValue (S u) x| ≤ (d * ‖u‖) * ‖Matrix.toEuclideanLin L x‖ * ‖x‖) :
    Measurable (completionVectorChoice L S hL hS hd hdom) :=
  normMinimumChoice_measurable _ _ _ (completionRelation_convex L S d) (completionRelation_closed
    L S d)

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
theorem completionVectorChoice_odd (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (hL : L.PosSemidef)
    (hS : ∀ u, (S u).transpose = S u) {d : ℝ} (hd : 0 ≤ d)
    (hdom : ∀ u x, |quadraticValue (S u) x| ≤ (d * ‖u‖) * ‖Matrix.toEuclideanLin L x‖ * ‖x‖) (u :
      U) :
    completionVectorChoice L S hL hS hd hdom (-u) =
      -completionVectorChoice L S hL hS hd hdom u := by
  have hm := completionVectorChoice_minimum L S hL hS hd hdom u
  apply normMinimum_unique (completionRelation L S d) (-u) (completionRelation_convex L S d (-u))
    (completionVectorChoice_minimum L S hL hS hd hdom (-u))
  refine ⟨(completionRelation_neg L S d u _).mpr hm.1,?_⟩
  intro v hv
  have hneg : completionRelation L S d u (-v) := by
    simpa only [neg_neg] using (completionRelation_neg L S d (-u) v).mpr hv
  simpa only [norm_neg] using hm.2 (-v) hneg

/-- Exact bounded odd Borel matrix choice for a linear parameter family.
Neither a linear choice nor continuous dependence is asserted. -/
theorem exists_borel_odd_weighted_completion (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (hL : L.PosSemidef)
    (hS : ∀ u, (S u).transpose = S u) {d : ℝ} (hd : 0 ≤ d)
    (hdom : ∀ u x, |quadraticValue (S u) x| ≤ (d * ‖u‖) * ‖Matrix.toEuclideanLin L x‖ * ‖x‖) :
    ∃ C : U→MatrixSpace (ι:=ι), Measurable C ∧
      (∀u, ‖C u‖≤(2*d)*‖u‖) ∧ (∀u, weightedMap L (C u)=S u) ∧
      (∀u, C (-u)= -C u) := by
  let f := completionVectorChoice L S hL hS hd hdom
  refine ⟨fun u ↦ matrixVectorEquiv (f u),
    matrixVectorEquiv.continuous.measurable.comp (completionVectorChoice_measurable L S hL hS hd
      hdom),
    (fun u ↦ (completionVectorChoice_minimum L S hL hS hd hdom u).1.1),
    (fun u ↦ (completionVectorChoice_minimum L S hL hS hd hdom u).1.2),?_⟩
  intro u
  change matrixVectorEquiv (completionVectorChoice L S hL hS hd hdom (-u)) =_
  rw [completionVectorChoice_odd,map_neg]

theorem exists_borel_odd_completion_apply_bound (L : MatrixSpace (ι := ι))
    (S : U →ₗ[ℝ] MatrixSpace (ι := ι)) (hL : L.PosSemidef)
    (hS : ∀ u, (S u).transpose = S u) {d : ℝ} (hd : 0 ≤ d)
    (hdom : ∀ u x, |quadraticValue (S u) x| ≤ (d * ‖u‖) * ‖Matrix.toEuclideanLin L x‖ * ‖x‖) :
    ∃ C : U→MatrixSpace (ι:=ι), Measurable C ∧
      (∀u x, ‖Matrix.toEuclideanLin (C u) x‖≤((2*d)*‖u‖)*‖x‖) ∧
      (∀u, (1/2:ℝ) • (L*C u+(C u).transpose*L)=S u) ∧
      (∀u, C (-u)= -C u) := by
  obtain ⟨C,hCmeas,hCnorm,hCeq,hCodd⟩ := exists_borel_odd_weighted_completion L S hL hS hd hdom
  refine ⟨C,hCmeas,?_,?_,hCodd⟩
  · intro u x
    exact (euclidean_apply_le_operatorNorm (C u) x).trans
      (mul_le_mul_of_nonneg_right (hCnorm u) (norm_nonneg x))
  · intro u
    have hLt : L.transpose=L := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hL.isHermitian.eq
    simpa only [weightedMap_eq L (C u) hLt] using hCeq u

end MatrixSelection

end WeightedQuadraticSelection
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
