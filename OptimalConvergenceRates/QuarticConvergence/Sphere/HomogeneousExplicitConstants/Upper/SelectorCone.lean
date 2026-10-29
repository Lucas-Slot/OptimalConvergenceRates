import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Matrix.Normed
import OptimalConvergenceRates.BasicNotions.ClosedConeImage
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SelectorSchur

/-! The actual finite coefficient cone of quadratic Gram selectors.
The cubic and quartic coefficients use ordered tensor arrays. Their
uniqueness as symmetric tensors is unnecessary for the closed-image
argument. Quadratic selectors themselves have symmetric coefficients. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SelectorCone

open Set Filter Topology
open scoped BigOperators Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Lin (n : ℕ) := Fin n → ℝ
abbrev Quad (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Cubic (n : ℕ) := (Fin 3 → Fin n) → ℝ
abbrev Quartic (n : ℕ) := (Fin 4 → Fin n) → ℝ
abbrev Coeff (n : ℕ) := ℝ × (Lin n × (Quad n × (Cubic n × Quartic n)))
abbrev Data (n : ℕ) := Coeff n × Quad n

def linEval {n : ℕ} (h : Fin n → ℝ) : Lin n →ₗ[ℝ] ℝ where
  toFun l := ∑ i, l i * h i
  map_add' l k := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c l := by simp [mul_assoc, ← Finset.mul_sum]

def quadEval {n : ℕ} (h : Fin n → ℝ) : Quad n →ₗ[ℝ] ℝ where
  toFun u := ∑ i, ∑ j, u i j * h i * h j
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [mul_assoc, ← Finset.mul_sum]

def tensorEval {n d : ℕ} (h : Fin n → ℝ) : ((Fin d → Fin n) → ℝ) →ₗ[ℝ] ℝ where
  toFun c := ∑ f, c f * ∏ i, h (f i)
  map_add' c e := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' t c := by simp [mul_assoc, ← Finset.mul_sum]

theorem linEval_smul {n : ℕ} (h l : Fin n → ℝ) (t : ℝ) :
    linEval (t • h) l = t * linEval h l := by
  simp only [linEval,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadEval_smul {n : ℕ} (h : Fin n → ℝ) (u : Quad n) (t : ℝ) :
    quadEval (t • h) u = t^2 * quadEval h u := by
  simp only [quadEval,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensorEval_smul {n d : ℕ} (h : Fin n → ℝ)
    (c : (Fin d → Fin n) → ℝ) (t : ℝ) :
    tensorEval (t • h) c = t^d * tensorEval h c := by
  simp only [tensorEval,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,smul_eq_mul,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  ring

/-- The actual selector quadratic form at a transverse point and three
scalar test coordinates. -/
def gramEvaluation {n : ℕ} (h : Fin n → ℝ) (x y z : ℝ) : Data n →ₗ[ℝ] ℝ where
  toFun d := d.1.1*x^2 + linEval h d.1.2.1*x*y + 2*quadEval h d.2*x*z +
    (quadEval h d.1.2.2.1-2*quadEval h d.2)*y^2 +
    tensorEval h d.1.2.2.2.1*y*z + tensorEval h d.1.2.2.2.2*z^2
  map_add' d e := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring
  map_smul' t d := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem gramEvaluation_smul_h {n : ℕ} (d : Data n) (h : Fin n → ℝ)
    (x y z t : ℝ) :
    gramEvaluation (t • h) x y z d = gramEvaluation h x (t*y) (t^2*z) d := by
  simp only [gramEvaluation,LinearMap.coe_mk,AddHom.coe_mk,linEval_smul,
    quadEval_smul,tensorEval_smul]
  ring

/-- Pointwise positivity of an actual quadratic selector in finite
coefficient space. Testing all transverse points includes the sphere. -/
def selectorCone (n : ℕ) : Set (Data n) :=
  {d | (∀ i j, d.2 i j = d.2 j i) ∧
    ∀ (h : Fin n → ℝ) (x y z : ℝ), 0 ≤ gramEvaluation h x y z d}

theorem selectorCone_isClosed (n : ℕ) : IsClosed (selectorCone n) := by
  simp only [selectorCone, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_eq (show Continuous (fun d : Data n ↦ d.2 i j) by fun_prop)
        (show Continuous (fun d : Data n ↦ d.2 j i) by fun_prop)
  · exact isClosed_iInter fun h ↦ isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
      isClosed_iInter fun z ↦ isClosed_Ici.preimage
        (gramEvaluation h x y z).continuous_of_finiteDimensional

theorem selectorCone_smul {n : ℕ} {d : Data n} (hd : d ∈ selectorCone n)
    (t : ℝ) (ht : 0 < t) : t • d ∈ selectorCone n := by
  constructor
  · intro i j
    simpa only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul] using! congrArg (t * ·) (hd.1 i j)
  · intro h x y z
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg ht.le (hd.2 h x y z)

/-- A symmetric quadratic matrix is determined by its actual diagonal
polynomial, including in dimension zero. -/
theorem quad_eq_zero_of_evaluation_zero {n : ℕ} (u : Quad n)
    (hsym : ∀ i j, u i j = u j i) (hu : ∀ h, quadEval h u = 0) : u = 0 := by
  classical
  have hdiag (i : Fin n) : u i i = 0 := by
    have hi := hu (Pi.single i 1)
    simpa [quadEval, Pi.single_apply] using hi
  ext i j
  by_cases hij : i = j
  · simpa [hij] using hdiag j
  · have hsum := hu (Pi.single i 1 + Pi.single j 1)
    simp [quadEval, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib,
      Pi.single_apply, hij, Ne.symm hij, hdiag, hsym j i] at hsum
    simpa only [Matrix.zero_apply] using hsum

/-- Forgetting the free quadratic entry has trivial kernel on the
pointwise positive selector cone. -/
theorem selectorCone_trivial_kernel {n : ℕ} {d : Data n}
    (hd : d ∈ selectorCone n) (hzero : d.1 = 0) : d = 0 := by
  have hu : d.2 = 0 := by
    apply quad_eq_zero_of_evaluation_zero d.2 hd.1
    intro h
    have hp := hd.2 h 1 0 1
    have hm := hd.2 h 1 0 (-1)
    simp only [gramEvaluation, LinearMap.coe_mk, AddHom.coe_mk, hzero,
      Prod.fst_zero, Prod.snd_zero, map_zero] at hp hm
    nlinarith
  exact Prod.ext hzero hu

/-- The cone of quartic coefficient data admitting an actual homogeneous
quadratic Gram selector is closed. This is the finite-dimensional
closedness step used before separation in the all-pole proof. -/
theorem quartic_selector_image_isClosed (n : ℕ) :
    IsClosed (Prod.fst '' selectorCone n) := by
  let L : Data n →L[ℝ] Coeff n := ContinuousLinearMap.fst ℝ (Coeff n) (Quad n)
  exact ClosedConeImage.isClosed_image_of_conic_trivial_kernel
    (selectorCone n) (selectorCone_isClosed n)
    (fun _ hd t ht ↦ selectorCone_smul hd t ht) L
    (fun _ hd hz ↦ selectorCone_trivial_kernel hd hz)

/-- The same positivity cone before choosing the symmetric coefficient
representative of the free quadratic entry. -/
def positivityCone (n : ℕ) : Set (Data n) :=
  {d | ∀ (h : Fin n → ℝ) (x y z : ℝ), 0 ≤ gramEvaluation h x y z d}

def radius {n : ℕ} (h : Fin n → ℝ) : ℝ := ∑ i, h i^2

theorem radius_nonneg {n : ℕ} (h : Fin n → ℝ) : 0 ≤ radius h :=
  Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

theorem radius_smul {n : ℕ} (h : Fin n → ℝ) (t : ℝ) :
    radius (t • h) = t^2 * radius h := by
  simp [radius,Pi.smul_apply,mul_pow,Finset.mul_sum]

theorem radius_eq_zero_iff {n : ℕ} (h : Fin n → ℝ) : radius h = 0 ↔ h = 0 := by
  constructor
  · intro hr
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (i : Fin n) _ ↦ sq_nonneg (h i))).mp hr
    funext i
    simpa only [Pi.zero_apply,pow_eq_zero_iff (by decide : (2:ℕ)≠0)] using hs i (Finset.mem_univ i)
  · rintro rfl
    simp [radius]

theorem gramEvaluation_zero_h {n : ℕ} (d : Data n) (x y z : ℝ) :
    gramEvaluation (0 : Fin n → ℝ) x y z d = d.1.1*x^2 := by
  simp [gramEvaluation,linEval,quadEval,tensorEval,Fin.prod_univ_succ]

/-- Homogeneity allows the evaluation-only cone to be tested on the
compact transverse unit sphere. The dimension assumption is used only
to extract the nonnegative leading coefficient from a unit test point. -/
theorem positivityCone_iff_unit_radius {n : ℕ} (hn : 0 < n) (d : Data n) :
    d ∈ positivityCone n ↔ ∀ h : Fin n → ℝ, radius h = 1 →
      ∀ x y z : ℝ, 0 ≤ gramEvaluation h x y z d := by
  constructor
  · intro hd h _ x y z
    exact hd h x y z
  · intro hd h x y z
    have ha : 0 ≤ d.1.1 := by
      have hp := hd (Pi.single (⟨0,hn⟩ : Fin n) 1)
        (by simp [radius,Pi.single_apply]) 1 0 0
      simpa [gramEvaluation] using hp
    by_cases hh : h = 0
    · rw [hh,gramEvaluation_zero_h]
      exact mul_nonneg ha (sq_nonneg x)
    have hR : 0 < radius h :=
      lt_of_le_of_ne (radius_nonneg h) (fun hz ↦ hh ((radius_eq_zero_iff h).mp hz.symm))
    let r := Real.sqrt (radius h)
    have hr : 0 < r := Real.sqrt_pos.mpr hR
    have hr2 : r^2 = radius h := Real.sq_sqrt hR.le
    have hunit : radius (r⁻¹ • h) = 1 := by
      rw [radius_smul,← hr2]
      field_simp
    have hp := hd (r⁻¹ • h) hunit x (r*y) (r^2*z)
    have heq : r • (r⁻¹ • h) = h := by simp [smul_smul,hr.ne']
    rw [← gramEvaluation_smul_h,heq] at hp
    exact hp

def symmetrizeQuad {n : ℕ} (u : Quad n) : Quad n := fun i j ↦ (u i j + u j i)/2

theorem symmetrizeQuad_symmetric {n : ℕ} (u : Quad n) :
    ∀ i j, symmetrizeQuad u i j = symmetrizeQuad u j i := by
  intro i j
  simp only [symmetrizeQuad, add_comm]

theorem quadEval_symmetrizeQuad {n : ℕ} (h : Fin n → ℝ) (u : Quad n) :
    quadEval h (symmetrizeQuad u) = quadEval h u := by
  have hs : (∑ i, ∑ j, u j i * h i * h j) = ∑ i, ∑ j, u i j * h i * h j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (∑ i, ∑ j, ((u i j + u j i)/2) * h i * h j) = _
  simp only [add_div, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div,
    ← Finset.sum_div]
  change (∑ i, ∑ j, u i j * h i * h j)/2 +
    (∑ i, ∑ j, u j i * h i * h j)/2 = _
  rw [hs]
  dsimp [quadEval]
  ring

theorem gramEvaluation_symmetrizeQuad {n : ℕ} (d : Data n)
    (h : Fin n → ℝ) (x y z : ℝ) :
    gramEvaluation h x y z (d.1,symmetrizeQuad d.2) = gramEvaluation h x y z d := by
  simp only [gramEvaluation, LinearMap.coe_mk, AddHom.coe_mk, quadEval_symmetrizeQuad]

/-- Symmetrizing the free entry changes no actual evaluation. This
identity is also needed when passing to the evaluation-only dual cone;
the extra symmetry equalities must not be silently dropped in duality. -/
theorem selector_image_eq_positivity_image (n : ℕ) :
    Prod.fst '' selectorCone n = Prod.fst '' positivityCone n := by
  apply Set.Subset.antisymm
  · rintro _ ⟨d,hd,rfl⟩
    exact ⟨d,hd.2,rfl⟩
  · rintro _ ⟨d,hd,rfl⟩
    refine ⟨(d.1,symmetrizeQuad d.2),⟨symmetrizeQuad_symmetric _,?_⟩,rfl⟩
    intro h x y z
    rw [gramEvaluation_symmetrizeQuad]
    exact hd h x y z

theorem quartic_positivity_image_isClosed (n : ℕ) :
    IsClosed (Prod.fst '' positivityCone n) := by
  rw [← selector_image_eq_positivity_image]
  exact quartic_selector_image_isClosed n

/-- The coefficient inequality is precisely positivity of the actual
three-by-three polynomial matrix. -/
theorem positivityCone_iff_matrix {n : ℕ} (d : Data n) :
    d ∈ positivityCone n ↔ ∀ h : Fin n → ℝ,
      (SelectorSchur.selectorMatrix d.1.1 (linEval h d.1.2.1)
        (quadEval h d.1.2.2.1) (tensorEval h d.1.2.2.2.1)
        (quadEval h d.2) (tensorEval h d.1.2.2.2.2)).PosSemidef := by
  constructor
  · intro hd h
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_,?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro v
      have hv := hd h (v 0) (v 1) (v 2)
      simp only [SelectorSchur.selectorMatrix, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, star_trivial, Finset.sum_empty, add_zero]
      convert hv using 1
      dsimp [gramEvaluation]
      ring
  · intro hd h x y z
    exact SelectorSchur.selectorMatrix_quadratic_nonneg (hd h) x y z

theorem positivityCone_zero_mem (n : ℕ) : (0 : Data n) ∈ positivityCone n := by
  intro h x y z
  simp only [map_zero, le_refl]

theorem positivityCone_add {n : ℕ} {d e : Data n}
    (hd : d ∈ positivityCone n) (he : e ∈ positivityCone n) :
    d + e ∈ positivityCone n := by
  intro h x y z
  rw [map_add]
  exact add_nonneg (hd h x y z) (he h x y z)

theorem positivityCone_nonneg_smul {n : ℕ} {d : Data n}
    (hd : d ∈ positivityCone n) (t : ℝ) (ht : 0 ≤ t) :
    t • d ∈ positivityCone n := by
  intro h x y z
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg ht (hd h x y z)

/-- The closed convex cone containing zero used in the separation argument.
Its points are actual quartic coefficient arrays admitting a quadratic
selector, with no assumed Slater condition. -/
def quarticSelectorCone (n : ℕ) : ProperCone ℝ (Coeff n) where
  carrier := Prod.fst '' positivityCone n
  zero_mem' := ⟨0,positivityCone_zero_mem n,rfl⟩
  add_mem' := by
    rintro _ _ ⟨d,hd,rfl⟩ ⟨e,he,rfl⟩
    exact ⟨d+e,positivityCone_add hd he,rfl⟩
  smul_mem' := by
    rintro ⟨t,ht⟩ _ ⟨d,hd,rfl⟩
    exact ⟨t • d,positivityCone_nonneg_smul hd t ht,rfl⟩
  isClosed' := quartic_positivity_image_isClosed n

end SelectorCone
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
