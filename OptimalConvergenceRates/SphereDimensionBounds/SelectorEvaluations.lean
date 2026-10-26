import OptimalConvergenceRates.SphereDimensionBounds.SelectorCone

/-! Compact normalized evaluations of the actual selector coefficient
space, and explicit coefficient data with value one on every generator.
This module does not assert the complete upper theorem. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.SelectorEvaluations

open Set Topology
open scoped BigOperators Matrix
open SelectorCone

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Parameters (n : ℕ) := Point n × Point 3

/-- The actual polynomial Gram evaluation as a member of the continuous dual. -/
def evaluation {n : ℕ} (p : Parameters n) : Data n →L[ℝ] ℝ where
  toLinearMap := gramEvaluation (fun i => p.1 i) (p.2 0) (p.2 1) (p.2 2)
  cont := (gramEvaluation (fun i => p.1 i) (p.2 0) (p.2 1) (p.2 2)).continuous_of_finiteDimensional

theorem evaluation_apply {n : ℕ} (p : Parameters n) (d : Data n) :
    evaluation p d = gramEvaluation (fun i => p.1 i) (p.2 0) (p.2 1) (p.2 2) d := rfl

theorem evaluation_continuous (n : ℕ) : Continuous (evaluation (n:=n)) := by
  apply continuous_clm_apply.mpr
  intro d
  change Continuous (fun p : Parameters n =>
    d.1.1*(p.2 0)^2 + linEval (fun i => p.1 i) d.1.2.1*(p.2 0)*(p.2 1) +
    2*quadEval (fun i => p.1 i) d.2*(p.2 0)*(p.2 2) +
    (quadEval (fun i => p.1 i) d.1.2.2.1-2*quadEval (fun i => p.1 i) d.2)*(p.2 1)^2 +
    tensorEval (fun i => p.1 i) d.1.2.2.2.1*(p.2 1)*(p.2 2) +
    tensorEval (fun i => p.1 i) d.1.2.2.2.2*(p.2 2)^2)
  dsimp only [linEval,quadEval,tensorEval,LinearMap.coe_mk,AddHom.coe_mk]
  fun_prop

/-- Two genuine Euclidean unit spheres, including the possible empty
transverse sphere in dimension zero. -/
def unitParameters (n : ℕ) : Set (Parameters n) :=
  Metric.sphere (0 : Point n) 1 ×ˢ Metric.sphere (0 : Point 3) 1

theorem unitParameters_isCompact (n : ℕ) : IsCompact (unitParameters n) :=
  (isCompact_sphere (0 : Point n) 1).prod (isCompact_sphere (0 : Point 3) 1)

/-- The concrete normalized generator set in the continuous coefficient dual. -/
def normalizedEvaluations (n : ℕ) : Set (Data n →L[ℝ] ℝ) :=
  evaluation '' unitParameters n

theorem normalizedEvaluations_isCompact (n : ℕ) : IsCompact (normalizedEvaluations n) :=
  (unitParameters_isCompact n).image (evaluation_continuous n)

theorem radius_eq_norm_sq {n : ℕ} (h : Point n) :
    radius (fun i => h i) = ‖h‖^2 := by
  simpa only [radius,Real.norm_eq_abs,sq_abs] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => ℝ) h).symm

theorem radius_eq_one_iff_norm {n : ℕ} (h : Point n) :
    radius (fun i => h i)=1 ↔ ‖h‖=1 := by
  rw [radius_eq_norm_sq]
  constructor
  · intro hsq
    nlinarith [norm_nonneg h]
  · intro hnorm
    rw [hnorm]
    norm_num

private theorem sum_tuple_succ {n k : ℕ} (f : (Fin (k + 1) → Fin n) → ℝ) :
    (∑ a, f a) = ∑ i : Fin n, ∑ a : Fin k → Fin n, f (Fin.cons i a) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Fin n)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

/-- A concrete ordered four-tensor for the squared transverse radius. -/
def radiusQuartic (n : ℕ) : Quartic n :=
  fun f => if f 0=f (0 : Fin 3).succ ∧
    f (0 : Fin 2).succ.succ=f (0 : Fin 1).succ.succ.succ then 1 else 0

theorem quadEval_identity {n : ℕ} (h : Fin n → ℝ) :
    quadEval h (1 : Quad n)=radius h := by
  classical
  simp [quadEval,Matrix.one_apply,radius,pow_two]

theorem tensorEval_radiusQuartic {n : ℕ} (h : Fin n → ℝ) :
    tensorEval h (radiusQuartic n)=radius h^2 := by
  classical
  simp only [tensorEval,LinearMap.coe_mk,AddHom.coe_mk,sum_tuple_succ,
    radiusQuartic,Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,Fin.cons_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Fin.prod_univ_zero,mul_one]
  simp only [ite_mul,zero_mul,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
    Fintype.card_fun,Fintype.card_fin,Nat.pow_zero,one_smul]
  simp only [radius,pow_two,Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Explicit coefficient data for the positive graded matrix
`diag(1,R,R²)`, with zero free entry. -/
def normalizer (n : ℕ) : Data n :=
  ((1,(0,(1,(0,radiusQuartic n)))),0)

theorem gramEvaluation_normalizer {n : ℕ} (h : Fin n → ℝ) (x y z : ℝ) :
    gramEvaluation h x y z (normalizer n)=x^2+radius h*y^2+radius h^2*z^2 := by
  simp [gramEvaluation,normalizer,quadEval_identity,tensorEval_radiusQuartic]

theorem evaluation_normalizer_of_unit {n : ℕ} {p : Parameters n}
    (hp : p ∈ unitParameters n) : evaluation p (normalizer n)=1 := by
  have hh : ‖p.1‖=1 := by simpa only [unitParameters,mem_prod,Metric.mem_sphere,
    dist_zero_right] using hp.1
  have hv : ‖p.2‖=1 := by simpa only [unitParameters,mem_prod,Metric.mem_sphere,
    dist_zero_right] using hp.2
  rw [evaluation_apply,gramEvaluation_normalizer,(radius_eq_one_iff_norm p.1).2 hh]
  have hnorm := radius_eq_norm_sq p.2
  simp only [radius,Fin.sum_univ_succ,Finset.sum_empty,add_zero] at hnorm
  rw [hv] at hnorm
  norm_num at hnorm ⊢
  change p.2 0^2+(p.2 1^2+p.2 2^2)=1 at hnorm
  linarith

/-- Every normalized generator takes value exactly one on the SAME
explicit coefficient data. This supplies a concrete conic-mass normalizer. -/
theorem normalizedEvaluations_normalizer (n : ℕ) :
    ∀ e ∈ normalizedEvaluations n, e (normalizer n)=1 := by
  rintro e ⟨p,hp,rfl⟩
  exact evaluation_normalizer_of_unit hp

theorem normalizedEvaluations_zero_not_mem (n : ℕ) :
    (0 : Data n →L[ℝ] ℝ) ∉ normalizedEvaluations n := by
  intro h
  have hz := normalizedEvaluations_normalizer n 0 h
  simp at hz

theorem gramEvaluation_smul_test {n : ℕ} (d : Data n) (h : Fin n → ℝ)
    (x y z t : ℝ) :
    gramEvaluation h (t*x) (t*y) (t*z) d=t^2*gramEvaluation h x y z d := by
  simp only [gramEvaluation,LinearMap.coe_mk,AddHom.coe_mk]
  ring

/-- Testing the real quadratic form on the Euclidean unit test sphere
already tests every real three-vector. -/
theorem gramEvaluation_nonneg_of_unit_tests {n : ℕ} (d : Data n) (h : Fin n → ℝ)
    (hunit : ∀ v : Point 3, ‖v‖=1 →
      0≤gramEvaluation h (v 0) (v 1) (v 2) d) :
    ∀ x y z : ℝ, 0≤gramEvaluation h x y z d := by
  intro x y z
  let v : Point 3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![x,y,z]
  change 0≤gramEvaluation h (v 0) (v 1) (v 2) d
  by_cases hv : v=0
  · simp [hv,gramEvaluation]
  have hnv : 0<‖v‖ := norm_pos_iff.mpr hv
  have hnorm : ‖(‖v‖⁻¹ : ℝ) • v‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hnv),inv_mul_cancel₀ hnv.ne']
  have hp := hunit ((‖v‖⁻¹ : ℝ) • v) hnorm
  simp only [PiLp.smul_apply,smul_eq_mul] at hp
  rw [gramEvaluation_smul_test] at hp
  exact nonneg_of_mul_nonneg_right hp (sq_pos_of_pos (inv_pos.mpr hnv))

theorem unitParameters_nonempty {n : ℕ} (hn : 0 < n) : (unitParameters n).Nonempty := by
  refine ⟨(EuclideanSpace.single (⟨0,hn⟩ : Fin n) (1:ℝ),
    EuclideanSpace.single (0 : Fin 3) (1:ℝ)),?_⟩
  constructor <;> simp [Metric.mem_sphere,PiLp.norm_single]

theorem normalizedEvaluations_nonempty {n : ℕ} (hn : 0 < n) :
    (normalizedEvaluations n).Nonempty :=
  (unitParameters_nonempty hn).image evaluation

/-- Both normalized spheres give exactly the ORIGINAL evaluation-only
coefficient cone. In particular no symmetry equality was discarded. -/
theorem positivityCone_iff_unit_evaluations {n : ℕ} (hn : 0 < n) (d : Data n) :
    d ∈ positivityCone n ↔ ∀ p ∈ unitParameters n, 0≤evaluation p d := by
  constructor
  · intro hd p _
    exact hd (fun i => p.1 i) (p.2 0) (p.2 1) (p.2 2)
  · intro hd
    apply (positivityCone_iff_unit_radius hn d).2
    intro h hh
    apply gramEvaluation_nonneg_of_unit_tests d h
    intro v hv
    let p : Parameters n := ((WithLp.equiv 2 (Fin n → ℝ)).symm h,v)
    have hp : p ∈ unitParameters n := by
      constructor
      · have hnorm : ‖p.1‖=1 := (radius_eq_one_iff_norm p.1).1 hh
        simpa only [Metric.mem_sphere,dist_zero_right] using hnorm
      · simpa only [Metric.mem_sphere,dist_zero_right] using hv
    exact hd p hp

theorem positivityCone_iff_normalizedEvaluations {n : ℕ} (hn : 0 < n) (d : Data n) :
    d ∈ positivityCone n ↔ ∀ e ∈ normalizedEvaluations n, 0≤e d := by
  rw [positivityCone_iff_unit_evaluations hn d]
  constructor
  · intro hd e he
    rcases he with ⟨p,hp,rfl⟩
    exact hd p hp
  · intro hd p hp
    exact hd (evaluation p) ⟨p,hp,rfl⟩

end OptimalConvergenceRates.SphereDimensionBounds.SelectorEvaluations
