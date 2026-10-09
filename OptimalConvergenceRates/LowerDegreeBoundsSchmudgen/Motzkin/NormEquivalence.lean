/- Uniform coefficient/sup-norm equivalence for ternary homogeneous sextics. -/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.Motzkin.JetBounds
import OptimalConvergenceRates.BasicNotions.SoSConeClosed
import Mathlib.Topology.ContinuousMap.Compact

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

namespace Motzkin

/-- Exponents of ternary monomials of total degree exactly six. -/
def HomExp6 := {α : ExpLE 3 6 // expDegree α.1 = 6}

noncomputable instance : Fintype HomExp6 := by
  classical
  unfold HomExp6
  infer_instance

/-- Reconstruct a homogeneous sextic from its finite coefficient vector. -/
noncomputable def homPoly6 (c : HomExp6 → ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ α : HomExp6, MvPolynomial.monomial α.1.1 (c α)

@[simp] theorem coeff_homPoly6 (c : HomExp6 → ℝ) (α : HomExp6) :
    MvPolynomial.coeff α.1.1 (homPoly6 c) = c α := by
  unfold homPoly6
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single α]
  · simp
  · intro β _ hβα
    have hval : β.1.1 ≠ α.1.1 := by
      intro h
      apply hβα
      apply Subtype.ext
      apply Subtype.ext
      exact h
    simp [MvPolynomial.coeff_monomial, hval]
  · simp

lemma homPoly6_isHomogeneous (c : HomExp6 → ℝ) : (homPoly6 c).IsHomogeneous 6 := by
  unfold homPoly6
  apply MvPolynomial.IsHomogeneous.sum
  intro α _
  apply MvPolynomial.isHomogeneous_monomial
  simpa [expDegree, Finsupp.degree_eq_sum, Finsupp.sum_fintype] using α.2

/-- The compact three-dimensional unit cube as a type. -/
abbrev MotzkinCube := {x : Fin 3 → ℝ // x ∈ Hypercube 3}

noncomputable instance : CompactSpace MotzkinCube :=
  isCompact_iff_compactSpace.mp Hypercube_compact

noncomputable def homEval6 (c : HomExp6 → ℝ) : C(MotzkinCube, ℝ) :=
  ⟨fun x => MvPolynomial.eval x.1 (homPoly6 c),
    (MvPolynomial.continuous_eval (homPoly6 c)).comp continuous_subtype_val⟩

noncomputable def homEvalLinear6 : (HomExp6 → ℝ) →ₗ[ℝ] C(MotzkinCube, ℝ) where
  toFun := homEval6
  map_add' c d := by
    ext x
    simp [homEval6, homPoly6, MvPolynomial.eval_add, Finset.sum_add_distrib]
  map_smul' a c := by
    ext x
    simp [homEval6, homPoly6, MvPolynomial.eval_monomial, Finset.mul_sum]
    ring_nf

lemma motzkinSqNorm_one_mem_cube {v : Fin 3 → ℝ} (hv : motzkinSqNorm v = 1) :
    v ∈ Hypercube 3 := by
  rw [Hypercube_mem_iff]
  intro i
  have hi : v i ^ 2 ≤ motzkinSqNorm v := by
    unfold motzkinSqNorm
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  rw [hv] at hi
  constructor <;> nlinarith [sq_abs (v i), abs_nonneg (v i)]

lemma homEvalLinear6_injective : Function.Injective homEvalLinear6 := by
  intro c d hcd
  have hzeroMap : homEvalLinear6 (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  have hunit : ∀ v : Fin 3 → ℝ, motzkinSqNorm v = 1 →
      MvPolynomial.eval v (homPoly6 (c - d)) = 0 := by
    intro v hv
    have happ := congrArg (fun f : C(MotzkinCube, ℝ) => f ⟨v, motzkinSqNorm_one_mem_cube hv⟩)
      hzeroMap
    simpa [homEvalLinear6, homEval6] using happ
  have hpzero : homPoly6 (c - d) = 0 := by
    apply MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero
    · exact homPoly6_isHomogeneous (c - d)
    · exact eval_eq_zero_of_unit_eq_zero (homPoly6_isHomogeneous (c - d)) hunit
  apply sub_eq_zero.mp
  funext α
  have hc := congrArg (MvPolynomial.coeff α.1.1) hpzero
  simpa using hc

/-- A uniform constant converting the cube sup norm of a homogeneous ternary
sextic to its coefficient `L1` norm. -/
noncomputable def motzkinDegreeSixNormConst : ℝ :=
  let K := Classical.choose
    ((LinearMap.injective_iff_antilipschitz homEvalLinear6).mp homEvalLinear6_injective)
  (Fintype.card HomExp6 : ℝ) * K

theorem motzkinDegreeSixNormConst_pos : 0 < motzkinDegreeSixNormConst := by
  let hex := (LinearMap.injective_iff_antilipschitz homEvalLinear6).mp
    homEvalLinear6_injective
  let K := Classical.choose hex
  have hK : 0 < K := (Classical.choose_spec hex).1
  have hcard : 0 < (Fintype.card HomExp6 : ℝ) := by
    have hnon : Nonempty HomExp6 := by
      refine ⟨⟨⟨Finsupp.single (0 : Fin 3) 6, ?_⟩, ?_⟩⟩
      · simp [expDegree]
      · simp [expDegree]
    exact_mod_cast Fintype.card_pos
  simpa [motzkinDegreeSixNormConst, K, hex] using mul_pos hcard hK


lemma homPoly6_coefficients (p : MvPolynomial (Fin 3) ℝ)
    (hp : homogeneousPart3 6 p = p) :
    homPoly6 (fun α => MvPolynomial.coeff α.1.1 p) = p := by
  ext β
  by_cases hβ : expDegree β = 6
  · let α : HomExp6 := ⟨⟨β, hβ.le⟩, hβ⟩
    simpa [α] using coeff_homPoly6 (fun γ => MvPolynomial.coeff γ.1.1 p) α
  · have hpzero : MvPolynomial.coeff β p = 0 :=
      (isHomogeneous_of_homogeneousPart3_eq hp).coeff_eq_zero (by
        simpa [expDegree, Finsupp.degree_eq_sum, Finsupp.sum_fintype] using hβ)
    have hqzero : MvPolynomial.coeff β
        (homPoly6 (fun α => MvPolynomial.coeff α.1.1 p)) = 0 :=
      (homPoly6_isHomogeneous _).coeff_eq_zero (by
        simpa [expDegree, Finsupp.degree_eq_sum, Finsupp.sum_fintype] using hβ)
    rw [hpzero, hqzero]

theorem motzkinCoeffNorm_homPoly6_le (c : HomExp6 → ℝ) :
    motzkinCoeffNorm (homPoly6 c) ≤ (Fintype.card HomExp6 : ℝ) * ‖c‖ := by
  calc
    motzkinCoeffNorm (homPoly6 c) ≤ ∑ α : HomExp6,
        motzkinCoeffNorm (MvPolynomial.monomial α.1.1 (c α)) := by
          exact motzkinCoeffNorm_sum_le Finset.univ _
    _ ≤ ∑ α : HomExp6, |c α| := by
      exact Finset.sum_le_sum fun α _ => motzkinCoeffNorm_monomial_le α.1.1 (c α)
    _ = ∑ α : HomExp6, ‖c α‖ := by simp [Real.norm_eq_abs]
    _ ≤ (Fintype.card HomExp6 : ℝ) * ‖c‖ := by
      simpa [nsmul_eq_mul] using Pi.sum_norm_apply_le_norm c

/-- A homogeneous ternary sextic whose absolute value is at most `B` on the
cube has coefficient `L1` norm at most a fixed multiple of `B`. -/
theorem motzkinCoeffNorm_homogeneous_six_le_cube_bound
    (p : MvPolynomial (Fin 3) ℝ) (hp : homogeneousPart3 6 p = p)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : Fin 3 → ℝ, x ∈ Hypercube 3 → |MvPolynomial.eval x p| ≤ B) :
    motzkinCoeffNorm p ≤ motzkinDegreeSixNormConst * B := by
  let c : HomExp6 → ℝ := fun α => MvPolynomial.coeff α.1.1 p
  let hex := (LinearMap.injective_iff_antilipschitz homEvalLinear6).mp
    homEvalLinear6_injective
  let K := Classical.choose hex
  have hanti : AntilipschitzWith K homEvalLinear6 := (Classical.choose_spec hex).2
  have heval : ‖homEvalLinear6 c‖ ≤ B := by
    rw [ContinuousMap.norm_le _ hB]
    intro x
    simpa [homEvalLinear6, homEval6, c, homPoly6_coefficients p hp] using hbound x.1 x.2
  have hc : ‖c‖ ≤ K * B := by
    calc
      ‖c‖ = dist c 0 := by simp
      _ ≤ K * dist (homEvalLinear6 c) (homEvalLinear6 0) := hanti.le_mul_dist c 0
      _ = K * ‖homEvalLinear6 c‖ := by simp
      _ ≤ K * B := mul_le_mul_of_nonneg_left heval K.coe_nonneg
  rw [← homPoly6_coefficients p hp]
  calc
    motzkinCoeffNorm (homPoly6 c) ≤ (Fintype.card HomExp6 : ℝ) * ‖c‖ :=
      motzkinCoeffNorm_homPoly6_le c
    _ ≤ (Fintype.card HomExp6 : ℝ) * (K * B) :=
      mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)
    _ = motzkinDegreeSixNormConst * B := by
      simp [motzkinDegreeSixNormConst, K, mul_assoc]

end Motzkin

end OptimalConvergenceRates

end
