/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/SphereBallTransfers/UpperBound.lean

  Box-to-sphere lifting machinery for the Choi-Lam hypersphere upper bound.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.SphereBallTransfers.SphereToBall
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.MainResults
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.WeightedJet.CertificateExtraction

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace SphereBallTransfers

private noncomputable def liftBoxToSphere :
    MvPolynomial (Fin 4) ℝ →ₐ[ℝ] MvPolynomial (Fin 5) ℝ :=
  MvPolynomial.rename xIndexInSphere

private def sphereBoxGeneratorSOS (i : Fin 4) : MvPolynomial (Fin 5) ℝ :=
  match i with
  | ⟨0, _⟩ => (X 1) ^ 2 + (X 2) ^ 2 + (X 3) ^ 2 + (X 4) ^ 2
  | ⟨1, _⟩ => (X 0) ^ 2 + (X 2) ^ 2 + (X 3) ^ 2 + (X 4) ^ 2
  | ⟨2, _⟩ => (X 0) ^ 2 + (X 1) ^ 2 + (X 3) ^ 2 + (X 4) ^ 2
  | _ => (X 0) ^ 2 + (X 1) ^ 2 + (X 2) ^ 2 + (X 4) ^ 2

private theorem liftBoxToSphere_choiLamPerturbed (epsilon : ℝ) :
    liftBoxToSphere (choiLamPerturbed epsilon) =
      choiLamSphereQuartic + MvPolynomial.C epsilon := by
  unfold liftBoxToSphere choiLamPerturbed choiLamSphereQuartic
  simp

private theorem sphereChoiLamPerturbed_eq_lift_add_relation (epsilon : ℝ) :
    sphereChoiLamPerturbed epsilon =
      liftBoxToSphere (choiLamPerturbed epsilon) +
        sphereRelation 5 * (MvPolynomial.C epsilon * (sphereRho + 1)) := by
  rw [liftBoxToSphere_choiLamPerturbed]
  unfold sphereChoiLamPerturbed
  rw [← sphereRhoRelation_eq_sphereRelation]
  unfold sphereRhoRelation
  ring

private theorem liftBoxToSphere_generator_congruent (i : Fin 4) :
    liftBoxToSphere (BoxSemialgebraicGenerator i) =
      sphereBoxGeneratorSOS i - sphereRelation 5 := by
  unfold liftBoxToSphere BoxSemialgebraicGenerator sphereBoxGeneratorSOS
    sphereRelation sphereQuadratic xIndexInSphere
  fin_cases i <;> simp [Fin.sum_univ_five] <;> ring_nf

private theorem sphereBoxGeneratorSOS_isSOS (i : Fin 4) :
    IsSOS (sphereBoxGeneratorSOS i) := by
  fin_cases i
  · change IsSOS ((X 1 : MvPolynomial (Fin 5) ℝ) ^ 2 + X 2 ^ 2 + X 3 ^ 2 + X 4 ^ 2)
    repeat first | apply IsSOS_add | apply IsSOS_sq
  · change IsSOS ((X 0 : MvPolynomial (Fin 5) ℝ) ^ 2 + X 2 ^ 2 + X 3 ^ 2 + X 4 ^ 2)
    repeat first | apply IsSOS_add | apply IsSOS_sq
  · change IsSOS ((X 0 : MvPolynomial (Fin 5) ℝ) ^ 2 + X 1 ^ 2 + X 3 ^ 2 + X 4 ^ 2)
    repeat first | apply IsSOS_add | apply IsSOS_sq
  · change IsSOS ((X 0 : MvPolynomial (Fin 5) ℝ) ^ 2 + X 1 ^ 2 + X 2 ^ 2 + X 4 ^ 2)
    repeat first | apply IsSOS_add | apply IsSOS_sq

private theorem X_sq_totalDegree_le_two (j : Fin 5) :
    ((X j : MvPolynomial (Fin 5) ℝ) ^ 2).totalDegree ≤ 2 := by
  calc
    ((X j : MvPolynomial (Fin 5) ℝ) ^ 2).totalDegree
        ≤ 2 * (X j : MvPolynomial (Fin 5) ℝ).totalDegree :=
          MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 := by simp

private theorem totalDegree_add_le_two {p q : MvPolynomial (Fin 5) ℝ}
    (hp : p.totalDegree ≤ 2) (hq : q.totalDegree ≤ 2) : (p + q).totalDegree ≤ 2 := by
  exact (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)

private theorem sphereBoxGeneratorSOS_totalDegree_le_two (i : Fin 4) :
    (sphereBoxGeneratorSOS i).totalDegree ≤ 2 := by
  fin_cases i
  · change (((X 1 : MvPolynomial (Fin 5) ℝ) ^ 2 + X 2 ^ 2 + X 3 ^ 2 + X 4 ^ 2).totalDegree ≤ 2)
    repeat first
      | exact X_sq_totalDegree_le_two _
      | apply totalDegree_add_le_two
  · change (((X 0 : MvPolynomial (Fin 5) ℝ) ^ 2 + X 2 ^ 2 + X 3 ^ 2 + X 4 ^ 2).totalDegree ≤ 2)
    repeat first
      | exact X_sq_totalDegree_le_two _
      | apply totalDegree_add_le_two
  · change (((X 0 : MvPolynomial (Fin 5) ℝ) ^ 2 + X 1 ^ 2 + X 3 ^ 2 + X 4 ^ 2).totalDegree ≤ 2)
    repeat first
      | exact X_sq_totalDegree_le_two _
      | apply totalDegree_add_le_two
  · change (((X 0 : MvPolynomial (Fin 5) ℝ) ^ 2 + X 1 ^ 2 + X 2 ^ 2 + X 4 ^ 2).totalDegree ≤ 2)
    repeat first
      | exact X_sq_totalDegree_le_two _
      | apply totalDegree_add_le_two

private theorem liftBoxToSphere_totalDegree_le (p : MvPolynomial (Fin 4) ℝ) :
    (liftBoxToSphere p).totalDegree ≤ p.totalDegree := by
  unfold liftBoxToSphere
  exact MvPolynomial.totalDegree_rename_le xIndexInSphere p

private def sphereBoxGeneratorSOSProd (J : Finset (Fin 4)) : MvPolynomial (Fin 5) ℝ :=
  ∏ i ∈ J, sphereBoxGeneratorSOS i

private def SphereRelCongruent (p q : MvPolynomial (Fin 5) ℝ) : Prop :=
  ∃ h : MvPolynomial (Fin 5) ℝ, p = q + sphereRelation 5 * h

private theorem SphereRelCongruent.refl (p : MvPolynomial (Fin 5) ℝ) :
    SphereRelCongruent p p := by
  exact ⟨0, by simp⟩

private theorem SphereRelCongruent.add {p q r s : MvPolynomial (Fin 5) ℝ}
    (hpq : SphereRelCongruent p q) (hrs : SphereRelCongruent r s) :
    SphereRelCongruent (p + r) (q + s) := by
  obtain ⟨a, ha⟩ := hpq
  obtain ⟨b, hb⟩ := hrs
  refine ⟨a + b, ?_⟩
  rw [ha, hb]
  ring

private theorem SphereRelCongruent.mul {p q r s : MvPolynomial (Fin 5) ℝ}
    (hpq : SphereRelCongruent p q) (hrs : SphereRelCongruent r s) :
    SphereRelCongruent (p * r) (q * s) := by
  obtain ⟨a, ha⟩ := hpq
  obtain ⟨b, hb⟩ := hrs
  refine ⟨q * b + a * s + sphereRelation 5 * a * b, ?_⟩
  rw [ha, hb]
  ring

private theorem SphereRelCongruent.finset_sum {ι : Type*} (s : Finset ι)
    (p q : ι → MvPolynomial (Fin 5) ℝ)
    (h : ∀ i ∈ s, SphereRelCongruent (p i) (q i)) :
    SphereRelCongruent (∑ i ∈ s, p i) (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact SphereRelCongruent.refl 0
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact SphereRelCongruent.add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem liftBoxToSphere_generator_congruent_rel (i : Fin 4) :
    SphereRelCongruent (liftBoxToSphere (BoxSemialgebraicGenerator i))
      (sphereBoxGeneratorSOS i) := by
  refine ⟨-1, ?_⟩
  rw [liftBoxToSphere_generator_congruent]
  ring

private theorem liftBoxToSphere_generatorProd_congruent (J : Finset (Fin 4)) :
    SphereRelCongruent (liftBoxToSphere (BoxSemialgebraicGeneratorProd J))
      (sphereBoxGeneratorSOSProd J) := by
  classical
  unfold BoxSemialgebraicGeneratorProd sphereBoxGeneratorSOSProd
  simp only [map_prod]
  induction J using Finset.induction with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      exact SphereRelCongruent.refl 1
  | insert i J hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact SphereRelCongruent.mul (liftBoxToSphere_generator_congruent_rel i) ih

private theorem IsSOS_liftBoxToSphere {p : MvPolynomial (Fin 4) ℝ}
    (hp : IsSOS p) : IsSOS (liftBoxToSphere p) := by
  obtain ⟨N, Q, hQ⟩ := hp
  refine ⟨N, fun i => liftBoxToSphere (Q i), ?_⟩
  rw [hQ]
  simp [liftBoxToSphere, map_sum, map_pow]

private theorem sphereBoxGeneratorSOSProd_isSOS (J : Finset (Fin 4)) :
    IsSOS (sphereBoxGeneratorSOSProd J) := by
  unfold sphereBoxGeneratorSOSProd
  exact IsSOS_finset_prod fun i _ => sphereBoxGeneratorSOS_isSOS i

private theorem sphereBoxGeneratorSOSProd_totalDegree_le_eight (J : Finset (Fin 4)) :
    (sphereBoxGeneratorSOSProd J).totalDegree ≤ 8 := by
  unfold sphereBoxGeneratorSOSProd
  calc
    (∏ i ∈ J, sphereBoxGeneratorSOS i).totalDegree
        ≤ ∑ i ∈ J, (sphereBoxGeneratorSOS i).totalDegree :=
          MvPolynomial.totalDegree_finset_prod J _
    _ ≤ ∑ _i ∈ J, 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact sphereBoxGeneratorSOS_totalDegree_le_two i
    _ = J.card * 2 := by simp
    _ = 2 * J.card := by omega
    _ ≤ 8 := by
          have hcard : J.card ≤ 4 := by
            simpa using Finset.card_le_univ (s := J)
          omega

private theorem boxPreordering_sigma_totalDegree_le_two_mul
    {r : ℕ} {σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ}
    (hsos : ∀ J, IsSOS (σ J))
    (hdeg : ∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r)
    (J : Finset (Fin 4)) : (σ J).totalDegree ≤ 2 * r := by
  obtain ⟨N, Q, hQ, hQdeg⟩ := box_preordering_sos_witness_degree_bound hsos hdeg J
  rw [hQ]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  calc
    ((Q i) ^ 2).totalDegree ≤ 2 * (Q i).totalDegree := MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 * r := Nat.mul_le_mul_left 2 (hQdeg i)

private theorem liftedBoxPreorderingSOSRep_isSOS
    (σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ) (hsos : ∀ J, IsSOS (σ J)) :
    IsSOS
      (∑ J ∈ (Finset.univ : Finset (Fin 4)).powerset,
        liftBoxToSphere (σ J) * sphereBoxGeneratorSOSProd J) := by
  classical
  apply IsSOS_sum_finset
  intro J _
  exact IsSOS_mul (IsSOS_liftBoxToSphere (hsos J)) (sphereBoxGeneratorSOSProd_isSOS J)

private theorem liftedBoxPreorderingSOSRep_totalDegree_le
    {r : ℕ} (σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ)
    (hsos : ∀ J, IsSOS (σ J))
    (hdeg : ∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) :
    (∑ J ∈ (Finset.univ : Finset (Fin 4)).powerset,
        liftBoxToSphere (σ J) * sphereBoxGeneratorSOSProd J).totalDegree ≤ 2 * (r + 4) := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro J _
  calc
    (liftBoxToSphere (σ J) * sphereBoxGeneratorSOSProd J).totalDegree
        ≤ (liftBoxToSphere (σ J)).totalDegree +
            (sphereBoxGeneratorSOSProd J).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ ≤ 2 * r + 8 := by
          have hσ := liftBoxToSphere_totalDegree_le (σ J)
          have hσ2 := boxPreordering_sigma_totalDegree_le_two_mul hsos hdeg J
          have hG := sphereBoxGeneratorSOSProd_totalDegree_le_eight J
          omega
    _ = 2 * (r + 4) := by omega

private theorem liftBoxPreordering_congruent_sosRep
    {p : MvPolynomial (Fin 4) ℝ} {r : ℕ}
    (hmem : p ∈ BoxPreordering 4 r) :
    ∃ σ : Finset (Fin 4) → MvPolynomial (Fin 4) ℝ,
      IsSOS
        (∑ J ∈ (Finset.univ : Finset (Fin 4)).powerset,
          liftBoxToSphere (σ J) * sphereBoxGeneratorSOSProd J) ∧
      (∑ J ∈ (Finset.univ : Finset (Fin 4)).powerset,
          liftBoxToSphere (σ J) * sphereBoxGeneratorSOSProd J).totalDegree ≤ 2 * (r + 4) ∧
      SphereRelCongruent (liftBoxToSphere p)
        (∑ J ∈ (Finset.univ : Finset (Fin 4)).powerset,
          liftBoxToSphere (σ J) * sphereBoxGeneratorSOSProd J) := by
  classical
  obtain ⟨σ, hsos, hdeg, hsum⟩ := hmem
  refine ⟨σ, liftedBoxPreorderingSOSRep_isSOS σ hsos,
    liftedBoxPreorderingSOSRep_totalDegree_le σ hsos hdeg, ?_⟩
  have hsum_cong :
      SphereRelCongruent
        (∑ J ∈ (Finset.univ : Finset (Fin 4)).powerset,
          liftBoxToSphere (σ J * BoxSemialgebraicGeneratorProd J))
        (∑ J ∈ (Finset.univ : Finset (Fin 4)).powerset,
          liftBoxToSphere (σ J) * sphereBoxGeneratorSOSProd J) := by
    apply SphereRelCongruent.finset_sum
    intro J _
    simp only [map_mul]
    exact SphereRelCongruent.mul (SphereRelCongruent.refl _)
      (liftBoxToSphere_generatorProd_congruent J)
  obtain ⟨h, hh⟩ := hsum_cong
  refine ⟨h, ?_⟩
  rw [hsum, map_sum]
  exact hh

private theorem liftBoxPreordering_to_sphereSOSMod
    {p : MvPolynomial (Fin 4) ℝ} {r : ℕ}
    (hmem : p ∈ BoxPreordering 4 r) :
    SphereSOSMod (liftBoxToSphere p) (r + 4) := by
  classical
  obtain ⟨σ, hS_sos, hS_deg, hcong⟩ := liftBoxPreordering_congruent_sosRep hmem
  obtain ⟨N, Q, hQ⟩ := hS_sos
  obtain ⟨h, hh⟩ := hcong
  refine ⟨N, Q, h, ?_, ?_⟩
  · rw [hh, hQ]
  · exact sos_summand_totalDegree_le_of_sum_sq_totalDegree hQ hS_deg

/-- Lift a Choi-Lam box preordering certificate to a hypersphere certificate. -/
theorem sphereChoiLamPerturbed_mem_of_boxPreordering
    {epsilon : ℝ} {r : ℕ}
    (hbox : choiLamPerturbed epsilon ∈ BoxPreordering 4 r) :
    ChoiLamHasSphereCert (r + 4) epsilon := by
  obtain ⟨N, Q, h, hdecomp, hdeg⟩ := liftBoxPreordering_to_sphereSOSMod hbox
  refine ⟨N, Q, h + MvPolynomial.C epsilon * (sphereRho + 1), ?_, hdeg⟩
  rw [sphereChoiLamPerturbed_eq_lift_add_relation, hdecomp]
  ring

end SphereBallTransfers
end OptimalConvergenceRates

end
