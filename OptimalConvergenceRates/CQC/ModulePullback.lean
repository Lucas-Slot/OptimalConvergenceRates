import OptimalConvergenceRates.CQC.SlackGeneratorIdentity
import OptimalConvergenceRates.CQC.ModuleSubstitution
import OptimalConvergenceRates.CQC.MultiplierRemoval

noncomputable section
open MvPolynomial Finset
namespace OptimalConvergenceRates
namespace CQCInternal
open GeneralArchimedean
variable {n m : ℕ}

theorem exists_common_quadraticModule_order
    {k : ℕ} {g : Fin m → MvPolynomial (Fin n) ℝ}
    {q : Fin k → MvPolynomial (Fin n) ℝ}
    (hq : ∀ i, QuadraticModuleMem g (q i)) :
    ∃ s, ∀ i, q i ∈ GenQuadraticModule g s := by
  classical
  let order : Fin k → ℕ := fun i ↦ Classical.choose (hq i)
  have horder : ∀ i, q i ∈ GenQuadraticModule g (order i) :=
    fun i ↦ Classical.choose_spec (hq i)
  refine ⟨∑ i, order i, ?_⟩
  intro i
  exact GenQuadraticModule_mono
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (order j)) (Finset.mem_univ i))
    (horder i)

theorem unitCubePullback_generator_mem
    {R : ℝ} (hR : 0 < R)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hbase : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ j, |x j| < R)
    (hslack : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ i,
      MvPolynomial.eval x (g i) < R ^ 2) :
    ∀ j, QuadraticModuleMem g
      (MvPolynomial.aeval (unitCubePullbackMap R g)
        (BoxSemialgebraicGenerator j)) := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k
    apply quadraticModuleMem_of_posOn g _ hne harch
    intro x hx
    simp only [BoxSemialgebraicGenerator, map_sub, map_one, map_pow,
      aeval_X, unitCubePullbackMap, Fin.addCases_left]
    rw [eval_mul, eval_C, eval_X]
    have hk := hbase x hx k
    have habs : |R⁻¹ * x k| < 1 := by
      calc
        |R⁻¹ * x k| = |x k| / R := by
          rw [abs_mul, abs_inv, abs_of_pos hR]
          ring
        _ < 1 := (div_lt_one hR).2 hk
    exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).2 habs)
  · intro i
    let U : ℝ := R ^ 2
    have hU : 0 < U := by dsimp [U]; positivity
    have hUqPos : ∀ x ∈ KrivineStengle.basicClosedSet g,
        0 < MvPolynomial.eval x (C U - g i) := by
      intro x hx
      simp only [eval_sub, eval_C]
      exact sub_pos.mpr (hslack x hx i)
    obtain ⟨rU, hUq⟩ := exists_order_of_posOn g (C U - g i)
      hne harch hUqPos
    have hsosLeft : IsSOS (C U⁻¹ * (C U - g i) ^ 2) :=
      IsSOS_mul (IsSOS_C_nonneg U⁻¹ (inv_nonneg.mpr hU.le))
        (IsSOS_sq (C U - g i))
    have hsosRight : IsSOS (C U⁻¹ * (g i) ^ 2) :=
      IsSOS_mul (IsSOS_C_nonneg U⁻¹ (inv_nonneg.mpr hU.le))
        (IsSOS_sq (g i))
    have hleft := genQuadraticModule_sos_mul_generator g i _ hsosLeft
    have hright := genQuadraticModule_sos_mul hsosRight hUq
    have hsum := genQuadraticModule_add hleft hright
    have hscale : IsSOS (C (4 / U ^ 2) : MvPolynomial (Fin n) ℝ) :=
      IsSOS_C_nonneg _ (div_nonneg (by norm_num) (sq_nonneg U))
    have hcert := genQuadraticModule_sos_mul hscale hsum
    rw [localized_generator_identity U hU.ne' (g i)] at hcert
    simp only [BoxSemialgebraicGenerator, map_sub, map_one, map_pow,
      aeval_X, unitCubePullbackMap, Fin.addCases_right]
    rw [show 1 - (C (2 / R ^ 2) * g i - 1) ^ 2 =
        C (4 / U ^ 2) * (g i * (C U - g i)) by
      simpa [U] using normalized_slack_generator_identity U hU.ne' (g i)]
    exact ⟨_, hcert⟩

theorem exists_unitCubePullback_generator_order
    {R : ℝ} (hR : 0 < R)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hbase : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ j, |x j| < R)
    (hslack : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ i,
      MvPolynomial.eval x (g i) < R ^ 2) :
    ∃ s, ∀ j,
      MvPolynomial.aeval (unitCubePullbackMap R g)
          (BoxSemialgebraicGenerator j) ∈ GenQuadraticModule g s :=
  exists_common_quadraticModule_order
    (unitCubePullback_generator_mem hR g hne harch hbase hslack)

/-- The degree expansion factor of the cube-to-generator substitution. -/
def generatorDegree (g : Fin m → MvPolynomial (Fin n) ℝ) : ℕ :=
  max 1 (Finset.univ.sup fun i ↦ (g i).totalDegree)

theorem generatorDegree_pos (g : Fin m → MvPolynomial (Fin n) ℝ) :
    0 < generatorDegree g := by
  simp [generatorDegree]

theorem unitCubePullback_degree
    (R : ℝ) (g : Fin m → MvPolynomial (Fin n) ℝ) :
    ∀ j, (unitCubePullbackMap R g j).totalDegree ≤ generatorDegree g := by
  classical
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp only [unitCubePullbackMap, Fin.addCases_left]
    calc
      (C R⁻¹ * X k).totalDegree ≤ (C R⁻¹).totalDegree + (X k).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simp
      _ ≤ generatorDegree g := le_max_left _ _
  · intro i
    simp only [unitCubePullbackMap, Fin.addCases_right]
    calc
      (C (2 / R ^ 2) * g i - 1).totalDegree ≤
          max (C (2 / R ^ 2) * g i).totalDegree
            (1 : MvPolynomial (Fin n) ℝ).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
      _ ≤ generatorDegree g := by
        apply max_le
        · exact (MvPolynomial.totalDegree_mul _ _).trans <| by
            simp only [MvPolynomial.totalDegree_C, zero_add]
            have hi : (g i).totalDegree ≤
                Finset.univ.sup (fun j ↦ (g j).totalDegree) :=
              Finset.le_sup (f := fun j ↦ (g j).totalDegree) (Finset.mem_univ i)
            exact hi.trans (le_max_right 1 _)
        · simp [generatorDegree]

theorem unitCube_certificate_pullback
    {R : ℝ} (hR : 0 < R)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (hne : (KrivineStengle.basicClosedSet g).Nonempty)
    (harch : IsArchimedean g)
    (hbase : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ j, |x j| < R)
    (hslack : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ i,
      MvPolynomial.eval x (g i) < R ^ 2) :
    ∃ s, ∀ {Q : MvPolynomial (Fin (n + m)) ℝ} {r : ℕ},
      Q ∈ BoxQuadraticModule (n + m) r →
      MvPolynomial.aeval (unitCubePullbackMap R g) Q ∈
        GenQuadraticModule g (s + generatorDegree g * r) := by
  obtain ⟨s, hs⟩ := exists_unitCubePullback_generator_order
    hR g hne harch hbase hslack
  exact ⟨s, fun hQ ↦
    aeval_mem_genQuadraticModule_of_box_generators g
      (unitCubePullbackMap R g) (unitCubePullback_degree R g) hs hQ⟩

end CQCInternal
end OptimalConvergenceRates
end


