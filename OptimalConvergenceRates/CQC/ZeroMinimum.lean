import OptimalConvergenceRates.CQC.AffineBox

/-! # Feasible points and zeros of the fixed cube lift -/

noncomputable section
open MvPolynomial Set
namespace OptimalConvergenceRates.CQCInternal

variable {n m : ℕ}

/-- The unit-cube point corresponding to the base point `x` and the slack
values `g i` in the affine box used by the CQC lift. -/
def feasibleToUnitPoint (R : ℝ)
    (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    Fin (n + m) → ℝ :=
  combinePoint (fun j ↦ x j / R)
    (fun i ↦ 2 * MvPolynomial.eval x (g i) / R ^ 2 - 1)

theorem feasibleToUnitPoint_mem_hypercube
    {R : ℝ} (hR : 0 < R)
    {g : Fin m → MvPolynomial (Fin n) ℝ} {x : Fin n → ℝ}
    (hx : x ∈ KrivineStengle.basicClosedSet g)
    (hbase : ∀ j, |x j| < R)
    (hslack : ∀ i, MvPolynomial.eval x (g i) < R ^ 2) :
    feasibleToUnitPoint R g x ∈ Hypercube (n + m) := by
  rw [Hypercube_mem_iff]
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro j
    simp only [feasibleToUnitPoint, combinePoint, Fin.addCases_left, mem_Icc]
    rw [← abs_le, abs_div, abs_of_pos hR]
    exact (div_le_one hR).2 (hbase j).le
  · intro i
    simp only [feasibleToUnitPoint, combinePoint, Fin.addCases_right, mem_Icc]
    have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
    have hi := hx i
    have hqnonneg : 0 ≤ 2 * MvPolynomial.eval x (g i) / R ^ 2 :=
      div_nonneg (mul_nonneg (by norm_num) hi) hR2.le
    have hqle : 2 * MvPolynomial.eval x (g i) / R ^ 2 ≤ 2 := by
      apply (div_le_iff₀ hR2).2
      nlinarith [hslack i]
    constructor <;> linarith

theorem unitToSlackValuePoint_feasibleToUnitPoint
    {R : ℝ} (hR : R ≠ 0)
    (g : Fin m → MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    unitToSlackValuePoint R (feasibleToUnitPoint R g x) =
      combinePoint x (fun i ↦ MvPolynomial.eval x (g i)) := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro j
    simp only [unitToSlackValuePoint, feasibleToUnitPoint, combinePoint,
      Fin.addCases_left]
    field_simp
  · intro i
    simp only [unitToSlackValuePoint, feasibleToUnitPoint, combinePoint,
      Fin.addCases_right]
    have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
    field_simp
    ring

theorem eval_unitBoxLiftPolynomial_feasibleToUnitPoint
    {R : ℝ} (hR : R ≠ 0)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin (n + m)) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (feasibleToUnitPoint R g x)
        (unitBoxLiftPolynomial R P) =
      MvPolynomial.eval x (generatorSlackSubstitution g P) := by
  rw [eval_unitBoxLiftPolynomial,
    unitToSlackValuePoint_feasibleToUnitPoint hR]
  unfold generatorSlackSubstitution
  change MvPolynomial.eval₂Hom (RingHom.id ℝ)
      (combinePoint x fun i ↦ MvPolynomial.eval x (g i)) P =
    MvPolynomial.eval₂Hom (RingHom.id ℝ) x
      (MvPolynomial.bind₁ (Fin.addCases X g) P)
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext k
  refine Fin.addCases ?_ ?_ k <;> simp [combinePoint]

/-- A zero of the original nonnegative polynomial produces a zero of the
fixed unit-cube lift. -/
theorem exists_cube_zero_of_exists_feasible_zero
    {R M : ℝ} (hR : 0 < R)
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ}
    (hbase : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ j, |x j| < R)
    (hslack : ∀ x ∈ KrivineStengle.basicClosedSet g, ∀ i,
      MvPolynomial.eval x (g i) < R ^ 2)
    (hzero : ∃ x ∈ KrivineStengle.basicClosedSet g,
      MvPolynomial.eval x p = 0) :
    ∃ z ∈ Hypercube (n + m),
      MvPolynomial.eval z
        (unitBoxLiftPolynomial R (descendedSlackObjective g p M)) = 0 := by
  obtain ⟨x, hx, hpx⟩ := hzero
  refine ⟨feasibleToUnitPoint R g x,
    feasibleToUnitPoint_mem_hypercube hR hx (hbase x hx) (hslack x hx), ?_⟩
  rw [eval_unitBoxLiftPolynomial_feasibleToUnitPoint hR.ne',
    generatorSlackSubstitution_descendedSlackObjective, map_mul, map_pow, hpx]
  ring

end OptimalConvergenceRates.CQCInternal
end
