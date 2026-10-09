import OptimalConvergenceRates.CQC.BoxLift

/-! # Affine transport of the descended slack-value box to the unit cube -/

noncomputable section
open MvPolynomial Set
namespace OptimalConvergenceRates
namespace CQCInternal
variable {n m : ℕ}

def unitToSlackValueMap (R : ℝ) :
    Fin (n + m) → MvPolynomial (Fin (n + m)) ℝ :=
  Fin.addCases
    (fun j ↦ C R * X (Fin.castAdd m j))
    (fun i ↦ C (R ^ 2 / 2) * (X (Fin.natAdd n i) + 1))

def unitToSlackValuePoint (R : ℝ) (z : Fin (n + m) → ℝ) :
    Fin (n + m) → ℝ :=
  combinePoint (fun j ↦ R * z (Fin.castAdd m j))
    (fun i ↦ R ^ 2 / 2 * (z (Fin.natAdd n i) + 1))

def unitBoxLiftPolynomial (R : ℝ)
    (P : MvPolynomial (Fin (n + m)) ℝ) :
    MvPolynomial (Fin (n + m)) ℝ :=
  MvPolynomial.aeval (unitToSlackValueMap R) P

def unitCubePullbackMap (R : ℝ)
    (g : Fin m → MvPolynomial (Fin n) ℝ) :
    Fin (n + m) → MvPolynomial (Fin n) ℝ :=
  Fin.addCases
    (fun j ↦ C R⁻¹ * X j)
    (fun i ↦ C (2 / R ^ 2) * g i - 1)

@[simp]
theorem eval_unitBoxLiftPolynomial
    (R : ℝ) (z : Fin (n + m) → ℝ)
    (P : MvPolynomial (Fin (n + m)) ℝ) :
    MvPolynomial.eval z (unitBoxLiftPolynomial R P) =
      MvPolynomial.eval (unitToSlackValuePoint R z) P := by
  unfold unitBoxLiftPolynomial
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) z
      (MvPolynomial.bind₁ _ P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  have hcoords :
      (fun i ↦ MvPolynomial.eval₂Hom (RingHom.id ℝ) z
        (unitToSlackValueMap R i)) = unitToSlackValuePoint R z := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp only [unitToSlackValueMap, Fin.addCases_left, map_mul,
        MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
      change R * z (Fin.castAdd m k) =
        basePoint (unitToSlackValuePoint R z) k
      simp [unitToSlackValuePoint]
    · intro i
      simp only [unitToSlackValueMap, Fin.addCases_right, map_mul, map_add,
        map_one, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
      change R ^ 2 / 2 * (z (Fin.natAdd n i) + 1) =
        slackPoint (unitToSlackValuePoint R z) i
      simp [unitToSlackValuePoint]
  rw [hcoords]
  rfl

theorem unitToSlackValuePoint_mem_slackValueBox
    {R : ℝ} (hR : 0 ≤ R) {z : Fin (n + m) → ℝ}
    (hz : z ∈ Hypercube (n + m)) :
    unitToSlackValuePoint R z ∈ slackValueBox R := by
  constructor
  · intro j
    rw [show basePoint (unitToSlackValuePoint R z) j =
      R * z (Fin.castAdd m j) by simp [unitToSlackValuePoint]]
    rw [abs_mul, abs_of_nonneg hR]
    have hj := (Hypercube_mem_iff z).mp hz (Fin.castAdd m j)
    have habs : |z (Fin.castAdd m j)| ≤ 1 := abs_le.mpr hj
    nlinarith
  · intro i
    rw [show slackPoint (unitToSlackValuePoint R z) i =
      R ^ 2 / 2 * (z (Fin.natAdd n i) + 1) by
      simp [unitToSlackValuePoint]]
    have hi := (Hypercube_mem_iff z).mp hz (Fin.natAdd n i)
    have hfactor : 0 ≤ R ^ 2 / 2 := div_nonneg (sq_nonneg R) (by norm_num)
    constructor
    · exact mul_nonneg hfactor (by linarith [hi.1])
    · calc
        R ^ 2 / 2 * (z (Fin.natAdd n i) + 1) ≤ R ^ 2 / 2 * 2 :=
          mul_le_mul_of_nonneg_left (by linarith [hi.2]) hfactor
        _ = R ^ 2 := by ring

theorem unitBoxLiftPolynomial_nonneg_on_hypercube
    {R : ℝ} (hR : 0 < R)
    {P : MvPolynomial (Fin (n + m)) ℝ}
    (hP : ∀ z ∈ slackValueBox R, 0 ≤ MvPolynomial.eval z P) :
    IsNonnegOn (unitBoxLiftPolynomial R P) (Hypercube (n + m)) := by
  intro z hz
  rw [eval_unitBoxLiftPolynomial]
  exact hP _ (unitToSlackValuePoint_mem_slackValueBox hR.le hz)

theorem unitCubePullback_unitBoxLiftPolynomial
    {R : ℝ} (hR : R ≠ 0)
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (P : MvPolynomial (Fin (n + m)) ℝ) :
    MvPolynomial.aeval (unitCubePullbackMap R g)
        (unitBoxLiftPolynomial R P) =
      generatorSlackSubstitution g P := by
  unfold unitBoxLiftPolynomial
  change MvPolynomial.aeval (unitCubePullbackMap R g)
      (MvPolynomial.bind₁ (unitToSlackValueMap R) P) = _
  rw [MvPolynomial.aeval_bind₁]
  apply congrArg (fun f : Fin (n + m) → MvPolynomial (Fin n) ℝ ↦
    MvPolynomial.aeval f P)
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp only [unitToSlackValueMap, Fin.addCases_left, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, aeval_X,
      unitCubePullbackMap]
    rw [← mul_assoc, ← C_mul]
    field_simp
    simp
  · intro i
    simp only [unitToSlackValueMap, Fin.addCases_right, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, map_add, map_one,
      aeval_X, unitCubePullbackMap]
    rw [sub_add_cancel, ← mul_assoc, ← C_mul]
    have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
    field_simp
    simp

end CQCInternal
end OptimalConvergenceRates
end
