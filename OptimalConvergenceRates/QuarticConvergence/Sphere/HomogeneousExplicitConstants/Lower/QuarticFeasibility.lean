import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.HardQuartic
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Lower.FiniteReindex
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Shared.ExplicitFeasibility

/-!
# The padded hard quartic in the ordinary `Fin (N+2)` sphere model

The finite relabeling is an equivalence, and the extra coordinate is exactly
the unused sphere coordinate from the transfer argument. Explicit SOS roots
prove nonemptiness of every feasible-value set of order at least two.
-/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace Foundation

open scoped BigOperators

section ExplicitRoots

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

def normalizedNegativeCoefficient : ℝ :=
  (1 / 16 : ℝ) * ((Fintype.card E : ℝ) / 4) *
    (1 / Real.sqrt (Fintype.card E : ℝ)) ^ 4

omit [Fintype V] [DecidableEq V] in
theorem normalizedNegativeCoefficient_nonneg :
    0 ≤ normalizedNegativeCoefficient (E := E) := by
  unfold normalizedNegativeCoefficient
  positivity

def normalizedQuarticSquareRoot (i j k : E → V) (b : E → ℝ) :
    E ⊕ V → MvPolynomial (Option V) ℝ :=
  Sum.elim
    (fun e ↦ MvPolynomial.C (1 / 4 : ℝ) *
      MvPolynomial.eval₂ MvPolynomial.C (normalizedVariablePolynomial i j k)
        (clauseRootPolynomial i j k b e))
    (fun v ↦ MvPolynomial.C
        (Real.sqrt (6 * (clauseOccurrenceCount i j k v : ℝ)) / 4) *
      MvPolynomial.eval₂ MvPolynomial.C (normalizedVariablePolynomial i j k)
        (deviationRootPolynomial v))

omit [Fintype V] in
theorem normalizedQuarticSquareRoot_isHomogeneous (i j k : E → V) (b : E → ℝ)
    (a : E ⊕ V) : (normalizedQuarticSquareRoot i j k b a).IsHomogeneous 2 := by
  cases a with
  | inl e =>
      exact ((clauseRootPolynomial_isHomogeneous i j k b e).eval₂ MvPolynomial.C
        (normalizedVariablePolynomial i j k) (fun r ↦ MvPolynomial.isHomogeneous_C _ r)
        (normalizedVariablePolynomial_isHomogeneous i j k)).C_mul _
  | inr v =>
      exact ((deviationRootPolynomial_isHomogeneous v).eval₂ MvPolynomial.C
        (normalizedVariablePolynomial i j k) (fun r ↦ MvPolynomial.isHomogeneous_C _ r)
        (normalizedVariablePolynomial_isHomogeneous i j k)).C_mul _

theorem normalizedQuartic_sos_sub_fourth (i j k : E → V) (b : E → ℝ) :
    normalizedQuarticPolynomial i j k b =
      (∑ a : E ⊕ V, normalizedQuarticSquareRoot i j k b a ^ 2) -
        MvPolynomial.C (normalizedNegativeCoefficient (E := E)) * MvPolynomial.X none ^ 4 := by
  classical
  let L := fun e ↦ MvPolynomial.eval₂ MvPolynomial.C (normalizedVariablePolynomial i j k)
    (clauseRootPolynomial i j k b e)
  let Q := fun v ↦ MvPolynomial.eval₂ MvPolynomial.C (normalizedVariablePolynomial i j k)
    (deviationRootPolynomial v)
  have hclause : ∀ e, normalizedQuarticSquareRoot i j k b (Sum.inl e) ^ 2 =
      MvPolynomial.C (1 / 16 : ℝ) * L e ^ 2 := by
    intro e
    change (MvPolynomial.C (1 / 4 : ℝ) * L e) ^ 2 = _
    rw [mul_pow, ← MvPolynomial.C_pow]
    norm_num
  have hpenalty : ∀ v, normalizedQuarticSquareRoot i j k b (Sum.inr v) ^ 2 =
      (MvPolynomial.C (1 / 16 : ℝ) * MvPolynomial.C 6) *
        (MvPolynomial.C (clauseOccurrenceCount i j k v : ℝ) * Q v ^ 2) := by
    intro v
    have hsqrt : (Real.sqrt (6 * (clauseOccurrenceCount i j k v : ℝ)) / 4) ^ 2 =
        (1 / 16 : ℝ) * 6 * (clauseOccurrenceCount i j k v : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by positivity)]
      ring
    change (MvPolynomial.C
      (Real.sqrt (6 * (clauseOccurrenceCount i j k v : ℝ)) / 4) * Q v) ^ 2 = _
    rw [mul_pow, ← MvPolynomial.C_pow, hsqrt, MvPolynomial.C_mul, MvPolynomial.C_mul]
    ring
  have hsum : (∑ a : E ⊕ V, normalizedQuarticSquareRoot i j k b a ^ 2) =
      MvPolynomial.C (1 / 16 : ℝ) *
        ((∑ e : E, L e ^ 2) + MvPolynomial.C 6 *
          (∑ v : V, MvPolynomial.C (clauseOccurrenceCount i j k v : ℝ) * Q v ^ 2)) := by
    rw [Fintype.sum_sum_type]
    simp_rw [hclause, hpenalty]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hnegative :
      MvPolynomial.C (1 / 16 : ℝ) *
        (MvPolynomial.C ((Fintype.card E : ℝ) / 4) *
          normalizedVariablePolynomial i j k none ^ 4) =
      MvPolynomial.C (normalizedNegativeCoefficient (E := E)) *
        (MvPolynomial.X none : MvPolynomial (Option V) ℝ) ^ 4 := by
    simp only [normalizedVariablePolynomial, normalizedNegativeCoefficient,
      mul_pow, MvPolynomial.C_mul, MvPolynomial.C_pow]
    ring
  rw [hsum]
  unfold normalizedQuarticPolynomial xorQuarticPolynomial
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  change MvPolynomial.C (1 / 16 : ℝ) *
      ((∑ e : E, L e ^ 2) + MvPolynomial.C 6 *
        (∑ v : V, MvPolynomial.C (clauseOccurrenceCount i j k v : ℝ) * Q v ^ 2) -
          MvPolynomial.C ((Fintype.card E : ℝ) / 4) *
            normalizedVariablePolynomial i j k none ^ 4) = _
  rw [mul_sub, hnegative]

end ExplicitRoots

def HardQuarticData.coordinateEquiv {N K : ℕ} (_D : HardQuarticData N K) :
    Option (Option (Fin N)) ≃ Fin (N + 2) :=
  (Fintype.equivFin _).trans (finCongr (by simp [Nat.add_assoc]))

def HardQuarticData.finitePolynomial {N K : ℕ} (D : HardQuarticData N K) : Polynomial (N + 2) :=
  MvPolynomial.rename D.coordinateEquiv (paddedPolynomial D.polynomial)

theorem HardQuarticData.finitePolynomial_isHomogeneous {N K : ℕ} (D : HardQuarticData N K) :
    D.finitePolynomial.IsHomogeneous 4 :=
  D.polynomial_isHomogeneous.rename_isHomogeneous.rename_isHomogeneous

theorem HardQuarticData.finitePolynomial_nonneg {N K : ℕ} (D : HardQuarticData N K)
    (x : Fin (N + 2) → ℝ) : 0 ≤ MvPolynomial.eval x D.finitePolynomial := by
  rw [HardQuarticData.finitePolynomial, MvPolynomial.eval_rename,
    paddedPolynomial, MvPolynomial.eval_rename]
  exact D.polynomial_nonneg _

theorem HardQuarticData.finitePolynomial_le_one_on_ball {N K : ℕ} (D : HardQuarticData N K)
    (x : Fin (N + 2) → ℝ) (hx : (∑ v : Fin (N + 2), x v ^ 2) ≤ 1) :
    MvPolynomial.eval x D.finitePolynomial ≤ 1 := by
  let y : Option (Option (Fin N)) → ℝ := x ∘ D.coordinateEquiv
  have hynorm : (∑ v : Option (Option (Fin N)), y v ^ 2) ≤ 1 :=
    (D.coordinateEquiv.sum_comp (fun v ↦ x v ^ 2)).le.trans hx
  have hinner : (∑ v : Option (Fin N), y (some v) ^ 2) ≤ 1 := by
    rw [Fintype.sum_option] at hynorm
    linarith [sq_nonneg (y none)]
  rw [HardQuarticData.finitePolynomial, MvPolynomial.eval_rename,
    paddedPolynomial, MvPolynomial.eval_rename]
  exact D.polynomial_le_one_on_ball (fun v ↦ y (some v)) hinner

theorem HardQuarticData.finitePolynomial_minimum_zero {N K : ℕ} (D : HardQuarticData N K) :
    IsSphereMinimum D.finitePolynomial 0 := by
  apply isSphereMinimum_reindex D.coordinateEquiv (paddedPolynomial D.polynomial) 0
  · intro x hx
    rw [paddedPolynomial, MvPolynomial.eval_rename]
    exact D.polynomial_nonneg _
  · exact ⟨paddingPole, paddingPole_sphere,
      paddedPolynomial_pole_eval D.polynomial D.polynomial_isHomogeneous⟩

theorem HardQuarticData.polynomial_positive_last_axis {N K : ℕ} (D : HardQuarticData N K) :
    0 < MvPolynomial.eval paddingPole D.polynomial := by
  have hmpos : (0 : ℝ) < (Fintype.card (Fin (8 * N)) : ℝ) := by
    exact_mod_cast D.edge_count_pos
  have hbase : 0 < xorQuartic D.first D.second D.third D.label (fun _ ↦ 0) 1 :=
    (by positivity : (0 : ℝ) < (Fintype.card (Fin (8 * N)) : ℝ) / 4).trans_le
      (xorQuartic_at_one_lower D.first D.second D.third D.label D.label_abs D.soundness (fun _ ↦ 0))
  have ha : 0 < 1 / Real.sqrt (Fintype.card (Fin (8 * N)) : ℝ) := by positivity
  have hscale := xorQuartic_homogeneous D.first D.second D.third D.label
    (1 / Real.sqrt (Fintype.card (Fin (8 * N)) : ℝ)) (fun _ ↦ 0) 1
  simp only [mul_zero, mul_one] at hscale
  change 0 < MvPolynomial.eval paddingPole
    (normalizedQuarticPolynomial D.first D.second D.third D.label)
  rw [normalizedQuarticPolynomial_eval]
  change 0 < normalizedQuartic D.first D.second D.third D.label (fun _ ↦ 0) 1
  unfold normalizedQuartic
  have hzero : positiveWeightCoordinate D.first D.second D.third (fun _ ↦ 0) =
      (fun _ : Fin N ↦ (0 : ℝ)) := by
    funext v
    simp [positiveWeightCoordinate]
  rw [hzero, hscale]
  exact div_pos (mul_pos (pow_pos ha 4) hbase) (by norm_num)

def HardQuarticData.finitePositivePoint {N K : ℕ} (D : HardQuarticData N K) : Fin (N + 2) → ℝ :=
  reindexedPoint D.coordinateEquiv (fun v : Option (Option (Fin N)) ↦
    v.elim 0 paddingPole)

theorem HardQuarticData.finitePositivePoint_sphere {N K : ℕ} (D : HardQuarticData N K) :
    D.finitePositivePoint ∈ unitSphere (N + 2) := by
  change (∑ v : Fin (N + 2), D.finitePositivePoint v ^ 2) = 1
  rw [HardQuarticData.finitePositivePoint, reindexedPoint_sum_sq]
  simp [Fintype.sum_option, paddingPole]

theorem HardQuarticData.finitePositivePoint_eval_pos {N K : ℕ} (D : HardQuarticData N K) :
    0 < MvPolynomial.eval D.finitePositivePoint D.finitePolynomial := by
  rw [HardQuarticData.finitePolynomial, HardQuarticData.finitePositivePoint, eval_reindexedPoint,
    paddedPolynomial, MvPolynomial.eval_rename]
  exact D.polynomial_positive_last_axis

theorem HardQuarticData.finitePolynomial_sphereSupNorm_pos {N K : ℕ} (D : HardQuarticData N K) :
    0 < sphereSupNorm D.finitePolynomial := by
  exact sphereSupNorm_pos_of_nonzero_value D.finitePositivePoint_sphere
    (ne_of_gt D.finitePositivePoint_eval_pos)

theorem HardQuarticData.finitePolynomial_sphereSupNorm_le_one {N K : ℕ} (D : HardQuarticData N K) :
    sphereSupNorm D.finitePolynomial ≤ 1 := by
  obtain ⟨x, hx, hvalue⟩ := sphereSupNorm_attained (by omega : 0 < N + 2) D.finitePolynomial
  rw [← hvalue, abs_of_nonneg (D.finitePolynomial_nonneg x)]
  exact D.finitePolynomial_le_one_on_ball x (le_of_eq hx)

/-- A finite family of quadratic roots and one nonpositive coordinate fourth
power give an explicit standard certificate after relabeling the variables. -/
theorem feasible_reindex_of_fintype_sos_sub_fourth {σ I : Type*} [Fintype σ] [Fintype I]
    {n r : ℕ} (e : σ ≃ Fin n) (t : σ) (c : ℝ) (hc : 0 ≤ c)
    (p : MvPolynomial σ ℝ) (h : I → MvPolynomial σ ℝ)
    (hh : ∀ a, (h a).totalDegree ≤ 2)
    (hp : p = (∑ a : I, h a ^ 2) - MvPolynomial.C c * MvPolynomial.X t ^ 4)
    (hr : 2 ≤ r) : Feasible r (MvPolynomial.rename e p) (-c) := by
  classical
  let u := (Fintype.equivFin I).symm
  have he : MvPolynomial.rename e p =
      (∑ a : I, MvPolynomial.rename e (h a) ^ 2) -
        MvPolynomial.C c * MvPolynomial.X (e t) ^ 4 := by
    have hrename := congrArg (MvPolynomial.rename e) hp
    simpa only [map_sub, map_sum, map_pow, map_mul, MvPolynomial.rename_C,
      MvPolynomial.rename_X] using hrename
  apply feasible_of_sos_sub_coordinate_fourth (e t) hc hr
    (fun j : Fin (Fintype.card I) ↦ MvPolynomial.rename e (h (u j)))
  · intro j
    exact (MvPolynomial.totalDegree_rename_le e (h (u j))).trans (hh (u j))
  · rw [u.sum_comp (fun a ↦ MvPolynomial.rename e (h a) ^ 2)]
    exact he

/-- The same explicitly feasible value works at every order at least two. -/
theorem HardQuarticData.finitePolynomial_feasible {N K : ℕ} (D : HardQuarticData N K)
    (r : ℕ) (hr : 2 ≤ r) :
    Feasible r D.finitePolynomial (-(normalizedNegativeCoefficient (E := Fin (8 * N)))) := by
  let H : (Fin (8 * N) ⊕ Fin N) → MvPolynomial (Option (Option (Fin N))) ℝ :=
    fun a ↦ paddedPolynomial (normalizedQuarticSquareRoot D.first D.second D.third D.label a)
  have hh : ∀ a, (H a).totalDegree ≤ 2 := by
    intro a
    exact (MvPolynomial.IsHomogeneous.rename_isHomogeneous
      (normalizedQuarticSquareRoot_isHomogeneous D.first D.second D.third D.label a)).totalDegree_le
  have hp : paddedPolynomial D.polynomial =
      (∑ a : Fin (8 * N) ⊕ Fin N, H a ^ 2) -
        MvPolynomial.C (normalizedNegativeCoefficient (E := Fin (8 * N))) *
          MvPolynomial.X (some (none : Option (Fin N))) ^ 4 := by
    have hpad := congrArg (paddedPolynomial (σ := Option (Fin N)))
      (normalizedQuartic_sos_sub_fourth D.first D.second D.third D.label)
    simpa only [HardQuarticData.polynomial, paddedPolynomial, map_sub, map_sum,
      map_pow, map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X, H] using hpad
  exact feasible_reindex_of_fintype_sos_sub_fourth D.coordinateEquiv
    (some (none : Option (Fin N))) (normalizedNegativeCoefficient (E := Fin (8 * N)))
    normalizedNegativeCoefficient_nonneg (paddedPolynomial D.polynomial) H hh hp hr

theorem HardQuarticData.feasibleValues_nonempty {N K : ℕ} (D : HardQuarticData N K)
    (r : ℕ) (hr : 2 ≤ r) : (feasibleValues r D.finitePolynomial).Nonempty :=
  ⟨-(normalizedNegativeCoefficient (E := Fin (8 * N))), D.finitePolynomial_feasible r hr⟩

end Foundation
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
