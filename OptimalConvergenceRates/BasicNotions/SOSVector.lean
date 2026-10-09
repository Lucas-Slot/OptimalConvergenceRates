/-
  OptimalConvergenceRates/BasicNotions/SOSVector.lean

  Finite-dimensional vector norms and inequalities used to package SOS witnesses.
-/
import OptimalConvergenceRates.BasicNotions.Defs

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n N : ℕ}

/-- Squared Euclidean norm of a finite real vector. -/
def vecSqNorm (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, v i ^ 2

theorem vecSqNorm_nonneg (v : Fin N → ℝ) : 0 ≤ vecSqNorm v := by
  unfold vecSqNorm
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

theorem vecSqNorm_zero {v : Fin N → ℝ} (hv : ∀ i, v i = 0) :
    vecSqNorm v = 0 := by
  unfold vecSqNorm
  apply Finset.sum_eq_zero
  intro i _
  rw [hv i]
  ring

/-- The square-root norm associated to `vecSqNorm`. -/
def vecNorm (v : Fin N → ℝ) : ℝ :=
  Real.sqrt (vecSqNorm v)

theorem vecNorm_nonneg (v : Fin N → ℝ) : 0 ≤ vecNorm v := by
  unfold vecNorm
  exact Real.sqrt_nonneg _

theorem vecNorm_sq (v : Fin N → ℝ) :
    vecNorm v ^ 2 = vecSqNorm v := by
  unfold vecNorm
  exact Real.sq_sqrt (vecSqNorm_nonneg v)

theorem vecSqNorm_le_of_vecNorm_le {v : Fin N → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (h : vecNorm v ≤ B) :
    vecSqNorm v ≤ B ^ 2 := by
  rw [← vecNorm_sq v]
  nlinarith [vecNorm_nonneg v]

/-- Euclidean dot product for finite real vectors. -/
def vecDot (u v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, u i * v i

theorem vecDot_self (v : Fin N → ℝ) :
    vecDot v v = vecSqNorm v := by
  unfold vecDot vecSqNorm
  congr 1
  ext i
  ring

theorem abs_vecDot_le_vecNorm_mul (u v : Fin N → ℝ) :
    |vecDot u v| ≤ vecNorm u * vecNorm v := by
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N)) u v
  unfold vecDot vecNorm vecSqNorm
  have hprod_nonneg : 0 ≤ Real.sqrt (∑ i : Fin N, u i ^ 2) *
      Real.sqrt (∑ i : Fin N, v i ^ 2) := by
    positivity
  have hsumu_nonneg : 0 ≤ ∑ i : Fin N, u i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (u i)
  have hsumv_nonneg : 0 ≤ ∑ i : Fin N, v i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hprod_sq : (Real.sqrt (∑ i : Fin N, u i ^ 2) *
      Real.sqrt (∑ i : Fin N, v i ^ 2)) ^ 2 =
      (∑ i : Fin N, u i ^ 2) * ∑ i : Fin N, v i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hsumu_nonneg, Real.sq_sqrt hsumv_nonneg]
  have hsquares : (∑ i : Fin N, u i * v i) ^ 2 ≤
      (Real.sqrt (∑ i : Fin N, u i ^ 2) * Real.sqrt (∑ i : Fin N, v i ^ 2)) ^ 2 := by
    rwa [hprod_sq]
  have habs := sq_le_sq.mp hsquares
  rwa [abs_of_nonneg hprod_nonneg] at habs

theorem vecDot_le_vecNorm_mul (u v : Fin N → ℝ) :
    vecDot u v ≤ vecNorm u * vecNorm v := by
  exact (le_abs_self _).trans (abs_vecDot_le_vecNorm_mul u v)

/-- If the squared norm is bounded by a nonnegative square, then the norm is bounded. -/
theorem vecNorm_le_of_vecSqNorm_le {v : Fin N → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (h : vecSqNorm v ≤ B ^ 2) :
    vecNorm v ≤ B := by
  unfold vecNorm
  calc
    Real.sqrt (vecSqNorm v) ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt h
    _ = B := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB]

/-- Triangle inequality for the finite-vector norm. -/
theorem vecNorm_add_le (u v : Fin N → ℝ) :
    vecNorm (fun i => u i + v i) ≤ vecNorm u + vecNorm v := by
  have hright_nonneg : 0 ≤ vecNorm u + vecNorm v :=
    add_nonneg (vecNorm_nonneg u) (vecNorm_nonneg v)
  apply vecNorm_le_of_vecSqNorm_le hright_nonneg
  have hleft : vecSqNorm (fun i => u i + v i) =
      vecSqNorm u + 2 * vecDot u v + vecSqNorm v := by
    unfold vecSqNorm vecDot
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [show (∑ x : Fin N, 2 * u x * v x) = 2 * (∑ x : Fin N, u x * v x) by
      rw [Finset.mul_sum]
      congr 1
      ext x
      ring]
  have hright : (vecNorm u + vecNorm v) ^ 2 =
      vecSqNorm u + 2 * (vecNorm u * vecNorm v) + vecSqNorm v := by
    rw [add_sq, vecNorm_sq, vecNorm_sq]
    ring
  rw [hleft, hright]
  nlinarith [vecDot_le_vecNorm_mul u v]

/-- Triangle inequality for differences of finite vectors. -/
theorem vecNorm_sub_le (u v : Fin N → ℝ) :
    vecNorm (fun i => u i - v i) ≤ vecNorm u + vecNorm v := by
  have h := vecNorm_add_le u (fun i => -v i)
  have hneg : vecNorm (fun i => -v i) = vecNorm v := by
    unfold vecNorm vecSqNorm
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa [sub_eq_add_neg, hneg] using h

theorem vecDot_unit_self {v : Fin N → ℝ} (hv : vecNorm v ≠ 0) :
    vecDot (fun i => v i / vecNorm v) v = vecNorm v := by
  unfold vecDot
  calc
    (∑ i : Fin N, v i / vecNorm v * v i)
        = ∑ i : Fin N, v i ^ 2 * (vecNorm v)⁻¹ := by
            congr 1
            ext i
            ring
    _ = (∑ i : Fin N, v i ^ 2) / vecNorm v := by
            rw [div_eq_mul_inv, Finset.sum_mul]
    _ = vecSqNorm v / vecNorm v := by rfl
    _ = vecNorm v := by
        rw [← vecNorm_sq v]
        field_simp [hv]

theorem vecNorm_smul_nonneg (c : ℝ) (hc : 0 ≤ c) (v : Fin N → ℝ) :
    vecNorm (fun i => c * v i) = c * vecNorm v := by
  unfold vecNorm vecSqNorm
  rw [show (∑ i : Fin N, (c * v i) ^ 2) = c ^ 2 * ∑ i : Fin N, v i ^ 2 by
    simp_rw [mul_pow]
    rw [Finset.mul_sum]
  ]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

theorem abs_vecDot_unit_le {v : Fin N → ℝ} (hv : vecNorm v ≠ 0) (w : Fin N → ℝ) :
    |vecDot (fun i => v i / vecNorm v) w| ≤ vecNorm w := by
  have hvn_pos : 0 < vecNorm v := lt_of_le_of_ne (vecNorm_nonneg v) (Ne.symm hv)
  have hunit : vecNorm (fun i => v i / vecNorm v) = 1 := by
    have hscale := vecNorm_smul_nonneg (N := N) (1 / vecNorm v) (by positivity) v
    rw [show (fun i => v i / vecNorm v) = fun i => (1 / vecNorm v) * v i by
      funext i
      ring]
    simpa [div_eq_mul_inv, hv] using hscale
  have h := abs_vecDot_le_vecNorm_mul (fun i => v i / vecNorm v) w
  rwa [hunit, one_mul] at h

/-! ## Compatibility norm API used by the Schmuedgen developments -/

/-- Squared Euclidean norm for a finite real vector. -/
def interiorVecSqNorm {N : ℕ} (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, v i ^ 2

/-- Euclidean norm for a finite real vector. -/
def interiorVecNorm {N : ℕ} (v : Fin N → ℝ) : ℝ :=
  Real.sqrt (interiorVecSqNorm v)

theorem interiorVecSqNorm_nonneg {N : ℕ} (v : Fin N → ℝ) : 0 ≤ interiorVecSqNorm v := by
  unfold interiorVecSqNorm
  exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg (v i))

theorem interiorVecNorm_nonneg {N : ℕ} (v : Fin N → ℝ) : 0 ≤ interiorVecNorm v := by
  unfold interiorVecNorm
  exact Real.sqrt_nonneg _

theorem component_abs_le_interiorVecNorm {N : ℕ} (v : Fin N → ℝ) (i : Fin N) :
    |v i| ≤ interiorVecNorm v := by
  unfold interiorVecNorm interiorVecSqNorm
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact Finset.single_le_sum (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)

theorem component_eq_zero_of_interiorVecNorm_le_zero {N : ℕ} {v : Fin N → ℝ}
    (hv : interiorVecNorm v ≤ 0) (i : Fin N) :
    v i = 0 := by
  have hnorm0 : interiorVecNorm v = 0 := le_antisymm hv (interiorVecNorm_nonneg v)
  have habs := component_abs_le_interiorVecNorm v i
  rw [hnorm0] at habs
  exact abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))

theorem interiorVecNorm_abs {N : ℕ} (v : Fin N → ℝ) :
    interiorVecNorm (fun i ↦ |v i|) = interiorVecNorm v := by
  unfold interiorVecNorm interiorVecSqNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [sq_abs]

theorem interiorVecNorm_add_le {N : ℕ} (u v : Fin N → ℝ) :
    interiorVecNorm (fun i ↦ u i + v i) ≤ interiorVecNorm u + interiorVecNorm v := by
  simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using vecNorm_add_le u v

theorem interiorVecNorm_neg {N : ℕ} (u : Fin N → ℝ) :
    interiorVecNorm (fun i ↦ -u i) = interiorVecNorm u := by
  unfold interiorVecNorm interiorVecSqNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem interiorVecNorm_smul_abs {N : ℕ} (c : ℝ) (u : Fin N → ℝ) :
    interiorVecNorm (fun i ↦ c * u i) = |c| * interiorVecNorm u := by
  rcases le_total 0 c with hc | hc
  · simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm, abs_of_nonneg hc] using
      vecNorm_smul_nonneg (N := N) c hc u
  · rcases eq_or_lt_of_le hc with rfl | hc'
    · simp [interiorVecNorm, interiorVecSqNorm]
    · have hnc : 0 ≤ -c := le_of_lt (neg_pos.mpr hc')
      calc
        interiorVecNorm (fun i ↦ c * u i) =
            interiorVecNorm (fun i ↦ (-c) * (-u i)) := by
              congr 1
              funext i
              ring
        _ = (-c) * interiorVecNorm (fun i ↦ -u i) := by
          simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using
            vecNorm_smul_nonneg (N := N) (-c) hnc (fun i ↦ -u i)
        _ = |c| * interiorVecNorm u := by rw [interiorVecNorm_neg, abs_of_neg hc']

theorem interiorVecNorm_sub_le {N : ℕ} (u v : Fin N → ℝ) :
    interiorVecNorm (fun i ↦ u i - v i) ≤ interiorVecNorm u + interiorVecNorm v := by
  simpa [interiorVecNorm, interiorVecSqNorm, vecNorm, vecSqNorm] using vecNorm_sub_le u v

theorem interiorVecNorm_finset_sum_le_sum_norm {N : ℕ} {ι : Type*}
    (s : Finset ι) (V : ι → Fin N → ℝ) :
    interiorVecNorm (fun i ↦ ∑ z ∈ s, V z i) ≤ ∑ z ∈ s, interiorVecNorm (V z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [interiorVecNorm, interiorVecSqNorm]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (interiorVecNorm_add_le (V a) (fun i ↦ ∑ z ∈ s, V z i)).trans
        (by linarith)

end OptimalConvergenceRates

end
