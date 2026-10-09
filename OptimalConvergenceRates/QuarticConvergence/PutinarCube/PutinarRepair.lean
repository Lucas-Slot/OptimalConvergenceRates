/-
  Degree-linear Putinar repair on the cube.

  The construction enlarges and lifts the shifted polynomial, repairs it on
  the sphere, descends to the enlarged-cube preordering, and eliminates the
  shifted generators using the explicit localized Chebyshev certificates.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarLiftBounds
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarSphereRepair
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarScaledDescent
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PutinarShiftedProducts
import OptimalConvergenceRates.QuarticConvergence.Sphere.SphereIdeal

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers

variable {n D κ A : ℕ}

/-! ## Elementary parameter and zero-norm lemmas -/

/-- A polynomial whose cube sup norm is at most zero is identically zero. -/
theorem eq_zero_of_polySupNorm_le_zero
    (u : MvPolynomial (Fin n) ℝ) (hu : polySupNorm u ≤ 0) :
    u = 0 := by
  apply mvPolynomial_eq_zero_of_eval_eq_zero_on_openCube 1 zero_lt_one
  intro x hx
  have hxCube : x ∈ Hypercube n := by
    rw [Hypercube_mem_iff]
    intro i
    have hi := abs_lt.mp (hx i)
    exact ⟨hi.1.le, hi.2.le⟩
  exact abs_nonpos_iff.mp (polySupNorm_eval_le u 0 hu x hxCube)

/-- The final canonical total-degree coefficient obtained by composing the
sphere repair, descent, and shifted-generator elimination. -/
def putinarRepairOrderConstant (n A κ : ℕ) : ℕ :=
  4 * A * (2 * n + 1) + 4 * n * κ

theorem putinarRepairOrderConstant_one_le
    (n κ : ℕ) {A : ℕ} (hA : 1 ≤ A) :
    1 ≤ putinarRepairOrderConstant n A κ := by
  have hfirst : 0 < 4 * A * (2 * n + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  unfold putinarRepairOrderConstant
  omega

/-- A sufficiently large dimension-only localization multiplier makes the
Chebyshev correction fit inside the enlarged-cube generator shift. -/
theorem two_mul_n_mul_putinarPairMu_le_enlargementShift
    (hD : 1 ≤ D) (hκ1 : 1 ≤ κ)
    (hκsize : 6 * (n : ℝ) * constCChebyshev ≤ (κ : ℝ)) :
    2 * (n : ℝ) * putinarPairMu (κ * D) ≤
      putinarEnlargementShift D := by
  apply le_trans ?_ (putinarEnlargementShift_ge hD)
  have hκR : 0 < (κ : ℝ) := by exact_mod_cast (show 0 < κ by omega)
  have hκR1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ1
  have hDR : 0 < (D : ℝ) := by exact_mod_cast (show 0 < D by omega)
  have hκleSq : (κ : ℝ) ≤ (κ : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg κ) (sub_nonneg.mpr hκR1)]
  have hκsq :
      6 * (n : ℝ) * constCChebyshev ≤ (κ : ℝ) ^ 2 :=
    hκsize.trans hκleSq
  have hleftDen : 0 < ((κ : ℝ) * (D : ℝ)) ^ 2 :=
    sq_pos_of_pos (mul_pos hκR hDR)
  have hrightDen : 0 < 3 * constCChebyshev * (D : ℝ) ^ 2 :=
    mul_pos (mul_pos (by norm_num) constCChebyshev_pos) (sq_pos_of_pos hDR)
  unfold putinarPairMu delta
  rw [Nat.cast_mul]
  change
    2 * (n : ℝ) * (1 / (((κ : ℝ) * (D : ℝ)) ^ 2)) ≤
      1 / (3 * constCChebyshev * (D : ℝ) ^ 2)
  rw [show 2 * (n : ℝ) * (1 / (((κ : ℝ) * (D : ℝ)) ^ 2)) =
    (2 * (n : ℝ)) / (((κ : ℝ) * (D : ℝ)) ^ 2) by ring]
  apply (div_le_div_iff₀ hleftDen hrightDen).2
  calc
    (2 * (n : ℝ)) * (3 * constCChebyshev * (D : ℝ) ^ 2) =
        (6 * (n : ℝ) * constCChebyshev) * (D : ℝ) ^ 2 := by ring
    _ ≤ (κ : ℝ) ^ 2 * (D : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hκsq (sq_nonneg _)
    _ = 1 * ((κ : ℝ) * (D : ℝ)) ^ 2 := by ring


/-! ## Composition with a supplied sphere repair -/

/-- Positive-bound form of the full Putinar repair. The output order is the
repository canonical total certificate degree. -/
theorem add_two_bound_mem_BoxQuadraticModule_of_degreeLinearRepair_pos
    (hn : 0 < n) (hA : 1 ≤ A) (hκ1 : 1 ≤ κ)
    (hκsize : 6 * (n : ℝ) * constCChebyshev ≤ (κ : ℝ))
    (hrepair : HasDegreeLinearRepair (n := 2 * n + 1) A)
    {D : ℕ} (hD : 1 ≤ D) {u : MvPolynomial (Fin n) ℝ} {L : ℝ}
    (huDegree : u.totalDegree ≤ D) (hL : 0 < L)
    (huBound : polySupNorm u ≤ L) :
    u + MvPolynomial.C (2 * L) ∈
      BoxQuadraticModule n (putinarRepairOrderConstant n A κ * D) := by
  let q : MvPolynomial (Fin n) ℝ := u + MvPolynomial.C (2 * L)
  let b : ℝ := putinarEnlargementRadius D
  let E : ℕ := (2 * n + 1) * D
  let P : MvPolynomial (Fin (2 * n + 1)) ℝ :=
    cubeSphereLift n (polyScale b q)
  have hspos : 0 < 2 * n + 1 := by omega
  have hEpos : 0 < E :=
    Nat.mul_pos hspos (show 0 < D by omega)
  have hE : 1 ≤ E := hEpos
  have hPdeg : P.totalDegree ≤ E := by
    simpa only [P, E, b, q] using
      cubeSphereLift_polyScale_add_two_bound_totalDegree_le u D L huDegree
  have hPbounds :
      ∀ z ∈ sphereSet (2 * n + 1),
        L / 2 ≤ MvPolynomial.eval z P ∧
          MvPolynomial.eval z P ≤ 7 * L / 2 := by
    intro z hz
    simpa only [P, b, q] using
      cubeSphereLift_polyScale_add_two_bound_conditioned
        hn u D L hD huDegree huBound z hz
  have hsphere : SphereSOSMod P (2 * A * E) :=
    sphereSOSMod_of_bounded_positive_of_degreeLinearRepair
      hspos hA hE hPdeg hL hPbounds hrepair
  have hsphereExpanded :
      SphereSOSMod (cubeSphereLift n (polyScale b q)) (2 * A * E) := by
    simpa only [P] using hsphere
  have hscaled0 :
      q ∈ ScaledBoxPreordering b n (2 * (2 * A * E)) :=
    sphereSOSMod_cubeSphereLift_polyScale_to_ScaledBoxPreordering
      hn b (ne_of_gt (putinarEnlargementRadius_pos hD)) hsphereExpanded
  have hscaled : q ∈ ScaledBoxPreordering b n (4 * A * E) := by
    rw [show 4 * A * E = 2 * (2 * A * E) by ring]
    exact hscaled0
  have hkpos : 0 < κ * D :=
    Nat.mul_pos (show 0 < κ by omega) (show 0 < D by omega)
  have hk : 1 ≤ κ * D := hkpos
  have hshift :
      2 * (n : ℝ) * putinarPairMu (κ * D) ≤ b ^ 2 - 1 := by
    simpa only [b, putinarEnlargementShift] using
      two_mul_n_mul_putinarPairMu_le_enlargementShift
        (n := n) hD hκ1 hκsize
  have hbox :
      q ∈ BoxQuadraticModule n (4 * A * E + 4 * n * (κ * D)) :=
    scaledBoxPreordering_mem_BoxQuadraticModule
      hn (κ * D) hk b hshift hscaled
  have horder :
      4 * A * E + 4 * n * (κ * D) =
        putinarRepairOrderConstant n A κ * D := by
    dsimp [E, putinarRepairOrderConstant]
    ring
  rw [horder] at hbox
  simpa only [q] using hbox

/-- Full supplied-repair theorem, including the zero-bound case. -/
theorem add_two_bound_mem_BoxQuadraticModule_of_degreeLinearRepair
    (hn : 0 < n) (hA : 1 ≤ A) (hκ1 : 1 ≤ κ)
    (hκsize : 6 * (n : ℝ) * constCChebyshev ≤ (κ : ℝ))
    (hrepair : HasDegreeLinearRepair (n := 2 * n + 1) A)
    {D : ℕ} (hD : 1 ≤ D) {u : MvPolynomial (Fin n) ℝ} {L : ℝ}
    (huDegree : u.totalDegree ≤ D) (hL : 0 ≤ L)
    (huBound : polySupNorm u ≤ L) :
    u + MvPolynomial.C (2 * L) ∈
      BoxQuadraticModule n (putinarRepairOrderConstant n A κ * D) := by
  by_cases hLzero : L = 0
  · subst L
    have huZero : u = 0 :=
      eq_zero_of_polySupNorm_le_zero u huBound
    simpa [huZero] using
      zero_mem_BoxQuadraticModule n
        (putinarRepairOrderConstant n A κ * D)
  · exact add_two_bound_mem_BoxQuadraticModule_of_degreeLinearRepair_pos
      hn hA hκ1 hκsize hrepair hD huDegree
        (lt_of_le_of_ne hL (Ne.symm hLzero)) huBound


/-! ## Dimension-only public repair interface -/

/-- A canonical-order Putinar repair constant for the n-dimensional cube. -/
def HasPutinarDegreeLinearRepair (Aq : ℕ) : Prop :=
  ∀ (D : ℕ) (u : MvPolynomial (Fin n) ℝ) (L : ℝ),
    1 ≤ D →
    u.totalDegree ≤ D →
    0 ≤ L →
    polySupNorm u ≤ L →
    u + MvPolynomial.C (2 * L) ∈ BoxQuadraticModule n (Aq * D)

/-- The supplied sphere repair and localization multiplier give a cube
degree-linear repair with the explicit composed constant. -/
theorem hasPutinarDegreeLinearRepair_of_degreeLinearRepair
    (hn : 0 < n) (hA : 1 ≤ A) (hκ1 : 1 ≤ κ)
    (hκsize : 6 * (n : ℝ) * constCChebyshev ≤ (κ : ℝ))
    (hrepair : HasDegreeLinearRepair (n := 2 * n + 1) A) :
    HasPutinarDegreeLinearRepair (n := n)
      (putinarRepairOrderConstant n A κ) := by
  intro D u L hD huDegree hL huBound
  exact add_two_bound_mem_BoxQuadraticModule_of_degreeLinearRepair
    hn hA hκ1 hκsize hrepair hD huDegree hL huBound

/-- The concrete sphere polynomial kernels yield a dimension-only canonical
Putinar repair constant. -/
theorem exists_putinarDegreeLinearRepair (hn : 0 < n) :
    ∃ Aq : ℕ, 1 ≤ Aq ∧ HasPutinarDegreeLinearRepair (n := n) Aq := by
  have hs3 : 3 ≤ 2 * n + 1 := by omega
  have hspos : 0 < 2 * n + 1 := by omega
  obtain ⟨A, hA, hK⟩ := spherePolynomialKernelRepair hs3
  have hrepair : HasDegreeLinearRepair (n := 2 * n + 1) A :=
    hasDegreeLinearRepair_of_spherePolynomialKernels hspos
      (sphereRestrictionKernelPrincipal_of_three_le hs3) hK
  obtain ⟨κ, hκ⟩ :=
    exists_nat_gt (max (6 * (n : ℝ) * constCChebyshev) 1)
  have hκ1 : 1 ≤ κ := by
    have hκreal : (1 : ℝ) < κ := (le_max_right _ _).trans_lt hκ
    exact_mod_cast hκreal.le
  have hκsize :
      6 * (n : ℝ) * constCChebyshev ≤ (κ : ℝ) :=
    ((le_max_left _ _).trans_lt hκ).le
  refine ⟨putinarRepairOrderConstant n A κ,
    putinarRepairOrderConstant_one_le n κ hA, ?_⟩
  exact hasPutinarDegreeLinearRepair_of_degreeLinearRepair
    hn hA hκ1 hκsize hrepair


/-- Direct supplied-bound form of the dimension-only repair theorem. -/
theorem exists_putinarRepair (hn : 0 < n) :
    ∃ Aq : ℕ, 1 ≤ Aq ∧
      ∀ (D : ℕ) (u : MvPolynomial (Fin n) ℝ) (L : ℝ),
        1 ≤ D →
        u.totalDegree ≤ D →
        0 ≤ L →
        polySupNorm u ≤ L →
        u + MvPolynomial.C (2 * L) ∈ BoxQuadraticModule n (Aq * D) := by
  simpa only [HasPutinarDegreeLinearRepair] using
    exists_putinarDegreeLinearRepair hn

/-- Exact-sup-norm form of the manuscript repair statement. -/
theorem exists_putinarRepair_supNorm (hn : 0 < n) :
    ∃ Aq : ℕ, 1 ≤ Aq ∧
      ∀ (D : ℕ) (u : MvPolynomial (Fin n) ℝ),
        1 ≤ D →
        u.totalDegree ≤ D →
        u + MvPolynomial.C (2 * polySupNorm u) ∈
          BoxQuadraticModule n (Aq * D) := by
  obtain ⟨Aq, hAq, hrepair⟩ := exists_putinarDegreeLinearRepair hn
  refine ⟨Aq, hAq, ?_⟩
  intro D u hD huDegree
  exact hrepair D u (polySupNorm u) hD huDegree
    (polySupNorm_nonneg u) le_rfl

/-- Pointwise-bound form matching the manuscript statement. -/
theorem exists_putinarRepair_of_pointwiseBound (hn : 0 < n) :
    ∃ Aq : ℕ, 1 ≤ Aq ∧
      ∀ (D : ℕ) (u : MvPolynomial (Fin n) ℝ) (L : ℝ),
        1 ≤ D →
        u.totalDegree ≤ D →
        0 ≤ L →
        (∀ x ∈ Hypercube n, |MvPolynomial.eval x u| ≤ L) →
        u + MvPolynomial.C (2 * L) ∈ BoxQuadraticModule n (Aq * D) := by
  obtain ⟨Aq, hAq, hrepair⟩ := exists_putinarDegreeLinearRepair hn
  refine ⟨Aq, hAq, ?_⟩
  intro D u L hD huDegree hL huBound
  exact hrepair D u L hD huDegree hL
    (polySupNorm_le_of_bound u L huBound)

end QuarticConvergence
end OptimalConvergenceRates

end
