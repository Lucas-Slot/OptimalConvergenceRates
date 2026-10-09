import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ParentPatch
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.UniformSplit
import Mathlib.Analysis.Calculus.ContDiff.Bounds

open Set
open scoped Topology

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence

/-- The radius on which a value `delta` survives a gradient bound `M`.  The extra `1` in the
denominator avoids a separate zero-gradient case and the minimum keeps the argument inside the
unit ball where the intrinsic-patch estimates are available. -/
def positiveValuePersistenceRadius (delta M : ℝ) : ℝ :=
  min 1 (delta / (2 * (M + 1)))

theorem positiveValuePersistenceRadius_pos {delta M : ℝ}
    (hdelta : 0 < delta) (hM : 0 ≤ M) :
    0 < positiveValuePersistenceRadius delta M := by
  exact lt_min zero_lt_one (div_pos hdelta (mul_pos (by norm_num) (by linarith)))

theorem positiveValuePersistenceRadius_le_one (delta M : ℝ) :
    positiveValuePersistenceRadius delta M ≤ 1 :=
  min_le_left _ _

theorem mul_positiveValuePersistenceRadius_le_half {delta M : ℝ}
    (hdelta : 0 ≤ delta) (hM : 0 ≤ M) :
    M * positiveValuePersistenceRadius delta M ≤ delta / 2 := by
  have hM1 : 0 < M + 1 := by linarith
  calc
    M * positiveValuePersistenceRadius delta M ≤
        M * (delta / (2 * (M + 1))) := by
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hM
    _ ≤ delta / 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hratio : M / (M + 1) ≤ 1 := (div_le_one hM1).2 (by linarith)
      have hfactor : M * (2 * (M + 1))⁻¹ ≤ (2 : ℝ)⁻¹ := by
        calc
          M * (2 * (M + 1))⁻¹ = (M / (M + 1)) / 2 := by
            field_simp [hM1.ne']
          _ ≤ 1 / 2 := div_le_div_of_nonneg_right hratio (by norm_num)
          _ = (2 : ℝ)⁻¹ := by norm_num
      calc
        M * (delta * (2 * (M + 1))⁻¹) = delta * (M * (2 * (M + 1))⁻¹) := by ring
        _ ≤ delta * (2 : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hfactor hdelta

/-- Quantitative persistence of a positive value under a first-derivative bound on the unit ball.
This is the positive-value alternative after intrinsic rescaling. -/
theorem lower_bound_on_positiveValueBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Phi : E → ℝ} {delta M : ℝ}
    (hdelta : 0 < delta) (hM : 0 ≤ M) (hPhi0 : delta ≤ Phi 0)
    (hPhi : Differentiable ℝ Phi)
    (hderiv : ∀ z, ‖z‖ ≤ 1 → ‖fderiv ℝ Phi z‖ ≤ M)
    {z : E} (hz : ‖z‖ ≤ positiveValuePersistenceRadius delta M) :
    delta / 2 ≤ Phi z := by
  have hzOne : ‖z‖ ≤ 1 := hz.trans (positiveValuePersistenceRadius_le_one delta M)
  have hbound (w : E) (hw : w ∈ segment ℝ (0 : E) z) : ‖fderiv ℝ Phi w‖ ≤ M := by
    apply hderiv w
    have hwz : ‖w - 0‖ ≤ ‖z - 0‖ := norm_sub_le_of_mem_segment hw
    have hwz' : ‖w‖ ≤ ‖z‖ := by simpa only [sub_zero] using hwz
    exact hwz'.trans hzOne
  have hmv := (convex_segment (0 : E) z).norm_image_sub_le_of_norm_fderiv_le
    (s := segment ℝ (0 : E) z) (x := (0 : E)) (y := z) (C := M)
    (fun w _ ↦ hPhi w) hbound (left_mem_segment ℝ 0 z) (right_mem_segment ℝ 0 z)
  have hvariation : |Phi z - Phi 0| ≤ M * ‖z‖ := by
    simpa [Real.norm_eq_abs] using hmv
  have hsmall : M * ‖z‖ ≤ delta / 2 :=
    (mul_le_mul_of_nonneg_left hz hM).trans
      (mul_positiveValuePersistenceRadius_le_half hdelta.le hM)
  have hdrop : Phi 0 - Phi z ≤ delta / 2 := by
    calc
      Phi 0 - Phi z ≤ |Phi z - Phi 0| := by rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ M * ‖z‖ := hvariation
      _ ≤ delta / 2 := hsmall
  linarith

section RegularizedSqrt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The everywhere-smooth square root used by the positive-value alternative. -/
def regularizedPositiveSqrt (a : ℝ) (Phi : E → ℝ) (x : E) : ℝ :=
  Real.sqrt (positiveIdentityRegularization a (Phi x))

theorem regularizedPositiveSqrt_contDiff {a : ℝ} {Phi : E → ℝ}
    (ha : 0 < a) (hPhi : ContDiff ℝ 4 Phi) :
    ContDiff ℝ 4 (regularizedPositiveSqrt a Phi) := by
  have hreg : ContDiff ℝ 4 (fun x ↦ positiveIdentityRegularization a (Phi x)) :=
    (positiveIdentityRegularization_contDiff a).comp hPhi
  exact hreg.sqrt (fun x ↦ ne_of_gt (positiveIdentityRegularization_pos ha))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem regularizedPositiveSqrt_eq {a : ℝ} {Phi : E → ℝ} {x : E}
    (ha : 0 < a) (hx : a ≤ Phi x) :
    regularizedPositiveSqrt a Phi x = Real.sqrt (Phi x) := by
  rw [regularizedPositiveSqrt, positiveIdentityRegularization_eq_self ha hx]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem regularizedPositiveSqrt_sq {a : ℝ} {Phi : E → ℝ} {x : E}
    (ha : 0 < a) (hx : a ≤ Phi x) :
    regularizedPositiveSqrt a Phi x ^ 2 = Phi x := by
  rw [regularizedPositiveSqrt_eq ha hx, Real.sq_sqrt (ha.le.trans hx)]


/-- On a bounded scalar interval, all derivatives through order four of the fixed regularized
square-root function admit one common bound. -/
theorem exists_regularizedPositiveSqrt_scalar_deriv_bound (a B : ℝ)
    (ha : 0 < a) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t : ℝ, |t| ≤ B → ∀ j, j ≤ 4 →
        ‖iteratedFDeriv ℝ j
          (regularizedPositiveSqrt a (fun s : ℝ ↦ s)) t‖ ≤ K := by
  let outer : ℝ → ℝ := regularizedPositiveSqrt a (fun s : ℝ ↦ s)
  have houter : ContDiff ℝ 4 outer :=
    regularizedPositiveSqrt_contDiff ha contDiff_id
  have hbound (j : ℕ) (hj : j ≤ 4) :
      ∃ K : ℝ, ∀ t ∈ Set.Icc (-B) B, ‖iteratedFDeriv ℝ j outer t‖ ≤ K :=
    isCompact_Icc.exists_bound_of_continuousOn
      ((houter.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn)
  obtain ⟨K0, hK0⟩ := hbound 0 (by norm_num)
  obtain ⟨K1, hK1⟩ := hbound 1 (by norm_num)
  obtain ⟨K2, hK2⟩ := hbound 2 (by norm_num)
  obtain ⟨K3, hK3⟩ := hbound 3 (by norm_num)
  obtain ⟨K4, hK4⟩ := hbound 4 (by norm_num)
  have hzero : (0 : ℝ) ∈ Set.Icc (-B) B := ⟨by linarith, hB⟩
  have hK0nonneg : 0 ≤ K0 := (norm_nonneg _).trans (hK0 0 hzero)
  have hK1nonneg : 0 ≤ K1 := (norm_nonneg _).trans (hK1 0 hzero)
  have hK2nonneg : 0 ≤ K2 := (norm_nonneg _).trans (hK2 0 hzero)
  have hK3nonneg : 0 ≤ K3 := (norm_nonneg _).trans (hK3 0 hzero)
  have hK4nonneg : 0 ≤ K4 := (norm_nonneg _).trans (hK4 0 hzero)
  let K := K0 + K1 + K2 + K3 + K4
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro t ht j hj
  have htIcc : t ∈ Set.Icc (-B) B := abs_le.mp ht
  interval_cases j
  · exact (hK0 t htIcc).trans (by dsimp [K]; linarith)
  · exact (hK1 t htIcc).trans (by dsimp [K]; linarith)
  · exact (hK2 t htIcc).trans (by dsimp [K]; linarith)
  · exact (hK3 t htIcc).trans (by dsimp [K]; linarith)
  · exact (hK4 t htIcc).trans (by dsimp [K]; linarith)

/-- Bounded jets of a scalar field give dimension-independent bounded jets of its regularized
square root.  The bound depends only on the threshold and the common input-jet bound. -/
theorem exists_uniform_regularizedPositiveSqrt_deriv_bound (a M : ℝ)
    (ha : 0 < a) (hM : 1 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {n : ℕ} {Phi : (Fin n → ℝ) → ℝ}, ContDiff ℝ 4 Phi →
        ∀ x : Fin n → ℝ,
          (∀ q, q ≤ 4 → ‖iteratedFDeriv ℝ q Phi x‖ ≤ M) →
          ∀ j, j ≤ 4 →
            ‖iteratedFDeriv ℝ j (regularizedPositiveSqrt a Phi) x‖ ≤ A := by
  obtain ⟨K, hKnonneg, houterBound⟩ :=
    exists_regularizedPositiveSqrt_scalar_deriv_bound a M ha (zero_le_one.trans hM)
  let outer : ℝ → ℝ := regularizedPositiveSqrt a (fun s : ℝ ↦ s)
  let A : ℝ := (Nat.factorial 4 : ℝ) * K * M ^ 4
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro n Phi hPhi x hPhiBound j hj
  have hvalue : |Phi x| ≤ M := by
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hPhiBound 0 (by norm_num)
  have houter : ContDiff ℝ 4 outer :=
    regularizedPositiveSqrt_contDiff ha contDiff_id
  have hinner (i : ℕ) (hiOne : 1 ≤ i) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i Phi x‖ ≤ M ^ i := by
    calc
      ‖iteratedFDeriv ℝ i Phi x‖ ≤ M := hPhiBound i (hi.trans hj)
      _ = M ^ 1 := by ring
      _ ≤ M ^ i := pow_le_pow_right₀ hM hiOne
  have hcomp := norm_iteratedFDeriv_comp_le houter hPhi
    (by exact_mod_cast hj) x
    (C := K) (D := M)
    (fun i hi ↦ houterBound (Phi x) hvalue i (hi.trans hj)) hinner
  have hfactorial : (j.factorial : ℝ) ≤ (Nat.factorial 4 : ℝ) := by
    exact_mod_cast Nat.factorial_le hj
  have hpower : M ^ j ≤ M ^ 4 := pow_le_pow_right₀ hM hj
  rw [show regularizedPositiveSqrt a Phi = outer ∘ Phi by rfl]
  calc
    ‖iteratedFDeriv ℝ j (outer ∘ Phi) x‖ ≤ (j.factorial : ℝ) * K * M ^ j := hcomp
    _ ≤ (Nat.factorial 4 : ℝ) * K * M ^ 4 := by gcongr
    _ = A := rfl

end RegularizedSqrt


section CutoffRoot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The compactly supported positive-branch root.  Regularization is performed before the cutoff
is multiplied in, so the function remains globally C4 even where `Phi` is not positive. -/
def positiveValuePatchRoot (a : ℝ) (cutoff Phi : E → ℝ) (x : E) : ℝ :=
  cutoff x * regularizedPositiveSqrt a Phi x

theorem positiveValuePatchRoot_contDiff {a : ℝ} {cutoff Phi : E → ℝ}
    (ha : 0 < a) (hcutoff : ContDiff ℝ 4 cutoff) (hPhi : ContDiff ℝ 4 Phi) :
    ContDiff ℝ 4 (positiveValuePatchRoot a cutoff Phi) :=
  hcutoff.mul (regularizedPositiveSqrt_contDiff ha hPhi)

omit [NormedSpace ℝ E] in
theorem positiveValuePatchRoot_compactSupport {a : ℝ} {cutoff Phi : E → ℝ}
    (hcutoff : HasCompactSupport cutoff) :
    HasCompactSupport (positiveValuePatchRoot a cutoff Phi) :=
  hcutoff.mul_right

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem support_positiveValuePatchRoot_subset (a : ℝ) (cutoff Phi : E → ℝ) :
    Function.support (positiveValuePatchRoot a cutoff Phi) ⊆ Function.support cutoff := by
  intro x hx hcutoff
  apply hx
  simp [positiveValuePatchRoot, hcutoff]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- If the cutoff is supported in the positive region, the global root has the required exact
square, both on and off the support. -/
theorem positiveValuePatchRoot_sq {a : ℝ} {cutoff Phi : E → ℝ}
    (ha : 0 < a) (hlower : ∀ x, cutoff x ≠ 0 → a ≤ Phi x) (x : E) :
    positiveValuePatchRoot a cutoff Phi x ^ 2 = cutoff x ^ 2 * Phi x := by
  by_cases hcutoff : cutoff x = 0
  · simp [positiveValuePatchRoot, hcutoff]
  · rw [positiveValuePatchRoot, mul_pow,
      regularizedPositiveSqrt_sq ha (hlower x hcutoff)]

end CutoffRoot

/-- Uniform C4 bounds persist after multiplying the positive root by a cutoff with uniformly
bounded C4 jets. -/
theorem exists_uniform_positiveValuePatchRoot_deriv_bound
    (a Mcut MPhi : ℝ) (ha : 0 < a) (hMcut : 0 ≤ Mcut) (hMPhi : 1 ≤ MPhi) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {n : ℕ} {cutoff Phi : (Fin n → ℝ) → ℝ},
        ContDiff ℝ 4 cutoff → ContDiff ℝ 4 Phi →
        ∀ x : Fin n → ℝ,
          (∀ q, q ≤ 4 → ‖iteratedFDeriv ℝ q cutoff x‖ ≤ Mcut) →
          (∀ q, q ≤ 4 → ‖iteratedFDeriv ℝ q Phi x‖ ≤ MPhi) →
          ∀ j, j ≤ 4 →
            ‖iteratedFDeriv ℝ j (positiveValuePatchRoot a cutoff Phi) x‖ ≤ A := by
  obtain ⟨Aroot, hAroot, hroot⟩ :=
    exists_uniform_regularizedPositiveSqrt_deriv_bound a MPhi ha hMPhi
  let A := 16 * Mcut * Aroot
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro n cutoff Phi hcutoff hPhi x hcutoffBound hPhiBound j hj
  have hrootSmooth := regularizedPositiveSqrt_contDiff ha hPhi
  have hproduct := norm_iteratedFDeriv_mul_le hcutoff hrootSmooth x
    (by exact_mod_cast hj)
  have hsum :
      ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i cutoff x‖ *
            ‖iteratedFDeriv ℝ (j - i) (regularizedPositiveSqrt a Phi) x‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Mcut * Aroot := by
    apply Finset.sum_le_sum
    intro i hi
    have hiJ : i ≤ j := Finset.mem_range_succ_iff.mp hi
    have hsubJ : j - i ≤ j := Nat.sub_le j i
    gcongr
    · exact hcutoffBound i (hiJ.trans hj)
    · exact hroot hPhi x hPhiBound (j - i) (hsubJ.trans hj)
  have hchoose :
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Mcut * Aroot) =
        (2 : ℝ) ^ j * Mcut * Aroot := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    norm_cast
    rw [Nat.sum_range_choose]
  have hpow : (2 : ℝ) ^ j ≤ 16 := by
    interval_cases j <;> norm_num
  change ‖iteratedFDeriv ℝ j
    (fun y ↦ cutoff y * regularizedPositiveSqrt a Phi y) x‖ ≤ A
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i cutoff x‖ *
            ‖iteratedFDeriv ℝ (j - i) (regularizedPositiveSqrt a Phi) x‖ := hproduct
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Mcut * Aroot := hsum
    _ = (2 : ℝ) ^ j * Mcut * Aroot := hchoose
    _ ≤ 16 * Mcut * Aroot := by gcongr
    _ = A := rfl


section IntrinsicPatch

/-- The intrinsic patch stays uniformly positive on an explicit ball whenever its value at the
origin clears a fixed threshold.  The derivative bound is supplied by `ParentPatch`. -/
theorem intrinsicRescaledPatch_lower_bound_on_positiveValueBall
    {n : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c) {delta : ℝ} (hdelta : 0 < delta)
    (hcenter : delta ≤ intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0)
    {z : Fin n → ℝ}
    (hz : ‖z‖ ≤ positiveValuePersistenceRadius delta (4 * (C + 1))) :
    delta / 2 ≤ intrinsicRescaledPatch u c (nonnegativeJetScale u c) z := by
  let Phi := intrinsicRescaledPatch u c (nonnegativeJetScale u c)
  let M := 4 * (C + 1)
  have hM : 0 ≤ M := by
    dsimp [M]
    nlinarith [hcontrol.constant_nonneg]
  have hPhi : ContDiff ℝ 6 Phi :=
    intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)
  apply lower_bound_on_positiveValueBall hdelta hM hcenter
      (hPhi.differentiable (by norm_num))
  · intro w hw
    have hbound := intrinsicRescaledPatch_uniform_deriv_on_unitBall
      hu hcontrol c hR w hw 1 (by norm_num)
    simpa only [Phi, M, norm_iteratedFDeriv_one] using hbound
  · simpa [M] using hz

/-- The globally regularized root of an intrinsically rescaled positive patch. -/
def intrinsicPositiveValueRoot {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (c : Fin n → ℝ) (R delta : ℝ) : (Fin n → ℝ) → ℝ :=
  regularizedPositiveSqrt (delta / 2) (intrinsicRescaledPatch u c R)

theorem intrinsicPositiveValueRoot_contDiff {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 6 u) (c : Fin n → ℝ) (R : ℝ) {delta : ℝ}
    (hdelta : 0 < delta) :
    ContDiff ℝ 4 (intrinsicPositiveValueRoot u c R delta) := by
  exact regularizedPositiveSqrt_contDiff (half_pos hdelta)
    ((intrinsicRescaledPatch_contDiff hu c R).of_le (by norm_num))

/-- On the persistence ball, the intrinsic positive root is the true square root. -/
theorem intrinsicPositiveValueRoot_eq_sqrt
    {n : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c) {delta : ℝ} (hdelta : 0 < delta)
    (hcenter : delta ≤ intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0)
    {z : Fin n → ℝ}
    (hz : ‖z‖ ≤ positiveValuePersistenceRadius delta (4 * (C + 1))) :
    intrinsicPositiveValueRoot u c (nonnegativeJetScale u c) delta z =
      Real.sqrt (intrinsicRescaledPatch u c (nonnegativeJetScale u c) z) := by
  apply regularizedPositiveSqrt_eq (half_pos hdelta)
  exact intrinsicRescaledPatch_lower_bound_on_positiveValueBall
    hu hcontrol c hR hdelta hcenter hz

/-- Consequently, the intrinsic positive root has exactly the desired square on that ball. -/
theorem intrinsicPositiveValueRoot_sq
    {n : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c) {delta : ℝ} (hdelta : 0 < delta)
    (hcenter : delta ≤ intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0)
    {z : Fin n → ℝ}
    (hz : ‖z‖ ≤ positiveValuePersistenceRadius delta (4 * (C + 1))) :
    intrinsicPositiveValueRoot u c (nonnegativeJetScale u c) delta z ^ 2 =
      intrinsicRescaledPatch u c (nonnegativeJetScale u c) z := by
  rw [intrinsicPositiveValueRoot_eq_sqrt hu hcontrol c hR hdelta hcenter hz,
    Real.sq_sqrt (intrinsicRescaledPatch_nonnegative hu.nonnegative c hR z)]

/-- A cutoff supported in the persistence ball turns the intrinsic patch into one exact global
square term after multiplication by the squared cutoff. -/
theorem intrinsic_positiveValuePatchRoot_sq
    {n : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c) {delta : ℝ} (hdelta : 0 < delta)
    (hcenter : delta ≤ intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0)
    {cutoff : (Fin n → ℝ) → ℝ}
    (hsupport : ∀ z, cutoff z ≠ 0 →
      ‖z‖ ≤ positiveValuePersistenceRadius delta (4 * (C + 1)))
    (z : Fin n → ℝ) :
    positiveValuePatchRoot (delta / 2) cutoff
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) z ^ 2 =
      cutoff z ^ 2 * intrinsicRescaledPatch u c (nonnegativeJetScale u c) z := by
  apply positiveValuePatchRoot_sq (half_pos hdelta)
  intro w hw
  exact intrinsicRescaledPatch_lower_bound_on_positiveValueBall
    hu hcontrol c hR hdelta hcenter (hsupport w hw)

/-- The C4 jets of all intrinsic positive roots are bounded by a constant depending only on the
jet-control constant and the fixed positivity threshold, not on dimension, center, or scale. -/
theorem exists_uniform_intrinsicPositiveValueRoot_deriv_bound
    (C delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {n : ℕ} {u : (Fin n → ℝ) → ℝ}, NormalizedNonnegativeC6 u →
        NonnegativeJetControl u C → ∀ (c : Fin n → ℝ),
          0 < nonnegativeJetScale u c → ∀ z, ‖z‖ ≤ 1 →
            ∀ j, j ≤ 4 →
              ‖iteratedFDeriv ℝ j
                (intrinsicPositiveValueRoot u c (nonnegativeJetScale u c) delta) z‖ ≤ A := by
  let M := 4 * (C + 1)
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith
  obtain ⟨A, hA, hroot⟩ :=
    exists_uniform_regularizedPositiveSqrt_deriv_bound (delta / 2) M
      (half_pos hdelta) hM
  refine ⟨A, hA, ?_⟩
  intro n u hu hcontrol c hR z hz j hj
  apply hroot
    ((intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)).of_le
      (by norm_num)) z
  · intro q hq
    exact intrinsicRescaledPatch_uniform_deriv_on_unitBall
      hu hcontrol c hR z hz q (hq.trans (by norm_num))
  · exact hj

/-- The same uniform conclusion after multiplication by any cutoff with a common C4 jet bound. -/
theorem exists_uniform_intrinsicPositiveValuePatchRoot_deriv_bound
    (C delta Mcut : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) (hMcut : 0 ≤ Mcut) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {n : ℕ} {u : (Fin n → ℝ) → ℝ} {cutoff : (Fin n → ℝ) → ℝ},
        NormalizedNonnegativeC6 u → NonnegativeJetControl u C →
        ContDiff ℝ 4 cutoff → ∀ (c : Fin n → ℝ),
          0 < nonnegativeJetScale u c → ∀ z, ‖z‖ ≤ 1 →
            (∀ q, q ≤ 4 → ‖iteratedFDeriv ℝ q cutoff z‖ ≤ Mcut) →
            ∀ j, j ≤ 4 →
              ‖iteratedFDeriv ℝ j
                (positiveValuePatchRoot (delta / 2) cutoff
                  (intrinsicRescaledPatch u c (nonnegativeJetScale u c))) z‖ ≤ A := by
  let M := 4 * (C + 1)
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith
  obtain ⟨A, hA, hroot⟩ :=
    exists_uniform_positiveValuePatchRoot_deriv_bound
      (delta / 2) Mcut M (half_pos hdelta) hMcut hM
  refine ⟨A, hA, ?_⟩
  intro n u cutoff hu hcontrol hcutoff c hR z hz hcutoffBound j hj
  apply hroot hcutoff
    ((intrinsicRescaledPatch_contDiff hu.contDiff c (nonnegativeJetScale u c)).of_le
      (by norm_num)) z hcutoffBound
  · intro q hq
    exact intrinsicRescaledPatch_uniform_deriv_on_unitBall
      hu hcontrol c hR z hz q (hq.trans (by norm_num))
  · exact hj


/-- If the cutoff support lies in the intrinsic unit ball, the preceding local estimate is a
global derivative estimate: outside that ball every derivative vanishes by support localization. -/
theorem exists_uniform_intrinsicPositiveValuePatchRoot_global_deriv_bound
    (C delta Mcut : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) (hMcut : 0 ≤ Mcut) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ {n : ℕ} {u : (Fin n → ℝ) → ℝ} {cutoff : (Fin n → ℝ) → ℝ},
        NormalizedNonnegativeC6 u → NonnegativeJetControl u C →
        ContDiff ℝ 4 cutoff → ∀ (c : Fin n → ℝ),
          0 < nonnegativeJetScale u c →
          Function.support cutoff ⊆ Metric.closedBall 0 1 →
          (∀ z q, q ≤ 4 → ‖iteratedFDeriv ℝ q cutoff z‖ ≤ Mcut) →
          ∀ z j, j ≤ 4 →
            ‖iteratedFDeriv ℝ j
              (positiveValuePatchRoot (delta / 2) cutoff
                (intrinsicRescaledPatch u c (nonnegativeJetScale u c))) z‖ ≤ A := by
  obtain ⟨A, hA, hlocal⟩ :=
    exists_uniform_intrinsicPositiveValuePatchRoot_deriv_bound
      C delta Mcut hC hdelta hMcut
  refine ⟨A, hA, ?_⟩
  intro n u cutoff hu hcontrol hcutoff c hR hsupport hcutoffBound z j hj
  by_cases hz : ‖z‖ ≤ 1
  · exact hlocal hu hcontrol hcutoff c hR z hz (hcutoffBound z) j hj
  · let root : (Fin n → ℝ) → ℝ :=
      positiveValuePatchRoot (delta / 2) cutoff
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c))
    have hrootSupport : Function.support root ⊆ Function.support cutoff := by
      simpa [root] using support_positiveValuePatchRoot_subset
        (delta / 2) cutoff (intrinsicRescaledPatch u c (nonnegativeJetScale u c))
    have hrootTopologicalSupport : tsupport root ⊆ Metric.closedBall 0 1 :=
      closure_minimal (hrootSupport.trans hsupport) Metric.isClosed_closedBall
    have hzBall : z ∉ Metric.closedBall (0 : Fin n → ℝ) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hzTopologicalSupport : z ∉ tsupport root :=
      fun hmem ↦ hzBall (hrootTopologicalSupport hmem)
    have hzDerivSupport : z ∉ Function.support (iteratedFDeriv ℝ j root) :=
      fun hmem ↦ hzTopologicalSupport (support_iteratedFDeriv_subset j hmem)
    have hzero : iteratedFDeriv ℝ j root z = 0 := by
      simpa [Function.mem_support] using hzDerivSupport
    rw [show positiveValuePatchRoot (delta / 2) cutoff
        (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) = root by rfl,
      hzero, norm_zero]
    exact hA

end IntrinsicPatch

end OptimalConvergenceRates.QuarticConvergence

end
