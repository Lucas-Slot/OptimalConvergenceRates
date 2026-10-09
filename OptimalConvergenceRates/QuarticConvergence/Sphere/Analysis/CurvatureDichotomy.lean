import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.ParentPatch

open Set
open scoped BigOperators Topology
noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence

/-- A bilinear map whose norm is larger than `r` has a pair of unit vectors on which its
absolute value is larger than `r`. -/
theorem exists_unit_pair_of_lt_norm {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Fin n → ℝ) ℝ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < ‖H‖) :
    ∃ x y : Fin n → ℝ, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ r < |H ![x, y]| := by
  have hex : ∃ m, r * ∏ i, ‖m i‖ < ‖H m‖ := by
    by_contra h
    push_neg at h
    exact (not_le_of_gt hr) (H.opNorm_le_bound hr0 h)
  rcases hex with ⟨m, hm⟩
  have hmrepr : ![m 0, m 1] = m := by
    ext i
    fin_cases i <;> simp
  rw [← hmrepr] at hm
  have hm0 : ‖m 0‖ ≠ 0 := by
    intro hzero
    have hmzero : m 0 = 0 := norm_eq_zero.mp hzero
    have hHzero : H ![m 0, m 1] = 0 := H.map_coord_zero 0 (by simp [hmzero])
    rw [hHzero, norm_zero] at hm
    have hprod0 : (∏ i, ‖![m 0, m 1] i‖) = 0 := by simp [hzero]
    rw [hprod0, mul_zero] at hm
    exact (lt_irrefl 0 hm)
  have hm1 : ‖m 1‖ ≠ 0 := by
    intro hzero
    have hmzero : m 1 = 0 := norm_eq_zero.mp hzero
    have hHzero : H ![m 0, m 1] = 0 := H.map_coord_zero 1 (by simp [hmzero])
    rw [hHzero, norm_zero] at hm
    have hprod0 : (∏ i, ‖![m 0, m 1] i‖) = 0 := by simp [hzero]
    rw [hprod0, mul_zero] at hm
    exact (lt_irrefl 0 hm)
  let x : Fin n → ℝ := ‖m 0‖⁻¹ • m 0
  let y : Fin n → ℝ := ‖m 1‖⁻¹ • m 1
  have hx : ‖x‖ = 1 := by
    simp [x, norm_smul, hm0]
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, hm1]
  refine ⟨x, y, hx, hy, ?_⟩
  dsimp [x, y]
  have hvec : ![‖m 0‖⁻¹ • m 0, ‖m 1‖⁻¹ • m 1] =
      fun i ↦ ![‖m 0‖⁻¹, ‖m 1‖⁻¹] i • ![m 0, m 1] i := by
    ext i
    fin_cases i <;> simp
  rw [hvec, H.map_smul_univ]
  rw [Real.norm_eq_abs] at hm
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  rw [abs_mul, abs_mul, abs_inv, abs_inv, abs_of_nonneg (norm_nonneg (m 0)),
    abs_of_nonneg (norm_nonneg (m 1))]
  have hn0pos : 0 < ‖m 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hm0)
  have hn1pos : 0 < ‖m 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hm1)
  have hpos : 0 < ‖m 0‖ * ‖m 1‖ := mul_pos hn0pos hn1pos
  have hinv : ‖m 0‖⁻¹ * ‖m 1‖⁻¹ * |H ![m 0, m 1]| =
      |H ![m 0, m 1]| / (‖m 0‖ * ‖m 1‖) := by
    field_simp
  rw [hinv]
  apply (lt_div_iff₀' hpos).2
  simpa [Fin.prod_univ_two, mul_assoc, mul_left_comm, mul_comm] using hm


theorem bilinear_neg_right {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Fin n → ℝ) ℝ)
    (x y : Fin n → ℝ) : H ![x, -y] = -H ![x, y] := by
  calc
    H ![x, -y] = (H.curryLeft x) (fun i : Fin 1 ↦ (-1 : ℝ) • (fun _ ↦ y) i) := by
      change H ![x, -y] = H (Fin.cons x (fun i : Fin 1 ↦ (-1 : ℝ) • (fun _ ↦ y) i))
      apply congrArg H
      funext i
      fin_cases i
      · rfl
      · simp
    _ = (∏ _ : Fin 1, (-1 : ℝ)) • (H.curryLeft x) (fun _ ↦ y) :=
      (H.curryLeft x).map_smul_univ _ _
    _ = -H ![x, y] := by
      rw [show (∏ _ : Fin 1, (-1 : ℝ)) = -1 by simp, neg_one_smul]
      apply congrArg Neg.neg
      change H (Fin.cons x fun _ : Fin 1 ↦ y) = H ![x, y]
      apply congrArg H
      ext i
      fin_cases i <;> simp

theorem bilinear_add_left {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Fin n → ℝ) ℝ)
    (x y z : Fin n → ℝ) : H ![x + y, z] = H ![x, z] + H ![y, z] := by
  change H.curryLeft (x + y) ![z] = _
  rw [map_add]
  rfl

theorem bilinear_add_right {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Fin n → ℝ) ℝ)
    (x y z : Fin n → ℝ) : H ![x, y + z] = H ![x, y] + H ![x, z] := by
  change (H.curryLeft x) ![y + z] = _
  have hupdate : ![y + z] = Function.update ![y] 0 (y + z) := by
    ext i
    fin_cases i
    simp
  rw [hupdate, (H.curryLeft x).map_update_add]
  have hyself : Function.update ![y] 0 y = ![y] := by
    ext i
    fin_cases i
    simp
  have hzself : Function.update ![y] 0 z = ![z] := by
    ext i
    fin_cases i
    simp
  rw [hyself, hzself]
  rfl

theorem bilinear_add_add {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Fin n → ℝ) ℝ)
    (x y : Fin n → ℝ) :
    H ![x + y, x + y] = H ![x, x] + H ![x, y] + H ![y, x] + H ![y, y] := by
  rw [bilinear_add_left H, bilinear_add_right H, bilinear_add_right H]
  ring

theorem bilinear_smul_diagonal {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Fin n → ℝ) ℝ)
    (a : ℝ) (x : Fin n → ℝ) : H ![a • x, a • x] = a ^ 2 * H ![x, x] := by
  have hvec : ![a • x, a • x] = fun i ↦ (fun _ : Fin 2 ↦ a) i • ![x, x] i := by
    ext i
    fin_cases i <;> simp
  rw [hvec, H.map_smul_univ]
  simp [pow_two, smul_eq_mul]

/-- A symmetric bilinear form of norm one whose negative diagonal part is at most `1/8`
has a unit vector on which its diagonal is at least `1/4`. -/
theorem exists_unit_diagonal_quarter_of_norm_one {n : ℕ}
    (H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Fin n → ℝ) ℝ)
    (hH : ‖H‖ = 1)
    (hsymm : ∀ x y : Fin n → ℝ, H ![x, y] = H ![y, x])
    {μ : ℝ} (hμ : μ ≤ 1 / 8)
    (hlower : ∀ v : Fin n → ℝ, -(μ * ‖v‖ ^ 2) ≤ H ![v, v]) :
    ∃ v : Fin n → ℝ, ‖v‖ = 1 ∧ 1 / 4 ≤ H ![v, v] := by
  have hthreequarters : (3 / 4 : ℝ) < ‖H‖ := by rw [hH]; norm_num
  rcases exists_unit_pair_of_lt_norm H (by norm_num : (0 : ℝ) ≤ 3 / 4) hthreequarters with
    ⟨x, y, hx, hy, hxyabs⟩
  let y' : Fin n → ℝ := if 0 ≤ H ![x, y] then y else -y
  have hy' : ‖y'‖ = 1 := by
    by_cases hsign : 0 ≤ H ![x, y]
    · simp [y', hsign, hy]
    · simp [y', hsign, hy]
  have hxy : (3 / 4 : ℝ) < H ![x, y'] := by
    by_cases hsign : 0 ≤ H ![x, y]
    · simpa [y', hsign, abs_of_nonneg hsign] using hxyabs
    · have hneg : H ![x, y] < 0 := lt_of_not_ge hsign
      rw [abs_of_neg hneg] at hxyabs
      change (3 / 4 : ℝ) < H ![x, if 0 ≤ H ![x, y] then y else -y]
      rw [if_neg hsign]
      rw [bilinear_neg_right]
      exact hxyabs
  let z := x + y'
  have hzdiag : 1 < H ![z, z] := by
    have hxx := hlower x
    have hyy := hlower y'
    rw [hx, one_pow, mul_one] at hxx
    rw [hy', one_pow, mul_one] at hyy
    change 1 < H ![x + y', x + y']
    rw [bilinear_add_add,
      hsymm y' x]
    nlinarith
  have hznorm : ‖z‖ ≤ 2 := by
    calc
      ‖z‖ = ‖x + y'‖ := rfl
      _ ≤ ‖x‖ + ‖y'‖ := norm_add_le _ _
      _ = 2 := by rw [hx, hy']; norm_num
  have hzne : z ≠ 0 := by
    intro hz
    have hzero : H ![z, z] = 0 := H.map_coord_zero 0 (by simpa using hz)
    rw [hzero] at hzdiag
    norm_num at hzdiag
  have hznormne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hzne
  have hznormpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hznormne)
  let v := ‖z‖⁻¹ • z
  have hvnorm : ‖v‖ = 1 := by simp [v, norm_smul, hznormne]
  refine ⟨v, hvnorm, ?_⟩
  rw [show v = ‖z‖⁻¹ • z by rfl, bilinear_smul_diagonal]
  have hsq : ‖z‖ ^ 2 ≤ 4 := by nlinarith [sq_nonneg (‖z‖ - 2)]
  have hsqpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos hznormpos
  have hquarter : (1 / 4 : ℝ) * ‖z‖ ^ 2 ≤ H ![z, z] := by nlinarith
  have hdiv : (1 / 4 : ℝ) ≤ H ![z, z] / ‖z‖ ^ 2 :=
    (le_div_iff₀ hsqpos).2 hquarter
  have heq : ‖z‖⁻¹ ^ 2 * H ![z, z] = H ![z, z] / ‖z‖ ^ 2 := by
    field_simp
  rw [heq]
  exact hdiv

/-- The explicit value threshold in the value-versus-curvature dichotomy. -/
def curvatureValueThreshold (C : ℝ) : ℝ := (1 / (16 * (C + 1))) ^ 2

/-- At an intrinsically normalized point, either the value has fixed size or the Hessian has a
uniformly positive unit diagonal. The constants are deliberately coarse and dimension-free. -/
theorem value_or_positive_curvature_at_origin {n : ℕ}
    (Φ : (Fin n → ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    {C : ℝ} (hC : 0 ≤ C) (hΦ0 : 0 ≤ Φ 0)
    (hnormalized :
      max (Real.sqrt (Real.sqrt (Φ 0)))
          (Real.sqrt ‖iteratedFDeriv ℝ 2 Φ 0‖) = 1)
    (hlower : ∀ v : Fin n → ℝ,
      -(C * Real.sqrt (Φ 0) * ‖v‖ ^ 2) ≤ iteratedFDeriv ℝ 2 Φ 0 ![v, v]) :
    curvatureValueThreshold C ≤ Φ 0 ∨
      ∃ v : Fin n → ℝ, ‖v‖ = 1 ∧
        1 / 4 ≤ iteratedFDeriv ℝ 2 Φ 0 ![v, v] := by
  let t : ℝ := 1 / (16 * (C + 1))
  have hCp : 0 < C + 1 := by linarith
  have htpos : 0 < t := by dsimp [t]; positivity
  have htden : 16 * (C + 1) * t = 1 := by
    dsimp [t]
    field_simp
  have ht_le : t ≤ 1 / 16 := by
    have hCt0 : 0 ≤ C * t := mul_nonneg hC htpos.le
    nlinarith
  by_cases hvalue : curvatureValueThreshold C ≤ Φ 0
  · exact Or.inl hvalue
  · right
    have hvalue_lt : Φ 0 < t ^ 2 := by
      simpa [curvatureValueThreshold, t] using lt_of_not_ge hvalue
    have hsqrt_sq : Real.sqrt (Φ 0) ^ 2 = Φ 0 := Real.sq_sqrt hΦ0
    have hsqrt_lt : Real.sqrt (Φ 0) < t := by
      nlinarith [Real.sqrt_nonneg (Φ 0), sq_nonneg (Real.sqrt (Φ 0) - t)]
    have hsqrt_lt_one : Real.sqrt (Φ 0) < 1 := by nlinarith
    have hsqrt_sqrt_lt_one : Real.sqrt (Real.sqrt (Φ 0)) < 1 :=
      (Real.sqrt_lt' zero_lt_one).2 (by simpa using hsqrt_lt_one)
    have hessianSqrt : Real.sqrt ‖iteratedFDeriv ℝ 2 Φ 0‖ = 1 := by
      rcases max_choice (Real.sqrt (Real.sqrt (Φ 0)))
          (Real.sqrt ‖iteratedFDeriv ℝ 2 Φ 0‖) with hleft | hright
      · rw [hleft] at hnormalized
        linarith
      · rw [hright] at hnormalized
        exact hnormalized
    have hessianNorm : ‖iteratedFDeriv ℝ 2 Φ 0‖ = 1 := by
      have hsquare := Real.sq_sqrt (norm_nonneg (iteratedFDeriv ℝ 2 Φ 0))
      rw [hessianSqrt] at hsquare
      norm_num at hsquare ⊢
      exact hsquare.symm
    have hCt : C * t ≤ 1 / 16 := by
      have ht0 : 0 ≤ t := htpos.le
      nlinarith [mul_nonneg hC ht0]
    have hmu : C * Real.sqrt (Φ 0) ≤ 1 / 8 := by
      have hmul : C * Real.sqrt (Φ 0) ≤ C * t :=
        mul_le_mul_of_nonneg_left hsqrt_lt.le hC
      nlinarith
    have hsymm : ∀ x y : Fin n → ℝ,
        iteratedFDeriv ℝ 2 Φ 0 ![x, y] = iteratedFDeriv ℝ 2 Φ 0 ![y, x] := by
      intro x y
      have hs : IsSymmSndFDerivAt ℝ Φ 0 :=
        hΦ.contDiffAt.isSymmSndFDerivAt (by norm_num)
      exact hs.iteratedFDeriv_cons
    apply exists_unit_diagonal_quarter_of_norm_one
      (iteratedFDeriv ℝ 2 Φ 0) hessianNorm hsymm hmu
    intro v
    simpa [mul_assoc] using hlower v

/-- Exact Hessian scaling at the origin of an intrinsically rescaled patch. -/
theorem intrinsicRescaledPatch_iteratedFDeriv_two_zero {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    iteratedFDeriv ℝ 2 (intrinsicRescaledPatch u c R) 0 =
      (R ^ 2)⁻¹ • iteratedFDeriv ℝ 2 u c := by
  let shifted : (Fin n → ℝ) → ℝ := fun w ↦ u (c + w)
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    R • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hshift : ContDiff ℝ 2 shifted := hu.comp (by fun_prop)
  have hcomp :
      iteratedFDeriv ℝ 2 (shifted ∘ L) 0 =
        (iteratedFDeriv ℝ 2 shifted (L 0)).compContinuousLinearMap (fun _ ↦ L) :=
    L.iteratedFDeriv_comp_right hshift 0 (by norm_num)
  have htranslate : iteratedFDeriv ℝ 2 shifted (L 0) = iteratedFDeriv ℝ 2 u c := by
    simpa [shifted, L] using iteratedFDeriv_comp_add_left (𝕜 := ℝ) 2 c (L 0)
  have hfun : intrinsicRescaledPatch u c R = (R ^ 4)⁻¹ • (shifted ∘ L) := by
    funext x
    simp only [intrinsicRescaledPatch, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hfun]
  have hsmoothAt : ContDiffAt ℝ 2 (shifted ∘ L) 0 := (hshift.comp L.contDiff).contDiffAt
  rw [iteratedFDeriv_const_smul_apply hsmoothAt, hcomp, htranslate]
  ext m
  simp only [ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, L,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [(iteratedFDeriv ℝ 2 u c).map_smul_univ]
  simp only [Fin.prod_univ_two, smul_eq_mul]
  field_simp

@[simp] theorem intrinsicRescaledPatch_zero {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (c : Fin n → ℝ) (R : ℝ) :
    intrinsicRescaledPatch u c R 0 = (R ^ 4)⁻¹ * u c := by
  simp [intrinsicRescaledPatch]

/-- Exact Hessian-norm scaling at the origin of an intrinsic patch. -/
theorem norm_intrinsicRescaledPatch_hessian_zero {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    ‖iteratedFDeriv ℝ 2 (intrinsicRescaledPatch u c R) 0‖ =
      (R ^ 2)⁻¹ * ‖iteratedFDeriv ℝ 2 u c‖ := by
  rw [intrinsicRescaledPatch_iteratedFDeriv_two_zero hu c hR, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg R))]

/-- Exact fourth-root value scaling at the origin of an intrinsic patch. -/
theorem sqrt_sqrt_intrinsicRescaledPatch_zero {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (c : Fin n → ℝ) {R : ℝ}
    (hR : 0 < R) :
    Real.sqrt (Real.sqrt (intrinsicRescaledPatch u c R 0)) =
      R⁻¹ * Real.sqrt (Real.sqrt (u c)) := by
  rw [intrinsicRescaledPatch_zero]
  rw [Real.sqrt_mul (inv_nonneg.mpr (pow_nonneg hR.le 4))]
  rw [Real.sqrt_inv]
  have hsqrtR4 : Real.sqrt (R ^ 4) = R ^ 2 := by
    rw [show R ^ 4 = (R ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg R)]
  rw [hsqrtR4]
  rw [Real.sqrt_mul (inv_nonneg.mpr (sq_nonneg R))]
  rw [Real.sqrt_inv, Real.sqrt_sq hR.le]

/-- Exact square-root Hessian scaling at the origin of an intrinsic patch. -/
theorem sqrt_norm_intrinsicRescaledPatch_hessian_zero {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    (c : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    Real.sqrt ‖iteratedFDeriv ℝ 2 (intrinsicRescaledPatch u c R) 0‖ =
      R⁻¹ * Real.sqrt ‖iteratedFDeriv ℝ 2 u c‖ := by
  rw [norm_intrinsicRescaledPatch_hessian_zero hu c hR]
  rw [Real.sqrt_mul (inv_nonneg.mpr (sq_nonneg R)), Real.sqrt_inv,
    Real.sqrt_sq hR.le]

/-- Intrinsic fourth-order rescaling normalizes the scale at the origin to exactly one. -/
theorem intrinsicRescaledPatch_normalized_at_origin {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    {c : Fin n → ℝ} {R : ℝ} (hR : 0 < R)
    (hscale : nonnegativeJetScale u c = R) :
    max (Real.sqrt (Real.sqrt (intrinsicRescaledPatch u c R 0)))
        (Real.sqrt ‖iteratedFDeriv ℝ 2 (intrinsicRescaledPatch u c R) 0‖) = 1 := by
  rw [sqrt_sqrt_intrinsicRescaledPatch_zero c hR,
    sqrt_norm_intrinsicRescaledPatch_hessian_zero hu c hR]
  rw [← mul_max_of_nonneg _ _ (inv_nonneg.mpr hR.le)]
  have hscale_ne : nonnegativeJetScale u c ≠ 0 := by rw [hscale]; exact hR.ne'
  rw [← hscale]
  exact inv_mul_cancel₀ hscale_ne

/-- Exact square-root value scaling at the origin of an intrinsic patch. -/
theorem sqrt_intrinsicRescaledPatch_zero {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (c : Fin n → ℝ) {R : ℝ} (hR : 0 < R) :
    Real.sqrt (intrinsicRescaledPatch u c R 0) = (R ^ 2)⁻¹ * Real.sqrt (u c) := by
  rw [intrinsicRescaledPatch_zero]
  rw [Real.sqrt_mul (inv_nonneg.mpr (pow_nonneg hR.le 4)), Real.sqrt_inv]
  have hsqrtR4 : Real.sqrt (R ^ 4) = R ^ 2 := by
    rw [show R ^ 4 = (R ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg R)]
  rw [hsqrtR4]

/-- The jet-control Hessian bound in the iterated-Fréchet-derivative representation. -/
theorem NonnegativeJetControl.iteratedFDeriv_two_lower {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} {C : ℝ} (hcontrol : NonnegativeJetControl u C)
    (hu : ContDiff ℝ 6 u) (x v : Fin n → ℝ) :
    -(C * Real.sqrt (u x) * ‖v‖ ^ 2) ≤ iteratedFDeriv ℝ 2 u x ![v, v] := by
  have hc : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 u) x :=
    (hu.differentiable_iteratedFDeriv (by norm_num)).differentiableAt
  have hhess : fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v =
      iteratedFDeriv ℝ 2 u x (fun _ ↦ v) := by
    rw [show (fun y ↦ fderiv ℝ u y v) =
        (fun y ↦ iteratedFDeriv ℝ 1 u y (fun _ ↦ v)) by funext y; simp]
    rw [fderiv_continuousMultilinear_apply_const hc (fun _ : Fin 1 ↦ v)]
    rw [iteratedFDeriv_succ_apply_left (n := 1) (f := u) (x := x) (m := fun _ ↦ v)]
    rfl
  calc
    -(C * Real.sqrt (u x) * ‖v‖ ^ 2) ≤
        fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v := hcontrol.hessian_lower x v
    _ = iteratedFDeriv ℝ 2 u x (fun _ ↦ v) := hhess
    _ = iteratedFDeriv ℝ 2 u x ![v, v] := by
      apply congrArg (iteratedFDeriv ℝ 2 u x)
      ext i
      fin_cases i <;> rfl

/-- The Hessian lower bound is invariant under intrinsic fourth-order rescaling. -/
theorem intrinsicRescaledPatch_hessian_lower_at_origin {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C)
    (c : Fin n → ℝ) {R : ℝ} (hR : 0 < R) (v : Fin n → ℝ) :
    -(C * Real.sqrt (intrinsicRescaledPatch u c R 0) * ‖v‖ ^ 2) ≤
      iteratedFDeriv ℝ 2 (intrinsicRescaledPatch u c R) 0 ![v, v] := by
  rw [sqrt_intrinsicRescaledPatch_zero c hR,
    intrinsicRescaledPatch_iteratedFDeriv_two_zero (hu.contDiff.of_le (by norm_num)) c hR,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  have hscaled := mul_le_mul_of_nonneg_left
    (hcontrol.iteratedFDeriv_two_lower hu.contDiff c v)
    (inv_nonneg.mpr (sq_nonneg R))
  convert hscaled using 1
  all_goals ring

/-- The value-versus-positive-curvature dichotomy specialized to the repository's intrinsic
rescaling at a positive nonnegative-jet scale. -/
theorem intrinsicRescaledPatch_value_or_positive_curvature {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c) :
    curvatureValueThreshold C ≤
        intrinsicRescaledPatch u c (nonnegativeJetScale u c) 0 ∨
      ∃ v : Fin n → ℝ, ‖v‖ = 1 ∧
        1 / 4 ≤ iteratedFDeriv ℝ 2
          (intrinsicRescaledPatch u c (nonnegativeJetScale u c)) 0 ![v, v] := by
  let R := nonnegativeJetScale u c
  have hR' : 0 < R := by simpa [R] using hR
  have hsmooth : ContDiff ℝ 2 (intrinsicRescaledPatch u c R) :=
    (intrinsicRescaledPatch_contDiff hu.contDiff c R).of_le (by norm_num)
  have hnonnegative : 0 ≤ intrinsicRescaledPatch u c R 0 :=
    intrinsicRescaledPatch_nonnegative hu.nonnegative c hR' 0
  have hnormalized :
      max (Real.sqrt (Real.sqrt (intrinsicRescaledPatch u c R 0)))
          (Real.sqrt ‖iteratedFDeriv ℝ 2 (intrinsicRescaledPatch u c R) 0‖) = 1 :=
    intrinsicRescaledPatch_normalized_at_origin (hu.contDiff.of_le (by norm_num)) hR' rfl
  have hlower : ∀ v : Fin n → ℝ,
      -(C * Real.sqrt (intrinsicRescaledPatch u c R 0) * ‖v‖ ^ 2) ≤
        iteratedFDeriv ℝ 2 (intrinsicRescaledPatch u c R) 0 ![v, v] :=
    intrinsicRescaledPatch_hessian_lower_at_origin hu hcontrol c hR'
  simpa [R] using value_or_positive_curvature_at_origin
    (intrinsicRescaledPatch u c R) hsmooth hcontrol.constant_nonneg hnonnegative
      hnormalized hlower

/-- The intrinsic-patch dichotomy returned in the original coordinates. -/
theorem value_or_positive_curvature_at_intrinsic_scale {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ)
    (hR : 0 < nonnegativeJetScale u c) :
    curvatureValueThreshold C * nonnegativeJetScale u c ^ 4 ≤ u c ∨
      ∃ v : Fin n → ℝ, ‖v‖ = 1 ∧
        (1 / 4) * nonnegativeJetScale u c ^ 2 ≤ iteratedFDeriv ℝ 2 u c ![v, v] := by
  let R := nonnegativeJetScale u c
  have hR' : 0 < R := by simpa [R] using hR
  rcases intrinsicRescaledPatch_value_or_positive_curvature hu hcontrol c hR with
    hvalue | ⟨v, hvnorm, hcurvature⟩
  · left
    rw [intrinsicRescaledPatch_zero] at hvalue
    have hmul := mul_le_mul_of_nonneg_left hvalue (pow_nonneg hR'.le 4)
    change curvatureValueThreshold C * R ^ 4 ≤ u c
    calc
      curvatureValueThreshold C * R ^ 4 = R ^ 4 * curvatureValueThreshold C := by ring
      _ ≤ R ^ 4 * ((R ^ 4)⁻¹ * u c) := hmul
      _ = u c := by field_simp
  · right
    refine ⟨v, hvnorm, ?_⟩
    rw [intrinsicRescaledPatch_iteratedFDeriv_two_zero
      (hu.contDiff.of_le (by norm_num)) c hR', ContinuousMultilinearMap.smul_apply,
      smul_eq_mul] at hcurvature
    have hmul := mul_le_mul_of_nonneg_left hcurvature (sq_nonneg R)
    change (1 / 4) * R ^ 2 ≤ iteratedFDeriv ℝ 2 u c ![v, v]
    calc
      (1 / 4) * R ^ 2 = R ^ 2 * (1 / 4) := by ring
      _ ≤ R ^ 2 * ((R ^ 2)⁻¹ * iteratedFDeriv ℝ 2 u c ![v, v]) := hmul
      _ = iteratedFDeriv ℝ 2 u c ![v, v] := by field_simp

/-- The original-coordinate dichotomy with the zero intrinsic-scale edge case discharged. -/
theorem value_or_positive_curvature_at_intrinsic_scale_total {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    {C : ℝ} (hcontrol : NonnegativeJetControl u C) (c : Fin n → ℝ) :
    curvatureValueThreshold C * nonnegativeJetScale u c ^ 4 ≤ u c ∨
      ∃ v : Fin n → ℝ, ‖v‖ = 1 ∧
        (1 / 4) * nonnegativeJetScale u c ^ 2 ≤ iteratedFDeriv ℝ 2 u c ![v, v] := by
  by_cases hR : 0 < nonnegativeJetScale u c
  · exact value_or_positive_curvature_at_intrinsic_scale hu hcontrol c hR
  · have hRzero : nonnegativeJetScale u c = 0 :=
      le_antisymm (not_lt.mp hR) (nonnegativeJetScale_nonneg u c)
    left
    rw [hRzero]
    simpa using hu.nonnegative c
end OptimalConvergenceRates.QuarticConvergence
