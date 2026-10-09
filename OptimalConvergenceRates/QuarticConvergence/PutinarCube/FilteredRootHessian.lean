/-
  Root-count-free square-function estimates for rotation Hessians of the
  retained roots and their normalized Boolean filters.

  The basic rotation Hessian below is the exact second derivative obtained
  by applying two ambient coordinate-rotation vector fields.  Keeping the
  correction term is essential: the vector field itself depends on the
  evaluation point.
-/
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.CircleRoots
import OptimalConvergenceRates.QuarticConvergence.PutinarCube.PositiveKernelContraction
import OptimalConvergenceRates.QuarticConvergence.SchmudgenCube.LiftRegularity
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotation
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.FilterRotationJets

open MvPolynomial Finset Set Filter
open scoped BigOperators Topology

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

open SphereBallTransfers


/-- The linear coordinate-rotation vector field `x_i e_j - x_j e_i`. -/
def coordinateRotationVector {n : ℕ} (i j : Fin n) (x : Fin n → ℝ) : Fin n → ℝ :=
  Pi.single j (x i) - Pi.single i (x j)

set_option maxHeartbeats 400000 in
-- This Pi-space sup-norm estimate needs extra elaboration time after the full analysis imports.
/-- Elaborating the Pi-space sup-norm triangle estimate needs a larger local
heartbeat budget after the project-wide analysis imports. -/
theorem coordinateRotationVector_norm_le_two_mul {n : ℕ}
    (i j : Fin n) (x : Fin n → ℝ) :
    ‖coordinateRotationVector i j x‖ ≤ 2 * ‖x‖ := by
  have hsingle (k : Fin n) (r : ℝ) :
      ‖(Pi.single k r : Fin n → ℝ)‖ = |r| := by
    simpa only [Real.norm_eq_abs] using
      (Pi.norm_single (G := fun _ : Fin n ↦ ℝ) (i := k) r)
  unfold coordinateRotationVector
  calc
    ‖(Pi.single j (x i) : Fin n → ℝ) - Pi.single i (x j)‖ ≤
        ‖(Pi.single j (x i) : Fin n → ℝ)‖ +
          ‖(Pi.single i (x j) : Fin n → ℝ)‖ := norm_sub_le _ _
    _ = |x i| + |x j| := by rw [hsingle, hsingle]
    _ ≤ ‖x‖ + ‖x‖ := by
      exact add_le_add
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
    _ = 2 * ‖x‖ := by ring

/-- The coordinate-rotation vector field as a continuous linear map. -/
def coordinateRotationCLM {n : ℕ} (i j : Fin n) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ((ContinuousLinearMap.single ℝ (fun _ : Fin n ↦ ℝ) j).comp
      (ContinuousLinearMap.proj i)) -
    ((ContinuousLinearMap.single ℝ (fun _ : Fin n ↦ ℝ) i).comp
      (ContinuousLinearMap.proj j))

@[simp] theorem coordinateRotationCLM_apply {n : ℕ} (i j : Fin n)
    (x : Fin n → ℝ) :
    coordinateRotationCLM i j x = coordinateRotationVector i j x := by
  rfl

/-- Applying two coordinate-rotation vector fields to a smooth ambient
function.  The second summand is the derivative of the inner vector field. -/
def rotationHessianValue {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i j a b : Fin n) (x : Fin n → ℝ) : ℝ :=
  iteratedFDeriv ℝ 2 f x
      ![coordinateRotationVector i j x, coordinateRotationVector a b x] +
    fderiv ℝ f x
      (coordinateRotationVector a b (coordinateRotationVector i j x))

/-- Mixed differentiation of a fixed directional derivative is evaluation of
the second iterated Fréchet derivative in the ordered pair of directions. -/
theorem fderiv_directionalFDeriv_mixed_eq_iteratedFDeriv_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y w) x v =
      iteratedFDeriv ℝ 2 f x ![v, w] := by
  have hfirst : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) x :=
    (hf.differentiable_iteratedFDeriv (by norm_num)).differentiableAt
  rw [show (fun y ↦ fderiv ℝ f y w) =
      (fun y ↦ iteratedFDeriv ℝ 1 f y (fun _ ↦ w)) by
        funext y
        simp [iteratedFDeriv_one_apply]]
  rw [fderiv_continuousMultilinear_apply_const hfirst (fun _ : Fin 1 ↦ w)]
  calc
    ((fderiv ℝ (iteratedFDeriv ℝ 1 f) x).flipMultilinear
        (fun _ ↦ w)) v =
        iteratedFDeriv ℝ 2 f x (fun q ↦ if q = 0 then v else w) := by
      rw [iteratedFDeriv_succ_apply_left]
      rfl
    _ = iteratedFDeriv ℝ 2 f x ![v, w] := by
      apply congrArg (iteratedFDeriv ℝ 2 f x)
      funext q
      fin_cases q <;> rfl

/-- The derivative of a variable directional derivative along a second
coordinate-rotation field is exactly `rotationHessianValue`. -/
theorem fderiv_coordinateRotationValue_eq_rotationHessianValue
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (i j a b : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y (coordinateRotationVector a b y)) x
        (coordinateRotationVector i j x) =
      rotationHessianValue f i j a b x := by
  have hcGlobal : ContDiff ℝ 1 (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv.mp hf).2.2
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hcGlobal.differentiable (by norm_num)).differentiableAt
  have hu : DifferentiableAt ℝ
      (fun y ↦ coordinateRotationVector a b y) x := by
    simpa only [← coordinateRotationCLM_apply] using
      (coordinateRotationCLM a b).differentiableAt
  rw [fderiv_clm_apply hc hu]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  have huDeriv :
      fderiv ℝ (fun y ↦ coordinateRotationVector a b y) x =
        coordinateRotationCLM a b := by
    rw [show (fun y ↦ coordinateRotationVector a b y) =
      (coordinateRotationCLM a b : (Fin n → ℝ) → (Fin n → ℝ)) by
        funext y
        exact (coordinateRotationCLM_apply a b y).symm]
    exact ContinuousLinearMap.fderiv (coordinateRotationCLM a b)
  rw [huDeriv, coordinateRotationCLM_apply]
  have hfixed :
      (fderiv ℝ (fderiv ℝ f) x) (coordinateRotationVector i j x)
          (coordinateRotationVector a b x) =
        fderiv ℝ (fun y ↦ fderiv ℝ f y (coordinateRotationVector a b x)) x
          (coordinateRotationVector i j x) := by
    rw [fderiv_clm_apply hc (differentiableAt_const
      (c := coordinateRotationVector a b x))]
    simp
  rw [hfixed, fderiv_directionalFDeriv_mixed_eq_iteratedFDeriv_two hf]
  unfold rotationHessianValue
  ring

/-- Rotation Hessians of C2 functions are continuous. -/
theorem continuous_rotationHessianValue
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f)
    (i j a b : Fin n) :
    Continuous (rotationHessianValue f i j a b) := by
  let g : (Fin n → ℝ) → ℝ := fun y ↦
    fderiv ℝ f y (coordinateRotationVector a b y)
  have hvab : ContDiff ℝ 1 (fun y ↦ coordinateRotationVector a b y) := by
    simpa only [← coordinateRotationCLM_apply] using
      (coordinateRotationCLM a b).contDiff
  have hvij : Continuous (fun y ↦ coordinateRotationVector i j y) := by
    simpa only [← coordinateRotationCLM_apply] using
      (coordinateRotationCLM i j).continuous
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (m := 1) (by norm_num)
  have hg : ContDiff ℝ 1 g := hdf.clm_apply hvab
  have hright : Continuous (fun x ↦
      fderiv ℝ g x (coordinateRotationVector i j x)) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply hvij
  apply hright.congr
  intro x
  exact fderiv_coordinateRotationValue_eq_rotationHessianValue
    hf i j a b x

/-- For polynomial evaluation the analytic rotation Hessian is exactly the
ordered pair of algebraic rotation derivatives. -/
theorem rotationHessianValue_mvPolynomial_eval
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (i j a b : Fin n)
    (x : Fin n → ℝ) :
    rotationHessianValue (fun y ↦ MvPolynomial.eval y P) i j a b x =
      MvPolynomial.eval x (rotationDeriv i j (rotationDeriv a b P)) := by
  let f : (Fin n → ℝ) → ℝ := fun y ↦ MvPolynomial.eval y P
  have hf : ContDiff ℝ 2 f := mvPolynomial_eval_contDiff P 2
  have hfield : (fun y ↦ fderiv ℝ f y (coordinateRotationVector a b y)) =
      (fun y ↦ MvPolynomial.eval y (rotationDeriv a b P)) := by
    funext y
    rw [(hasFDerivAt_mvPolynomial_eval P y).fderiv,
      mvPolynomialEvalFDeriv_eq_directionalDeriv]
    exact directionalDeriv_coordinateRotation P y a b
  calc
    rotationHessianValue f i j a b x =
        fderiv ℝ (fun y ↦ fderiv ℝ f y (coordinateRotationVector a b y)) x
          (coordinateRotationVector i j x) :=
      (fderiv_coordinateRotationValue_eq_rotationHessianValue hf i j a b x).symm
    _ = fderiv ℝ (fun y ↦ MvPolynomial.eval y (rotationDeriv a b P)) x
          (coordinateRotationVector i j x) := by rw [hfield]
    _ = directionalDeriv (rotationDeriv a b P) x
          (coordinateRotationVector i j x) := by
      rw [(hasFDerivAt_mvPolynomial_eval (rotationDeriv a b P) x).fderiv]
      exact mvPolynomialEvalFDeriv_eq_directionalDeriv _ _ _
    _ = MvPolynomial.eval x (rotationDeriv i j (rotationDeriv a b P)) :=
      directionalDeriv_coordinateRotation (rotationDeriv a b P) x i j

/-- The scaled first-jet estimate loses no inverse power because every
retained radius is at most one. -/
theorem finiteRetainedRootRegularity_fderiv_norm_le_jetBound
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (nu : Fin atoms.N)
    (x : Fin n → ℝ) :
    ‖fderiv ℝ (atoms.root nu) x‖ ≤ regular.jetBound := by
  have hr : 0 < atoms.radius nu := atoms.radius_pos nu
  have hscaled := regular.scaled_jet nu 1 (by omega) x
  rw [norm_iteratedFDeriv_one, pow_one] at hscaled
  have hcancel :
      ‖fderiv ℝ (atoms.root nu) x‖ ≤
        regular.jetBound * atoms.radius nu := by
    apply le_of_mul_le_mul_right _ hr
    calc
      ‖fderiv ℝ (atoms.root nu) x‖ * atoms.radius nu ≤
          regular.jetBound * atoms.radius nu ^ 2 := hscaled
      _ = (regular.jetBound * atoms.radius nu) * atoms.radius nu := by ring
  exact hcancel.trans
    (mul_le_of_le_one_right regular.jetBound_nonneg (atoms.radius_upper nu))

/-- The second scaled jet is uniformly bounded by the declared jet constant. -/
theorem finiteRetainedRootRegularity_iteratedFDeriv_two_norm_le_jetBound
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (nu : Fin atoms.N)
    (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ 2 (atoms.root nu) x‖ ≤ regular.jetBound := by
  have hrsq : 0 < atoms.radius nu ^ 2 := sq_pos_of_pos (atoms.radius_pos nu)
  apply le_of_mul_le_mul_right _ hrsq
  exact regular.scaled_jet nu 2 (by omega) x

/-- A retained atom has uniformly bounded rotation Hessian on the unit
ball.  The constant comes from two rotation-vector norms and the derivative
of the inner rotation field. -/
theorem finiteRetainedRootRegularity_abs_rotationHessianValue_le_eight
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    {atoms : FiniteRetainedRootData n C k F}
    (regular : FiniteRetainedRootRegularity atoms) (nu : Fin atoms.N)
    (i j a b : Fin n) (x : Fin n → ℝ) (hx : ‖x‖ ≤ 1) :
    |rotationHessianValue (atoms.root nu) i j a b x| ≤
      8 * regular.jetBound := by
  let vij := coordinateRotationVector i j x
  let vab := coordinateRotationVector a b x
  let corr := coordinateRotationVector a b vij
  have hvij : ‖vij‖ ≤ 2 := by
    exact (coordinateRotationVector_norm_le_two_mul i j x).trans (by nlinarith)
  have hvab : ‖vab‖ ≤ 2 := by
    exact (coordinateRotationVector_norm_le_two_mul a b x).trans (by nlinarith)
  have hcorr : ‖corr‖ ≤ 4 := by
    exact (coordinateRotationVector_norm_le_two_mul a b vij).trans (by nlinarith)
  have htwoNorm := finiteRetainedRootRegularity_iteratedFDeriv_two_norm_le_jetBound regular nu x
  have honeNorm := finiteRetainedRootRegularity_fderiv_norm_le_jetBound regular nu x
  have htwoApply :
      ‖iteratedFDeriv ℝ 2 (atoms.root nu) x ![vij, vab]‖ ≤
        4 * regular.jetBound := by
    calc
      ‖iteratedFDeriv ℝ 2 (atoms.root nu) x ![vij, vab]‖ ≤
          ‖iteratedFDeriv ℝ 2 (atoms.root nu) x‖ *
            ∏ q, ‖![vij, vab] q‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 2 (atoms.root nu) x‖ * (‖vij‖ * ‖vab‖) := by
        simp [Fin.prod_univ_succ]
      _ ≤ regular.jetBound * (2 * 2) := by gcongr; exact regular.jetBound_nonneg
      _ = 4 * regular.jetBound := by ring
  have honeApply :
      ‖fderiv ℝ (atoms.root nu) x corr‖ ≤ 4 * regular.jetBound := by
    calc
      ‖fderiv ℝ (atoms.root nu) x corr‖ ≤
          ‖fderiv ℝ (atoms.root nu) x‖ * ‖corr‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ regular.jetBound * 4 := by gcongr; exact regular.jetBound_nonneg
      _ = 4 * regular.jetBound := by ring
  rw [← Real.norm_eq_abs]
  change ‖iteratedFDeriv ℝ 2 (atoms.root nu) x ![vij, vab] +
    fderiv ℝ (atoms.root nu) x corr‖ ≤ 8 * regular.jetBound
  calc
    _ ≤ ‖iteratedFDeriv ℝ 2 (atoms.root nu) x ![vij, vab]‖ +
        ‖fderiv ℝ (atoms.root nu) x corr‖ := norm_add_le _ _
    _ ≤ 4 * regular.jetBound + 4 * regular.jetBound := add_le_add htwoApply honeApply
    _ = 8 * regular.jetBound := by ring

/-- A tangent derivative vanishes strictly outside a spherical support cap. -/
theorem tangent_fderiv_eq_zero_of_sphere_support_unit
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Differentiable ℝ f) (center : sphereSet n) (r : ℝ)
    (hsupp : ∀ y (hy : y ∈ sphereSet n), f y ≠ 0 →
      (⟨y, hy⟩ : sphereSet n) ∈ sphereChordalCap center r)
    (x u : Fin n → ℝ)
    (hx : ∑ q, x q ^ 2 = 1) (hu : ∑ q, u q ^ 2 = 1)
    (horth : ∑ q, u q * x q = 0)
    (hout : ¬ sphereChordalSq x center.1 ≤ r ^ 2) :
    fderiv ℝ f x u = 0 := by
  let gamma : ℝ → (Fin n → ℝ) := fun t q ↦
    t * u q + Real.sqrt (1 - t ^ 2) * x q
  have hgamma : HasDerivAt gamma u 0 := by
    simpa [gamma] using hasDerivAt_greatCirclePath_zero x u
  have hgamma0 : gamma 0 = x := by
    funext q
    simp [gamma]
  have hchord : Continuous (fun t ↦ sphereChordalSq (gamma t) center.1) := by
    unfold sphereChordalSq gamma
    fun_prop
  have hfar0 : r ^ 2 < sphereChordalSq (gamma 0) center.1 := by
    rw [hgamma0]
    exact lt_of_not_ge hout
  have hfar : ∀ᶠ t in nhds 0,
      r ^ 2 < sphereChordalSq (gamma t) center.1 :=
    (isOpen_lt continuous_const hchord).mem_nhds hfar0
  have hsmall : ∀ᶠ t in nhds 0, t ∈ Set.Ioo (-1 : ℝ) 1 :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hzero : (fun t ↦ f (gamma t)) =ᶠ[nhds 0] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [hfar, hsmall] with t htfar ht
    have hmem : gamma t ∈ sphereSet n :=
      sphereGreatCirclePoint_mem u x hu hx horth t ht.1.le ht.2.le
    by_contra hne
    exact (not_le_of_gt htfar) (hsupp (gamma t) hmem hne)
  have hcomp : HasDerivAt (fun t ↦ f (gamma t)) (fderiv ℝ f x u) 0 := by
    have hfo : HasFDerivAt f (fderiv ℝ f x) (gamma 0) := by
      simpa [hgamma0] using (hf x).hasFDerivAt
    exact hfo.comp_hasDerivAt 0 hgamma
  calc
    fderiv ℝ f x u = deriv (fun t ↦ f (gamma t)) 0 := hcomp.deriv.symm
    _ = deriv (fun _ ↦ (0 : ℝ)) 0 := hzero.deriv_eq
    _ = 0 := deriv_const 0 0

/-- The preceding support lemma for an arbitrary tangent vector. -/
theorem tangent_fderiv_eq_zero_of_sphere_support
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Differentiable ℝ f) (center : sphereSet n) (r : ℝ)
    (hsupp : ∀ y (hy : y ∈ sphereSet n), f y ≠ 0 →
      (⟨y, hy⟩ : sphereSet n) ∈ sphereChordalCap center r)
    (x v : Fin n → ℝ)
    (hx : ∑ q, x q ^ 2 = 1)
    (horth : ∑ q, v q * x q = 0)
    (hout : ¬ sphereChordalSq x center.1 ≤ r ^ 2) :
    fderiv ℝ f x v = 0 := by
  let q : ℝ := ∑ p, v p ^ 2
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun p _ ↦ sq_nonneg (v p)
  by_cases hq : q = 0
  · have hv : v = 0 := by
      funext p
      have hp : v p ^ 2 ≤ q :=
        Finset.single_le_sum (fun l _ ↦ sq_nonneg (v l)) (Finset.mem_univ p)
      rw [hq] at hp
      simp only [Pi.zero_apply]
      nlinarith [sq_nonneg (v p)]
    rw [hv]
    simp
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    let c : ℝ := Real.sqrt q
    let u : Fin n → ℝ := c⁻¹ • v
    have hcpos : 0 < c := Real.sqrt_pos.2 hqpos
    have hcne : c ≠ 0 := hcpos.ne'
    have hcu : c • u = v := by
      ext p
      simp [u, hcne]
    have hu : ∑ p, u p ^ 2 = 1 := by
      calc
        ∑ p, u p ^ 2 = c⁻¹ ^ 2 * q := by
          simp only [u, Pi.smul_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        _ = 1 := by
          rw [show q = c ^ 2 by exact (Real.sq_sqrt hq0).symm]
          field_simp
    have huorth : ∑ p, u p * x p = 0 := by
      calc
        ∑ p, u p * x p = c⁻¹ * ∑ p, v p * x p := by
          simp only [u, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        _ = 0 := by rw [horth, mul_zero]
    have hunit := tangent_fderiv_eq_zero_of_sphere_support_unit
      hf center r hsupp x u hx hu huorth hout
    rw [← hcu, map_smul, hunit, smul_zero]

/-- Coordinate-rotation vectors are tangent to every Euclidean sphere. -/
theorem coordinateRotationVector_orth {n : ℕ} (i j : Fin n)
    (x : Fin n → ℝ) :
    ∑ q, coordinateRotationVector i j x q * x q = 0 := by
  simp only [coordinateRotationVector, Pi.sub_apply, Pi.single_apply]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp
  ring

/-- A rotation Hessian inherits the spherical cap support of the original
function.  This is the tangent-support bridge needed for overlap counting. -/
theorem rotationHessianValue_eq_zero_of_sphere_support
    {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (center : sphereSet n) (r : ℝ)
    (hsupp : ∀ y (hy : y ∈ sphereSet n), f y ≠ 0 →
      (⟨y, hy⟩ : sphereSet n) ∈ sphereChordalCap center r)
    (i j a b : Fin n) (x : Fin n → ℝ)
    (hx : x ∈ sphereSet n)
    (hout : ¬ sphereChordalSq x center.1 ≤ r ^ 2) :
    rotationHessianValue f i j a b x = 0 := by
  let g : (Fin n → ℝ) → ℝ := fun y ↦
    fderiv ℝ f y (coordinateRotationVector a b y)
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdv : Differentiable ℝ (fun y ↦ coordinateRotationVector a b y) := by
    simpa only [← coordinateRotationCLM_apply] using
      (coordinateRotationCLM a b).differentiable
  have hg : Differentiable ℝ g := hdf.clm_apply hdv
  have hgsupp : ∀ y (hy : y ∈ sphereSet n), g y ≠ 0 →
      (⟨y, hy⟩ : sphereSet n) ∈ sphereChordalCap center r := by
    intro y hy hgne
    by_contra hnot
    apply hgne
    apply tangent_fderiv_eq_zero_of_sphere_support
      (hf.differentiable (by norm_num)) center r hsupp y
      (coordinateRotationVector a b y) (by
        simpa only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X,
          Set.mem_setOf_eq] using hy)
      (coordinateRotationVector_orth a b y)
    simpa only [sphereChordalCap, Set.mem_setOf_eq] using hnot
  rw [← fderiv_coordinateRotationValue_eq_rotationHessianValue hf]
  exact tangent_fderiv_eq_zero_of_sphere_support hg center r hgsupp x
    (coordinateRotationVector i j x) (by
      simpa only [sphereSet, sphereQuadratic, map_sum, map_pow, eval_X,
        Set.mem_setOf_eq] using hx)
    (coordinateRotationVector_orth i j x) hout

/-- The overlap budget gives a root-count-free square bound for the rotation
Hessians of all atoms whose supporting caps contain the evaluation point. -/
theorem FiniteControlledRootData.sum_rotationHessianValue_sq_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F) (i j a b : Fin n)
    (x : sphereSet n) :
    ∑ nu ∈ Finset.univ.filter (fun nu ↦
        sphereChordalSq x.1 (data.atoms.center nu).1 ≤
          data.atoms.radius nu ^ 2),
      rotationHessianValue (data.atoms.root nu) i j a b x.1 ^ 2 ≤
        16 * C := by
  let s : Finset (Fin data.atoms.N) := Finset.univ.filter (fun nu ↦
    sphereChordalSq x.1 (data.atoms.center nu).1 ≤
      data.atoms.radius nu ^ 2)
  have heach (nu : Fin data.atoms.N) :
      rotationHessianValue (data.atoms.root nu) i j a b x.1 ^ 2 ≤
        64 * data.regular.jetBound ^ 2 := by
    have habs := finiteRetainedRootRegularity_abs_rotationHessianValue_le_eight
      data.regular nu i j a b x.1 (norm_coe_sphereSet_le_one x)
    calc
      rotationHessianValue (data.atoms.root nu) i j a b x.1 ^ 2 =
          |rotationHessianValue (data.atoms.root nu) i j a b x.1| ^ 2 := by
        rw [sq_abs]
      _ ≤ (8 * data.regular.jetBound) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 64 * data.regular.jetBound ^ 2 := by ring
  have hcard : (s.card : ℝ) ≤ data.atoms.overlapBound := by
    exact_mod_cast data.atoms.cap_overlap_card x.1 x.2
  change ∑ nu ∈ s,
      rotationHessianValue (data.atoms.root nu) i j a b x.1 ^ 2 ≤ 16 * C
  calc
    _ ≤ ∑ _nu ∈ s, 64 * data.regular.jetBound ^ 2 := by
      exact Finset.sum_le_sum fun nu _hnu ↦ heach nu
    _ = (s.card : ℝ) * (64 * data.regular.jetBound ^ 2) := by
      simp
    _ ≤ (data.atoms.overlapBound : ℝ) *
        (64 * data.regular.jetBound ^ 2) := by
      exact mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = 64 * ((data.atoms.overlapBound : ℝ) *
        data.regular.jetBound ^ 2) := by ring
    _ ≤ 64 * (C / 4) := by
      exact mul_le_mul_of_nonneg_left data.overlap_jetBound_sq_le (by norm_num)
    _ = 16 * C := by ring

/-- The actual (unmasked) atom rotation Hessians satisfy the same root-count-free
square bound: tangential support makes every off-cap term vanish. -/
theorem FiniteControlledRootData.sum_all_rotationHessianValue_sq_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F) (i j a b : Fin n)
    (x : sphereSet n) :
    ∑ nu, rotationHessianValue (data.atoms.root nu) i j a b x.1 ^ 2 ≤
      16 * C := by
  rw [show (∑ nu, rotationHessianValue
        (data.atoms.root nu) i j a b x.1 ^ 2) =
      ∑ nu ∈ Finset.univ.filter (fun nu ↦
        sphereChordalSq x.1 (data.atoms.center nu).1 ≤
          data.atoms.radius nu ^ 2),
        rotationHessianValue (data.atoms.root nu) i j a b x.1 ^ 2 by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro nu _hnu
    by_cases hcap : sphereChordalSq x.1 (data.atoms.center nu).1 ≤
        data.atoms.radius nu ^ 2
    · simp [hcap]
    · have hz := rotationHessianValue_eq_zero_of_sphere_support
        ((data.regular.root_contDiff nu).of_le (by norm_num))
        (data.atoms.center nu) (data.atoms.radius nu)
        (data.atoms.supported nu) i j a b x.1 x.2 hcap
      simp [hcap, hz]]
  exact data.sum_rotationHessianValue_sq_le i j a b x

/-- Positivity of the normalized kernel transports the genuine all-root
Hessian square bound through the Boolean filter, still without a root-count
factor. -/
theorem FiniteControlledRootData.booleanFilteredRotationHessian_squareFunction_le
    {n : ℕ} (hn : 2 ≤ n) {C : ℝ} {k : ℕ}
    {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F) (i j a b : Fin n)
    (x : sphereSet n) :
    ∑ nu, (booleanFilteredFunctionValue (n + 3) k data.atoms.base
      (fun y ↦ rotationHessianValue (data.atoms.root nu) i j a b y.1)
      x.1) ^ 2 ≤ 144 * C := by
  let hessian : Fin data.atoms.N → sphereSet n → ℝ := fun nu y ↦
    rotationHessianValue (data.atoms.root nu) i j a b y.1
  have hhessian : ∀ nu, Continuous (hessian nu) := by
    intro nu
    exact (continuous_rotationHessianValue
      ((data.regular.root_contDiff nu).of_le (by norm_num)) i j a b).comp
        continuous_subtype_val
  have hcoeff : ∀ nu, ZonalKernelCoeffIntegrable (n + 3) k (hessian nu) := by
    intro nu
    exact zonalKernelCoeffIntegrable_of_continuous (by omega) (n + 3) k
      (hessian nu) (hhessian nu) (zonalKernelCoeffContinuous (n + 3) k)
  have hC : 0 ≤ C := by
    have hleft : 0 ≤ (data.atoms.overlapBound : ℝ) *
        data.regular.jetBound ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    nlinarith [data.overlap_jetBound_sq_le]
  have hfiltered := booleanFilteredFunction_squareFunction_le_nine
    hn (n + 3) k data.atoms.base hessian hhessian hcoeff (16 * C)
      (mul_nonneg (by norm_num) hC)
      (fun y ↦ data.sum_all_rotationHessianValue_sq_le i j a b y) x
  simpa only [hessian] using hfiltered.trans_eq (by ring)

/-- A total-family formulation of the same estimate, with the Hessian set to
zero off the atom cap.  This is often the most convenient square-function
input while the tangential support lemma is kept separate. -/
def FiniteControlledRootData.capMaskedRotationHessian
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F) (i j a b : Fin n)
    (nu : Fin data.atoms.N) (x : sphereSet n) : ℝ :=
  if sphereChordalSq x.1 (data.atoms.center nu).1 ≤
      data.atoms.radius nu ^ 2 then
    rotationHessianValue (data.atoms.root nu) i j a b x.1
  else 0

theorem FiniteControlledRootData.sum_capMaskedRotationHessian_sq_le
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin n) ℝ}
    (data : FiniteControlledRootData n C k F) (i j a b : Fin n)
    (x : sphereSet n) :
    ∑ nu, (data.capMaskedRotationHessian i j a b nu x) ^ 2 ≤ 16 * C := by
  rw [show (∑ nu, (data.capMaskedRotationHessian i j a b nu x) ^ 2) =
      ∑ nu ∈ Finset.univ.filter (fun nu ↦
        sphereChordalSq x.1 (data.atoms.center nu).1 ≤
          data.atoms.radius nu ^ 2),
        rotationHessianValue (data.atoms.root nu) i j a b x.1 ^ 2 by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro nu _hnu
    by_cases hcap : sphereChordalSq x.1 (data.atoms.center nu).1 ≤
        data.atoms.radius nu ^ 2 <;>
      simp [FiniteControlledRootData.capMaskedRotationHessian, hcap]]
  exact data.sum_rotationHessianValue_sq_le i j a b x

/-- The two algebraic circle rotations of a restricted controlled polynomial
are exactly its ambient analytic rotation Hessian at the scaled sphere point. -/
theorem FiniteControlledRootData.eval_two_circleRotationDeriv_eq_rotationHessianValue
    {n : ℕ} {C : ℝ} {k : ℕ} {F : MvPolynomial (Fin (2 * n + 1)) ℝ}
    (data : FiniteControlledRootData (2 * n + 1) C k F)
    (nu : Fin data.atoms.N) (i j : Fin n) (z : CubeCircleVar n → ℝ) :
    MvPolynomial.eval z
        (circleRotationDeriv i (circleRotationDeriv j
          (data.productCirclePolynomial nu))) =
      rotationHessianValue
        (fun y ↦ MvPolynomial.eval y (data.filter.polynomial nu))
        (cubeSphereFirst n i) (cubeSphereSecond n i)
        (cubeSphereFirst n j) (cubeSphereSecond n j)
        (productCircleSpherePoint n z) := by
  rw [FiniteControlledRootData.productCirclePolynomial,
    circleRotationDeriv_two_productCircleSubstitution,
    eval_productCircleSubstitution]
  exact (rotationHessianValue_mvPolynomial_eval
    (data.filter.polynomial nu)
    (cubeSphereFirst n i) (cubeSphereSecond n i)
    (cubeSphereFirst n j) (cubeSphereSecond n j)
    (productCircleSpherePoint n z)).symm

end QuarticConvergence
end OptimalConvergenceRates

end
