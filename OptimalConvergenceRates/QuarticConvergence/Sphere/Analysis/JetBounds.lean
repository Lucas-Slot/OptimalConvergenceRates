
/-
  OptimalConvergenceRates/QuarticConvergence/Sphere/Analysis/JetBounds.lean

  Nonnegative jets and the intrinsic fourth-order scale used by the
  scale-resolved atom construction.
-/
import OptimalConvergenceRates.QuarticConvergence.Sphere.Analysis.OneDimensionalTaylor
import OptimalConvergenceRates.QuarticConvergence.Sphere.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open Set

noncomputable section

namespace OptimalConvergenceRates
namespace QuarticConvergence

/-- A normalized compactly supported nonnegative `C⁶` function on Euclidean space. -/
structure NormalizedNonnegativeC6 {n : ℕ} (u : (Fin n → ℝ) → ℝ) : Prop where
  nonnegative : ∀ x, 0 ≤ u x
  contDiff : ContDiff ℝ 6 u
  compact_support : HasCompactSupport u
  iteratedFDeriv_le_one : ∀ j, j ≤ 6 → ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ 1

/-- A positive common bound on all derivatives through order six gives the normalized input used
by the Euclidean atom theorem after division by that bound. -/
def normalizedNonnegativeC6_of_bound {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ∀ x, 0 ≤ u x) (hsmooth : ContDiff ℝ 6 u) (hcompact : HasCompactSupport u)
    (M : ℝ) (hM : 0 < M)
    (hderiv : ∀ j, j ≤ 6 → ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ M) :
    NormalizedNonnegativeC6 (fun x ↦ M⁻¹ * u x) where
  nonnegative := by
    intro x
    exact mul_nonneg (inv_nonneg.mpr hM.le) (hu x)
  contDiff := hsmooth.const_smul M⁻¹
  compact_support := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      hcompact.smul_left (f := fun _ ↦ M⁻¹)
  iteratedFDeriv_le_one := by
    intro j hj x
    have hsmoothAt : ContDiffAt ℝ j u x :=
      (hsmooth.of_le (by exact_mod_cast hj)).contDiffAt
    change ‖iteratedFDeriv ℝ j (M⁻¹ • u) x‖ ≤ 1
    rw [iteratedFDeriv_const_smul_apply hsmoothAt, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hM.le)]
    calc
      M⁻¹ * ‖iteratedFDeriv ℝ j u x‖ ≤ M⁻¹ * M :=
        mul_le_mul_of_nonneg_left (hderiv j hj x) (inv_nonneg.mpr hM.le)
      _ = 1 := inv_mul_cancel₀ hM.ne'
/-- Contracting the spatial variables by a factor in `(0,1]` preserves normalized
nonnegativity, compact topological support, and all derivative bounds. -/
theorem NormalizedNonnegativeC6.comp_smul {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : NormalizedNonnegativeC6 u) {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho ≤ 1) :
    NormalizedNonnegativeC6 (fun x ↦ u (rho • x)) where
  nonnegative := fun x ↦ hu.nonnegative (rho • x)
  contDiff := hu.contDiff.comp (by fun_prop)
  compact_support := hu.compact_support.comp_smul hrho.ne'
  iteratedFDeriv_le_one := by
    intro j hj x
    let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
      rho • ContinuousLinearMap.id ℝ (Fin n → ℝ)
    have hcomp :
        iteratedFDeriv ℝ j (u ∘ L) x =
          (iteratedFDeriv ℝ j u (L x)).compContinuousLinearMap (fun _ ↦ L) :=
      L.iteratedFDeriv_comp_right hu.contDiff x (by exact_mod_cast hj)
    change ‖iteratedFDeriv ℝ j (u ∘ L) x‖ ≤ 1
    rw [hcomp]
    have hL : ‖L‖ ≤ rho := by
      calc
        ‖L‖ ≤ ‖rho‖ * ‖ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ :=
          norm_smul_le rho (ContinuousLinearMap.id ℝ (Fin n → ℝ))
        _ ≤ rho * 1 := by
          rw [Real.norm_of_nonneg hrho.le]
          gcongr
          exact ContinuousLinearMap.norm_id_le
        _ = rho := mul_one rho
    calc
      ‖(iteratedFDeriv ℝ j u (L x)).compContinuousLinearMap (fun _ ↦ L)‖ ≤
          ‖iteratedFDeriv ℝ j u (L x)‖ * ∏ _ : Fin j, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ 1 * ∏ _ : Fin j, ‖L‖ := by
        gcongr
        exact hu.iteratedFDeriv_le_one j hj (L x)
      _ ≤ 1 * ∏ _ : Fin j, rho := by
        gcongr
      _ = rho ^ j := by simp
      _ ≤ 1 := pow_le_one₀ hrho.le hrho_one
/-- The intrinsic scale `max {u^(1/4), ‖D²u‖^(1/2)}`, written with nested square roots. -/
def nonnegativeJetScale {n : ℕ} (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  max (Real.sqrt (Real.sqrt (u x))) (Real.sqrt ‖iteratedFDeriv ℝ 2 u x‖)

/-- The intrinsic scale of a normalized input is at most one.  This supplies the bounded-radius
hypothesis needed by Euclidean ball-selection theorems. -/
theorem nonnegativeJetScale_le_one {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : NormalizedNonnegativeC6 u) (x : Fin n → ℝ) :
    nonnegativeJetScale u x ≤ 1 := by
  have hu1 : u x ≤ 1 := by
    have h := hu.iteratedFDeriv_le_one 0 (by norm_num) x
    simpa [abs_of_nonneg (hu.nonnegative x)] using h
  have hq : Real.sqrt (Real.sqrt (u x)) ≤ 1 := by
    rw [Real.sqrt_le_one, Real.sqrt_le_one]
    exact hu1
  have hH : Real.sqrt ‖iteratedFDeriv ℝ 2 u x‖ ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hu.iteratedFDeriv_le_one 2 (by norm_num) x
  exact max_le hq hH

/-- Restricting a normalized function to a line in a vector of norm at most
one preserves the unit fourth-derivative bound. This is the analytic bridge
from the repository's Fréchet-derivative normalization to the scalar Taylor
lemmas. -/
theorem norm_iteratedDeriv_line_le_one {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : NormalizedNonnegativeC6 u) (x v : Fin n → ℝ) (hv : ‖v‖ ≤ 1) (t : ℝ) :
    ‖iteratedDeriv 4 (fun s : ℝ => u (x + s • v)) t‖ ≤ 1 := by
  let L : ℝ →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.toSpanSingleton ℝ v
  let shifted : (Fin n → ℝ) → ℝ := fun z => u (x + z)
  have hshift : ContDiff ℝ 6 shifted := by
    exact hu.contDiff.comp (contDiff_const.add contDiff_id)
  have hcomp :
      iteratedFDeriv ℝ 4 (shifted ∘ L) t =
        (iteratedFDeriv ℝ 4 shifted (L t)).compContinuousLinearMap (fun _ => L) :=
    L.iteratedFDeriv_comp_right hshift t (by norm_num)
  have htranslation :
      iteratedFDeriv ℝ 4 shifted (L t) = iteratedFDeriv ℝ 4 u (x + L t) := by
    simpa [shifted] using iteratedFDeriv_comp_add_left (𝕜 := ℝ) 4 x (L t)
  have hnormL : ‖L‖ = ‖v‖ := by simp [L]
  have hcompNorm : ‖iteratedFDeriv ℝ 4 (shifted ∘ L) t‖ ≤ 1 := by
    rw [hcomp, htranslation]
    calc
      ‖(iteratedFDeriv ℝ 4 u (x + L t)).compContinuousLinearMap (fun _ => L)‖
          ≤ ‖iteratedFDeriv ℝ 4 u (x + L t)‖ * ∏ _ : Fin 4, ‖L‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ 1 * ∏ _ : Fin 4, ‖L‖ := by
        gcongr
        exact hu.iteratedFDeriv_le_one 4 (by norm_num) (x + L t)
      _ ≤ 1 := by
        simpa [hnormL] using (pow_le_one₀ (norm_nonneg v) hv : ‖v‖ ^ 4 ≤ 1)
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  convert hcompNorm using 2

/-- The scalar Taylor coefficient of an affine line restriction is the
corresponding multivariate Fréchet derivative evaluated repeatedly on the
line direction. -/
theorem iteratedDeriv_line_zero {n k : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 6 u) (hk : k ≤ 6) (x v : Fin n → ℝ) :
    iteratedDeriv k (fun t : ℝ => u (x + t • v)) 0 =
      iteratedFDeriv ℝ k u x (fun _ => v) := by
  let L : ℝ →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.toSpanSingleton ℝ v
  let shifted : (Fin n → ℝ) → ℝ := fun z => u (x + z)
  have hshift : ContDiff ℝ 6 shifted := hu.comp (contDiff_const.add contDiff_id)
  have hcomp :
      iteratedFDeriv ℝ k (shifted ∘ L) 0 =
        (iteratedFDeriv ℝ k shifted (L 0)).compContinuousLinearMap (fun _ => L) :=
    L.iteratedFDeriv_comp_right hshift 0 (by exact_mod_cast hk)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ k (shifted ∘ L) 0 (fun _ => 1) = _
  rw [hcomp]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [show iteratedFDeriv ℝ k shifted (L 0) = iteratedFDeriv ℝ k u (x + L 0) by
    simpa [shifted] using iteratedFDeriv_comp_add_left (𝕜 := ℝ) k x (L 0)]
  simp [L]

/-- Nonnegativity and the normalized fourth derivative give the quartic
majorant whose coefficients are the directional Fréchet derivatives at the
base point. -/
theorem nonnegative_line_quartic_majorant {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : NormalizedNonnegativeC6 u) (x v : Fin n → ℝ) (hv : ‖v‖ ≤ 1) :
    ∀ t : ℝ,
      0 ≤ u x + iteratedFDeriv ℝ 1 u x (fun _ => v) * t +
        iteratedFDeriv ℝ 2 u x (fun _ => v) * t ^ 2 / 2 +
        iteratedFDeriv ℝ 3 u x (fun _ => v) * t ^ 3 / 6 + t ^ 4 / 6 := by
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · let T : ℝ := -t
    let w : Fin n → ℝ := -v
    have hT : 0 < T := by dsimp [T]; linarith
    have hw : ‖w‖ ≤ 1 := by simpa [w] using hv
    let f : ℝ → ℝ := fun s => u (x + s • w)
    have hf : ContDiff ℝ 4 f := by
      dsimp [f]
      apply (hu.contDiff.comp ?_).of_le (by norm_num)
      fun_prop
    have hrem := abs_sub_explicit_taylor_three_le hT hf
      (fun s => norm_iteratedDeriv_line_le_one hu x w hw s)
    have hd : deriv f 0 = iteratedFDeriv ℝ 1 u x (fun _ => w) := by
      rw [← iteratedDeriv_one]
      exact iteratedDeriv_line_zero hu.contDiff (by norm_num) x w
    have htwo : iteratedDeriv 2 f 0 = iteratedFDeriv ℝ 2 u x (fun _ => w) :=
      iteratedDeriv_line_zero hu.contDiff (by norm_num) x w
    have hthree : iteratedDeriv 3 f 0 = iteratedFDeriv ℝ 3 u x (fun _ => w) :=
      iteratedDeriv_line_zero hu.contDiff (by norm_num) x w
    rw [hd, htwo, hthree] at hrem
    have hmaj := quartic_majorant_nonnegative (f := f)
      (hu.nonnegative (x + T • w)) hrem
    have hneg2 : iteratedFDeriv ℝ 2 u x (fun _ => -v) =
        iteratedFDeriv ℝ 2 u x (fun _ => v) := by
      rw [show (fun _ : Fin 2 => -v) = fun _ => (-1 : ℝ) • v by funext; simp]
      rw [(iteratedFDeriv ℝ 2 u x).map_smul_univ]
      norm_num
    have hneg3 : iteratedFDeriv ℝ 3 u x (fun _ => -v) =
        -iteratedFDeriv ℝ 3 u x (fun _ => v) := by
      rw [show (fun _ : Fin 3 => -v) = fun _ => (-1 : ℝ) • v by funext; simp]
      rw [(iteratedFDeriv ℝ 3 u x).map_smul_univ]
      norm_num
    dsimp [f] at hmaj
    have hmajFinal :
        0 ≤ u x + fderiv ℝ u x v * t +
          iteratedFDeriv ℝ 2 u x (fun _ => v) * t ^ 2 / 2 +
          iteratedFDeriv ℝ 3 u x (fun _ => v) * t ^ 3 / 6 + t ^ 4 / 6 := by
      have hmajNeg :
          0 ≤ u x + fderiv ℝ u x v * t +
            iteratedFDeriv ℝ 2 u x (fun _ => v) * t ^ 2 / 2 +
            -(iteratedFDeriv ℝ 3 u x (fun _ => v) * (-t) ^ 3) / 6 +
            (-t) ^ 4 / 6 := by
        simpa [T, w, hneg2, hneg3] using hmaj
      convert hmajNeg using 1; ring
    rw [iteratedFDeriv_one_apply]
    exact hmajFinal
  · simpa using hu.nonnegative x
  · let f : ℝ → ℝ := fun s => u (x + s • v)
    have hf : ContDiff ℝ 4 f := by
      dsimp [f]
      apply (hu.contDiff.comp ?_).of_le (by norm_num)
      fun_prop
    have hrem := abs_sub_explicit_taylor_three_le ht hf
      (fun s => norm_iteratedDeriv_line_le_one hu x v hv s)
    have hd : deriv f 0 = iteratedFDeriv ℝ 1 u x (fun _ => v) := by
      rw [← iteratedDeriv_one]
      exact iteratedDeriv_line_zero hu.contDiff (by norm_num) x v
    have htwo : iteratedDeriv 2 f 0 = iteratedFDeriv ℝ 2 u x (fun _ => v) :=
      iteratedDeriv_line_zero hu.contDiff (by norm_num) x v
    have hthree : iteratedDeriv 3 f 0 = iteratedFDeriv ℝ 3 u x (fun _ => v) :=
      iteratedDeriv_line_zero hu.contDiff (by norm_num) x v
    rw [hd, htwo, hthree] at hrem
    have hmaj := quartic_majorant_nonnegative (f := f)
      (hu.nonnegative (x + t • v)) hrem
    simpa [f] using hmaj

/-- The intrinsic jet scale is nonnegative. -/
theorem nonnegativeJetScale_nonneg {n : ℕ} (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    0 ≤ nonnegativeJetScale u x := by
  exact (Real.sqrt_nonneg _).trans (le_max_left _ _)

/-- The fourth-root contribution is bounded by the intrinsic scale. -/
theorem sqrt_sqrt_le_nonnegativeJetScale {n : ℕ} (u : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : Real.sqrt (Real.sqrt (u x)) ≤ nonnegativeJetScale u x := by
  exact le_max_left _ _

/-- The Hessian contribution is bounded by the intrinsic scale. -/
theorem sqrt_iteratedFDeriv_two_le_nonnegativeJetScale {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    Real.sqrt ‖iteratedFDeriv ℝ 2 u x‖ ≤ nonnegativeJetScale u x := by
  exact le_max_right _ _

/-- The value term is at most the fourth power of the intrinsic scale. -/
theorem value_le_nonnegativeJetScale_pow_four {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u) (x : Fin n → ℝ) :
    u x ≤ nonnegativeJetScale u x ^ 4 := by
  have ha0 : 0 ≤ u x := hu.nonnegative x
  have hsqrta0 : 0 ≤ Real.sqrt (u x) := Real.sqrt_nonneg _
  have hq2 : (Real.sqrt (Real.sqrt (u x))) ^ 2 = Real.sqrt (u x) :=
    Real.sq_sqrt hsqrta0
  have hsqrta2 : (Real.sqrt (u x)) ^ 2 = u x := Real.sq_sqrt ha0
  calc
    u x = (Real.sqrt (Real.sqrt (u x))) ^ 4 := by nlinarith
    _ ≤ nonnegativeJetScale u x ^ 4 := pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (sqrt_sqrt_le_nonnegativeJetScale u x) 4

/-- The Hessian norm is at most the square of the intrinsic scale. -/
theorem norm_iteratedFDeriv_two_le_nonnegativeJetScale_sq {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ 2 u x‖ ≤ nonnegativeJetScale u x ^ 2 := by
  calc
    ‖iteratedFDeriv ℝ 2 u x‖ =
        (Real.sqrt ‖iteratedFDeriv ℝ 2 u x‖) ^ 2 := by
          rw [Real.sq_sqrt (norm_nonneg _)]
    _ ≤ nonnegativeJetScale u x ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (sqrt_iteratedFDeriv_two_le_nonnegativeJetScale u x) 2

/-- The scalar two-scale estimate already controls every diagonal value of
the third derivative. The remaining third-derivative leaf is precisely the
polarization from this diagonal estimate to the multilinear operator norm. -/
theorem third_derivative_diagonal_bound {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : NormalizedNonnegativeC6 u) (x v : Fin n → ℝ) (hv : ‖v‖ ≤ 1) :
    |iteratedFDeriv ℝ 3 u x (fun _ => v)| ≤ 9 * nonnegativeJetScale u x := by
  let R := nonnegativeJetScale u x
  have hpoly := nonnegative_line_quartic_majorant hu x v hv
  have hcUpper : |iteratedFDeriv ℝ 2 u x (fun _ => v)| ≤ R ^ 2 := by
    rw [← Real.norm_eq_abs]
    calc
      ‖iteratedFDeriv ℝ 2 u x (fun _ => v)‖
          ≤ ‖iteratedFDeriv ℝ 2 u x‖ * ∏ _ : Fin 2, ‖v‖ :=
            (iteratedFDeriv ℝ 2 u x).le_opNorm _
      _ ≤ R ^ 2 * ∏ _ : Fin 2, ‖v‖ := by
        gcongr
        exact norm_iteratedFDeriv_two_le_nonnegativeJetScale_sq u x
      _ ≤ R ^ 2 := by
        have hvpow : ‖v‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg v) hv
        simpa using mul_le_mul_of_nonneg_left hvpow (sq_nonneg R)
  exact cubic_coefficient_bound_of_quartic_nonnegative_of_nonneg
    (nonnegativeJetScale_nonneg u x) (value_le_nonnegativeJetScale_pow_four hu x)
    hcUpper hpoly

/-- The three scale-sensitive nonnegative-jet estimates needed by the cover and split. -/
structure NonnegativeJetControl {n : ℕ} (u : (Fin n → ℝ) → ℝ) (C : ℝ) : Prop where
  constant_nonneg : 0 ≤ C
  first : ∀ x,
    ‖iteratedFDeriv ℝ 1 u x‖ ≤
      C * nonnegativeJetScale u x * Real.sqrt (u x)
  third : ∀ x, ‖iteratedFDeriv ℝ 3 u x‖ ≤ C * nonnegativeJetScale u x
  hessian_lower : ∀ x v,
    -(C * Real.sqrt (u x) * ‖v‖ ^ 2) ≤
      fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v

/-- Uniform nonnegative jet control in a fixed Euclidean dimension. -/
def HasUniformNonnegativeJetBounds (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ u : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 u →
      NonnegativeJetControl u C

/-- The third Fréchet derivative is symmetric in its first two coordinates. -/
theorem iteratedFDeriv_three_swap_zero_one {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 6 u) (x a b c : Fin n → ℝ) :
    iteratedFDeriv ℝ 3 u x ![a, b, c] = iteratedFDeriv ℝ 3 u x ![b, a, c] := by
  have hfd : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (m := 2) (by norm_num)
  have hs : IsSymmSndFDerivAt ℝ (fderiv ℝ u) x :=
    hfd.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hsval := hs.iteratedFDeriv_cons (v := a) (w := b)
  have happ := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L c) hsval
  simpa [iteratedFDeriv_succ_apply_right] using happ

/-- The third Fréchet derivative is symmetric in its final two coordinates. -/
theorem iteratedFDeriv_three_swap_one_two {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 6 u) (x a b c : Fin n → ℝ) :
    iteratedFDeriv ℝ 3 u x ![a, b, c] = iteratedFDeriv ℝ 3 u x ![a, c, b] := by
  have hB : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 u) x :=
    (hu.differentiable_iteratedFDeriv (by norm_num)).differentiableAt
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hfun :
      (fun y => iteratedFDeriv ℝ 2 u y ![b, c]) =
        (fun y => iteratedFDeriv ℝ 2 u y ![c, b]) := by
    funext y
    have hs : IsSymmSndFDerivAt ℝ u y :=
      hu2.contDiffAt.isSymmSndFDerivAt (by norm_num)
    exact hs.iteratedFDeriv_cons
  have htailbc : Fin.tail ![a, b, c] = ![b, c] := by
    ext i
    fin_cases i <;> simp
  have htailcb : Fin.tail ![a, c, b] = ![c, b] := by
    ext i
    fin_cases i <;> simp
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, htailbc, htailcb]
  simp only [Matrix.cons_val_zero]
  rw [← fderiv_continuousMultilinear_apply_const_apply hB ![b, c] a]
  rw [hfun]
  rw [fderiv_continuousMultilinear_apply_const_apply hB ![c, b] a]

/-- Four diagonal values recover a symmetric trilinear value. -/
theorem cubic_polarization_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E [×3]→L[ℝ] ℝ) (hs01 : ∀ a b c, T ![a, b, c] = T ![b, a, c])
    (hs12 : ∀ a b c, T ![a, b, c] = T ![a, c, b]) (a b c : E) :
    24 * T ![a, b, c] =
      T (fun _ => a + b + c) - T (fun _ => a + b - c) -
        T (fun _ => a - b + c) - T (fun _ => -a + b + c) := by
  have hadd0 (p q r s : E) :
      T ![p + q, r, s] = T ![p, r, s] + T ![q, r, s] := by
    change T.curryLeft (p + q) ![r, s] =
      T.curryLeft p ![r, s] + T.curryLeft q ![r, s]
    rw [map_add]
    rfl
  have hadd1 (p q r s : E) :
      T ![p, q + r, s] = T ![p, q, s] + T ![p, r, s] := by
    change (T.curryLeft p).curryLeft (q + r) ![s] =
      (T.curryLeft p).curryLeft q ![s] + (T.curryLeft p).curryLeft r ![s]
    rw [map_add]
    rfl
  have hadd2 (p q r s : E) :
      T ![p, q, r + s] = T ![p, q, r] + T ![p, q, s] := by
    rw [show ![p, q, r + s] = Function.update ![p, q, r] 2 (r + s) by
      ext i
      fin_cases i <;> simp]
    rw [T.map_update_add]
    congr 1 <;> apply congrArg T <;> ext i <;> fin_cases i <;> simp
  have hneg0 (p q r : E) : T ![-p, q, r] = -T ![p, q, r] := by
    change T.curryLeft (-p) ![q, r] = -T.curryLeft p ![q, r]
    rw [map_neg]
    rfl
  have hneg1 (p q r : E) : T ![p, -q, r] = -T ![p, q, r] := by
    change (T.curryLeft p).curryLeft (-q) ![r] =
      -(T.curryLeft p).curryLeft q ![r]
    rw [map_neg]
    rfl
  have hneg2 (p q r : E) : T ![p, q, -r] = -T ![p, q, r] := by
    have h := T.map_update_smul ![p, q, r] 2 (-1 : ℝ) r
    rw [show Function.update ![p, q, r] 2 ((-1 : ℝ) • r) = ![p, q, -r] by
      ext i
      fin_cases i <;> simp] at h
    rw [show Function.update ![p, q, r] 2 r = ![p, q, r] by
      ext i
      fin_cases i <;> simp] at h
    simpa using h
  have hconst (v : E) : (fun _ : Fin 3 => v) = ![v, v, v] := by
    ext i
    fin_cases i <;> rfl
  rw [hconst (a + b + c), hconst (a + b - c), hconst (a - b + c),
    hconst (-a + b + c)]
  simp only [sub_eq_add_neg, hadd0, hadd1, hadd2, hneg0, hneg1, hneg2]
  simp only [hs01, hs12]
  ring

/-- Homogeneous form of the diagonal third-derivative estimate. -/
theorem third_derivative_diagonal_bound_homogeneous {n : ℕ}
    {u : (Fin n → ℝ) → ℝ} (hu : NormalizedNonnegativeC6 u)
    (x v : Fin n → ℝ) :
    |iteratedFDeriv ℝ 3 u x (fun _ => v)| ≤
      ‖v‖ ^ 3 * (9 * nonnegativeJetScale u x) := by
  let w : Fin n → ℝ := NormedSpace.normalize v
  have hw : ‖w‖ ≤ 1 := by
    by_cases hv : v = 0
    · subst v
      simp [w]
    · exact (NormedSpace.norm_normalize hv).le
  have hunit := third_derivative_diagonal_bound hu x w hw
  have hscale : iteratedFDeriv ℝ 3 u x (fun _ => v) =
      ‖v‖ ^ 3 * iteratedFDeriv ℝ 3 u x (fun _ => w) := by
    rw [show (fun _ : Fin 3 => v) = fun i => ‖v‖ • (fun _ : Fin 3 => w) i by
      funext i
      exact (NormedSpace.norm_smul_normalize v).symm]
    rw [(iteratedFDeriv ℝ 3 u x).map_smul_univ]
    simp [smul_eq_mul]
  rw [hscale, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg v) 3)]
  exact mul_le_mul_of_nonneg_left hunit (pow_nonneg (norm_nonneg v) 3)

/-- The sharp first-derivative estimate obtained from one-dimensional nonnegativity. -/
theorem nonnegative_first_derivative_bound {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 u → ∀ x,
        ‖iteratedFDeriv ℝ 1 u x‖ ≤
          C * nonnegativeJetScale u x * Real.sqrt (u x) := by
  refine ⟨4, by norm_num, ?_⟩
  intro u hu x
  let R := nonnegativeJetScale u x
  have hR0 : 0 ≤ R := nonnegativeJetScale_nonneg u x
  have ha0 : 0 ≤ u x := hu.nonnegative x
  have hsqrta0 : 0 ≤ Real.sqrt (u x) := Real.sqrt_nonneg _
  have hq2 : (Real.sqrt (Real.sqrt (u x))) ^ 2 = Real.sqrt (u x) :=
    Real.sq_sqrt hsqrta0
  have hsqrta2 : (Real.sqrt (u x)) ^ 2 = u x := Real.sq_sqrt ha0
  have hqR : Real.sqrt (Real.sqrt (u x)) ≤ R :=
    sqrt_sqrt_le_nonnegativeJetScale u x
  have haUpper : u x ≤ R ^ 4 := by
    calc
      u x = (Real.sqrt (Real.sqrt (u x))) ^ 4 := by nlinarith
      _ ≤ R ^ 4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hqR 4
  have hsR : Real.sqrt ‖iteratedFDeriv ℝ 2 u x‖ ≤ R :=
    sqrt_iteratedFDeriv_two_le_nonnegativeJetScale u x
  have hD2Upper : ‖iteratedFDeriv ℝ 2 u x‖ ≤ R ^ 2 := by
    calc
      ‖iteratedFDeriv ℝ 2 u x‖ =
          (Real.sqrt ‖iteratedFDeriv ℝ 2 u x‖) ^ 2 := by
            rw [Real.sq_sqrt (norm_nonneg _)]
      _ ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsR 2
  rw [norm_iteratedFDeriv_one]
  change ‖fderiv ℝ u x‖ ≤ 4 * R * Real.sqrt (u x)
  apply (fderiv ℝ u x).opNorm_le_bound (by positivity)
  intro v
  by_cases hvzero : v = 0
  · subst v
    simp
  · let w : Fin n → ℝ := NormedSpace.normalize v
    have hunit : ‖w‖ = 1 := NormedSpace.norm_normalize hvzero
    have hpoly := nonnegative_line_quartic_majorant hu x w hunit.le
    have hcUpper : |iteratedFDeriv ℝ 2 u x (fun _ => w)| ≤ R ^ 2 := by
      rw [← Real.norm_eq_abs]
      calc
        ‖iteratedFDeriv ℝ 2 u x (fun _ => w)‖
            ≤ ‖iteratedFDeriv ℝ 2 u x‖ * ∏ _ : Fin 2, ‖w‖ :=
              (iteratedFDeriv ℝ 2 u x).le_opNorm _
        _ ≤ R ^ 2 := by simp [hunit, hD2Upper]
    have hbunit : |iteratedFDeriv ℝ 1 u x (fun _ => w)| ≤
        4 * R * Real.sqrt (u x) := by
      rcases ha0.eq_or_lt with haeq | hapos
      · have hbzero : iteratedFDeriv ℝ 1 u x (fun _ => w) = 0 :=
          linear_coefficient_eq_zero_of_quartic_nonnegative (by
            intro t
            have hux : u x = 0 := haeq.symm
            simpa [hux] using hpoly t)
        have hux : u x = 0 := haeq.symm
        rw [hbzero, hux]
        norm_num
      · exact linear_coefficient_refined_bound_of_quartic_nonnegative hapos
          (lt_of_lt_of_le (Real.sqrt_pos.2 (Real.sqrt_pos.2 hapos)) hqR)
          haUpper hcUpper hpoly
    have hfw : ‖fderiv ℝ u x w‖ ≤ 4 * R * Real.sqrt (u x) := by
      simpa [Real.norm_eq_abs] using hbunit
    calc
      ‖fderiv ℝ u x v‖ = ‖v‖ * ‖fderiv ℝ u x w‖ := by
        conv_lhs => rw [← NormedSpace.norm_smul_normalize v]
        rw [map_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
      _ ≤ ‖v‖ * (4 * R * Real.sqrt (u x)) :=
        mul_le_mul_of_nonneg_left hfw (norm_nonneg v)
      _ = (4 * R * Real.sqrt (u x)) * ‖v‖ := by ring

/-- The third-derivative estimate obtained by restricting to lines and polarizing. -/
theorem nonnegative_third_derivative_bound {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 u → ∀ x,
        ‖iteratedFDeriv ℝ 3 u x‖ ≤ C * nonnegativeJetScale u x := by
  refine ⟨81, by norm_num, ?_⟩
  intro u hu x
  let T := iteratedFDeriv ℝ 3 u x
  let R := nonnegativeJetScale u x
  have hR : 0 ≤ R := nonnegativeJetScale_nonneg u x
  apply T.opNorm_le_bound (by positivity)
  intro m
  let w : Fin 3 → (Fin n → ℝ) := fun i => NormedSpace.normalize (m i)
  have hw (i : Fin 3) : ‖w i‖ ≤ 1 := by
    by_cases hi : m i = 0
    · simp [w, hi]
    · exact (NormedSpace.norm_normalize hi).le
  let a := w 0
  let b := w 1
  let c := w 2
  have ha : ‖a‖ ≤ 1 := hw 0
  have hb : ‖b‖ ≤ 1 := hw 1
  have hc : ‖c‖ ≤ 1 := hw 2
  have hspp : ‖a + b + c‖ ≤ 3 := by
    calc
      ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
        (norm_add_le (a + b) c).trans (by linarith [norm_add_le a b])
      _ ≤ 3 := by linarith
  have hspm : ‖a + b - c‖ ≤ 3 := by
    calc
      ‖a + b - c‖ ≤ ‖a + b‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_add_le a b]
      _ ≤ 3 := by linarith
  have hsmp : ‖a - b + c‖ ≤ 3 := by
    calc
      ‖a - b + c‖ ≤ ‖a - b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith [norm_sub_le a b]
      _ ≤ 3 := by linarith
  have hmpp : ‖-a + b + c‖ ≤ 3 := by
    calc
      ‖-a + b + c‖ ≤ ‖-a + b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ ‖-a‖ + ‖b‖ + ‖c‖ := by linarith [norm_add_le (-a) b]
      _ = ‖a‖ + ‖b‖ + ‖c‖ := by rw [norm_neg]
      _ ≤ 3 := by linarith
  have hdiag (z : Fin n → ℝ) (hz : ‖z‖ ≤ 3) :
      |T (fun _ => z)| ≤ 243 * R := by
    have hp : ‖z‖ ^ 3 ≤ (3 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg z) hz 3
    calc
      |T (fun _ => z)| ≤ ‖z‖ ^ 3 * (9 * R) := by
        simpa [T, R] using third_derivative_diagonal_bound_homogeneous hu x z
      _ ≤ (3 : ℝ) ^ 3 * (9 * R) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = 243 * R := by ring
  have hid := cubic_polarization_identity T
    (fun p q r => iteratedFDeriv_three_swap_zero_one hu.contDiff x p q r)
    (fun p q r => iteratedFDeriv_three_swap_one_two hu.contDiff x p q r) a b c
  have h24 : |24 * T ![a, b, c]| ≤ 972 * R := by
    rw [hid]
    calc
      |T (fun _ => a + b + c) - T (fun _ => a + b - c) -
          T (fun _ => a - b + c) - T (fun _ => -a + b + c)|
          ≤ |T (fun _ => a + b + c) - T (fun _ => a + b - c) -
              T (fun _ => a - b + c)| + |T (fun _ => -a + b + c)| := abs_sub _ _
      _ ≤ (|T (fun _ => a + b + c) - T (fun _ => a + b - c)| +
              |T (fun _ => a - b + c)|) + |T (fun _ => -a + b + c)| := by
            gcongr
            exact abs_sub _ _
      _ ≤ ((|T (fun _ => a + b + c)| + |T (fun _ => a + b - c)|) +
              |T (fun _ => a - b + c)|) + |T (fun _ => -a + b + c)| := by
            gcongr
            exact abs_sub _ _
      _ ≤ ((243 * R + 243 * R) + 243 * R) + 243 * R := by
            gcongr
            exacts [hdiag _ hspp, hdiag _ hspm, hdiag _ hsmp, hdiag _ hmpp]
      _ = 972 * R := by ring
  have habc : |T ![a, b, c]| ≤ 81 * R := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24)] at h24
    linarith
  have hwvec : w = ![a, b, c] := by
    ext i
    fin_cases i <;> rfl
  have hTw : ‖T w‖ ≤ 81 * R := by
    rw [hwvec, Real.norm_eq_abs]
    exact habc
  have hmrep : m = fun i => ‖m i‖ • w i := by
    funext i
    exact (NormedSpace.norm_smul_normalize (m i)).symm
  have hmap := T.map_smul_univ (fun i => ‖m i‖) w
  rw [← hmrep] at hmap
  rw [hmap, norm_smul]
  rw [Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)]
  calc
    (∏ i, ‖m i‖) * ‖T w‖ ≤ (∏ i, ‖m i‖) * (81 * R) :=
      mul_le_mul_of_nonneg_left hTw (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = 81 * R * ∏ i, ‖m i‖ := by ring

/-- The lower Hessian estimate obtained from the even one-dimensional Taylor bound. -/
theorem nonnegative_hessian_lower_bound {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : (Fin n → ℝ) → ℝ, NormalizedNonnegativeC6 u → ∀ x v,
        -(C * Real.sqrt (u x) * ‖v‖ ^ 2) ≤
          fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v := by
  refine ⟨2, by norm_num, ?_⟩
  intro u hu x v
  by_cases hvzero : v = 0
  · subst v
    simp
  · let w : Fin n → ℝ := NormedSpace.normalize v
    have hunit : ‖w‖ = 1 := by
      exact NormedSpace.norm_normalize hvzero
    have hpoly := nonnegative_line_quartic_majorant hu x w hunit.le
    have hcunit : -(2 * Real.sqrt (u x)) ≤
        iteratedFDeriv ℝ 2 u x (fun _ => w) :=
      quadratic_coefficient_lower_of_even_quartic_nonnegative (hu.nonnegative x)
        (even_quartic_nonnegative hpoly)
    have hscale : iteratedFDeriv ℝ 2 u x (fun _ => v) =
        ‖v‖ ^ 2 * iteratedFDeriv ℝ 2 u x (fun _ => w) := by
      rw [show (fun _ : Fin 2 => v) = fun _ => ‖v‖ • w by
        funext i
        exact (NormedSpace.norm_smul_normalize v).symm]
      rw [(iteratedFDeriv ℝ 2 u x).map_smul_univ]
      simp [smul_eq_mul]
    have hscaled := mul_le_mul_of_nonneg_left hcunit (sq_nonneg ‖v‖)
    have hhess : fderiv ℝ (fun y => fderiv ℝ u y v) x v =
        iteratedFDeriv ℝ 2 u x (fun _ => v) := by
      have hc : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 u) x :=
        (hu.contDiff.differentiable_iteratedFDeriv (by norm_num)).differentiableAt
      rw [show (fun y => fderiv ℝ u y v) =
          (fun y => iteratedFDeriv ℝ 1 u y (fun _ => v)) by funext y; simp]
      rw [fderiv_continuousMultilinear_apply_const hc (fun _ : Fin 1 => v)]
      rw [iteratedFDeriv_succ_apply_left (n := 1) (f := u) (x := x) (m := fun _ => v)]
      rfl
    rw [hhess, hscale]
    nlinarith

/-- Assemble the three scalar/multivariate jet leaves with one common constant. -/
theorem uniformNonnegativeJetBounds (n : ℕ) : HasUniformNonnegativeJetBounds n := by
  obtain ⟨C₁, hC₁, hfirst⟩ := nonnegative_first_derivative_bound (n := n)
  obtain ⟨C₃, hC₃, hthird⟩ := nonnegative_third_derivative_bound (n := n)
  obtain ⟨C₂, hC₂, hhessian⟩ := nonnegative_hessian_lower_bound (n := n)
  let C := max C₁ (max C₂ C₃)
  have hC₁C : C₁ ≤ C := le_max_left _ _
  have hC₂C : C₂ ≤ C := (le_max_left C₂ C₃).trans (le_max_right C₁ _)
  have hC₃C : C₃ ≤ C := (le_max_right C₂ C₃).trans (le_max_right C₁ _)
  have hC : 0 < C := hC₁.trans_le hC₁C
  refine ⟨C, hC, ?_⟩
  intro u hu
  refine {
    constant_nonneg := hC.le
    first := ?_
    third := ?_
    hessian_lower := ?_ }
  · intro x
    exact (hfirst u hu x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₁C (nonnegativeJetScale_nonneg u x))
      (Real.sqrt_nonneg _))
  · intro x
    exact (hthird u hu x).trans
      (mul_le_mul_of_nonneg_right hC₃C (nonnegativeJetScale_nonneg u x))
  · intro x v
    exact (neg_le_neg (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₂C (Real.sqrt_nonneg _)) (sq_nonneg ‖v‖))).trans
      (hhessian u hu x v)

end QuarticConvergence
end OptimalConvergenceRates

end
