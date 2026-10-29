import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! Near-identity inverse estimates and repair of positive images with a constant correction.
Shared by the general-polynomial and homogeneous sphere constructions. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence

section NearIdentity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A linear endomorphism whose error is strictly smaller than every nonzero input is
injective. -/
theorem linearEnd_injective_of_norm_sub_lt (T : Module.End ℝ V)
    (hT : ∀ v, v ≠ 0 → ‖v - T v‖ < ‖v‖) : Function.Injective T := by
  intro x y hxy
  by_contra hne
  have hv : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hstrict := hT (x - y) hv
  have hzero : T (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [hzero, sub_zero] at hstrict
  exact (lt_irrefl ‖x - y‖) hstrict

/-- The usual operator-error estimate with constant below one implies injectivity. -/
theorem linearEnd_injective_of_error_le (T : Module.End ℝ V) (c : ℝ) (hc : c < 1)
    (hT : ∀ v, ‖v - T v‖ ≤ c * ‖v‖) : Function.Injective T := by
  apply linearEnd_injective_of_norm_sub_lt T
  intro v hv
  calc
    ‖v - T v‖ ≤ c * ‖v‖ := hT v
    _ < 1 * ‖v‖ := mul_lt_mul_of_pos_right hc (norm_pos_iff.mpr hv)
    _ = ‖v‖ := one_mul _

/-- In finite dimension, a near-identity endomorphism is onto; no Neumann-series
construction is needed. -/
theorem linearEnd_surjective_of_error_le [FiniteDimensional ℝ V]
    (T : Module.End ℝ V) (c : ℝ) (hc : c < 1)
    (hT : ∀ v, ‖v - T v‖ ≤ c * ‖v‖) : Function.Surjective T :=
  LinearMap.surjective_of_injective (linearEnd_injective_of_error_le T c hc hT)
/-- A finite-dimensional near-identity map has a preimage whose norm is controlled by
1 / (1-c). -/
theorem linearEnd_exists_preimage_norm_le [FiniteDimensional ℝ V]
    (T : Module.End ℝ V) (c : ℝ) (hc : c < 1)
    (hT : ∀ v, ‖v - T v‖ ≤ c * ‖v‖) (y : V) :
    ∃ x : V, T x = y ∧ ‖x‖ ≤ ‖y‖ / (1 - c) := by
  obtain ⟨x, hx⟩ := linearEnd_surjective_of_error_le T c hc hT y
  refine ⟨x, hx, ?_⟩
  have hnorm : ‖x‖ ≤ c * ‖x‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - T x) + T x‖ := by
        congr 1
        abel
      _ ≤ ‖x - T x‖ + ‖T x‖ := norm_add_le _ _
      _ ≤ c * ‖x‖ + ‖T x‖ := add_le_add (hT x) le_rfl
      _ = c * ‖x‖ + ‖y‖ := by rw [hx]
  apply (le_div_iff₀ (sub_pos.mpr hc)).2
  nlinarith

/-- The same preimage differs from the target by at most c / (1-c) times the
target norm. -/
theorem linearEnd_exists_preimage_correction_le [FiniteDimensional ℝ V]
    (T : Module.End ℝ V) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hT : ∀ v, ‖v - T v‖ ≤ c * ‖v‖) (y : V) :
    ∃ x : V, T x = y ∧
      ‖x‖ ≤ ‖y‖ / (1 - c) ∧ ‖x - y‖ ≤ c / (1 - c) * ‖y‖ := by
  obtain ⟨x, hx, hxnorm⟩ := linearEnd_exists_preimage_norm_le T c hc1 hT y
  refine ⟨x, hx, hxnorm, ?_⟩
  calc
    ‖x - y‖ = ‖x - T x‖ := by rw [hx]
    _ ≤ c * ‖x‖ := hT x
    _ ≤ c * (‖y‖ / (1 - c)) := mul_le_mul_of_nonneg_left hxnorm hc0
    _ = c / (1 - c) * ‖y‖ := by ring

end NearIdentity

namespace PositiveImageRepair

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem positive_preimage [FiniteDimensional ℝ V] {Ω : Type*}
    (E : V →ₗ[ℝ] (Ω → ℝ)) (e : V)
    (he : ∀ x, E e x = 1) (hen : ‖e‖ ≤ 1)
    (heval : ∀ v x, |E v x| ≤ ‖v‖)
    (A : V →ₗ[ℝ] V) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 4)
    (hnear : ∀ v, ‖v - A v‖ ≤ t*‖v‖)
    (F : V) (hFn : ‖F‖ ≤ 1) (hF : ∀ x, 0 ≤ E F x) :
    ∃ H, A H=F+(2*t) • e ∧ ‖H‖≤2 ∧ ∀ x, 0≤E H x := by
  have ht1 : t<1 := by linarith
  have honto : Function.Surjective A :=
    linearEnd_surjective_of_error_le A t ht1 hnear
  obtain ⟨H,hH⟩ := honto (F+(2*t) • e)
  have htarget : ‖F+(2*t) • e‖≤1+2*t := by
    calc
      ‖F+(2*t) • e‖≤‖F‖+‖(2*t) • e‖ := norm_add_le _ _
      _ = ‖F‖+(2*t)*‖e‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      _ ≤ 1+(2*t)*1 := add_le_add hFn (mul_le_mul_of_nonneg_left hen (by positivity))
      _ = 1+2*t := by ring
  have hsum : ‖H‖≤t*‖H‖+(1+2*t) := by
    calc
      ‖H‖=‖(H-A H)+A H‖ := by congr 1; abel
      _ ≤ ‖H-A H‖+‖A H‖ := norm_add_le _ _
      _ ≤ t*‖H‖+(1+2*t) := add_le_add (hnear H) (by rw [hH]; exact htarget)
  have htn := mul_le_mul_of_nonneg_right ht (norm_nonneg H)
  have hHn : ‖H‖≤2 := by nlinarith
  have herr : ‖H-(F+(2*t) • e)‖≤2*t := by
    rw [←hH]
    exact (hnear H).trans (by nlinarith)
  refine ⟨H,hH,hHn,?_⟩
  intro x
  have hval := (abs_le.mp ((heval (H-(F+(2*t) • e)) x).trans herr)).1
  simp only [map_sub,map_add,map_smul,Pi.sub_apply,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul,he,mul_one] at hval
  linarith [hF x]

/-- Algebraic repair of the Taylor image. This conditional component is
independent of a concrete polynomial kernel or SOS construction. -/
theorem certificate_of_positive_images [FiniteDimensional ℝ V] {Ω : Type*}
    (E : V →ₗ[ℝ] (Ω → ℝ)) (e : V)
    (he : ∀ x, E e x = 1) (hen : ‖e‖ ≤ 1) (heval : ∀ v x, |E v x| ≤ ‖v‖)
    (K : Set V) (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hconst : ∀ c:ℝ, 0≤c → c • e∈K)
    (A : V →ₗ[ℝ] V) {t q : ℝ} (ht0 : 0≤t) (ht : t≤1/4) (hq : 0≤q)
    (hnear : ∀ v, ‖v-A v‖≤t*‖v‖)
    (himage : ∀ v, (∀ x, 0≤E v x) → A v+(q*‖v‖) • e∈K)
    (F : V) (hFn : ‖F‖≤1) (hF : ∀ x, 0≤E F x) :
    F+(2*(t+q)) • e∈K := by
  obtain ⟨H,hH,hHn,hpos⟩ := positive_preimage E e he hen heval A ht0 ht hnear F hFn hF
  have hres : 0≤q*(2-‖H‖) := mul_nonneg hq (sub_nonneg.mpr hHn)
  have hs := hadd _ (himage H hpos) _ (hconst _ hres)
  rw [hH] at hs
  convert hs using 1; module

end PositiveImageRepair
end OptimalConvergenceRates.QuarticConvergence
