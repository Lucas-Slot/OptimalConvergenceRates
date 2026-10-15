/-
  OptimalConvergenceRates/BasicNotions/Defs.lean

  Core hypercube and polynomial norm definitions used throughout the project.
-/
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

open MvPolynomial Finset

noncomputable section

/-- Syntax compatibility for the pre-v4.34 argument order of multivariate coefficients. -/
macro "legacyMvCoeff" m:term:max p:term:max : term =>
  `(AddMonoidAlgebra.coeff $p $m)

/-- Partially applied form used by coefficient extensionality arguments. -/
macro "legacyMvCoeff" m:term:max : term =>
  `(fun p => AddMonoidAlgebra.coeff p $m)

namespace OptimalConvergenceRates

variable {n : ℕ}

/-- Compatibility alias for the pre-v4.34 unqualified coefficient API. -/
abbrev coeff {σ R : Type*} [CommSemiring R]
    (m : σ →₀ ℕ) (p : MvPolynomial σ R) : R :=
  AddMonoidAlgebra.coeff p m

/-! ## The Hypercube B^n = [-1,1]^n -/

/-- The hypercube B^n = [-1,1]^n ⊆ ℝ^n -/
def Hypercube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-1) 1)

/-! ## The scaled hypercube [-η,η]^n -/

/-- The scaled hypercube [-η,η]^n = {x : Fin n → ℝ | |x_i| ≤ η for all i} -/
def ScaledHypercube (η : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-η) η)

theorem ScaledHypercube_mem_iff (η : ℝ) (x : Fin n → ℝ) :
    x ∈ ScaledHypercube η n ↔ ∀ i, x i ∈ Set.Icc (-η) η := by
  simp only [ScaledHypercube, Set.mem_pi, Set.mem_univ, true_implies]

theorem ScaledHypercube_mem_abs (η : ℝ) (_hη : 0 ≤ η) (x : Fin n → ℝ) :
    x ∈ ScaledHypercube η n ↔ ∀ i, |x i| ≤ η := by
  rw [ScaledHypercube_mem_iff]
  exact ⟨fun h i => abs_le.mpr ⟨h i |>.1, h i |>.2⟩,
         fun h i => (abs_le.mp (h i))⟩

theorem ScaledHypercube_nonempty (η : ℝ) (hη : 0 ≤ η) : (ScaledHypercube η n).Nonempty :=
  ⟨fun _ => 0, fun _ _ => ⟨by linarith, by linarith⟩⟩

theorem ScaledHypercube_compact (η : ℝ) : IsCompact (ScaledHypercube η n) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem ScaledHypercube_one : ScaledHypercube 1 n = Hypercube n := by
  ext x
  simp only [ScaledHypercube, Hypercube, Set.mem_pi, Set.mem_univ, true_implies]

/-! ## Sup-norm, min, max on the hypercube -/

/-- Sup-norm of a multivariate polynomial on B^n = [-1,1]^n.
    See also `polySupNormScaled` (on [-r,r]^n) and `polySupNormUni` (univariate, on [-1,1]). -/
noncomputable def polySupNorm (f : MvPolynomial (Fin n) ℝ) : ℝ :=
  sSup ((fun x => |MvPolynomial.eval x f|) '' Hypercube n)

/-- Sup-norm of a multivariate polynomial on the scaled hypercube [-r,r]^n.
    See also `polySupNorm` (on B^n) and `polySupNormUni` (univariate, on [-1,1]). -/
noncomputable def polySupNormScaled (f : MvPolynomial (Fin n) ℝ) (r : ℝ) : ℝ :=
  sSup ((fun x => |MvPolynomial.eval x f|) '' ScaledHypercube r n)

/-- Sup-norm of a univariate polynomial on [-1,1].
    See also `polySupNorm` (multivariate, on B^n) and `polySupNormScaled` (on [-r,r]^n). -/
noncomputable def polySupNormUni (p : Polynomial ℝ) : ℝ :=
  sSup ((fun x => |p.eval x|) '' Set.Icc (-1) 1)

/-- Minimum of f over B^n -/
noncomputable def polyMin (f : MvPolynomial (Fin n) ℝ) : ℝ :=
  sInf ((fun x => MvPolynomial.eval x f) '' Hypercube n)

/-- Maximum of f over B^n -/
noncomputable def polyMax (f : MvPolynomial (Fin n) ℝ) : ℝ :=
  sSup ((fun x => MvPolynomial.eval x f) '' Hypercube n)

/-! ## Basic polySupNormUni lemmas -/

private theorem icc_compact : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc

private theorem icc_nonempty : (Set.Icc (-1 : ℝ) 1).Nonempty :=
  Set.nonempty_Icc.mpr (by norm_num)

private theorem continuous_abs_poly_eval (p : Polynomial ℝ) :
    Continuous (fun x : ℝ => |p.eval x|) :=
  continuous_abs.comp (Polynomial.continuous_aeval p)

private theorem bddAbove_abs_poly_image (p : Polynomial ℝ) :
    BddAbove ((fun x => |p.eval x|) '' Set.Icc (-1) 1) :=
  (icc_compact.image (continuous_abs_poly_eval p)).bddAbove

theorem polySupNormUni_nonneg (p : Polynomial ℝ) : 0 ≤ polySupNormUni p := by
  unfold polySupNormUni
  apply le_csSup_of_le (bddAbove_abs_poly_image p)
  · exact ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩, rfl⟩
  · exact abs_nonneg _

theorem polySupNormUni_eval_le (p : Polynomial ℝ) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    |p.eval x| ≤ polySupNormUni p := by
  unfold polySupNormUni
  exact le_csSup (bddAbove_abs_poly_image p)
    ⟨x, Set.mem_Icc.mpr ⟨hx1, hx2⟩, rfl⟩

theorem polySupNormUni_le_of_bound (p : Polynomial ℝ) (c : ℝ)
    (hc : ∀ x : ℝ, -1 ≤ x → x ≤ 1 → |p.eval x| ≤ c) :
    polySupNormUni p ≤ c := by
  unfold polySupNormUni
  apply csSup_le (Set.Nonempty.image _ icc_nonempty)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hc x hx.1 hx.2

/-! ## Hypercube properties -/

theorem Hypercube_compact : IsCompact (Hypercube n) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem Hypercube_nonempty : (Hypercube n).Nonempty :=
  ⟨fun _ => 0, fun _ _ => ⟨by linarith, by linarith⟩⟩

theorem Hypercube_mem_iff (x : Fin n → ℝ) :
    x ∈ Hypercube n ↔ ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1 := by
  simp only [Hypercube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]

/-! ## Univariate embedding -/

/-- Embed a univariate polynomial into the i-th variable of MvPolynomial (Fin n) ℝ.
    This maps x ↦ X_i via aeval. -/
noncomputable def embedUnivariate (i : Fin n) :
    Polynomial ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ :=
  Polynomial.aeval (X i)

/-- The total degree of `embedUnivariate i p` is at most `natDegree p`. -/
theorem totalDegree_embedUnivariate {n : ℕ} (i : Fin n) (p : Polynomial ℝ) :
    (embedUnivariate i p).totalDegree ≤ p.natDegree := by
  unfold embedUnivariate
  rw [Polynomial.aeval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  calc (p.coeff k • X i ^ k).totalDegree
      ≤ (X i ^ k : MvPolynomial (Fin n) ℝ).totalDegree :=
        MvPolynomial.totalDegree_smul_le _ _
    _ = k := MvPolynomial.totalDegree_X_pow i k
    _ ≤ p.natDegree := by
        rw [Finset.mem_range] at hk; omega

/-! ## Sup-norm, min, max properties -/

theorem Hypercube_image_compact (f : MvPolynomial (Fin n) ℝ) :
    IsCompact ((fun x => MvPolynomial.eval x f) '' Hypercube n) :=
  Hypercube_compact.image (MvPolynomial.continuous_eval f)

theorem Hypercube_image_nonempty (f : MvPolynomial (Fin n) ℝ) :
    ((fun x => MvPolynomial.eval x f) '' Hypercube n).Nonempty :=
  Set.Nonempty.image _ Hypercube_nonempty

theorem polyMin_le_polyMax (f : MvPolynomial (Fin n) ℝ) :
    polyMin f ≤ polyMax f := by
  exact csInf_le_csSup
    (Hypercube_image_nonempty f)
    (Hypercube_image_compact f).bddBelow
    (Hypercube_image_compact f).bddAbove

theorem polyMin_mem (f : MvPolynomial (Fin n) ℝ) :
    ∃ x ∈ Hypercube n, MvPolynomial.eval x f = polyMin f := by
  have hc := Hypercube_image_compact f
  have hne := Hypercube_image_nonempty f
  have h := hc.sInf_mem hne
  obtain ⟨x, hx, heval⟩ := h
  exact ⟨x, hx, heval⟩

theorem polyMax_mem (f : MvPolynomial (Fin n) ℝ) :
    ∃ x ∈ Hypercube n, MvPolynomial.eval x f = polyMax f := by
  have hc := Hypercube_image_compact f
  have hne := Hypercube_image_nonempty f
  have h := hc.sSup_mem hne
  obtain ⟨x, hx, heval⟩ := h
  exact ⟨x, hx, heval⟩

/-- Pointwise bound from sup-norm: if polySupNorm p ≤ c, then |eval x p| ≤ c on B^n -/
theorem polySupNorm_eval_le (f : MvPolynomial (Fin n) ℝ) (c : ℝ) (hc : polySupNorm f ≤ c)
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    |MvPolynomial.eval x f| ≤ c := by
  have hmem : |MvPolynomial.eval x f| ∈
      (fun x => |MvPolynomial.eval x f|) '' Hypercube n :=
    ⟨x, hx, rfl⟩
  have hbdd : BddAbove ((fun x => |MvPolynomial.eval x f|) '' Hypercube n) :=
    (Hypercube_compact.image (continuous_abs.comp (MvPolynomial.continuous_eval f))).bddAbove
  exact le_trans (le_csSup hbdd hmem) hc

/-- Converse: pointwise bound implies sup-norm bound. -/
theorem polySupNorm_le_of_bound (p : MvPolynomial (Fin n) ℝ) (c : ℝ)
    (h : ∀ x ∈ Hypercube n, |MvPolynomial.eval x p| ≤ c) :
    polySupNorm p ≤ c := by
  unfold polySupNorm
  apply csSup_le (Set.image_nonempty.mpr Hypercube_nonempty)
  rintro _ ⟨x, hx, rfl⟩; exact h x hx

/-- Pointwise lower bound from polyMin -/
theorem polyMin_le_eval (f : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ)
    (hx : x ∈ Hypercube n) :
    polyMin f ≤ MvPolynomial.eval x f := by
  exact csInf_le (Hypercube_image_compact f).bddBelow ⟨x, hx, rfl⟩

/-- When f is nonneg on B^n, polySupNorm f ≤ polyMax f
    (since |f(x)| = f(x) ≤ polyMax f). -/
theorem polySupNorm_le_polyMax_of_nonneg (f : MvPolynomial (Fin n) ℝ)
    (hf : ∀ x ∈ Hypercube n, 0 ≤ MvPolynomial.eval x f) :
    polySupNorm f ≤ polyMax f := by
  unfold polySupNorm polyMax
  have hne : ((fun x => |MvPolynomial.eval x f|) '' Hypercube n).Nonempty :=
    Hypercube_nonempty.image _
  apply csSup_le hne
  rintro _ ⟨x, hx, rfl⟩
  change |MvPolynomial.eval x f| ≤ _
  rw [abs_of_nonneg (hf x hx)]
  exact le_csSup (Hypercube_image_compact f).bddAbove ⟨x, hx, rfl⟩

/-- polyMax (f - C c) = polyMax f - c -/
theorem polyMax_sub_C (f : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    polyMax (f - MvPolynomial.C c) = polyMax f - c := by
  unfold polyMax
  set S := (fun x => MvPolynomial.eval x f) '' Hypercube n with hS_def
  have heq : (fun x => MvPolynomial.eval x (f - MvPolynomial.C c)) '' Hypercube n =
      (fun y => y - c) '' S := by
    ext y; simp only [Set.mem_image, map_sub, MvPolynomial.eval_C, hS_def]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨MvPolynomial.eval x f, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [heq]
  have hne : S.Nonempty := Hypercube_image_nonempty f
  have hbdd : BddAbove S := (Hypercube_image_compact f).bddAbove
  have hcpt : IsCompact S := Hypercube_image_compact f
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨v, hv, rfl⟩
    exact sub_le_sub_right (le_csSup hbdd hv) c
  · have hmem : sSup S ∈ S := hcpt.sSup_mem hne
    exact le_csSup (hcpt.image (continuous_sub_right c)).bddAbove
      ⟨sSup S, hmem, rfl⟩

/-- polyMin (f - C c) = polyMin f - c -/
theorem polyMin_sub_C (f : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    polyMin (f - MvPolynomial.C c) = polyMin f - c := by
  unfold polyMin
  set S := (fun x => MvPolynomial.eval x f) '' Hypercube n with hS_def
  have heq : (fun x => MvPolynomial.eval x (f - MvPolynomial.C c)) '' Hypercube n =
      (fun y => y - c) '' S := by
    ext y; simp only [Set.mem_image, map_sub, MvPolynomial.eval_C, hS_def]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨MvPolynomial.eval x f, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [heq]
  have hne : S.Nonempty := Hypercube_image_nonempty f
  have hbdd : BddBelow S := (Hypercube_image_compact f).bddBelow
  have hcpt : IsCompact S := Hypercube_image_compact f
  apply le_antisymm
  · have hmem : sInf S ∈ S := hcpt.sInf_mem hne
    exact csInf_le (hcpt.image (continuous_sub_right c)).bddBelow
      ⟨sInf S, hmem, rfl⟩
  · apply le_csInf (hne.image _)
    rintro _ ⟨v, hv, rfl⟩
    exact sub_le_sub_right (csInf_le hbdd hv) c

/-- The spread polyMax f - polyMin f is unchanged by subtracting a constant. -/
theorem polyMax_sub_polyMin_sub_C (f : MvPolynomial (Fin n) ℝ) (c : ℝ) :
    polyMax (f - MvPolynomial.C c) - polyMin (f - MvPolynomial.C c) =
    polyMax f - polyMin f := by
  rw [polyMax_sub_C, polyMin_sub_C]; ring

end OptimalConvergenceRates

end
