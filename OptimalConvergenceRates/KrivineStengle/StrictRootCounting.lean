/-
  OptimalConvergenceRates/KrivineStengle/StrictRootCounting.lean

  The finite combinatorial passage from Hermite root-sign identities to
  counting roots satisfying a conjunction of strict inequalities.
-/
import OptimalConvergenceRates.KrivineStengle.HermiteTraceIsometry
import OptimalConvergenceRates.KrivineStengle.OrderedSignCalculus

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Sum of the signs of `h` over the distinct roots of `f` in the base
field. -/
def rootSignSum (f h : F[X]) : ℤ :=
  ∑ r ∈ f.roots.toFinset, orderedSign (h.eval r)

/-- Number of distinct roots of `f` at which every member of `g` is
strictly positive. -/
def strictRootCount {s : ℕ} (f : F[X]) (g : Fin s → F[X]) : ℕ :=
  (f.roots.toFinset.filter fun r ↦ ∀ i, 0 < (g i).eval r).card

theorem strictRootCount_pos_iff {s : ℕ} (f : F[X]) (g : Fin s → F[X]) :
    0 < strictRootCount f g ↔
      ∃ r ∈ f.roots.toFinset, ∀ i, 0 < (g i).eval r := by
  rw [strictRootCount, Finset.card_pos]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩
  · rintro ⟨r, hr, hpos⟩
    exact ⟨r, Finset.mem_filter.mpr ⟨hr, hpos⟩⟩

/-- Pure sign combinatorics: the `{1,2}` exponent sum selects precisely
the roots where all side polynomials are positive. -/
theorem sum_rootSignSum_products_pow_one_two {s : ℕ}
    (f : F[X]) (g : Fin s → F[X]) :
    (∑ exponent : Fin s → Fin 2,
        rootSignSum f (∏ i, (g i) ^ (exponent i).1.succ)) =
      (2 : ℤ) ^ s * (strictRootCount f g : ℤ) := by
  classical
  calc
    (∑ exponent : Fin s → Fin 2,
        rootSignSum f (∏ i, (g i) ^ (exponent i).1.succ)) =
        ∑ exponent : Fin s → Fin 2, ∑ r ∈ f.roots.toFinset,
          orderedSign ((∏ i, (g i) ^ (exponent i).1.succ).eval r) := rfl
    _ = ∑ r ∈ f.roots.toFinset, ∑ exponent : Fin s → Fin 2,
          orderedSign ((∏ i, (g i) ^ (exponent i).1.succ).eval r) := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ f.roots.toFinset,
          if ∀ i, 0 < (g i).eval r then (2 : ℤ) ^ s else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      simpa only [eval_prod, eval_pow] using
        sum_orderedSign_products_pow_one_two (fun i ↦ (g i).eval r)
    _ = ∑ r ∈ (f.roots.toFinset.filter fun r ↦ ∀ i, 0 < (g i).eval r),
          (2 : ℤ) ^ s := by
      rw [Finset.sum_filter]
    _ = (2 : ℤ) ^ s * (strictRootCount f g : ℤ) := by
      simp [strictRootCount, mul_comm]

/-- Once Hermite's root-sign identity is available for `f`, strict root
counting follows without any division by `2^s`. -/
theorem strictRootCount_hermite_identity {s : ℕ}
    (f : F[X]) (hf : f.Monic) (g : Fin s → F[X])
    (hHermite : ∀ h : F[X], hermiteSignature f h hf = rootSignSum f h) :
    (2 : ℤ) ^ s * (strictRootCount f g : ℤ) =
      ∑ exponent : Fin s → Fin 2,
        hermiteSignature f (∏ i, (g i) ^ (exponent i).1.succ) hf := by
  rw [← sum_rootSignSum_products_pow_one_two f g]
  apply Finset.sum_congr rfl
  intro exponent _
  exact (hHermite _).symm

/-- Positivity of the finite Hermite-signature sum is equivalent to the
existence of a distinct root satisfying all strict side inequalities. -/
theorem exists_root_all_pos_iff_hermite_sum_pos {s : ℕ}
    (f : F[X]) (hf : f.Monic) (g : Fin s → F[X])
    (hHermite : ∀ h : F[X], hermiteSignature f h hf = rootSignSum f h) :
    (∃ r ∈ f.roots.toFinset, ∀ i, 0 < (g i).eval r) ↔
      0 < ∑ exponent : Fin s → Fin 2,
        hermiteSignature f (∏ i, (g i) ^ (exponent i).1.succ) hf := by
  rw [← strictRootCount_pos_iff f g]
  rw [← strictRootCount_hermite_identity f hf g hHermite]
  rw [mul_pos_iff_of_pos_left (by positivity : 0 < (2 : ℤ) ^ s)]
  norm_cast

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Positive powers preserve the distinct-root sign sum. -/
theorem rootSignSum_pow (f h : F[X]) {n : ℕ} (hn : n ≠ 0) :
    rootSignSum (f ^ n) h = rootSignSum f h := by
  simp [rootSignSum, roots_pow, Multiset.toFinset_nsmul _ _ hn]

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F]

/-- Coprime polynomials have disjoint sets of roots in the base field. -/
theorem disjoint_roots_toFinset_of_isCoprime {f g : F[X]}
    (hfg : IsCoprime f g) :
    Disjoint f.roots.toFinset g.roots.toFinset := by
  classical
  rw [Finset.disjoint_left]
  intro r hrf hrg
  have hrf' : r ∈ f.roots := Multiset.mem_toFinset.mp hrf
  have hrg' : r ∈ g.roots := Multiset.mem_toFinset.mp hrg
  have hf0 : f ≠ 0 := ne_zero_of_mem_roots hrf'
  have hg0 : g ≠ 0 := ne_zero_of_mem_roots hrg'
  have hfr : f.eval r = 0 := (mem_roots hf0).mp hrf'
  have hgr : g.eval r = 0 := (mem_roots hg0).mp hrg'
  rcases aeval_ne_zero_of_isCoprime hfg r with hne | hne
  · exact hne (by simpa [aeval_def] using hfr)
  · exact hne (by simpa [aeval_def] using hgr)

variable [IsStrictOrderedRing F]

/-- Root-sign sums add across coprime factors. -/
theorem rootSignSum_mul {f g : F[X]} (h : F[X]) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) (hfg : IsCoprime f g) :
    rootSignSum (f * g) h = rootSignSum f h + rootSignSum g h := by
  classical
  rw [rootSignSum, roots_mul (mul_ne_zero hf0 hg0), Multiset.toFinset_add,
    Finset.sum_union (disjoint_roots_toFinset_of_isCoprime hfg)]
  rfl

end OptimalConvergenceRates.KrivineStengle

end
