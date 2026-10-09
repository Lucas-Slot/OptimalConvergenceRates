import OptimalConvergenceRates.KrivineStengle.HermiteLinear
import OptimalConvergenceRates.KrivineStengle.HermiteProduct

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Hermite's root-sign identity passes from pairwise coprime monic
factors to their finite product. -/
theorem hermiteSignature_eq_rootSignSum_finset_prod
    {ι : Type v} (s : Finset ι) (f : ι → F[X])
    (hmonic : ∀ i ∈ s, (f i).Monic)
    (hcoprime : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j))
    (hidentity : ∀ i (hi : i ∈ s) (h : F[X]),
      hermiteSignature (f i) h (hmonic i hi) = rootSignSum (f i) h) :
    ∀ h : F[X],
      hermiteSignature (∏ i ∈ s, f i) h
          (monic_prod_of_monic s f hmonic) =
        rootSignSum (∏ i ∈ s, f i) h := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro h
      simpa using hermiteSignature_eq_rootSignSum_one (F := F) h
  | @insert a s ha ih =>
      intro h
      have hma : (f a).Monic := hmonic a (Finset.mem_insert_self a s)
      have hms : (∏ i ∈ s, f i).Monic :=
        monic_prod_of_monic s f fun i hi ↦ hmonic i (Finset.mem_insert_of_mem hi)
      have hcop : IsCoprime (f a) (∏ i ∈ s, f i) := by
        apply IsCoprime.prod_right
        intro i hi
        apply hcoprime a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi)
        exact fun hai ↦ ha (hai ▸ hi)
      have hrest (p : F[X]) :
          hermiteSignature (∏ i ∈ s, f i) p hms =
            rootSignSum (∏ i ∈ s, f i) p := by
        exact ih
          (fun i hi ↦ hmonic i (Finset.mem_insert_of_mem hi))
          (by
            intro i hi j hj hij
            exact hcoprime i (Finset.mem_insert_of_mem hi) j
              (Finset.mem_insert_of_mem hj) hij)
          (by
            intro i hi q
            exact hidentity i (Finset.mem_insert_of_mem hi) q) p
      have hproduct := hermiteSignature_eq_rootSignSum_mul hma hms hcop
        (fun p ↦ hidentity a (Finset.mem_insert_self a s) p) hrest h
      simpa only [Finset.prod_insert ha] using hproduct


/-- Hermite's root-sign identity for a product of distinct linear factors. -/
theorem hermiteSignature_eq_rootSignSum_prod_X_sub_C
    {ι : Type v} (s : Finset ι) (a : ι → F)
    (hinj : Set.InjOn a s) :
    ∀ h : F[X],
      hermiteSignature (∏ i ∈ s, (X - C (a i))) h
          (monic_prod_X_sub_C a s) =
        rootSignSum (∏ i ∈ s, (X - C (a i))) h := by
  exact hermiteSignature_eq_rootSignSum_finset_prod s
    (fun i ↦ X - C (a i))
    (fun i _ ↦ monic_X_sub_C (a i))
    (by
      intro i hi j hj hij
      exact isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero_of_ne (fun heq ↦ hij (hinj hi hj heq))).isUnit)
    (by
      intro i _ h
      exact hermiteSignature_eq_rootSignSum_X_sub_C (a i) h)

end OptimalConvergenceRates.KrivineStengle

end
