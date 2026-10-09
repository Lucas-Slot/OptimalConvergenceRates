import OptimalConvergenceRates.KrivineStengle.HermiteQuadraticPowerTrace
import OptimalConvergenceRates.KrivineStengle.HermiteTraceIsometry
import OptimalConvergenceRates.KrivineStengle.StrictRootCounting
import OptimalConvergenceRates.KrivineStengle.SignatureOperations

noncomputable section

open Polynomial QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [IsRealClosed R]

private theorem eval₂_adjoinRoot_of_root_eq_mk (f p : R[X]) :
    eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) p = AdjoinRoot.mk f p := by
  rw [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

theorem hermiteTraceFormSignature_quadratic_pow {q : R[X]}
    (hqMonic : q.Monic) (hqDegree : q.natDegree = 2)
    (h : R[X]) {n : ℕ} (hn : 0 < n) :
    hermiteTraceFormSignature (q ^ n) h (hqMonic.pow n) =
      hermiteTraceFormSignature q h hqMonic := by
  let hqnMonic : (q ^ n).Monic := hqMonic.pow n
  letI : Module.Free R (AdjoinRoot (q ^ n)) := hqnMonic.free_adjoinRoot
  letI : Module.Finite R (AdjoinRoot (q ^ n)) :=
    (AdjoinRoot.powerBasis' hqnMonic).finite
  letI : Module.Free R (AdjoinRoot q) := hqMonic.free_adjoinRoot
  letI : Module.Finite R (AdjoinRoot q) :=
    (AdjoinRoot.powerBasis' hqMonic).finite
  let hdiv : q ∣ q ^ n := dvd_pow_self q (Nat.ne_of_gt hn)
  let φ : AdjoinRoot (q ^ n) →ₐ[R] AdjoinRoot q :=
    AdjoinRoot.algHomOfDvd R (q ^ n) q hdiv
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    refine ⟨AdjoinRoot.mk (q ^ n) p, ?_⟩
    simp [φ, AdjoinRoot.coe_algHomOfDvd, Polynomial.aeval_def,
      Algebra.toRingHom_ofId, AdjoinRoot.aeval_eq, eval₂_adjoinRoot_of_root_eq_mk]
  have hform :
      (hermiteTraceForm (q ^ n) h hqnMonic).toQuadraticMap =
        (((n : R) • (hermiteTraceForm q h hqMonic).toQuadraticMap).comp
          φ.toLinearMap) := by
    ext x
    induction x using AdjoinRoot.induction_on with
    | _ p =>
      simp only [LinearMap.BilinMap.toQuadraticMap_apply,
        hermiteTraceForm_apply, QuadraticMap.comp_apply, smul_apply]
      have ht := trace_aeval_adjoinRoot_quadratic_pow
        hqMonic hqDegree (h * p * p) hn
      simpa [φ, AdjoinRoot.coe_algHomOfDvd, Polynomial.aeval_def,
        Algebra.toRingHom_ofId, AdjoinRoot.aeval_eq, map_mul, nsmul_eq_mul,
        mul_assoc, eval₂_adjoinRoot_of_root_eq_mk] using ht
  change signature (hermiteTraceForm (q ^ n) h hqnMonic).toQuadraticMap =
    signature (hermiteTraceForm q h hqMonic).toQuadraticMap
  rw [hform, signature_comp_surjective _ _ hφsurj]
  exact signature_smul_pos _ (Nat.cast_pos.mpr hn)

theorem hermiteSignature_quadratic_pow {q : R[X]}
    (hqMonic : q.Monic) (hqDegree : q.natDegree = 2)
    (h : R[X]) {n : ℕ} (hn : 0 < n) :
    hermiteSignature (q ^ n) h (hqMonic.pow n) =
      hermiteSignature q h hqMonic := by
  rw [← hermiteTraceFormSignature_eq, ← hermiteTraceFormSignature_eq]
  exact hermiteTraceFormSignature_quadratic_pow hqMonic hqDegree h hn

theorem hermiteSignature_irreducible_quadratic_pow {q : R[X]}
    (hqMonic : q.Monic) (hqIrr : Irreducible q)
    (hqDegree : q.natDegree = 2) (h : R[X]) {n : ℕ} (hn : 0 < n) :
    hermiteSignature (q ^ n) h (hqMonic.pow n) = 0 := by
  rw [hermiteSignature_quadratic_pow hqMonic hqDegree h hn,
    hermiteSignature_irreducible_quadratic hqMonic hqIrr hqDegree]

theorem rootSignSum_irreducible_quadratic_pow {q : R[X]}
    (hqIrr : Irreducible q) (hqDegree : q.natDegree = 2)
    (h : R[X]) {n : ℕ} (hn : 0 < n) :
    rootSignSum (q ^ n) h = 0 := by
  rw [rootSignSum_pow q h (Nat.ne_of_gt hn),
    rootSignSum_irreducible_quadratic hqIrr hqDegree]

theorem hermiteSignature_eq_rootSignSum_irreducible_quadratic_pow {q : R[X]}
    (hqMonic : q.Monic) (hqIrr : Irreducible q)
    (hqDegree : q.natDegree = 2) (h : R[X]) {n : ℕ} (hn : 0 < n) :
    hermiteSignature (q ^ n) h (hqMonic.pow n) = rootSignSum (q ^ n) h := by
  rw [hermiteSignature_irreducible_quadratic_pow hqMonic hqIrr hqDegree h hn,
    rootSignSum_irreducible_quadratic_pow hqIrr hqDegree h hn]

end OptimalConvergenceRates.KrivineStengle

end
