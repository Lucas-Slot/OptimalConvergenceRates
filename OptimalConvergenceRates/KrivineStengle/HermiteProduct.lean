import OptimalConvergenceRates.KrivineStengle.HermiteTraceIsometry
import OptimalConvergenceRates.KrivineStengle.SignatureProduct
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import OptimalConvergenceRates.KrivineStengle.StrictRootCounting


noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]

/-- Chinese-remainder decomposition of an adjoined-root algebra for coprime factors. -/
noncomputable def adjoinRootMulEquiv {f g : F[X]} (hfg : IsCoprime f g) :
    AdjoinRoot (f * g) ≃ₐ[F] AdjoinRoot f × AdjoinRoot g := by
  let hI : IsCoprime (Ideal.span {f}) (Ideal.span {g}) :=
    (Ideal.isCoprime_span_singleton_iff f g).2 hfg
  let e₀ : AdjoinRoot (f * g) ≃+*
      (F[X] ⧸ Ideal.span {f}) × (F[X] ⧸ Ideal.span {g}) :=
    (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton f g).symm).trans
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {f}) (Ideal.span {g}) hI)
  exact
    { e₀ with
      commutes' := by
        intro r
        rfl }

@[simp] theorem adjoinRootMulEquiv_mk {f g : F[X]} (hfg : IsCoprime f g)
    (p : F[X]) :
    adjoinRootMulEquiv hfg (AdjoinRoot.mk (f * g) p) =
      (AdjoinRoot.mk f p, AdjoinRoot.mk g p) := by
  rfl

@[simp] theorem adjoinRootMulEquiv_root {f g : F[X]} (hfg : IsCoprime f g) :
    adjoinRootMulEquiv hfg (AdjoinRoot.root (f * g)) =
      (AdjoinRoot.root f, AdjoinRoot.root g) := by
  simpa only [AdjoinRoot.mk_X] using adjoinRootMulEquiv_mk hfg X

@[simp] theorem adjoinRootMulEquiv_aeval {f g : F[X]} (hfg : IsCoprime f g)
    (p : F[X]) :
    adjoinRootMulEquiv hfg (aeval (AdjoinRoot.root (f * g)) p) =
      (aeval (AdjoinRoot.root f) p, aeval (AdjoinRoot.root g) p) := by
  simp only [AdjoinRoot.aeval_eq, adjoinRootMulEquiv_mk]

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Polynomial QuadraticMap

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]

/-- The weighted trace form of a product of coprime monic polynomials is the
orthogonal product of the weighted trace forms of the factors. -/
noncomputable def hermiteTraceFormMulIsometry {f g : F[X]} (h : F[X])
    (hf : f.Monic) (hg : g.Monic) (hfg : IsCoprime f g) :
    (hermiteTraceForm (f * g) h (hf.mul hg)).toQuadraticMap.IsometryEquiv
      ((hermiteTraceForm f h hf).toQuadraticMap.prod
        (hermiteTraceForm g h hg).toQuadraticMap) := by
  letI : Module.Free F (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  letI : Module.Free F (AdjoinRoot g) := hg.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  letI : Module.Free F (AdjoinRoot (f * g)) := (hf.mul hg).free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot (f * g)) :=
    (AdjoinRoot.powerBasis' (hf.mul hg)).finite
  refine
    { toLinearEquiv := (adjoinRootMulEquiv hfg).toLinearEquiv
      map_app' := ?_ }
  intro x
  rw [QuadraticMap.prod_apply]
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, hermiteTraceForm_apply]
  calc
    _ = Algebra.trace F (AdjoinRoot f × AdjoinRoot g)
        (aeval (AdjoinRoot.root f) h *
            ((adjoinRootMulEquiv hfg).toLinearEquiv x).1 *
            ((adjoinRootMulEquiv hfg).toLinearEquiv x).1,
          aeval (AdjoinRoot.root g) h *
            ((adjoinRootMulEquiv hfg).toLinearEquiv x).2 *
            ((adjoinRootMulEquiv hfg).toLinearEquiv x).2) :=
      (Algebra.trace_prod_apply _).symm
    _ = Algebra.trace F (AdjoinRoot f × AdjoinRoot g)
        (adjoinRootMulEquiv hfg
          (aeval (AdjoinRoot.root (f * g)) h * x * x)) := by
      congr 1
      ext <;> simp
    _ = _ := Algebra.trace_eq_of_algEquiv (adjoinRootMulEquiv hfg) _


/-- The intrinsic signatures of Hermite trace forms add across coprime monic
factors. -/
theorem hermiteTraceFormSignature_mul [LinearOrder F] [IsStrictOrderedRing F]
    {f g : F[X]} (h : F[X]) (hf : f.Monic) (hg : g.Monic)
    (hfg : IsCoprime f g) :
    hermiteTraceFormSignature (f * g) h (hf.mul hg) =
      hermiteTraceFormSignature f h hf + hermiteTraceFormSignature g h hg := by
  letI : Module.Free F (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  letI : Module.Free F (AdjoinRoot g) := hg.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  letI : Module.Free F (AdjoinRoot (f * g)) := (hf.mul hg).free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot (f * g)) :=
    (AdjoinRoot.powerBasis' (hf.mul hg)).finite
  change signature (hermiteTraceForm (f * g) h (hf.mul hg)).toQuadraticMap =
    signature (hermiteTraceForm f h hf).toQuadraticMap +
      signature (hermiteTraceForm g h hg).toQuadraticMap
  rw [signature_congr (hermiteTraceFormMulIsometry h hf hg hfg).toLinearEquiv
    (hermiteTraceFormMulIsometry h hf hg hfg).map_app]
  exact signature_prod _ _

/-- Hermite signatures add across coprime monic factors. -/
theorem hermiteSignature_mul [LinearOrder F] [IsStrictOrderedRing F]
    {f g : F[X]} (h : F[X]) (hf : f.Monic) (hg : g.Monic)
    (hfg : IsCoprime f g) :
    hermiteSignature (f * g) h (hf.mul hg) =
      hermiteSignature f h hf + hermiteSignature g h hg := by
  rw [← hermiteTraceFormSignature_eq, hermiteTraceFormSignature_mul h hf hg hfg,
    hermiteTraceFormSignature_eq, hermiteTraceFormSignature_eq]

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Hermite's root-sign identity is closed under products of coprime monic
polynomials. -/
theorem hermiteSignature_eq_rootSignSum_mul {f g : F[X]}
    (hf : f.Monic) (hg : g.Monic) (hfg : IsCoprime f g)
    (hfIdentity : ∀ h : F[X], hermiteSignature f h hf = rootSignSum f h)
    (hgIdentity : ∀ h : F[X], hermiteSignature g h hg = rootSignSum g h) :
    ∀ h : F[X],
      hermiteSignature (f * g) h (hf.mul hg) = rootSignSum (f * g) h := by
  intro h
  rw [hermiteSignature_mul h hf hg hfg, hfIdentity h, hgIdentity h,
    rootSignSum_mul h hf.ne_zero hg.ne_zero hfg]

end OptimalConvergenceRates.KrivineStengle

end
