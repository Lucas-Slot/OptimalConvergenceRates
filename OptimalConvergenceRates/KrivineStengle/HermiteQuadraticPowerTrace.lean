import OptimalConvergenceRates.KrivineStengle.HermiteQuadratic

noncomputable section

open Polynomial

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {F : Type u} [Field F]


private theorem trace_aeval_mul_self_nilpotent
    {q : F[X]} (hqMonic : q.Monic) {n : ℕ} (t : F[X]) :
    Algebra.trace F (AdjoinRoot (q ^ n))
        (aeval (AdjoinRoot.root (q ^ n)) (q * t)) = 0 := by
  let hf : (q ^ n).Monic := hqMonic.pow n
  letI : Module.Free F (AdjoinRoot (q ^ n)) := hf.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot (q ^ n)) :=
    (AdjoinRoot.powerBasis' hf).finite
  have hqnil : IsNilpotent (aeval (AdjoinRoot.root (q ^ n)) q) := by
    refine ⟨n, ?_⟩
    rw [← map_pow, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hprod : IsNilpotent
      (aeval (AdjoinRoot.root (q ^ n)) q *
        aeval (AdjoinRoot.root (q ^ n)) t) :=
    (Commute.all _ _).isNilpotent_mul_right hqnil
  rw [map_mul]
  exact (Algebra.isNilpotent_trace_of_isNilpotent hprod).eq_zero

theorem trace_aeval_adjoinRoot_quadratic_pow {q : F[X]}
    (hqMonic : q.Monic) (hqDegree : q.natDegree = 2)
    (h : F[X]) {n : ℕ} (hn : 0 < n) :
    Algebra.trace F (AdjoinRoot (q ^ n))
        (aeval (AdjoinRoot.root (q ^ n)) h) =
      n • Algebra.trace F (AdjoinRoot q)
        (aeval (AdjoinRoot.root q) h) := by
  let hqnMonic : (q ^ n).Monic := hqMonic.pow n
  letI : Module.Free F (AdjoinRoot (q ^ n)) := hqnMonic.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot (q ^ n)) :=
    (AdjoinRoot.powerBasis' hqnMonic).finite
  letI : Module.Free F (AdjoinRoot q) := hqMonic.free_adjoinRoot
  letI : Module.Finite F (AdjoinRoot q) :=
    (AdjoinRoot.powerBasis' hqMonic).finite
  let r := h %ₘ q
  let d := h /ₘ q
  have hrDegree : r.natDegree ≤ 1 := by
    have hqOne : q ≠ 1 := by
      intro heq
      have hdegree := hqDegree
      simp [heq] at hdegree
    have hlt := natDegree_modByMonic_lt h hqMonic hqOne
    dsimp only [r]
    rw [hqDegree] at hlt
    omega
  have hr : r = C (r.coeff 1) * X + C (r.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one hrDegree
  have hdecomp : r + q * d = h := modByMonic_add_div h hqMonic
  have htraceN :
      Algebra.trace F (AdjoinRoot (q ^ n))
          (aeval (AdjoinRoot.root (q ^ n)) h) =
        Algebra.trace F (AdjoinRoot (q ^ n))
          (aeval (AdjoinRoot.root (q ^ n)) r) := by
    conv_lhs => rw [← hdecomp]
    rw [map_add, map_mul, map_add]
    have hz := trace_aeval_mul_self_nilpotent hqMonic (n := n) d
    rw [map_mul] at hz
    rw [hz, add_zero]
  have htraceOne :
      Algebra.trace F (AdjoinRoot (q ^ n)) 1 =
        n • Algebra.trace F (AdjoinRoot q) 1 := by
    rw [← map_one (algebraMap F (AdjoinRoot (q ^ n))),
      Algebra.trace_algebraMap,
      ← map_one (algebraMap F (AdjoinRoot q)), Algebra.trace_algebraMap]
    rw [(AdjoinRoot.powerBasis' hqnMonic).finrank,
      (AdjoinRoot.powerBasis' hqMonic).finrank]
    simp [hqMonic.natDegree_pow, hqDegree, nsmul_eq_mul]
  have htraceRoot :
      Algebra.trace F (AdjoinRoot (q ^ n)) (AdjoinRoot.root (q ^ n)) =
        n • Algebra.trace F (AdjoinRoot q) (AdjoinRoot.root q) := by
    have hnzero : q ^ n ≠ 0 := pow_ne_zero n hqMonic.ne_zero
    have hqzero : q ≠ 0 := hqMonic.ne_zero
    letI : Nontrivial (AdjoinRoot (q ^ n)) := AdjoinRoot.nontrivial _ (by
      rw [degree_eq_natDegree hnzero, hqMonic.natDegree_pow, hqDegree]
      simp [Nat.ne_of_gt hn])
    letI : Nontrivial (AdjoinRoot q) := AdjoinRoot.nontrivial _ (by
      rw [degree_eq_natDegree hqzero, hqDegree]
      norm_num)
    rw [show AdjoinRoot.root (q ^ n) =
        (AdjoinRoot.powerBasis hnzero).gen by simp]
    rw [(AdjoinRoot.powerBasis hnzero).trace_gen_eq_nextCoeff_minpoly]
    rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic hqnMonic]
    rw [show AdjoinRoot.root q = (AdjoinRoot.powerBasis hqzero).gen by simp]
    rw [(AdjoinRoot.powerBasis hqzero).trace_gen_eq_nextCoeff_minpoly]
    rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic hqMonic,
      hqMonic.nextCoeff_pow]
    module
  rw [htraceN]
  conv_rhs => rw [← hdecomp]
  rw [map_add, map_mul, map_add]
  simp [AdjoinRoot.aeval_eq]
  rw [hr]
  simp only [map_add, map_mul, AdjoinRoot.mk_C,
    AdjoinRoot.mk_X]
  have hrootMulN (c : F) :
      Algebra.trace F (AdjoinRoot (q ^ n))
          (algebraMap F _ c * AdjoinRoot.root (q ^ n)) =
        c * Algebra.trace F (AdjoinRoot (q ^ n)) (AdjoinRoot.root (q ^ n)) := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hrootMulOne (c : F) :
      Algebra.trace F (AdjoinRoot q) (algebraMap F _ c * AdjoinRoot.root q) =
        c * Algebra.trace F (AdjoinRoot q) (AdjoinRoot.root q) := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hconstN (c : F) :
      Algebra.trace F (AdjoinRoot (q ^ n)) (algebraMap F _ c) =
        c * Algebra.trace F (AdjoinRoot (q ^ n)) 1 := by
    rw [Algebra.trace_algebraMap, ← map_one (algebraMap F (AdjoinRoot (q ^ n))),
      Algebra.trace_algebraMap]
    simp [nsmul_eq_mul]
    ring
  have hconstOne (c : F) :
      Algebra.trace F (AdjoinRoot q) (algebraMap F _ c) =
        c * Algebra.trace F (AdjoinRoot q) 1 := by
    rw [Algebra.trace_algebraMap, ← map_one (algebraMap F (AdjoinRoot q)),
      Algebra.trace_algebraMap]
    simp [nsmul_eq_mul]
    ring
  simp only [← AdjoinRoot.algebraMap_eq]
  rw [hrootMulN, hconstN, hrootMulOne, hconstOne, htraceOne, htraceRoot]
  simp only [nsmul_eq_mul]
  ring

end OptimalConvergenceRates.KrivineStengle

end
