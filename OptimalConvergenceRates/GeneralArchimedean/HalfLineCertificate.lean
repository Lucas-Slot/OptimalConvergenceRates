/-
  A half-line Markov--Lukacs decomposition derived from global univariate
  SOS and the reusable even/odd contraction API.
-/
import OptimalConvergenceRates.BasicNotions.UnivariateParity
import OptimalConvergenceRates.GeneralArchimedean.PositiveCoefficientCertificate
import OptimalConvergenceRates.MarkovLukacz.UnivariateSOS
import Mathlib.Order.Interval.Set.Infinite

noncomputable section

open Polynomial Finset

namespace OptimalConvergenceRates
namespace GeneralArchimedean

open UnivariateParity

/-- An SOS certificate for a polynomial nonnegative on (-infinity,U]. -/
structure HalfLineCertificate (U : ℝ) (p : Polynomial ℝ) where
  sigmaZero : Polynomial ℝ
  sigmaBoundary : Polynomial ℝ
  isSOSZero : IsSOSUni sigmaZero
  isSOSBoundary : IsSOSUni sigmaBoundary
  degreeZero_le : sigmaZero.natDegree ≤ 2 * p.natDegree
  degreeBoundary_le : sigmaBoundary.natDegree ≤ 2 * p.natDegree
  identity :
    p = sigmaZero + (Polynomial.C U - Polynomial.X) * sigmaBoundary

/-- Every univariate polynomial nonnegative on the left half-line admits the
ordinary two-term half-line quadratic-module representation. -/
theorem halfLineCertificate_nonempty
    (U : ℝ) (p : Polynomial ℝ)
    (hp : ∀ u : ℝ, u ≤ U → 0 ≤ p.eval u) :
    Nonempty (HalfLineCertificate U p) := by
  let q : Polynomial ℝ :=
    p.comp (Polynomial.C U - Polynomial.X ^ 2)
  have hq : ∀ t : ℝ, 0 ≤ q.eval t := by
    intro t
    dsimp [q]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact hp _ (by nlinarith [sq_nonneg t])
  have hreflectSquareDegree :
      (Polynomial.C U - Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by
    calc
      (Polynomial.C U - Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤
          max (Polynomial.C U : Polynomial ℝ).natDegree
            (Polynomial.X ^ 2 : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ ≤ 2 := by simp
  have hqDegree : q.natDegree ≤ 2 * p.natDegree := by
    dsimp [q]
    calc
      (p.comp (Polynomial.C U - Polynomial.X ^ 2)).natDegree ≤
          p.natDegree *
            (Polynomial.C U - Polynomial.X ^ 2 : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ p.natDegree * 2 :=
        Nat.mul_le_mul_left p.natDegree hreflectSquareDegree
      _ = 2 * p.natDegree := by omega
  obtain ⟨k, f, hf, hfDegree⟩ :=
    (IsSOSUni_of_nonneg q hq).exists_degree_controlled
  have hfDegree' (i : Fin k) : (f i).natDegree ≤ p.natDegree :=
    Nat.le_of_mul_le_mul_left ((hfDegree i).trans hqDegree) (by omega)
  let e : Fin k → Polynomial ℝ := fun i => evenContract (f i)
  let o : Fin k → Polynomial ℝ := fun i => oddContract (f i)
  let reflect : Polynomial ℝ := Polynomial.C U - Polynomial.X
  let sigmaZero : Polynomial ℝ :=
    ∑ i : Fin k, ((e i).comp reflect) ^ 2
  let sigmaBoundary : Polynomial ℝ :=
    ∑ i : Fin k, ((o i).comp reflect) ^ 2
  have hsosZero : IsSOSUni sigmaZero := by
    exact ⟨k, fun i => (e i).comp reflect, rfl⟩
  have hreflectDegree : reflect.natDegree ≤ 1 := by
    dsimp [reflect]
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have heDegree (i : Fin k) : (e i).natDegree ≤ p.natDegree :=
    (evenContract_natDegree_le (f i)).trans (hfDegree' i)
  have hoDegree (i : Fin k) : (o i).natDegree ≤ p.natDegree :=
    (oddContract_natDegree_le (f i)).trans (hfDegree' i)
  have hzeroDegree : sigmaZero.natDegree ≤ 2 * p.natDegree := by
    dsimp [sigmaZero]
    apply Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    intro i hi
    have hcomp : ((e i).comp reflect).natDegree ≤ p.natDegree := by
      calc
        ((e i).comp reflect).natDegree ≤
            (e i).natDegree * reflect.natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ p.natDegree * 1 :=
          Nat.mul_le_mul (heDegree i) hreflectDegree
        _ = p.natDegree := by omega
    exact Polynomial.natDegree_pow_le.trans
      (Nat.mul_le_mul_left 2 hcomp)
  have hboundaryDegree :
      sigmaBoundary.natDegree ≤ 2 * p.natDegree := by
    dsimp [sigmaBoundary]
    apply Polynomial.natDegree_sum_le_of_forall_le Finset.univ
    intro i hi
    have hcomp : ((o i).comp reflect).natDegree ≤ p.natDegree := by
      calc
        ((o i).comp reflect).natDegree ≤
            (o i).natDegree * reflect.natDegree :=
          Polynomial.natDegree_comp_le
        _ ≤ p.natDegree * 1 :=
          Nat.mul_le_mul (hoDegree i) hreflectDegree
        _ = p.natDegree := by omega
    exact Polynomial.natDegree_pow_le.trans
      (Nat.mul_le_mul_left 2 hcomp)
  have hsosBoundary : IsSOSUni sigmaBoundary := by
    exact ⟨k, fun i => (o i).comp reflect, rfl⟩
  refine ⟨⟨sigmaZero, sigmaBoundary, hsosZero, hsosBoundary,
    hzeroDegree, hboundaryDegree, ?_⟩⟩
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Iic_infinite U).mono
  intro u hu
  let t : ℝ := Real.sqrt (U - u)
  have hdiff : 0 ≤ U - u := sub_nonneg.mpr hu
  have ht_sq : t ^ 2 = U - u := Real.sq_sqrt hdiff
  have hqpos : q.eval t = p.eval u := by
    dsimp [q]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [ht_sq]
    congr 1
    ring
  have hqneg : q.eval (-t) = p.eval u := by
    dsimp [q]
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, neg_sq]
    rw [ht_sq]
    congr 1
    ring
  have hfpos := congrArg (fun z : Polynomial ℝ => z.eval t) hf
  have hfneg := congrArg (fun z : Polynomial ℝ => z.eval (-t)) hf
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_pow] at hfpos hfneg
  have hterm : ∀ i : Fin k,
      ((f i).eval t ^ 2 + (f i).eval (-t) ^ 2) / 2 =
        (e i).eval (U - u) ^ 2 +
          (U - u) * (o i).eval (U - u) ^ 2 := by
    intro i
    have hpos := eval_evenContract_add_oddContract (f i) t
    have hneg := eval_evenContract_add_oddContract (f i) (-t)
    simp only [neg_sq] at hneg
    rw [ht_sq] at hpos hneg
    dsimp [e, o]
    rw [hpos, hneg]
    nlinarith [ht_sq]
  have havg :
      p.eval u =
        ∑ i : Fin k,
          ((e i).eval (U - u) ^ 2 +
            (U - u) * (o i).eval (U - u) ^ 2) := by
    calc
      p.eval u = (q.eval t + q.eval (-t)) / 2 := by rw [hqpos, hqneg]; ring
      _ = ((∑ i : Fin k, (f i).eval t ^ 2) +
          (∑ i : Fin k, (f i).eval (-t) ^ 2)) / 2 := by
            rw [← hfpos, ← hfneg]
      _ = ∑ i : Fin k,
          (((f i).eval t ^ 2 + (f i).eval (-t) ^ 2) / 2) := by
            rw [← Finset.sum_add_distrib]
            simp only [div_eq_mul_inv]
            rw [Finset.sum_mul]
      _ = ∑ i : Fin k,
          ((e i).eval (U - u) ^ 2 +
            (U - u) * (o i).eval (U - u) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i
  change p.eval u =
    (sigmaZero + (Polynomial.C U - Polynomial.X) * sigmaBoundary).eval u
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X]
  dsimp [sigmaZero, sigmaBoundary, reflect]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_pow,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X]
  rw [havg]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]

variable {n m : ℕ}


/-- Degree-controlled substitution of a half-line certificate. -/
theorem HalfLineCertificate.subst_mem_at
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {U : ℝ} {p : Polynomial ℝ}
    (cert : HalfLineCertificate U p)
    (a : MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hUa : MvPolynomial.C U - a ∈ GenQuadraticModule g r) :
    polynomialSubst a p ∈ GenQuadraticModule g
      (r + 2 * p.natDegree * a.totalDegree) := by
  let d := 2 * p.natDegree * a.totalDegree
  have hzeroDegree :
      (polynomialSubst a cert.sigmaZero).totalDegree ≤ d := by
    exact (polynomialSubst_totalDegree_le a cert.sigmaZero).trans
      (Nat.mul_le_mul_right a.totalDegree cert.degreeZero_le)
  have hzero : polynomialSubst a cert.sigmaZero ∈
      GenQuadraticModule g d :=
    genQuadraticModule_sos g
      (isSOS_polynomialSubst a cert.isSOSZero) hzeroDegree
  have hboundaryDegree :
      (polynomialSubst a cert.sigmaBoundary).totalDegree ≤ d := by
    exact (polynomialSubst_totalDegree_le a cert.sigmaBoundary).trans
      (Nat.mul_le_mul_right a.totalDegree cert.degreeBoundary_le)
  have hsos : IsSOS (polynomialSubst a cert.sigmaBoundary) :=
    isSOS_polynomialSubst a cert.isSOSBoundary
  have hboundaryRaw :=
    genQuadraticModule_sos_mul hsos hUa
  have hboundary : polynomialSubst a cert.sigmaBoundary *
        (MvPolynomial.C U - a) ∈
      GenQuadraticModule g (r + d) :=
    GenQuadraticModule_mono (Nat.add_le_add_left hboundaryDegree r)
      hboundaryRaw
  have hzero' := GenQuadraticModule_mono (Nat.le_add_left d r) hzero
  have hsum := GenQuadraticModule_add hzero' hboundary
  convert hsum using 1
  have hid := congrArg (Polynomial.aeval a) cert.identity
  simpa [polynomialSubst, map_add, map_mul, map_sub, mul_comm] using hid
/-- A half-line certificate may be substituted whenever the boundary
polynomial U-a belongs to the target quadratic module. -/
theorem HalfLineCertificate.subst_mem
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {U : ℝ} {p : Polynomial ℝ}
    (cert : HalfLineCertificate U p)
    (a : MvPolynomial (Fin n) ℝ)
    (hUa : QuadraticModuleMem g (MvPolynomial.C U - a)) :
    QuadraticModuleMem g (polynomialSubst a p) := by
  have hzero : QuadraticModuleMem g
      (polynomialSubst a cert.sigmaZero) :=
    QuadraticModuleMem.of_isSOS g
      (isSOS_polynomialSubst a cert.isSOSZero)
  have hsos : IsSOS (polynomialSubst a cert.sigmaBoundary) :=
    isSOS_polynomialSubst a cert.isSOSBoundary
  have hboundary : QuadraticModuleMem g
      ((MvPolynomial.C U - a) *
        polynomialSubst a cert.sigmaBoundary) := by
    simpa [mul_comm] using QuadraticModuleMem.sos_mul hsos hUa
  have hsum := hzero.add hboundary
  convert hsum using 1
  have hid := congrArg (Polynomial.aeval a) cert.identity
  simpa [polynomialSubst, map_add, map_mul, map_sub] using hid

end GeneralArchimedean
end OptimalConvergenceRates

end
