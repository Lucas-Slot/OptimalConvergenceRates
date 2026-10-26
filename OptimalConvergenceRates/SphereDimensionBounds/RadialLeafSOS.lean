import OptimalConvergenceRates.SphereDimensionBounds.RadialNodeSOS

/-! Explicit scalar leaf squares and diagonal quartic padding. -/
noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.RadialLeafSOS
open scoped BigOperators
open MvPolynomial ChebyshevSOSKernel
abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

/-- The off-diagonal part of the square of a sum of squares has the
literal product roots x_i*x_j. -/
theorem off_diagonal_identity {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → Poly n) :
    (∑i,∑j,if i=j then 0 else (x i*x j)^2)+(∑i,x i^4)=(∑i,x i^2)^2:=by
  have hpoint (i j:ι):(if i=j then 0 else (x i*x j)^2)+(if i=j then x i^4 else 0)=x i^2*x j^2:=by
    by_cases h:i=j
    · subst j;simp;ring
    · simp [h,mul_pow]
  have hs:=congrArg (fun f:ι→ι→Poly n=>∑i,∑j,f i j) (funext fun i=>funext fun j=>hpoint i j)
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    ←Finset.mul_sum,←Finset.sum_mul,pow_two] using hs

/-- Actual quadratic roots for every diagonal slack with coefficients at
most one, including singular and empty index families. -/
theorem diagonal_slack_boundedSOS {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Poly n) (hx : ∀ i, (x i).totalDegree ≤ 1) (c : ι→ℝ) (hc : ∀ i, c i ≤ 1) :
    BoundedSOS 2 ((∑i,x i^2)^2-∑i,C (c i)*x i^4):=by
  have hd:BoundedSOS 2 (∑i,C (1-c i)*x i^4):=by
    apply BoundedSOS.sum
    intro i _
    have hp:(x i^2).totalDegree≤2:=(totalDegree_pow _ _).trans (by have hi:=hx i;omega)
    simpa only [←pow_mul] using (BoundedSOS.square (x i^2) hp).scale (1-c i) (sub_nonneg.mpr (hc i))
  have ho:BoundedSOS 2 (∑i,∑j,if i=j then 0 else (x i*x j)^2):=by
    apply BoundedSOS.sum
    intro i _
    apply BoundedSOS.sum
    intro j _
    split_ifs
    · exact BoundedSOS.zero
    · exact BoundedSOS.square _ ((totalDegree_mul _ _).trans (by have hi:=hx i;have hj:=hx j;omega))
  have hid:((∑i,x i^2)^2-∑i,C (c i)*x i^4)=
      (∑i,C (1-c i)*x i^4)+(∑i,∑j,if i=j then 0 else (x i*x j)^2):=by
    rw [←off_diagonal_identity x]
    simp only [map_sub,map_one,sub_mul,one_mul,Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact hd.add ho

/-- Leaf cubic completion with its actual quadratic roots. Zero spectral
coefficients are allowed; their leaf cubic is zero as well. -/
theorem leaf_boundedSOS {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Poly n) (hx : ∀ i, (x i).totalDegree ≤ 1) (z : Poly n) (hz : z.totalDegree ≤ 1)
    (a gamma : ι→ℝ) (hg : ∀ i, |gamma i| ≤ 2) :
    BoundedSOS 2 (z^2*(∑i,C (a i)^2*x i^2)+
      z*(∑i,C (a i*gamma i)*x i^3)+(∑i,x i^2)^2):=by
  have hq:BoundedSOS 2 (∑i,(z*C (a i)*x i+C (gamma i/2)*x i^2)^2):=by
    apply BoundedSOS.of_family
    intro i
    apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by
        have ht:((z*C (a i)):Poly n).totalDegree≤1:=
          (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,add_zero] using hz)
        have hi:=hx i
        omega)
    · exact (totalDegree_mul _ _).trans (by
        have ht:(x i^2).totalDegree≤2:=(totalDegree_pow _ _).trans (by have hi:=hx i;omega)
        simpa only [totalDegree_C,zero_add] using ht)
  have hc:∀i,(gamma i/2)^2≤1:=by
    intro i
    have hh:=abs_le.mp (hg i)
    nlinarith
  have hs:=diagonal_slack_boundedSOS x hx (fun i=>(gamma i/2)^2) hc
  have hpoint(i:ι):(z*C (a i)*x i+C (gamma i/2)*x i^2)^2=
      z^2*C (a i)^2*x i^2+z*C (a i*gamma i)*x i^3+C ((gamma i/2)^2)*x i^4:=by
    have half:(2:Poly n)*C (gamma i/2)=C (gamma i):=by
      rw [show (2:Poly n)=C (2:ℝ) from rfl,←map_mul]
      congr 1
      ring
    simp only [map_pow,map_mul]
    linear_combination (z*C (a i)*x i^3)*half
  have hid:(z^2*(∑i,C (a i)^2*x i^2)+z*(∑i,C (a i*gamma i)*x i^3)+(∑i,x i^2)^2)=
      (∑i,(z*C (a i)*x i+C (gamma i/2)*x i^2)^2)+
        ((∑i,x i^2)^2-∑i,C ((gamma i/2)^2)*x i^4):=by
    simp_rw [hpoint]
    simp only [mul_assoc,Finset.sum_add_distrib,←Finset.mul_sum]
    ring
  rw [hid]
  exact hq.add hs

end OptimalConvergenceRates.SphereDimensionBounds.RadialLeafSOS
