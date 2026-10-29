import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.FiniteMatrixVariance

/-! Exact rectangular radial-node SOS completion with its full root-degree
budget. The actual matrix smoothing certificate is a separate supplier. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace RadialNodeSOS
open scoped BigOperators Matrix
open MvPolynomial ChebyshevSOSKernel FiniteMatrixVariance

abbrev Poly (n : ℕ):=MvPolynomial (Fin n) ℝ

theorem quadraticForm_smul {n d : ℕ} (p : Poly n) (M : Matrix (Fin d) (Fin d) (Poly n)) (x : Fin d
  → Poly n) :
    quadraticForm (p•M) x=p*quadraticForm M x:=by
  simp only [quadraticForm,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticForm_sub {n d : ℕ} (M N : Matrix (Fin d) (Fin d) (Poly n)) (x : Fin d → Poly n) :
    quadraticForm (M-N) x=quadraticForm M x-quadraticForm N x:=by
  simp only [quadraticForm,Matrix.sub_apply,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem quadraticForm_identity {n d : ℕ} (x : Fin d → Poly n) :
    quadraticForm (1:Matrix (Fin d) (Fin d) (Poly n)) x=∑ i,x i^2:=by
  simp [quadraticForm,Matrix.one_apply,pow_two]

theorem quadraticForm_dot {n d : ℕ} (M : Matrix (Fin d) (Fin d) (Poly n)) (x : Fin d → Poly n) :
    quadraticForm M x=dotProduct x (M*ᵥx):=by
  simp only [quadraticForm,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

theorem quadraticForm_gram {n d e : ℕ} (C0 : Matrix (Fin d) (Fin e) (Poly n)) (x : Fin d → Poly n) :
    quadraticForm (C0*C0.transpose) x=∑ i,(∑ j,C0 j i*x j)^2:=by
  rw [quadraticForm_dot,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec]
  have hv:Matrix.vecMul x C0=C0.transpose*ᵥx:=by
    funext i
    simp only [Matrix.vecMul,Matrix.mulVec,dotProduct,Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hv]
  simp only [dotProduct,Matrix.mulVec,Matrix.transpose_apply,pow_two]

/-- Degree-preserving coordinate inclusion transports an actual matrix
SOS root family to the ambient longitudinal/transverse variables. -/
theorem matrixSOS_rename {n m d r : ℕ} {M : Matrix (Fin d) (Fin d) (Poly n)}
    (hM : BoundedMatrixSOS r M) (f : Fin n → Fin m) :
    BoundedMatrixSOS r (fun i j↦rename f (M i j)):=by
  obtain ⟨k,v,hv,rfl⟩:=hM
  have hid:(fun i j↦rename f ((∑ t,outer (v t)) i j))=
      ∑ t,outer (fun i↦rename f (v t i)):=by
    apply Matrix.ext
    intro i j
    simp only [Matrix.sum_apply,map_sum,outer,map_mul]
  rw [hid]
  apply BoundedMatrixSOS.of_family
  intro t i
  exact (totalDegree_rename_le f _).trans (hv t i)

def completedRoot {n d e : ℕ} (s : ℕ) (R z : Poly n)
    (C0 : Matrix (Fin d) (Fin e) (Poly n)) (D : Fin d → Poly n) (v : Fin e → Poly n) (i : Fin
      e):Poly n:=
  z*(∑ j,C0 j i*D j)+R^s*v i

theorem completedRoot_degree {n d e s : ℕ} (hs : 1 ≤ s) (R z : Poly n)
    (hR : R.totalDegree ≤ 2) (hz : z.totalDegree ≤ 1)
    (C0 : Matrix (Fin d) (Fin e) (Poly n)) (hC : ∀ i j, (C0 i j).totalDegree ≤ 2 * s - 1)
    (D : Fin d → Poly n) (hD : ∀ i, (D i).totalDegree ≤ 1)
    (v : Fin e → Poly n) (hv : ∀ i, (v i).totalDegree ≤ 1) (i : Fin e) :
    (completedRoot s R z C0 D v i).totalDegree≤2*s+1:=by
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    have hsum:(∑ j,C0 j i*D j).totalDegree≤2*s:=by
      apply totalDegree_finsetSum_le
      intro j _
      exact (totalDegree_mul _ _).trans (by have hc:=hC j i;have hd:=hD j;omega)
    omega
  · apply (totalDegree_mul _ _).trans
    have hp:(R^s).totalDegree≤2*s:=(totalDegree_pow _ _).trans (by nlinarith)
    have hi:=hv i
    omega

/-- The input radius is an actual sum of linear squares, so all its
powers have explicit polynomial SOS factors. -/
theorem radius_power_boundedSOS {n s : ℕ} {R : Poly n} (hR : BoundedSOS 1 R) :
    BoundedSOS s (R^s):=by
  simpa only [Nat.one_mul] using BoundedSOS.pow hR s

/-- Exact rectangular completion identity before applying any norm or
pointwise matrix argument. -/
theorem radial_completion_identity {n d e s : ℕ} (hs : 1 ≤ s) (beta : ℝ) (R z w q : Poly n)
    (C0 : Matrix (Fin d) (Fin e) (Poly n)) (D : Fin d → Poly n) (v : Fin e → Poly n)
    (hpair : (∑ i, D i * (∑ j, C0 i j * v j)) = R ^ (s - 1) * q) :
    quadraticForm (R^(s+1)•((C beta*R^(2*s-2)*w)•(1:Matrix (Fin d) (Fin d) (Poly
      n))-C0*C0.transpose))
        (fun i↦z*D i)+R^(s+1)*(∑ i,completedRoot s R z C0 D v i^2)=
      C beta*z^2*R^(3*s-1)*w*(∑ i,D i^2)+2*z*R^(3*s)*q+R^(3*s+1)*(∑ i,v i^2):=by
  let ell:Fin e→Poly n:=fun i↦∑ j,C0 j i*D j
  have hpair':(∑ i,ell i*v i)=R^(s-1)*q:=by
    rw [←hpair]
    dsimp [ell]
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hzD:(∑ i,(z*D i)^2)=z^2*(∑ i,D i^2):=by simp only [mul_pow,Finset.mul_sum]
  have hzC:(∑ i,(∑ j,C0 j i*(z*D j))^2)=z^2*(∑ i,ell i^2):=by
    have he(i:Fin e):(∑ j,C0 j i*(z*D j))=z*ell i:=by
      dsimp [ell]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [he]
    simp only [mul_pow,Finset.mul_sum]
  have hy:(∑ i,completedRoot s R z C0 D v i^2)=
      z^2*(∑ i,ell i^2)+2*z*R^s*(∑ i,ell i*v i)+(R^s)^2*(∑ i,v i^2):=by
    have he(i:Fin e):completedRoot s R z C0 D v i^2=
        z^2*ell i^2+2*z*R^s*(ell i*v i)+(R^s)^2*v i^2:=by
      dsimp [completedRoot,ell]
      ring
    simp_rw [he]
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
  rw [quadraticForm_smul,quadraticForm_sub,quadraticForm_smul,quadraticForm_identity,
    quadraticForm_gram,hzD,hzC,hy,hpair']
  have h1:R^(s+1)*R^(2*s-2)=R^(3*s-1):=by rw [←pow_add];congr 1;omega
  have h2:R^(s+1)*R^s*R^(s-1)=R^(3*s):=by rw [←pow_add,←pow_add];congr 1;omega
  have h3:R^(s+1)*(R^s)^2=R^(3*s+1):=by rw [←pow_mul,←pow_add];congr 1;omega
  calc
    _=C beta*z^2*(R^(s+1)*R^(2*s-2))*w*(∑ i,D i^2)+
        2*z*(R^(s+1)*R^s*R^(s-1))*q+(R^(s+1)*(R^s)^2)*(∑ i,v i^2):=by ring
    _=_:=by rw [h1,h2,h3]

/-- The actual matrix certificate yields actual scalar SOS roots after
contraction and the completed square, with the full3s+2 budget. -/
theorem radial_node_boundedSOS {n d e s : ℕ} (hs : 1 ≤ s) (beta : ℝ) (R z w q : Poly n)
    (hR : R.totalDegree ≤ 2) (hRsos : BoundedSOS 1 R) (hz : z.totalDegree ≤ 1)
    (C0 : Matrix (Fin d) (Fin e) (Poly n)) (hC : ∀ i j, (C0 i j).totalDegree ≤ 2 * s - 1)
    (D : Fin d → Poly n) (hD : ∀ i, (D i).totalDegree ≤ 1)
    (v : Fin e → Poly n) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (hpair : (∑ i, D i * (∑ j, C0 i j * v j)) = R ^ (s - 1) * q)
    (hM : BoundedMatrixSOS (3 * s)
      (R ^ (s + 1) • ((C beta * R ^ (2 * s - 2) * w) • (1 : Matrix (Fin d) (Fin d) (Poly n)) - C0
        * C0.transpose))) :
    BoundedSOS (3*s+2) (C beta*z^2*R^(3*s-1)*w*(∑ i,D i^2)+
      2*z*R^(3*s)*q+R^(3*s+1)*(∑ i,v i^2)):=by
  have hx:∀ i,(z*D i).totalDegree≤2:=by
    intro i
    exact (totalDegree_mul _ _).trans (by have hi:=hD i;omega)
  have hc:=hM.contract (fun i↦z*D i) hx
  have hy:BoundedSOS (2*s+1) (∑ i,completedRoot s R z C0 D v i^2):=
    BoundedSOS.of_family _ (completedRoot_degree hs R z hR hz C0 hC D hD v hv)
  have hrad:BoundedSOS (s+1) (R^(s+1)):=radius_power_boundedSOS hRsos
  have hproduct:=hrad.mul hy
  have hproduct':BoundedSOS (3*s+2) (R^(s+1)*(∑ i,completedRoot s R z C0 D v i^2)):=by
    convert hproduct using 1
    omega
  have hsum:=hc.add hproduct'
  rwa [radial_completion_identity hs beta R z w q C0 D v hpair] at hsum

/-- The cubic polarization factors three are retained exactly by replacing
the longitudinal variable by three halves of itself. -/
theorem radial_node_three_boundedSOS {n d e s : ℕ} (hs : 1 ≤ s) (beta : ℝ) (R z w q : Poly n)
    (hR : R.totalDegree ≤ 2) (hRsos : BoundedSOS 1 R) (hz : z.totalDegree ≤ 1)
    (C0 : Matrix (Fin d) (Fin e) (Poly n)) (hC : ∀ i j, (C0 i j).totalDegree ≤ 2 * s - 1)
    (D : Fin d → Poly n) (hD : ∀ i, (D i).totalDegree ≤ 1)
    (v : Fin e → Poly n) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (hpair : (∑ i, D i * (∑ j, C0 i j * v j)) = R ^ (s - 1) * q)
    (hM : BoundedMatrixSOS (3 * s)
      (R ^ (s + 1) • ((C beta * R ^ (2 * s - 2) * w) • (1 : Matrix (Fin d) (Fin d) (Poly n)) - C0
        * C0.transpose))) :
    BoundedSOS (3*s+2) (C ((9:ℝ)*beta/4)*z^2*R^(3*s-1)*w*(∑ i,D i^2)+
      3*z*R^(3*s)*q+R^(3*s+1)*(∑ i,v i^2)):=by
  have hz' : (C ((3:ℝ)/2)*z).totalDegree≤1 :=
    (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hz)
  have h:=radial_node_boundedSOS hs beta R (C ((3:ℝ)/2)*z) w q hR hRsos hz'
    C0 hC D hD v hv hpair hM
  have hc : C ((9:ℝ)*beta/4)=(C beta:Poly n)*C ((3:ℝ)/2)^2 :=by
    rw [←map_pow,←map_mul]
    congr 1
    ring
  have hhalf : (2:Poly n)*C ((3:ℝ)/2)=3 :=by
    rw [show (2:Poly n)=C (2:ℝ) from rfl,←map_mul]
    norm_num
    rfl
  have hmiddle : 2*(C ((3:ℝ)/2)*z)*R^(3*s)*q=3*z*R^(3*s)*q :=by
    linear_combination (z*R^(3*s)*q)*hhalf
  rw [hmiddle] at h
  rw [hc]
  convert h using 1
  ring

/-- Both genuine mixed-node certificates combine with constants6084 and
1521, hence7605; no mixed cubic is dropped. -/
theorem radial_node_pair_boundedSOS {n d e f s : ℕ} (hs : 1 ≤ s) (R z w q t : Poly n)
    (hR : R.totalDegree ≤ 2) (hRsos : BoundedSOS 1 R) (hz : z.totalDegree ≤ 1)
    (C0 : Matrix (Fin d) (Fin e) (Poly n)) (hC : ∀ i j, (C0 i j).totalDegree ≤ 2 * s - 1)
    (F0 : Matrix (Fin d) (Fin f) (Poly n)) (hF : ∀ i j, (F0 i j).totalDegree ≤ 2 * s - 1)
    (D : Fin d → Poly n) (hD : ∀ i, (D i).totalDegree ≤ 1)
    (v : Fin e → Poly n) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (u : Fin f → Poly n) (hu : ∀ i, (u i).totalDegree ≤ 1)
    (hpairq : (∑ i, D i * (∑ j, C0 i j * v j)) = R ^ (s - 1) * q)
    (hpairt : (∑ i, D i * (∑ j, F0 i j * u j)) = R ^ (s - 1) * t)
    (hMC : BoundedMatrixSOS (3 * s)
      (R ^ (s + 1) • ((C 2704 * R ^ (2 * s - 2) * w) • (1 : Matrix (Fin d) (Fin d) (Poly n)) - C0
        * C0.transpose)))
    (hMF : BoundedMatrixSOS (3 * s)
      (R ^ (s + 1) • ((C 676 * R ^ (2 * s - 2) * w) • (1 : Matrix (Fin d) (Fin d) (Poly n)) - F0 *
        F0.transpose))) :
    BoundedSOS (3*s+2) (C 7605*z^2*R^(3*s-1)*w*(∑ i,D i^2)+
      z*R^(3*s)*(3*q+3*t)+R^(3*s+1)*((∑ i,v i^2)+(∑ i,u i^2))):=by
  have hq:=radial_node_three_boundedSOS hs 2704 R z w q hR hRsos hz
    C0 hC D hD v hv hpairq hMC
  have ht:=radial_node_three_boundedSOS hs 676 R z w t hR hRsos hz
    F0 hF D hD u hu hpairt hMF
  norm_num at hq ht
  simp only [map_ofNat] at hq ht ⊢
  convert hq.add ht using 1
  ring

end RadialNodeSOS
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
