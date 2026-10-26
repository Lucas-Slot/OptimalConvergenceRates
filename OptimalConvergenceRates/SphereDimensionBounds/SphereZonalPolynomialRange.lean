import OptimalConvergenceRates.SphereDimensionBounds.SphereMoments
import OptimalConvergenceRates.SphereDimensionBounds.LinearFormPolarization
import OptimalConvergenceRates.SphereDimensionBounds.HomogeneousSOSFromSphere

/-! Actual polynomial range of zonal integration for the normalized
Euclidean sphere measure. Algebraic coefficient extraction and finite
polarization preserve the degree of the input, independently of the
degree of the scalar zonal kernel. -/

noncomputable section
namespace OptimalConvergenceRates.SphereDimensionBounds.SphereZonalPolynomialRange

open scoped BigOperators InnerProductSpace
open MeasureTheory MvPolynomial OptimalConvergenceRates.SphereDimensionBounds.Foundation SphereMeasure SphereMoments LinearFormPolarization

abbrev Poly (n : ℕ) := OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n

def toPoint {n : ℕ} (x : Fin n → ℝ) : E n := (WithLp.equiv 2 (Fin n → ℝ)).symm x

def normSquared {n : ℕ} (z : E n) : ℝ := ‖z‖^2

theorem linearFormPolynomial_inner {n : ℕ} (z x : E n) :
    eval (fun i => x i) (linearFormPolynomial (fun i => z i))=⟪z,x⟫_ℝ := by
  simp [linearFormPolynomial_eval,PiLp.inner_apply,RCLike.inner_apply,mul_comm]

theorem linearFormPolynomial_degree {n : ℕ} (z : Fin n → ℝ) :
    (linearFormPolynomial z).totalDegree≤1 := by
  apply (show (linearFormPolynomial z).IsHomogeneous 1 from ?_).totalDegree_le
  apply IsHomogeneous.sum
  intro i hi
  exact (isHomogeneous_X ℝ i).C_mul _

theorem totalDegree_coeff_mul_le_index {n : ℕ}
    (P Q : Polynomial (Poly n))
    (hP : ∀ d, (P.coeff d).totalDegree ≤ d)
    (hQ : ∀ d, (Q.coeff d).totalDegree ≤ d) (d : ℕ) :
    ((P*Q).coeff d).totalDegree≤d := by
  rw [Polynomial.coeff_mul]
  apply totalDegree_finsetSum_le
  intro ij hij
  exact (totalDegree_mul _ _).trans ((Nat.add_le_add (hP ij.1) (hQ ij.2)).trans
    (Finset.mem_antidiagonal.mp hij).le)

theorem totalDegree_coeff_pow_le_index {n : ℕ} (P : Polynomial (Poly n))
    (hP : ∀ d, (P.coeff d).totalDegree ≤ d) :
    ∀ q d,((P^q).coeff d).totalDegree≤d := by
  intro q
  induction q with
  | zero => intro d;cases d <;> simp [Polynomial.coeff_one]
  | succ q ih =>
      intro d
      rw [pow_succ]
      exact totalDegree_coeff_mul_le_index (P^q) P ih hP d

def radialLine {n : ℕ} (z : E n) : Polynomial (Poly n) :=
  Polynomial.C 1+
    Polynomial.C ((2:Poly n)*linearFormPolynomial (fun i => z i))*Polynomial.X+
    Polynomial.C (C (normSquared z))*Polynomial.X^2

theorem radialLine_coeff_degree {n : ℕ} (z : E n) (d : ℕ) :
    ((radialLine z).coeff d).totalDegree≤d := by
  rcases d with _|d
  · simp [radialLine,Polynomial.coeff_one]
  rcases d with _|d
  · rw [show (radialLine z).coeff 1=(2:Poly n)*linearFormPolynomial (fun i => z i) by
      simp [radialLine,Polynomial.coeff_one]]
    apply (totalDegree_mul _ _).trans
    simpa only [show (2:Poly n)=C (2:ℝ) from rfl,totalDegree_C,zero_add]
      using linearFormPolynomial_degree (fun i => z i)
  rcases d with _|d
  · simp [radialLine,Polynomial.coeff_one]
  · simp [radialLine,Polynomial.coeff_one]

def radialCoefficient {n : ℕ} (q d : ℕ) (z : E n) : Poly n := (radialLine z^q).coeff d

theorem radialCoefficient_degree {n : ℕ} (q d : ℕ) (z : E n) :
    (radialCoefficient q d z).totalDegree≤d :=
  totalDegree_coeff_pow_le_index (radialLine z) (radialLine_coeff_degree z) q d

theorem map_radialLine {n : ℕ} (x z : E n) (hx : ‖x‖ = 1) :
    Polynomial.map (eval (fun i => x i)) (radialLine z)=normLine x z := by
  simp [radialLine,normLine,hx,linearFormPolynomial_inner,real_inner_comm,normSquared]
  simp_rw [←map_mul]
  rw [←map_sum]
  congr 1

theorem radialCoefficient_eval {n q d : ℕ} (x z : E n) (hx : ‖x‖ = 1) :
    eval (fun i => x i) (radialCoefficient q d z)=((normLine x z)^q).coeff d := by
  rw [radialCoefficient,←Polynomial.coeff_map,Polynomial.map_pow,map_radialLine x z hx]

def evenMixedPolynomial {n : ℕ} (q d : ℕ) (base : Sphere n) (z : E n) : Poly n :=
  C ((Nat.choose (2*q) d:ℝ)⁻¹*linearMoment (2*q) base.1)*radialCoefficient q d z

theorem evenMixedPolynomial_degree {n : ℕ} (q d : ℕ) (base : Sphere n) (z : E n) :
    (evenMixedPolynomial q d base z).totalDegree≤d := by
  exact (totalDegree_mul _ _).trans (by
    simpa only [totalDegree_C,zero_add] using radialCoefficient_degree q d z)

theorem evenMixedPolynomial_eval {n q d : ℕ} (hn : 0 < n) (base : Sphere n)
    (z x : E n) (hd : d ≤ 2 * q) (hx : ‖x‖ = 1) :
    eval (fun i => x i) (evenMixedPolynomial q d base z)=mixedMoment (2*q-d) d x z := by
  have hchoose : (Nat.choose (2*q) d:ℝ)≠0 := by
    exact_mod_cast (Nat.choose_pos hd).ne'
  rw [evenMixedPolynomial,eval_mul,eval_C,radialCoefficient_eval x z hx]
  have hcoeff := choose_mul_mixedMoment hn base x z hd
  calc
    (Nat.choose (2*q) d:ℝ)⁻¹*linearMoment (2*q) base.1*((normLine x z)^q).coeff d=
        (Nat.choose (2*q) d:ℝ)⁻¹*((Nat.choose (2*q) d:ℝ)*mixedMoment (2*q-d) d x z) := by
      rw [mul_assoc,←hcoeff]
    _=mixedMoment (2*q-d) d x z := by field_simp

theorem mixedMoment_odd {n a b : ℕ} (hn : 0 < n) (x z : E n) (hab : Odd (a + b)) :
    mixedMoment a b x z=0 := by
  have hpoly : momentLine (a+b) x z=0 := by
    apply Polynomial.funext
    intro t
    rw [momentLine_eval hn,linearMoment_odd _ hab]
    simp
  have hb : b≤a+b := by omega
  have hcoeff := momentLine_coeff x z hb
  rw [hpoly,Polynomial.coeff_zero] at hcoeff
  have hchoose : (Nat.choose (a+b) b:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hb).ne'
  have hmul : (Nat.choose (a+b) b:ℝ)*mixedMoment a b x z=0 := by
    simpa only [Nat.add_sub_cancel_right] using hcoeff.symm
  exact (mul_eq_zero.mp hmul).resolve_left hchoose

theorem exists_mixedMoment_polynomial {n m d : ℕ} (hn : 0 < n) (base : Sphere n) (z : E n) :
    ∃ q : Poly n,q.totalDegree≤d ∧ ∀ x : Sphere n,
      eval (fun i => x.1 i) q=mixedMoment m d x.1 z := by
  by_cases hodd : Odd (m+d)
  · refine ⟨0,by simp,?_⟩
    intro x
    simpa only [map_zero] using (mixedMoment_odd hn x.1 z hodd).symm
  · rcases Nat.not_odd_iff_even.mp hodd with ⟨q,hq⟩
    have hsum : m+d=2*q := by omega
    have hd : d≤2*q := by omega
    refine ⟨evenMixedPolynomial q d base z,evenMixedPolynomial_degree q d base z,?_⟩
    intro x
    have hx : ‖x.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.2
    have heval := evenMixedPolynomial_eval hn base z x.1 hd hx
    rwa [show 2*q-d=m by omega] at heval

def zonalAverage {n : ℕ} (v : Poly n) (P : Polynomial ℝ) (x : E n) : ℝ :=
  ∫ y : Sphere n,eval (fun i => y.1 i) v*P.eval ⟪x,y.1⟫_ℝ ∂surface n

theorem continuous_sphere_eval {n : ℕ} (v : Poly n) :
    Continuous (fun y : Sphere n => eval (fun i => y.1 i) v) := by
  apply (MvPolynomial.continuous_eval v).comp
  apply continuous_pi
  intro i
  exact (PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _ : Fin n => ℝ) i).continuous.comp
    continuous_subtype_val

theorem integrable_zonalAverage {n : ℕ} (hn : 0 < n) (v : Poly n)
    (P : Polynomial ℝ) (x : E n) :
    Integrable (fun y : Sphere n => eval (fun i => y.1 i) v*P.eval ⟪x,y.1⟫_ℝ)
      (surface n) := by
  apply integrable_continuous hn
  exact (continuous_sphere_eval v).mul (by fun_prop)

theorem exists_homogeneous_monomial_range {n d m : ℕ} (hn : 0 < n) (base : Sphere n)
    (v : Poly n) (hv : v.IsHomogeneous d) :
    ∃ q : Poly n,q.totalDegree≤d ∧ ∀ x : Sphere n,
      eval (fun i => x.1 i) q=
        ∫ y : Sphere n,eval (fun i => y.1 i) v*⟪x.1,y.1⟫_ℝ^m ∂surface n := by
  obtain ⟨N,c,z,hvsum⟩ := exists_fin_sum_linearForm_pow_eq_of_isHomogeneous v hv
  let w : Fin N → Poly n := fun j => Classical.choose
    (exists_mixedMoment_polynomial (m:=m) (d:=d) hn base (toPoint (z j)))
  have hwdeg (j : Fin N) : (w j).totalDegree≤d :=
    (Classical.choose_spec (exists_mixedMoment_polynomial (m:=m) (d:=d) hn base (toPoint (z j)))).1
  have hweval (j : Fin N) (x : Sphere n) :
      eval (fun i => x.1 i) (w j)=mixedMoment m d x.1 (toPoint (z j)) :=
    (Classical.choose_spec (exists_mixedMoment_polynomial (m:=m) (d:=d) hn base (toPoint (z j)))).2 x
  refine ⟨∑ j,C (c j)*w j,?_,?_⟩
  · apply totalDegree_finsetSum_le
    intro j hj
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hwdeg j)
  · intro x
    calc
      eval (fun i => x.1 i) (∑ j,C (c j)*w j)=∑ j,c j*mixedMoment m d x.1 (toPoint (z j)) := by
        rw [eval_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [eval_mul,eval_C,hweval]
      _=∫ y : Sphere n,∑ j,c j*(⟪x.1,y.1⟫_ℝ^m*⟪toPoint (z j),y.1⟫_ℝ^d) ∂surface n := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j hj
          exact (integral_const_mul _ _).symm
        · intro j hj
          exact (integrable_mixedMoment hn m d x.1 (toPoint (z j))).const_mul _
      _=∫ y : Sphere n,eval (fun i => y.1 i) v*⟪x.1,y.1⟫_ℝ^m ∂surface n := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro y
        dsimp only
        rw [hvsum,eval_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [eval_mul,eval_C,eval_pow]
        rw [show eval (fun i => y.1 i) (linearFormPolynomial (z j))=⟪toPoint (z j),y.1⟫_ℝ from
          linearFormPolynomial_inner (toPoint (z j)) y.1]
        ring

theorem exists_homogeneous_zonal_range {n d : ℕ} (hn : 0 < n) (base : Sphere n)
    (v : Poly n) (hv : v.IsHomogeneous d) (P : Polynomial ℝ) :
    ∃ q : Poly n,q.totalDegree≤d ∧ ∀ x : Sphere n,
      eval (fun i => x.1 i) q=zonalAverage v P x.1 := by
  classical
  let w : ℕ → Poly n := fun m => Classical.choose
    (exists_homogeneous_monomial_range (m:=m) hn base v hv)
  have hwdeg (m : ℕ) : (w m).totalDegree≤d :=
    (Classical.choose_spec (exists_homogeneous_monomial_range (m:=m) hn base v hv)).1
  have hweval (m : ℕ) (x : Sphere n) : eval (fun i => x.1 i) (w m)=
      ∫ y : Sphere n,eval (fun i => y.1 i) v*⟪x.1,y.1⟫_ℝ^m ∂surface n :=
    (Classical.choose_spec (exists_homogeneous_monomial_range (m:=m) hn base v hv)).2 x
  refine ⟨∑ m ∈ P.support,C (P.coeff m)*w m,?_,?_⟩
  · apply totalDegree_finsetSum_le
    intro m hm
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hwdeg m)
  · intro x
    simp only [eval_sum,eval_mul,eval_C]
    simp_rw [hweval]
    calc
      (∑ m ∈ P.support,P.coeff m*
          ∫ y : Sphere n,eval (fun i => y.1 i) v*⟪x.1,y.1⟫_ℝ^m ∂surface n)=
          ∫ y : Sphere n,∑ m ∈ P.support,
            P.coeff m*(eval (fun i => y.1 i) v*⟪x.1,y.1⟫_ℝ^m) ∂surface n := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro m hm
          exact (integral_const_mul _ _).symm
        · intro m hm
          have h := integrable_zonalAverage hn v (Polynomial.X^m) x.1
          simpa only [Polynomial.eval_pow,Polynomial.eval_X] using h.const_mul (P.coeff m)
      _=zonalAverage v P x.1 := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro y
        dsimp only
        rw [Polynomial.eval_eq_sum,Polynomial.sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring

theorem exists_zonal_range {n : ℕ} (hn : 0 < n) (base : Sphere n)
    (v : Poly n) (P : Polynomial ℝ) :
    ∃ q : Poly n,q.totalDegree≤v.totalDegree ∧ ∀ x : Sphere n,
      eval (fun i => x.1 i) q=zonalAverage v P x.1 := by
  let w : ℕ → Poly n := fun d => Classical.choose (exists_homogeneous_zonal_range hn base
    (homogeneousComponent d v) (homogeneousComponent_isHomogeneous d v) P)
  have hwdeg (d : ℕ) : (w d).totalDegree≤d :=
    (Classical.choose_spec (exists_homogeneous_zonal_range hn base
      (homogeneousComponent d v) (homogeneousComponent_isHomogeneous d v) P)).1
  have hweval (d : ℕ) (x : Sphere n) : eval (fun i => x.1 i) (w d)=
      zonalAverage (homogeneousComponent d v) P x.1 :=
    (Classical.choose_spec (exists_homogeneous_zonal_range hn base
      (homogeneousComponent d v) (homogeneousComponent_isHomogeneous d v) P)).2 x
  refine ⟨∑ d ∈ Finset.range (v.totalDegree+1),w d,?_,?_⟩
  · apply totalDegree_finsetSum_le
    intro d hd
    exact (hwdeg d).trans (by have h := Finset.mem_range.mp hd;omega)
  · intro x
    rw [eval_sum]
    simp_rw [hweval]
    change (∑ d ∈ Finset.range (v.totalDegree+1),
        ∫ y : Sphere n,eval (fun i => y.1 i) (homogeneousComponent d v)*P.eval ⟪x.1,y.1⟫_ℝ ∂surface n)=_
    rw [←integral_finsetSum _ (fun d _ => integrable_zonalAverage hn (homogeneousComponent d v) P x.1)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    rw [←Finset.sum_mul,←eval_sum,sum_homogeneousComponent]

theorem zonalAverage_parity {n d : ℕ} (v : Poly n) (hv : v.IsHomogeneous d)
    (P : Polynomial ℝ) (x : E n) : zonalAverage v P (-x)=(-1:ℝ)^d*zonalAverage v P x := by
  let L : E n ≃ₗᵢ[ℝ] E n := LinearIsometryEquiv.neg ℝ
  let f : Sphere n → ℝ := fun y => eval (fun i => y.1 i) v*P.eval ⟪-x,y.1⟫_ℝ
  have hc := (sphereMap_measurePreserving L).integral_comp (sphereHomeomorph L).measurableEmbedding f
  calc
    zonalAverage v P (-x)=∫ y : Sphere n,f (sphereMap L y) ∂surface n := hc.symm
    _=∫ y : Sphere n,(-1:ℝ)^d*(eval (fun i => y.1 i) v*P.eval ⟪x,y.1⟫_ℝ) ∂surface n := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      have hpneg : eval (fun i => -y.1 i) v=(-1:ℝ)^d*eval (fun i => y.1 i) v := by
        simpa only [neg_one_mul] using homogeneous_eval_scale v d hv (-1) (fun i => y.1 i)
      change eval (fun i => -y.1 i) v*P.eval ⟪-x,-y.1⟫_ℝ=_
      rw [hpneg,inner_neg_neg]
      ring
    _=(-1:ℝ)^d*zonalAverage v P x := integral_const_mul _ _

theorem radialHomogenize_eval_of_sphere_parity {n d : ℕ} (v : Poly n) (hv : v.totalDegree ≤ d)
    (hpar : ∀ x : Sphere n,eval (fun i => -x.1 i) v=(-1:ℝ)^d*eval (fun i => x.1 i) v)
    (x : Sphere n) :
    eval (fun i => x.1 i) (HomogeneousSOSFromSphere.radialHomogenize v d)=eval (fun i => x.1 i) v := by
  by_cases hd : d=0
  · subst d
    have hh := HomogeneousSOSFromSphere.sum_components_to_bound v hv
    have hid : HomogeneousSOSFromSphere.radialHomogenize v 0=v := by
      simpa [HomogeneousSOSFromSphere.radialHomogenize] using hh
    rw [hid]
  · have hdpos : 1≤d := by omega
    have hsum := HomogeneousSOSFromSphere.radialHomogenize_pair_eval hdpos v hv
      (fun i => x.1 i) (coordinates_unitSphere x)
    have hneg := HomogeneousSOSFromSphere.radialHomogenize_pair_eval hdpos v hv
      (fun i => -x.1 i) (HomogeneousSOSFromSphere.neg_point_sphere (coordinates_unitSphere x))
    have hscale (q : Poly n) (k : ℕ) (hq : q.IsHomogeneous k) :
        eval (fun i => -x.1 i) q=(-1:ℝ)^k*eval (fun i => x.1 i) q := by
      simpa only [neg_one_mul] using homogeneous_eval_scale q k hq (-1) (fun i => x.1 i)
    rw [hscale _ _ (HomogeneousSOSFromSphere.radialHomogenize_homogeneous v d),
      hscale _ _ (HomogeneousSOSFromSphere.radialHomogenize_homogeneous v (d-1)),hpar x] at hneg
    have hsign : (-1:ℝ)^d=-(-1:ℝ)^(d-1) := by
      calc
        (-1:ℝ)^d=(-1:ℝ)^((d-1)+1) := congrArg (fun k => (-1:ℝ)^k) (by omega)
        _=-(-1:ℝ)^(d-1) := by rw [pow_succ];ring
    rw [hsign] at hneg
    have hprod : (-1:ℝ)^(d-1)*eval (fun i => x.1 i)
        (HomogeneousSOSFromSphere.radialHomogenize v (d-1))=0 := by
      linear_combination (hneg+((-1:ℝ)^(d-1))*hsum)/2
    have hz := (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ (by norm_num : (-1:ℝ)≠0))
    linarith

/-- A homogeneous input has an actual representative homogeneous of the
SAME degree, for every polynomial zonal kernel and the actual sphere measure. -/
theorem exists_homogeneous_zonal_lift {n d : ℕ} (hn : 0 < n) (base : Sphere n)
    (v : Poly n) (hv : v.IsHomogeneous d) (P : Polynomial ℝ) :
    ∃ q : Poly n,q.IsHomogeneous d ∧ ∀ x : Sphere n,
      eval (fun i => x.1 i) q=zonalAverage v P x.1 := by
  obtain ⟨q,hq,hqeval⟩ := exists_homogeneous_zonal_range hn base v hv P
  have hpar : ∀ x : Sphere n,eval (fun i => -x.1 i) q=(-1:ℝ)^d*eval (fun i => x.1 i) q := by
    intro x
    let nx : Sphere n := sphereMap (LinearIsometryEquiv.neg ℝ) x
    have hnq := hqeval nx
    change eval (fun i => -x.1 i) q=zonalAverage v P (-x.1) at hnq
    rw [hnq,zonalAverage_parity v hv P x.1,hqeval x]
  refine ⟨HomogeneousSOSFromSphere.radialHomogenize q d,
    HomogeneousSOSFromSphere.radialHomogenize_homogeneous q d,?_⟩
  intro x
  rw [radialHomogenize_eval_of_sphere_parity q hq hpar x,hqeval x]

/-- Filtration preservation with no auxiliary base point premise. The
actual scalar kernel may have arbitrarily large degree. -/
theorem exists_zonal_polynomial {n D : ℕ} (hn : 0 < n) (v : Poly n)
    (hv : v.totalDegree ≤ D) (P : Polynomial ℝ) :
    ∃ q : Poly n,q.totalDegree≤D ∧ ∀ x : Sphere n,
      eval (fun i => x.1 i) q=zonalAverage v P x.1 := by
  obtain ⟨q,hq,hqe⟩ := exists_zonal_range hn (axisSphere ⟨0,hn⟩) v P
  exact ⟨q,hq.trans hv,hqe⟩

/-- Homogeneous parity lift at the same input degree, for the actual
normalized Haar sphere integral and every polynomial zonal kernel. -/
theorem exists_homogeneous_zonal_polynomial {n d : ℕ} (hn : 0 < n) (v : Poly n)
    (hv : v.IsHomogeneous d) (P : Polynomial ℝ) :
    ∃ q : Poly n,q.IsHomogeneous d ∧ ∀ x : Sphere n,
      eval (fun i => x.1 i) q=zonalAverage v P x.1 :=
  exists_homogeneous_zonal_lift hn (axisSphere ⟨0,hn⟩) v hv P

end OptimalConvergenceRates.SphereDimensionBounds.SphereZonalPolynomialRange
