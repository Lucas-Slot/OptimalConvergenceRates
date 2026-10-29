import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SmoothingMoments

/-! Directional first and second moments of actual zonal sphere averages. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace DirectionalSmoothingMoments

open scoped BigOperators InnerProductSpace
open Polynomial MeasureTheory SphereMeasure SphereMoments SphereAngularMoments

theorem mul_coeff_two (p q : Polynomial ℝ) :
    (p*q).coeff 2=p.coeff 0*q.coeff 2+p.coeff 1*q.coeff 1+p.coeff 2*q.coeff 0 := by
  rw [Polynomial.coeff_mul,Finset.Nat.antidiagonal_eq_map]
  simp [Finset.sum_range_succ]
  rfl

theorem pow_coeff_zero (p : Polynomial ℝ) (hzero : p.coeff 0 = 1) (q : ℕ) :
    (p^q).coeff 0=1 := by
  change Polynomial.constantCoeff (p^q)=1
  rw [map_pow]
  change p.coeff 0^q=1
  rw [hzero,one_pow]

theorem pow_coeff_one (p : Polynomial ℝ) (hzero : p.coeff 0 = 1) (q : ℕ) :
    (p^q).coeff 1=(q:ℝ)*p.coeff 1 := by
  induction q with
  | zero => simp [Polynomial.coeff_one]
  | succ q ih =>
    rw [pow_succ,Polynomial.mul_coeff_one,pow_coeff_zero p hzero q,hzero,ih]
    push_cast
    ring

theorem pow_coeff_two (p : Polynomial ℝ) (hzero : p.coeff 0 = 1) (q : ℕ) :
    (p^q).coeff 2=(q:ℝ)*p.coeff 2+((q:ℝ)*((q:ℝ)-1)/2)*(p.coeff 1)^2 := by
  induction q with
  | zero => simp [Polynomial.coeff_one]
  | succ q ih =>
    rw [pow_succ,mul_coeff_two,pow_coeff_zero p hzero q,pow_coeff_one p hzero q,hzero,ih]
    push_cast
    ring

theorem normLine_coeff_zero {n : ℕ} (x : Sphere n) (v : E n) :
    (normLine x.1 v).coeff 0=1 := by
  have hx : ‖x.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.2
  simp [normLine,hx]

theorem normLine_coeff_one {n : ℕ} (x v : E n) :
    (normLine x v).coeff 1=2*⟪x,v⟫_ℝ := by
  simp only [normLine,Polynomial.coeff_add,Polynomial.coeff_C,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C_mul_X_pow]
  norm_num

theorem normLine_coeff_two {n : ℕ} (x v : E n) :
    (normLine x v).coeff 2=‖v‖^2 := by
  simp only [normLine,Polynomial.coeff_add,Polynomial.coeff_C,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C_mul_X_pow]
  norm_num

theorem mixedMoment_odd {n a b : ℕ} (x z : E n) (hodd : Odd (a + b)) :
    mixedMoment a b x z=0 := by
  let L : E n ≃ₗᵢ[ℝ] E n := LinearIsometryEquiv.neg ℝ
  let f : Sphere n → ℝ := fun y ↦ ⟪x,y.1⟫_ℝ^a*⟪z,y.1⟫_ℝ^b
  have h := (sphereMap_measurePreserving L).integral_comp
    (sphereHomeomorph L).measurableEmbedding f
  have heq : (fun y : Sphere n ↦ f (sphereMap L y))=fun y ↦ -f y := by
    funext y
    change ⟪x,-y.1⟫_ℝ^a*⟪z,-y.1⟫_ℝ^b=-(⟪x,y.1⟫_ℝ^a*⟪z,y.1⟫_ℝ^b)
    rw [inner_neg_right,inner_neg_right]
    have hid : (-⟪x,y.1⟫_ℝ)^a*(-⟪z,y.1⟫_ℝ)^b=
        (-1:ℝ)^(a+b)*(⟪x,y.1⟫_ℝ^a*⟪z,y.1⟫_ℝ^b) := by
      rw [show -⟪x,y.1⟫_ℝ=(-1:ℝ)*⟪x,y.1⟫_ℝ by ring,
        show -⟪z,y.1⟫_ℝ=(-1:ℝ)*⟪z,y.1⟫_ℝ by ring,mul_pow,mul_pow,pow_add]
      ring
    rw [hid,hodd.neg_one_pow,neg_one_mul]
  rw [heq,integral_neg] at h
  change -mixedMoment a b x z=mixedMoment a b x z at h
  linarith

theorem mixedMoment_linear {n : ℕ} (hn : 0 < n) (x : Sphere n) (v : E n) (m : ℕ) :
    mixedMoment m 1 x.1 v=linearMoment (m+1) x.1*⟪x.1,v⟫_ℝ := by
  rcases Nat.even_or_odd m with hm|hm
  · rw [mixedMoment_odd _ _ (hm.add_odd (by decide : Odd 1)),
      linearMoment_odd _ (hm.add_odd (by decide : Odd 1)),zero_mul]
  · obtain ⟨q,hq⟩ := hm
    have hqm : m=2*q+1 := by omega
    subst m
    have h := choose_mul_mixedMoment (q:=q+1) (j:=1) hn x x.1 v (by omega)
    rw [pow_coeff_one _ (normLine_coeff_zero x v),normLine_coeff_one] at h
    have hid1 : 2*(q+1)-1=2*q+1 := by omega
    have hid2 : 2*(q+1)=2*q+1+1 := by omega
    simp only [Nat.choose_one_right,hid1,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at h
    rw [←hid2]
    have hfac : (0:ℝ)<2*((q:ℝ)+1) := by positivity
    nlinarith

theorem mixedMoment_quadratic_even {n : ℕ} (hn : 0 < n) (x : Sphere n)
    (v : E n) (q : ℕ) :
    (2*(q:ℝ)+1)*mixedMoment (2*q) 2 x.1 v=
      linearMoment (2*q+2) x.1*(‖v‖^2+2*(q:ℝ)*⟪x.1,v⟫_ℝ^2) := by
  have h := choose_mul_mixedMoment (q:=q+1) (j:=2) hn x x.1 v (by omega)
  rw [pow_coeff_two _ (normLine_coeff_zero x v),normLine_coeff_one,normLine_coeff_two] at h
  have hc : (Nat.choose (2*(q+1)) 2:ℝ)=((q:ℝ)+1)*(2*(q:ℝ)+1) := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  rw [hc] at h
  have hi1 : 2*(q+1)-2=2*q := by omega
  have hi2 : 2*(q+1)=2*q+2 := by omega
  simp only [hi1,hi2,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h
  apply mul_left_cancel₀ (by positivity : (q:ℝ)+1 ≠ 0)
  linear_combination h

theorem mixedMoment_quadratic {n : ℕ} (hn : 0 < n) (x : Sphere n)
    (v : E n) (m : ℕ) :
    ((n:ℝ)-1)*mixedMoment m 2 x.1 v=
      (linearMoment m x.1-linearMoment (m+2) x.1)*‖v‖^2+
        ((n:ℝ)*linearMoment (m+2) x.1-linearMoment m x.1)*⟪x.1,v⟫_ℝ^2 := by
  rcases Nat.even_or_odd m with hm|hm
  · obtain ⟨q,hq⟩ := hm
    have hqm : m=2*q := by omega
    rw [hqm]
    have h := mixedMoment_quadratic_even hn x v q
    let a : Fin n := ⟨0,hn⟩
    have hrec := coordinateMoment_even_recurrence hn a q
    rw [←unit_linearMoment a x (2*q+2),←unit_linearMoment a x (2*q)] at hrec
    apply mul_left_cancel₀ (by positivity : 2*(q:ℝ)+1 ≠ 0)
    linear_combination ((n:ℝ)-1)*h+(‖v‖^2-⟪x.1,v⟫_ℝ^2)*hrec
  · rw [mixedMoment_odd _ _ (hm.add_even (by decide : Even 2)),
      linearMoment_odd _ hm,linearMoment_odd _ (hm.add_even (by decide : Even 2))]
    ring

end DirectionalSmoothingMoments
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
