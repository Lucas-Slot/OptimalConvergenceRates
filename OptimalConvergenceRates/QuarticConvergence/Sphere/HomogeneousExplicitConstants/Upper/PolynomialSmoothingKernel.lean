import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.ZonalSmoothingAction

/-! The normalized polynomial smoothing kernel and its actual first two
directional moments on the same Euclidean sphere. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace PolynomialSmoothingKernel

open scoped BigOperators InnerProductSpace
open MeasureTheory Polynomial SphereMeasure SphereMoments SphereAngularMoments
  ZonalSmoothingAction

def normalization (n k : ℕ) : ℝ := SmoothingMoments.mass (n-2) k

def kernel {n : ℕ} (k : ℕ) (x : E n) (y : Sphere n) : ℝ :=
  (SmoothingMoments.kernelPower k).eval ⟪x,y.1⟫_ℝ/normalization n k

def lambda1 (n k : ℕ) : ℝ := (k:ℝ)/((k:ℝ)+(n:ℝ)-1)
def lambda2 (n k : ℕ) : ℝ :=
  ((n:ℝ)*(SmoothingMoments.second (n-2) k/normalization n k)-1)/((n:ℝ)-1)

theorem normalization_pos (n k : ℕ) : 0 < normalization n k :=
  SmoothingMoments.mass_pos (n-2) k

theorem kernel_eval {n : ℕ} (k : ℕ) (x : E n) (y : Sphere n) :
    kernel k x y=(1+⟪x,y.1⟫_ℝ)^k/normalization n k := by
  simp [kernel,SmoothingMoments.kernelPower]

theorem kernel_nonnegative {n : ℕ} (k : ℕ) (x y : Sphere n) : 0 ≤ kernel k x.1 y := by
  rw [kernel_eval]
  apply div_nonneg _ (normalization_pos n k).le
  apply pow_nonneg
  have hx : ‖x.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using x.2
  have hy : ‖y.1‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using y.2
  have hb := abs_real_inner_le_norm x.1 y.1
  rw [hx,hy,mul_one] at hb
  linarith [(abs_le.mp hb).1]

theorem kernel_integrable {n : ℕ} (hn : 0 < n) (k : ℕ) (x : E n) :
    Integrable (kernel k x) (surface n) := by
  apply integrable_continuous hn
  unfold kernel
  fun_prop

theorem kernel_mass {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (x : Sphere n) :
    (∫ y : Sphere n,kernel k x.1 y ∂surface n)=1 := by
  unfold kernel
  rw [integral_div,integral_zonal_eq_angular hn]
  exact div_self (normalization_pos n k).ne'

theorem lambda2_explicit {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    lambda2 n k=(k:ℝ)*((k:ℝ)-1)/
      (((k:ℝ)+(n:ℝ)-1)*((k:ℝ)+(n:ℝ))) := by
  have h := SmoothingMoments.quadratic_eigenvalue (n-2) k
  have hnreal : ((n-2:ℕ):ℝ)=(n:ℝ)-2 := by
    rw [Nat.cast_sub hn,Nat.cast_ofNat]
  change (((n:ℝ)*(SmoothingMoments.second (n-2) k/SmoothingMoments.mass (n-2) k)-1)/
    ((n:ℝ)-1))=_
  convert h using 1 <;> rw [hnreal] <;> congr 1 <;> ring

theorem kernel_linear {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (x : Sphere n) (v : E n) :
    (∫ y : Sphere n,kernel k x.1 y*⟪v,y.1⟫_ℝ ∂surface n)=
      lambda1 n k*⟪x.1,v⟫_ℝ := by
  unfold kernel
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div,integral_weighted_linear (by omega : 0 < n),
    zonalIntegral_eq_angular hn]
  change (SmoothingMoments.first (n-2) k*⟪x.1,v⟫_ℝ)/SmoothingMoments.mass (n-2) k=_
  rw [mul_div_right_comm,SmoothingMoments.first_normalized]
  have hnreal : ((n-2:ℕ):ℝ)=(n:ℝ)-2 := by rw [Nat.cast_sub hn,Nat.cast_ofNat]
  unfold lambda1
  rw [hnreal]
  congr 2
  ring

theorem quadratic_normalization (N Z S I V A : ℝ) (hZ : Z ≠ 0) (hN : N ≠ 0)
    (hN1 : N - 1 ≠ 0) (h : (N - 1) * I = (Z - S) * V + (N * S - Z) * A) :
    I/Z=((N*(S/Z)-1)/(N-1))*A+(1-(N*(S/Z)-1)/(N-1))*V/N := by
  have hI : I=((Z-S)*V+(N*S-Z)*A)/(N-1) :=
    (eq_div_iff hN1).mpr (by linarith)
  rw [hI]
  field_simp [hZ,hN,hN1]
  ring

theorem kernel_quadratic {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (x : Sphere n) (v : E n) :
    (∫ y : Sphere n,kernel k x.1 y*⟪v,y.1⟫_ℝ^2 ∂surface n)=
      lambda2 n k*⟪x.1,v⟫_ℝ^2+(1-lambda2 n k)*‖v‖^2/(n:ℝ) := by
  have h := integral_weighted_quadratic (by omega : 0 < n) x v (SmoothingMoments.kernelPower k)
  rw [zonalIntegral_eq_angular hn] at h
  change ((n:ℝ)-1)*(∫ y : Sphere n,
    (SmoothingMoments.kernelPower k).eval ⟪x.1,y.1⟫_ℝ * ⟪v,y.1⟫_ℝ^2 ∂surface n)=
    (normalization n k-SmoothingMoments.second (n-2) k)*‖v‖^2+
      ((n:ℝ)*SmoothingMoments.second (n-2) k-normalization n k)*⟪x.1,v⟫_ℝ^2 at h
  unfold kernel
  simp_rw [div_mul_eq_mul_div]
  rw [integral_div]
  unfold lambda2
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0:ℝ)<(n:ℝ)-1 := sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  exact quadratic_normalization _ _ _ _ _ _ (normalization_pos n k).ne' hnpos.ne' hn1.ne' h

end PolynomialSmoothingKernel
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
