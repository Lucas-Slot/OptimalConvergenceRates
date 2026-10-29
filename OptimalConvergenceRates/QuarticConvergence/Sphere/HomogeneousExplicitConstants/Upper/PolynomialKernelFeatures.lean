import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.MatrixKernelSmoothing
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.PolynomialSmoothingKernel

/-! An actual finite polynomial feature expansion for the normalized even
power kernel. Every feature chooses a constant or one coordinate at each
of s slots; its polynomial degree is at most s. -/

noncomputable section

namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace PolynomialKernelFeatures

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
open MvPolynomial MeasureTheory Matrix SphereMeasure PolynomialSmoothingKernel

abbrev P (n : ℕ) := Foundation.Polynomial n
abbrev Feature (n s : ℕ) := Fin s→Option (Fin n)

def featurePolynomial {n s : ℕ} (α : Feature n s) : P n :=
  ∏j, Option.elim' 1 X (α j)

def rawCoefficient {n s : ℕ} (y : E n) (α : Feature n s) : ℝ :=
  ∏j, Option.elim' 1 (fun i ↦ y i) (α j)

def coefficient {n s : ℕ} (y : Sphere n) (α : Feature n s) : ℝ :=
  rawCoefficient y.1 α / Real.sqrt (normalization n (2*s))

def linearPolynomial {n : ℕ} (y : E n) : P n :=
  ∑i, C (y i)*X i

theorem featurePolynomial_degree {n s : ℕ} (α : Feature n s) :
    (featurePolynomial α).totalDegree≤s := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    (∑j : Fin s, (Option.elim' 1 X (α j) : P n).totalDegree)≤∑_j : Fin s, 1 := by
      apply Finset.sum_le_sum
      intro j _
      cases α j <;> simp
    _=s := by simp

theorem raw_expansion {n s : ℕ} (y : E n) :
    (∑α : Feature n s, C (rawCoefficient y α)*featurePolynomial α)=
      (1+linearPolynomial y)^s := by
  have hsum : (∑o : Option (Fin n), Option.elim' (1:P n) (fun i ↦ C (y i)*X i) o)=
      1+linearPolynomial y := by simp [linearPolynomial,Fintype.sum_option]
  rw [←hsum,Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro α _
  unfold rawCoefficient featurePolynomial
  rw [map_prod,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  cases α j <;> simp

theorem linearPolynomial_eval {n : ℕ} (y x : E n) :
    eval (fun i ↦ x i) (linearPolynomial y)=⟪x,y⟫_ℝ := by
  simp [linearPolynomial,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]

theorem normalized_expansion {n s : ℕ} (y : Sphere n) :
    (∑α : Feature n s, C (coefficient y α)*featurePolynomial α)=
      C ((Real.sqrt (normalization n (2*s)))⁻¹)*(1+linearPolynomial y.1)^s := by
  simp only [coefficient,div_eq_mul_inv,map_mul]
  rw [←raw_expansion y.1]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

theorem normalized_root_eval {n s : ℕ} (x : E n) (y : Sphere n) :
    eval (fun i ↦ x i) (MatrixKernelSmoothing.rootPolynomial coefficient (featurePolynomial (n:=n)
      (s:=s)) y)=
      (1+⟪x,y.1⟫_ℝ)^s/Real.sqrt (normalization n (2*s)) := by
  rw [MatrixKernelSmoothing.rootPolynomial,normalized_expansion]
  simp [linearPolynomial_eval,div_eq_mul_inv,mul_comm]

theorem normalized_root_square {n s : ℕ} (x : E n) (y : Sphere n) :
    eval (fun i ↦ x i) (MatrixKernelSmoothing.rootPolynomial coefficient (featurePolynomial (n:=n)
      (s:=s)) y)^2=
      kernel (2*s) x y := by
  rw [normalized_root_eval,kernel_eval,div_pow,Real.sq_sqrt (normalization_pos n (2*s)).le]
  congr 1
  rw [←pow_mul]
  congr 1
  omega

theorem normalized_root_mass {n s : ℕ} (hn : 2 ≤ n) (x : Sphere n) :
    (∫y : Sphere n, eval (fun i ↦ x.1 i)
      (MatrixKernelSmoothing.rootPolynomial coefficient (featurePolynomial (n:=n) (s:=s)) y)^2
        ∂surface n)=1 := by
  simp_rw [normalized_root_square]
  exact kernel_mass hn (2*s) x

theorem rawCoefficient_continuous {n s : ℕ} (α : Feature n s) :
    Continuous (fun y : E n ↦ rawCoefficient y α) := by
  unfold rawCoefficient
  apply continuous_finsetProd
  intro j _
  cases α j <;> simp only [Option.elim'_none,Option.elim'_some] <;> fun_prop

theorem coefficient_continuous {n s : ℕ} (α : Feature n s) :
    Continuous (fun y : Sphere n ↦ coefficient y α) :=
  ((rawCoefficient_continuous α).comp continuous_subtype_val).div_const _

theorem coefficient_products_integrable {n s : ℕ} (hn : 0 < n) (α β : Feature n s) :
    Integrable (fun y : Sphere n ↦ coefficient y α*coefficient y β) (surface n) :=
  SphereMeasure.integrable_continuous hn _ ((coefficient_continuous α).mul (coefficient_continuous
    β))

theorem weighted_coefficient_products_integrable {n s : ℕ} (hn : 0 < n)
    (α β : Feature n s) (g : Sphere n → ℝ) (hg : Measurable g)
    (hbound : ∃ B, ∀ y, |g y| ≤ B) :
    Integrable (fun y : Sphere n ↦ coefficient y α*coefficient y β*g y) (surface n) := by
  obtain ⟨B,hB⟩ := hbound
  apply (coefficient_products_integrable hn α β).mul_bdd (c := B) hg.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y ↦ by
    simpa only [Real.norm_eq_abs] using hB y

theorem normalized_root_mass_algebraic {n s : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : x ∈ Foundation.unitSphere n) :
    (∫y : Sphere n, eval x
      (MatrixKernelSmoothing.rootPolynomial coefficient (featurePolynomial (n:=n) (s:=s)) y)^2
        ∂surface n)=1 := by
  let z : E n := (WithLp.equiv 2 ((Fin n)→ℝ)).symm x
  have hsq : ‖z‖^2=1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa only [z,WithLp.equiv_symm_apply, PiLp.toLp_apply,Real.norm_eq_abs,sq_abs,
      Foundation.unitSphere,Set.mem_ofPred_eq] using hx
  have hz : ‖z‖=1 := by nlinarith [norm_nonneg z]
  let p : Sphere n := ⟨z,by simpa only [Metric.mem_sphere,dist_zero_right] using hz⟩
  simpa only [p,z,WithLp.equiv_symm_apply, PiLp.toLp_apply] using normalized_root_mass (s:=s) hn p

theorem matrix_entry_le_operatorNorm {d e : ℕ} (F : Matrix (Fin d) (Fin e) ℝ)
    (u : Fin d) (v : Fin e) : |F u v|≤‖F‖ := by
  let x : EuclideanSpace ℝ (Fin e) := EuclideanSpace.single v 1
  let z : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 ((Fin d)→ℝ)).symm (F *ᵥ x)
  have hc := PiLp.norm_apply_le z u
  have hn := Matrix.l2_opNorm_mulVec F x
  have hx : ‖x‖=1 := by simpa only [x,norm_one] using PiLp.norm_single 2 (fun _ : Fin e ↦ ℝ) v (1:ℝ)
  rw [hx,mul_one] at hn
  have hinput : (⇑x : Fin e→ℝ)=Pi.single v (1:ℝ) := by funext i;rfl
  have hFx : F *ᵥ (⇑x : Fin e→ℝ)=fun i ↦ F i v := by
    rw [hinput,Matrix.mulVec_single_one]
    rfl
  have hentry : z u=F u v := by
    change (F *ᵥ (⇑x : Fin e→ℝ)) u=F u v
    rw [hFx]
  have hz : |F u v|≤‖z‖ := by
    simpa only [hentry,Real.norm_eq_abs] using hc
  exact hz.trans hn

/-- Actual normalized even-power-kernel matrix SOS for a bounded Borel
matrix field. All coefficient integrability and kernel normalization
premises of the generic certificate are discharged here. -/
theorem bounded_field_kernel_sphereSOS {n s d e : ℕ} (hn : 2 ≤ n)
    (F : Sphere n → Matrix (Fin d) (Fin e) ℝ)
    (hFmeas : ∀ u v, Measurable (fun y ↦ F y u v)) {B : ℝ} (hB : 0 ≤ B)
    (hFnorm : ∀ y, ‖F y‖ ≤ B) :
    ∃ N : Matrix (Fin d) (Fin d) (P n), FiniteMatrixVariance.BoundedMatrixSOS (3*s) N ∧
      ∀x∈Foundation.unitSphere n,∀u v,eval x (N u v)=
        B^2*(if u=v then 1 else 0)-
          ∑k,eval x (MatrixKernelSmoothing.meanMatrix (surface n) (coefficient (s:=s))
            (featurePolynomial (s:=s)) F u k)*
            eval x (MatrixKernelSmoothing.meanMatrix (surface n) (coefficient (s:=s))
              (featurePolynomial (s:=s)) F v k) := by
  apply MatrixKernelSmoothing.exists_smoothed_matrix_sphereSOS (surface n) (coefficient (s:=s))
    (featurePolynomial (s:=s)) featurePolynomial_degree F hB hFnorm
  · exact coefficient_products_integrable (by omega)
  · intro α β u v
    apply weighted_coefficient_products_integrable (by omega) α β _ (hFmeas u v)
    exact ⟨B,fun y ↦ (matrix_entry_le_operatorNorm (F y) u v).trans (hFnorm y)⟩
  · exact normalized_root_mass_algebraic hn

end PolynomialKernelFeatures
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
