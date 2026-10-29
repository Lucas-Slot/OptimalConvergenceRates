import OptimalConvergenceRates.QuarticConvergence.Sphere.FiniteDegree
import OptimalConvergenceRates.QuarticConvergence.Sphere.HomogeneousExplicitConstants.Upper.SphereZonalPolynomialRange

/-! Actual finite-dimensional spaces of polynomial functions on the full
Euclidean sphere, with the genuine continuous-function supremum norm. -/

noncomputable section
namespace OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
namespace SpherePolynomialSpace

open scoped BigOperators
open MvPolynomial Foundation SphereMeasure SphereZonalPolynomialRange

abbrev Poly (n : ℕ) := Foundation.Polynomial n

theorem toPoint_norm_one {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ unitSphere n) : ‖toPoint x‖=1 := by
  have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n ↦ ℝ) (toPoint x)
  have hx' : (∑ i,x i^2)=1 := hx
  simp only [Real.norm_eq_abs,sq_abs] at hsq
  change ‖toPoint x‖^2=(∑ i,x i^2) at hsq
  rw [hx'] at hsq
  nlinarith [norm_nonneg (toPoint x)]

def coordinateSphere {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ unitSphere n) : Sphere n :=
  ⟨toPoint x,by simpa only [Metric.mem_sphere,dist_zero_right] using toPoint_norm_one x hx⟩

/-- Transport functions using the existing algebraic/Euclidean sphere homeomorphism. -/
def coordinateTransport (n : ℕ) :
    C(SphereBallTransfers.sphereSet n, ℝ) →ₗ[ℝ] C(Sphere n, ℝ) where
  toFun f := f.comp ⟨euclideanSphereHomeomorphSphereSet n,
    (euclideanSphereHomeomorphSphereSet n).continuous_toFun⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restriction (n : ℕ) : Poly n →ₗ[ℝ] C(Sphere n, ℝ) :=
  (coordinateTransport n).comp (sphereRestrictionLinear n)

@[simp] theorem restriction_apply (n : ℕ) (p : Poly n) (x : Sphere n) :
    restriction n p x=eval (fun i ↦ x.1 i) p := rfl

def boundedSpace (n D : ℕ) : Submodule ℝ C(Sphere n,ℝ) :=
  (spherePolynomialSpace n D).map (coordinateTransport n)

theorem boundedSpace_eq (n D : ℕ) :
    boundedSpace n D = (restrictTotalDegree (Fin n) ℝ D).map (restriction n) := by
  exact (Submodule.map_comp (sphereRestrictionLinear n) (coordinateTransport n)
    (restrictTotalDegree (Fin n) ℝ D)).symm

def homogeneousSpace (n d : ℕ) : Submodule ℝ C(Sphere n,ℝ) :=
  (homogeneousSubmodule (Fin n) ℝ d).map (restriction n)

theorem mem_boundedSpace {n D : ℕ} (F : C(Sphere n, ℝ)) :
    F∈boundedSpace n D ↔ ∃ p : Poly n,p.totalDegree≤D ∧ restriction n p=F := by
  rw [boundedSpace_eq]
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨p,(mem_restrictTotalDegree (Fin n) D p).mp hp,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨p,(mem_restrictTotalDegree (Fin n) D p).mpr hp,rfl⟩

theorem mem_homogeneousSpace {n d : ℕ} (F : C(Sphere n, ℝ)) :
    F∈homogeneousSpace n d ↔ ∃ p : Poly n,p.IsHomogeneous d ∧ restriction n p=F := Iff.rfl

instance boundedSpace_finiteDimensional (n D : ℕ) : FiniteDimensional ℝ (boundedSpace n D) :=
  Module.Finite.map (spherePolynomialSpace n D) (coordinateTransport n)

theorem homogeneousSpace_le_bounded (n d : ℕ) : homogeneousSpace n d≤boundedSpace n d := by
  rw [boundedSpace_eq]
  rintro F ⟨p,hp,rfl⟩
  exact ⟨p,(mem_restrictTotalDegree (Fin n) d p).mpr hp.totalDegree_le,rfl⟩

instance homogeneousSpace_finiteDimensional (n d : ℕ) :
    FiniteDimensional ℝ (homogeneousSpace n d) :=
  FiniteDimensional.of_injective (Submodule.inclusion (homogeneousSpace_le_bounded n d))
    (Submodule.inclusion_injective (homogeneousSpace_le_bounded n d))

def homogeneousRestriction (n d : ℕ) :
    homogeneousSubmodule (Fin n) ℝ d →ₗ[ℝ] homogeneousSpace n d where
  toFun p := ⟨restriction n p.1,⟨p.1,p.2,rfl⟩⟩
  map_add' p q := by apply Subtype.ext;exact map_add (restriction n) p.1 q.1
  map_smul' a p := by apply Subtype.ext;exact map_smul (restriction n) a p.1

theorem homogeneousRestriction_surjective (n d : ℕ) :
    Function.Surjective (homogeneousRestriction n d) := by
  intro F
  rcases F.2 with ⟨p,hp,heq⟩
  exact ⟨⟨p,hp⟩,Subtype.ext heq⟩

instance homogeneousSpace_projective (n d : ℕ) : Module.Projective ℝ (homogeneousSpace n d) := by
  letI : Module.Free ℝ (homogeneousSpace n d) := Module.Free.of_divisionRing ℝ _
  exact Module.Projective.of_free

def homogeneousRepresentative (n d : ℕ) :
    homogeneousSpace n d →ₗ[ℝ] homogeneousSubmodule (Fin n) ℝ d :=
  Classical.choose ((homogeneousRestriction n d).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (homogeneousRestriction_surjective n d)))

theorem homogeneousRepresentative_right_inverse (n d : ℕ) (F : homogeneousSpace n d) :
    homogeneousRestriction n d (homogeneousRepresentative n d F)=F := by
  have h := Classical.choose_spec ((homogeneousRestriction n d).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (homogeneousRestriction_surjective n d)))
  exact LinearMap.congr_fun h F

theorem homogeneousRepresentative_eval {n d : ℕ} (F : homogeneousSpace n d) (x : Sphere n) :
    eval (fun i ↦ x.1 i) (homogeneousRepresentative n d F).1=F.1 x := by
  have h := congrArg Subtype.val (homogeneousRepresentative_right_inverse n d F)
  exact DFunLike.congr_fun h x

def evaluation (n d : ℕ) : homogeneousSpace n d →ₗ[ℝ] (Sphere n → ℝ) where
  toFun F := F.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evaluation_bound {n d : ℕ} (F : homogeneousSpace n d) (x : Sphere n) :
    |evaluation n d F x|≤‖F‖ := by
  exact (Real.norm_eq_abs _).symm ▸ ContinuousMap.norm_coe_le_norm F.1 x

def constantOne (n l : ℕ) : homogeneousSpace n (2*l) :=
  ⟨restriction n ((radiusPolynomial n)^l),⟨(radiusPolynomial n)^l,
    (HomogeneousSphereBounds.radius_homogeneous n).pow l,rfl⟩⟩

@[simp] theorem constantOne_apply (n l : ℕ) (x : Sphere n) :
    (constantOne n l).1 x=1 := by
  simp only [constantOne,restriction_apply,eval_pow,radiusPolynomial_eval]
  rw [show (∑ i,x.1 i^2)=1 from coordinates_unitSphere x,one_pow]

theorem constantOne_norm_le_one (n l : ℕ) : ‖constantOne n l‖≤1 := by
  change ‖(constantOne n l).1‖≤1
  apply (ContinuousMap.norm_le _ (by norm_num : (0:ℝ)≤1)).mpr
  intro x
  rw [constantOne_apply]
  norm_num

theorem homogeneousRepresentative_bound {n d : ℕ} (F : homogeneousSpace n d) (x : Sphere n) :
    |eval (fun i ↦ x.1 i) (homogeneousRepresentative n d F).1|≤‖F‖ := by
  rw [homogeneousRepresentative_eval]
  exact evaluation_bound F x

end SpherePolynomialSpace
end OptimalConvergenceRates.QuarticConvergence.HomogeneousExplicitConstants
