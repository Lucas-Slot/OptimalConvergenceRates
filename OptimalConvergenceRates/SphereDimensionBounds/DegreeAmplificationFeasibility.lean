import OptimalConvergenceRates.SphereDimensionBounds.DegreeAmplificationPolynomial
import OptimalConvergenceRates.SphereDimensionBounds.RadialHierarchyBridge
import OptimalConvergenceRates.SphereDimensionBounds.Foundation.QuarticFeasibility

/-! Explicit first-order certificates for the amplified sparse-XOR forms. -/

noncomputable section

namespace OptimalConvergenceRates.SphereDimensionBounds.DegreeAmplification

open scoped BigOperators
open MvPolynomial OptimalConvergenceRates.SphereDimensionBounds.Foundation ChebyshevSOSKernel RadialHierarchyBridge

theorem boundedSOS_pow {n a : ℕ} {p : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n}
    (hp : BoundedSOS a p) (j : ℕ) : BoundedSOS (a*j) (p^j) := by
  induction j with
  | zero => simpa using BoundedSOS.square (1 : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n) (by simp : totalDegree (1 : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial n)≤0)
  | succ j ih =>
      rw [pow_succ]
      simpa [Nat.mul_succ] using ih.mul hp

theorem radius_boundedSOS (n : ℕ) : BoundedSOS 1 (radiusPolynomial n) := by
  exact BoundedSOS.of_family (fun i : Fin n => X i) (by intro i; simp)

def finiteAmplified {N K : ℕ} (D : HardQuarticData N K) (k j : ℕ) : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial (N+2) :=
  rename D.coordinateEquiv (amplified D.polynomial k j)

theorem finiteAmplified_formula {N K : ℕ} (D : HardQuarticData N K) (k j : ℕ) :
    finiteAmplified D k j = (radiusPolynomial (N+2))^j * D.finitePolynomial *
      chebV (X (D.coordinateEquiv none)) (radiusPolynomial (N+2)) k^4 := by
  unfold finiteAmplified amplified
  simp only [map_mul,map_pow,(cheb_rename D.coordinateEquiv _ _ k).2,
    genericRadius_reindex,rename_X]
  rfl

theorem finiteAmplified_radial_sos {N K : ℕ} (D : HardQuarticData N K) (k j : ℕ) :
    BoundedSOS (2*(k+1)+j)
      (finiteAmplified D k j +
        C (normalizedNegativeCoefficient (E := Fin (8*N))) *
          (radiusPolynomial (N+2))^(2*(k+1)+j)) := by
  classical
  let e := D.coordinateEquiv
  let s : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial (N+2) := radiusPolynomial (N+2)
  let t : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial (N+2) := X (e none)
  let u : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial (N+2) := X (e (some none))
  let R : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial (N+2) := ∑ v : Fin N, (X (e (some (some v))))^2
  let Q : OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial (N+2) := R+u^2
  let c : ℝ := normalizedNegativeCoefficient (E := Fin (8*N))
  let H : (Fin (8*N) ⊕ Fin N) → OptimalConvergenceRates.SphereDimensionBounds.Foundation.Polynomial (N+2) := fun a =>
    rename (e ∘ some) (normalizedQuarticSquareRoot D.first D.second D.third D.label a)
  have hs : s=t^2+Q := by
    have he := genericRadius_reindex e
    simp only [genericRadius,Fintype.sum_option,map_add,map_sum,map_pow,rename_X] at he
    change t^2+(u^2+R)=s at he
    dsimp [Q]
    linear_combination -he
  have hR : BoundedSOS 1 R := BoundedSOS.of_family
    (fun v : Fin N => X (e (some (some v)))) (by intro v; simp)
  have hu : BoundedSOS 1 (u^2) := BoundedSOS.square u (by simp [u])
  have hQ : BoundedSOS 1 Q := hR.add hu
  have hH : BoundedSOS 2 (∑ a,H a^2) := by
    apply BoundedSOS.of_family
    intro a
    exact (totalDegree_rename_le _ _).trans
      (normalizedQuarticSquareRoot_isHomogeneous D.first D.second D.third D.label a).totalDegree_le
  have hid : D.finitePolynomial=(∑ a,H a^2)-C c*u^4 := by
    have h := congrArg (rename (e ∘ some))
      (normalizedQuartic_sos_sub_fourth D.first D.second D.third D.label)
    simpa only [HardQuarticData.finitePolynomial,HardQuarticData.polynomial,
      paddedPolynomial,rename_rename,map_sub,map_sum,map_pow,map_mul,rename_C,rename_X,
      H,c,u,e,Function.comp_apply] using h
  have hc : 0≤c := normalizedNegativeCoefficient_nonneg
  have hbase : BoundedSOS 2 (D.finitePolynomial+C c*Q^2) := by
    have hcomp := (hR.mul (hR.add (hu.scale 2 (by norm_num)))).scale c hc
    change BoundedSOS 2 (C c*(R*(R+2*u^2))) at hcomp
    convert hH.add hcomp using 1
    rw [hid]
    dsimp [Q]
    ring
  let A := chebA t s k
  let V := chebV t s k
  have hhom := cheb_homogeneous t s (isHomogeneous_X ℝ _)
    (genericRadius_homogeneous (σ := Fin (N+2))) k
  have hAd : A.totalDegree≤k+1 := hhom.1.totalDegree_le
  have hVd : V.totalDegree≤k := hhom.2.totalDegree_le
  have hVs : BoundedSOS k (V^2) := BoundedSOS.square V hVd
  have hVfour : BoundedSOS (2*k) (V^4) := by
    simpa [← pow_mul] using BoundedSOS.square (V^2)
      ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hVd))
  have hAs : BoundedSOS (k+1) (A^2) := BoundedSOS.square A hAd
  have hspow : BoundedSOS (k+1) (s^(k+1)) := by
    simpa [s] using boundedSOS_pow (radius_boundedSOS (N+2)) (k+1)
  have hQV : BoundedSOS (k+1) (Q*V^2) := by
    simpa [Nat.add_comm] using hQ.mul hVs
  have hpell : A^2+Q*V^2=s^(k+1) := by
    have h := cheb_pell t s k
    have hsub : s-t^2=Q := by rw [hs]; ring
    simpa only [hsub] using h
  have hmain : BoundedSOS (2*(k+1))
      (D.finitePolynomial*V^4+C c*s^(2*(k+1))) := by
    have hh := (hbase.mul hVfour).add
      (((hAs.mul (hspow.add hQV)).scale c hc).mono (by omega))
    have hh' : BoundedSOS (2*(k+1))
        ((D.finitePolynomial+C c*Q^2)*V^4+C c*(A^2*(s^(k+1)+Q*V^2))) :=
      hh.mono (by omega)
    convert hh' using 1
    rw [show s^(2*(k+1))=(s^(k+1))^2 by ring]
    rw [← hpell]
    ring
  have hfinal := (boundedSOS_pow (radius_boundedSOS (N+2)) j).mul hmain
  convert hfinal using 1
  · omega
  · rw [finiteAmplified_formula]
    dsimp [s,t,V,c,e]
    rw [pow_add]
    ring

theorem finiteAmplified_feasible {N K : ℕ} (D : HardQuarticData N K) (k j r : ℕ)
    (hr : 2 * (k + 1) + j ≤ r) :
    Feasible r (finiteAmplified D k j)
      (-(normalizedNegativeCoefficient (E := Fin (8*N)))) := by
  exact feasible_mono hr (bounded_sos_radial_shift_feasible _ _
    (finiteAmplified_radial_sos D k j))

end OptimalConvergenceRates.SphereDimensionBounds.DegreeAmplification
