/-
  OptimalConvergenceRates/ScaledRobinson/HomogenizationCore.lean

  Algebraic infrastructure for the scaled Robinson homogenization.
-/
import OptimalConvergenceRates.ScaledRobinson.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import OptimalConvergenceRates.BaldiSlot2024.ScaledSchmudgen

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates
namespace ScaledRobinson

/-- The variable equivalence that treats `X 2` as the univariate polynomial variable and
`X 0, X 1` as coefficient variables. -/
def fin3ToOptionFin2 : Fin 3 ≃ Option (Fin 2) where
  toFun i := if h : (i : ℕ) = 2 then none else some ⟨i, by omega⟩
  invFun o := match o with
    | none => 2
    | some j => ⟨j, by omega⟩
  left_inv := by
    intro i
    fin_cases i <;> simp
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some j => fin_cases j <;> simp

/-- View a ternary polynomial as a univariate polynomial in `z`, with coefficients in
`ℝ[x,y]`. -/
def zAsPolynomialEquiv :
    MvPolynomial (Fin 3) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin 2) ℝ) :=
  (MvPolynomial.renameEquiv ℝ fin3ToOptionFin2).trans
    (MvPolynomial.optionEquivLeft ℝ (Fin 2))

@[simp]
theorem zAsPolynomialEquiv_X_zero :
    zAsPolynomialEquiv (X 0 : MvPolynomial (Fin 3) ℝ) =
      Polynomial.C (X 0 : MvPolynomial (Fin 2) ℝ) := by
  simp [zAsPolynomialEquiv, fin3ToOptionFin2]

@[simp]
theorem zAsPolynomialEquiv_X_one :
    zAsPolynomialEquiv (X 1 : MvPolynomial (Fin 3) ℝ) =
      Polynomial.C (X 1 : MvPolynomial (Fin 2) ℝ) := by
  simp [zAsPolynomialEquiv, fin3ToOptionFin2]

@[simp]
theorem zAsPolynomialEquiv_X_two :
    zAsPolynomialEquiv (X 2 : MvPolynomial (Fin 3) ℝ) = Polynomial.X := by
  simp [zAsPolynomialEquiv, fin3ToOptionFin2]

/-- Reflection in the homogenizing variable, `z ↦ -z`, on ternary polynomials. -/
def zReflect3 : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval ![(X 0 : MvPolynomial (Fin 3) ℝ), X 1, -X 2]

/-- Substitution `z ↦ z^2` on ternary polynomials. -/
def zSquareSubst3 : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval
    ![(X 0 : MvPolynomial (Fin 3) ℝ), X 1,
      (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2]

@[simp]
theorem zReflect3_X_zero : zReflect3 (X 0 : MvPolynomial (Fin 3) ℝ) = X 0 := by
  simp [zReflect3]

@[simp]
theorem zReflect3_X_one : zReflect3 (X 1 : MvPolynomial (Fin 3) ℝ) = X 1 := by
  simp [zReflect3]

@[simp]
theorem zReflect3_X_two : zReflect3 (X 2 : MvPolynomial (Fin 3) ℝ) = -X 2 := by
  simp [zReflect3]

@[simp]
theorem zSquareSubst3_X_zero :
    zSquareSubst3 (X 0 : MvPolynomial (Fin 3) ℝ) = X 0 := by
  simp [zSquareSubst3]

@[simp]
theorem zSquareSubst3_X_one :
    zSquareSubst3 (X 1 : MvPolynomial (Fin 3) ℝ) = X 1 := by
  simp [zSquareSubst3]

@[simp]
theorem zSquareSubst3_X_two :
    zSquareSubst3 (X 2 : MvPolynomial (Fin 3) ℝ) =
      (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 := by
  simp [zSquareSubst3]

/-- Exponent map induced by `z ↦ z^2`: it doubles only the third exponent. -/
def zSquareExp3AddMonoidHom : (Fin 3 →₀ ℕ) →+ (Fin 3 →₀ ℕ) where
  toFun d := d.update (2 : Fin 3) (2 * d (2 : Fin 3))
  map_zero' := by
    ext i
    fin_cases i <;> simp
  map_add' d e := by
    ext i
    fin_cases i <;> simp
    omega

/-- The monomial-domain map induced by `z ↦ z^2` fixes `X 0`. -/
theorem zSquareExp3_mapDomain_X_zero :
    (AddMonoidAlgebra.mapDomainAlgHom ℝ ℝ zSquareExp3AddMonoidHom :
        MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ)
      (X (0 : Fin 3)) = (X (0 : Fin 3) : MvPolynomial (Fin 3) ℝ) := by
  rw [MvPolynomial.X]
  change AddMonoidAlgebra.mapDomain zSquareExp3AddMonoidHom
      (AddMonoidAlgebra.single (Finsupp.single (0 : Fin 3) 1) (1 : ℝ)) =
    AddMonoidAlgebra.single (Finsupp.single (0 : Fin 3) 1) (1 : ℝ)
  rw [AddMonoidAlgebra.mapDomain_single]
  congr 1
  ext j
  fin_cases j <;> simp [zSquareExp3AddMonoidHom]

/-- The monomial-domain map induced by `z ↦ z^2` fixes `X 1`. -/
theorem zSquareExp3_mapDomain_X_one :
    (AddMonoidAlgebra.mapDomainAlgHom ℝ ℝ zSquareExp3AddMonoidHom :
        MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ)
      (X (1 : Fin 3)) = (X (1 : Fin 3) : MvPolynomial (Fin 3) ℝ) := by
  rw [MvPolynomial.X]
  change AddMonoidAlgebra.mapDomain zSquareExp3AddMonoidHom
      (AddMonoidAlgebra.single (Finsupp.single (1 : Fin 3) 1) (1 : ℝ)) =
    AddMonoidAlgebra.single (Finsupp.single (1 : Fin 3) 1) (1 : ℝ)
  rw [AddMonoidAlgebra.mapDomain_single]
  congr 1
  ext j
  fin_cases j <;> simp [zSquareExp3AddMonoidHom]

/-- The monomial-domain map induced by `z ↦ z^2` sends `X 2` to `X 2 ^ 2`. -/
theorem zSquareExp3_mapDomain_X_two :
    (AddMonoidAlgebra.mapDomainAlgHom ℝ ℝ zSquareExp3AddMonoidHom :
        MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ)
      (X (2 : Fin 3)) = (X (2 : Fin 3) : MvPolynomial (Fin 3) ℝ) ^ 2 := by
  rw [MvPolynomial.X]
  change AddMonoidAlgebra.mapDomain zSquareExp3AddMonoidHom
      (AddMonoidAlgebra.single (Finsupp.single (2 : Fin 3) 1) (1 : ℝ)) =
    (MvPolynomial.monomial (Finsupp.single (2 : Fin 3) 1) (1 : ℝ)) ^ 2
  rw [AddMonoidAlgebra.mapDomain_single]
  change MvPolynomial.monomial (zSquareExp3AddMonoidHom (Finsupp.single (2 : Fin 3) 1))
      (1 : ℝ) = (MvPolynomial.monomial (Finsupp.single (2 : Fin 3) 1) (1 : ℝ)) ^ 2
  rw [show zSquareExp3AddMonoidHom (Finsupp.single (2 : Fin 3) 1) =
      Finsupp.single (2 : Fin 3) 2 by
    ext j
    fin_cases j <;> simp [zSquareExp3AddMonoidHom]]
  rw [← MvPolynomial.X_pow_eq_monomial]
  rfl

/-- The substitution `z ↦ z^2` is the monomial-domain map that doubles the third exponent. -/
theorem zSquareSubst3_eq_mapDomain :
    zSquareSubst3 =
      (AddMonoidAlgebra.mapDomainAlgHom ℝ ℝ zSquareExp3AddMonoidHom :
        MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact zSquareSubst3_X_zero.trans zSquareExp3_mapDomain_X_zero.symm
  · exact zSquareSubst3_X_one.trans zSquareExp3_mapDomain_X_one.symm
  · exact zSquareSubst3_X_two.trans zSquareExp3_mapDomain_X_two.symm

/-- The exponent map for `z ↦ z^2` is injective. -/
theorem zSquareExp3AddMonoidHom_injective : Function.Injective zSquareExp3AddMonoidHom := by
  intro d e h
  ext i
  have hi := congrArg (fun f : Fin 3 →₀ ℕ => f i) h
  by_cases hi2 : i = (2 : Fin 3)
  · subst i
    simp [zSquareExp3AddMonoidHom] at hi
    omega
  · fin_cases i
    · simpa [zSquareExp3AddMonoidHom] using hi
    · simpa [zSquareExp3AddMonoidHom] using hi
    · contradiction

/-- The support of a square-substituted polynomial is the image of the support under the
exponent map that doubles the third exponent. -/
theorem zSquareSubst3_support (p : MvPolynomial (Fin 3) ℝ) :
    (zSquareSubst3 p).support = Finset.image zSquareExp3AddMonoidHom p.support := by
  rw [zSquareSubst3_eq_mapDomain]
  change (AddMonoidAlgebra.mapDomain zSquareExp3AddMonoidHom p).support =
    Finset.image zSquareExp3AddMonoidHom p.support
  exact Finsupp.mapDomain_support_of_injective zSquareExp3AddMonoidHom_injective p

/-- The source weighted degree of one exponent is the ordinary total degree after
substituting `z^2` for the third variable. -/
theorem sourceWeight3_eq_zSquareExp3_sum (d : Fin 3 →₀ ℕ) :
    (∑ i ∈ d.support, d i * (![1, 1, 2] i)) =
      (zSquareExp3AddMonoidHom d).sum (fun _ e => e) := by
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
  rw [Finset.sum_subset (s₁ := d.support) (s₂ := Finset.univ)]
  · rw [Fin.sum_univ_three]
    conv_rhs => rw [Fin.sum_univ_three]
    simp [zSquareExp3AddMonoidHom]
    omega
  · intro i _
    exact Finset.mem_univ i
  · intro i _ hi
    have hzero : d i = 0 := by simpa [Finsupp.mem_support_iff] using hi
    rw [hzero]
    simp

@[simp]
theorem zReflect3_C (a : ℝ) :
    zReflect3 (MvPolynomial.C a : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C a := by
  simp [zReflect3]

/-- Univariate reflection `z ↦ -z` on polynomials in `z` with coefficients in `ℝ[x,y]`,
viewed as an `ℝ`-algebra hom. -/
def zPolynomialReflect :
    Polynomial (MvPolynomial (Fin 2) ℝ) →ₐ[ℝ] Polynomial (MvPolynomial (Fin 2) ℝ) :=
  { (Polynomial.aeval (-Polynomial.X : Polynomial (MvPolynomial (Fin 2) ℝ))).toRingHom with
    commutes' := by
      intro r
      simp }

/-- Univariate substitution `z ↦ z^2` on polynomials in `z` with coefficients in
`ℝ[x,y]`, viewed as an `ℝ`-algebra hom. -/
def zPolynomialSquareSubst :
    Polynomial (MvPolynomial (Fin 2) ℝ) →ₐ[ℝ] Polynomial (MvPolynomial (Fin 2) ℝ) :=
  { (Polynomial.aeval
      (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℝ))).toRingHom with
    commutes' := by
      intro r
      simp }

/-- Under `zAsPolynomialEquiv`, reflecting the ternary homogenizing variable is the
univariate substitution `z ↦ -z`. -/
theorem zAsPolynomialEquiv_zReflect3 (p : MvPolynomial (Fin 3) ℝ) :
    zAsPolynomialEquiv (zReflect3 p) = zPolynomialReflect (zAsPolynomialEquiv p) := by
  have h : zAsPolynomialEquiv.toAlgHom.comp zReflect3 =
      zPolynomialReflect.comp zAsPolynomialEquiv.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [zPolynomialReflect]
  exact AlgHom.congr_fun h p

/-- The univariate square-substitution map is polynomial expansion by the factor `2`. -/
theorem zPolynomialSquareSubst_eq_expand
    (P : Polynomial (MvPolynomial (Fin 2) ℝ)) :
    zPolynomialSquareSubst P = Polynomial.expand (MvPolynomial (Fin 2) ℝ) 2 P := by
  induction P using Polynomial.induction_on' with
  | monomial n c =>
      unfold zPolynomialSquareSubst
      rw [Polynomial.expand_monomial]
      change Polynomial.aeval (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℝ))
          (Polynomial.monomial n c) = Polynomial.monomial (n * 2) c
      rw [Polynomial.aeval_monomial]
      change Polynomial.C c * (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℝ)) ^ n =
          Polynomial.monomial (n * 2) c
      rw [show (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℝ)) ^ n =
          Polynomial.X ^ (n * 2) by
        rw [← pow_mul]
        rw [show 2 * n = n * 2 by omega]]
      rw [Polynomial.C_mul_X_pow_eq_monomial]
  | add P Q hP hQ =>
      simp [map_add, hP, hQ]

/-- The univariate square-substitution map is injective. -/
theorem zPolynomialSquareSubst_injective : Function.Injective zPolynomialSquareSubst := by
  intro P Q hPQ
  apply Polynomial.expand_injective (R := MvPolynomial (Fin 2) ℝ) (n := 2) (by norm_num)
  rw [← zPolynomialSquareSubst_eq_expand P, ← zPolynomialSquareSubst_eq_expand Q]
  exact hPQ


/-- Under `zAsPolynomialEquiv`, substituting `z^2` for the ternary homogenizing variable is
the univariate substitution `z ↦ z^2`. -/
theorem zAsPolynomialEquiv_zSquareSubst3 (p : MvPolynomial (Fin 3) ℝ) :
    zAsPolynomialEquiv (zSquareSubst3 p) =
      zPolynomialSquareSubst (zAsPolynomialEquiv p) := by
  have h : zAsPolynomialEquiv.toAlgHom.comp zSquareSubst3 =
      zPolynomialSquareSubst.comp zAsPolynomialEquiv.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [zPolynomialSquareSubst]
  exact AlgHom.congr_fun h p

/-- The ternary square-substitution map is injective. -/
theorem zSquareSubst3_injective : Function.Injective zSquareSubst3 := by
  intro p q hpq
  apply zAsPolynomialEquiv.injective
  apply zPolynomialSquareSubst_injective
  rw [← zAsPolynomialEquiv_zSquareSubst3, ← zAsPolynomialEquiv_zSquareSubst3]
  exact congrArg zAsPolynomialEquiv hpq

/-- Square-substitution of a monomial gives the corresponding even monomial. -/
theorem zPolynomialSquareSubst_monomial_even
    (n : ℕ) (c : MvPolynomial (Fin 2) ℝ) (hn : Even n) :
    zPolynomialSquareSubst (Polynomial.monomial (n / 2) c) =
      Polynomial.monomial n c := by
  obtain ⟨k, hk⟩ := hn
  subst n
  rw [show (k + k) / 2 = k by omega]
  unfold zPolynomialSquareSubst
  change Polynomial.aeval (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℝ))
      (Polynomial.monomial k c) = Polynomial.monomial (k + k) c
  rw [Polynomial.aeval_monomial]
  change Polynomial.C c * (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℝ)) ^ k =
      Polynomial.monomial (k + k) c
  rw [← pow_mul]
  rw [show 2 * k = k + k by omega]
  rw [Polynomial.C_mul_X_pow_eq_monomial]

/-- Multiplying by `z` after square-substitution gives the corresponding odd monomial. -/
theorem X_mul_zPolynomialSquareSubst_monomial_odd
    (n : ℕ) (c : MvPolynomial (Fin 2) ℝ) (hn : ¬ Even n) :
    Polynomial.X * zPolynomialSquareSubst (Polynomial.monomial (n / 2) c) =
      Polynomial.monomial n c := by
  have hn_decomp : n = 2 * (n / 2) + 1 := by
    have hmod_ne : n % 2 ≠ 0 := by
      intro h0
      apply hn
      use n / 2
      have hdecomp := Nat.mod_add_div n 2
      omega
    have hmod_lt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
    have hmod : n % 2 = 1 := by omega
    have hdecomp := Nat.mod_add_div n 2
    omega
  rw [hn_decomp]
  rw [show (2 * (n / 2) + 1) / 2 = n / 2 by omega]
  unfold zPolynomialSquareSubst
  change Polynomial.X *
      Polynomial.aeval (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℝ))
        (Polynomial.monomial (n / 2) c) =
    Polynomial.monomial (2 * (n / 2) + 1) c
  rw [Polynomial.aeval_monomial]
  change Polynomial.X *
      (Polynomial.C c * (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℝ)) ^ (n / 2)) =
    Polynomial.monomial (2 * (n / 2) + 1) c
  rw [← pow_mul]
  rw [show Polynomial.X * (Polynomial.C c * Polynomial.X ^ (2 * (n / 2))) =
      Polynomial.C c * Polynomial.X ^ (2 * (n / 2) + 1) by ring]
  rw [Polynomial.C_mul_X_pow_eq_monomial]

/-- Every polynomial in `z` splits as an even-in-`z` part plus `z` times an even-in-`z`
part, written through the square-substitution map. -/
theorem exists_zPolynomialSquareSubst_even_odd
    (P : Polynomial (MvPolynomial (Fin 2) ℝ)) :
    ∃ A B : Polynomial (MvPolynomial (Fin 2) ℝ),
      P = zPolynomialSquareSubst A + Polynomial.X * zPolynomialSquareSubst B := by
  induction P using Polynomial.induction_on' with
  | monomial n c =>
      by_cases hn : Even n
      · refine ⟨Polynomial.monomial (n / 2) c, 0, ?_⟩
        rw [zPolynomialSquareSubst_monomial_even n c hn]
        simp
      · refine ⟨0, Polynomial.monomial (n / 2) c, ?_⟩
        rw [X_mul_zPolynomialSquareSubst_monomial_odd n c hn]
        simp
  | add P Q hP hQ =>
      obtain ⟨A, B, hAB⟩ := hP
      obtain ⟨C, D, hCD⟩ := hQ
      refine ⟨A + C, B + D, ?_⟩
      rw [hAB, hCD]
      simp [map_add]
      ring

/-- Every ternary polynomial splits as an even-in-`z` square-substitution part plus `z`
times another even-in-`z` square-substitution part. -/
theorem exists_zSquareSubst3_even_odd (p : MvPolynomial (Fin 3) ℝ) :
    ∃ A B : MvPolynomial (Fin 3) ℝ,
      p = zSquareSubst3 A + (X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 B := by
  obtain ⟨A, B, hAB⟩ := exists_zPolynomialSquareSubst_even_odd (zAsPolynomialEquiv p)
  refine ⟨zAsPolynomialEquiv.symm A, zAsPolynomialEquiv.symm B, ?_⟩
  apply zAsPolynomialEquiv.injective
  rw [map_add, map_mul, zAsPolynomialEquiv_X_two]
  rw [zAsPolynomialEquiv_zSquareSubst3, zAsPolynomialEquiv_zSquareSubst3]
  simp only [AlgEquiv.apply_symm_apply]
  exact hAB

/-- Square-substituted ternary polynomials are invariant under `z ↦ -z`. -/
theorem zReflect3_zSquareSubst3 (p : MvPolynomial (Fin 3) ℝ) :
    zReflect3 (zSquareSubst3 p) = zSquareSubst3 p := by
  have h : zReflect3.comp zSquareSubst3 = zSquareSubst3 := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [zReflect3, zSquareSubst3]
  exact AlgHom.congr_fun h p

/-- A ternary polynomial fixed by `z ↦ -z` is a polynomial in `z^2`. -/
theorem exists_zSquareSubst3_of_zReflect3_eq_self
    {p : MvPolynomial (Fin 3) ℝ} (hp : zReflect3 p = p) :
    ∃ A : MvPolynomial (Fin 3) ℝ, p = zSquareSubst3 A := by
  obtain ⟨A, B, hAB⟩ := exists_zSquareSubst3_even_odd p
  let t : MvPolynomial (Fin 3) ℝ := (X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 B
  have hreflect : zReflect3 p = zSquareSubst3 A - t := by
    rw [hAB]
    dsimp [t]
    simp [zReflect3_zSquareSubst3]
    ring
  have heq : zSquareSubst3 A - t = zSquareSubst3 A + t := by
    rw [← hreflect, hp, hAB]
  have ht_neg : -t = t := by
    exact add_left_cancel (a := zSquareSubst3 A) (by simpa [sub_eq_add_neg] using heq)
  have ht_eq_neg : t = -t := by simpa using congrArg Neg.neg ht_neg
  have htwice_add : t + t = 0 := by
    calc
      t + t = -t + t := by nth_rw 1 [ht_eq_neg]
      _ = 0 := neg_add_cancel t
  have htwice : (2 : MvPolynomial (Fin 3) ℝ) * t = 0 := by
    simpa [two_mul] using htwice_add
  have htwo_ne : (2 : MvPolynomial (Fin 3) ℝ) ≠ 0 := by
    rw [show (2 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (2 : ℝ) from
      (MvPolynomial.C_eq_coe_nat 2).symm]
    exact MvPolynomial.C_ne_zero.mpr (by norm_num)
  have ht : t = 0 := (mul_eq_zero.mp htwice).resolve_left htwo_ne
  refine ⟨A, ?_⟩
  rw [hAB]
  dsimp [t] at ht
  rw [ht, add_zero]

/-- A ternary polynomial negated by `z ↦ -z` is `z` times a polynomial in `z^2`. -/
theorem exists_X_two_mul_zSquareSubst3_of_zReflect3_eq_neg
    {p : MvPolynomial (Fin 3) ℝ} (hp : zReflect3 p = -p) :
    ∃ B : MvPolynomial (Fin 3) ℝ,
      p = (X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 B := by
  obtain ⟨A, B, hAB⟩ := exists_zSquareSubst3_even_odd p
  let s : MvPolynomial (Fin 3) ℝ := zSquareSubst3 A
  let t : MvPolynomial (Fin 3) ℝ := (X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 B
  have hreflect : zReflect3 p = s - t := by
    rw [hAB]
    dsimp [s, t]
    simp [zReflect3_zSquareSubst3]
    ring
  have heq : s - t = -(s + t) := by
    rw [← hreflect, hp, hAB]
  have hs_neg : s = -s := by
    have hcancel : s - t + t = -(s + t) + t := congrArg (fun q => q + t) heq
    simpa [sub_eq_add_neg] using hcancel
  have htwice_add : s + s = 0 := by
    calc
      s + s = s + -s := by nth_rw 2 [hs_neg]
      _ = 0 := add_neg_cancel s
  have htwice : (2 : MvPolynomial (Fin 3) ℝ) * s = 0 := by
    simpa [two_mul] using htwice_add
  have htwo_ne : (2 : MvPolynomial (Fin 3) ℝ) ≠ 0 := by
    rw [show (2 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (2 : ℝ) from
      (MvPolynomial.C_eq_coe_nat 2).symm]
    exact MvPolynomial.C_ne_zero.mpr (by norm_num)
  have hs : s = 0 := (mul_eq_zero.mp htwice).resolve_left htwo_ne
  refine ⟨B, ?_⟩
  rw [hAB]
  dsimp [s, t] at hs ⊢
  rw [hs, zero_add]

/-- The reflection `z ↦ -z` is involutive. -/
theorem zReflect3_involutive (p : MvPolynomial (Fin 3) ℝ) :
    zReflect3 (zReflect3 p) = p := by
  have h : zReflect3.comp zReflect3 =
      (AlgHom.id ℝ (MvPolynomial (Fin 3) ℝ)) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [zReflect3]
  exact AlgHom.congr_fun h p

/-- Composition rule for the local two-variable scaling map. -/
theorem scale2_comp (a b : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    scale2 a (scale2 b p) = scale2 (b * a) p := by
  simpa [scale2, polyScale] using polyScale_comp (n := 2) a b p

/-- Scaling by one is the identity. -/
theorem scale2_one (p : MvPolynomial (Fin 2) ℝ) :
    scale2 1 p = p := by
  simp [scale2]

/-- Scaling the unit-ball generator gives the scaled-ball generator up to a positive factor. -/
theorem scale2_unitBallGenerator (eps : ℝ) (hEps : eps ≠ 0) :
    scale2 eps UnitBallGenerator = MvPolynomial.C (eps ^ 2) * BallGenerator (eps⁻¹ ^ 2) := by
  unfold scale2 UnitBallGenerator BallGenerator
  simp only [map_sub, map_one, map_pow, MvPolynomial.aeval_X, mul_pow, mul_sub]
  have hconst :
      (MvPolynomial.C eps : MvPolynomial (Fin 2) ℝ) ^ 2 * MvPolynomial.C eps⁻¹ ^ 2 = 1 := by
    rw [← MvPolynomial.C_pow, ← MvPolynomial.C_pow, ← MvPolynomial.C_mul]
    field_simp [hEps]
    simp
  rw [hconst]

/-- Scaling the `eps⁻²` ball generator gives the unit-ball generator up to a factor. -/
theorem scale2_ballGenerator_invSq (eps : ℝ) :
    scale2 eps⁻¹ (BallGenerator (eps⁻¹ ^ 2)) =
      MvPolynomial.C (eps⁻¹ ^ 2) * UnitBallGenerator := by
  unfold scale2 UnitBallGenerator BallGenerator
  simp only [map_sub, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, mul_pow, mul_sub]
  ring

/-- The local two-variable scaling map has the expected total-degree bound. -/
theorem scale2_totalDegree_le (c : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    (scale2 c p).totalDegree ≤ p.totalDegree := by
  simpa [scale2, polyScale] using polyScale_totalDegree_le (n := 2) c p

/-- Scaling preserves root-degree-bounded SOS witnesses. -/
theorem HasDegreeBoundedSOS.scale {σ : MvPolynomial (Fin 2) ℝ} {r : ℕ}
    (hσ : HasDegreeBoundedSOS σ r) (c : ℝ) :
    HasDegreeBoundedSOS (ScaledRobinson.scale2 c σ) r := by
  obtain ⟨N, Q, hQ, hdeg⟩ := hσ
  refine ⟨N, fun i => ScaledRobinson.scale2 c (Q i), ?_, ?_⟩
  · rw [hQ]
    simp only [map_sum, map_pow]
  · intro i
    exact (scale2_totalDegree_le c (Q i)).trans (hdeg i)

/-- Multiplication by a nonnegative scalar preserves root-degree-bounded SOS witnesses. -/
theorem HasDegreeBoundedSOS.const_mul {σ : MvPolynomial (Fin 2) ℝ} {r : ℕ}
    (hσ : HasDegreeBoundedSOS σ r) {c : ℝ} (hc : 0 ≤ c) :
    HasDegreeBoundedSOS (MvPolynomial.C c * σ) r := by
  obtain ⟨N, Q, hQ, hdeg⟩ := hσ
  refine ⟨N, fun i => MvPolynomial.C (Real.sqrt c) * Q i, ?_, ?_⟩
  · rw [hQ]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [mul_pow, ← MvPolynomial.C_pow, Real.sq_sqrt hc]
  · intro i
    calc (MvPolynomial.C (Real.sqrt c) * Q i).totalDegree
        ≤ (MvPolynomial.C (Real.sqrt c)).totalDegree + (Q i).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = (Q i).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ r := hdeg i

/-- Degree-bounded SOS witnesses are closed under addition. -/
theorem HasDegreeBoundedSOS.add {σ τ : MvPolynomial (Fin 2) ℝ} {r : ℕ}
    (hσ : HasDegreeBoundedSOS σ r) (hτ : HasDegreeBoundedSOS τ r) :
    HasDegreeBoundedSOS (σ + τ) r := by
  obtain ⟨Nσ, Qσ, hQσ, hdegσ⟩ := hσ
  obtain ⟨Nτ, Qτ, hQτ, hdegτ⟩ := hτ
  refine ⟨Nσ + Nτ, Fin.append Qσ Qτ, ?_, ?_⟩
  · rw [hQσ, hQτ, Fin.sum_univ_add]
    simp [Fin.append]
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro iσ
      simpa [Fin.append] using hdegσ iσ
    · intro iτ
      simpa [Fin.append] using hdegτ iτ

/-- Ball-module membership is antitone in the radius parameter. -/
theorem BallQuadraticModule_of_lambda_le {lambda lambda0 : ℝ} {r : ℕ}
    (hle : lambda ≤ lambda0) :
    BallQuadraticModule lambda0 r ⊆ BallQuadraticModule lambda r := by
  intro p hp
  obtain ⟨σ0, σ1, hσ0, hσ1, hp_eq⟩ := hp
  refine ⟨σ0 + MvPolynomial.C (lambda0 - lambda) * σ1, σ1, ?_, hσ1, ?_⟩
  · exact hσ0.add ((hσ1.const_mul (sub_nonneg.mpr hle)).mono (Nat.sub_le r 1))
  · rw [hp_eq]
    unfold BallGenerator
    rw [MvPolynomial.C_sub]
    ring

/-- The critical threshold is positive for `m >= 1`. -/
theorem criticalLambda_pos {m : ℕ} (hm : 1 ≤ m) : 0 < criticalLambda m := by
  unfold criticalLambda
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- The odd integer `L = 2*m+1` used in the critical four-square construction. -/
def criticalL (m : ℕ) : ℝ :=
  2 * (m : ℝ) + 1

/-- The critical value is `L^2 - 1`. -/
theorem criticalLambda_eq_criticalL_sq_sub_one (m : ℕ) :
    criticalLambda m = criticalL m ^ 2 - 1 := by
  unfold criticalLambda criticalL
  ring

/-- The axis linear factor at the critical value. -/
theorem criticalLambda_sub_one_eq (m : ℕ) :
    criticalLambda m - 1 = criticalL m ^ 2 - 2 := by
  rw [criticalLambda_eq_criticalL_sq_sub_one]
  ring

/-- The diagonal linear factor at the critical value. -/
theorem criticalLambda_sub_two_div_two_eq (m : ℕ) :
    (criticalLambda m - 2) / 2 = 2 * (m : ℝ) * ((m : ℝ) + 1) - 1 := by
  unfold criticalLambda
  ring

/-- The critical value is at least two for `m >= 1`. -/
theorem two_le_criticalLambda {m : ℕ} (hm : 1 ≤ m) : (2 : ℝ) ≤ criticalLambda m := by
  unfold criticalLambda
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- Axis specialization of the symmetric cubic identity. -/
theorem Phi_axis {A : Type*} [CommRing A] (a c : A) :
    Phi a 0 c = (a - c) ^ 2 * (a + c) := by
  unfold Phi
  ring

/-- Diagonal specialization of the symmetric cubic identity. -/
theorem Phi_diag {A : Type*} [CommRing A] (a c : A) :
    Phi a a c = c * (a - c) ^ 2 := by
  unfold Phi
  ring

/-- The affine-in-`XY` rearrangement of `Phi(lambda X, lambda Y, S)`. -/
theorem four_mul_Phi_affine {A : Type*} [CommRing A] (lambda X Y S : A) :
    4 * Phi (lambda * X) (lambda * Y) S =
      S * (lambda * (X + Y) - 2 * S) ^ 2 +
        lambda ^ 2 * (4 * lambda * (X + Y) - 5 * S) * ((X + Y) ^ 2 - 4 * (X * Y)) := by
  unfold Phi
  ring

/-- An SOS polynomial whose total degree is at most `2*r` has a root-degree-bounded
SOS representation of order `r`. -/
theorem HasDegreeBoundedSOS.of_isSOS_totalDegree_le
    {σ : MvPolynomial (Fin 2) ℝ} {r : ℕ}
    (hσ : IsSOS σ) (hdeg : σ.totalDegree ≤ 2 * r) :
    HasDegreeBoundedSOS σ r := by
  obtain ⟨N, Q, hQ⟩ := hσ
  exact ⟨N, Q, hQ, sos_summand_totalDegree_le_of_sum_sq_totalDegree hQ hdeg⟩

/-- A degree-bounded SOS witness is, in particular, an SOS witness. -/
theorem HasDegreeBoundedSOS.toIsSOS {σ : MvPolynomial (Fin 2) ℝ} {r : ℕ}
    (hσ : HasDegreeBoundedSOS σ r) : IsSOS σ := by
  obtain ⟨N, Q, hQ, _hdeg⟩ := hσ
  exact ⟨N, Q, hQ⟩

/-- A finite sum of real squares can vanish only when each summand vanishes. -/
theorem sum_sq_eq_zero_iff {N : ℕ} (v : Fin N → ℝ) :
    (∑ i : Fin N, v i ^ 2) = 0 ↔ ∀ i : Fin N, v i = 0 := by
  constructor
  · intro h i
    have hi_le : v i ^ 2 ≤ 0 := by
      calc v i ^ 2
          ≤ ∑ j : Fin N, v j ^ 2 :=
              Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
        _ = 0 := h
    exact sq_eq_zero_iff.mp (le_antisymm hi_le (sq_nonneg (v i)))
  · intro h
    apply Finset.sum_eq_zero
    intro i _hi
    rw [h i]
    ring

/-- If an SOS polynomial evaluates to zero, every square root in the chosen witness vanishes. -/
theorem IsSOS.eval_zero_of_witness
    {n N : ℕ} {p : MvPolynomial (Fin n) ℝ} {Q : Fin N → MvPolynomial (Fin n) ℝ}
    (hQ : p = ∑ i : Fin N, (Q i) ^ 2) {x : Fin n → ℝ}
    (hx : MvPolynomial.eval x p = 0) :
    ∀ i : Fin N, MvPolynomial.eval x (Q i) = 0 := by
  intro i
  have hsum : (∑ j : Fin N, MvPolynomial.eval x (Q j) ^ 2) = 0 := by
    simpa [hQ, map_sum, map_pow] using hx
  exact (sum_sq_eq_zero_iff fun j : Fin N => MvPolynomial.eval x (Q j)).mp hsum i

/-- A square identity immediately gives an SOS witness. -/
theorem IsSOS_of_four_sq {n : ℕ} {p A B C D : MvPolynomial (Fin n) ℝ}
    (hp : p = A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) : IsSOS p := by
  refine ⟨4, ![A, B, C, D], ?_⟩
  rw [hp]
  simp [Fin.sum_univ_four]

/-- A square polynomial is SOS. -/
theorem IsSOS_sq {n : ℕ} (q : MvPolynomial (Fin n) ℝ) : IsSOS (q ^ 2) :=
  ⟨1, fun _ => q, by simp⟩

/-- Zero is SOS. -/
theorem IsSOS_zero {n : ℕ} : IsSOS (0 : MvPolynomial (Fin n) ℝ) := by
  refine ⟨0, fun i => Fin.elim0 i, ?_⟩
  simp

/-- Multivariate SOS witnesses are closed under addition. -/
theorem IsSOS.add {n : ℕ} {p q : MvPolynomial (Fin n) ℝ} (hp : IsSOS p) (hq : IsSOS q) :
    IsSOS (p + q) := by
  obtain ⟨Np, P, hP⟩ := hp
  obtain ⟨Nq, Q, hQ⟩ := hq
  refine ⟨Np + Nq, Fin.append P Q, ?_⟩
  rw [hP, hQ, Fin.sum_univ_add]
  simp [Fin.append]

/-- Finite sums of SOS polynomials are SOS. -/
theorem IsSOS.finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin n) ℝ) (hp : ∀ i ∈ s, IsSOS (p i)) :
    IsSOS (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (IsSOS_zero : IsSOS (0 : MvPolynomial (Fin n) ℝ))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact IsSOS.add (hp a (by simp)) (ih fun i hi => hp i (by simp [hi]))

/-- Multiplication by a square preserves multivariate SOS witnesses. -/
theorem IsSOS.sq_mul {n : ℕ} {s q : MvPolynomial (Fin n) ℝ} (hq : IsSOS q) :
    IsSOS (s ^ 2 * q) := by
  obtain ⟨N, Q, hQ⟩ := hq
  refine ⟨N, fun i => s * Q i, ?_⟩
  rw [hQ, Finset.mul_sum]
  congr 1
  ext i
  ring_nf

/-- Multiplication by a nonnegative scalar preserves multivariate SOS witnesses. -/
theorem IsSOS.const_mul {n : ℕ} {q : MvPolynomial (Fin n) ℝ} (hq : IsSOS q)
    {c : ℝ} (hc : 0 ≤ c) : IsSOS (MvPolynomial.C c * q) := by
  obtain ⟨N, Q, hQ⟩ := hq
  refine ⟨N, fun i => MvPolynomial.C (Real.sqrt c) * Q i, ?_⟩
  rw [hQ, Finset.mul_sum]
  congr 1
  ext i
  rw [mul_pow, ← MvPolynomial.C_pow, Real.sq_sqrt hc]

/-- Multiplication by the square of the homogenizing variable preserves ternary SOS witnesses. -/
theorem IsSOS.z_sq_mul {q : MvPolynomial (Fin 3) ℝ} (hq : IsSOS q) :
    IsSOS ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 * q) :=
  IsSOS.sq_mul hq

/-- A square multiplied by `x^2 + y^2 + z^2` is SOS. -/
theorem IsSOS.sphereSq_mul_square (q : MvPolynomial (Fin 3) ℝ) :
    IsSOS (sphereSq * q ^ 2) := by
  refine IsSOS_of_four_sq
    (A := (X 0 : MvPolynomial (Fin 3) ℝ) * q)
    (B := (X 1 : MvPolynomial (Fin 3) ℝ) * q)
    (C := (X 2 : MvPolynomial (Fin 3) ℝ) * q)
    (D := 0) ?_
  unfold sphereSq
  ring

/-- A finite sum of squares multiplied by `x^2 + y^2 + z^2` is SOS. -/
theorem IsSOS.sphereSq_mul_sum_squares {N : ℕ} (Q : Fin N → MvPolynomial (Fin 3) ℝ) :
    IsSOS (sphereSq * ∑ i : Fin N, (Q i) ^ 2) := by
  rw [Finset.mul_sum]
  exact IsSOS.finset_sum (Finset.univ : Finset (Fin N))
    (fun i => sphereSq * (Q i) ^ 2)
    (fun i _ => IsSOS.sphereSq_mul_square (Q i))

/-- Multiplication by `lambda*z^2` preserves ternary SOS witnesses for nonnegative `lambda`. -/
theorem IsSOS.lambda_z_sq_mul {lambda : ℝ} (hLam : 0 ≤ lambda)
    {q : MvPolynomial (Fin 3) ℝ} (hq : IsSOS q) :
    IsSOS (MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 * q) := by
  simpa [mul_assoc] using IsSOS.const_mul (IsSOS.z_sq_mul hq) hLam

/-- A square multiplied by `lambda*z^2` is SOS for nonnegative `lambda`. -/
theorem IsSOS.lambda_z_sq_mul_square {lambda : ℝ} (hLam : 0 ≤ lambda)
    (q : MvPolynomial (Fin 3) ℝ) :
    IsSOS (MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 * q ^ 2) := by
  refine IsSOS_of_four_sq
    (A := MvPolynomial.C (Real.sqrt lambda) * (X 2 : MvPolynomial (Fin 3) ℝ) * q)
    (B := 0) (C := 0) (D := 0) ?_
  have hC : MvPolynomial.C lambda =
      (MvPolynomial.C (Real.sqrt lambda) : MvPolynomial (Fin 3) ℝ) ^ 2 := by
    rw [← MvPolynomial.C_pow, Real.sq_sqrt hLam]
  rw [hC]
  ring

/-- A square multiplied by `lambda*z^2*(x^2+y^2+z^2)` is SOS for nonnegative `lambda`. -/
theorem IsSOS.lambda_z_sq_sphereSq_mul_square {lambda : ℝ} (hLam : 0 ≤ lambda)
    (q : MvPolynomial (Fin 3) ℝ) :
    IsSOS (MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 * sphereSq * q ^ 2) := by
  refine IsSOS_of_four_sq
    (A := MvPolynomial.C (Real.sqrt lambda) * (X 2 : MvPolynomial (Fin 3) ℝ) *
      (X 0 : MvPolynomial (Fin 3) ℝ) * q)
    (B := MvPolynomial.C (Real.sqrt lambda) * (X 2 : MvPolynomial (Fin 3) ℝ) *
      (X 1 : MvPolynomial (Fin 3) ℝ) * q)
    (C := MvPolynomial.C (Real.sqrt lambda) * (X 2 : MvPolynomial (Fin 3) ℝ) *
      (X 2 : MvPolynomial (Fin 3) ℝ) * q)
    (D := 0) ?_
  unfold sphereSq
  have hC : MvPolynomial.C lambda =
      (MvPolynomial.C (Real.sqrt lambda) : MvPolynomial (Fin 3) ℝ) ^ 2 := by
    rw [← MvPolynomial.C_pow, Real.sq_sqrt hLam]
  rw [hC]
  ring

/-- Symmetrizing an SOS witness under `z ↦ -z` preserves the represented invariant form. -/
theorem IsSOS.exists_z_reflection_symmetrized_witness {p : MvPolynomial (Fin 3) ℝ}
    (hp : IsSOS p) (hinv : zReflect3 p = p) :
    ∃ M : ℕ, ∃ Q : Fin M → MvPolynomial (Fin 3) ℝ,
      p = ∑ i : Fin M, (Q i) ^ 2 := by
  obtain ⟨N, H, hH⟩ := hp
  let c : MvPolynomial (Fin 3) ℝ := MvPolynomial.C ((2 : ℝ)⁻¹)
  refine ⟨N + N, Fin.append (fun i : Fin N => c * (H i + zReflect3 (H i)))
    (fun i : Fin N => c * (H i - zReflect3 (H i))), ?_⟩
  have hmap : zReflect3 p = ∑ i : Fin N, (zReflect3 (H i)) ^ 2 := by
    rw [hH]
    simp only [map_sum, map_pow]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [show (∑ i : Fin N, (c * (H i + zReflect3 (H i))) ^ 2) =
      c ^ 2 * ∑ i : Fin N, (H i + zReflect3 (H i)) ^ 2 by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]]
  rw [show (∑ i : Fin N, (c * (H i - zReflect3 (H i))) ^ 2) =
      c ^ 2 * ∑ i : Fin N, (H i - zReflect3 (H i)) ^ 2 by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]]
  have hc_sq : c ^ 2 = MvPolynomial.C ((4 : ℝ)⁻¹) := by
    dsimp [c]
    rw [← MvPolynomial.C_pow]
    congr 1
    norm_num [inv_pow]
  rw [hc_sq]
  have hcombine :
      MvPolynomial.C ((4 : ℝ)⁻¹) * (∑ i : Fin N, (H i + zReflect3 (H i)) ^ 2) +
        MvPolynomial.C ((4 : ℝ)⁻¹) * (∑ i : Fin N, (H i - zReflect3 (H i)) ^ 2) =
      MvPolynomial.C ((4 : ℝ)⁻¹) *
        (∑ i : Fin N, ((H i + zReflect3 (H i)) ^ 2 + (H i - zReflect3 (H i)) ^ 2)) := by
    rw [Finset.sum_add_distrib, mul_add]
  rw [hcombine]
  have hpair :
      (∑ i : Fin N, ((H i + zReflect3 (H i)) ^ 2 + (H i - zReflect3 (H i)) ^ 2)) =
        2 * ((∑ i : Fin N, (H i) ^ 2) + ∑ i : Fin N, (zReflect3 (H i)) ^ 2) := by
    calc
      (∑ i : Fin N, ((H i + zReflect3 (H i)) ^ 2 + (H i - zReflect3 (H i)) ^ 2))
          = ∑ i : Fin N, (2 * (H i) ^ 2 + 2 * (zReflect3 (H i)) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 2 * ((∑ i : Fin N, (H i) ^ 2) + ∑ i : Fin N, (zReflect3 (H i)) ^ 2) := by
            rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
  rw [hpair]
  rw [← hH, ← hmap, hinv]
  rw [show (2 : MvPolynomial (Fin 3) ℝ) * (p + p) =
      (4 : MvPolynomial (Fin 3) ℝ) * p by ring]
  rw [show (4 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (4 : ℝ) from
    (MvPolynomial.C_eq_coe_nat 4).symm]
  rw [show MvPolynomial.C ((4 : ℝ)⁻¹) * (MvPolynomial.C (4 : ℝ) * p) =
      (MvPolynomial.C ((4 : ℝ)⁻¹) * MvPolynomial.C (4 : ℝ)) * p by ring]
  rw [← MvPolynomial.C_mul]
  norm_num

/-- Symmetrizing an invariant SOS witness under `z ↦ -z` separates every square root into
its reflection-invariant and reflection-anti-invariant parts. -/
theorem IsSOS.exists_z_reflection_even_odd_witness {p : MvPolynomial (Fin 3) ℝ}
    (hp : IsSOS p) (hinv : zReflect3 p = p) :
    ∃ N : ℕ, ∃ A B : Fin N → MvPolynomial (Fin 3) ℝ,
      p = (∑ i : Fin N, (A i) ^ 2) + ∑ i : Fin N, (B i) ^ 2 ∧
      (∀ i : Fin N, zReflect3 (A i) = A i) ∧
      (∀ i : Fin N, zReflect3 (B i) = -B i) := by
  obtain ⟨N, H, hH⟩ := hp
  let c : MvPolynomial (Fin 3) ℝ := MvPolynomial.C ((2 : ℝ)⁻¹)
  let A : Fin N → MvPolynomial (Fin 3) ℝ := fun i => c * (H i + zReflect3 (H i))
  let B : Fin N → MvPolynomial (Fin 3) ℝ := fun i => c * (H i - zReflect3 (H i))
  refine ⟨N, A, B, ?_, ?_, ?_⟩
  · have hmap : zReflect3 p = ∑ i : Fin N, (zReflect3 (H i)) ^ 2 := by
      rw [hH]
      simp only [map_sum, map_pow]
    dsimp [A, B, c]
    rw [show (∑ i : Fin N,
          (MvPolynomial.C ((2 : ℝ)⁻¹) * (H i + zReflect3 (H i))) ^ 2) =
        MvPolynomial.C ((4 : ℝ)⁻¹) *
          ∑ i : Fin N, (H i + zReflect3 (H i)) ^ 2 by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
        rw [← MvPolynomial.C_pow]
        norm_num [inv_pow]]
    rw [show (∑ i : Fin N,
          (MvPolynomial.C ((2 : ℝ)⁻¹) * (H i - zReflect3 (H i))) ^ 2) =
        MvPolynomial.C ((4 : ℝ)⁻¹) *
          ∑ i : Fin N, (H i - zReflect3 (H i)) ^ 2 by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
        rw [← MvPolynomial.C_pow]
        norm_num [inv_pow]]
    rw [show MvPolynomial.C ((4 : ℝ)⁻¹) *
          (∑ i : Fin N, (H i + zReflect3 (H i)) ^ 2) +
        MvPolynomial.C ((4 : ℝ)⁻¹) *
          (∑ i : Fin N, (H i - zReflect3 (H i)) ^ 2) =
        MvPolynomial.C ((4 : ℝ)⁻¹) *
          (∑ i : Fin N,
            ((H i + zReflect3 (H i)) ^ 2 + (H i - zReflect3 (H i)) ^ 2)) by
        rw [Finset.sum_add_distrib, mul_add]]
    rw [show (∑ i : Fin N,
          ((H i + zReflect3 (H i)) ^ 2 + (H i - zReflect3 (H i)) ^ 2)) =
        2 * ((∑ i : Fin N, (H i) ^ 2) + ∑ i : Fin N, (zReflect3 (H i)) ^ 2) by
        calc
          (∑ i : Fin N,
              ((H i + zReflect3 (H i)) ^ 2 + (H i - zReflect3 (H i)) ^ 2))
              = ∑ i : Fin N, (2 * (H i) ^ 2 + 2 * (zReflect3 (H i)) ^ 2) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
          _ = 2 * ((∑ i : Fin N, (H i) ^ 2) +
                ∑ i : Fin N, (zReflect3 (H i)) ^ 2) := by
                rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]]
    rw [← hH, ← hmap, hinv]
    rw [show (2 : MvPolynomial (Fin 3) ℝ) * (p + p) =
        (4 : MvPolynomial (Fin 3) ℝ) * p by ring]
    rw [show (4 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (4 : ℝ) from
      (MvPolynomial.C_eq_coe_nat 4).symm]
    rw [show MvPolynomial.C ((4 : ℝ)⁻¹) * (MvPolynomial.C (4 : ℝ) * p) =
        (MvPolynomial.C ((4 : ℝ)⁻¹) * MvPolynomial.C (4 : ℝ)) * p by ring]
    rw [← MvPolynomial.C_mul]
    norm_num
  · intro i
    dsimp [A, c]
    simp [zReflect3_involutive]
    ring_nf
  · intro i
    dsimp [B, c]
    simp [zReflect3_involutive]
    ring_nf

/-- Multiplication by a scalar constant does not increase total degree. -/
theorem totalDegree_C_mul_le {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    (MvPolynomial.C c * p).totalDegree ≤ p.totalDegree := by
  calc (MvPolynomial.C c * p).totalDegree
      ≤ (MvPolynomial.C c : MvPolynomial (Fin n) ℝ).totalDegree + p.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ = 0 + p.totalDegree := by simp [MvPolynomial.totalDegree_C]
    _ = p.totalDegree := Nat.zero_add p.totalDegree

/-- Substitution by polynomials of degree at most one does not increase total degree. -/
theorem totalDegree_aeval_le_of_linear {n m : ℕ}
    (f : Fin n → MvPolynomial (Fin m) ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : MvPolynomial (Fin n) ℝ) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  calc
    (algebraMap ℝ (MvPolynomial (Fin m) ℝ) (MvPolynomial.coeff d p) *
        d.prod fun i k => f i ^ k).totalDegree
        ≤ (algebraMap ℝ (MvPolynomial (Fin m) ℝ) (MvPolynomial.coeff d p)).totalDegree +
            (d.prod fun i k => f i ^ k).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ = (d.prod fun i k => f i ^ k).totalDegree := by
          rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C]
          simp
    _ ≤ ∑ i ∈ d.support, (f i ^ d i).totalDegree := by
          simp only [Finsupp.prod]
          exact MvPolynomial.totalDegree_finset_prod d.support _
    _ ≤ ∑ i ∈ d.support, d i := by
          apply Finset.sum_le_sum
          intro i _
          calc
            (f i ^ d i).totalDegree ≤ d i * (f i).totalDegree :=
              MvPolynomial.totalDegree_pow _ _
            _ ≤ d i * 1 := Nat.mul_le_mul_left (d i) (hf i)
            _ = d i := Nat.mul_one (d i)
    _ = d.sum (fun _ e => e) := by rfl
    _ ≤ p.totalDegree := Finset.le_sup (f := fun s => s.sum fun _ e => e) hd

/-- Substitution by polynomials of degree at most two at most doubles total degree. -/
theorem totalDegree_aeval_le_of_quadratic {n m : ℕ}
    (f : Fin n → MvPolynomial (Fin m) ℝ) (hf : ∀ i, (f i).totalDegree ≤ 2)
    (p : MvPolynomial (Fin n) ℝ) :
    (MvPolynomial.aeval f p).totalDegree ≤ 2 * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  calc
    (algebraMap ℝ (MvPolynomial (Fin m) ℝ) (MvPolynomial.coeff d p) *
        d.prod fun i k => f i ^ k).totalDegree
        ≤ (algebraMap ℝ (MvPolynomial (Fin m) ℝ) (MvPolynomial.coeff d p)).totalDegree +
            (d.prod fun i k => f i ^ k).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ = (d.prod fun i k => f i ^ k).totalDegree := by
          rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C]
          simp
    _ ≤ ∑ i ∈ d.support, (f i ^ d i).totalDegree := by
          simp only [Finsupp.prod]
          exact MvPolynomial.totalDegree_finset_prod d.support _
    _ ≤ ∑ i ∈ d.support, 2 * d i := by
          apply Finset.sum_le_sum
          intro i _
          calc
            (f i ^ d i).totalDegree ≤ d i * (f i).totalDegree :=
              MvPolynomial.totalDegree_pow _ _
            _ ≤ d i * 2 := Nat.mul_le_mul_left (d i) (hf i)
            _ = 2 * d i := by omega
    _ = 2 * d.sum (fun _ e => e) := by
          simp only [Finsupp.sum]
          rw [Finset.mul_sum]
    _ ≤ 2 * p.totalDegree :=
          Nat.mul_le_mul_left 2 (Finset.le_sup (f := fun s => s.sum fun _ e => e) hd)

/-- Reflection in the homogenizing variable does not increase total degree. -/
theorem zReflect3_totalDegree_le (p : MvPolynomial (Fin 3) ℝ) :
    (zReflect3 p).totalDegree ≤ p.totalDegree := by
  unfold zReflect3
  apply totalDegree_aeval_le_of_linear
  intro i
  fin_cases i <;> simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_neg]

/-- Dehomogenizing a ternary polynomial by setting `z = 1` does not increase total degree. -/
theorem dehomogenize3To2_totalDegree_le (p : MvPolynomial (Fin 3) ℝ) :
    (dehomogenize3To2 p).totalDegree ≤ p.totalDegree := by
  unfold dehomogenize3To2
  apply totalDegree_aeval_le_of_linear
  intro i
  fin_cases i <;> simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_one]

/-- Total-degree bound for a product of three polynomials from bounds on the factors. -/
theorem totalDegree_mul_three_le {p q r : MvPolynomial (Fin 3) ℝ} {dp dq dr : ℕ}
    (hp : p.totalDegree ≤ dp) (hq : q.totalDegree ≤ dq) (hr : r.totalDegree ≤ dr) :
    (p * q * r).totalDegree ≤ dp + dq + dr := by
  calc (p * q * r).totalDegree
      ≤ (p * q).totalDegree + r.totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ (p.totalDegree + q.totalDegree) + r.totalDegree :=
        Nat.add_le_add_right (MvPolynomial.totalDegree_mul p q) r.totalDegree
    _ ≤ (dp + dq) + dr := Nat.add_le_add (Nat.add_le_add hp hq) hr
    _ = dp + dq + dr := by omega

/-- If two polynomials have degree at most `d`, then `p^2*q` has degree at most `3*d`. -/
theorem totalDegree_pow_two_mul_le {p q : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    (p ^ 2 * q).totalDegree ≤ 3 * d := by
  calc (p ^ 2 * q).totalDegree
      ≤ (p ^ 2).totalDegree + q.totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 2 * d + d := Nat.add_le_add
        ((MvPolynomial.totalDegree_pow p 2).trans (Nat.mul_le_mul_left 2 hp)) hq
    _ = 3 * d := by omega

/-- The Robinson cubic `Phi` triples a common total-degree bound on its arguments. -/
theorem Phi_totalDegree_le {a b c : MvPolynomial (Fin 3) ℝ} {d : ℕ}
    (ha : a.totalDegree ≤ d) (hb : b.totalDegree ≤ d) (hc : c.totalDegree ≤ d) :
    (Phi a b c).totalDegree ≤ 3 * d := by
  have h3a : (a ^ 3).totalDegree ≤ 3 * d :=
    (MvPolynomial.totalDegree_pow a 3).trans (Nat.mul_le_mul_left 3 ha)
  have h3b : (b ^ 3).totalDegree ≤ 3 * d :=
    (MvPolynomial.totalDegree_pow b 3).trans (Nat.mul_le_mul_left 3 hb)
  have h3c : (c ^ 3).totalDegree ≤ 3 * d :=
    (MvPolynomial.totalDegree_pow c 3).trans (Nat.mul_le_mul_left 3 hc)
  have habc : (3 * a * b * c).totalDegree ≤ 3 * d := by
    calc (3 * a * b * c).totalDegree
        = (MvPolynomial.C (3 : ℝ) * (a * b * c)).totalDegree := by
          congr 1
          rw [show (3 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (3 : ℝ) from
            (MvPolynomial.C_eq_coe_nat 3).symm]
          ring
      _ ≤ (a * b * c).totalDegree := totalDegree_C_mul_le (n := 3) (3 : ℝ) (a * b * c)
      _ ≤ d + d + d := totalDegree_mul_three_le ha hb hc
      _ = 3 * d := by omega
  have ha2b : (a ^ 2 * b).totalDegree ≤ 3 * d := totalDegree_pow_two_mul_le ha hb
  have ha2c : (a ^ 2 * c).totalDegree ≤ 3 * d := totalDegree_pow_two_mul_le ha hc
  have hb2a : (b ^ 2 * a).totalDegree ≤ 3 * d := totalDegree_pow_two_mul_le hb ha
  have hb2c : (b ^ 2 * c).totalDegree ≤ 3 * d := totalDegree_pow_two_mul_le hb hc
  have hc2a : (c ^ 2 * a).totalDegree ≤ 3 * d := totalDegree_pow_two_mul_le hc ha
  have hc2b : (c ^ 2 * b).totalDegree ≤ 3 * d := totalDegree_pow_two_mul_le hc hb
  have hsum :
      (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a +
        c ^ 2 * b).totalDegree ≤ 3 * d := by
    repeat first | apply le_trans (MvPolynomial.totalDegree_add _ _) | apply max_le
    all_goals assumption
  unfold Phi
  repeat first | apply le_trans (MvPolynomial.totalDegree_add _ _) |
    apply le_trans (MvPolynomial.totalDegree_sub _ _) | apply max_le
  all_goals assumption

/-- The squared-radius form has total degree at most two. -/
theorem sphereSq_totalDegree_le_two :
    (sphereSq : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 2 := by
  unfold sphereSq
  calc ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + X 1 ^ 2 + X 2 ^ 2).totalDegree
      ≤ max ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + X 1 ^ 2).totalDegree
          ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := by
      apply max_le
      · calc ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + X 1 ^ 2).totalDegree
            ≤ max ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree
                ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree :=
              MvPolynomial.totalDegree_add _ _
          _ ≤ 2 := by simp [MvPolynomial.totalDegree_X_pow]
      · simp [MvPolynomial.totalDegree_X_pow]

/-- Scalar multiples of coordinate squares have total degree at most two. -/
theorem C_mul_X_pow_two_totalDegree_le_two (lambda : ℝ) (i : Fin 3) :
    (MvPolynomial.C lambda * (X i : MvPolynomial (Fin 3) ℝ) ^ 2).totalDegree ≤ 2 := by
  exact (totalDegree_C_mul_le lambda ((X i : MvPolynomial (Fin 3) ℝ) ^ 2)).trans
    (by simp [MvPolynomial.totalDegree_X_pow])

/-- The threshold form `P_{m,lambda}` has the expected homogeneous total-degree bound. -/
theorem Pmlambda_totalDegree_le (m : ℕ) (lambda : ℝ) :
    (Pmlambda m lambda).totalDegree ≤ 2 * (m + 3) := by
  unfold Pmlambda
  calc (sphereSq ^ m *
        Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
          (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) sphereSq).totalDegree
      ≤ (sphereSq ^ m).totalDegree +
          (Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
            (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2)
            sphereSq).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ m * 2 + 3 * 2 := Nat.add_le_add
        ((MvPolynomial.totalDegree_pow sphereSq m).trans
          (Nat.mul_le_mul_left m sphereSq_totalDegree_le_two))
        (Phi_totalDegree_le (C_mul_X_pow_two_totalDegree_le_two lambda 0)
          (C_mul_X_pow_two_totalDegree_le_two lambda 1) sphereSq_totalDegree_le_two)
    _ = 2 * (m + 3) := by omega

/-- Symmetrizing an invariant SOS witness under `z ↦ -z` can be done without increasing
the square-root degree bound. -/
theorem IsSOS.exists_z_reflection_even_odd_witness_degree_bound
    {p : MvPolynomial (Fin 3) ℝ} {r : ℕ}
    (hp : IsSOS p) (hinv : zReflect3 p = p) (hdeg : p.totalDegree ≤ 2 * r) :
    ∃ N : ℕ, ∃ A B : Fin N → MvPolynomial (Fin 3) ℝ,
      p = (∑ i : Fin N, (A i) ^ 2) + ∑ i : Fin N, (B i) ^ 2 ∧
      (∀ i : Fin N, zReflect3 (A i) = A i) ∧
      (∀ i : Fin N, zReflect3 (B i) = -B i) ∧
      (∀ i : Fin N, (A i).totalDegree ≤ r) ∧
      (∀ i : Fin N, (B i).totalDegree ≤ r) := by
  obtain ⟨N, H, hH⟩ := hp
  have hHdeg : ∀ i : Fin N, (H i).totalDegree ≤ r :=
    sos_summand_totalDegree_le_of_sum_sq_totalDegree hH hdeg
  let c : MvPolynomial (Fin 3) ℝ := MvPolynomial.C ((2 : ℝ)⁻¹)
  let A : Fin N → MvPolynomial (Fin 3) ℝ := fun i => c * (H i + zReflect3 (H i))
  let B : Fin N → MvPolynomial (Fin 3) ℝ := fun i => c * (H i - zReflect3 (H i))
  refine ⟨N, A, B, ?_, ?_, ?_, ?_, ?_⟩
  · have hmap : zReflect3 p = ∑ i : Fin N, (zReflect3 (H i)) ^ 2 := by
      rw [hH]
      simp only [map_sum, map_pow]
    dsimp [A, B, c]
    rw [show (∑ i : Fin N,
          (MvPolynomial.C ((2 : ℝ)⁻¹) * (H i + zReflect3 (H i))) ^ 2) =
        MvPolynomial.C ((4 : ℝ)⁻¹) *
          ∑ i : Fin N, (H i + zReflect3 (H i)) ^ 2 by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
        rw [← MvPolynomial.C_pow]
        norm_num [inv_pow]]
    rw [show (∑ i : Fin N,
          (MvPolynomial.C ((2 : ℝ)⁻¹) * (H i - zReflect3 (H i))) ^ 2) =
        MvPolynomial.C ((4 : ℝ)⁻¹) *
          ∑ i : Fin N, (H i - zReflect3 (H i)) ^ 2 by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
        rw [← MvPolynomial.C_pow]
        norm_num [inv_pow]]
    rw [show MvPolynomial.C ((4 : ℝ)⁻¹) *
          (∑ i : Fin N, (H i + zReflect3 (H i)) ^ 2) +
        MvPolynomial.C ((4 : ℝ)⁻¹) *
          (∑ i : Fin N, (H i - zReflect3 (H i)) ^ 2) =
        MvPolynomial.C ((4 : ℝ)⁻¹) *
          (∑ i : Fin N,
            ((H i + zReflect3 (H i)) ^ 2 + (H i - zReflect3 (H i)) ^ 2)) by
        rw [Finset.sum_add_distrib, mul_add]]
    rw [show (∑ i : Fin N,
          ((H i + zReflect3 (H i)) ^ 2 + (H i - zReflect3 (H i)) ^ 2)) =
        2 * ((∑ i : Fin N, (H i) ^ 2) + ∑ i : Fin N, (zReflect3 (H i)) ^ 2) by
        calc
          (∑ i : Fin N,
              ((H i + zReflect3 (H i)) ^ 2 + (H i - zReflect3 (H i)) ^ 2))
              = ∑ i : Fin N, (2 * (H i) ^ 2 + 2 * (zReflect3 (H i)) ^ 2) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
          _ = 2 * ((∑ i : Fin N, (H i) ^ 2) +
                ∑ i : Fin N, (zReflect3 (H i)) ^ 2) := by
                rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]]
    rw [← hH, ← hmap, hinv]
    rw [show (2 : MvPolynomial (Fin 3) ℝ) * (p + p) =
        (4 : MvPolynomial (Fin 3) ℝ) * p by ring]
    rw [show (4 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (4 : ℝ) from
      (MvPolynomial.C_eq_coe_nat 4).symm]
    rw [show MvPolynomial.C ((4 : ℝ)⁻¹) * (MvPolynomial.C (4 : ℝ) * p) =
        (MvPolynomial.C ((4 : ℝ)⁻¹) * MvPolynomial.C (4 : ℝ)) * p by ring]
    rw [← MvPolynomial.C_mul]
    norm_num
  · intro i
    dsimp [A, c]
    simp [zReflect3_involutive]
    ring_nf
  · intro i
    dsimp [B, c]
    simp [zReflect3_involutive]
    ring_nf
  · intro i
    dsimp [A, c]
    calc (MvPolynomial.C ((2 : ℝ)⁻¹) * (H i + zReflect3 (H i))).totalDegree
        ≤ (H i + zReflect3 (H i)).totalDegree := totalDegree_C_mul_le _ _
      _ ≤ max (H i).totalDegree (zReflect3 (H i)).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ r := max_le (hHdeg i) ((zReflect3_totalDegree_le (H i)).trans (hHdeg i))
  · intro i
    dsimp [B, c]
    calc (MvPolynomial.C ((2 : ℝ)⁻¹) * (H i - zReflect3 (H i))).totalDegree
        ≤ (H i - zReflect3 (H i)).totalDegree := totalDegree_C_mul_le _ _
      _ ≤ max (H i).totalDegree (zReflect3 (H i)).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ ≤ r := max_le (hHdeg i) ((zReflect3_totalDegree_le (H i)).trans (hHdeg i))

/-- An invariant ternary SOS has a witness whose roots are square-substituted even parts
and `z` times square-substituted odd parts. -/
theorem IsSOS.exists_zSquareSubst3_even_odd_witness {p : MvPolynomial (Fin 3) ℝ}
    (hp : IsSOS p) (hinv : zReflect3 p = p) :
    ∃ N : ℕ, ∃ A B : Fin N → MvPolynomial (Fin 3) ℝ,
      p = (∑ i : Fin N, (zSquareSubst3 (A i)) ^ 2) +
        ∑ i : Fin N,
          ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 (B i)) ^ 2 := by
  obtain ⟨N, A, B, hsum, hA, hB⟩ := IsSOS.exists_z_reflection_even_odd_witness hp hinv
  choose A0 hA0 using fun i => exists_zSquareSubst3_of_zReflect3_eq_self (hA i)
  choose B0 hB0 using fun i => exists_X_two_mul_zSquareSubst3_of_zReflect3_eq_neg (hB i)
  refine ⟨N, A0, B0, ?_⟩
  rw [hsum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [hA0 i]
  · apply Finset.sum_congr rfl
    intro i _
    rw [hB0 i]

/-- SOS witnesses are preserved by multivariate polynomial substitution. -/
theorem IsSOS.aeval {n m : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : IsSOS p) (f : Fin n → MvPolynomial (Fin m) ℝ) :
    IsSOS (MvPolynomial.aeval f p) := by
  obtain ⟨N, Q, hQ⟩ := hp
  refine ⟨N, fun i => MvPolynomial.aeval f (Q i), ?_⟩
  rw [hQ]
  simp only [map_sum, map_pow]

/-- Reflection in the homogenizing variable preserves ternary SOS witnesses. -/
theorem IsSOS.map_zReflect3 {p : MvPolynomial (Fin 3) ℝ} (hp : IsSOS p) :
    IsSOS (zReflect3 p) := by
  simpa [zReflect3] using
    IsSOS.aeval hp ![(X 0 : MvPolynomial (Fin 3) ℝ), X 1, -X 2]

/-- Exponent vector used by bounded homogenization from `(x,y)` to `(x,y,w)`. -/
def homExp2To3 (d : ℕ) (e : Fin 2 →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single (0 : Fin 3) (e 0) + Finsupp.single (1 : Fin 3) (e 1) +
    Finsupp.single (2 : Fin 3) (d - e.degree)

/-- Exponent arithmetic for bounded homogenization. -/
theorem homExp2To3_add {d e : ℕ} {a b : Fin 2 →₀ ℕ}
    (ha : a.degree ≤ d) (hb : b.degree ≤ e) :
    homExp2To3 (d + e) (a + b) = homExp2To3 d a + homExp2To3 e b := by
  ext i
  fin_cases i <;> simp [homExp2To3]
  omega

/-- Bounded homogenization from two variables to three variables.

`homogenize2To3 d p` is `w^d p(x/w,y/w)` when `p.totalDegree <= d`. If a
monomial has degree above `d`, the exponent of `w` is truncated by natural subtraction; all
intended uses carry a total-degree bound preventing that case.
-/
def homogenize2To3 (d : ℕ) (p : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  p.sum fun e c => MvPolynomial.monomial (homExp2To3 d e) c

/-- Homogenization as an explicit finite sum over the support. -/
theorem homogenize2To3_as_sum_support (d : ℕ) (p : MvPolynomial (Fin 2) ℝ) :
    homogenize2To3 d p =
      ∑ e ∈ p.support, MvPolynomial.monomial (homExp2To3 d e) (MvPolynomial.coeff e p) := by
  unfold homogenize2To3
  rfl

/-- A monomial in the support of a degree-bounded polynomial has bounded degree. -/
theorem support_degree_le_of_totalDegree_le {p : MvPolynomial (Fin 2) ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) {e : Fin 2 →₀ ℕ} (he : e ∈ p.support) : e.degree ≤ d := by
  exact (MvPolynomial.le_totalDegree he).trans hp

/-- Homogenization of a monomial. -/
theorem homogenize2To3_monomial (d : ℕ) (e : Fin 2 →₀ ℕ) (c : ℝ) :
    homogenize2To3 d (MvPolynomial.monomial e c : MvPolynomial (Fin 2) ℝ) =
      MvPolynomial.monomial (homExp2To3 d e) c := by
  by_cases hc : c = 0
  · simp [hc, homogenize2To3]
  · simp [homogenize2To3]

/-- Bounded homogenization is multiplicative on monomials when the target degrees match. -/
theorem homogenize2To3_monomial_mul {d e : ℕ} {a b : Fin 2 →₀ ℕ} {c k : ℝ}
    (ha : a.degree ≤ d) (hb : b.degree ≤ e) :
    homogenize2To3 (d + e)
        ((MvPolynomial.monomial a c : MvPolynomial (Fin 2) ℝ) * MvPolynomial.monomial b k) =
      homogenize2To3 d (MvPolynomial.monomial a c : MvPolynomial (Fin 2) ℝ) *
        homogenize2To3 e (MvPolynomial.monomial b k : MvPolynomial (Fin 2) ℝ) := by
  rw [MvPolynomial.monomial_mul]
  rw [homogenize2To3_monomial, homogenize2To3_monomial, homogenize2To3_monomial]
  rw [homExp2To3_add ha hb]
  rw [MvPolynomial.monomial_mul]

/-- Homogenizing zero gives zero. -/
theorem homogenize2To3_zero (d : ℕ) :
    homogenize2To3 d (0 : MvPolynomial (Fin 2) ℝ) = 0 := by
  simp [homogenize2To3]

/-- Homogenization is additive. -/
theorem homogenize2To3_add (d : ℕ) (p q : MvPolynomial (Fin 2) ℝ) :
    homogenize2To3 d (p + q) = homogenize2To3 d p + homogenize2To3 d q := by
  classical
  unfold homogenize2To3
  exact Finsupp.sum_add_index
    (fun e => by simp)
    (fun e c₁ c₂ => by simp [MvPolynomial.monomial])

/-- Homogenization commutes with negation. -/
theorem homogenize2To3_neg (d : ℕ) (p : MvPolynomial (Fin 2) ℝ) :
    homogenize2To3 d (-p) = -homogenize2To3 d p := by
  unfold homogenize2To3
  rw [Finsupp.sum_neg_index]
  · simp [MvPolynomial.monomial]
  · intro a
    simp

/-- Homogenization commutes with subtraction. -/
theorem homogenize2To3_sub (d : ℕ) (p q : MvPolynomial (Fin 2) ℝ) :
    homogenize2To3 d (p - q) = homogenize2To3 d p - homogenize2To3 d q := by
  unfold homogenize2To3
  exact Finsupp.sum_sub_index (fun a b1 b2 => by simp [MvPolynomial.monomial, sub_eq_add_neg])

/-- Homogenization commutes with finite sums. -/
theorem homogenize2To3_finset_sum {ι : Type*} (s : Finset ι)
    (d : ℕ) (p : ι → MvPolynomial (Fin 2) ℝ) :
    homogenize2To3 d (∑ i ∈ s, p i) = ∑ i ∈ s, homogenize2To3 d (p i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [homogenize2To3_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, homogenize2To3_add, ih, Finset.sum_insert ha]

/-- Homogenizing a constant to degree `d` multiplies it by the homogenizing variable. -/
theorem homogenize2To3_C (d : ℕ) (c : ℝ) :
    homogenize2To3 d (MvPolynomial.C c : MvPolynomial (Fin 2) ℝ) =
      MvPolynomial.C c * (X 2 : MvPolynomial (Fin 3) ℝ) ^ d := by
  rw [show (MvPolynomial.C c : MvPolynomial (Fin 2) ℝ) = MvPolynomial.monomial 0 c by simp]
  rw [homogenize2To3_monomial]
  rw [show homExp2To3 d 0 = Finsupp.single (2 : Fin 3) d by
    ext i
    fin_cases i <;> simp [homExp2To3]]
  rw [MvPolynomial.monomial_eq]
  simp

/-- Exact-degree homogenization of a pure `x`-power. -/
theorem homogenize2To3_X0_pow_self (n : ℕ) :
    homogenize2To3 n ((X 0 : MvPolynomial (Fin 2) ℝ) ^ n) =
      (X 0 : MvPolynomial (Fin 3) ℝ) ^ n := by
  rw [MvPolynomial.X_pow_eq_monomial]
  rw [homogenize2To3_monomial]
  rw [show homExp2To3 n (Finsupp.single (0 : Fin 2) n) =
      Finsupp.single (0 : Fin 3) n by
    ext i
    fin_cases i <;> simp [homExp2To3]]
  rw [← MvPolynomial.X_pow_eq_monomial]

/-- Exact-degree homogenization of a pure `y`-power. -/
theorem homogenize2To3_X1_pow_self (n : ℕ) :
    homogenize2To3 n ((X 1 : MvPolynomial (Fin 2) ℝ) ^ n) =
      (X 1 : MvPolynomial (Fin 3) ℝ) ^ n := by
  rw [MvPolynomial.X_pow_eq_monomial]
  rw [homogenize2To3_monomial]
  rw [show homExp2To3 n (Finsupp.single (1 : Fin 2) n) =
      Finsupp.single (1 : Fin 3) n by
    ext i
    fin_cases i <;> simp [homExp2To3]]
  rw [← MvPolynomial.X_pow_eq_monomial]

/-- Homogenizing the affine ball generator gives the homogeneous ball generator. -/
theorem homogenize2To3_ballGenerator (lambda : ℝ) :
    homogenize2To3 2 (BallGenerator lambda) = HomBallGenerator lambda := by
  have hC : homogenize2To3 2 (MvPolynomial.C lambda : MvPolynomial (Fin 2) ℝ) =
      MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 := by
    rw [show (MvPolynomial.C lambda : MvPolynomial (Fin 2) ℝ) =
        MvPolynomial.monomial 0 lambda by simp]
    rw [homogenize2To3_monomial]
    rw [show homExp2To3 2 0 = Finsupp.single (2 : Fin 3) 2 by
      ext i
      fin_cases i <;> simp [homExp2To3]]
    rw [MvPolynomial.monomial_eq]
    simp
  have hX0 : homogenize2To3 2 ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2) =
      (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 := by
    rw [show ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2) =
        MvPolynomial.monomial (Finsupp.single (0 : Fin 2) 2) 1 by
        rw [MvPolynomial.monomial_eq]
        simp]
    rw [homogenize2To3_monomial]
    rw [show homExp2To3 2 (Finsupp.single (0 : Fin 2) 2) =
        Finsupp.single (0 : Fin 3) 2 by
      ext i
      fin_cases i <;> simp [homExp2To3]]
    rw [MvPolynomial.monomial_eq]
    simp
  have hX1 : homogenize2To3 2 ((X 1 : MvPolynomial (Fin 2) ℝ) ^ 2) =
      (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 := by
    rw [show ((X 1 : MvPolynomial (Fin 2) ℝ) ^ 2) =
        MvPolynomial.monomial (Finsupp.single (1 : Fin 2) 2) 1 by
        rw [MvPolynomial.monomial_eq]
        simp]
    rw [homogenize2To3_monomial]
    rw [show homExp2To3 2 (Finsupp.single (1 : Fin 2) 2) =
        Finsupp.single (1 : Fin 3) 2 by
      ext i
      fin_cases i <;> simp [homExp2To3]]
    rw [MvPolynomial.monomial_eq]
    simp
  unfold BallGenerator HomBallGenerator
  rw [homogenize2To3_sub, homogenize2To3_sub, hC, hX0, hX1]

/-- Bounded homogenization is multiplicative when both factors satisfy their degree bounds. -/
theorem homogenize2To3_mul_of_totalDegree_le {d e : ℕ}
    {p q : MvPolynomial (Fin 2) ℝ} (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ e) :
    homogenize2To3 (d + e) (p * q) = homogenize2To3 d p * homogenize2To3 e q := by
  classical
  have hprod : p * q =
      ∑ a ∈ p.support, ∑ b ∈ q.support,
        MvPolynomial.monomial a (MvPolynomial.coeff a p) *
          MvPolynomial.monomial b (MvPolynomial.coeff b q) := by
    conv_lhs => rw [MvPolynomial.as_sum p, MvPolynomial.as_sum q]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
  calc
    homogenize2To3 (d + e) (p * q)
        = ∑ a ∈ p.support, ∑ b ∈ q.support,
            homogenize2To3 (d + e)
              (MvPolynomial.monomial a (MvPolynomial.coeff a p) *
                MvPolynomial.monomial b (MvPolynomial.coeff b q)) := by
            rw [hprod]
            rw [homogenize2To3_finset_sum]
            apply Finset.sum_congr rfl
            intro a _
            rw [homogenize2To3_finset_sum]
    _ = ∑ a ∈ p.support, ∑ b ∈ q.support,
            homogenize2To3 d (MvPolynomial.monomial a (MvPolynomial.coeff a p)) *
              homogenize2To3 e (MvPolynomial.monomial b (MvPolynomial.coeff b q)) := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            exact homogenize2To3_monomial_mul (support_degree_le_of_totalDegree_le hp ha)
              (support_degree_le_of_totalDegree_le hq hb)
    _ = homogenize2To3 d p * homogenize2To3 e q := by
            rw [homogenize2To3_as_sum_support, homogenize2To3_as_sum_support]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            rw [homogenize2To3_monomial, homogenize2To3_monomial]

/-- Exact-degree homogenization of a mixed `x^a y^b` monomial. -/
theorem homogenize2To3_X0_pow_mul_X1_pow_self (a b : ℕ) :
    homogenize2To3 (a + b)
        ((X 0 : MvPolynomial (Fin 2) ℝ) ^ a * (X 1 : MvPolynomial (Fin 2) ℝ) ^ b) =
      (X 0 : MvPolynomial (Fin 3) ℝ) ^ a * (X 1 : MvPolynomial (Fin 3) ℝ) ^ b := by
  calc
    homogenize2To3 (a + b)
        ((X 0 : MvPolynomial (Fin 2) ℝ) ^ a * (X 1 : MvPolynomial (Fin 2) ℝ) ^ b)
        = homogenize2To3 a ((X 0 : MvPolynomial (Fin 2) ℝ) ^ a) *
            homogenize2To3 b ((X 1 : MvPolynomial (Fin 2) ℝ) ^ b) := by
          exact homogenize2To3_mul_of_totalDegree_le (d := a) (e := b)
            (p := (X 0 : MvPolynomial (Fin 2) ℝ) ^ a)
            (q := (X 1 : MvPolynomial (Fin 2) ℝ) ^ b)
            (by simp [MvPolynomial.totalDegree_X_pow])
            (by simp [MvPolynomial.totalDegree_X_pow])
    _ = (X 0 : MvPolynomial (Fin 3) ℝ) ^ a * (X 1 : MvPolynomial (Fin 3) ℝ) ^ b := by
          rw [homogenize2To3_X0_pow_self, homogenize2To3_X1_pow_self]

/-- Homogenizing a pure `x`-power to a larger degree adds the required power of `z`. -/
theorem homogenize2To3_X0_pow_of_le {d n : ℕ} (h : n ≤ d) :
    homogenize2To3 d ((X 0 : MvPolynomial (Fin 2) ℝ) ^ n) =
      (X 0 : MvPolynomial (Fin 3) ℝ) ^ n * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (d - n) := by
  have hadd : n + (d - n) = d := Nat.add_sub_of_le h
  calc
    homogenize2To3 d ((X 0 : MvPolynomial (Fin 2) ℝ) ^ n)
        = homogenize2To3 (n + (d - n))
            (((X 0 : MvPolynomial (Fin 2) ℝ) ^ n) *
              (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ)) := by
          rw [hadd]
          simp
    _ = homogenize2To3 n ((X 0 : MvPolynomial (Fin 2) ℝ) ^ n) *
          homogenize2To3 (d - n) (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ) := by
          exact homogenize2To3_mul_of_totalDegree_le (d := n) (e := d - n)
            (p := (X 0 : MvPolynomial (Fin 2) ℝ) ^ n)
            (q := (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ))
            (by simp [MvPolynomial.totalDegree_X_pow])
            (by simp)
    _ = (X 0 : MvPolynomial (Fin 3) ℝ) ^ n * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (d - n) := by
          rw [homogenize2To3_X0_pow_self, homogenize2To3_C]
          simp

/-- Homogenizing a pure `y`-power to a larger degree adds the required power of `z`. -/
theorem homogenize2To3_X1_pow_of_le {d n : ℕ} (h : n ≤ d) :
    homogenize2To3 d ((X 1 : MvPolynomial (Fin 2) ℝ) ^ n) =
      (X 1 : MvPolynomial (Fin 3) ℝ) ^ n * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (d - n) := by
  have hadd : n + (d - n) = d := Nat.add_sub_of_le h
  calc
    homogenize2To3 d ((X 1 : MvPolynomial (Fin 2) ℝ) ^ n)
        = homogenize2To3 (n + (d - n))
            (((X 1 : MvPolynomial (Fin 2) ℝ) ^ n) *
              (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ)) := by
          rw [hadd]
          simp
    _ = homogenize2To3 n ((X 1 : MvPolynomial (Fin 2) ℝ) ^ n) *
          homogenize2To3 (d - n) (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ) := by
          exact homogenize2To3_mul_of_totalDegree_le (d := n) (e := d - n)
            (p := (X 1 : MvPolynomial (Fin 2) ℝ) ^ n)
            (q := (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ))
            (by simp [MvPolynomial.totalDegree_X_pow])
            (by simp)
    _ = (X 1 : MvPolynomial (Fin 3) ℝ) ^ n * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (d - n) := by
          rw [homogenize2To3_X1_pow_self, homogenize2To3_C]
          simp

/-- Homogenizing a mixed monomial to a larger degree adds the required power of `z`. -/
theorem homogenize2To3_X0_pow_mul_X1_pow_of_le {d a b : ℕ} (h : a + b ≤ d) :
    homogenize2To3 d
        ((X 0 : MvPolynomial (Fin 2) ℝ) ^ a * (X 1 : MvPolynomial (Fin 2) ℝ) ^ b) =
      (X 0 : MvPolynomial (Fin 3) ℝ) ^ a * (X 1 : MvPolynomial (Fin 3) ℝ) ^ b *
        (X 2 : MvPolynomial (Fin 3) ℝ) ^ (d - (a + b)) := by
  have hadd : a + b + (d - (a + b)) = d := Nat.add_sub_of_le h
  calc
    homogenize2To3 d
        ((X 0 : MvPolynomial (Fin 2) ℝ) ^ a * (X 1 : MvPolynomial (Fin 2) ℝ) ^ b)
        = homogenize2To3 (a + b + (d - (a + b)))
            (((X 0 : MvPolynomial (Fin 2) ℝ) ^ a * (X 1 : MvPolynomial (Fin 2) ℝ) ^ b) *
              (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ)) := by
          rw [hadd]
          simp
    _ = homogenize2To3 (a + b)
            ((X 0 : MvPolynomial (Fin 2) ℝ) ^ a * (X 1 : MvPolynomial (Fin 2) ℝ) ^ b) *
          homogenize2To3 (d - (a + b)) (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ) := by
          exact homogenize2To3_mul_of_totalDegree_le (d := a + b) (e := d - (a + b))
            (p := (X 0 : MvPolynomial (Fin 2) ℝ) ^ a * (X 1 : MvPolynomial (Fin 2) ℝ) ^ b)
            (q := (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ))
            (by
              calc (((X 0 : MvPolynomial (Fin 2) ℝ) ^ a * X 1 ^ b).totalDegree)
                  ≤ ((X 0 : MvPolynomial (Fin 2) ℝ) ^ a).totalDegree +
                      ((X 1 : MvPolynomial (Fin 2) ℝ) ^ b).totalDegree :=
                    MvPolynomial.totalDegree_mul _ _
                _ ≤ a + b := by simp [MvPolynomial.totalDegree_X_pow])
            (by simp)
    _ = (X 0 : MvPolynomial (Fin 3) ℝ) ^ a * (X 1 : MvPolynomial (Fin 3) ℝ) ^ b *
          (X 2 : MvPolynomial (Fin 3) ℝ) ^ (d - (a + b)) := by
          rw [homogenize2To3_X0_pow_mul_X1_pow_self, homogenize2To3_C]
          simp [mul_assoc]

/-- Total-degree bound for the standard mixed monomials in two variables. -/
theorem totalDegree_X0_pow_mul_X1_pow_le (a b : ℕ) :
    (((X 0 : MvPolynomial (Fin 2) ℝ) ^ a * (X 1 : MvPolynomial (Fin 2) ℝ) ^ b).totalDegree
      ≤ a + b) := by
  calc (((X 0 : MvPolynomial (Fin 2) ℝ) ^ a * (X 1 : MvPolynomial (Fin 2) ℝ) ^ b).totalDegree)
      ≤ ((X 0 : MvPolynomial (Fin 2) ℝ) ^ a).totalDegree +
          ((X 1 : MvPolynomial (Fin 2) ℝ) ^ b).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ a + b := by simp [MvPolynomial.totalDegree_X_pow]

/-- Homogenization commutes with multiplication by a scalar constant. -/
theorem homogenize2To3_C_mul_of_totalDegree_le {d : ℕ} {c : ℝ}
    {p : MvPolynomial (Fin 2) ℝ} (hp : p.totalDegree ≤ d) :
    homogenize2To3 d (MvPolynomial.C c * p) =
      MvPolynomial.C c * homogenize2To3 d p := by
  have hC : (MvPolynomial.C c : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 0 := by
    simp
  simpa [homogenize2To3_C, mul_assoc] using
    homogenize2To3_mul_of_totalDegree_le (d := 0) (e := d)
      (p := (MvPolynomial.C c : MvPolynomial (Fin 2) ℝ)) (q := p) hC hp

/-- Dehomogenizing a homogenized monomial recovers the original monomial. -/
theorem dehomogenize3To2_homogenize2To3_monomial
    (d : ℕ) (e : Fin 2 →₀ ℕ) (c : ℝ) :
    dehomogenize3To2
        (homogenize2To3 d (MvPolynomial.monomial e c : MvPolynomial (Fin 2) ℝ)) =
      (MvPolynomial.monomial e c : MvPolynomial (Fin 2) ℝ) := by
  classical
  rw [homogenize2To3_monomial]
  change (MvPolynomial.aeval ![(X 0 : MvPolynomial (Fin 2) ℝ), X 1, 1] :
      MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ)
        (MvPolynomial.monomial (homExp2To3 d e) c) =
      (MvPolynomial.monomial e c : MvPolynomial (Fin 2) ℝ)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.monomial_eq]
  congr 1
  have he : e = Finsupp.single (0 : Fin 2) (e 0) + Finsupp.single (1 : Fin 2) (e 1) := by
    ext i
    fin_cases i <;> simp
  rw [he]
  simp only [homExp2To3, Fin.isValue, Finsupp.prod_pow, Finsupp.coe_add, Pi.add_apply,
    Fin.prod_univ_two,
    Finsupp.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true,
    Finsupp.single_eq_of_ne, add_zero, one_ne_zero, zero_add]
  rw [Fin.prod_univ_three]
  simp

/-- Dehomogenizing a homogenized polynomial recovers the original polynomial. -/
theorem dehomogenize3To2_homogenize2To3 (d : ℕ) (p : MvPolynomial (Fin 2) ℝ) :
    dehomogenize3To2 (homogenize2To3 d p) = p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
      exact dehomogenize3To2_homogenize2To3_monomial d e c
  | add p q hp hq =>
      rw [homogenize2To3_add, map_add, hp, hq]

/-- Homogenization of a degree-bounded SOS polynomial is an SOS polynomial, assuming each
square root is homogenized to a common degree. The multiplicativity identity for bounded
homogenization is kept separate because it is the substantial algebraic step. -/
theorem HasDegreeBoundedSOS.homogenize_isSOS_of_square_identity
    {σ : MvPolynomial (Fin 2) ℝ} {r d : ℕ} (hσ : HasDegreeBoundedSOS σ r)
    (hident : homogenize2To3 d σ =
      ∑ i : Fin hσ.choose, homogenize2To3 (d / 2) (hσ.choose_spec.choose i) ^ 2) :
    IsSOS (homogenize2To3 d σ) := by
  refine ⟨hσ.choose, fun i => homogenize2To3 (d / 2) (hσ.choose_spec.choose i), ?_⟩
  exact hident

/-- Homogenizing a degree-bounded SOS polynomial to twice the root-degree bound is SOS. -/
theorem HasDegreeBoundedSOS.homogenize_isSOS
    {σ : MvPolynomial (Fin 2) ℝ} {r : ℕ} (hσ : HasDegreeBoundedSOS σ r) :
    IsSOS (homogenize2To3 (2 * r) σ) := by
  obtain ⟨N, Q, hQ, hdeg⟩ := hσ
  refine ⟨N, fun i => homogenize2To3 r (Q i), ?_⟩
  rw [hQ, homogenize2To3_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa [pow_two, two_mul] using
    homogenize2To3_mul_of_totalDegree_le (d := r) (e := r) (p := Q i) (q := Q i)
      (hdeg i) (hdeg i)

/-- Degree bound for a bounded SOS polynomial. -/
theorem HasDegreeBoundedSOS.totalDegree_le {σ : MvPolynomial (Fin 2) ℝ} {r : ℕ}
    (hσ : HasDegreeBoundedSOS σ r) : σ.totalDegree ≤ 2 * r := by
  obtain ⟨N, Q, hQ, hdeg⟩ := hσ
  rw [hQ]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _hi
  calc ((Q i) ^ 2).totalDegree
      ≤ 2 * (Q i).totalDegree := MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 * r := Nat.mul_le_mul_left 2 (hdeg i)

/-- The Robinson cubic is homogeneous of degree three in its three arguments. -/
theorem Phi_mul_left {A : Type*} [CommRing A] (c a b d : A) :
    Phi (c * a) (c * b) (c * d) = c ^ 3 * Phi a b d := by
  unfold Phi
  ring

/-- The squared-radius form is homogeneous of degree two. -/
theorem sphereSq_isHomogeneous : sphereSq.IsHomogeneous 2 := by
  unfold sphereSq
  exact ((MvPolynomial.isHomogeneous_X_pow (0 : Fin 3) 2).add
    (MvPolynomial.isHomogeneous_X_pow (1 : Fin 3) 2)).add
    (MvPolynomial.isHomogeneous_X_pow (2 : Fin 3) 2)

/-- The homogeneous ball generator is homogeneous of degree two. -/
theorem HomBallGenerator_isHomogeneous (lambda : ℝ) :
    (HomBallGenerator lambda).IsHomogeneous 2 := by
  unfold HomBallGenerator
  exact (((MvPolynomial.isHomogeneous_X_pow (2 : Fin 3) 2).C_mul lambda).sub
    (MvPolynomial.isHomogeneous_X_pow (0 : Fin 3) 2)).sub
    (MvPolynomial.isHomogeneous_X_pow (1 : Fin 3) 2)

/-- The squared-radius form is invariant under `z ↦ -z`. -/
theorem zReflect3_sphereSq : zReflect3 sphereSq = sphereSq := by
  unfold sphereSq
  simp [zReflect3]

/-- The homogeneous Robinson form is invariant under `z ↦ -z`. -/
theorem zReflect3_homRobinson : zReflect3 homRobinson = homRobinson := by
  unfold homRobinson Phi
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, zReflect3_X_zero,
    zReflect3_X_one, zReflect3_X_two]
  ring_nf

/-- Multiplying the homogeneous Robinson form by an even power of `z` preserves
invariance under `z ↦ -z`. -/
theorem zReflect3_homRobinson_mul_even_z_pow (m : ℕ) :
    zReflect3 (homRobinson * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m)) =
      homRobinson * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) := by
  simp only [map_mul, map_pow, zReflect3_homRobinson, zReflect3_X_two]
  rw [show (-X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) =
      (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) by
    calc
      (-X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m)
          = ((-X 2 : MvPolynomial (Fin 3) ℝ) ^ 2) ^ m := by rw [pow_mul]
      _ = ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2) ^ m := by simp
      _ = (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) := by rw [pow_mul]]

/-- Source polynomial in variables `(x,y,t)` whose square-substitution `t = w^2` is
`w^(2*m) * Phi(x^2,y^2,w^2)`. -/
def homRobinsonSource (m : ℕ) : MvPolynomial (Fin 3) ℝ :=
  (X 2 : MvPolynomial (Fin 3) ℝ) ^ m *
    Phi ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2) ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 2)
      (X 2 : MvPolynomial (Fin 3) ℝ)

/-- The source preimage of `P_{m,lambda}` under the square-substitution `z ↦ z^2`. -/
def PmlambdaEvenSource (m : ℕ) (lambda : ℝ) : MvPolynomial (Fin 3) ℝ :=
  ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 + X 2) ^ m *
    Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
      (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2)
      ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 + X 2)

/-- Substitute the source variable `t = z^2` by the homogeneous ball generator
`lambda*w^2 - x^2 - y^2`. -/
def homBallSourceSubst (lambda : ℝ) :
    MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval
    ![(X 0 : MvPolynomial (Fin 3) ℝ), X 1, HomBallGenerator lambda]

/-- Weighted source degree for polynomials in `(x,y,t)`, where `x,y` have weight one
and the source variable `t` has weight two. -/
def sourceWeightedDegree3 (p : MvPolynomial (Fin 3) ℝ) : ℕ :=
  p.support.sup fun d => ∑ i ∈ d.support, d i * (![1, 1, 2] i)

/-- Square-substitution cannot lower the weighted source degree: its support is an
injective image and each monomial's weighted source degree becomes ordinary degree. -/
theorem sourceWeightedDegree3_le_zSquareSubst3_totalDegree
    (p : MvPolynomial (Fin 3) ℝ) :
    sourceWeightedDegree3 p ≤ (zSquareSubst3 p).totalDegree := by
  classical
  unfold sourceWeightedDegree3 MvPolynomial.totalDegree
  apply Finset.sup_le
  intro d hd
  rw [sourceWeight3_eq_zSquareExp3_sum d]
  have hdimg : zSquareExp3AddMonoidHom d ∈ (zSquareSubst3 p).support := by
    rw [zSquareSubst3_support]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  exact Finset.le_sup (s := (zSquareSubst3 p).support)
    (f := fun d => d.sum fun _ e => e) hdimg

/-- The source weighted degree plus the explicit odd `z` factor is the ordinary degree
of the corresponding monomial in `X 2 * zSquareSubst3 p`. -/
theorem sourceWeight3_add_one_eq_X_two_mul_zSquareExp3_sum (d : Fin 3 →₀ ℕ) :
    (∑ i ∈ d.support, d i * (![1, 1, 2] i)) + 1 =
      (Finsupp.single (2 : Fin 3) 1 + zSquareExp3AddMonoidHom d).sum (fun _ e => e) := by
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
  rw [Finset.sum_subset (s₁ := d.support) (s₂ := Finset.univ)]
  · rw [Fin.sum_univ_three]
    conv_rhs => rw [Fin.sum_univ_three]
    simp [zSquareExp3AddMonoidHom]
    omega
  · intro i _
    exact Finset.mem_univ i
  · intro i _ hi
    have hzero : d i = 0 := by simpa [Finsupp.mem_support_iff] using hi
    rw [hzero]
    simp

/-- If `X 2 * zSquareSubst3 p` has degree at most `r + 1`, then the source preimage
has weighted degree at most `r`. This is the degree drop for the odd reflected roots. -/
theorem sourceWeightedDegree3_le_of_X_two_mul_zSquareSubst3_totalDegree_le
    {p : MvPolynomial (Fin 3) ℝ} {r : ℕ}
    (hdeg : ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 p).totalDegree ≤ r + 1) :
    sourceWeightedDegree3 p ≤ r := by
  classical
  unfold sourceWeightedDegree3 MvPolynomial.totalDegree at *
  apply Finset.sup_le
  intro d hd
  have hdimg0 : zSquareExp3AddMonoidHom d ∈ (zSquareSubst3 p).support := by
    rw [zSquareSubst3_support]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hdimg : Finsupp.single (2 : Fin 3) 1 + zSquareExp3AddMonoidHom d ∈
      ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 p).support := by
    rw [MvPolynomial.support_X_mul]
    exact Finset.mem_map.mpr ⟨zSquareExp3AddMonoidHom d, hdimg0, rfl⟩
  have hle := Finset.le_sup
    (s := ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 p).support)
    (f := fun d => d.sum fun _ e => e) hdimg
  have hle' : (∑ i ∈ d.support, d i * (![1, 1, 2] i)) + 1 ≤
      ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 p).support.sup
        (fun d => d.sum fun _ e => e) := by
    simpa [sourceWeight3_add_one_eq_X_two_mul_zSquareExp3_sum d] using hle
  omega

/-- The ball-source substitution is controlled by the weighted source degree. -/
theorem homBallSourceSubst_totalDegree_le_weighted
    (lambda : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    (homBallSourceSubst lambda p).totalDegree ≤ sourceWeightedDegree3 p := by
  classical
  unfold homBallSourceSubst
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.aeval_monomial]
  calc
    (algebraMap ℝ (MvPolynomial (Fin 3) ℝ) (MvPolynomial.coeff d p) *
        d.prod (fun i k => (![X 0, X 1, HomBallGenerator lambda] i) ^ k)).totalDegree
        ≤ (algebraMap ℝ (MvPolynomial (Fin 3) ℝ) (MvPolynomial.coeff d p)).totalDegree +
            (d.prod (fun i k => (![X 0, X 1, HomBallGenerator lambda] i) ^ k)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ =
        (d.prod (fun i k => (![X 0, X 1, HomBallGenerator lambda] i) ^ k)).totalDegree := by
          rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C]
          simp
    _ ≤ ∑ i ∈ d.support,
          ((![X 0, X 1, HomBallGenerator lambda] i : MvPolynomial (Fin 3) ℝ) ^
                d i).totalDegree := by
          simp only [Finsupp.prod]
          exact MvPolynomial.totalDegree_finset_prod d.support _
    _ ≤ ∑ i ∈ d.support, d i * (![1, 1, 2] i) := by
          apply Finset.sum_le_sum
          intro i _
          calc
            ((![X 0, X 1, HomBallGenerator lambda] i : MvPolynomial (Fin 3) ℝ) ^
                d i).totalDegree
                ≤ d i *
                  (![X 0, X 1, HomBallGenerator lambda] i : MvPolynomial (Fin 3) ℝ).totalDegree :=
              MvPolynomial.totalDegree_pow _ _
            _ ≤ d i * (![1, 1, 2] i) := by
              apply Nat.mul_le_mul_left
              fin_cases i
              · simp [MvPolynomial.totalDegree_X]
              · simp [MvPolynomial.totalDegree_X]
              · exact (HomBallGenerator_isHomogeneous lambda).totalDegree_le
    _ ≤ sourceWeightedDegree3 p := by
          unfold sourceWeightedDegree3
          exact Finset.le_sup
            (s := p.support) (f := fun d => ∑ i ∈ d.support, d i * (![1, 1, 2] i)) hd

/-- The ball-source substitution has quadratic coordinate images, hence at most doubles
source total degree. -/
theorem homBallSourceSubst_totalDegree_le (lambda : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    (homBallSourceSubst lambda p).totalDegree ≤ 2 * p.totalDegree := by
  unfold homBallSourceSubst
  apply totalDegree_aeval_le_of_quadratic
  intro i
  fin_cases i
  · simp [MvPolynomial.totalDegree_X]
  · simp [MvPolynomial.totalDegree_X]
  · exact (HomBallGenerator_isHomogeneous lambda).totalDegree_le

/-- Source form of the homogeneous ball generator in variables `(x,y,t)` with `t = w^2`. -/
def homBallGeneratorSource (lambda : ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) -
    (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 - (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2

/-- Polynomial substitution from the source variable `t` to the target sphere-square form,
with `x,y` scaled by `sqrt(lambda)`. -/
def pmlambdaSourceSubst (lambda : ℝ) :
    MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval
    ![MvPolynomial.C (Real.sqrt lambda) * (X 0 : MvPolynomial (Fin 3) ℝ),
      MvPolynomial.C (Real.sqrt lambda) * (X 1 : MvPolynomial (Fin 3) ℝ), sphereSq]

/-- Square-substitution sends the source preimage of `P_{m,lambda}` to `P_{m,lambda}`. -/
theorem zSquareSubst3_PmlambdaEvenSource (m : ℕ) (lambda : ℝ) :
    zSquareSubst3 (PmlambdaEvenSource m lambda) = Pmlambda m lambda := by
  have hS : zSquareSubst3
      ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 + X 2) =
      sphereSq := by
    simp [zSquareSubst3, sphereSq]
  have hPhi : zSquareSubst3
      (Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
        (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2)
        ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 + X 2)) =
      Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
        (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) sphereSq := by
    unfold Phi
    simp [zSquareSubst3, sphereSq]
    ring_nf
    left
    left
    change zSquareSubst3 (3 : MvPolynomial (Fin 3) ℝ) = 3
    simpa using map_ofNat zSquareSubst3 3
  unfold PmlambdaEvenSource Pmlambda
  rw [map_mul, map_pow, hS, hPhi]

/-- Substituting `t = lambda*w^2 - x^2 - y^2` into the source preimage of `P` gives
the scaled homogeneous Robinson form. -/
theorem homBallSourceSubst_PmlambdaEvenSource (m : ℕ) (lambda : ℝ) :
    homBallSourceSubst lambda (PmlambdaEvenSource m lambda) =
      MvPolynomial.C (lambda ^ (m + 3)) *
        ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) := by
  have hS : homBallSourceSubst lambda
      ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 + X 2) =
      MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 := by
    simp [homBallSourceSubst, HomBallGenerator]
  have hPhi : homBallSourceSubst lambda
      (Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
        (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2)
        ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 + X 2)) =
      Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
        (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2)
        (MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2) := by
    unfold Phi
    simp [homBallSourceSubst, HomBallGenerator]
    ring_nf
    left
    simpa using map_ofNat
      (MvPolynomial.bind₁
        ![(X 0 : MvPolynomial (Fin 3) ℝ), X 1,
          MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 +
            (-(X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 - (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2)] :
        MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ) 3
  unfold PmlambdaEvenSource homRobinson
  rw [map_mul, map_pow, hS, hPhi, Phi_mul_left]
  rw [mul_pow, ← MvPolynomial.C_pow]
  rw [show ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2) ^ m =
      (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) by rw [pow_mul]]
  rw [show lambda ^ (m + 3) = lambda ^ m * lambda ^ 3 by rw [pow_add]]
  rw [← MvPolynomial.C_pow]
  rw [show MvPolynomial.C (lambda ^ m) * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) *
        (MvPolynomial.C (lambda ^ 3) * Phi ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
          ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2)) =
      (MvPolynomial.C (lambda ^ m) * MvPolynomial.C (lambda ^ 3)) *
        ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) *
          Phi ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2)
            ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2)) by ring]
  rw [← MvPolynomial.C_mul]

/-- Square-substitution sends the source Robinson form to the homogeneous Robinson form
with the extra even power of the homogenizing variable. -/
theorem zSquareSubst3_homRobinsonSource (m : ℕ) :
    zSquareSubst3 (homRobinsonSource m) =
      (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson := by
  simp [zSquareSubst3, homRobinsonSource, homRobinson, Phi, pow_mul]
  ring_nf
  change zSquareSubst3 (3 : MvPolynomial (Fin 3) ℝ) = 3
  simpa using map_ofNat zSquareSubst3 3

/-- Square-substitution sends the source ball generator to the homogeneous ball generator. -/
theorem zSquareSubst3_homBallGeneratorSource (lambda : ℝ) :
    zSquareSubst3 (homBallGeneratorSource lambda) = HomBallGenerator lambda := by
  simp [zSquareSubst3, homBallGeneratorSource, HomBallGenerator]

/-- The source substitution sends the source Robinson form to `P_{m,lambda}`. -/
theorem pmlambdaSourceSubst_homRobinsonSource {lambda : ℝ} (hLam : 0 ≤ lambda)
    (m : ℕ) :
    pmlambdaSourceSubst lambda (homRobinsonSource m) = Pmlambda m lambda := by
  have hsqrt_sq :
      (MvPolynomial.C (Real.sqrt lambda) : MvPolynomial (Fin 3) ℝ) ^ 2 =
        MvPolynomial.C lambda := by
    rw [← MvPolynomial.C_pow, Real.sq_sqrt hLam]
  simp [pmlambdaSourceSubst, homRobinsonSource, Pmlambda, Phi, sphereSq, mul_pow, hsqrt_sq]
  ring_nf
  left
  left
  left
  change pmlambdaSourceSubst lambda (3 : MvPolynomial (Fin 3) ℝ) = 3
  simpa using map_ofNat (pmlambdaSourceSubst lambda) 3

/-- The source substitution sends the source ball generator to `lambda * z^2`. -/
theorem pmlambdaSourceSubst_homBallGeneratorSource {lambda : ℝ} (hLam : 0 ≤ lambda) :
    pmlambdaSourceSubst lambda (homBallGeneratorSource lambda) =
      MvPolynomial.C lambda * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 := by
  have hsqrt_sq :
      (MvPolynomial.C (Real.sqrt lambda) : MvPolynomial (Fin 3) ℝ) ^ 2 =
        MvPolynomial.C lambda := by
    rw [← MvPolynomial.C_pow, Real.sq_sqrt hLam]
  simp [pmlambdaSourceSubst, homBallGeneratorSource, sphereSq, mul_pow, hsqrt_sq]
  ring_nf

/-- An invariant ternary SOS descends through `z ↦ z^2` to a source polynomial whose
`P_{m,lambda}` substitution is again SOS. -/
theorem IsSOS.exists_source_of_zSquareSubst3_invariant
    {lambda : ℝ} {τ : MvPolynomial (Fin 3) ℝ}
    (hτ : IsSOS τ) (hinv : zReflect3 τ = τ) :
    ∃ σ : MvPolynomial (Fin 3) ℝ,
      zSquareSubst3 σ = τ ∧ IsSOS (pmlambdaSourceSubst lambda σ) := by
  obtain ⟨N, A, B, hsum⟩ := IsSOS.exists_zSquareSubst3_even_odd_witness hτ hinv
  refine ⟨(∑ i : Fin N, (A i) ^ 2) +
      (X 2 : MvPolynomial (Fin 3) ℝ) * ∑ i : Fin N, (B i) ^ 2, ?_, ?_⟩
  · rw [hsum]
    simp only [map_add, map_mul, map_sum, map_pow, zSquareSubst3_X_two]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · have hA : IsSOS (∑ i : Fin N, (pmlambdaSourceSubst lambda (A i)) ^ 2) := by
      exact IsSOS.finset_sum (Finset.univ : Finset (Fin N))
        (fun i => (pmlambdaSourceSubst lambda (A i)) ^ 2)
        (fun i _ => IsSOS_sq (pmlambdaSourceSubst lambda (A i)))
    have hB : IsSOS (sphereSq *
        ∑ i : Fin N, (pmlambdaSourceSubst lambda (B i)) ^ 2) :=
      IsSOS.sphereSq_mul_sum_squares fun i => pmlambdaSourceSubst lambda (B i)
    simpa [pmlambdaSourceSubst, map_add, map_mul, map_sum, map_pow] using IsSOS.add hA hB

/-- The homogeneous ball generator is invariant under `z ↦ -z`. -/
theorem zReflect3_HomBallGenerator (lambda : ℝ) :
    zReflect3 (HomBallGenerator lambda) = HomBallGenerator lambda := by
  unfold HomBallGenerator
  simp [zReflect3]

/-- The threshold form `P_{m,lambda}` is invariant under `z ↦ -z`. -/
theorem zReflect3_Pmlambda (m : ℕ) (lambda : ℝ) :
    zReflect3 (Pmlambda m lambda) = Pmlambda m lambda := by
  unfold Pmlambda Phi sphereSq
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, zReflect3_C, zReflect3_X_zero,
    zReflect3_X_one, zReflect3_X_two]
  ring_nf

/-- Any SOS witness for `P_{m,lambda}` may be replaced by one whose square roots are
separated into parts even and odd in the homogenizing variable. -/
theorem IsSOS.exists_Pmlambda_z_reflection_even_odd_witness {m : ℕ} {lambda : ℝ}
    (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ A B : Fin N → MvPolynomial (Fin 3) ℝ,
      Pmlambda m lambda = (∑ i : Fin N, (A i) ^ 2) + ∑ i : Fin N, (B i) ^ 2 ∧
      (∀ i : Fin N, zReflect3 (A i) = A i) ∧
      (∀ i : Fin N, zReflect3 (B i) = -B i) :=
  IsSOS.exists_z_reflection_even_odd_witness hSOS (zReflect3_Pmlambda m lambda)

/-- Any SOS witness for `P_{m,lambda}` may be symmetrized under `z ↦ -z` while keeping
the expected root-degree bound `m + 3`. -/
theorem IsSOS.exists_Pmlambda_z_reflection_even_odd_witness_degree_bound
    {m : ℕ} {lambda : ℝ} (hSOS : IsSOS (Pmlambda m lambda)) :
    ∃ N : ℕ, ∃ A B : Fin N → MvPolynomial (Fin 3) ℝ,
      Pmlambda m lambda = (∑ i : Fin N, (A i) ^ 2) + ∑ i : Fin N, (B i) ^ 2 ∧
      (∀ i : Fin N, zReflect3 (A i) = A i) ∧
      (∀ i : Fin N, zReflect3 (B i) = -B i) ∧
      (∀ i : Fin N, (A i).totalDegree ≤ m + 3) ∧
      (∀ i : Fin N, (B i).totalDegree ≤ m + 3) :=
  IsSOS.exists_z_reflection_even_odd_witness_degree_bound hSOS (zReflect3_Pmlambda m lambda)
    (Pmlambda_totalDegree_le m lambda)


/-- Dehomogenizing the homogeneous ball generator gives the affine ball generator. -/
theorem dehomogenize3To2_HomBallGenerator (lambda : ℝ) :
    dehomogenize3To2 (HomBallGenerator lambda) = BallGenerator lambda := by
  simp [dehomogenize3To2, HomBallGenerator, BallGenerator]

/-- Homogenizing the dehomogenized Robinson polynomial to degree six recovers the
homogeneous Robinson form. -/
theorem homogenize2To3_robinson :
    homogenize2To3 6 robinson = homRobinson := by
  have h1 :
      homogenize2To3 6 (1 : MvPolynomial (Fin 2) ℝ) =
        (X 2 : MvPolynomial (Fin 3) ℝ) ^ 6 := by
    simpa using homogenize2To3_C 6 (1 : ℝ)
  have h3C :
      homogenize2To3 6
          (MvPolynomial.C (3 : ℝ) *
            ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 * (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2)) =
        MvPolynomial.C (3 : ℝ) *
          ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 *
            (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2) := by
    rw [homogenize2To3_C_mul_of_totalDegree_le]
    · rw [homogenize2To3_X0_pow_mul_X1_pow_of_le (by norm_num : 2 + 2 ≤ 6)]
    · exact (totalDegree_X0_pow_mul_X1_pow_le 2 2).trans (by norm_num : 2 + 2 ≤ 6)
  have h3 :
      homogenize2To3 6
          ((3 : MvPolynomial (Fin 2) ℝ) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 *
            (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2) =
        MvPolynomial.C (3 : ℝ) *
          ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 *
            (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2) := by
    calc
      homogenize2To3 6
          ((3 : MvPolynomial (Fin 2) ℝ) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 *
            (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2)
          = homogenize2To3 6
              (MvPolynomial.C (3 : ℝ) *
                ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 *
                  (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2)) := by
            congr 1
            rw [show (MvPolynomial.C (3 : ℝ) : MvPolynomial (Fin 2) ℝ) = 3 from
              MvPolynomial.C_eq_coe_nat 3]
            ring_nf
      _ = MvPolynomial.C (3 : ℝ) *
          ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 *
            (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2) := h3C
  unfold robinson homRobinson Phi
  simp only [homogenize2To3_add, homogenize2To3_sub]
  rw [homogenize2To3_X0_pow_of_le (by norm_num : 6 ≤ 6)]
  rw [homogenize2To3_X1_pow_of_le (by norm_num : 6 ≤ 6)]
  rw [h1]
  rw [homogenize2To3_X0_pow_mul_X1_pow_of_le (by norm_num : 4 + 2 ≤ 6)]
  rw [homogenize2To3_X0_pow_of_le (by norm_num : 4 ≤ 6)]
  rw [homogenize2To3_X0_pow_mul_X1_pow_of_le (by norm_num : 2 + 4 ≤ 6)]
  rw [homogenize2To3_X1_pow_of_le (by norm_num : 4 ≤ 6)]
  rw [homogenize2To3_X0_pow_of_le (by norm_num : 2 ≤ 6)]
  rw [homogenize2To3_X1_pow_of_le (by norm_num : 2 ≤ 6)]
  rw [h3]
  rw [show (MvPolynomial.C (3 : ℝ) : MvPolynomial (Fin 3) ℝ) = 3 from
    MvPolynomial.C_eq_coe_nat 3]
  ring_nf

/-- Dehomogenizing the homogeneous Robinson form gives the affine Robinson polynomial. -/
theorem dehomogenize3To2_homRobinson :
    dehomogenize3To2 homRobinson = robinson := by
  have hthree :
      (MvPolynomial.aeval ![(X 0 : MvPolynomial (Fin 2) ℝ), X 1, 1] :
        MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ)
          (3 : MvPolynomial (Fin 3) ℝ) = (3 : MvPolynomial (Fin 2) ℝ) := by
    simpa using map_ofNat
      (MvPolynomial.aeval ![(X 0 : MvPolynomial (Fin 2) ℝ), X 1, 1] :
        MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) 3
  have hthree' :
      (MvPolynomial.bind₁ ![(X 0 : MvPolynomial (Fin 2) ℝ), X 1, 1])
          (3 : MvPolynomial (Fin 3) ℝ) = (3 : MvPolynomial (Fin 2) ℝ) := by
    simpa using hthree
  simp [dehomogenize3To2, homRobinson, robinson, Phi, hthree']
  ring_nf

/-- Dehomogenizing any even homogenizing-variable multiple of the homogeneous Robinson
form gives the affine Robinson polynomial. -/
theorem dehomogenize3To2_z_pow_mul_homRobinson (m : ℕ) :
    dehomogenize3To2 ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) =
      robinson := by
  rw [map_mul, dehomogenize3To2_homRobinson]
  simp [dehomogenize3To2]


/-- Dehomogenizing the squared-radius form gives `1 + x^2 + y^2`. -/
theorem dehomogenize3To2_sphereSq :
    dehomogenize3To2 sphereSq =
      1 + (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2 := by
  simp [dehomogenize3To2, sphereSq]
  ring

/-- Parity selector from the critical construction: `0` for odd `m`, `1` for even `m`. -/
def criticalEta (m : ℕ) : ℕ :=
  if m % 2 = 0 then 1 else 0

/-- Complementary parity selector from the critical construction. -/
def criticalDelta (m : ℕ) : ℕ :=
  1 - criticalEta m

/-- The parity selector is always at most one. -/
theorem criticalEta_le_one (m : ℕ) : criticalEta m ≤ 1 := by
  unfold criticalEta
  split <;> omega

/-- The complementary parity selector is always at most one. -/
theorem criticalDelta_le_one (m : ℕ) : criticalDelta m ≤ 1 := by
  unfold criticalDelta
  exact Nat.sub_le 1 (criticalEta m)

/-- The two parity selectors add to one. -/
theorem criticalEta_add_criticalDelta (m : ℕ) :
    criticalEta m + criticalDelta m = 1 := by
  have hEta := criticalEta_le_one m
  unfold criticalDelta
  omega

/-- The odd case has `eta = 0`. -/
theorem criticalEta_eq_zero_of_odd {m : ℕ} (hm : m % 2 ≠ 0) : criticalEta m = 0 := by
  simp [criticalEta, hm]

/-- The even case has `eta = 1`. -/
theorem criticalEta_eq_one_of_even {m : ℕ} (hm : m % 2 = 0) : criticalEta m = 1 := by
  simp [criticalEta, hm]

/-- The odd case has `delta = 1`. -/
theorem criticalDelta_eq_one_of_odd {m : ℕ} (hm : m % 2 ≠ 0) : criticalDelta m = 1 := by
  unfold criticalDelta
  rw [criticalEta_eq_zero_of_odd hm]

/-- The even case has `delta = 0`. -/
theorem criticalDelta_eq_zero_of_even {m : ℕ} (hm : m % 2 = 0) : criticalDelta m = 0 := by
  unfold criticalDelta
  rw [criticalEta_eq_one_of_even hm]

/-- The four-square interpolation expression used in the critical construction.
The variables are ordered as `X`, `Y`, `R = X + Y`, `p = X*Y`, and `T`. -/
def criticalInterpolationRhs {A : Type*} [CommRing A] (X Y R p T : A) (eta delta : ℕ)
    (alpha beta q h : A) : A :=
  T ^ eta * (alpha + 4 * p * q) ^ 2 +
    X * T ^ delta * (beta + 2 * Y * h) ^ 2 +
    Y * T ^ delta * (beta + 2 * X * h) ^ 2 +
    4 * p * (R ^ 2 - 4 * p) * T ^ eta * q ^ 2

/-- The interpolation expression is affine in `p`; the apparent `p^2` terms cancel. -/
theorem criticalInterpolationRhs_affine {A : Type*} [CommRing A]
    {X Y R p T : A} {eta delta : ℕ} {alpha beta q h : A}
    (hR : R = X + Y) (hp : p = X * Y) :
    criticalInterpolationRhs X Y R p T eta delta alpha beta q h =
      T ^ eta * alpha ^ 2 + R * T ^ delta * beta ^ 2 +
        p * (8 * T ^ eta * alpha * q + 8 * T ^ delta * beta * h +
          4 * R * T ^ delta * h ^ 2 + 4 * R ^ 2 * T ^ eta * q ^ 2) := by
  subst R
  subst p
  unfold criticalInterpolationRhs
  ring

/-- The interpolation expression has the prescribed axis endpoint at `p = 0`. -/
theorem criticalInterpolationRhs_axis_endpoint {A : Type*} [CommRing A]
    {X Y R T : A} {eta delta : ℕ} {alpha beta q h : A}
    (hR : R = X + Y) (hp : (0 : A) = X * Y) :
    criticalInterpolationRhs X Y R 0 T eta delta alpha beta q h =
      T ^ eta * alpha ^ 2 + R * T ^ delta * beta ^ 2 := by
  rw [criticalInterpolationRhs_affine hR hp]
  ring

/-- The affine interpolation expression has the prescribed diagonal endpoint. -/
theorem criticalInterpolationRhs_diagonal_endpoint
    {X Y R T alpha beta q h : ℝ} {eta delta : ℕ}
    (hR : R = X + Y) (hp : R ^ 2 / 4 = X * Y) :
    criticalInterpolationRhs X Y R (R ^ 2 / 4) T eta delta alpha beta q h =
      T ^ eta * (alpha + R ^ 2 * q) ^ 2 +
        R * T ^ delta * (beta + R * h) ^ 2 := by
  rw [criticalInterpolationRhs_affine hR hp]
  ring

/-- Substitution variables for the critical four-square construction. -/
def criticalX : MvPolynomial (Fin 3) ℝ :=
  (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2

/-- Substitution variables for the critical four-square construction. -/
def criticalY : MvPolynomial (Fin 3) ℝ :=
  (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2

/-- The symmetric sum `R = x^2 + y^2` in the critical construction. -/
def criticalR : MvPolynomial (Fin 3) ℝ :=
  criticalX + criticalY

/-- The product variable `p = x^2 y^2` in the critical construction. -/
def criticalP : MvPolynomial (Fin 3) ℝ :=
  criticalX * criticalY

/-- The square `T = z^2` in the critical construction. -/
def criticalT : MvPolynomial (Fin 3) ℝ :=
  (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2

/-- The squared-radius form is `R + T` in the critical-construction variables. -/
theorem sphereSq_eq_criticalR_add_criticalT : sphereSq = criticalR + criticalT := by
  unfold sphereSq criticalR criticalT criticalX criticalY
  ring

/-- The threshold form written in the critical-construction variables. -/
theorem Pmlambda_eq_critical_variables (m : ℕ) (lambda : ℝ) :
    Pmlambda m lambda =
      (criticalR + criticalT) ^ m *
        Phi (MvPolynomial.C lambda * criticalX) (MvPolynomial.C lambda * criticalY)
          (criticalR + criticalT) := by
  rw [Pmlambda, sphereSq_eq_criticalR_add_criticalT]
  unfold criticalX criticalY
  rfl

/-- The discriminant term becomes the square `(x^2-y^2)^2` after substitution. -/
theorem criticalP_mul_discriminant :
    criticalP * (criticalR ^ 2 - 4 * criticalP) =
      (X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 * (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 *
        ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 - (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) ^ 2 := by
  unfold criticalP criticalR criticalX criticalY
  ring

/-- Powers of `z^2` are squares of powers of `z`. -/
theorem criticalT_pow_eq_sq (n : ℕ) :
    criticalT ^ n = ((X 2 : MvPolynomial (Fin 3) ℝ) ^ n) ^ 2 := by
  unfold criticalT
  rw [← pow_mul, ← pow_mul]
  congr 1
  omega

/-- The interpolation identity after substituting `R=x^2+y^2`, `p=x^2y^2`, `T=z^2`
really is a four-square identity in `x,y,z`. -/
theorem criticalInterpolationRhs_substitution_four_sq
    (eta delta : ℕ) (alpha beta q h : MvPolynomial (Fin 3) ℝ) :
    criticalInterpolationRhs criticalX criticalY criticalR criticalP criticalT
        eta delta alpha beta q h =
      ((X 2 : MvPolynomial (Fin 3) ℝ) ^ eta * (alpha + 4 * criticalP * q)) ^ 2 +
        ((X 0 : MvPolynomial (Fin 3) ℝ) * (X 2 : MvPolynomial (Fin 3) ℝ) ^ delta *
          (beta + 2 * criticalY * h)) ^ 2 +
        ((X 1 : MvPolynomial (Fin 3) ℝ) * (X 2 : MvPolynomial (Fin 3) ℝ) ^ delta *
          (beta + 2 * criticalX * h)) ^ 2 +
        (2 * (X 0 : MvPolynomial (Fin 3) ℝ) * (X 1 : MvPolynomial (Fin 3) ℝ) *
          (X 2 : MvPolynomial (Fin 3) ℝ) ^ eta *
          ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 -
            (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) * q) ^ 2 := by
  unfold criticalInterpolationRhs criticalX criticalY criticalR criticalP criticalT
  have hEta : (((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2) ^ eta) =
      ((X 2 : MvPolynomial (Fin 3) ℝ) ^ eta) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hDelta : (((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2) ^ delta) =
      ((X 2 : MvPolynomial (Fin 3) ℝ) ^ delta) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hEta, hDelta]
  simp only [criticalX, criticalY]
  ring_nf

/-- The substituted interpolation expression is SOS, uniformly in the four auxiliary
polynomials. -/
theorem criticalInterpolationRhs_substitution_isSOS
    (eta delta : ℕ) (alpha beta q h : MvPolynomial (Fin 3) ℝ) :
    IsSOS (criticalInterpolationRhs criticalX criticalY criticalR criticalP criticalT
      eta delta alpha beta q h) := by
  let A : MvPolynomial (Fin 3) ℝ :=
    (X 2 : MvPolynomial (Fin 3) ℝ) ^ eta * (alpha + 4 * criticalP * q)
  let Bx : MvPolynomial (Fin 3) ℝ :=
    (X 0 : MvPolynomial (Fin 3) ℝ) * (X 2 : MvPolynomial (Fin 3) ℝ) ^ delta *
      (beta + 2 * criticalY * h)
  let By : MvPolynomial (Fin 3) ℝ :=
    (X 1 : MvPolynomial (Fin 3) ℝ) * (X 2 : MvPolynomial (Fin 3) ℝ) ^ delta *
      (beta + 2 * criticalX * h)
  let D : MvPolynomial (Fin 3) ℝ :=
    2 * (X 0 : MvPolynomial (Fin 3) ℝ) * (X 1 : MvPolynomial (Fin 3) ℝ) *
      (X 2 : MvPolynomial (Fin 3) ℝ) ^ eta *
        ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 -
          (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) * q
  refine IsSOS_of_four_sq (A := A) (B := Bx) (C := By) (D := D) ?_
  dsimp [A, Bx, By, D]
  exact criticalInterpolationRhs_substitution_four_sq eta delta alpha beta q h

/-- A critical interpolation identity immediately gives the critical SOS certificate.
This packages a critical interpolation identity as an SOS certificate. -/
theorem Pmlambda_critical_isSOS_of_interpolation_identity
    (m eta delta : ℕ) (alpha beta q h : MvPolynomial (Fin 3) ℝ)
    (hcrit : Pmlambda m (criticalLambda m) =
      criticalInterpolationRhs criticalX criticalY criticalR criticalP criticalT
        eta delta alpha beta q h) :
    IsSOS (Pmlambda m (criticalLambda m)) := by
  rw [hcrit]
  exact criticalInterpolationRhs_substitution_isSOS eta delta alpha beta q h

/-- The critical interpolation expression with the parity parameters specialized to `m`. -/
def criticalInterpolationFor (m : ℕ)
    (alpha beta q h : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  criticalInterpolationRhs criticalX criticalY criticalR criticalP criticalT
    (criticalEta m) (criticalDelta m) alpha beta q h

/-- The specialized critical interpolation expression is SOS. -/
theorem criticalInterpolationFor_isSOS
    (m : ℕ) (alpha beta q h : MvPolynomial (Fin 3) ℝ) :
    IsSOS (criticalInterpolationFor m alpha beta q h) := by
  unfold criticalInterpolationFor
  exact criticalInterpolationRhs_substitution_isSOS (criticalEta m) (criticalDelta m)
    alpha beta q h

/-- A critical interpolation identity with the canonical parity parameters immediately gives
the critical SOS certificate. -/
theorem Pmlambda_critical_isSOS_of_criticalInterpolation_identity
    (m : ℕ) (alpha beta q h : MvPolynomial (Fin 3) ℝ)
    (hcrit : Pmlambda m (criticalLambda m) = criticalInterpolationFor m alpha beta q h) :
    IsSOS (Pmlambda m (criticalLambda m)) := by
  rw [hcrit]
  exact criticalInterpolationFor_isSOS m alpha beta q h

/-- The homogeneous threshold form is affine in the product variable `x^2*y^2`. -/
theorem four_mul_Pmlambda_affine (m : ℕ) (lambda : ℝ) :
    4 * Pmlambda m lambda =
      sphereSq ^ m *
        (sphereSq * (MvPolynomial.C lambda *
              ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) -
            2 * sphereSq) ^ 2 +
          (MvPolynomial.C lambda : MvPolynomial (Fin 3) ℝ) ^ 2 *
            (4 * MvPolynomial.C lambda *
                ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 +
                  (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) -
              5 * sphereSq) *
              (((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 +
                  (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2) ^ 2 -
                4 * ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 *
                  (X 1 : MvPolynomial (Fin 3) ℝ) ^ 2))) := by
  unfold Pmlambda
  rw [show (4 : MvPolynomial (Fin 3) ℝ) * (sphereSq ^ m *
      Phi (MvPolynomial.C lambda * X 0 ^ 2) (MvPolynomial.C lambda * X 1 ^ 2) sphereSq) =
      sphereSq ^ m * (4 * Phi (MvPolynomial.C lambda * X 0 ^ 2)
        (MvPolynomial.C lambda * X 1 ^ 2) sphereSq) by ring]
  rw [four_mul_Phi_affine]

/-- The affine-in-`p` identity written in the critical-construction variables. -/
theorem four_mul_Pmlambda_affine_critical_variables (m : ℕ) (lambda : ℝ) :
    4 * Pmlambda m lambda =
      (criticalR + criticalT) ^ m *
        ((criticalR + criticalT) *
            (MvPolynomial.C lambda * criticalR - 2 * (criticalR + criticalT)) ^ 2 +
          (MvPolynomial.C lambda : MvPolynomial (Fin 3) ℝ) ^ 2 *
            (4 * MvPolynomial.C lambda * criticalR - 5 * (criticalR + criticalT)) *
              (criticalR ^ 2 - 4 * criticalP)) := by
  rw [four_mul_Pmlambda_affine, sphereSq_eq_criticalR_add_criticalT]
  unfold criticalR criticalP criticalX criticalY
  ring

/-- Dehomogenization formula for the homogeneous threshold form. -/
theorem dehomogenize3To2_Pmlambda (m : ℕ) (lambda : ℝ) :
    dehomogenize3To2 (Pmlambda m lambda) =
      (1 + (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2) ^ m *
        Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2)
          (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2)
          (1 + (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2) := by
  have hthree :
      (MvPolynomial.bind₁ ![(X 0 : MvPolynomial (Fin 2) ℝ), X 1, 1])
          (3 : MvPolynomial (Fin 3) ℝ) = (3 : MvPolynomial (Fin 2) ℝ) := by
    simpa using map_ofNat
      (MvPolynomial.aeval ![(X 0 : MvPolynomial (Fin 2) ℝ), X 1, 1] :
        MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ) 3
  simp [dehomogenize3To2, Pmlambda, sphereSq, Phi, hthree]
  ring_nf

/-- Dehomogenization preserves SOS witnesses. -/
theorem IsSOS.dehomogenize3To2 {p : MvPolynomial (Fin 3) ℝ} (hp : IsSOS p) :
    IsSOS (dehomogenize3To2 p) := by
  simpa [dehomogenize3To2] using
    IsSOS.aeval hp ![(X 0 : MvPolynomial (Fin 2) ℝ), X 1, 1]

/-- Dehomogenizing an SOS witness for `P_{m,lambda}` gives the explicit affine SOS. -/
theorem IsSOS.dehomogenize3To2_Pmlambda {m : ℕ} {lambda : ℝ}
    (hSOS : IsSOS (Pmlambda m lambda)) :
    IsSOS ((1 + (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2) ^ m *
      Phi (MvPolynomial.C lambda * (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2)
        (MvPolynomial.C lambda * (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2)
        (1 + (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 + (X 1 : MvPolynomial (Fin 2) ℝ) ^ 2)) := by
  rw [← _root_.OptimalConvergenceRates.ScaledRobinson.dehomogenize3To2_Pmlambda]
  exact IsSOS.dehomogenize3To2 hSOS

/-- The scaled ball generator has degree at most two. -/
theorem ballGenerator_totalDegree_le_two (lambda : ℝ) :
    (BallGenerator lambda).totalDegree ≤ 2 := by
  unfold BallGenerator
  calc (MvPolynomial.C lambda - (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 - X 1 ^ 2).totalDegree
      ≤ max (MvPolynomial.C lambda - (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2).totalDegree
          ((X 1 : MvPolynomial (Fin 2) ℝ) ^ 2).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ 2 := by
      apply max_le
      · calc (MvPolynomial.C lambda - (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2).totalDegree
            ≤ max (MvPolynomial.C lambda).totalDegree
                ((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2).totalDegree :=
              MvPolynomial.totalDegree_sub _ _
          _ ≤ 2 := by
            simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow]
      · simp [MvPolynomial.totalDegree_X_pow]

/-- Homogenizing a product by the ball generator factors through the homogeneous ball
generator, provided the other factor satisfies its degree bound. -/
theorem homogenize2To3_ballGenerator_mul_of_totalDegree_le {lambda : ℝ} {d : ℕ}
    {σ : MvPolynomial (Fin 2) ℝ} (hσ : σ.totalDegree ≤ d) :
    homogenize2To3 (2 + d) (BallGenerator lambda * σ) =
      HomBallGenerator lambda * homogenize2To3 d σ := by
  calc
    homogenize2To3 (2 + d) (BallGenerator lambda * σ)
        = homogenize2To3 2 (BallGenerator lambda) * homogenize2To3 d σ :=
          homogenize2To3_mul_of_totalDegree_le (d := 2) (e := d)
            (p := BallGenerator lambda) (q := σ) (ballGenerator_totalDegree_le_two lambda) hσ
    _ = HomBallGenerator lambda * homogenize2To3 d σ := by
          rw [homogenize2To3_ballGenerator]

/-- Homogeneous two-term certificate for the ball form `lambda*w^2 - x^2 - y^2`. -/
def HomBallCertificate (lambda : ℝ) (p : MvPolynomial (Fin 3) ℝ) : Prop :=
  ∃ τ0 τ1 : MvPolynomial (Fin 3) ℝ,
    IsSOS τ0 ∧ IsSOS τ1 ∧ p = τ0 + HomBallGenerator lambda * τ1

/-- Homogeneous ball certificate with total-degree bounds on the two SOS pieces.  The
root-degree bounds after dehomogenization follow from SOS no-cancellation. -/
def DegreeBoundedHomBallCertificate (lambda : ℝ) (r : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) : Prop :=
  ∃ τ0 τ1 : MvPolynomial (Fin 3) ℝ,
    IsSOS τ0 ∧ IsSOS τ1 ∧ τ0.totalDegree ≤ 2 * r ∧ τ1.totalDegree ≤ 2 * (r - 1) ∧
      p = τ0 + HomBallGenerator lambda * τ1

/-- Dehomogenizing a homogeneous ball certificate whose SOS pieces have total-degree
bounds gives an affine ball-module certificate with root-degree bounds. -/
theorem DegreeBoundedHomBallCertificate.dehomogenize_mem_BallQuadraticModule
    {lambda : ℝ} {r : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : DegreeBoundedHomBallCertificate lambda r p) :
    dehomogenize3To2 p ∈ BallQuadraticModule lambda r := by
  obtain ⟨τ0, τ1, hτ0, hτ1, hτ0deg, hτ1deg, hp_eq⟩ := hp
  refine ⟨dehomogenize3To2 τ0, dehomogenize3To2 τ1, ?_, ?_, ?_⟩
  · exact HasDegreeBoundedSOS.of_isSOS_totalDegree_le (IsSOS.dehomogenize3To2 hτ0)
      ((dehomogenize3To2_totalDegree_le τ0).trans hτ0deg)
  · exact HasDegreeBoundedSOS.of_isSOS_totalDegree_le (IsSOS.dehomogenize3To2 hτ1)
      ((dehomogenize3To2_totalDegree_le τ1).trans hτ1deg)
  · rw [hp_eq]
    simp only [map_add, map_mul]
    rw [dehomogenize3To2_HomBallGenerator]

/-- A degree-bounded homogeneous certificate for the Robinson homogenization
dehomogenizes to the corresponding affine ball-module certificate. -/
theorem DegreeBoundedHomBallCertificate.robinson_mem_BallQuadraticModule
    {m : ℕ} {lambda : ℝ}
    (hp : DegreeBoundedHomBallCertificate lambda (m + 3)
      ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson)) :
    robinson ∈ BallQuadraticModule lambda (m + 3) := by
  have hmem := hp.dehomogenize_mem_BallQuadraticModule
  rw [dehomogenize3To2_z_pow_mul_homRobinson] at hmem
  exact hmem

/-- An SOS representation of `P_{m,lambda}` gives the corresponding homogeneous
ball-module certificate, without yet recording degree bounds on the square roots. -/
theorem Pmlambda_isSOS_to_HomBallCertificate
    {m : ℕ} {lambda : ℝ} (hLam : 0 < lambda) (hSOS : IsSOS (Pmlambda m lambda)) :
    HomBallCertificate lambda
      ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) := by
  obtain ⟨N, A, B, hsum⟩ :=
    IsSOS.exists_zSquareSubst3_even_odd_witness hSOS (zReflect3_Pmlambda m lambda)
  let σ0 : MvPolynomial (Fin 3) ℝ :=
    ∑ i : Fin N, (homBallSourceSubst lambda (A i)) ^ 2
  let σ1 : MvPolynomial (Fin 3) ℝ :=
    ∑ i : Fin N, (homBallSourceSubst lambda (B i)) ^ 2
  have hpreSq : zSquareSubst3 (PmlambdaEvenSource m lambda) =
      zSquareSubst3 ((∑ i : Fin N, (A i) ^ 2) +
        (X 2 : MvPolynomial (Fin 3) ℝ) * ∑ i : Fin N, (B i) ^ 2) := by
    calc
      zSquareSubst3 (PmlambdaEvenSource m lambda) = Pmlambda m lambda :=
        zSquareSubst3_PmlambdaEvenSource m lambda
      _ = (∑ i : Fin N, (zSquareSubst3 (A i)) ^ 2) +
            ∑ i : Fin N, ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 (B i)) ^ 2 :=
          hsum
      _ = zSquareSubst3 ((∑ i : Fin N, (A i) ^ 2) +
            (X 2 : MvPolynomial (Fin 3) ℝ) * ∑ i : Fin N, (B i) ^ 2) := by
          simp only [map_add, map_mul, map_sum, map_pow, zSquareSubst3_X_two]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
  have hpre : PmlambdaEvenSource m lambda =
      (∑ i : Fin N, (A i) ^ 2) +
        (X 2 : MvPolynomial (Fin 3) ℝ) * ∑ i : Fin N, (B i) ^ 2 :=
    zSquareSubst3_injective hpreSq
  have hscaled : MvPolynomial.C (lambda ^ (m + 3)) *
        ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) =
      σ0 + HomBallGenerator lambda * σ1 := by
    calc
      MvPolynomial.C (lambda ^ (m + 3)) *
          ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson)
          = homBallSourceSubst lambda (PmlambdaEvenSource m lambda) := by
              rw [homBallSourceSubst_PmlambdaEvenSource]
      _ = homBallSourceSubst lambda
            ((∑ i : Fin N, (A i) ^ 2) +
              (X 2 : MvPolynomial (Fin 3) ℝ) * ∑ i : Fin N, (B i) ^ 2) := by
              rw [hpre]
      _ = σ0 + HomBallGenerator lambda * σ1 := by
              dsimp [σ0, σ1]
              simp only [map_add, map_mul, map_sum, map_pow]
              simp [homBallSourceSubst]
  have hσ0 : IsSOS σ0 := by
    dsimp [σ0]
    exact IsSOS.finset_sum (Finset.univ : Finset (Fin N))
      (fun i => (homBallSourceSubst lambda (A i)) ^ 2)
      (fun i _ => IsSOS_sq (homBallSourceSubst lambda (A i)))
  have hσ1 : IsSOS σ1 := by
    dsimp [σ1]
    exact IsSOS.finset_sum (Finset.univ : Finset (Fin N))
      (fun i => (homBallSourceSubst lambda (B i)) ^ 2)
      (fun i _ => IsSOS_sq (homBallSourceSubst lambda (B i)))
  let c : ℝ := lambda ^ (m + 3)
  have hcpos : 0 < c := by
    dsimp [c]
    exact pow_pos hLam (m + 3)
  have hcnonneg : 0 ≤ c⁻¹ := le_of_lt (inv_pos.mpr hcpos)
  refine ⟨MvPolynomial.C c⁻¹ * σ0, MvPolynomial.C c⁻¹ * σ1,
    IsSOS.const_mul hσ0 hcnonneg, IsSOS.const_mul hσ1 hcnonneg, ?_⟩
  calc
    (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson
        = MvPolynomial.C c⁻¹ *
            (MvPolynomial.C c * ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson)) := by
            rw [show MvPolynomial.C c⁻¹ *
                (MvPolynomial.C c * ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) *
                  homRobinson)) =
                (MvPolynomial.C c⁻¹ * MvPolynomial.C c) *
                  ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) by ring]
            rw [← MvPolynomial.C_mul]
            field_simp [ne_of_gt hcpos]
            simp
    _ = MvPolynomial.C c⁻¹ * (σ0 + HomBallGenerator lambda * σ1) := by
            rw [hscaled]
    _ = MvPolynomial.C c⁻¹ * σ0 +
          HomBallGenerator lambda * (MvPolynomial.C c⁻¹ * σ1) := by
            ring

/-- Degree-bounded version of `Pmlambda_isSOS_to_HomBallCertificate`, assuming the
post-substitution square roots have the degree bounds needed for dehomogenization.

After the even/odd `z`-splitting of an SOS witness for `P_{m,lambda}`, the
substitution `t = lambda*w^2 - x^2 - y^2` must preserve the relevant
root-degree bounds. -/
theorem Pmlambda_isSOS_to_DegreeBoundedHomBallCertificate_of_subst_degree_bounds
    {m : ℕ} {lambda : ℝ} (hLam : 0 < lambda) (_hSOS : IsSOS (Pmlambda m lambda))
    (hsubst :
      ∃ N : ℕ, ∃ A B : Fin N → MvPolynomial (Fin 3) ℝ,
        Pmlambda m lambda =
          (∑ i : Fin N, (zSquareSubst3 (A i)) ^ 2) +
            ∑ i : Fin N,
              ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 (B i)) ^ 2 ∧
        (∀ i : Fin N, (homBallSourceSubst lambda (A i)).totalDegree ≤ m + 3) ∧
        (∀ i : Fin N, (homBallSourceSubst lambda (B i)).totalDegree ≤ m + 2)) :
    DegreeBoundedHomBallCertificate lambda (m + 3)
      ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) := by
  obtain ⟨N, A, B, hsum, hAdeg, hBdeg⟩ := hsubst
  let σ0 : MvPolynomial (Fin 3) ℝ :=
    ∑ i : Fin N, (homBallSourceSubst lambda (A i)) ^ 2
  let σ1 : MvPolynomial (Fin 3) ℝ :=
    ∑ i : Fin N, (homBallSourceSubst lambda (B i)) ^ 2
  have hpreSq : zSquareSubst3 (PmlambdaEvenSource m lambda) =
      zSquareSubst3 ((∑ i : Fin N, (A i) ^ 2) +
        (X 2 : MvPolynomial (Fin 3) ℝ) * ∑ i : Fin N, (B i) ^ 2) := by
    calc
      zSquareSubst3 (PmlambdaEvenSource m lambda) = Pmlambda m lambda :=
        zSquareSubst3_PmlambdaEvenSource m lambda
      _ = (∑ i : Fin N, (zSquareSubst3 (A i)) ^ 2) +
            ∑ i : Fin N, ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 (B i)) ^ 2 :=
          hsum
      _ = zSquareSubst3 ((∑ i : Fin N, (A i) ^ 2) +
            (X 2 : MvPolynomial (Fin 3) ℝ) * ∑ i : Fin N, (B i) ^ 2) := by
          simp only [map_add, map_mul, map_sum, map_pow, zSquareSubst3_X_two]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
  have hpre : PmlambdaEvenSource m lambda =
      (∑ i : Fin N, (A i) ^ 2) +
        (X 2 : MvPolynomial (Fin 3) ℝ) * ∑ i : Fin N, (B i) ^ 2 :=
    zSquareSubst3_injective hpreSq
  have hscaled : MvPolynomial.C (lambda ^ (m + 3)) *
        ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) =
      σ0 + HomBallGenerator lambda * σ1 := by
    calc
      MvPolynomial.C (lambda ^ (m + 3)) *
          ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson)
          = homBallSourceSubst lambda (PmlambdaEvenSource m lambda) := by
              rw [homBallSourceSubst_PmlambdaEvenSource]
      _ = homBallSourceSubst lambda
            ((∑ i : Fin N, (A i) ^ 2) +
              (X 2 : MvPolynomial (Fin 3) ℝ) * ∑ i : Fin N, (B i) ^ 2) := by
              rw [hpre]
      _ = σ0 + HomBallGenerator lambda * σ1 := by
              dsimp [σ0, σ1]
              simp only [map_add, map_mul, map_sum, map_pow]
              simp [homBallSourceSubst]
  have hσ0 : IsSOS σ0 := by
    dsimp [σ0]
    exact IsSOS.finset_sum (Finset.univ : Finset (Fin N))
      (fun i => (homBallSourceSubst lambda (A i)) ^ 2)
      (fun i _ => IsSOS_sq (homBallSourceSubst lambda (A i)))
  have hσ1 : IsSOS σ1 := by
    dsimp [σ1]
    exact IsSOS.finset_sum (Finset.univ : Finset (Fin N))
      (fun i => (homBallSourceSubst lambda (B i)) ^ 2)
      (fun i _ => IsSOS_sq (homBallSourceSubst lambda (B i)))
  have hσ0deg : σ0.totalDegree ≤ 2 * (m + 3) := by
    dsimp [σ0]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    calc ((homBallSourceSubst lambda (A i)) ^ 2).totalDegree
        ≤ 2 * (homBallSourceSubst lambda (A i)).totalDegree :=
          MvPolynomial.totalDegree_pow _ 2
      _ ≤ 2 * (m + 3) := Nat.mul_le_mul_left 2 (hAdeg i)
  have hσ1deg : σ1.totalDegree ≤ 2 * ((m + 3) - 1) := by
    rw [show (m + 3) - 1 = m + 2 by omega]
    dsimp [σ1]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    calc ((homBallSourceSubst lambda (B i)) ^ 2).totalDegree
        ≤ 2 * (homBallSourceSubst lambda (B i)).totalDegree :=
          MvPolynomial.totalDegree_pow _ 2
      _ ≤ 2 * (m + 2) := Nat.mul_le_mul_left 2 (hBdeg i)
  let c : ℝ := lambda ^ (m + 3)
  have hcpos : 0 < c := by
    dsimp [c]
    exact pow_pos hLam (m + 3)
  have hcnonneg : 0 ≤ c⁻¹ := le_of_lt (inv_pos.mpr hcpos)
  refine ⟨MvPolynomial.C c⁻¹ * σ0, MvPolynomial.C c⁻¹ * σ1,
    IsSOS.const_mul hσ0 hcnonneg, IsSOS.const_mul hσ1 hcnonneg, ?_, ?_, ?_⟩
  · exact (totalDegree_C_mul_le c⁻¹ σ0).trans hσ0deg
  · exact (totalDegree_C_mul_le c⁻¹ σ1).trans hσ1deg
  · calc
      (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson
          = MvPolynomial.C c⁻¹ *
              (MvPolynomial.C c * ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) *
                homRobinson)) := by
              rw [show MvPolynomial.C c⁻¹ *
                  (MvPolynomial.C c * ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) *
                    homRobinson)) =
                  (MvPolynomial.C c⁻¹ * MvPolynomial.C c) *
                    ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) by ring]
              rw [← MvPolynomial.C_mul]
              field_simp [ne_of_gt hcpos]
              simp
      _ = MvPolynomial.C c⁻¹ * (σ0 + HomBallGenerator lambda * σ1) := by
              rw [hscaled]
      _ = MvPolynomial.C c⁻¹ * σ0 +
            HomBallGenerator lambda * (MvPolynomial.C c⁻¹ * σ1) := by
              ring

/-- Degree-bounded version of `Pmlambda_isSOS_to_HomBallCertificate`, assuming the
source square roots have the weighted degree bounds dictated by the square substitution
`t = z^2`. -/
theorem Pmlambda_isSOS_to_DegreeBoundedHomBallCertificate_of_source_weighted_bounds
    {m : ℕ} {lambda : ℝ} (hLam : 0 < lambda) (hSOS : IsSOS (Pmlambda m lambda))
    (hsubst :
      ∃ N : ℕ, ∃ A B : Fin N → MvPolynomial (Fin 3) ℝ,
        Pmlambda m lambda =
          (∑ i : Fin N, (zSquareSubst3 (A i)) ^ 2) +
            ∑ i : Fin N,
              ((X 2 : MvPolynomial (Fin 3) ℝ) * zSquareSubst3 (B i)) ^ 2 ∧
        (∀ i : Fin N, sourceWeightedDegree3 (A i) ≤ m + 3) ∧
        (∀ i : Fin N, sourceWeightedDegree3 (B i) ≤ m + 2)) :
    DegreeBoundedHomBallCertificate lambda (m + 3)
      ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson) := by
  obtain ⟨N, A, B, hsum, hAdeg, hBdeg⟩ := hsubst
  refine Pmlambda_isSOS_to_DegreeBoundedHomBallCertificate_of_subst_degree_bounds hLam hSOS ?_
  refine ⟨N, A, B, hsum, ?_, ?_⟩
  · intro i
    exact (homBallSourceSubst_totalDegree_le_weighted lambda (A i)).trans (hAdeg i)
  · intro i
    exact (homBallSourceSubst_totalDegree_le_weighted lambda (B i)).trans (hBdeg i)

/-- Degree-bounded homogeneous two-term certificate for the ball form
`lambda*w^2 - x^2 - y^2`.  The bounds are recorded on the affine square roots before
homogenization, which is the data carried by a truncated `BallQuadraticModule` certificate. -/
def BoundedHomBallCertificate (lambda : ℝ) (r : ℕ)
    (p : MvPolynomial (Fin 3) ℝ) : Prop :=
  ∃ σ0 σ1 : MvPolynomial (Fin 2) ℝ,
    HasDegreeBoundedSOS σ0 r ∧ HasDegreeBoundedSOS σ1 (r - 1) ∧
      p = homogenize2To3 (2 * r) σ0 +
        HomBallGenerator lambda * homogenize2To3 (2 * (r - 1)) σ1

/-- Forgetting degree bounds in a bounded homogeneous ball certificate. -/
theorem BoundedHomBallCertificate.toHomBallCertificate {lambda : ℝ} {r : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : BoundedHomBallCertificate lambda r p) :
    HomBallCertificate lambda p := by
  obtain ⟨σ0, σ1, hσ0, hσ1, hp_eq⟩ := hp
  exact ⟨homogenize2To3 (2 * r) σ0, homogenize2To3 (2 * (r - 1)) σ1,
    hσ0.homogenize_isSOS, hσ1.homogenize_isSOS, hp_eq⟩

/-- Dehomogenizing a bounded homogeneous ball certificate gives an affine ball-module
certificate with the same root-degree bounds. -/
theorem BoundedHomBallCertificate.dehomogenize_mem_BallQuadraticModule
    {lambda : ℝ} {r : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : BoundedHomBallCertificate lambda r p) :
    dehomogenize3To2 p ∈ BallQuadraticModule lambda r := by
  obtain ⟨σ0, σ1, hσ0, hσ1, hp_eq⟩ := hp
  refine ⟨σ0, σ1, hσ0, hσ1, ?_⟩
  rw [hp_eq]
  simp only [map_add, map_mul]
  rw [dehomogenize3To2_homogenize2To3, dehomogenize3To2_HomBallGenerator,
    dehomogenize3To2_homogenize2To3]

/-- A bounded homogeneous certificate for the Robinson homogenization dehomogenizes to the
corresponding affine ball-module certificate. -/
theorem BoundedHomBallCertificate.robinson_mem_BallQuadraticModule
    {m : ℕ} {lambda : ℝ}
    (hp : BoundedHomBallCertificate lambda (m + 3)
      ((X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) * homRobinson)) :
    robinson ∈ BallQuadraticModule lambda (m + 3) := by
  have hmem := hp.dehomogenize_mem_BallQuadraticModule
  rw [dehomogenize3To2_z_pow_mul_homRobinson] at hmem
  exact hmem

/-- Homogeneous ball certificates are antitone in the squared-radius parameter. -/
theorem HomBallCertificate.of_lambda_le {lambda lambda0 : ℝ} {p : MvPolynomial (Fin 3) ℝ}
    (hle : lambda ≤ lambda0) (hp : HomBallCertificate lambda0 p) :
    HomBallCertificate lambda p := by
  obtain ⟨τ0, τ1, hτ0, hτ1, hp_eq⟩ := hp
  refine ⟨τ0 + MvPolynomial.C (lambda0 - lambda) * (X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 * τ1,
    τ1, ?_, hτ1, ?_⟩
  · convert IsSOS.add hτ0
        (IsSOS.const_mul (IsSOS.z_sq_mul hτ1) (sub_nonneg.mpr hle)) using 1
    ring
  · rw [hp_eq]
    unfold HomBallGenerator
    rw [MvPolynomial.C_sub]
    ring

/-- An invariant homogeneous ball certificate can be represented with invariant SOS
summands. -/
theorem HomBallCertificate.exists_zReflect3_invariant_witness {lambda : ℝ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : HomBallCertificate lambda p)
    (hinv : zReflect3 p = p) :
    ∃ τ0 τ1 : MvPolynomial (Fin 3) ℝ,
      IsSOS τ0 ∧ IsSOS τ1 ∧ zReflect3 τ0 = τ0 ∧ zReflect3 τ1 = τ1 ∧
        p = τ0 + HomBallGenerator lambda * τ1 := by
  obtain ⟨σ0, σ1, hσ0, hσ1, hcert⟩ := hp
  let c : MvPolynomial (Fin 3) ℝ := MvPolynomial.C ((2 : ℝ)⁻¹)
  let τ0 : MvPolynomial (Fin 3) ℝ := c * (σ0 + zReflect3 σ0)
  let τ1 : MvPolynomial (Fin 3) ℝ := c * (σ1 + zReflect3 σ1)
  have hσ0_ref : IsSOS (zReflect3 σ0) := IsSOS.map_zReflect3 hσ0
  have hσ1_ref : IsSOS (zReflect3 σ1) := IsSOS.map_zReflect3 hσ1
  refine ⟨τ0, τ1, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [τ0, c]
    exact IsSOS.const_mul (IsSOS.add hσ0 hσ0_ref) (by norm_num : 0 ≤ ((2 : ℝ)⁻¹))
  · dsimp [τ1, c]
    exact IsSOS.const_mul (IsSOS.add hσ1 hσ1_ref) (by norm_num : 0 ≤ ((2 : ℝ)⁻¹))
  · dsimp [τ0, c]
    simp [zReflect3_involutive]
    ring
  · dsimp [τ1, c]
    simp [zReflect3_involutive]
    ring
  · have hreflect_cert :
        p = zReflect3 σ0 + HomBallGenerator lambda * zReflect3 σ1 := by
      calc
        p = zReflect3 p := by rw [hinv]
        _ = zReflect3 (σ0 + HomBallGenerator lambda * σ1) := by rw [hcert]
        _ = zReflect3 σ0 + HomBallGenerator lambda * zReflect3 σ1 := by
            simp [zReflect3_HomBallGenerator]
    dsimp [τ0, τ1, c]
    have hhalf :
        MvPolynomial.C ((2 : ℝ)⁻¹) * p + MvPolynomial.C ((2 : ℝ)⁻¹) * p = p := by
      rw [show MvPolynomial.C ((2 : ℝ)⁻¹) * p + MvPolynomial.C ((2 : ℝ)⁻¹) * p =
          (MvPolynomial.C ((2 : ℝ)⁻¹) * (2 : MvPolynomial (Fin 3) ℝ)) * p by ring]
      rw [show (2 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (2 : ℝ) from
        (MvPolynomial.C_eq_coe_nat 2).symm]
      rw [← MvPolynomial.C_mul]
      norm_num
    calc
      p = MvPolynomial.C ((2 : ℝ)⁻¹) * p + MvPolynomial.C ((2 : ℝ)⁻¹) * p := by
        rw [hhalf]
      _ = MvPolynomial.C ((2 : ℝ)⁻¹) * (σ0 + HomBallGenerator lambda * σ1) +
          MvPolynomial.C ((2 : ℝ)⁻¹) *
            (zReflect3 σ0 + HomBallGenerator lambda * zReflect3 σ1) := by
        nth_rw 1 [hcert]
        nth_rw 1 [hreflect_cert]
      _ = MvPolynomial.C ((2 : ℝ)⁻¹) * (σ0 + zReflect3 σ0) +
          HomBallGenerator lambda * (MvPolynomial.C ((2 : ℝ)⁻¹) * (σ1 + zReflect3 σ1)) := by
        ring

/-- Homogenizing a ball-module certificate gives a homogeneous certificate with SOS
homogenized summands. -/
theorem BallQuadraticModule.exists_homogenized_certificate
    {lambda : ℝ} {r : ℕ} {p : MvPolynomial (Fin 2) ℝ} (hr : 1 ≤ r)
    (hp : p ∈ BallQuadraticModule lambda r) :
    ∃ τ0 τ1 : MvPolynomial (Fin 3) ℝ,
      IsSOS τ0 ∧ IsSOS τ1 ∧
        homogenize2To3 (2 * r) p = τ0 + HomBallGenerator lambda * τ1 := by
  obtain ⟨σ0, σ1, hσ0, hσ1, hp_eq⟩ := hp
  refine ⟨homogenize2To3 (2 * r) σ0, homogenize2To3 (2 * (r - 1)) σ1,
    hσ0.homogenize_isSOS, hσ1.homogenize_isSOS, ?_⟩
  rw [hp_eq, homogenize2To3_add]
  congr 1
  have harith : 2 * r = 2 + 2 * (r - 1) := by omega
  rw [harith]
  exact homogenize2To3_ballGenerator_mul_of_totalDegree_le hσ1.totalDegree_le

/-- An affine ball-module certificate homogenizes to a homogeneous ball certificate. -/
theorem BallQuadraticModule.homogenize_mem_HomBallCertificate
    {lambda : ℝ} {r : ℕ} {p : MvPolynomial (Fin 2) ℝ} (hr : 1 ≤ r)
    (hp : p ∈ BallQuadraticModule lambda r) :
    HomBallCertificate lambda (homogenize2To3 (2 * r) p) := by
  obtain ⟨τ0, τ1, hτ0, hτ1, hcert⟩ :=
    BallQuadraticModule.exists_homogenized_certificate (lambda := lambda) (r := r)
      (p := p) hr hp
  exact ⟨τ0, τ1, hτ0, hτ1, hcert⟩

/-- An affine ball-module certificate homogenizes to a bounded homogeneous ball certificate. -/
theorem BallQuadraticModule.homogenize_mem_BoundedHomBallCertificate
    {lambda : ℝ} {r : ℕ} {p : MvPolynomial (Fin 2) ℝ} (hr : 1 ≤ r)
    (hp : p ∈ BallQuadraticModule lambda r) :
    BoundedHomBallCertificate lambda r (homogenize2To3 (2 * r) p) := by
  obtain ⟨σ0, σ1, hσ0, hσ1, hp_eq⟩ := hp
  refine ⟨σ0, σ1, hσ0, hσ1, ?_⟩
  rw [hp_eq, homogenize2To3_add]
  congr 1
  have harith : 2 * r = 2 + 2 * (r - 1) := by omega
  rw [harith]
  exact homogenize2To3_ballGenerator_mul_of_totalDegree_le hσ1.totalDegree_le

/-- Ball-module certificates have the expected coarse total-degree bound. -/
theorem BallQuadraticModule.totalDegree_le {lambda : ℝ} {r : ℕ}
    {p : MvPolynomial (Fin 2) ℝ} (hp : p ∈ BallQuadraticModule lambda r) :
    p.totalDegree ≤ max (2 * r) (2 + 2 * (r - 1)) := by
  obtain ⟨σ0, σ1, hσ0, hσ1, hp_eq⟩ := hp
  rw [hp_eq]
  calc (σ0 + BallGenerator lambda * σ1).totalDegree
      ≤ max σ0.totalDegree (BallGenerator lambda * σ1).totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ max (2 * r) (2 + 2 * (r - 1)) := by
      apply max_le_max
      · exact hσ0.totalDegree_le
      · calc (BallGenerator lambda * σ1).totalDegree
            ≤ (BallGenerator lambda).totalDegree + σ1.totalDegree :=
              MvPolynomial.totalDegree_mul _ _
          _ ≤ 2 + 2 * (r - 1) :=
              Nat.add_le_add (ballGenerator_totalDegree_le_two lambda) hσ1.totalDegree_le

/-- The Robinson polynomial has total degree at most six. -/
theorem robinson_totalDegree_le_six : robinson.totalDegree ≤ 6 := by
  let A : MvPolynomial (Fin 2) ℝ := (X 0) ^ 6 + (X 1) ^ 6 + 1
  let B : MvPolynomial (Fin 2) ℝ := (X 0) ^ 4 * (X 1) ^ 2 + (X 0) ^ 4 +
    (X 0) ^ 2 * (X 1) ^ 4 + (X 1) ^ 4 + (X 0) ^ 2 + (X 1) ^ 2
  let C : MvPolynomial (Fin 2) ℝ := 3 * (X 0) ^ 2 * (X 1) ^ 2
  have hA : A.totalDegree ≤ 6 := by
    dsimp [A]
    calc (((X 0 : MvPolynomial (Fin 2) ℝ) ^ 6 + X 1 ^ 6 + 1).totalDegree)
        ≤ max (((X 0 : MvPolynomial (Fin 2) ℝ) ^ 6 + X 1 ^ 6).totalDegree)
            (1 : MvPolynomial (Fin 2) ℝ).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ 6 := by
        apply max_le
        · calc (((X 0 : MvPolynomial (Fin 2) ℝ) ^ 6 + X 1 ^ 6).totalDegree)
              ≤ max (((X 0 : MvPolynomial (Fin 2) ℝ) ^ 6).totalDegree)
                  (((X 1 : MvPolynomial (Fin 2) ℝ) ^ 6).totalDegree) :=
                MvPolynomial.totalDegree_add _ _
            _ ≤ 6 := by simp [MvPolynomial.totalDegree_X_pow]
        · simp
  have hB : B.totalDegree ≤ 6 := by
    dsimp [B]
    repeat first | apply le_trans (MvPolynomial.totalDegree_add _ _) | apply max_le
    all_goals try simp [MvPolynomial.totalDegree_X_pow]
    · exact (totalDegree_X0_pow_mul_X1_pow_le 4 2).trans (by norm_num)
    · exact (totalDegree_X0_pow_mul_X1_pow_le 2 4).trans (by norm_num)
  have hC : C.totalDegree ≤ 6 := by
    dsimp [C]
    calc (((3 : MvPolynomial (Fin 2) ℝ) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 *
          X 1 ^ 2).totalDegree)
        ≤ (((3 : MvPolynomial (Fin 2) ℝ) * (X 0 : MvPolynomial (Fin 2) ℝ) ^ 2).totalDegree) +
            (((X 1 : MvPolynomial (Fin 2) ℝ) ^ 2).totalDegree) :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ (((3 : MvPolynomial (Fin 2) ℝ)).totalDegree +
              (((X 0 : MvPolynomial (Fin 2) ℝ) ^ 2).totalDegree)) +
            (((X 1 : MvPolynomial (Fin 2) ℝ) ^ 2).totalDegree) := by
          exact Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
      _ ≤ 6 := by
          rw [← show (MvPolynomial.C (3 : ℝ) : MvPolynomial (Fin 2) ℝ) = 3 from
            MvPolynomial.C_eq_coe_nat 3]
          simp [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_C]
  unfold robinson
  change (A - B + C).totalDegree ≤ 6
  calc (A - B + C).totalDegree ≤ max (A - B).totalDegree C.totalDegree :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 6 := by
        apply max_le
        · exact (MvPolynomial.totalDegree_sub A B).trans (max_le hA hB)
        · exact hC

/-- Homogenizing to a larger target degree adds powers of the homogenizing variable. -/
theorem homogenize2To3_add_right_of_totalDegree_le {d k : ℕ}
    {p : MvPolynomial (Fin 2) ℝ} (hp : p.totalDegree ≤ d) :
    homogenize2To3 (d + k) p =
      homogenize2To3 d p * (X 2 : MvPolynomial (Fin 3) ℝ) ^ k := by
  calc
    homogenize2To3 (d + k) p = homogenize2To3 (d + k)
        (p * (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ)) := by simp
    _ = homogenize2To3 d p * homogenize2To3 k (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ) := by
        exact homogenize2To3_mul_of_totalDegree_le (d := d) (e := k) (p := p)
          (q := (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℝ)) hp (by simp)
    _ = homogenize2To3 d p * (X 2 : MvPolynomial (Fin 3) ℝ) ^ k := by
        rw [homogenize2To3_C]
        simp

/-- Higher-degree homogenization of Robinson adds the corresponding power of `z`. -/
theorem homogenize2To3_robinson_mul_z_pow (m : ℕ) :
    homogenize2To3 (2 * (m + 3)) robinson =
      homRobinson * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m) := by
  have harith : 2 * (m + 3) = 6 + 2 * m := by omega
  rw [harith]
  rw [homogenize2To3_add_right_of_totalDegree_le (d := 6) (k := 2 * m)
    (p := robinson) robinson_totalDegree_le_six]
  rw [homogenize2To3_robinson]

/-- A ball-module certificate for `robinson` gives the corresponding homogeneous certificate. -/
theorem robinson_mem_ballQuadraticModule_to_HomBallCertificate
    {m : ℕ} {lambda : ℝ} (hp : robinson ∈ BallQuadraticModule lambda (m + 3)) :
    HomBallCertificate lambda
      (homRobinson * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m)) := by
  have hcert := BallQuadraticModule.homogenize_mem_HomBallCertificate
    (lambda := lambda) (r := m + 3) (p := robinson) (by omega : 1 ≤ m + 3) hp
  rwa [homogenize2To3_robinson_mul_z_pow] at hcert

/-- A ball-module certificate for `robinson` gives the corresponding bounded homogeneous
certificate, retaining the truncation data from the affine module. -/
theorem robinson_mem_ballQuadraticModule_to_BoundedHomBallCertificate
    {m : ℕ} {lambda : ℝ} (hp : robinson ∈ BallQuadraticModule lambda (m + 3)) :
    BoundedHomBallCertificate lambda (m + 3)
      (homRobinson * (X 2 : MvPolynomial (Fin 3) ℝ) ^ (2 * m)) := by
  have hcert := BallQuadraticModule.homogenize_mem_BoundedHomBallCertificate
    (lambda := lambda) (r := m + 3) (p := robinson) (by omega : 1 ≤ m + 3) hp
  rwa [homogenize2To3_robinson_mul_z_pow] at hcert

/-- The `x^6` coefficient of the dehomogenized Robinson polynomial is nonzero. -/
theorem robinson_coeff_x6 :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 6) robinson = 1 := by
  have hzero : ¬ (0 : Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 2) 6 := by
    intro h
    have : (0 : Fin 2 →₀ ℕ) 0 = (Finsupp.single (0 : Fin 2) 6) 0 := by rw [h]
    simp at this
  unfold robinson
  simp [MvPolynomial.coeff_add, MvPolynomial.coeff_sub, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_X_pow, MvPolynomial.coeff_one, Finsupp.single_eq_single_iff, hzero]

/-- The Robinson polynomial has total degree at least six. -/
theorem six_le_robinson_totalDegree : 6 ≤ robinson.totalDegree := by
  have hcoeff : MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 6) robinson ≠ 0 := by
    rw [robinson_coeff_x6]
    norm_num
  have hmem : Finsupp.single (0 : Fin 2) 6 ∈ robinson.support := by
    rw [MvPolynomial.mem_support_iff]
    exact hcoeff
  simpa using MvPolynomial.le_totalDegree hmem

/-- No ball-module certificate for `robinson` exists below order three. -/
theorem robinson_not_mem_ballQuadraticModule_of_lt_three {lambda : ℝ} {r : ℕ}
    (hr : r < 3) : robinson ∉ BallQuadraticModule lambda r := by
  intro hmem
  have hdeg := BallQuadraticModule.totalDegree_le hmem
  have hlow : max (2 * r) (2 + 2 * (r - 1)) < 6 := by omega
  exact not_lt_of_ge six_le_robinson_totalDegree (hdeg.trans_lt hlow)

end ScaledRobinson
end OptimalConvergenceRates

end
