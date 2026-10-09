/-
  The qualitative compactness input: strict Schmüdgen and Wörmann's trick.
-/
import OptimalConvergenceRates.GeneralCompact.Geometry
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanEnvelope
import OptimalConvergenceRates.KrivineStengle.Nonnegative
import OptimalConvergenceRates.KrivineStengle.PreorderingMinimality

noncomputable section

open MvPolynomial Finset

namespace OptimalConvergenceRates.GeneralCompact

variable {n m : ℕ}

namespace PreorderingMem

open KrivineStengle

/-- Every SOS polynomial belongs to every generated preordering. -/
theorem of_isSOS (g : Fin m → MvPolynomial (Fin n) ℝ)
    {p : MvPolynomial (Fin n) ℝ} (hp : IsSOS p) :
    PreorderingMem g p := by
  exact ⟨p.totalDegree,
    GenQuadraticModule_subset_GenPreordering
      (genQuadraticModule_sos g hp le_rfl)⟩

/-- A finite sum of preordering elements is a preordering element. -/
theorem sum {ι : Type*} {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (p : ι → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i ∈ s, PreorderingMem g (p i)) :
    PreorderingMem g (∑ i ∈ s, p i) :=
  (preorderingMem_isSquareCone g).sum_mem hp

/-- Multiplication by a nonnegative real scalar preserves membership. -/
theorem scale_nonneg {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p : MvPolynomial (Fin n) ℝ} (hp : PreorderingMem g p)
    {a : ℝ} (ha : 0 ≤ a) : PreorderingMem g (C a * p) :=
  preorderingMem_mul (of_isSOS g (IsSOS_C_nonneg a ha)) hp

end PreorderingMem

open KrivineStengle

/-- Splitting after adjoining one generator: the even part belongs to the
old preordering and the odd part is the new generator times an old
preordering element. -/
theorem split_appendGenerator
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    {h q : MvPolynomial (Fin n) ℝ}
    (hq : PreorderingMem (appendGenerator g h) q) :
    ∃ s t, PreorderingMem g s ∧ PreorderingMem g t ∧ q = s + h * t := by
  let T : Set (MvPolynomial (Fin n) ℝ) := {p | PreorderingMem g p}
  let D := IsSquareCone.adjoinSign T h
  have hT : IsSquareCone T := preorderingMem_isSquareCone g
  have hD : IsSquareCone D := hT.isSquareCone_adjoinSign h
  have hgenerators : ∀ i, appendGenerator g h i ∈ D := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [D] using hT.mem_adjoinSign h
    · apply hT.subset_adjoinSign h
      simpa [T] using preorderingMem_generator g j
  have hqD : q ∈ D := hq.mem_squareCone hD hgenerators
  rcases hqD with ⟨s, hs, t, ht, hst⟩
  exact ⟨s, t, hs, ht, hst⟩

/-- A positive real constant remains strictly positive under any unital
ring homomorphism from the real polynomial ring to an ordered field. -/
private theorem map_C_pos
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (phi : MvPolynomial (Fin n) ℝ →+* F) {a : ℝ} (ha : 0 < a) :
    0 < phi (C a) := by
  let psi : ℝ →+* F := phi.comp (MvPolynomial.C : ℝ →+* MvPolynomial (Fin n) ℝ)
  have hsqrt : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hmap : psi (Real.sqrt a) ≠ 0 := by
    simpa using (RingHom.injective psi).ne hsqrt
  calc
    0 < psi (Real.sqrt a) ^ 2 := sq_pos_of_ne_zero hmap
    _ = psi a := by rw [← map_pow, Real.sq_sqrt ha.le]
    _ = phi (C a) := rfl

/-- Strict Krivine--Stengle in the form needed by Wörmann's trick. -/
theorem strict_certificate_of_positive_margin
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hp : ∀ x ∈ basicClosedSet g, delta ≤ eval x p) :
    ∃ a b, PreorderingMem g a ∧ PreorderingMem g b ∧
      p * a = 1 + b := by
  let g' := appendGenerator g (-p)
  have hrefute : PreorderingMem g' (-1) := by
    by_contra hnot
    have hproper : IsProperSquareCone {q | PreorderingMem g' q} :=
      ⟨preorderingMem_isSquareCone g', hnot⟩
    obtain ⟨sep⟩ := exists_orderedFieldSeparator hproper
    let F := sep.FieldType
    letI : Field F := sep.field
    letI : LinearOrder F := sep.order
    letI : IsStrictOrderedRing F := sep.strictOrderedRing
    let phi : MvPolynomial (Fin n) ℝ →+* F := sep.map
    have hg : ∀ i, 0 ≤ phi (g i) := by
      intro i
      exact sep.nonneg (by
        simpa [g', phi] using
          preorderingMem_generator g' i.castSucc)
    have hp_nonpos : phi p ≤ 0 := by
      have hlast := sep.nonneg (by
        simpa [g', phi] using
          preorderingMem_generator g' (Fin.last m))
      simpa [map_neg] using hlast
    have hshift : phi (p - C delta) < 0 := by
      rw [map_sub]
      have hconst := map_C_pos phi hdelta
      linarith
    obtain ⟨x, hx, hpx⟩ :=
      finiteSignRealization g (p - C delta) F phi hg hshift
    have hxlower := hp x hx
    simp only [eval_sub, eval_C] at hpx
    linarith
  obtain ⟨s, t, hs, ht, hid⟩ :=
    split_appendGenerator (g := g) (h := -p) hrefute
  refine ⟨t, s, ht, hs, ?_⟩
  linear_combination hid

/-- Strictly positive polynomials on a nonempty compact basic closed set
belong to its preordering.  The slightly stronger multiplicative identity
is retained because Wörmann's trick uses it. -/
theorem strict_compact_certificate
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ)
    (hne : (basicClosedSet g).Nonempty)
    (hcompact : IsCompact (basicClosedSet g))
    (hp : ∀ x ∈ basicClosedSet g, 0 < eval x p) :
    ∃ a b, PreorderingMem g a ∧ PreorderingMem g b ∧
      p * a = 1 + b := by
  obtain ⟨x₀, hx₀, hmin⟩ :=
    polynomialMinimum_mem_of_compact hne hcompact p
  let delta := GeneralArchimedean.polynomialMinimum g p
  have hdelta : 0 < delta := by simpa [delta, ← hmin] using hp x₀ hx₀
  apply strict_certificate_of_positive_margin g p hdelta
  intro x hx
  exact polynomialMinimum_le_eval_of_compact hcompact p hx

/-- A quadratic-module certificate in the singleton ball generator can be
multiplied by a fixed preordering element and transported back to the
original preordering. -/
private theorem mul_singleton_module_mem
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p u q : MvPolynomial (Fin n) ℝ)
    (hu : PreorderingMem g u) (hup : PreorderingMem g (u * p))
    (hq : GeneralArchimedean.QuadraticModuleMem
      (fun _ : Fin 1 ↦ p) q) :
    PreorderingMem g (u * q) := by
  obtain ⟨r, sigmaZero, sigma, hsigmaZero, hsigma,
    hdegreeZero, hdegree, hid⟩ := hq
  have hzero : PreorderingMem g (u * sigmaZero) :=
    preorderingMem_mul hu (PreorderingMem.of_isSOS g hsigmaZero)
  have hterms : ∀ i : Fin 1,
      PreorderingMem g (u * (sigma i * p)) := by
    intro i
    have hsig := PreorderingMem.of_isSOS g (hsigma i)
    have := preorderingMem_mul hsig hup
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hsum : PreorderingMem g (∑ i : Fin 1, u * (sigma i * p)) :=
    PreorderingMem.sum Finset.univ _ (fun i _ ↦ hterms i)
  have hall := preorderingMem_add hzero hsum
  rw [hid]
  convert hall using 1
  rw [mul_add, Finset.mul_sum]

/-- Wörmann's trick: compactness makes the generated preordering
Archimedean, without assuming that the displayed quadratic module is. -/
theorem compact_isPreorderingArchimedean
    (g : Fin m → MvPolynomial (Fin n) ℝ)
    (hne : (basicClosedSet g).Nonempty)
    (hcompact : IsCompact (basicClosedSet g)) :
    IsPreorderingArchimedean g := by
  obtain ⟨R, hR, hballpos⟩ := compact_exists_sum_sq_lt hne hcompact
  let S : MvPolynomial (Fin n) ℝ := ∑ i, X i ^ 2
  let p : MvPolynomial (Fin n) ℝ := C R - S
  have hp : ∀ x ∈ basicClosedSet g, 0 < eval x p := by
    intro x hx
    have := hballpos x hx
    simpa [p, S] using sub_pos.mpr this
  obtain ⟨a, b, ha, hb, hab⟩ :=
    strict_compact_certificate g p hne hcompact hp
  let u : MvPolynomial (Fin n) ℝ := 1 + b
  have hu : PreorderingMem g u :=
    preorderingMem_add (preorderingMem_one g) hb
  have hup : PreorderingMem g (u * p) := by
    have hpa2 : PreorderingMem g (p ^ 2 * a) :=
      preorderingMem_mul (preorderingMem_sq g p) ha
    rw [show u * p = p ^ 2 * a by
      dsimp [u]
      rw [← hab]
      ring]
    exact hpa2
  let g₀ : Fin 1 → MvPolynomial (Fin n) ℝ := fun _ ↦ p
  have harch₀ : GeneralArchimedean.IsArchimedean g₀ := by
    refine ⟨R, p.totalDegree, hR, ?_⟩
    simpa [g₀, p, S] using genQuadraticModule_generator g₀ (0 : Fin 1)
  obtain ⟨B, hB, hplus, hminus⟩ :=
    harch₀.exists_coefficient_envelope b
  let E := GeneralArchimedean.weightedCoeffEnvelope B b
  have huEb : PreorderingMem g (u * (C E - b)) := by
    exact mul_singleton_module_mem g p u (C E - b) hu hup (by
      simpa [E] using hminus)
  let L : ℝ := E + (E / 2) ^ 2
  have hLb : PreorderingMem g (C L - b) := by
    have hsquare := preorderingMem_sq g (b - C (E / 2))
    have hadd := preorderingMem_add huEb hsquare
    have hCL : (C L : MvPolynomial (Fin n) ℝ) =
        C E + C (E / 2) ^ 2 := by
      simp [L, map_add, map_pow]
    have hhalf : (C E : MvPolynomial (Fin n) ℝ) = C (E / 2) * 2 := by
      change C E = C (E / 2) * C 2
      rw [← map_mul]
      congr 1
      ring
    rw [hCL]
    convert hadd using 1
    dsimp [u]
    rw [hhalf]
    ring
  have hsumSOS : IsSOS S := by
    dsimp [S]
    exact IsSOS_sum_finset fun i _ ↦ IsSOS_sq (X i)
  have hbS : PreorderingMem g (b * S) :=
    preorderingMem_mul hb (PreorderingMem.of_isSOS g hsumSOS)
  have hfirst := preorderingMem_add hup hbS
  have hscaled : PreorderingMem g (C R * (C L - b)) :=
    PreorderingMem.scale_nonneg hLb hR.le
  have hfinal := preorderingMem_add hfirst hscaled
  obtain ⟨r, hr⟩ := hfinal
  refine ⟨R * (L + 1), r, mul_pos hR ?_, ?_⟩
  · have hE : 0 ≤ E :=
      GeneralArchimedean.weightedCoeffEnvelope_nonneg
        (zero_le_one.trans hB) b
    dsimp [L]
    nlinarith [sq_nonneg E]
  · convert hr using 1
    dsimp [u, p, S, L]
    simp only [map_add, map_mul, map_pow, map_one]
    ring

end OptimalConvergenceRates.GeneralCompact

end
