/-
  OptimalConvergenceRates/KrivineStengle/PrimeCone.lean

  Maximal proper cones, totality, and prime support.
-/
import OptimalConvergenceRates.KrivineStengle.SquareCone
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

variable {R : Type*} [CommRing R]

/-- The product alternative for a maximal proper square cone. -/
theorem maximalProperCone_productAlternative {C P : Set R}
    (hmax : Maximal (fun Q : Set R ↦ IsProperSquareCone Q ∧ C ⊆ Q) P)
    {a b : R} (hab : a * b ∈ P) : a ∈ P ∨ -b ∈ P := by
  by_contra hnot
  rw [not_or] at hnot
  have hPproper : IsProperSquareCone P := hmax.prop.1
  have hP : IsSquareCone P := hPproper.1
  have hCa : C ⊆ IsSquareCone.adjoinSign P a :=
    hmax.prop.2.trans (hP.subset_adjoinSign a)
  have himproper_a : ¬IsProperSquareCone (IsSquareCone.adjoinSign P a) := by
    intro hproper
    have heq := hmax.eq_of_le ⟨hproper, hCa⟩ (hP.subset_adjoinSign a)
    exact hnot.1 (heq ▸ hP.mem_adjoinSign a)
  have hneg_a : (-1 : R) ∈ IsSquareCone.adjoinSign P a := by
    apply Classical.byContradiction
    intro hneg
    exact himproper_a ⟨hP.isSquareCone_adjoinSign a, hneg⟩
  obtain ⟨u, hu, v, hv, huv⟩ := hneg_a
  have hCnb : C ⊆ IsSquareCone.adjoinSign P (-b) :=
    hmax.prop.2.trans (hP.subset_adjoinSign (-b))
  have himproper_nb : ¬IsProperSquareCone (IsSquareCone.adjoinSign P (-b)) := by
    intro hproper
    have heq := hmax.eq_of_le ⟨hproper, hCnb⟩ (hP.subset_adjoinSign (-b))
    exact hnot.2 (heq ▸ hP.mem_adjoinSign (-b))
  have hneg_nb : (-1 : R) ∈ IsSquareCone.adjoinSign P (-b) := by
    apply Classical.byContradiction
    intro hneg
    exact himproper_nb ⟨hP.isSquareCone_adjoinSign (-b), hneg⟩
  obtain ⟨w, hw, z, hz, hwz⟩ := hneg_nb
  have hav : a * v = -1 - u := by
    calc
      a * v = (u + a * v) - u := by ring
      _ = -1 - u := by rw [← huv]
  have hnbz : (-b) * z = -1 - w := by
    calc
      (-b) * z = (w + (-b) * z) - w := by ring
      _ = -1 - w := by rw [← hwz]
  have hbz : b * z = 1 + w := by
    calc
      b * z = -((-b) * z) := by ring
      _ = -(-1 - w) := by rw [hnbz]
      _ = 1 + w := by ring
  have habvz : a * b * v * z ∈ P := by
    exact hP.mul_mem (hP.mul_mem hab hv) hz
  have hmem : u + w + u * w + a * b * v * z ∈ P := by
    exact hP.add_mem (hP.add_mem (hP.add_mem hu hw) (hP.mul_mem hu hw)) habvz
  have hid : u + w + u * w + a * b * v * z = -1 := by
    calc
      u + w + u * w + a * b * v * z =
          u + w + u * w + (a * v) * (b * z) := by ring
      _ = u + w + u * w + (-1 - u) * (1 + w) := by rw [hav, hbz]
      _ = -1 := by ring
  exact hPproper.2 (hid ▸ hmem)

/-- A maximal proper square cone contains one of the two signs of every element. -/
theorem maximalProperCone_total {C P : Set R}
    (hmax : Maximal (fun Q : Set R ↦ IsProperSquareCone Q ∧ C ⊆ Q) P)
    (x : R) : x ∈ P ∨ -x ∈ P := by
  have hsquare : x * x ∈ P := by
    simpa [pow_two] using hmax.prop.1.1.sq_mem x
  exact maximalProperCone_productAlternative hmax (a := x) (b := x) hsquare

/-- The support of a total square cone, bundled as an ideal. -/
def coneSupport (P : Set R) (hP : IsSquareCone P) (htotal : ∀ x, x ∈ P ∨ -x ∈ P) :
    Ideal R where
  carrier := {x | x ∈ P ∧ -x ∈ P}
  zero_mem' := ⟨hP.zero_mem, by simpa using hP.zero_mem⟩
  add_mem' := by
    rintro x y ⟨hx, hnx⟩ ⟨hy, hny⟩
    exact ⟨hP.add_mem hx hy, by simpa [add_comm] using hP.add_mem hnx hny⟩
  smul_mem' := by
    rintro c x ⟨hx, hnx⟩
    rcases htotal c with hc | hnc
    · exact ⟨hP.mul_mem hc hx, by simpa using hP.mul_mem hc hnx⟩
    · exact ⟨by simpa using hP.mul_mem hnc hnx, by simpa using hP.mul_mem hnc hx⟩

@[simp]
theorem mem_coneSupport {P : Set R} {hP : IsSquareCone P}
    {htotal : ∀ x, x ∈ P ∨ -x ∈ P} {x : R} :
    x ∈ coneSupport P hP htotal ↔ x ∈ P ∧ -x ∈ P :=
  Iff.rfl

/-- The support of a maximal proper cone is prime. -/
theorem maximalProperCone_support_isPrime {C P : Set R}
    (hmax : Maximal (fun Q : Set R ↦ IsProperSquareCone Q ∧ C ⊆ Q) P) :
    (coneSupport P hmax.prop.1.1 (maximalProperCone_total hmax)).IsPrime := by
  let hP : IsSquareCone P := hmax.prop.1.1
  let htotal : ∀ x, x ∈ P ∨ -x ∈ P := maximalProperCone_total hmax
  let I := coneSupport P hP htotal
  refine ⟨?_, ?_⟩
  · intro htop
    have hneg : (-1 : R) ∈ P := by
      have hone : (1 : R) ∈ coneSupport P hP htotal := by
        rw [htop]
        exact Set.mem_univ 1
      exact hone.2
    exact hmax.prop.1.2 hneg
  · intro x y hxy
    have hxyP : x * y ∈ P := hxy.1
    have hnxyP : -(x * y) ∈ P := hxy.2
    have h₁ := maximalProperCone_productAlternative hmax (a := x) (b := y) hxyP
    have h₂ := maximalProperCone_productAlternative hmax (a := -x) (b := y)
      (by simpa using hnxyP)
    have h₃ := maximalProperCone_productAlternative hmax (a := x) (b := -y)
      (by simpa using hnxyP)
    have h₄ := maximalProperCone_productAlternative hmax (a := -x) (b := -y)
      (by simpa using hxyP)
    by_cases hx : x ∈ P
    · by_cases hnx : -x ∈ P
      · exact Or.inl ⟨hx, hnx⟩
      · have hny : -y ∈ P := h₂.resolve_left hnx
        have hy : y ∈ P := by simpa using h₄.resolve_left hnx
        exact Or.inr ⟨hy, hny⟩
    · have hny : -y ∈ P := h₁.resolve_left hx
      have hy : y ∈ P := by simpa using h₃.resolve_left hx
      exact Or.inr ⟨hy, hny⟩

end OptimalConvergenceRates.KrivineStengle

end
