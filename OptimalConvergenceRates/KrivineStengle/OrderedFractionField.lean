/-
  OptimalConvergenceRates/KrivineStengle/OrderedFractionField.lean

  Ordered-field separation for proper square cones.
-/
import OptimalConvergenceRates.KrivineStengle.PrimeCone
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u

variable {R : Type u} [CommRing R]

/-- The image of a total cone in the quotient by its support. -/
def quotientCone (P : Set R) (hP : IsSquareCone P)
    (htotal : ∀ x, x ∈ P ∨ -x ∈ P) : RingCone (R ⧸ coneSupport P hP htotal) where
  carrier := {x | ∃ a ∈ P, Ideal.Quotient.mk (coneSupport P hP htotal) a = x}
  zero_mem' := ⟨0, hP.zero_mem, map_zero _⟩
  one_mem' := ⟨1, hP.one_mem, map_one _⟩
  add_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, hP.add_mem ha hb, map_add _ _ _⟩
  mul_mem' := by
    rintro x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, hP.mul_mem ha hb, map_mul _ _ _⟩
  eq_zero_of_mem_of_neg_mem' := by
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbnx⟩
    have hab0 : Ideal.Quotient.mk (coneSupport P hP htotal) (a + b) = 0 := by
      rw [map_add, hax, hbnx]
      simp
    have hab_support : a + b ∈ coneSupport P hP htotal :=
      Ideal.Quotient.eq_zero_iff_mem.mp hab0
    have hna : -a ∈ P := by
      have : b + (-(a + b)) ∈ P := hP.add_mem hb hab_support.2
      simpa [add_comm, add_left_comm, add_assoc] using this
    have ha_support : a ∈ coneSupport P hP htotal := ⟨ha, hna⟩
    rw [← hax]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha_support

@[simp]
theorem mem_quotientCone_mk {P : Set R} {hP : IsSquareCone P}
    {htotal : ∀ x, x ∈ P ∨ -x ∈ P} {a : R} :
    Ideal.Quotient.mk (coneSupport P hP htotal) a ∈ quotientCone P hP htotal ↔ a ∈ P := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have hsub : b - a ∈ coneSupport P hP htotal :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem b a).mp hba
    have : a = b + (-(b - a)) := by ring
    rw [this]
    exact hP.add_mem hb hsub.2
  · intro ha
    exact ⟨a, ha, rfl⟩

instance quotientCone_hasMemOrNegMem (P : Set R) (hP : IsSquareCone P)
    (htotal : ∀ x, x ∈ P ∨ -x ∈ P) :
    HasMemOrNegMem (quotientCone P hP htotal) where
  mem_or_neg_mem := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rcases htotal a with ha | hna
    · exact Or.inl (mem_quotientCone_mk.mpr ha)
    · exact Or.inr (by simpa using mem_quotientCone_mk.mpr hna)

/-- The nonnegative fractions over a linearly ordered domain, expressed without choosing
numerator and denominator functions. -/
def fractionCone (A : Type u) [CommRing A] [IsDomain A] [LinearOrder A]
    [IsStrictOrderedRing A] : RingCone (FractionRing A) where
  carrier := {z | ∃ a b : A, b ≠ 0 ∧
    algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b = z ∧ 0 ≤ a * b}
  zero_mem' := ⟨0, 1, one_ne_zero, by simp⟩
  one_mem' := ⟨1, 1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, habx, hab⟩ ⟨c, d, hd, hcdy, hcd⟩
    refine ⟨a * d + c * b, b * d, mul_ne_zero hb hd, ?_, ?_⟩
    · rw [← habx, ← hcdy]
      have hb' : algebraMap A (FractionRing A) b ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
      have hd' : algebraMap A (FractionRing A) d ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.mpr hd)
      push_cast
      field_simp [hb', hd']
    · have h1 : 0 ≤ (a * b) * d ^ 2 := mul_nonneg hab (sq_nonneg d)
      have h2 : 0 ≤ (c * d) * b ^ 2 := mul_nonneg hcd (sq_nonneg b)
      calc
        0 ≤ (a * b) * d ^ 2 + (c * d) * b ^ 2 := add_nonneg h1 h2
        _ = (a * d + c * b) * (b * d) := by ring
  mul_mem' := by
    rintro x y ⟨a, b, hb, habx, hab⟩ ⟨c, d, hd, hcdy, hcd⟩
    refine ⟨a * c, b * d, mul_ne_zero hb hd, ?_, ?_⟩
    · rw [← habx, ← hcdy]
      push_cast
      field_simp
    · calc
        0 ≤ (a * b) * (c * d) := mul_nonneg hab hcd
        _ = (a * c) * (b * d) := by ring
  eq_zero_of_mem_of_neg_mem' := by
    rintro z ⟨a, b, hb, habz, hab⟩ ⟨c, d, hd, hcdz, hcd⟩
    have hb' : algebraMap A (FractionRing A) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hb)
    have hd' : algebraMap A (FractionRing A) d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.mpr hd)
    have heq :
        algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b =
          -(algebraMap A (FractionRing A) c / algebraMap A (FractionRing A) d) := by
      rw [habz, hcdz]
      simp
    have hcross : a * d = -(c * b) := by
      apply IsFractionRing.injective A (FractionRing A)
      push_cast
      field_simp [hb', hd'] at heq
      simpa [mul_comm, mul_left_comm, mul_assoc] using heq
    have hnonneg : 0 ≤ (a * b) * d ^ 2 := mul_nonneg hab (sq_nonneg d)
    have hnonpos : (a * b) * d ^ 2 ≤ 0 := by
      have h := mul_nonneg hcd (sq_nonneg b)
      have hid : (a * b) * d ^ 2 = -((c * d) * b ^ 2) := by
        calc
          (a * b) * d ^ 2 = (a * d) * (b * d) := by ring
          _ = (-(c * b)) * (b * d) := by rw [hcross]
          _ = -((c * d) * b ^ 2) := by ring
      rw [hid]
      exact neg_nonpos.mpr h
    have hzero : (a * b) * d ^ 2 = 0 := le_antisymm hnonpos hnonneg
    have ha : a = 0 := by
      rcases mul_eq_zero.mp hzero with hab0 | hd20
      · exact (mul_eq_zero.mp hab0).resolve_right hb
      · exact False.elim (hd (eq_zero_of_pow_eq_zero hd20))
    rw [← habz, ha]
    simp

instance fractionCone_hasMemOrNegMem (A : Type u) [CommRing A] [IsDomain A]
    [LinearOrder A] [IsStrictOrderedRing A] : HasMemOrNegMem (fractionCone A) where
  mem_or_neg_mem := by
    intro z
    obtain ⟨a, b, hb, habz⟩ := IsFractionRing.div_surjective (A := A) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    rcases le_total 0 (a * b) with hab | hab
    · exact Or.inl ⟨a, b, hb0, habz, hab⟩
    · refine Or.inr ⟨-a, b, hb0, ?_, ?_⟩
      · rw [map_neg, neg_div, habz]
      · simpa using neg_nonneg.mpr hab

/-- Data produced by separation of a proper square cone. -/
structure OrderedFieldSeparator (C : Set R) where
  FieldType : Type u
  field : Field FieldType
  order : LinearOrder FieldType
  strictOrderedRing : @IsStrictOrderedRing FieldType field.toSemiring order.toPartialOrder
  map : R →+* FieldType
  nonneg : ∀ {x}, x ∈ C → @LE.le FieldType order.toLE 0 (map x)

/-- Every proper square cone maps to the nonnegative cone of a linearly ordered field. -/
theorem exists_orderedFieldSeparator {C : Set R} (hC : IsProperSquareCone C) :
    Nonempty (OrderedFieldSeparator C) := by
  classical
  obtain ⟨P, hCP, hmax⟩ := exists_maximal_isProperSquareCone hC
  let hP : IsSquareCone P := hmax.prop.1.1
  let htotal : ∀ x, x ∈ P ∨ -x ∈ P := maximalProperCone_total hmax
  let I : Ideal R := coneSupport P hP htotal
  let D := R ⧸ I
  let qC : RingCone D := quotientCone P hP htotal
  letI hprime : I.IsPrime := maximalProperCone_support_isPrime hmax
  letI : LinearOrder D := LinearOrder.mkOfAddGroupCone qC
  letI : IsOrderedRing D := IsOrderedRing.mkOfCone qC
  let fC : RingCone (FractionRing D) := fractionCone D
  letI : LinearOrder (FractionRing D) := LinearOrder.mkOfAddGroupCone fC
  letI : IsOrderedRing (FractionRing D) := IsOrderedRing.mkOfCone fC
  let φ : R →+* FractionRing D :=
    (algebraMap D (FractionRing D)).comp (Ideal.Quotient.mk I)
  refine ⟨⟨FractionRing D, inferInstance, inferInstance, inferInstance, φ, ?_⟩⟩
  intro x hx
  rw [PartialOrder.mkOfAddGroupCone_le_iff]
  simp only [sub_zero]
  refine ⟨Ideal.Quotient.mk I x, 1, one_ne_zero, ?_, ?_⟩
  · simp only [map_one, div_one]
    exact rfl
  · rw [mul_one, PartialOrder.mkOfAddGroupCone_le_iff]
    simp only [sub_zero]
    exact mem_quotientCone_mk.mpr (hCP hx)

end OptimalConvergenceRates.KrivineStengle

end
