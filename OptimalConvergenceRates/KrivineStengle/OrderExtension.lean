/-
  OptimalConvergenceRates/KrivineStengle/OrderExtension.lean

  Extending an ordered field structure through a field extension.
-/
import OptimalConvergenceRates.KrivineStengle.OrderedFractionField
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Ring.InjSurj

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u v

variable (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable (L : Type v) [Field L] [Algebra F L]

/-- The least square cone in `L` containing the images of all nonnegative elements of `F`.
This impredicative presentation is equivalent to the finite weighted sums of squares used on
paper, and is particularly convenient for the order-extension criterion. -/
def weightedSquareCone : Set L :=
  {x | ∀ P : Set L, IsSquareCone P →
    (∀ c : F, 0 ≤ c → algebraMap F L c ∈ P) → x ∈ P}

theorem weightedSquareCone_isSquareCone : IsSquareCone (weightedSquareCone F L) where
  zero_mem := by
    intro P hP hbase
    exact hP.zero_mem
  one_mem := by
    intro P hP hbase
    exact hP.one_mem
  add_mem := by
    intro x y hx hy P hP hbase
    exact hP.add_mem (hx P hP hbase) (hy P hP hbase)
  mul_mem := by
    intro x y hx hy P hP hbase
    exact hP.mul_mem (hx P hP hbase) (hy P hP hbase)
  sq_mem := by
    intro x P hP hbase
    exact hP.sq_mem x

theorem algebraMap_mem_weightedSquareCone {c : F} (hc : 0 ≤ c) :
    algebraMap F L c ∈ weightedSquareCone F L := by
  intro P hP hbase
  exact hbase c hc

/-- A choice of ordered-field structure on `L` for which the given `F`-algebra map is
monotone. The order is data rather than an instance so several extensions can coexist. -/
structure OrderedExtensionData where
  order : LinearOrder L
  strictOrderedRing : @IsStrictOrderedRing L _ order.toPartialOrder
  algebraMap_monotone :
    ∀ {a b : F}, a ≤ b → @LE.le L order.toLE (algebraMap F L a) (algebraMap F L b)

private theorem nonnegative_isSquareCone
    [LinearOrder L] [IsStrictOrderedRing L] : IsSquareCone {x : L | 0 ≤ x} where
  zero_mem := le_rfl
  one_mem := zero_le_one
  add_mem := add_nonneg
  mul_mem := mul_nonneg
  sq_mem := sq_nonneg

/-- If the order already extends, the weighted-square cone is proper. -/
theorem weightedSquareCone_isProper_of_orderedExtension
    (E : OrderedExtensionData F L) :
    IsProperSquareCone (weightedSquareCone F L) := by
  letI : LinearOrder L := E.order
  letI : IsStrictOrderedRing L := E.strictOrderedRing
  refine ⟨weightedSquareCone_isSquareCone F L, ?_⟩
  intro hneg
  have hbase : ∀ c : F, 0 ≤ c → 0 ≤ algebraMap F L c := by
    intro c hc
    simpa only [map_zero] using E.algebraMap_monotone hc
  have : (0 : L) ≤ -1 :=
    hneg {x : L | 0 ≤ x} (nonnegative_isSquareCone (L := L)) hbase
  exact (not_le_of_gt (neg_one_lt_zero : (-1 : L) < 0)) this

/-- Pull the separator order back along an injective field homomorphism. -/
private def orderedExtensionOfSeparator
    (S : OrderedFieldSeparator (weightedSquareCone F L)) : OrderedExtensionData F L := by
  letI : Field S.FieldType := S.field
  letI : LinearOrder S.FieldType := S.order
  letI : IsStrictOrderedRing S.FieldType := S.strictOrderedRing
  have hinj : Function.Injective S.map := S.map.injective
  let orderL : LinearOrder L := LinearOrder.lift' S.map hinj
  letI : LinearOrder L := orderL
  have hle (x y : L) : S.map x ≤ S.map y ↔ x ≤ y := Iff.rfl
  have hlt (x y : L) : S.map x < S.map y ↔ x < y := Iff.rfl
  let orderedL : IsStrictOrderedRing L :=
    Function.Injective.isStrictOrderedRing S.map (map_zero S.map) (map_one S.map)
      (map_add S.map) (map_mul S.map) (fun {x y} ↦ hle x y) (fun {x y} ↦ hlt x y)
  refine ⟨orderL, orderedL, ?_⟩
  intro a b hab
  rw [← hle (algebraMap F L a) (algebraMap F L b)]
  rw [← sub_nonneg]
  rw [← map_sub, ← map_sub]
  exact S.nonneg (algebraMap_mem_weightedSquareCone F L (sub_nonneg.mpr hab))

/-- The order-extension criterion: an order on `F` extends through the given field extension
exactly when its weighted-square cone does not contain `-1`. -/
theorem nonempty_orderedExtensionData_iff :
    Nonempty (OrderedExtensionData F L) ↔ -1 ∉ weightedSquareCone F L := by
  constructor
  · rintro ⟨E⟩
    exact (weightedSquareCone_isProper_of_orderedExtension F L E).2
  · intro hproper
    obtain ⟨S⟩ := exists_orderedFieldSeparator
      (C := weightedSquareCone F L) ⟨weightedSquareCone_isSquareCone F L, hproper⟩
    exact ⟨orderedExtensionOfSeparator F L S⟩

end OptimalConvergenceRates.KrivineStengle

end

noncomputable section

namespace OptimalConvergenceRates.KrivineStengle

universe u v w

variable (F : Type u) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {L : Type v} [Field L] [Algebra F L]
variable {K : Type w} [Field K] [Algebra F K]

/-- Pull an extending order back along an injective algebra homomorphism. -/
def OrderedExtensionData.pullback (E : OrderedExtensionData F L) (i : K →ₐ[F] L) :
    OrderedExtensionData F K := by
  letI : LinearOrder L := E.order
  letI : IsStrictOrderedRing L := E.strictOrderedRing
  let orderK : LinearOrder K := LinearOrder.lift' i i.injective
  letI : LinearOrder K := orderK
  have hle (x y : K) : i x ≤ i y ↔ x ≤ y := Iff.rfl
  have hlt (x y : K) : i x < i y ↔ x < y := Iff.rfl
  let orderedK : IsStrictOrderedRing K :=
    Function.Injective.isStrictOrderedRing i i.map_zero i.map_one i.map_add i.map_mul
      (fun {x y} ↦ hle x y) (fun {x y} ↦ hlt x y)
  refine ⟨orderK, orderedK, ?_⟩
  intro a b hab
  rw [← hle (algebraMap F K a) (algebraMap F K b)]
  simpa only [i.commutes] using E.algebraMap_monotone hab

/-- Transport an extending order forward across an algebra equivalence. -/
def OrderedExtensionData.transport (E : OrderedExtensionData F L) (e : L ≃ₐ[F] K) :
    OrderedExtensionData F K :=
  E.pullback F e.symm.toAlgHom

end OptimalConvergenceRates.KrivineStengle

end
