/-
  Algebra of the order induced by an untruncated quadratic module.
-/
import OptimalConvergenceRates.GeneralArchimedean.ArchimedeanEnvelopeDegree

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.GeneralArchimedean

variable {n m : ℕ}


theorem totalDegree_finset_prod_le_card_mul
    {ι : Type*} (s : Finset ι)
    (p : ι → MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hdegree : ∀ i ∈ s, (p i).totalDegree ≤ d) :
    (∏ i ∈ s, p i).totalDegree ≤ s.card * d := by
  classical
  calc
    (∏ i ∈ s, p i).totalDegree ≤
        ∑ i ∈ s, (p i).totalDegree :=
      MvPolynomial.totalDegree_finset_prod s p
    _ ≤ ∑ _i ∈ s, d :=
      Finset.sum_le_sum fun i hi => hdegree i hi
    _ = s.card * d := by simp

/-- The preorder induced by a quadratic module: `p ≤[M] q` means `q - p ∈ M`. -/
def ModuleLE (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p q : MvPolynomial (Fin n) ℝ) : Prop :=
  QuadraticModuleMem g (q - p)

namespace ModuleLE

theorem refl (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) : ModuleLE g p p := by
  have hz := QuadraticModuleMem.of_isSOS g IsSOS_zero
  simpa [ModuleLE] using hz

theorem trans {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q r : MvPolynomial (Fin n) ℝ}
    (hpq : ModuleLE g p q) (hqr : ModuleLE g q r) :
    ModuleLE g p r := by
  have hsum := hpq.add hqr
  simpa [ModuleLE] using hsum

theorem add {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q u v : MvPolynomial (Fin n) ℝ}
    (hpq : ModuleLE g p q) (huv : ModuleLE g u v) :
    ModuleLE g (p + u) (q + v) := by
  change QuadraticModuleMem g (q - p) at hpq
  change QuadraticModuleMem g (v - u) at huv
  change QuadraticModuleMem g ((q + v) - (p + u))
  have hsum := QuadraticModuleMem.add hpq huv
  convert hsum using 1
  ring

/-- Finite sums preserve the module order. -/
theorem sum {ι : Type*} {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι)
    (p q : ι → MvPolynomial (Fin n) ℝ)
    (hle : ∀ i ∈ s, ModuleLE g (p i) (q i)) :
    ModuleLE g (∑ i ∈ s, p i) (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ModuleLE.refl g (0 : MvPolynomial (Fin n) ℝ)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact ModuleLE.add (hle a (Finset.mem_insert_self a s))
        (ih fun i hi => hle i (Finset.mem_insert_of_mem hi))

theorem sos_mul_left {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q s : MvPolynomial (Fin n) ℝ}
    (hs : IsSOS s) (hpq : ModuleLE g p q) :
    ModuleLE g (s * p) (s * q) := by
  change QuadraticModuleMem g (q - p) at hpq
  change QuadraticModuleMem g (s * q - s * p)
  have hmul := QuadraticModuleMem.sos_mul hs hpq
  convert hmul using 1
  ring

theorem sos_mul_right {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q s : MvPolynomial (Fin n) ℝ}
    (hs : IsSOS s) (hpq : ModuleLE g p q) :
    ModuleLE g (p * s) (q * s) := by
  simpa [mul_comm] using sos_mul_left hs hpq

/-- Multiplication is monotone when the two multipliers used in the
telescoping identity are SOS. -/
theorem mul {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q u v : MvPolynomial (Fin n) ℝ}
    (hp : IsSOS p) (hv : IsSOS v)
    (hpq : ModuleLE g p q) (huv : ModuleLE g u v) :
    ModuleLE g (p * u) (q * v) := by
  have h₁ := sos_mul_left hv hpq
  have h₂ := sos_mul_left hp huv
  have hsum := ModuleLE.add h₁ h₂
  change QuadraticModuleMem g ((v * q + p * v) - (v * p + p * u)) at hsum
  change QuadraticModuleMem g (q * v - p * u)
  convert hsum using 1
  ring

theorem nonneg_constant {g : Fin m → MvPolynomial (Fin n) ℝ}
    {c : ℝ} (hc : 0 ≤ c) : ModuleLE g 0 (C c) := by
  change QuadraticModuleMem g (C c - 0)
  exact ⟨0, by simpa using genQuadraticModule_C_nonneg g hc⟩

theorem constant {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a b : ℝ} (hab : a ≤ b) :
    ModuleLE g (C a) (C b) := by
  change QuadraticModuleMem g (C b - C a)
  have h := nonneg_constant (g := g) (sub_nonneg.mpr hab)
  change QuadraticModuleMem g (C (b - a) - 0) at h
  simpa [map_sub] using h

theorem sos_one :
    IsSOS (1 : MvPolynomial (Fin n) ℝ) := by
  simpa using IsSOS_C_nonneg (n := n) 1 zero_le_one

/-- Finite products preserve module order when the lower and upper factors
used by the telescoping argument are sums of squares. -/
theorem prod {ι : Type*}
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι)
    (p q : ι → MvPolynomial (Fin n) ℝ)
    (hp : ∀ i ∈ s, IsSOS (p i))
    (hq : ∀ i ∈ s, IsSOS (q i))
    (hle : ∀ i ∈ s, ModuleLE g (p i) (q i)) :
    ModuleLE g (∏ i ∈ s, p i) (∏ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ModuleLE.refl g (1 : MvPolynomial (Fin n) ℝ)
  | @insert a s ha ih =>
      have htail := ih
        (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi => hq i (Finset.mem_insert_of_mem hi))
        (fun i hi => hle i (Finset.mem_insert_of_mem hi))
      have hmul := ModuleLE.mul
        (hp a (Finset.mem_insert_self a s))
        (IsSOS_finset_prod fun i hi =>
          hq i (Finset.mem_insert_of_mem hi))
        (hle a (Finset.mem_insert_self a s)) htail
      simpa [Finset.prod_insert, ha] using hmul

/-- If every SOS factor is above one in module order, so is their product. -/
theorem one_le_prod {ι : Type*}
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (q : ι → MvPolynomial (Fin n) ℝ)
    (hq : ∀ i ∈ s, IsSOS (q i))
    (hle : ∀ i ∈ s, ModuleLE g 1 (q i)) :
    ModuleLE g 1 (∏ i ∈ s, q i) := by
  have hone : ∀ i ∈ s,
      IsSOS (1 : MvPolynomial (Fin n) ℝ) := fun _ _ => sos_one
  simpa using ModuleLE.prod s
    (fun _ => (1 : MvPolynomial (Fin n) ℝ)) q hone hq hle

end ModuleLE

/-- Degree-indexed module order.  This is the quantitative counterpart of
`ModuleLE`; its index bounds the complete certificate terms of the
difference. -/
def ModuleLEAt (g : Fin m → MvPolynomial (Fin n) ℝ) (r : ℕ)
    (p q : MvPolynomial (Fin n) ℝ) : Prop :=
  q - p ∈ GenQuadraticModule g r

namespace ModuleLEAt

theorem toModuleLE {g : Fin m → MvPolynomial (Fin n) ℝ} {r : ℕ}
    {p q : MvPolynomial (Fin n) ℝ} (h : ModuleLEAt g r p q) :
    ModuleLE g p q :=
  ⟨r, h⟩

theorem mono {g : Fin m → MvPolynomial (Fin n) ℝ} {r s : ℕ}
    {p q : MvPolynomial (Fin n) ℝ} (hrs : r ≤ s)
    (h : ModuleLEAt g r p q) :
    ModuleLEAt g s p q :=
  GenQuadraticModule_mono hrs h

theorem refl (g : Fin m → MvPolynomial (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    ModuleLEAt g 0 p p := by
  change p - p ∈ GenQuadraticModule g 0
  simpa using genQuadraticModule_zero g

theorem add {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q u v : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (hpq : ModuleLEAt g r p q) (huv : ModuleLEAt g s u v) :
    ModuleLEAt g (max r s) (p + u) (q + v) := by
  have hpq' := hpq.mono (le_max_left r s)
  have huv' := huv.mono (le_max_right r s)
  have hsum := GenQuadraticModule_add hpq' huv'
  change (q + v) - (p + u) ∈ GenQuadraticModule g (max r s)
  convert hsum using 1
  ring

theorem trans {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q u : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (hpq : ModuleLEAt g r p q) (hqu : ModuleLEAt g s q u) :
    ModuleLEAt g (max r s) p u := by
  have hsum := hpq.add hqu
  change u - p ∈ GenQuadraticModule g (max r s)
  change ((q + u) - (p + q)) ∈
    GenQuadraticModule g (max r s) at hsum
  convert hsum using 1
  ring

theorem sos_mul_left {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q a : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (ha : IsSOS a) (hpq : ModuleLEAt g r p q) :
    ModuleLEAt g (r + a.totalDegree) (a * p) (a * q) := by
  have hmul := genQuadraticModule_sos_mul ha hpq
  change a * q - a * p ∈
    GenQuadraticModule g (r + a.totalDegree)
  convert hmul using 1
  ring

theorem sos_mul_right {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q a : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (ha : IsSOS a) (hpq : ModuleLEAt g r p q) :
    ModuleLEAt g (r + a.totalDegree) (p * a) (q * a) := by
  simpa [mul_comm] using hpq.sos_mul_left ha

theorem mul {g : Fin m → MvPolynomial (Fin n) ℝ}
    {p q u v : MvPolynomial (Fin n) ℝ} {r s : ℕ}
    (hp : IsSOS p) (hv : IsSOS v)
    (hpq : ModuleLEAt g r p q) (huv : ModuleLEAt g s u v) :
    ModuleLEAt g (max (r + v.totalDegree) (s + p.totalDegree))
      (p * u) (q * v) := by
  have h₁ := hpq.sos_mul_left hv
  have h₂ := huv.sos_mul_left hp
  have hsum := h₁.add h₂
  change q * v - p * u ∈ GenQuadraticModule g
    (max (r + v.totalDegree) (s + p.totalDegree))
  change ((v * q + p * v) - (v * p + p * u)) ∈
    GenQuadraticModule g
      (max (r + v.totalDegree) (s + p.totalDegree))
    at hsum
  convert hsum using 1
  ring

theorem nonneg_constant {g : Fin m → MvPolynomial (Fin n) ℝ}
    {c : ℝ} (hc : 0 ≤ c) :
    ModuleLEAt g 0 0 (C c) := by
  change C c - 0 ∈ GenQuadraticModule g 0
  simpa using genQuadraticModule_C_nonneg g hc

theorem constant {g : Fin m → MvPolynomial (Fin n) ℝ}
    {a b : ℝ} (hab : a ≤ b) :
    ModuleLEAt g 0 (C a) (C b) := by
  change C b - C a ∈ GenQuadraticModule g 0
  convert genQuadraticModule_C_nonneg g (sub_nonneg.mpr hab) using 1
  rw [map_sub]

/-- Finite sums preserve a common truncation order. -/
theorem sum {ι : Type*} {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (p q : ι → MvPolynomial (Fin n) ℝ) {r : ℕ}
    (hle : ∀ i ∈ s, ModuleLEAt g r (p i) (q i)) :
    ModuleLEAt g r (∑ i ∈ s, p i) (∑ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (ModuleLEAt.refl g (0 : MvPolynomial (Fin n) ℝ)).mono
        (Nat.zero_le r)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      simpa using (ModuleLEAt.add
        (hle a (Finset.mem_insert_self a s))
        (ih fun i hi => hle i (Finset.mem_insert_of_mem hi)))

/-- Finite products preserve module order at a coarse explicit order.  The
factor degree bound is intentionally symmetric: this makes the result easy
to reuse in the preordering-to-module conversion. -/
theorem prod {ι : Type*} {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (p q : ι → MvPolynomial (Fin n) ℝ) (r d : ℕ)
    (hp : ∀ i ∈ s, IsSOS (p i))
    (hq : ∀ i ∈ s, IsSOS (q i))
    (hpdeg : ∀ i ∈ s, (p i).totalDegree ≤ d)
    (hqdeg : ∀ i ∈ s, (q i).totalDegree ≤ d)
    (hle : ∀ i ∈ s, ModuleLEAt g r (p i) (q i)) :
    ModuleLEAt g (s.card * (r + d))
      (∏ i ∈ s, p i) (∏ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ModuleLEAt.refl g (1 : MvPolynomial (Fin n) ℝ)
  | @insert a s ha ih =>
      have htail := ih
        (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi => hq i (Finset.mem_insert_of_mem hi))
        (fun i hi => hpdeg i (Finset.mem_insert_of_mem hi))
        (fun i hi => hqdeg i (Finset.mem_insert_of_mem hi))
        (fun i hi => hle i (Finset.mem_insert_of_mem hi))
      have hqtail :
          (∏ i ∈ s, q i).totalDegree ≤ s.card * d := by
        calc
          (∏ i ∈ s, q i).totalDegree
              ≤ ∑ i ∈ s, (q i).totalDegree :=
                MvPolynomial.totalDegree_finset_prod s q
          _ ≤ ∑ _i ∈ s, d :=
                Finset.sum_le_sum fun i hi =>
                  hqdeg i (Finset.mem_insert_of_mem hi)
          _ = s.card * d := by simp
      have hmul := ModuleLEAt.mul
        (hp a (Finset.mem_insert_self a s))
        (IsSOS_finset_prod fun i hi =>
          hq i (Finset.mem_insert_of_mem hi))
        (hle a (Finset.mem_insert_self a s)) htail
      rw [Finset.card_insert_of_notMem ha]
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      apply hmul.mono
      apply max_le
      · have haOrder : r + (∏ i ∈ s, q i).totalDegree ≤
            (s.card + 1) * (r + d) := by
          calc
            r + (∏ i ∈ s, q i).totalDegree
                ≤ r + s.card * d := Nat.add_le_add_left hqtail r
            _ ≤ r + s.card * d + (s.card * r + d) :=
              Nat.le_add_right _ _
            _ = (s.card + 1) * (r + d) := by ring
        simpa [Nat.add_comm] using haOrder
      · have hpa := hpdeg a (Finset.mem_insert_self a s)
        calc
          s.card * (r + d) + (p a).totalDegree
              ≤ s.card * (r + d) + d := Nat.add_le_add_left hpa _
          _ ≤ s.card * (r + d) + (r + d) :=
            Nat.add_le_add_left (Nat.le_add_left d r) _
          _ = (s.card + 1) * (r + d) := by ring

/-- If each SOS factor is above one at order `r` and has degree at most `d`,
then its product is above one at the corresponding product order. -/
theorem one_le_prod {ι : Type*}
    {g : Fin m → MvPolynomial (Fin n) ℝ}
    (s : Finset ι) (q : ι → MvPolynomial (Fin n) ℝ) (r d : ℕ)
    (hq : ∀ i ∈ s, IsSOS (q i))
    (hqdeg : ∀ i ∈ s, (q i).totalDegree ≤ d)
    (hle : ∀ i ∈ s, ModuleLEAt g r 1 (q i)) :
    ModuleLEAt g (s.card * (r + d)) 1 (∏ i ∈ s, q i) := by
  have hone : ∀ i ∈ s,
      IsSOS (1 : MvPolynomial (Fin n) ℝ) := fun _ _ => ModuleLE.sos_one
  have honeDegree : ∀ i ∈ s,
      (1 : MvPolynomial (Fin n) ℝ).totalDegree ≤ d := by
    intro i hi
    simp
  simpa using ModuleLEAt.prod s
    (fun _ => (1 : MvPolynomial (Fin n) ℝ)) q r d
    hone hq honeDegree hqdeg hle



end ModuleLEAt
end OptimalConvergenceRates.GeneralArchimedean

end
