/-
  OptimalConvergenceRates/BasicNotions/BoxCones.lean

  Box generators 1 - x_i^2, box preorderings, box quadratic modules, and their basic API.
-/
import OptimalConvergenceRates.BasicNotions.SOS
import Mathlib.Data.Finset.Powerset

open MvPolynomial Finset

noncomputable section

namespace OptimalConvergenceRates

variable {n N : ℕ}

/-! ## Semialgebraic generators -/

/-- The i-th semialgebraic generator g_i(x) = 1 - x_i² -/
def BoxSemialgebraicGenerator (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  1 - (X i) ^ 2

/-- Product of generators: g_J = ∏_{j ∈ J} g_j -/
def BoxSemialgebraicGeneratorProd (J : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∏ j ∈ J, BoxSemialgebraicGenerator j

theorem BoxSemialgebraicGenerator_eval (i : Fin n) (x : Fin n → ℝ) :
    MvPolynomial.eval x (BoxSemialgebraicGenerator i) = 1 - (x i) ^ 2 := by
  simp [BoxSemialgebraicGenerator, map_sub, map_one, map_pow, eval_X]

theorem BoxSemialgebraicGenerator_nonneg_on_hypercube (i : Fin n) (x : Fin n → ℝ)
    (hx : x ∈ Hypercube n) :
    0 ≤ MvPolynomial.eval x (BoxSemialgebraicGenerator i) := by
  rw [BoxSemialgebraicGenerator_eval]
  have hi := ((Hypercube_mem_iff x).mp hx i)
  nlinarith [hi.1, hi.2, sq_abs (x i)]

theorem BoxSemialgebraicGeneratorProd_nonneg_on_hypercube (J : Finset (Fin n))
    (x : Fin n → ℝ) (hx : x ∈ Hypercube n) :
    0 ≤ MvPolynomial.eval x (BoxSemialgebraicGeneratorProd J) := by
  unfold BoxSemialgebraicGeneratorProd
  rw [map_prod]
  exact Finset.prod_nonneg (fun j _ => BoxSemialgebraicGenerator_nonneg_on_hypercube j x hx)

theorem BoxSemialgebraicGeneratorProd_empty :
    BoxSemialgebraicGeneratorProd (∅ : Finset (Fin n)) = 1 := by
  unfold BoxSemialgebraicGeneratorProd
  exact Finset.prod_empty


/-! ## Univariate box preordering -/

/-- Membership in the univariate preordering Q([-1,1])_r:
    p ∈ Q([-1,1])_r iff p = σ₀ + σ₁·(1-x²) with σ₀, σ₁ SOS
    and deg(σ₀), deg(σ₁·(1-x²)) ≤ r -/
def BoxUniPreordering (r : ℕ) : Set (Polynomial ℝ) :=
  { p | ∃ (σ₀ σ₁ : Polynomial ℝ),
    IsSOSUni σ₀ ∧ IsSOSUni σ₁ ∧
    σ₀.natDegree ≤ r ∧ (σ₁ * (1 - Polynomial.X ^ 2)).natDegree ≤ r ∧
    p = σ₀ + σ₁ * (1 - Polynomial.X ^ 2) }

/-! ## The truncated preordering BoxPreo(B^n)_r -/

/-- Membership in the truncated preordering BoxPreo(B^n)_r.
    p ∈ BoxPreo(B^n)_r iff p = ∑_{J ⊆ [n]} σ_J · g_J where each σ_J is SOS
    and deg(σ_J · g_J) ≤ r. -/
def BoxPreordering (n : ℕ) (r : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  { p | ∃ (σ : Finset (Fin n) → MvPolynomial (Fin n) ℝ),
    (∀ J, IsSOS (σ J)) ∧
    (∀ J, (σ J * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) ∧
    p = ∑ J ∈ Finset.univ.powerset, σ J * BoxSemialgebraicGeneratorProd J }

theorem box_preordering_mono {r s : ℕ} (hrs : r ≤ s) :
    BoxPreordering n r ⊆ BoxPreordering n s := by
  intro p ⟨σ, hsos, hdeg, hsum⟩
  exact ⟨σ, hsos, fun J => le_trans (hdeg J) hrs, hsum⟩

theorem box_preordering_subset_nonneg :
    BoxPreordering n r ⊆ { p | IsNonnegOn p (Hypercube n) } := by
  intro p ⟨σ, hsos, _, hsum⟩ x hx
  rw [hsum, map_sum]
  apply Finset.sum_nonneg
  intro J _
  rw [map_mul]
  exact mul_nonneg
    (IsSOS_nonneg _ (hsos J) x (Set.mem_univ _))
    (BoxSemialgebraicGeneratorProd_nonneg_on_hypercube J x hx)

/-! ## BoxPreordering closure properties -/

/-- The BoxPreordering is closed under addition -/
theorem BoxPreordering_add {p q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : p ∈ BoxPreordering n r) (hq : q ∈ BoxPreordering n r) :
    p + q ∈ BoxPreordering n r := by
  obtain ⟨σ_p, hsos_p, hdeg_p, hsum_p⟩ := hp
  obtain ⟨σ_q, hsos_q, hdeg_q, hsum_q⟩ := hq
  refine ⟨fun J => σ_p J + σ_q J, ?_, ?_, ?_⟩
  · intro J; exact IsSOS_add (hsos_p J) (hsos_q J)
  · intro J
    calc ((σ_p J + σ_q J) * BoxSemialgebraicGeneratorProd J).totalDegree
        = (σ_p J * BoxSemialgebraicGeneratorProd J +
           σ_q J * BoxSemialgebraicGeneratorProd J).totalDegree := by ring_nf
      _ ≤ max (σ_p J * BoxSemialgebraicGeneratorProd J).totalDegree
              (σ_q J * BoxSemialgebraicGeneratorProd J).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ r := max_le (hdeg_p J) (hdeg_q J)
  · rw [hsum_p, hsum_q, ← Finset.sum_add_distrib]
    congr 1; ext J; ring_nf

/-- The BoxPreordering is closed under nonneg scalar multiplication -/
theorem BoxPreordering_nonneg_scale {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (hp : p ∈ BoxPreordering n r) :
    MvPolynomial.C c * p ∈ BoxPreordering n r := by
  obtain ⟨σ, hsos, hdeg, hsum⟩ := hp
  refine ⟨fun J => MvPolynomial.C c * σ J, ?_, ?_, ?_⟩
  · intro J; exact IsSOS_nonneg_scale (hsos J) c hc
  · intro J
    calc (MvPolynomial.C c * σ J * BoxSemialgebraicGeneratorProd J).totalDegree
        = (MvPolynomial.C c * (σ J * BoxSemialgebraicGeneratorProd J)).totalDegree := by ring_nf
      _ ≤ (MvPolynomial.C c).totalDegree +
           (σ J * BoxSemialgebraicGeneratorProd J).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = (σ J * BoxSemialgebraicGeneratorProd J).totalDegree := by
          rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ r := hdeg J
  · rw [hsum, Finset.mul_sum]; congr 1; ext J; ring_nf

/-- The BoxPreordering is closed under finite sums -/
theorem BoxPreordering_sum {ι : Type*} {s : Finset ι} {r : ℕ}
    {f : ι → MvPolynomial (Fin n) ℝ} (hf : ∀ i ∈ s, f i ∈ BoxPreordering n r) :
    ∑ i ∈ s, f i ∈ BoxPreordering n r := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    -- 0 ∈ BoxPreordering: take all σ_J = 0
    refine ⟨0, fun J => ⟨0, Fin.elim0, by simp⟩, fun J => by simp, ?_⟩
    simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact BoxPreordering_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- A positive constant C(c) is in the BoxPreordering at any level -/
theorem positive_const_in_box_preordering {c : ℝ} (hc : 0 < c) (n r : ℕ) :
    MvPolynomial.C c ∈ BoxPreordering n r := by
  -- Take σ ∅ = C c, σ J = 0 for J ≠ ∅
  refine ⟨Function.update (0 : Finset (Fin n) → MvPolynomial (Fin n) ℝ) ∅
    (MvPolynomial.C c), ?_, ?_, ?_⟩
  · -- IsSOS for each J
    intro J
    by_cases hJ : J = ∅
    · subst hJ; rw [Function.update_self]
      exact ⟨1, fun _ => MvPolynomial.C (Real.sqrt c), by
        simp only [Fin.sum_univ_one, sq, ← MvPolynomial.C_mul,
          Real.mul_self_sqrt hc.le]⟩
    · rw [Function.update_of_ne hJ, Pi.zero_apply]
      exact ⟨0, Fin.elim0, by simp⟩
  · -- Degree bounds
    intro J
    by_cases hJ : J = ∅
    · subst hJ
      rw [Function.update_self, BoxSemialgebraicGeneratorProd_empty, mul_one,
        MvPolynomial.totalDegree_C]; exact Nat.zero_le _
    · rw [Function.update_of_ne hJ, Pi.zero_apply, zero_mul]
      exact Nat.zero_le _
  · -- Sum equals C c
    rw [Finset.sum_eq_single ∅
      (fun J _ hJ => by rw [Function.update_of_ne hJ, Pi.zero_apply, zero_mul])
      (fun h => absurd (Finset.mem_powerset.mpr (Finset.empty_subset _)) h)]
    rw [Function.update_self, BoxSemialgebraicGeneratorProd_empty, mul_one]

/-! ## Lifting lemmas: univariate → multivariate -/

/-- Lifting univariate SOS to multivariate SOS via embedUnivariate.
    Since embedUnivariate i is a ring hom, ∑ q_j² ↦ ∑ (embed q_j)². -/
theorem IsSOS_of_IsSOSUni (i : Fin n) (p : Polynomial ℝ) (hp : IsSOSUni p) :
    IsSOS (embedUnivariate i p) := by
  obtain ⟨m, q, rfl⟩ := hp
  exact ⟨m, fun j => embedUnivariate i (q j), by
    simp only [map_sum, map_pow]⟩

/-- embedUnivariate i (1 - X²) = BoxSemialgebraicGenerator i -/
theorem embedUnivariate_one_sub_sq (i : Fin n) :
    embedUnivariate i (1 - Polynomial.X ^ 2) = BoxSemialgebraicGenerator i := by
  simp [embedUnivariate, BoxSemialgebraicGenerator,
        Polynomial.aeval_X, map_sub, map_pow, map_one]

/-- BoxSemialgebraicGeneratorProd of a singleton is BoxSemialgebraicGenerator -/
theorem BoxSemialgebraicGeneratorProd_singleton (i : Fin n) :
    BoxSemialgebraicGeneratorProd ({i} : Finset (Fin n)) = BoxSemialgebraicGenerator i := by
  simp [BoxSemialgebraicGeneratorProd]

/-- An SOS polynomial with totalDegree ≤ r times a generator product g_J
    with totalDegree bound is in the BoxPreordering. -/
private theorem IsSOS_mul_generatorProd_in_BoxPreordering (J : Finset (Fin n))
    (σ : MvPolynomial (Fin n) ℝ) (r : ℕ)
    (hsos : IsSOS σ) (hdeg : (σ * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) :
    σ * BoxSemialgebraicGeneratorProd J ∈ BoxPreordering n r := by
  have hJ_mem : J ∈ (Finset.univ : Finset (Fin n)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ J)
  refine ⟨Function.update 0 J σ, ?_, ?_, ?_⟩
  · intro K; by_cases hK : K = J
    · subst hK; rwa [Function.update_self]
    · rw [Function.update_of_ne hK, Pi.zero_apply]; exact ⟨0, Fin.elim0, by simp⟩
  · intro K; by_cases hK : K = J
    · subst hK; rwa [Function.update_self]
    · rw [Function.update_of_ne hK, Pi.zero_apply, zero_mul]; exact Nat.zero_le _
  · rw [Finset.sum_eq_single J
      (fun K _ hK => by rw [Function.update_of_ne hK, Pi.zero_apply, zero_mul])
      (fun h => absurd hJ_mem h)]
    rw [Function.update_self]

/-- Lifting BoxUniPreordering membership to BoxPreordering membership via embedUnivariate.
    If p = σ₀ + σ₁·(1-X²) with σ₀, σ₁ SOS and degree bounds, then
    embed(p) = embed(σ₀) + embed(σ₁)·g_i ∈ BoxPreordering. -/
theorem embedUnivariate_in_BoxPreordering (i : Fin n) (p : Polynomial ℝ) (r : ℕ)
    (hp : p ∈ BoxUniPreordering r) :
    embedUnivariate i p ∈ BoxPreordering n r := by
  obtain ⟨σ₀, σ₁, hsos₀, hsos₁, hdeg₀, hdeg₁, rfl⟩ := hp
  rw [map_add, map_mul, embedUnivariate_one_sub_sq]
  apply BoxPreordering_add
  · -- embed(σ₀) ∈ BoxPreordering n r (as SOS with trivial g_∅ = 1)
    rw [show embedUnivariate i σ₀ = embedUnivariate i σ₀ * BoxSemialgebraicGeneratorProd ∅ from
      by rw [BoxSemialgebraicGeneratorProd_empty, mul_one]]
    apply IsSOS_mul_generatorProd_in_BoxPreordering
    · exact IsSOS_of_IsSOSUni i σ₀ hsos₀
    · rw [BoxSemialgebraicGeneratorProd_empty, mul_one]
      exact le_trans (totalDegree_embedUnivariate i σ₀) hdeg₀
  · -- embed(σ₁) * g_i ∈ BoxPreordering n r
    rw [show embedUnivariate i σ₁ * BoxSemialgebraicGenerator i =
        embedUnivariate i σ₁ * BoxSemialgebraicGeneratorProd {i} from
      by rw [BoxSemialgebraicGeneratorProd_singleton]]
    apply IsSOS_mul_generatorProd_in_BoxPreordering
    · exact IsSOS_of_IsSOSUni i σ₁ hsos₁
    · -- totalDegree(embed(σ₁) * g_{i}) = totalDegree(embed(σ₁ * (1-X²))) ≤ natDegree(σ₁*(1-X²)) ≤ r
      rw [BoxSemialgebraicGeneratorProd_singleton, ← embedUnivariate_one_sub_sq,
          ← map_mul (embedUnivariate i)]
      exact le_trans (totalDegree_embedUnivariate i _) hdeg₁

/-! ## Product of univariate preordering elements in disjoint variables -/

/-- Product of a finset of generators equals BoxSemialgebraicGeneratorProd.
    ∏_{i ∈ J} BoxSemialgebraicGenerator i = BoxSemialgebraicGeneratorProd J -/
private theorem prod_generator_eq (J : Finset (Fin n)) :
    ∏ i ∈ J, BoxSemialgebraicGenerator i = BoxSemialgebraicGeneratorProd J :=
  rfl

/-- Key: the product ∏_{i ∈ J} (embed_i(σ₁ i) * g_i) splits as
    (∏_{i ∈ J} embed_i(σ₁ i)) * BoxSemialgebraicGeneratorProd J -/
private theorem prod_embed_mul_gen
    (σ₁ : Fin n → Polynomial ℝ) (J : Finset (Fin n)) :
    ∏ i ∈ J, (embedUnivariate i (σ₁ i) * BoxSemialgebraicGenerator i) =
    (∏ i ∈ J, embedUnivariate i (σ₁ i)) * BoxSemialgebraicGeneratorProd J := by
  rw [Finset.prod_mul_distrib, prod_generator_eq]

/-- Product of embeddings of univariate preordering elements is in
    the multivariate BoxPreordering.
    If each ps i ∈ BoxUniPreordering r, then ∏ embed_i(ps i) ∈ BoxPreordering n (r * n).

    Proof: Expand each embed_i(ps i) = embed_i(σ₀ i) + embed_i(σ₁ i) · g_i.
    By Finset.prod_add:
      ∏_i (a_i + b_i) = ∑_{t ⊆ [n]} (∏_{i∈t} a_i) · (∏_{i∈[n]\t} b_i)
    Each summand has the form σ_J · g_J where σ_J is SOS
    (product of SOS in disjoint variables) and deg(σ_J · g_J) ≤ r·n. -/
theorem prod_BoxUniPreordering_in_BoxPreordering (n : ℕ)
    (ps : Fin n → Polynomial ℝ) (r : ℕ)
    (h : ∀ i, ps i ∈ BoxUniPreordering r) :
    (∏ i : Fin n, embedUnivariate i (ps i)) ∈ BoxPreordering n (r * n) := by
  -- Extract decompositions: ps i = σ₀ i + σ₁ i * (1 - X²)
  choose σ₀ σ₁ hsos₀ hsos₁ hdeg₀ hdeg₁ hdecomp using h
  -- Set a_i = embed_i(σ₀ i), b_i = embed_i(σ₁ i) * g_i
  set a : Fin n → MvPolynomial (Fin n) ℝ := fun i => embedUnivariate i (σ₀ i)
  set b : Fin n → MvPolynomial (Fin n) ℝ := fun i =>
    embedUnivariate i (σ₁ i) * BoxSemialgebraicGenerator i
  -- Each embed_i(ps i) = a i + b i
  have hab : ∀ i, embedUnivariate i (ps i) = a i + b i := by
    intro i; rw [hdecomp i, map_add, map_mul, embedUnivariate_one_sub_sq]
  simp_rw [hab]
  -- Apply the product-of-sums expansion:
  -- ∏(a+b) = ∑_{t ⊆ univ} (∏_{i∈t} a i) · (∏_{i∈univ\t} b i)
  rw [Finset.prod_add a b Finset.univ]
  -- Each summand (∏_{i∈t} a i) · (∏_{i∈univ\t} b i)
  -- = (∏_{i∈t} embed_i(σ₀ i)) · (∏_{i∈univ\t} embed_i(σ₁ i)) · g_{univ\t}
  -- is a SOS polynomial times a generator product, hence in the BoxPreordering.
  apply BoxPreordering_sum
  intro t ht
  -- Rewrite the b-product: ∏_{i∈univ\t} b_i = (∏ embed_i(σ₁)) * g_{univ\t}
  rw [show ∏ i ∈ Finset.univ \ t, b i =
      (∏ i ∈ Finset.univ \ t, embedUnivariate i (σ₁ i)) *
      BoxSemialgebraicGeneratorProd (Finset.univ \ t)
    from prod_embed_mul_gen σ₁ (Finset.univ \ t)]
  -- Now the summand is (∏_{t} a_i) * (∏_{univ\t} embed σ₁) * g_{univ\t}
  -- = [(∏_t embed σ₀) * (∏_{univ\t} embed σ₁)] * g_{univ\t}
  rw [show (∏ i ∈ t, a i) *
      ((∏ i ∈ Finset.univ \ t, embedUnivariate i (σ₁ i)) *
       BoxSemialgebraicGeneratorProd (Finset.univ \ t)) =
    ((∏ i ∈ t, embedUnivariate i (σ₀ i)) *
     (∏ i ∈ Finset.univ \ t, embedUnivariate i (σ₁ i))) *
    BoxSemialgebraicGeneratorProd (Finset.univ \ t) from by ring]
  apply IsSOS_mul_generatorProd_in_BoxPreordering
  · -- SOS: product of SOS polynomials
    apply IsSOS_mul
    · apply IsSOS_finset_prod
      intro i _; exact IsSOS_of_IsSOSUni i (σ₀ i) (hsos₀ i)
    · apply IsSOS_finset_prod
      intro i _; exact IsSOS_of_IsSOSUni i (σ₁ i) (hsos₁ i)
  · -- Degree bound: totalDegree ≤ r * n
    -- Rewrite: σ_mv * g_J = (∏_t embed σ₀) * (∏_{univ\t} (embed σ₁ * g_i))
    -- and bound totalDegree using product degree bound
    rw [show ((∏ i ∈ t, embedUnivariate i (σ₀ i)) *
        (∏ i ∈ Finset.univ \ t, embedUnivariate i (σ₁ i))) *
        BoxSemialgebraicGeneratorProd (Finset.univ \ t) =
      (∏ i ∈ t, embedUnivariate i (σ₀ i)) *
      ((∏ i ∈ Finset.univ \ t, embedUnivariate i (σ₁ i)) *
        BoxSemialgebraicGeneratorProd (Finset.univ \ t)) from by ring]
    rw [show (∏ i ∈ Finset.univ \ t, embedUnivariate i (σ₁ i)) *
        BoxSemialgebraicGeneratorProd (Finset.univ \ t) =
      ∏ i ∈ Finset.univ \ t,
        (embedUnivariate i (σ₁ i) * BoxSemialgebraicGenerator i) from by
      rw [← prod_embed_mul_gen]]
    -- Now: totalDegree((∏_t embed σ₀) * (∏_{univ\t} (embed σ₁ * g_i)))
    -- ≤ totalDegree(∏_t embed σ₀) + totalDegree(∏_{univ\t} (embed σ₁ * g_i))
    -- ≤ ∑_t totalDegree(embed σ₀_i) + ∑_{univ\t} totalDegree(embed(σ₁_i * (1-X²)))
    -- ≤ ∑_t natDeg(σ₀_i) + ∑_{univ\t} natDeg(σ₁_i * (1-X²))
    -- ≤ ∑_t r + ∑_{univ\t} r = r * n
    -- Bound 1: totalDeg(product) ≤ sum of totalDegs
    have hb1 := MvPolynomial.totalDegree_mul
      (∏ i ∈ t, embedUnivariate i (σ₀ i))
      (∏ i ∈ Finset.univ \ t,
        (embedUnivariate i (σ₁ i) * BoxSemialgebraicGenerator i))
    have hb2a := MvPolynomial.totalDegree_finsetProd
      t (fun i => embedUnivariate i (σ₀ i))
    have hb2b := MvPolynomial.totalDegree_finsetProd
      (Finset.univ \ t) (fun i =>
        embedUnivariate i (σ₁ i) * BoxSemialgebraicGenerator i)
    -- Bound 2: totalDeg(embed p) ≤ natDeg p
    have hb3a : ∑ i ∈ t, (embedUnivariate i (σ₀ i)).totalDegree ≤
        ∑ i ∈ t, r :=
      Finset.sum_le_sum (fun i _ =>
        le_trans (totalDegree_embedUnivariate i (σ₀ i)) (hdeg₀ i))
    have hb3b : ∑ i ∈ Finset.univ \ t,
        (embedUnivariate i (σ₁ i) *
          BoxSemialgebraicGenerator i).totalDegree ≤
        ∑ i ∈ Finset.univ \ t, r :=
      Finset.sum_le_sum (fun i _ => by
        rw [← embedUnivariate_one_sub_sq, ← map_mul]
        exact le_trans (totalDegree_embedUnivariate i _) (hdeg₁ i))
    -- Bound 3: ∑_t r + ∑_{univ\t} r = r * n
    have hb4 : ∑ _ ∈ t, r + ∑ _ ∈ Finset.univ \ t, r = r * n := by
      simp only [Finset.sum_const, smul_eq_mul]
      have h1 : (Finset.univ \ t).card + t.card = n := by
        have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ t)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact this
      nlinarith
    linarith

/-! ## The truncated quadratic module QM(B^n)_r -/

/-- Membership in the truncated quadratic module QM(B^n)_r.
    p ∈ QM(B^n)_r iff p = σ₀ + ∑_i σ_i · g_i where each σ_i is SOS
    and deg(σ₀) ≤ r and deg(σ_i · g_i) ≤ r.
    Unlike the BoxPreordering, we only use individual generators g_i = 1 - x_i²,
    not their products. -/
def BoxQuadraticModule (n : ℕ) (r : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  { p | ∃ (σ₀ : MvPolynomial (Fin n) ℝ) (σ : Fin n → MvPolynomial (Fin n) ℝ),
    IsSOS σ₀ ∧
    (∀ i, IsSOS (σ i)) ∧
    σ₀.totalDegree ≤ r ∧
    (∀ i, (σ i * BoxSemialgebraicGenerator i).totalDegree ≤ r) ∧
    p = σ₀ + ∑ i : Fin n, σ i * BoxSemialgebraicGenerator i }

/-! ## BoxQuadraticModule properties -/

/-- The quadratic module is contained in the preordering.
    Proof: σ₀ ∈ BoxPreordering (SOS with g_∅ = 1) and each σ_i · g_i ∈ BoxPreordering
    (SOS with singleton g_{i}), so the sum is in BoxPreordering by closure under addition. -/
theorem BoxQuadraticModule_subset_BoxPreordering :
    BoxQuadraticModule n r ⊆ BoxPreordering n r := by
  intro p ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩
  rw [hsum]
  apply BoxPreordering_add
  · rw [show σ₀ = σ₀ * BoxSemialgebraicGeneratorProd ∅ from
      by rw [BoxSemialgebraicGeneratorProd_empty, mul_one]]
    exact IsSOS_mul_generatorProd_in_BoxPreordering ∅ σ₀ r hsos₀
      (by rw [BoxSemialgebraicGeneratorProd_empty, mul_one]; exact hdeg₀)
  · apply BoxPreordering_sum
    intro i _
    rw [show σ i * BoxSemialgebraicGenerator i =
      σ i * BoxSemialgebraicGeneratorProd {i} from
      by rw [BoxSemialgebraicGeneratorProd_singleton]]
    exact IsSOS_mul_generatorProd_in_BoxPreordering {i} (σ i) r (hsos i)
      (by rw [BoxSemialgebraicGeneratorProd_singleton]; exact hdeg i)

theorem BoxQuadraticModule_subset_nonneg :
    BoxQuadraticModule n r ⊆ { p | IsNonnegOn p (Hypercube n) } :=
  fun _ hp => box_preordering_subset_nonneg (BoxQuadraticModule_subset_BoxPreordering hp)

theorem BoxQuadraticModule_mono {r s : ℕ} (hrs : r ≤ s) :
    BoxQuadraticModule n r ⊆ BoxQuadraticModule n s := by
  intro p ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩
  exact ⟨σ₀, σ, hsos₀, hsos, le_trans hdeg₀ hrs, fun i => le_trans (hdeg i) hrs, hsum⟩

theorem BoxQuadraticModule_add {p q : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (hp : p ∈ BoxQuadraticModule n r) (hq : q ∈ BoxQuadraticModule n r) :
    p + q ∈ BoxQuadraticModule n r := by
  obtain ⟨σ₀_p, σ_p, hsos₀_p, hsos_p, hdeg₀_p, hdeg_p, hsum_p⟩ := hp
  obtain ⟨σ₀_q, σ_q, hsos₀_q, hsos_q, hdeg₀_q, hdeg_q, hsum_q⟩ := hq
  refine ⟨σ₀_p + σ₀_q, fun i => σ_p i + σ_q i, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsSOS_add hsos₀_p hsos₀_q
  · intro i; exact IsSOS_add (hsos_p i) (hsos_q i)
  · exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le hdeg₀_p hdeg₀_q)
  · intro i
    calc ((σ_p i + σ_q i) * BoxSemialgebraicGenerator i).totalDegree
        = (σ_p i * BoxSemialgebraicGenerator i +
           σ_q i * BoxSemialgebraicGenerator i).totalDegree := by ring_nf
      _ ≤ max (σ_p i * BoxSemialgebraicGenerator i).totalDegree
              (σ_q i * BoxSemialgebraicGenerator i).totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ r := max_le (hdeg_p i) (hdeg_q i)
  · rw [hsum_p, hsum_q]
    have key : ∑ i : Fin n, (fun i => σ_p i + σ_q i) i * BoxSemialgebraicGenerator i =
        ∑ i, σ_p i * BoxSemialgebraicGenerator i + ∑ i, σ_q i * BoxSemialgebraicGenerator i := by
      simp only [add_mul]; exact Finset.sum_add_distrib
    rw [key]; ring

theorem BoxQuadraticModule_nonneg_scale {p : MvPolynomial (Fin n) ℝ} {r : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (hp : p ∈ BoxQuadraticModule n r) :
    MvPolynomial.C c * p ∈ BoxQuadraticModule n r := by
  obtain ⟨σ₀, σ, hsos₀, hsos, hdeg₀, hdeg, hsum⟩ := hp
  refine ⟨MvPolynomial.C c * σ₀, fun i => MvPolynomial.C c * σ i, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsSOS_nonneg_scale hsos₀ c hc
  · intro i; exact IsSOS_nonneg_scale (hsos i) c hc
  · calc (MvPolynomial.C c * σ₀).totalDegree
        ≤ (MvPolynomial.C c).totalDegree + σ₀.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = σ₀.totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ r := hdeg₀
  · intro i
    calc (MvPolynomial.C c * σ i * BoxSemialgebraicGenerator i).totalDegree
        = (MvPolynomial.C c * (σ i * BoxSemialgebraicGenerator i)).totalDegree := by ring_nf
      _ ≤ (MvPolynomial.C c).totalDegree +
           (σ i * BoxSemialgebraicGenerator i).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ = (σ i * BoxSemialgebraicGenerator i).totalDegree := by
          rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ r := hdeg i
  · rw [hsum, mul_add, Finset.mul_sum]; simp only [mul_assoc]

theorem positive_const_in_BoxQuadraticModule {c : ℝ} (hc : 0 < c) (n r : ℕ) :
    MvPolynomial.C c ∈ BoxQuadraticModule n r := by
  refine ⟨MvPolynomial.C c, 0, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨1, fun _ => MvPolynomial.C (Real.sqrt c), by
      simp only [Fin.sum_univ_one, sq, ← MvPolynomial.C_mul,
        Real.mul_self_sqrt hc.le]⟩
  · intro i; exact ⟨0, Fin.elim0, by simp⟩
  · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  · intro i; simp
  · simp


end OptimalConvergenceRates

end
