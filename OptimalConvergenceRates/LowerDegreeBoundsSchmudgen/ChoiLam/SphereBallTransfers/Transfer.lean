/-
  OptimalConvergenceRates/LowerDegreeBoundsSchmudgen/ChoiLam/SphereBallTransfers/Transfer.lean

  Algebra maps and interfaces for transferring sphere certificates to ball and box certificates.
-/
import OptimalConvergenceRates.LowerDegreeBoundsSchmudgen.ChoiLam.SphereBallTransfers.Defs

open MvPolynomial Finset
open scoped BigOperators

noncomputable section

namespace OptimalConvergenceRates
namespace SphereBallTransfers


/-! ## Intermediate ball certificate -/

/-- The ball generator `g(y) = 1 - sum_i y_i^2` in four variables. -/
def ballQuadratic4 : MvPolynomial (Fin 4) ℝ :=
  ∑ i : Fin 4, (X i) ^ 2

/-- The ball generator `g(y) = 1 - sum_i y_i^2` in four variables. -/
def ballGenerator4 : MvPolynomial (Fin 4) ℝ :=
  1 - ballQuadratic4

/-- The two-block ball identity produced from a sphere certificate:
`C + epsilon = sum a_j^2 + g * sum b_j^2`, with degree bounds on `a_j` and `b_j`. -/
structure BallCertificate (k : ℕ) (epsilon : ℝ) where
  N : ℕ
  a : Fin N → MvPolynomial (Fin 4) ℝ
  b : Fin N → MvPolynomial (Fin 4) ℝ
  decomp :
    choiLamPerturbed epsilon =
      (∑ j : Fin N, (a j) ^ 2) + ballGenerator4 * ∑ j : Fin N, (b j) ^ 2
  degree_a : ∀ j : Fin N, (a j).totalDegree ≤ k
  degree_b : ∀ j : Fin N, (b j).totalDegree ≤ k - 1

/-- Reduce a sphere certificate modulo `u^2 = g` and compare the unique
`A + uB` remainder. -/
def SphereToBallTransfer : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃epsilon : ℝ⦄, 2 ≤ k → ChoiLamHasSphereCert k epsilon →
    Nonempty (BallCertificate k epsilon)



/-! ## Scaling from the ball variables to the box variables -/

/-- The scaling homomorphism `x_i ↦ y_i / 2`. -/
noncomputable def scaleToBox : MvPolynomial (Fin 4) ℝ →ₐ[ℝ] MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.aeval fun i : Fin 4 => MvPolynomial.C (1 / 2 : ℝ) * X i

@[simp] theorem scaleToBox_X (i : Fin 4) :
    scaleToBox (X i) = MvPolynomial.C (1 / 2 : ℝ) * X i := by
  simp [scaleToBox]

/-- Scaling sends the Choi-Lam quartic to `1/16` times itself. -/
theorem scaleToBox_choiLamQuartic :
    scaleToBox choiLamQuartic = MvPolynomial.C (1 / 16 : ℝ) * choiLamQuartic := by
  have hc4 : (MvPolynomial.C (1 / 2 : ℝ) : MvPolynomial (Fin 4) ℝ) ^ 4 =
      MvPolynomial.C (1 / 16 : ℝ) := by
    norm_num [← MvPolynomial.C_pow]
  unfold scaleToBox choiLamQuartic
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.aeval_X]
  ring_nf
  rw [hc4]
  ring_nf

/-- Scaling sends the ball generator to the average of the four box generators. -/
theorem scaleToBox_ballGenerator4 :
    scaleToBox ballGenerator4 =
      MvPolynomial.C (1 / 4 : ℝ) * ∑ i : Fin 4, BoxSemialgebraicGenerator i := by
  have hc2 : (MvPolynomial.C (1 / 2 : ℝ) : MvPolynomial (Fin 4) ℝ) ^ 2 =
      MvPolynomial.C (1 / 4 : ℝ) := by
    norm_num [← MvPolynomial.C_pow]
  unfold scaleToBox ballGenerator4 ballQuadratic4 BoxSemialgebraicGenerator
  simp only [map_sub, map_one, map_sum, map_pow, MvPolynomial.aeval_X]
  simp [Fin.sum_univ_four]
  ring_nf
  rw [hc2]
  have hc4 : (MvPolynomial.C (1 / 4 : ℝ) : MvPolynomial (Fin 4) ℝ) * 4 = 1 := by
    change (MvPolynomial.C (1 / 4 : ℝ) : MvPolynomial (Fin 4) ℝ) *
      MvPolynomial.C (4 : ℝ) = MvPolynomial.C (1 : ℝ)
    rw [← MvPolynomial.C_mul]
    norm_num
  rw [hc4]
  ring_nf


/-- Scaling the box-side Choi-Lam perturbation introduces the factor `16` in the
constant perturbation. -/
theorem scaleToBox_choiLamPerturbed (epsilon : ℝ) :
    scaleToBox (choiLamPerturbed epsilon) =
      MvPolynomial.C (1 / 16 : ℝ) * choiLamPerturbed (16 * epsilon) := by
  unfold choiLamPerturbed
  simp only [map_add, algHom_C, algebraMap_eq, C_mul]
  rw [scaleToBox_choiLamQuartic]
  rw [mul_add]
  congr 1
  rw [← MvPolynomial.C_mul]
  rw [← MvPolynomial.C_mul]
  congr 1
  ring


private theorem scaledSquares_identity {N : ℕ}
    (a b : Fin N → MvPolynomial (Fin 4) ℝ) :
    (∑ j : Fin N, (MvPolynomial.C (4 : ℝ) * a j) ^ 2) +
      ∑ i : Fin 4,
        (∑ j : Fin N, (MvPolynomial.C (2 : ℝ) * b j) ^ 2) * BoxSemialgebraicGenerator i =
    MvPolynomial.C (16 : ℝ) *
      ((∑ j : Fin N, (a j) ^ 2) +
        (MvPolynomial.C (1 / 4 : ℝ) * ∑ i : Fin 4, BoxSemialgebraicGenerator i) *
          ∑ j : Fin N, (b j) ^ 2) := by
  let S : MvPolynomial (Fin 4) ℝ := ∑ i : Fin 4, BoxSemialgebraicGenerator i
  let B : MvPolynomial (Fin 4) ℝ := ∑ j : Fin N, (b j) ^ 2
  have hc4 : (MvPolynomial.C (4 : ℝ) : MvPolynomial (Fin 4) ℝ) ^ 2 =
      MvPolynomial.C (16 : ℝ) := by norm_num [← MvPolynomial.C_pow]
  have hc2 : (MvPolynomial.C (2 : ℝ) : MvPolynomial (Fin 4) ℝ) ^ 2 =
      MvPolynomial.C (4 : ℝ) := by norm_num [← MvPolynomial.C_pow]
  have hc16_4 : (MvPolynomial.C (16 : ℝ) : MvPolynomial (Fin 4) ℝ) *
      MvPolynomial.C (1 / 4 : ℝ) = MvPolynomial.C (4 : ℝ) := by
    rw [← MvPolynomial.C_mul]
    norm_num
  simp_rw [mul_pow, hc4, hc2]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  rw [mul_add]
  congr 1
  calc
    (MvPolynomial.C (4 : ℝ) * ∑ x : Fin N, b x ^ 2) *
        (∑ i : Fin 4, BoxSemialgebraicGenerator i)
        = MvPolynomial.C (4 : ℝ) *
            ((∑ i : Fin 4, BoxSemialgebraicGenerator i) * ∑ x : Fin N, b x ^ 2) := by
          ring
    _ = MvPolynomial.C (4 : ℝ) *
            (∑ x : Fin N, (∑ i : Fin 4, BoxSemialgebraicGenerator i) * b x ^ 2) := by
          rw [Finset.mul_sum]
    _ = MvPolynomial.C (16 : ℝ) *
        ((MvPolynomial.C (1 / 4 : ℝ) * ∑ i : Fin 4, BoxSemialgebraicGenerator i) *
          ∑ x : Fin N, b x ^ 2) := by
          rw [show MvPolynomial.C (16 : ℝ) *
              ((MvPolynomial.C (1 / 4 : ℝ) * ∑ i : Fin 4, BoxSemialgebraicGenerator i) *
                ∑ x : Fin N, b x ^ 2) =
              (MvPolynomial.C (16 : ℝ) * MvPolynomial.C (1 / 4 : ℝ)) *
                ((∑ i : Fin 4, BoxSemialgebraicGenerator i) * ∑ x : Fin N, b x ^ 2) by
            ring]
          rw [hc16_4, ← Finset.mul_sum]

/-- The already-scaled two-block identity appearing just before packing into the
box Schmuedgen cone. -/
structure ScaledBallCertificate (k : ℕ) (epsilon : ℝ) where
  N : ℕ
  a : Fin N → MvPolynomial (Fin 4) ℝ
  b : Fin N → MvPolynomial (Fin 4) ℝ
  decomp :
    choiLamPerturbed (16 * epsilon) =
      (∑ j : Fin N, (MvPolynomial.C (4 : ℝ) * a j) ^ 2) +
        ∑ i : Fin 4,
          (∑ j : Fin N, (MvPolynomial.C (2 : ℝ) * b j) ^ 2) *
            BoxSemialgebraicGenerator i
  degree_a : ∀ j : Fin N, (a j).totalDegree ≤ k
  degree_b : ∀ j : Fin N, (b j).totalDegree ≤ k - 1

private lemma isSOS_sum_scaled_sq {N : ℕ} (c : ℝ)
    (p : Fin N → MvPolynomial (Fin 4) ℝ) :
    IsSOS (∑ j : Fin N, (MvPolynomial.C c * p j) ^ 2) := by
  apply IsSOS_sum_finset
  intro j _
  exact IsSOS_sq (MvPolynomial.C c * p j)

private lemma totalDegree_C_mul_le {n : ℕ} (c : ℝ) (p : MvPolynomial (Fin n) ℝ)
    {d : ℕ} (hp : p.totalDegree ≤ d) :
    (MvPolynomial.C c * p).totalDegree ≤ d := by
  calc
    (MvPolynomial.C c * p).totalDegree
        ≤ (MvPolynomial.C c : MvPolynomial (Fin n) ℝ).totalDegree + p.totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ = 0 + p.totalDegree := by rw [MvPolynomial.totalDegree_C]
    _ ≤ 0 + d := Nat.add_le_add_left hp 0
    _ = d := Nat.zero_add d

private lemma totalDegree_sum_scaled_sq_le {N d : ℕ} (c : ℝ)
    (p : Fin N → MvPolynomial (Fin 4) ℝ) (hp : ∀ j, (p j).totalDegree ≤ d) :
    (∑ j : Fin N, (MvPolynomial.C c * p j) ^ 2).totalDegree ≤ 2 * d := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  calc
    ((MvPolynomial.C c * p j) ^ 2).totalDegree
        ≤ 2 * (MvPolynomial.C c * p j).totalDegree := MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 * d := Nat.mul_le_mul_left 2 (totalDegree_C_mul_le c (p j) (hp j))

private theorem totalDegree_aeval_le_of_linear {n m : ℕ}
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
private theorem isSOS_mul_generatorProd_in_box_preordering4 (J : Finset (Fin 4))
    (σ : MvPolynomial (Fin 4) ℝ) (r : ℕ)
    (hsos : IsSOS σ) (hdeg : (σ * BoxSemialgebraicGeneratorProd J).totalDegree ≤ r) :
    σ * BoxSemialgebraicGeneratorProd J ∈ BoxPreordering 4 r := by
  have hJ_mem : J ∈ (Finset.univ : Finset (Fin 4)).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ J)
  refine ⟨Function.update 0 J σ, ?_, ?_, ?_⟩
  · intro K
    by_cases hK : K = J
    · subst hK
      rwa [Function.update_self]
    · rw [Function.update_of_ne hK, Pi.zero_apply]
      exact IsSOS_zero
  · intro K
    by_cases hK : K = J
    · subst hK
      rwa [Function.update_self]
    · rw [Function.update_of_ne hK, Pi.zero_apply, zero_mul]
      exact Nat.zero_le _
  · rw [Finset.sum_eq_single J
      (fun K _ hK => by rw [Function.update_of_ne hK, Pi.zero_apply, zero_mul])
      (fun h => absurd hJ_mem h)]
    rw [Function.update_self]

/-- Pack the scaled two-block identity into the existing box preordering. -/
theorem ScaledBallCertificate.toBoxCert {k : ℕ} {epsilon : ℝ}
    (hk : 2 ≤ k) (w : ScaledBallCertificate k epsilon) : BoxCert k (16 * epsilon) := by
  classical
  let A : MvPolynomial (Fin 4) ℝ := ∑ j : Fin w.N, (MvPolynomial.C (4 : ℝ) * w.a j) ^ 2
  let B : MvPolynomial (Fin 4) ℝ := ∑ j : Fin w.N, (MvPolynomial.C (2 : ℝ) * w.b j) ^ 2
  have hA_sos : IsSOS A := by
    dsimp [A]
    exact isSOS_sum_scaled_sq 4 w.a
  have hB_sos : IsSOS B := by
    dsimp [B]
    exact isSOS_sum_scaled_sq 2 w.b
  have hA_deg : (A * BoxSemialgebraicGeneratorProd (∅ : Finset (Fin 4))).totalDegree ≤ 2 * k := by
    rw [BoxSemialgebraicGeneratorProd_empty, mul_one]
    dsimp [A]
    exact totalDegree_sum_scaled_sq_le 4 w.a w.degree_a
  have hB_deg (i : Fin 4) :
      (B * BoxSemialgebraicGeneratorProd ({i} : Finset (Fin 4))).totalDegree ≤ 2 * k := by
    rw [BoxSemialgebraicGeneratorProd_singleton]
    calc
      (B * BoxSemialgebraicGenerator i).totalDegree
          ≤ B.totalDegree + (BoxSemialgebraicGenerator i).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * (k - 1) + 2 := by
        apply Nat.add_le_add
        · dsimp [B]
          exact totalDegree_sum_scaled_sq_le 2 w.b w.degree_b
        · unfold BoxSemialgebraicGenerator
          calc
            (1 - X i ^ 2 : MvPolynomial (Fin 4) ℝ).totalDegree
                ≤ max (1 : MvPolynomial (Fin 4) ℝ).totalDegree ((X i) ^ 2).totalDegree :=
                  MvPolynomial.totalDegree_sub _ _
            _ ≤ 2 := by
              apply max_le
              · simp
              · calc
                  ((X i : MvPolynomial (Fin 4) ℝ) ^ 2).totalDegree
                      ≤ 2 * (X i : MvPolynomial (Fin 4) ℝ).totalDegree :=
                        MvPolynomial.totalDegree_pow _ 2
                  _ ≤ 2 := by simp
      _ ≤ 2 * k := by omega
  rw [BoxCert, Tbox]
  rw [w.decomp]
  change A + ∑ i : Fin 4, B * BoxSemialgebraicGenerator i ∈ BoxPreordering 4 (2 * k)
  apply BoxPreordering_add
  · rw [show A = A * BoxSemialgebraicGeneratorProd (∅ : Finset (Fin 4)) by
      rw [BoxSemialgebraicGeneratorProd_empty, mul_one]]
    exact isSOS_mul_generatorProd_in_box_preordering4 ∅ A (2 * k) hA_sos hA_deg
  · apply BoxPreordering_sum
    intro i _
    rw [show B * BoxSemialgebraicGenerator i =
        B * BoxSemialgebraicGeneratorProd ({i} : Finset (Fin 4)) by
      rw [BoxSemialgebraicGeneratorProd_singleton]]
    exact isSOS_mul_generatorProd_in_box_preordering4 {i} B (2 * k) hB_sos (hB_deg i)

/-- A scaled-ball certificate yields the corresponding box certificate. -/
def ScaledBallToBoxTransfer : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃epsilon : ℝ⦄, 2 ≤ k → Nonempty (ScaledBallCertificate k epsilon) →
    BoxCert k (16 * epsilon)

/-- Packing a scaled-ball certificate into the box preordering. -/
theorem scaledBallToBoxTransfer : ScaledBallToBoxTransfer := by
  intro k epsilon hk hw
  rcases hw with ⟨w⟩
  exact w.toBoxCert hk


/-- Apply `x_i ↦ y_i / 2` to a `BallCertificate`, preserving the degree bounds
needed by the packing stage. -/
def BallToScaledBallTransfer : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃epsilon : ℝ⦄, 2 ≤ k → Nonempty (BallCertificate k epsilon) →
    Nonempty (ScaledBallCertificate k epsilon)

/-- The generic degree-preservation property needed for the scaling map. -/
def ScaleDegreePreserving : Prop :=
  ∀ {p : MvPolynomial (Fin 4) ℝ} {d : ℕ},
    p.totalDegree ≤ d → (scaleToBox p).totalDegree ≤ d

/-- Scaling variables by `1 / 2` does not increase total degree. -/
theorem scaleDegreePreserving : ScaleDegreePreserving := by
  intro p d hp
  exact (totalDegree_aeval_le_of_linear
    (fun i : Fin 4 => MvPolynomial.C (1 / 2 : ℝ) * X i) (by
      intro i
      exact totalDegree_C_mul_le (1 / 2 : ℝ) (X i) (by simp)) p).trans hp

/-- Apart from the generic degree-preservation lemma for `scaleToBox`, the
ball-to-scaled-ball construction is fully algebraic. -/
theorem ballToScaledBallTransfer_of_scaleDegreePreserving
    (hdegscale : ScaleDegreePreserving) : BallToScaledBallTransfer := by
  intro k epsilon hk hw
  rcases hw with ⟨w⟩
  refine ⟨{
    N := w.N
    a := fun j => scaleToBox (w.a j)
    b := fun j => scaleToBox (w.b j)
    decomp := ?_
    degree_a := ?_
    degree_b := ?_ }⟩
  · have h := congrArg scaleToBox w.decomp
    rw [scaleToBox_choiLamPerturbed] at h
    simp only [map_add, map_mul, map_sum, map_pow] at h
    rw [scaleToBox_ballGenerator4] at h
    rw [scaledSquares_identity (fun j => scaleToBox (w.a j))
      (fun j => scaleToBox (w.b j))]
    rw [← h]
    have hc : (MvPolynomial.C (16 : ℝ) : MvPolynomial (Fin 4) ℝ) *
        MvPolynomial.C (1 / 16 : ℝ) = 1 := by
      change (MvPolynomial.C (16 : ℝ) : MvPolynomial (Fin 4) ℝ) *
        MvPolynomial.C (1 / 16 : ℝ) = MvPolynomial.C (1 : ℝ)
      rw [← MvPolynomial.C_mul]
      norm_num
    rw [← mul_assoc, hc, one_mul]
  · intro j
    exact hdegscale (w.degree_a j)
  · intro j
    exact hdegscale (w.degree_b j)

/-- Scale `x_i` to `y_i / 2` and turn the two-block ball identity into a box
Schmuedgen certificate. -/
def BallToBoxTransfer : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃epsilon : ℝ⦄, 2 ≤ k → Nonempty (BallCertificate k epsilon) →
    BoxCert k (16 * epsilon)

/-- The scaling and packing substages compose to `BallToBoxTransfer`. -/
theorem ballToBoxTransfer_of_ballToScaledBall
    (hscale : BallToScaledBallTransfer) : BallToBoxTransfer := by
  intro k epsilon hk hw
  exact scaledBallToBoxTransfer hk (hscale hk hw)

/-- A generic total-degree preservation lemma for `scaleToBox` is enough to prove the
entire ball-to-box stage. -/
theorem ballToBoxTransfer_of_scaleDegreePreserving
    (hdegscale : ScaleDegreePreserving) : BallToBoxTransfer :=
  ballToBoxTransfer_of_ballToScaledBall
    (ballToScaledBallTransfer_of_scaleDegreePreserving hdegscale)

/-- The checked ball-to-box stage, including scaling degree bounds and packing into
Schmuedgen's box preordering. -/
theorem ballToBoxTransfer : BallToBoxTransfer :=
  ballToBoxTransfer_of_scaleDegreePreserving scaleDegreePreserving

/-- The exact degree-preserving transfer theorem isolated as a reusable property.

The construction reduces each sphere square root modulo
`u^2 = 1 - sum_i x_i^2`, then scales `x_i` to `y_i / 2`. -/
def SphereToBoxTransfer : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃epsilon : ℝ⦄, 2 ≤ k → ChoiLamHasSphereCert k epsilon → BoxCert k (16 * epsilon)


/-- The two algebraic stages compose to the exact sphere-to-box transfer. -/
theorem sphereToBoxTransfer_of_sphereToBall_and_ballToBox
    (hsb : SphereToBallTransfer) (hbb : BallToBoxTransfer) : SphereToBoxTransfer := by
  intro k epsilon hk hcert
  exact hbb hk (hsb hk hcert)

/-- The sphere-to-box transfer after the checked scaling and packing stages;
only the sphere-to-ball normal-form step remains as an input. -/
theorem sphereToBoxTransfer_of_sphereToBall
    (hsb : SphereToBallTransfer) : SphereToBoxTransfer :=
  sphereToBoxTransfer_of_sphereToBall_and_ballToBox hsb ballToBoxTransfer

/-- The fourth-power lower bound transfers immediately once the algebraic
sphere-to-box certificate map is available. -/
theorem sphere_lowerBound_from_BoxLB4
    (htransfer : SphereToBoxTransfer) {beta delta0 : ℝ} (hbox : BoxLB4 beta delta0)
    {k : ℕ} {epsilon : ℝ} (hk : 2 ≤ k) (heps : 0 < epsilon)
    (heps0 : epsilon ≤ delta0 / 16) (hcert : ChoiLamHasSphereCert k epsilon) :
    beta / 16 ≤ epsilon * (k : ℝ) ^ 4 := by
  have hdelta_pos : 0 < 16 * epsilon := by positivity
  have hdelta_le : 16 * epsilon ≤ delta0 := by linarith
  have hboxcert : BoxCert k (16 * epsilon) := htransfer hk hcert
  have h := hbox hdelta_pos hdelta_le hboxcert
  nlinarith


end SphereBallTransfers
end OptimalConvergenceRates

end
