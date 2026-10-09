/-
  OptimalConvergenceRates/KrivineStengle/GuardedRationalOperations.lean

  Composite guarded rational operations used by symbolic matrix arithmetic.
-/
import OptimalConvergenceRates.KrivineStengle.MonicNormalization

noncomputable section

open MvPolynomial

namespace OptimalConvergenceRates.KrivineStengle.GuardedRational

/-- Additive negation without changing the denominator guard. -/
def neg (r : GuardedRational n) : GuardedRational n :=
  ⟨-r.num, r.den⟩

/-- Subtraction expressed through the guarded addition operation. -/
def sub (r s : GuardedRational n) : GuardedRational n :=
  r.add s.neg

/-- Natural powers using only guarded multiplication. -/
def pow (r : GuardedRational n) : ℕ → GuardedRational n
  | 0 => one
  | k + 1 => (pow r k).mul r

/-- A fixed-order finite sum. No algebraic laws are imposed on the raw
numerator/denominator representation; its evaluation theorem supplies the
field-level sum. -/
def listSum : List (GuardedRational n) → GuardedRational n
  | [] => zero
  | r :: rs => r.add (listSum rs)

/-- A fixed-order finite product. -/
def listProd : List (GuardedRational n) → GuardedRational n
  | [] => one
  | r :: rs => r.mul (listProd rs)

theorem Valid.neg {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r : GuardedRational n}
    (hr : r.Valid coeff x) : r.neg.Valid coeff x := by
  exact hr

theorem Valid.sub {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r s : GuardedRational n}
    (hr : r.Valid coeff x) (hs : s.Valid coeff x) :
    (r.sub s).Valid coeff x :=
  hr.add coeff x (hs.neg coeff x)

theorem Valid.pow {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r : GuardedRational n}
    (hr : r.Valid coeff x) : ∀ k, (r.pow k).Valid coeff x
  | 0 => valid_ofPolynomial coeff x 1
  | k + 1 => (Valid.pow coeff x hr k).mul coeff x hr

theorem Valid.listSum {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {rs : List (GuardedRational n)}
    (hrs : ∀ r ∈ rs, r.Valid coeff x) : (listSum rs).Valid coeff x := by
  induction rs with
  | nil => exact valid_ofPolynomial coeff x 0
  | cons r rs ih =>
      exact (hrs r (by simp)).add coeff x
        (ih (fun s hs ↦ hrs s (by simp [hs])))

theorem Valid.listProd {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {rs : List (GuardedRational n)}
    (hrs : ∀ r ∈ rs, r.Valid coeff x) : (listProd rs).Valid coeff x := by
  induction rs with
  | nil => exact valid_ofPolynomial coeff x 1
  | cons r rs ih =>
      exact (hrs r (by simp)).mul coeff x
        (ih (fun s hs ↦ hrs s (by simp [hs])))

theorem eval_neg {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) (r : GuardedRational n) :
    r.neg.eval coeff x = -r.eval coeff x := by
  simp [neg, eval, neg_div]

theorem eval_sub {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r s : GuardedRational n}
    (hr : r.Valid coeff x) (hs : s.Valid coeff x) :
    (r.sub s).eval coeff x = r.eval coeff x - s.eval coeff x := by
  rw [sub, eval_add coeff x hr (hs.neg coeff x), eval_neg]
  simp [sub_eq_add_neg]

theorem eval_pow {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {r : GuardedRational n}
    (hr : r.Valid coeff x) : ∀ k, (r.pow k).eval coeff x = (r.eval coeff x) ^ k
  | 0 => by simp [pow, one]
  | k + 1 => by
      rw [pow, eval_mul coeff x (Valid.pow coeff x hr k) hr,
        eval_pow coeff x hr k, pow_succ]

theorem eval_listSum {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {rs : List (GuardedRational n)}
    (hrs : ∀ r ∈ rs, r.Valid coeff x) :
    (listSum rs).eval coeff x =
      (rs.map (fun r : GuardedRational n ↦ eval coeff x r)).sum := by
  induction rs with
  | nil => simp [listSum, zero]
  | cons r rs ih =>
      rw [listSum, eval_add coeff x (hrs r (by simp))
        ((Valid.listSum coeff x) (fun s hs ↦ hrs s (by simp [hs])))]
      simp [ih (fun s hs ↦ hrs s (by simp [hs]))]

theorem eval_listProd {F : Type*} [Field F] (coeff : ℝ →+* F)
    (x : Fin n → F) {rs : List (GuardedRational n)}
    (hrs : ∀ r ∈ rs, r.Valid coeff x) :
    (listProd rs).eval coeff x =
      (rs.map (fun r : GuardedRational n ↦ eval coeff x r)).prod := by
  induction rs with
  | nil => simp [listProd, one]
  | cons r rs ih =>
      rw [listProd, eval_mul coeff x (hrs r (by simp))
        ((Valid.listProd coeff x) (fun s hs ↦ hrs s (by simp [hs])))]
      simp [ih (fun s hs ↦ hrs s (by simp [hs]))]

end OptimalConvergenceRates.KrivineStengle.GuardedRational

end
