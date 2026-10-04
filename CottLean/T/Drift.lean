import CottLean.T.Readings

/-!
# Both readings at once, and how far they drift

`Readings` shows the ratio reading and the complex reading agree on the integers and nowhere else. Here
both are carried side by side and allowed to drift. A `Paired` value holds a ratio side `r` and a complex
side `c`, and each operation acts on each side in that side's own reading:

| `Paired` | ratio side | complex side |
|---|---|---|
| `a + b` | `+` | `⊕` |
| `a * b` | `*` | `⊗` |
| `-a` | `-x = T(-p, q)` | `-_x = T(-p, -q)` |
| `a⁻¹` | `reciprocal` | `-x = T(-p, q)`, the conjugate |

The inverse column follows the model's naming. `reciprocal` is the inverse under `*`, and `-x` is the
inverse under `⊗`. So `-x` is the ratio reading's negation and the complex reading's reciprocal. The
integer `n` is `of n = (T(n,1), T(0,n))`.

The complex side's inverse here is only the numerator of the true one. `1/(q + p·i)` is
`(q − p·i)/(p² + q²)`, and a Gaussian integer has nowhere to keep the denominator `p² + q²`. So most of
the drift below is that missing denominator, not a real disagreement between the readings. The exact
inverse needs ratio coordinates, and `Nested.Point` gives it there.

* **The complex side never leaves the real line, and never divides.** Every operation keeps it real
  (`IsReal`), and the inverse leaves it unchanged (`skip_inv`). So the complex side holds `skip a`: the
  integer the expression would give if every division were skipped.
* **Neither side determines the other.** `1/2 + 1/2` and `4 · (1/4)` have the same ratio side `T(4,4)`
  and complex sides `4` and `16` (`ratio_same_skip_differs`). `2` and `1/2` have the same complex side
  (`skip_same_ratio_differs`).
* **The drift.** `drift a` is the ratio side minus the complex side read as a ratio,
  `T(p − n·q, q)`. It is `0` on every integer (`drift_of`). It is additive exactly
  (`drift_add`), odd (`drift_neg`), and satisfies the product rule up to a residue
  (`drift_mul`), exactly when the right denominator is `1` (`drift_mul_of_q_eq_one`):

  ```
  drift (a + b) = drift a + drift b
  drift (a * b) = drift a · r_b + n_a · drift b
  ```

* **Division is the only source of drift.** `agrees a`, a drift numerator of `0`, holds on every integer
  and survives `+`, `-`, and `*` while the complex side is real (`agrees_add`, `agrees_neg`, `agrees_mul`). The inverse breaks it. For
  `1/n` the drift is `T(1 − n², n)`, the ratio `1/n − n` (`drift_inv_of`). It is zero only at the units
  `±1` (`agrees_inv_of_iff`).
* **The laws that survive are the ones both readings keep.** Sum and product are commutative monoids
  with the units `of 0` and `of 1` (`add_of_zero`, `mul_of_one`). Distributivity holds exactly on the
  complex side and up to a residue on the ratio side (`distrib`). `a + -a` and `a · a⁻¹` are residues
  on the ratio side, and `0ω` and the norm on the complex side (`add_neg_self`, `mul_inv_self`).
-/

namespace T

/-- A ratio side and a complex side, carried together. -/
@[ext]
structure Paired where
  /-- The ratio side, read as `p/q`, under `+` and `*`. -/
  r : T
  /-- The complex side, read as `q + p·i`, under `⊕` and `⊗`. -/
  c : T
  deriving DecidableEq, Repr

namespace Paired

/-- The integer `n` in both readings: `(T(n,1), T(0,n))`. -/
def of (n : ℤ) : Paired := ⟨ratioInt n, complexInt n⟩

instance : Add Paired := ⟨fun a b => ⟨a.r + b.r, a.c ⊕ b.c⟩⟩
instance : Mul Paired := ⟨fun a b => ⟨a.r * b.r, a.c ⊗ b.c⟩⟩
instance : Neg Paired := ⟨fun a => ⟨-a.r, oplusInverse a.c⟩⟩
instance : Inv Paired := ⟨fun a => ⟨reciprocal a.r, -a.c⟩⟩

@[simp] theorem add_r (a b : Paired) : (a + b).r = a.r + b.r := rfl
@[simp] theorem add_c (a b : Paired) : (a + b).c = (a.c ⊕ b.c) := rfl
@[simp] theorem mul_r (a b : Paired) : (a * b).r = a.r * b.r := rfl
@[simp] theorem mul_c (a b : Paired) : (a * b).c = a.c ⊗ b.c := rfl
@[simp] theorem neg_r (a : Paired) : (-a).r = -a.r := rfl
@[simp] theorem neg_c (a : Paired) : (-a).c = oplusInverse a.c := rfl
@[simp] theorem inv_r (a : Paired) : a⁻¹.r = reciprocal a.r := rfl
@[simp] theorem inv_c (a : Paired) : a⁻¹.c = -a.c := rfl

/-! ## The integers -/

theorem of_add (a b : ℤ) : of (a + b) = of a + of b := by
  ext1
  · exact ratioInt_plus a b
  · exact complexInt_oplus a b

theorem of_mul (a b : ℤ) : of (a * b) = of a * of b := by
  ext1
  · exact ratioInt_times a b
  · exact complexInt_otimes a b

theorem of_neg (a : ℤ) : of (-a) = -of a := by
  ext1
  · exact ratioInt_neg a
  · exact complexInt_neg a

theorem add_of_zero (a : Paired) : a + of 0 = a := by
  ext1
  · exact plus_zero a.r
  · exact oplus_zeroOmega a.c

theorem mul_of_one (a : Paired) : a * of 1 = a := by
  ext1
  · exact times_one a.r
  · exact otimes_zero a.c

/-! ## The complex side stays real, and skips division -/

/-- The complex side is on the real line. -/
def IsReal (a : Paired) : Prop := a.c.p = 0

/-- The integer the complex side holds: its real part. -/
def skip (a : Paired) : ℤ := a.c.q

theorem isReal_of (n : ℤ) : IsReal (of n) := rfl

theorem IsReal.add {a b : Paired} (ha : IsReal a) (hb : IsReal b) : IsReal (a + b) := by
  change a.c.p + b.c.p = 0
  rw [show a.c.p = 0 from ha, show b.c.p = 0 from hb]; rfl

theorem IsReal.mul {a b : Paired} (ha : IsReal a) (hb : IsReal b) : IsReal (a * b) := by
  change a.c.p * b.c.q + b.c.p * a.c.q = 0
  rw [show a.c.p = 0 from ha, show b.c.p = 0 from hb]; simp

theorem IsReal.neg {a : Paired} (ha : IsReal a) : IsReal (-a) := by
  change -a.c.p = 0
  rw [show a.c.p = 0 from ha]; rfl

theorem IsReal.inv {a : Paired} (ha : IsReal a) : IsReal a⁻¹ := by
  change -a.c.p = 0
  rw [show a.c.p = 0 from ha]; rfl

theorem skip_of (n : ℤ) : skip (of n) = n := rfl

theorem skip_add (a b : Paired) : skip (a + b) = skip a + skip b := rfl

theorem skip_mul {a b : Paired} (ha : IsReal a) : skip (a * b) = skip a * skip b := by
  change a.c.q * b.c.q - a.c.p * b.c.p = a.c.q * b.c.q
  rw [show a.c.p = 0 from ha]; ring

theorem skip_neg (a : Paired) : skip (-a) = -skip a := rfl

/-- The inverse leaves the complex side's integer where it was: the complex reading does not divide. -/
theorem skip_inv (a : Paired) : skip a⁻¹ = skip a := rfl

/-! ## Neither side determines the other -/

/-- `1/2 + 1/2` and `4 · (1/4)` are both `T(4,4)` on the ratio side, and `4` and `16` on the complex side. -/
theorem ratio_same_skip_differs :
    ((of 2)⁻¹ + (of 2)⁻¹).r = (of 4 * (of 4)⁻¹).r ∧
      skip ((of 2)⁻¹ + (of 2)⁻¹) = 4 ∧ skip (of 4 * (of 4)⁻¹) = 16 := by
  decide

/-- `2` and `1/2` have the same complex side. -/
theorem skip_same_ratio_differs : (of 2).c = (of 2)⁻¹.c ∧ (of 2).r ≠ (of 2)⁻¹.r := by decide

/-! ## The drift -/

/-- The ratio side minus the complex side read as a ratio: `r + -(n/1)`, which is `T(p − n·q, q)`. -/
def drift (a : Paired) : T := a.r + -ratioInt (skip a)

@[simp] theorem drift_def (a : Paired) : drift a = ⟨a.r.p - a.c.q * a.r.q, a.r.q⟩ := by
  ext <;> simp [drift, ratioInt, skip]; ring

theorem drift_of (n : ℤ) : drift (of n) = 0 := by
  ext <;> simp [of, ratioInt, complexInt]

theorem drift_add (a b : Paired) : drift (a + b) = drift a + drift b := by
  ext <;> simp [oplus]; ring

theorem drift_neg (a : Paired) : drift (-a) = -drift a := by
  ext <;> simp [oplusInverse]; ring

/-- The product rule, up to the residue of the right ratio denominator. -/
theorem drift_mul {a b : Paired} (ha : IsReal a) :
    drift a * b.r + ratioInt (skip a) * drift b = scale b.r.q (drift (a * b)) := by
  simp only [IsReal] at ha
  ext <;> simp [otimes, ratioInt, skip, scale, ha] <;> ring

theorem drift_mul_of_q_eq_one {a b : Paired} (ha : IsReal a) (hb : b.r.q = 1) :
    drift a * b.r + ratioInt (skip a) * drift b = drift (a * b) := by
  rw [drift_mul ha, hb]; ext <;> simp [scale]

theorem drift_inv (a : Paired) : drift a⁻¹ = ⟨a.r.q - a.c.q * a.r.p, a.r.p⟩ := by
  simp [reciprocal]

/-- The drift of `1/n` is `T(1 − n², n)`, the ratio `1/n − n`. -/
theorem drift_inv_of (n : ℤ) : drift (of n)⁻¹ = ⟨1 - n ^ 2, n⟩ := by
  ext <;> simp [of, ratioInt, complexInt, reciprocal]; ring

/-! ## Agreement, and what breaks it -/

/-- The two sides agree: the ratio side is the complex side's integer, scaled. -/
def agrees (a : Paired) : Prop := (drift a).p = 0

/-- The drift's numerator, as a formula. -/
theorem agrees_iff (a : Paired) : agrees a ↔ a.r.p = a.c.q * a.r.q := by
  rw [agrees, drift_def]; constructor <;> intro h <;> linarith

theorem agrees_of (n : ℤ) : agrees (of n) := by rw [agrees, drift_of]; rfl

theorem agrees_add {a b : Paired} (ha : agrees a) (hb : agrees b) : agrees (a + b) := by
  rw [agrees, drift_add]
  change (drift a).p * (drift b).q + (drift b).p * (drift a).q = 0
  rw [show (drift a).p = 0 from ha, show (drift b).p = 0 from hb]; ring

theorem agrees_neg {a : Paired} (ha : agrees a) : agrees (-a) := by
  rw [agrees, drift_neg]
  change -(drift a).p = 0
  rw [show (drift a).p = 0 from ha, neg_zero]

/-- `*` keeps agreement while the left complex side is real. -/
theorem agrees_mul {a b : Paired} (hr : IsReal a) (ha : agrees a) (hb : agrees b) : agrees (a * b) := by
  rw [agrees_iff] at *
  change a.r.p * b.r.p = (a.c.q * b.c.q - a.c.p * b.c.p) * (a.r.q * b.r.q)
  rw [show a.c.p = 0 from hr, ha, hb]; ring

/-- `1/n` agrees exactly at the units `±1`. -/
theorem agrees_inv_of_iff (n : ℤ) : agrees (of n)⁻¹ ↔ n = 1 ∨ n = -1 := by
  rw [agrees, drift_inv_of]
  change 1 - n ^ 2 = 0 ↔ _
  constructor
  · intro h
    have h2 : (n - 1) * (n + 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h2 with h | h
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-! ## The laws that survive -/

/-- Distributivity holds exactly on the complex side and up to a residue on the ratio side. -/
theorem distrib (a b d : Paired) :
    (a * d + b * d).c = ((a + b) * d).c ∧ (a * d + b * d).r = scale d.r.q ((a + b) * d).r :=
  ⟨(oplus_otimes a.c b.c d.c).symm, distrib_scaled a.r b.r d.r⟩

theorem add_neg_self (a : Paired) : a + -a = ⟨⟨0, a.r.q ^ 2⟩, «0ω»⟩ := by
  ext1
  · exact plus_neg_self a.r
  · exact oplus_oplusInverse a.c

theorem mul_inv_self (a : Paired) :
    a * a⁻¹ = ⟨⟨a.r.p * a.r.q, a.r.p * a.r.q⟩, ⟨0, a.c.p ^ 2 + a.c.q ^ 2⟩⟩ := by
  ext1
  · exact times_reciprocal_self a.r
  · exact otimes_neg_self a.c

end Paired

end T
