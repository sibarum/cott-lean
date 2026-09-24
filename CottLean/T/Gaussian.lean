import CottLean.T.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# The exponent position is the Gaussian integers

`T(p, q)` is the point `q + p·i`. Under that reading `⊕` is the sum of the points and `⊗` is their
product, so `(T, ⊕, ⊗)` is `ℤ[i]` term by term -- not by analogy, and not up to any reduction: the map
below is the identity on coordinates, with the two slots named the other way round.

`-x`, which is `T(-p, q)`, is the complex conjugate. The `⊕` inverse `-_x = T(-p, -q)` is the ring's own
negation.

## Why a second type

`T`'s own `+` and `*` are the value position, and those are not a ring (see `Fraction`). So the ring
structure is put on `GaussianPosition`, which is `T` itself read in the exponent position: its `+` is `⊕`
and its `*` is `⊗`, definitionally. Every ring law Mathlib has then holds of `⊕` and `⊗`, and the theorems
at the bottom restate the ones the docs quote in the docs' own notation.
-/



namespace T

/-! ## The map -/

/-- `T(p, q) ↦ q + p·i`. -/
def toGaussian : T ≃ GaussianInt where
  toFun x := ⟨x.q, x.p⟩
  invFun z := ⟨z.im, z.re⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem toGaussian_re (x : T) : (toGaussian x).re = x.q := rfl
@[simp] theorem toGaussian_im (x : T) : (toGaussian x).im = x.p := rfl

theorem toGaussian_injective : Function.Injective toGaussian := toGaussian.injective

/-! ## Each operation, carried across -/

theorem toGaussian_oplus (x y : T) : toGaussian (x ⊕ y) = toGaussian x + toGaussian y := by
  ext <;> simp [oplus, toGaussian]

theorem toGaussian_otimes (x y : T) : toGaussian (x ⊗ y) = toGaussian x * toGaussian y := by
  ext <;> simp [otimes, toGaussian] <;> ring

/-- `-x` is the conjugate. -/
theorem toGaussian_neg (x : T) : toGaussian (-x) = star (toGaussian x) := by
  ext <;> simp [toGaussian]

/-- `-_x` is the negative. -/
theorem toGaussian_oplusInverse (x : T) : toGaussian (oplusInverse x) = -toGaussian x := by
  ext <;> simp [oplusInverse, toGaussian]

@[simp] theorem toGaussian_zero : toGaussian 0 = 1 := by ext <;> rfl
@[simp] theorem toGaussian_zeroOmega : toGaussian «0ω» = 0 := by ext <;> rfl
@[simp] theorem toGaussian_omega : toGaussian «ω» = ⟨0, 1⟩ := rfl
@[simp] theorem toGaussian_underZero : toGaussian «_0» = -1 := by ext <;> rfl
@[simp] theorem toGaussian_negOmega : toGaussian «-ω» = ⟨0, -1⟩ := rfl

theorem toGaussian_otimesPowNat (x : T) (n : ℕ) :
    toGaussian (otimesPowNat x n) = toGaussian x ^ n := by
  induction n with
  | zero => rw [otimesPowNat, pow_zero]; exact toGaussian_zero
  | succ n ih => rw [otimesPowNat, toGaussian_otimes, ih, pow_succ]

/-- The angle scaled `n` times is the point raised to `n`, and to a negative `n` through the conjugate. -/
theorem toGaussian_otimesPower_ofNat (x : T) (n : ℕ) :
    toGaussian (otimesPower x n) = toGaussian x ^ n :=
  toGaussian_otimesPowNat x n

theorem toGaussian_otimesPower_negSucc (x : T) (n : ℕ) :
    toGaussian (otimesPower x (Int.negSucc n)) = star (toGaussian x) ^ (n + 1) := by
  rw [otimesPower, toGaussian_otimesPowNat]
  rfl

/-! ## The ring the exponent position is -/

/-- `T` read in the exponent position: `+` is `⊕` and `*` is `⊗`. -/
def GaussianPosition : Type := T

namespace GaussianPosition

/-- Read a pair in the exponent position. -/
def of : T ≃ GaussianPosition := Equiv.refl T
/-- And back. -/
def val : GaussianPosition ≃ T := Equiv.refl T

instance : Zero GaussianPosition := ⟨of «0ω»⟩
instance : One GaussianPosition := ⟨of «0»⟩
instance : Add GaussianPosition := ⟨fun x y => of (val x ⊕ val y)⟩
instance : Mul GaussianPosition := ⟨fun x y => of (val x ⊗ val y)⟩
instance : Neg GaussianPosition := ⟨fun x => of (oplusInverse (val x))⟩
instance : Sub GaussianPosition := ⟨fun x y => x + -y⟩
instance : SMul ℕ GaussianPosition := ⟨fun n x => of ⟨n * (val x).p, n * (val x).q⟩⟩
instance : SMul ℤ GaussianPosition := ⟨fun n x => of ⟨n * (val x).p, n * (val x).q⟩⟩
instance : Pow GaussianPosition ℕ := ⟨fun x n => of (otimesPowNat (val x) n)⟩
instance : NatCast GaussianPosition := ⟨fun n => of ⟨0, n⟩⟩
instance : IntCast GaussianPosition := ⟨fun n => of ⟨0, n⟩⟩

/-- The map, on the exponent position. -/
def toG (x : GaussianPosition) : GaussianInt := toGaussian (val x)

theorem toG_injective : Function.Injective toG := toGaussian_injective

instance : CommRing GaussianPosition :=
  toG_injective.commRing toG
    toGaussian_zeroOmega
    toGaussian_zero
    (fun x y => toGaussian_oplus (val x) (val y))
    (fun x y => toGaussian_otimes (val x) (val y))
    (fun x => toGaussian_oplusInverse (val x))
    (fun x y => by
      change toGaussian (val x ⊕ oplusInverse (val y)) = _
      rw [toGaussian_oplus, toGaussian_oplusInverse, sub_eq_add_neg]; rfl)
    (fun n x => by
      change (⟨(n : ℤ) * (val x).q, (n : ℤ) * (val x).p⟩ : GaussianInt) = _
      rw [nsmul_eq_mul]; ext <;> simp [toG])
    (fun n x => by
      change (⟨n * (val x).q, n * (val x).p⟩ : GaussianInt) = _
      rw [zsmul_eq_mul]; ext <;> simp [toG])
    (fun x n => toGaussian_otimesPowNat (val x) n)
    (fun n => by change (⟨(n : ℤ), 0⟩ : GaussianInt) = _; ext <;> simp)
    (fun n => by change (⟨n, 0⟩ : GaussianInt) = _; ext <;> simp)

/-- The exponent position is `ℤ[i]`, as a ring. -/
def ringEquiv : GaussianPosition ≃+* GaussianInt where
  toEquiv := val.trans toGaussian
  map_mul' x y := toGaussian_otimes (val x) (val y)
  map_add' x y := toGaussian_oplus (val x) (val y)

end GaussianPosition

/-! ## What that gives, in the docs' notation

Each of these is one line because the ring did the work. They are the facts T-Design.md §2.1 measured
over samples, now for every pair.
-/


theorem oplus_comm (x y : T) : (x ⊕ y) = (y ⊕ x) :=
  toGaussian_injective (by simp [toGaussian_oplus, add_comm])

theorem oplus_assoc (x y z : T) : ((x ⊕ y) ⊕ z) = (x ⊕ (y ⊕ z)) :=
  toGaussian_injective (by simp [toGaussian_oplus, add_assoc])

theorem otimes_comm (x y : T) : x ⊗ y = y ⊗ x :=
  toGaussian_injective (by simp [toGaussian_otimes, mul_comm])

theorem otimes_assoc (x y z : T) : x ⊗ y ⊗ z = x ⊗ (y ⊗ z) :=
  toGaussian_injective (by simp [toGaussian_otimes, mul_assoc])

/-- `(x ⊕ y) ⊗ z = (x ⊗ z) ⊕ (y ⊗ z)`, exactly on the coordinates, as the model says. -/
theorem oplus_otimes (x y z : T) : (x ⊕ y) ⊗ z = ((x ⊗ z) ⊕ (y ⊗ z)) :=
  toGaussian_injective (by simp [toGaussian_oplus, toGaussian_otimes, add_mul])

theorem otimes_oplus (x y z : T) : x ⊗ (y ⊕ z) = ((x ⊗ y) ⊕ (x ⊗ z)) :=
  toGaussian_injective (by simp [toGaussian_oplus, toGaussian_otimes, mul_add])

/-- `0ω` is the unit of `⊕`. -/
theorem oplus_zeroOmega (x : T) : (x ⊕ «0ω») = x :=
  toGaussian_injective (by simp [toGaussian_oplus])

/-- `0` is the unit of `⊗`. -/
theorem otimes_zero (x : T) : x ⊗ 0 = x :=
  toGaussian_injective (by rw [toGaussian_otimes, toGaussian_zero, mul_one])

/-- `-_x` undoes `⊕`, landing on its unit. -/
theorem oplus_oplusInverse (x : T) : (x ⊕ oplusInverse x) = «0ω» :=
  toGaussian_injective (by simp [toGaussian_oplus, toGaussian_oplusInverse])

/-! ### Minus, which is conjugation -/

theorem neg_neg (x : T) : -(-x) = x := by ext <;> simp

theorem neg_oplus (x y : T) : -(x ⊕ y) = (-x ⊕ -y) :=
  toGaussian_injective (by simp only [toGaussian_neg, toGaussian_oplus, star_add])

theorem neg_otimes (x y : T) : -(x ⊗ y) = -x ⊗ -y :=
  toGaussian_injective (by simp only [toGaussian_neg, toGaussian_otimes, star_mul'])

/-- A pair against its own negation is the norm, standing in the denominator: `T(0, p²+q²)`. It lands on
the unit's angle and not on the unit, because nothing reduces. -/
theorem otimes_neg_self (x : T) : x ⊗ -x = ⟨0, x.p ^ 2 + x.q ^ 2⟩ := by
  ext <;> simp [otimes]
  ring

/-- The reciprocal is the quarter turn after the conjugate: `1/x = ω ⊗ -x`. As an angle that is the
reflection about half a right angle, where tan and cot trade. -/
theorem reciprocal_eq_omega_otimes_neg (x : T) : reciprocal x = «ω» ⊗ -x := by
  ext <;> simp [reciprocal, otimes, «ω»]

/-! ### The four pairs that `⊗` can undo -/

/-- The pairs with a `⊗` inverse are exactly the four on the axes: `0`, `ω`, `_0` and `-ω`. -/
theorem exists_otimes_eq_zero_iff (x : T) :
    (∃ y, x ⊗ y = 0) ↔ x = 0 ∨ x = «ω» ∨ x = «_0» ∨ x = «-ω» := by
  constructor
  · rintro ⟨y, h⟩
    have hp : x.p * y.q + y.p * x.q = 0 := congrArg T.p h
    have hq : x.q * y.q - x.p * y.p = 1 := congrArg T.q h
    -- The norms multiply, and the product of the norms is the norm of `0`, which is one.
    have hn : (x.p ^ 2 + x.q ^ 2) * (y.p ^ 2 + y.q ^ 2) = 1 := by
      have : (x.p ^ 2 + x.q ^ 2) * (y.p ^ 2 + y.q ^ 2)
          = (x.q * y.q - x.p * y.p) ^ 2 + (x.p * y.q + y.p * x.q) ^ 2 := by ring
      rw [this, hp, hq]; norm_num
    have hx : x.p ^ 2 + x.q ^ 2 = 1 := by
      have h1 : 0 ≤ y.p ^ 2 + y.q ^ 2 := by positivity
      have h2 : 0 ≤ x.p ^ 2 + x.q ^ 2 := by positivity
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hn with h | h
      · exact h
      · omega
    have bp : -1 ≤ x.p ∧ x.p ≤ 1 := by constructor <;> nlinarith [sq_nonneg x.q]
    have bq : -1 ≤ x.q ∧ x.q ≤ 1 := by constructor <;> nlinarith [sq_nonneg x.p]
    obtain ⟨p, q⟩ := x
    simp only at bp bq hx
    obtain ⟨bp1, bp2⟩ := bp
    obtain ⟨bq1, bq2⟩ := bq
    interval_cases p <;> interval_cases q <;> simp_all [«ω», «_0», «-ω»]
  · rintro (h | h | h | h) <;> subst h
    · exact ⟨0, by decide⟩
    · exact ⟨«-ω», by decide⟩
    · exact ⟨«_0», by decide⟩
    · exact ⟨«ω», by decide⟩

end T
