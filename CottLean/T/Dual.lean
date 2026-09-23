import CottLean.T.Gaussian
import CottLean.T.ValuePosition
import Mathlib.Algebra.DualNumber

/-!
# `⊕` with `+` is the dual numbers, and `⊕` with `*` is `ℤ × ℤ`

`⊕` adds the coordinates, and each of the three products distributes over it. So each product makes a
ring with `⊕`, and each ring is one of the three planar algebras over `ℤ`:

| product | its square of the unit on the axis | ring |
|---|---|---|
| `⊗` | `ω ⊗ ω = _0`, the `⊗` unit negated | `ℤ[i]`, `i² = −1` (`Gaussian`) |
| `+` | `ω + ω = 0ω`, the `⊕` unit | `ℤ[ε]`, `ε² = 0` |
| `*` | `T(1,0) * T(0,1) = 0ω` | `ℤ × ℤ` |

The dual map is the Gaussian map with `i` replaced by `ε`: `T(p, q) ↦ q + p·ε`. `T(a,b) + T(c,d) =
T(ad+bc, bd)` is `(b + aε)(d + cε) = bd + (ad+bc)ε`, term by term. The unit of `+` is `0 = T(0,1)`, the
same pair as the unit of `⊗`. `-x = T(-p, q)` is the dual conjugate here too, and `x + -x = T(0, q²)` is
its norm, as `x ⊗ -x = T(0, p²+q²)` is the Gaussian one.

The product map is `T(p, q) ↦ (p, q)`: `*` is coordinatewise already. Its unit is `1 = T(1,1)`.

So the two positions share `⊕`, not a product. The value position's `+` and the exponent position's `⊗`
are the parabolic and elliptic products on the one additive group `(T, ⊕)`, and `*` is the hyperbolic
one.
-/

namespace T

open TrivSqZeroExt DualNumber

/-! ## The dual map -/

/-- `T(p, q) ↦ q + p·ε`. -/
def toDual : T ≃ DualNumber ℤ where
  toFun x := (x.q, x.p)
  invFun z := ⟨z.snd, z.fst⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem toDual_fst (x : T) : (toDual x).fst = x.q := rfl
@[simp] theorem toDual_snd (x : T) : (toDual x).snd = x.p := rfl

theorem toDual_injective : Function.Injective toDual := toDual.injective

theorem toDual_oplus (x y : T) : toDual (x ⊕ y) = toDual x + toDual y := by
  ext <;> simp [oplus]

theorem toDual_plus (x y : T) : toDual (x + y) = toDual x * toDual y := by
  ext
  · simp
  · simp; ring

/-- `-x` is the dual conjugate. -/
theorem toDual_neg (x : T) : toDual (-x) = inl (toDual x).fst - inr (toDual x).snd := by
  ext <;> simp

theorem toDual_oplusInverse (x : T) : toDual (oplusInverse x) = -toDual x := by
  ext <;> simp [oplusInverse]

@[simp] theorem toDual_zero : toDual 0 = 1 := by ext <;> rfl
@[simp] theorem toDual_zeroOmega : toDual «0ω» = 0 := by ext <;> rfl
@[simp] theorem toDual_omega : toDual «ω» = ε := by ext <;> rfl

/-! ## The ring `⊕` and `+` make -/

/-- `T` with `⊕` for addition and `+` for multiplication. -/
def DualPosition : Type := T

namespace DualPosition

/-- Read a pair in the dual position. -/
def of : T ≃ DualPosition := Equiv.refl T
/-- And back. -/
def val : DualPosition ≃ T := Equiv.refl T

instance : Zero DualPosition := ⟨of «0ω»⟩
instance : One DualPosition := ⟨of 0⟩
instance : Add DualPosition := ⟨fun x y => of (val x ⊕ val y)⟩
instance : Mul DualPosition := ⟨fun x y => of (val x + val y)⟩
instance : Neg DualPosition := ⟨fun x => of (oplusInverse (val x))⟩
instance : Sub DualPosition := ⟨fun x y => x + -y⟩
instance : SMul ℕ DualPosition := ⟨fun n x => of ⟨n * (val x).p, n * (val x).q⟩⟩
instance : SMul ℤ DualPosition := ⟨fun n x => of ⟨n * (val x).p, n * (val x).q⟩⟩
instance : Pow DualPosition ℕ := ⟨fun x n => npowRec n x⟩
instance : NatCast DualPosition := ⟨fun n => of ⟨0, n⟩⟩
instance : IntCast DualPosition := ⟨fun n => of ⟨0, n⟩⟩

/-- The map, on the dual position. -/
def toD (x : DualPosition) : DualNumber ℤ := toDual (val x)

theorem toD_injective : Function.Injective toD := toDual_injective

theorem toD_mul (x y : DualPosition) : toD (x * y) = toD x * toD y := toDual_plus (val x) (val y)

theorem toD_pow (x : DualPosition) (n : ℕ) : toD (x ^ n) = toD x ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact toDual_zero
  | succ n ih =>
    change toD (npowRec n x * x) = _
    rw [toD_mul, pow_succ]
    exact congrArg (· * toD x) ih

instance : CommRing DualPosition :=
  toD_injective.commRing toD
    toDual_zeroOmega
    toDual_zero
    (fun x y => toDual_oplus (val x) (val y))
    toD_mul
    (fun x => toDual_oplusInverse (val x))
    (fun x y => by
      change toDual (val x ⊕ oplusInverse (val y)) = _
      rw [toDual_oplus, toDual_oplusInverse, sub_eq_add_neg]; rfl)
    (fun n x => by
      change toDual ⟨(n : ℤ) * (val x).p, (n : ℤ) * (val x).q⟩ = _
      ext <;> simp [toD])
    (fun n x => by
      change toDual ⟨n * (val x).p, n * (val x).q⟩ = _
      ext <;> simp [toD])
    toD_pow
    (fun n => by change toDual ⟨0, (n : ℤ)⟩ = _; ext <;> simp)
    (fun n => by change toDual ⟨0, n⟩ = _; ext <;> simp)

/-- `⊕` and `+` are `ℤ[ε]`, as a ring. -/
def ringEquiv : DualPosition ≃+* DualNumber ℤ where
  toEquiv := val.trans toDual
  map_mul' := toD_mul
  map_add' x y := toDual_oplus (val x) (val y)

end DualPosition

/-! ### In the docs' notation -/

/-- `(x ⊕ y) + z = (x + z) ⊕ (y + z)`, exactly on the coordinates. The `*` law needs a scale
(`distrib_scaled`); this one does not. -/
theorem oplus_plus (x y z : T) : (x ⊕ y) + z = ((x + z) ⊕ (y + z)) :=
  toDual_injective (by simp only [toDual_plus, toDual_oplus, add_mul])

/-- `ω` is the nilpotent: `ω + ω = 0ω`. -/
theorem omega_plus_omega : «ω» + «ω» = «0ω» :=
  toDual_injective (by rw [toDual_plus, toDual_omega, toDual_zeroOmega, eps_mul_eps])


/-! ## `⊕` and `*` -/

/-- `T(p, q) ↦ (p, q)`. -/
def toProd : T ≃ ℤ × ℤ where
  toFun x := (x.p, x.q)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem toProd_injective : Function.Injective toProd := toProd.injective

theorem toProd_oplus (x y : T) : toProd (x ⊕ y) = toProd x + toProd y := rfl
theorem toProd_times (x y : T) : toProd (x * y) = toProd x * toProd y := rfl
theorem toProd_oplusInverse (x : T) : toProd (oplusInverse x) = -toProd x := rfl
@[simp] theorem toProd_one : toProd «1» = 1 := rfl
@[simp] theorem toProd_zeroOmega : toProd «0ω» = 0 := rfl

/-- `T` with `⊕` for addition and `*` for multiplication. -/
def ProdPosition : Type := T

namespace ProdPosition

/-- Read a pair in the product position. -/
def of : T ≃ ProdPosition := Equiv.refl T
/-- And back. -/
def val : ProdPosition ≃ T := Equiv.refl T

instance : Zero ProdPosition := ⟨of «0ω»⟩
instance : One ProdPosition := ⟨of «1»⟩
instance : Add ProdPosition := ⟨fun x y => of (val x ⊕ val y)⟩
instance : Mul ProdPosition := ⟨fun x y => of (val x * val y)⟩
instance : Neg ProdPosition := ⟨fun x => of (oplusInverse (val x))⟩
instance : Sub ProdPosition := ⟨fun x y => x + -y⟩
instance : SMul ℕ ProdPosition := ⟨fun n x => of ⟨n * (val x).p, n * (val x).q⟩⟩
instance : SMul ℤ ProdPosition := ⟨fun n x => of ⟨n * (val x).p, n * (val x).q⟩⟩
instance : Pow ProdPosition ℕ := ⟨fun x n => of (power (val x) n)⟩
instance : NatCast ProdPosition := ⟨fun n => of ⟨n, n⟩⟩
instance : IntCast ProdPosition := ⟨fun n => of ⟨n, n⟩⟩

/-- The map, on the product position. -/
def toP (x : ProdPosition) : ℤ × ℤ := toProd (val x)

theorem toP_injective : Function.Injective toP := toProd_injective

instance : CommRing ProdPosition :=
  toP_injective.commRing toP rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun x y => by
      change toProd (val x ⊕ oplusInverse (val y)) = _
      rw [toProd_oplus, toProd_oplusInverse, sub_eq_add_neg]; rfl)
    (fun n x => by
      change ((n : ℤ) * (val x).p, (n : ℤ) * (val x).q) = _
      ext <;> simp [toP, toProd])
    (fun n x => by
      change (n * (val x).p, n * (val x).q) = _
      ext <;> simp [toP, toProd])
    (fun x n => by
      change ((val x).p ^ n, (val x).q ^ n) = _
      ext <;> simp [toP, toProd])
    (fun n => by change ((n : ℤ), (n : ℤ)) = _; ext <;> simp)
    (fun n => by change (n, n) = _; ext <;> simp)

/-- `⊕` and `*` are `ℤ × ℤ`, as a ring. -/
def ringEquiv : ProdPosition ≃+* ℤ × ℤ where
  toEquiv := val.trans toProd
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end ProdPosition

/-- `(x ⊕ y) * z = (x * z) ⊕ (y * z)`, exactly. -/
theorem oplus_times (x y z : T) : (x ⊕ y) * z = ((x * z) ⊕ (y * z)) :=
  toProd_injective (by simp only [toProd_times, toProd_oplus, add_mul])

end T
