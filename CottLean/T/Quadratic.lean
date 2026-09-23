import CottLean.T.Dual
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# One product for every quadratic ring

`⊗` and `+` differ only in the square of `ω`. Reading `T(p, q)` as `q + p·ω`, both come from one
formula with two integer parameters, where `ω² = a + b·ω`:

```
qtimes a b (T(p,q)) (T(r,s)) = T(ps + rq + b·pr, qs + a·pr)
```

`(T, ⊕, qtimes a b)` is Mathlib's `QuadraticAlgebra ℤ a b` for every `a` and `b` (`QuadPosition.ringEquiv`),
by the same map every time. Every ring that is free of rank two over ℤ, with `1` in a basis, is one of these.

| `a` | `b` | `ω²` | ring | discriminant `b² + 4a` | in T |
|---|---|---|---|---|---|
| `−1` | `0` | `−1` | Gaussian integers ℤ[i] | `−4` | `⊗` (`otimes_eq_qtimes`) |
| `0` | `0` | `0` | dual numbers ℤ[ε] | `0` | `+` (`plus_eq_qtimes`) |
| `1` | `0` | `1` | split-complex integers ℤ[j] | `4` | `⊚` (`splitTimes`) |
| `0` | `1` | `ω` | ℤ × ℤ | `1` | `*`, by another basis |
| `−1` | `−1` | `−1 − ω` | Eisenstein integers ℤ[ζ₃] | `−3` | `qtimes (-1) (-1)` |

The complex, dual and split-complex numbers are the three `b = 0` rows, and `a` is the sign of `ω²`.

`*` is the one row that needs another basis. Its unit is `1 = T(1,1)` rather than `0 = T(0,1)`, and `ω` is
idempotent under it (`ω * ω = ω`), so it is read as `q + (p − q)·ω` (`ProdPosition.quadEquiv`). Over ℤ,
the split-complex integers are not `ℤ × ℤ`: they have discriminant `4`, not `1`, and no idempotent but `0`
and `1` (`split_not_prod`). The two agree only once `2` is invertible.
-/

namespace T

/-! ## The product -/

/-- `T(p,q) · T(r,s)` with `ω² = a + b·ω`. -/
def qtimes (a b : ℤ) (x y : T) : T :=
  ⟨x.p * y.q + y.p * x.q + b * x.p * y.p, x.q * y.q + a * x.p * y.p⟩

/-- `⊗` is the case `ω² = −1`. -/
theorem otimes_eq_qtimes (x y : T) : x ⊗ y = qtimes (-1) 0 x y := by
  ext <;> simp [otimes, qtimes]; ring

/-- `+` is the case `ω² = 0`. -/
theorem plus_eq_qtimes (x y : T) : x + y = qtimes 0 0 x y := by
  ext <;> simp [qtimes]

/-- The split-complex product, the case `ω² = 1`: `T(p,q) · T(r,s) = T(ps + rq, qs + pr)`. -/
def splitTimes (x y : T) : T := qtimes 1 0 x y

@[inherit_doc] scoped infixl:70 " ⊚ " => splitTimes

/-- Under the three `b = 0` products `ω` squares to `−1`, `0` and `1` of each ring: `_0`, `0ω` and `0`. -/
example : «ω» ⊗ «ω» = «_0» ∧ «ω» + «ω» = «0ω» ∧ «ω» ⊚ «ω» = 0 := by decide

/-! ## The map -/

/-- `T(p, q) ↦ q + p·ω`. -/
def toQuad (a b : ℤ) : T ≃ QuadraticAlgebra ℤ a b where
  toFun x := ⟨x.q, x.p⟩
  invFun z := ⟨z.im, z.re⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem toQuad_re (a b : ℤ) (x : T) : (toQuad a b x).re = x.q := rfl
@[simp] theorem toQuad_im (a b : ℤ) (x : T) : (toQuad a b x).im = x.p := rfl

theorem toQuad_oplus (a b : ℤ) (x y : T) : toQuad a b (x ⊕ y) = toQuad a b x + toQuad a b y := by
  ext <;> simp [oplus]

theorem toQuad_qtimes (a b : ℤ) (x y : T) :
    toQuad a b (qtimes a b x y) = toQuad a b x * toQuad a b y := by
  ext <;> simp [qtimes]; ring

theorem toQuad_oplusInverse (a b : ℤ) (x : T) : toQuad a b (oplusInverse x) = -toQuad a b x := by
  ext <;> simp [oplusInverse]

@[simp] theorem toQuad_zero (a b : ℤ) : toQuad a b 0 = 1 := by ext <;> rfl
@[simp] theorem toQuad_zeroOmega (a b : ℤ) : toQuad a b «0ω» = 0 := by ext <;> rfl
@[simp] theorem toQuad_omega (a b : ℤ) : toQuad a b «ω» = QuadraticAlgebra.omega := by ext <;> rfl

/-! ## The ring -/

/-- `T` with `⊕` for addition and `qtimes a b` for multiplication. -/
def QuadPosition (_a _b : ℤ) : Type := T

namespace QuadPosition

variable (a b : ℤ)

/-- Read a pair in the quadratic position. -/
def of : T ≃ QuadPosition a b := Equiv.refl T
/-- And back. -/
def val : QuadPosition a b ≃ T := Equiv.refl T

instance : Zero (QuadPosition a b) := ⟨of a b «0ω»⟩
instance : One (QuadPosition a b) := ⟨of a b 0⟩
instance : Add (QuadPosition a b) := ⟨fun x y => of a b (val a b x ⊕ val a b y)⟩
instance : Mul (QuadPosition a b) := ⟨fun x y => of a b (qtimes a b (val a b x) (val a b y))⟩
instance : Neg (QuadPosition a b) := ⟨fun x => of a b (oplusInverse (val a b x))⟩
instance : Sub (QuadPosition a b) := ⟨fun x y => x + -y⟩
instance : SMul ℕ (QuadPosition a b) := ⟨fun n x => of a b ⟨n * (val a b x).p, n * (val a b x).q⟩⟩
instance : SMul ℤ (QuadPosition a b) := ⟨fun n x => of a b ⟨n * (val a b x).p, n * (val a b x).q⟩⟩
instance : Pow (QuadPosition a b) ℕ := ⟨fun x n => npowRec n x⟩
instance : NatCast (QuadPosition a b) := ⟨fun n => of a b ⟨0, n⟩⟩
instance : IntCast (QuadPosition a b) := ⟨fun n => of a b ⟨0, n⟩⟩

/-- The map, on the quadratic position. -/
def toQ (x : QuadPosition a b) : QuadraticAlgebra ℤ a b := toQuad a b (val a b x)

theorem toQ_injective : Function.Injective (toQ a b) := (toQuad a b).injective

theorem toQ_mul (x y : QuadPosition a b) : toQ a b (x * y) = toQ a b x * toQ a b y :=
  toQuad_qtimes a b (val a b x) (val a b y)

theorem toQ_pow (x : QuadPosition a b) (n : ℕ) : toQ a b (x ^ n) = toQ a b x ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact toQuad_zero a b
  | succ n ih =>
    change toQ a b (npowRec n x * x) = _
    rw [toQ_mul, pow_succ]
    exact congrArg (· * toQ a b x) ih

instance : CommRing (QuadPosition a b) :=
  (toQ_injective a b).commRing (toQ a b)
    (toQuad_zeroOmega a b)
    (toQuad_zero a b)
    (fun x y => toQuad_oplus a b (val a b x) (val a b y))
    (toQ_mul a b)
    (fun x => toQuad_oplusInverse a b (val a b x))
    (fun x y => by
      change toQuad a b (val a b x ⊕ oplusInverse (val a b y)) = _
      rw [toQuad_oplus, toQuad_oplusInverse, sub_eq_add_neg]; rfl)
    (fun n x => by
      change toQuad a b ⟨(n : ℤ) * (val a b x).p, (n : ℤ) * (val a b x).q⟩ = _
      ext <;> simp [toQ])
    (fun n x => by
      change toQuad a b ⟨n * (val a b x).p, n * (val a b x).q⟩ = _
      ext <;> simp [toQ])
    (toQ_pow a b)
    (fun n => by change toQuad a b ⟨0, (n : ℤ)⟩ = _; ext <;> simp)
    (fun n => by change toQuad a b ⟨0, n⟩ = _; ext <;> simp)

/-- `⊕` and `qtimes a b` are `QuadraticAlgebra ℤ a b`, as a ring. -/
def ringEquiv : QuadPosition a b ≃+* QuadraticAlgebra ℤ a b where
  toEquiv := (val a b).trans (toQuad a b)
  map_mul' := toQ_mul a b
  map_add' x y := toQuad_oplus a b (val a b x) (val a b y)

end QuadPosition

/-! ## `*`, in the basis `1, ω` -/

/-- `T(p, q) ↦ q + (p − q)·ω`, with `ω² = ω`. -/
def toQuadProd : T ≃ QuadraticAlgebra ℤ 0 1 where
  toFun x := ⟨x.q, x.p - x.q⟩
  invFun z := ⟨z.im + z.re, z.re⟩
  left_inv _ := by ext <;> simp
  right_inv _ := by ext <;> simp

theorem toQuadProd_oplus (x y : T) : toQuadProd (x ⊕ y) = toQuadProd x + toQuadProd y := by
  ext <;> simp [toQuadProd, oplus]; ring

theorem toQuadProd_times (x y : T) : toQuadProd (x * y) = toQuadProd x * toQuadProd y := by
  ext <;> simp [toQuadProd]; ring

/-- `ω` is idempotent under `*`, as `ω` is in `QuadraticAlgebra ℤ 0 1`. -/
theorem omega_times_omega : «ω» * «ω» = «ω» := by decide

/-- `⊕` and `*` are `QuadraticAlgebra ℤ 0 1`, as a ring. -/
def ProdPosition.quadEquiv : ProdPosition ≃+* QuadraticAlgebra ℤ 0 1 where
  toEquiv := ProdPosition.val.trans toQuadProd
  map_mul' x y := toQuadProd_times (ProdPosition.val x) (ProdPosition.val y)
  map_add' x y := toQuadProd_oplus (ProdPosition.val x) (ProdPosition.val y)

/-! ## The split-complex integers are not `ℤ × ℤ` -/

/-- The only idempotents of ℤ[j] are `0` and `1`: `(x + yj)² = x + yj` forces `2xy = y`, so `y = 0`. -/
theorem split_idempotent {z : QuadraticAlgebra ℤ 1 0} (h : z * z = z) : z = 0 ∨ z = 1 := by
  have hre : z.re * z.re + z.im * z.im = z.re := by simpa using congrArg QuadraticAlgebra.re h
  have him : z.re * z.im + z.im * z.re = z.im := by simpa using congrArg QuadraticAlgebra.im h
  have hy : z.im = 0 := by
    by_contra hne
    have : 2 * z.re = 1 := by
      have : (2 * z.re - 1) * z.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact absurd h hne
    omega
  rw [hy] at hre
  have : z.re * (z.re - 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h1
  · left; exact QuadraticAlgebra.ext h0 hy
  · right; exact QuadraticAlgebra.ext (by rw [QuadraticAlgebra.re_one]; linarith) hy

/-- Over ℤ, `ω² = 1` and `ω² = ω` give different rings: `ℤ × ℤ` has the idempotent `(1, 0)`. -/
theorem split_not_prod : IsEmpty (QuadraticAlgebra ℤ 1 0 ≃+* ℤ × ℤ) := by
  refine ⟨fun e => ?_⟩
  have hi : e.symm (1, 0) * e.symm (1, 0) = e.symm (1, 0) := by
    rw [← map_mul]; rfl
  rcases split_idempotent hi with h | h
  · have := congrArg e h; simp at this
  · have := congrArg e h; simp at this

end T
