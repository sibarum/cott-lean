import CottLean.T.Bases
import Mathlib.Algebra.DualNumber

/-!
# A coefficient and an order of zero

`Z(p, q) = p·0^q`. The coefficient is `p` and the order of the zero is `q`; a negative order is a power
of `ω`. So `k = Z(k, 0)`, `−1 = Z(−1, 0)`, `0 = Z(1, 1)`, `0ᵏ = Z(1, k)`, `ω = Z(1, −1)` and
`ωᵏ = Z(1, −k)`. Multiplying multiplies the coefficients and adds the orders.

## Why `L` cannot hold it

`Lmul` adds scales with fraction `+`, and fraction `+` is the dual-number product
(`T.toDual_plus`). On ratios, `(a : d) ↦ d + a·ε` takes `pairPlus` to `·` (`ratioDual_pairPlus`). Zero's
scale unit `−1 : 0` is `−ε` (`ratioDual_zeroScale`). So both of the exponent law's failures in `Bases` are
`ε² = 0`:

* `zeroScale_absorbs`: `(−1 : 0) + (a : 1) = (−1 : 0)`. It is `−ε·(1 + a·ε) = −ε − a·ε²`, and the
  coefficient's scale `a` sits in the `ε²` term the dual numbers drop.
* `zeroScale_sq`: `(−1 : 0) + (−1 : 0) = (0 : 0)`. It is `(−ε)² = ε² = 0`, so two zeros make `0ω`.

So `L`'s scale coordinate cannot hold a coefficient and an order of zero. `T/ZeroAlgebra.lean` derives `Z`'s
operations, its logarithm `E` and where traction's products hold it, and `T/Residual.lean` keeps a
coefficient `0` from ever being reached.

## What it keeps

* `zero_mul_omega`: `0·ω = 1`, where the wheel gives `0ω`.
* `negZero_ne_zero`: with the sign in the coefficient, `−0 = Z(−1, 1)` is not `0`. Traction's `−x =
  T(−p, q)` gives `−0 = 0` (`T.neg_zero_eq`), so `Z`'s minus is not traction's `−`.
* `negOne_ne_zeroPow`: `−1` is no power of zero.
-/

namespace T.Unquotiented

open TrivSqZeroExt DualNumber

/-! ## The scale coordinate of `L` is the dual numbers -/

/-- A ratio `a : d` as the dual number `d + a·ε`. -/
def ratioDual (x : Ratio) : DualNumber ℝ := inl x.2 + inr x.1

/-- Fraction `+` on ratios is the dual-number product. -/
theorem ratioDual_pairPlus (x y : Ratio) : ratioDual (pairPlus x y) = ratioDual x * ratioDual y := by
  ext <;> simp [ratioDual, pairPlus]; ring

theorem ratioDual_injective : Function.Injective ratioDual := by
  intro x y h
  exact Prod.ext (by simpa [ratioDual] using congrArg TrivSqZeroExt.snd h)
    (by simpa [ratioDual] using congrArg TrivSqZeroExt.fst h)

/-- Zero's scale unit `−1 : 0` is `−ε`. -/
theorem ratioDual_zeroScale : ratioDual Base.zero.scaleUnit = -ε := by
  ext <;> simp [ratioDual, Base.zero]

/-- A finite scale `a : 1` is `1 + a·ε`. -/
theorem ratioDual_finite (a : ℝ) : ratioDual (a, 1) = 1 + a • ε := by
  ext <;> simp [ratioDual]

/-- Zero's scale absorbs a finite one: the coefficient's scale is lost. -/
theorem zeroScale_absorbs (a : ℝ) : pairPlus Base.zero.scaleUnit (a, 1) = Base.zero.scaleUnit := by
  simp [pairPlus, Base.zero]

/-- Because it sits in the `ε²` term: `−ε·(1 + a·ε) = −ε`. -/
theorem zeroScale_absorbs_dual (a : ℝ) : (-ε : DualNumber ℝ) * (1 + a • ε) = -ε := by
  rw [mul_add, mul_one, mul_smul_comm, neg_mul, eps_mul_eps, neg_zero, smul_zero, add_zero]

/-- Two zeros' scales make `0 : 0`. -/
theorem zeroScale_sq : pairPlus Base.zero.scaleUnit Base.zero.scaleUnit = (0, 0) := by
  simp [pairPlus, Base.zero]

/-- Because `(−ε)² = ε² = 0`. -/
theorem zeroScale_sq_dual : (-ε : DualNumber ℝ) * -ε = 0 := by
  rw [neg_mul_neg, eps_mul_eps]

end T.Unquotiented

namespace T.ZeroScale

/-! ## `Z` -/

/-- `Z(p, q) = p·0^q`: a coefficient and an order of zero. -/
@[ext]
structure Z where
  /-- The coefficient. -/
  p : ℤ
  /-- The order of the zero; negative for a power of `ω`. -/
  q : ℤ
  deriving DecidableEq

namespace Z

instance : Mul Z := ⟨fun x y => ⟨x.p * y.p, x.q + y.q⟩⟩
instance : One Z := ⟨⟨1, 0⟩⟩

@[simp] theorem mul_def (x y : Z) : x * y = ⟨x.p * y.p, x.q + y.q⟩ := rfl
@[simp] theorem one_def : (1 : Z) = ⟨1, 0⟩ := rfl

instance : CommMonoid Z where
  mul_assoc x y z := by ext <;> simp [mul_assoc, add_assoc]
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  mul_comm x y := by ext <;> simp [mul_comm, add_comm]

/-- The integer `k`, of order `0`. -/
def ofInt (k : ℤ) : Z := ⟨k, 0⟩
/-- `0 = Z(1, 1)`. -/
def zero : Z := ⟨1, 1⟩
/-- `ω = Z(1, −1)`. -/
def omega : Z := ⟨1, -1⟩
/-- `−0 = Z(−1, 1)`. -/
def negZero : Z := ⟨-1, 1⟩

/-- The power of a monomial multiplies its order. -/
theorem pow_def (x : Z) (k : ℕ) : x ^ k = ⟨x.p ^ k, k * x.q⟩ := by
  induction k with
  | zero => ext <;> simp
  | succ k ih => rw [pow_succ, ih]; ext <;> simp [pow_succ]; ring

theorem zero_pow (k : ℕ) : zero ^ k = ⟨1, k⟩ := by simp [pow_def, zero]

theorem omega_pow (k : ℕ) : omega ^ k = ⟨1, -k⟩ := by simp [pow_def, omega]

/-- `0·ω = 1`, where the wheel gives `0ω`. -/
theorem zero_mul_omega : zero * omega = 1 := by ext <;> simp [zero, omega]

theorem ofInt_mul (a b : ℤ) : ofInt (a * b) = ofInt a * ofInt b := by ext <;> simp [ofInt]

theorem negOne_eq : ofInt (-1) = ⟨-1, 0⟩ := rfl

/-- `−0` is not `0`: the sign is in the coefficient. -/
theorem negZero_ne_zero : negZero ≠ zero := by decide

theorem negZero_eq : negZero = ofInt (-1) * zero := by ext <;> simp [negZero, ofInt, zero]

/-- Traction's own `−` fixes `0`. -/
theorem _root_.T.neg_zero_eq : -(0 : T) = 0 := by rfl

/-- `−1` is no power of zero, nor of `ω`. -/
theorem negOne_ne_zeroPow (k : ℤ) : ofInt (-1) ≠ ⟨1, k⟩ := by
  intro h; have := congrArg Z.p h; simp [ofInt] at this

end Z

end T.ZeroScale
