import Mathlib.Tactic

/-!
# `T(p, q)`

The pair of cott-engine's `sibarum.cott.engine.ratio.T`, as docs/Traction-Model.md and docs/T-Design.md
state it. Two readings of one object: the ratio `p ÷ q`, and the point `q + p·i` in the plane.

Nothing is reduced and nothing is normalised. Equality is coordinate equality -- it is the structure's own
`=` -- so `T(1,2)` and `T(2,4)` are different pairs, `T(0,-1)` is not `T(0,1)`, and `T(0,0)` is a member
like any other.

## Zero and minus

* `0` is `T(0,1)` by default. It is not the only zero-magnitude pair -- `T(0,0)`, `T(1,0)` and the
  negatives are each the right one in some uses -- so the others stay reachable by name, and the literal is
  only the usual choice.
* `-x` is `T(-p, q)`: the numerator turns and the denominator stays. So `-0 = 0`, and `T(0,-1)` is `_0`,
  the bottom-negative zero, reached by a reciprocal rather than by a minus sign. `T(-p,-q)` is still here
  as the `⊕` inverse, by name.
-/

/-- `T(p, q)`: the ratio `p ÷ q`, and the point `q + p·i`. -/
@[ext]
structure T where
  /-- The numerator, and the imaginary part of the point. -/
  p : ℤ
  /-- The denominator, and the real part of the point. Zero here, where a rational's may not be. -/
  q : ℤ
  deriving DecidableEq, Repr

namespace T

/-! ## The nine named values, in ring order -/

/-- `0 = T(0,1)`, at 0°. -/
def «0» : T := ⟨0, 1⟩
/-- `1 = T(1,1)`, at 45°. The value-position unit. -/
def «1» : T := ⟨1, 1⟩
/-- `ω = T(1,0)`, at 90°. -/
def «ω» : T := ⟨1, 0⟩
/-- `_1 = T(1,-1)`, at 135°. -/
def «_1» : T := ⟨1, -1⟩
/-- `_0 = T(0,-1)`, at 180°: the bottom-negative zero. Zero has no top-negative, since `-0 = 0`. -/
def «_0» : T := ⟨0, -1⟩
/-- `-_1 = T(-1,-1)`, at −135°. -/
def «-_1» : T := ⟨-1, -1⟩
/-- `-ω = T(-1,0)`, at −90°. -/
def «-ω» : T := ⟨-1, 0⟩
/-- `-1 = T(-1,1)`, at −45°. -/
def «-1» : T := ⟨-1, 1⟩
/-- `0ω = T(0,0)`, at no angle. The unit of `⊕`. -/
def «0ω» : T := ⟨0, 0⟩

/-- The nine, in the order of T-Design.md's table. -/
def nine : List T := [«0», «1», «ω», «_1», «_0», «-_1», «-ω», «-1», «0ω»]

/-! ## The value position -/

/-- `T(a,b) + T(c,d) = T(ad+bc, bd)`: the value-position sum, cross-multiplying always. -/
def plus (x y : T) : T := ⟨x.p * y.q + y.p * x.q, x.q * y.q⟩

/-- `T(a,b) · T(c,d) = T(ac, bd)`: the value-position product. -/
def times (x y : T) : T := ⟨x.p * y.p, x.q * y.q⟩

instance : Add T := ⟨plus⟩
instance : Mul T := ⟨times⟩

/-- `T(b,a)`: the value-position inverse. Total -- `0` and `ω` are each other's reciprocal. -/
def reciprocal (x : T) : T := ⟨x.q, x.p⟩

/-- `T(a,b)^n = T(a^n, b^n)`: the product iterated. Natural `n` only, as in the engine, which refuses a
negative one rather than reduce. -/
def power (x : T) (n : ℕ) : T := ⟨x.p ^ n, x.q ^ n⟩

/-! ## The exponent position -/

/-- `T(a,b) ⊕ T(c,d) = T(a+c, b+d)`: the mediant. -/
def oplus (x y : T) : T := ⟨x.p + y.p, x.q + y.q⟩

/-- `T(a,b) ⊗ T(c,d) = T(ad+bc, bd−ac)`: the product of the points, which adds the angles. -/
def otimes (x y : T) : T := ⟨x.p * y.q + y.p * x.q, x.q * y.q - x.p * y.p⟩

@[inherit_doc] scoped infixl:65 " ⊕ " => oplus
@[inherit_doc] scoped infixl:70 " ⊗ " => otimes

/-- `T(-a,-b)`: the inverse under `⊕`. -/
def oplusInverse (x : T) : T := ⟨-x.p, -x.q⟩

/-- `T(-a,b)`: the inverse under `⊗`, which is the point conjugated. It is also `-x`. -/
def otimesInverse (x : T) : T := ⟨-x.p, x.q⟩

/-! ## The defaults -/

/-- `0` is `T(0,1)`. -/
instance : Zero T := ⟨«0»⟩

/-- `-x = T(-p, q)`. -/
instance : Neg T := ⟨otimesInverse⟩

@[simp] theorem zero_def : (0 : T) = ⟨0, 1⟩ := rfl
@[simp] theorem neg_def (x : T) : -x = ⟨-x.p, x.q⟩ := rfl

/-- `⊗` iterated `n` times, from the `⊗` unit `T(0,1)`. -/
def otimesPowNat (x : T) : ℕ → T
  | 0 => «0»
  | n + 1 => otimesPowNat x n ⊗ x

/-- The angle scaled `n` times. Total over `ℤ`: a negative exponent is the conjugate raised. -/
def otimesPower (x : T) : ℤ → T
  | .ofNat n => otimesPowNat x n
  | .negSucc n => otimesPowNat (otimesInverse x) (n + 1)

/-- The model's `z(T(a,b)) = T(2ab, b²−a²)`: the point squared. -/
def doubleAngle (x : T) : T := x ⊗ x

/-- The same tangent with a denominator that is not negative: the classical branch, asked for by name. -/
def principal (x : T) : T := if x.q < 0 then oplusInverse x else x

/-! ## Smoke checks against the engine's tests -/

example : reciprocal «0» = «ω» := rfl
example : «ω» ⊗ «ω» = «_0» := by decide
example : -(0 : T) = 0 := by decide
example : 0 * reciprocal «-1» = «_0» := by decide
example : -«ω» = «-ω» := by decide
example : -«_1» = «-_1» := by decide
example : «ω» + «ω» = «0ω» := by decide
example : doubleAngle ⟨1, 2⟩ = ⟨4, 3⟩ := by decide
example : otimesPower «ω» 4 = «0» := by decide

end T
