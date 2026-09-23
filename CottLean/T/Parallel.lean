import CottLean.T.Velocity

/-!
# The parallel sum

The power sum `(xⁿ + yⁿ)^(1/n)` stays on the integer pairs at two exponents. `n = 1` is `+`, and `n = −1`
is the parallel sum, the rule for resistors in parallel:

```
x ∥ y = 1 / (1/x + 1/y),     T(a,b) ∥ T(c,d) = T(ac, ad + bc)
```

It is `+` carried through the reciprocal (`reciprocal_par`), so everything `+` has, `∥` has with the
coordinates swapped:

* `(T, ⊕, ∥)` is the dual numbers again, by `T(p, q) ↦ p + q·ε` (`ParPosition.ringEquiv`), and the
  reciprocal is a ring isomorphism from `(T, ⊕, +)` onto it (`ParPosition.reciprocalEquiv`).
* `ω` is its unit: an open circuit changes nothing (`par_omega`). `0` is its nilpotent: `0 ∥ 0 = 0ω`.
* The other operand comes back exactly when the known one has a non-zero numerator
  (`par_recoverable_iff`), as `+` needs a non-zero denominator.

## The wheel's two formulas

Classically `1/(1/x + 1/y)` and `xy/(x + y)` are the same. In the value position they are not.
The first is `∥` exactly, and the second is `∥` with both coordinates multiplied by `x.q · y.q`
(`parAdd_eq`), the factor `tanAdd` and `velAdd` carry too. So the second collapses to `0ω` against an
open circuit, where `x ∥ y` is `y` scaled (`open_contrast`).
-/

namespace T

/-! ## The operation -/

/-- `T(a,b) ∥ T(c,d) = T(ac, ad + bc)`: the parallel sum. -/
def par (x y : T) : T := ⟨x.p * y.p, x.p * y.q + y.p * x.q⟩

@[inherit_doc] scoped infixl:65 " ∥ " => par

/-- `∥` is `+` carried through the reciprocal. -/
theorem reciprocal_par (x y : T) : reciprocal (x ∥ y) = reciprocal x + reciprocal y := by
  ext <;> simp [par, reciprocal]; ring

theorem par_eq (x y : T) : x ∥ y = reciprocal (reciprocal x + reciprocal y) := by
  rw [← reciprocal_par, reciprocal_reciprocal]

/-- The resistors `1 ∥ 1` are `1/2`. -/
example : «1» ∥ «1» = ⟨1, 2⟩ := by decide

/-! ## The ring `⊕` and `∥` make -/

/-- `T(p, q) ↦ p + q·ε`: the dual map, after the reciprocal. -/
def toParDual : T ≃ DualNumber ℤ :=
  (⟨reciprocal, reciprocal, fun _ => rfl, fun _ => rfl⟩ : T ≃ T).trans toDual

@[simp] theorem toParDual_fst (x : T) : (toParDual x).fst = x.p := rfl
@[simp] theorem toParDual_snd (x : T) : (toParDual x).snd = x.q := rfl

theorem toParDual_oplus (x y : T) : toParDual (x ⊕ y) = toParDual x + toParDual y := by
  ext <;> simp [oplus]

theorem toParDual_par (x y : T) : toParDual (x ∥ y) = toParDual x * toParDual y := by
  change toDual (reciprocal (x ∥ y)) = toDual (reciprocal x) * toDual (reciprocal y)
  rw [reciprocal_par, toDual_plus]

theorem toParDual_oplusInverse (x : T) : toParDual (oplusInverse x) = -toParDual x := by
  ext <;> simp [oplusInverse]

@[simp] theorem toParDual_omega : toParDual «ω» = 1 := by ext <;> rfl
@[simp] theorem toParDual_zeroOmega : toParDual «0ω» = 0 := by ext <;> rfl

/-- `T` with `⊕` for addition and `∥` for multiplication. -/
def ParPosition : Type := T

namespace ParPosition

/-- Read a pair in the parallel position. -/
def of : T ≃ ParPosition := Equiv.refl T
/-- And back. -/
def val : ParPosition ≃ T := Equiv.refl T

instance : Zero ParPosition := ⟨of «0ω»⟩
instance : One ParPosition := ⟨of «ω»⟩
instance : Add ParPosition := ⟨fun x y => of (val x ⊕ val y)⟩
instance : Mul ParPosition := ⟨fun x y => of (val x ∥ val y)⟩
instance : Neg ParPosition := ⟨fun x => of (oplusInverse (val x))⟩
instance : Sub ParPosition := ⟨fun x y => x + -y⟩
instance : SMul ℕ ParPosition := ⟨fun n x => of ⟨n * (val x).p, n * (val x).q⟩⟩
instance : SMul ℤ ParPosition := ⟨fun n x => of ⟨n * (val x).p, n * (val x).q⟩⟩
instance : Pow ParPosition ℕ := ⟨fun x n => npowRec n x⟩
instance : NatCast ParPosition := ⟨fun n => of ⟨n, 0⟩⟩
instance : IntCast ParPosition := ⟨fun n => of ⟨n, 0⟩⟩

/-- The map, on the parallel position. -/
def toP (x : ParPosition) : DualNumber ℤ := toParDual (val x)

theorem toP_injective : Function.Injective toP := toParDual.injective

theorem toP_mul (x y : ParPosition) : toP (x * y) = toP x * toP y := toParDual_par (val x) (val y)

theorem toP_pow (x : ParPosition) (n : ℕ) : toP (x ^ n) = toP x ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact toParDual_omega
  | succ n ih =>
    change toP (npowRec n x * x) = _
    rw [toP_mul, pow_succ]
    exact congrArg (· * toP x) ih

instance : CommRing ParPosition :=
  toP_injective.commRing toP
    toParDual_zeroOmega
    toParDual_omega
    (fun x y => toParDual_oplus (val x) (val y))
    toP_mul
    (fun x => toParDual_oplusInverse (val x))
    (fun x y => by
      change toParDual (val x ⊕ oplusInverse (val y)) = _
      rw [toParDual_oplus, toParDual_oplusInverse, sub_eq_add_neg]; rfl)
    (fun n x => by
      change toParDual ⟨(n : ℤ) * (val x).p, (n : ℤ) * (val x).q⟩ = _
      ext <;> simp [toP])
    (fun n x => by
      change toParDual ⟨n * (val x).p, n * (val x).q⟩ = _
      ext <;> simp [toP])
    toP_pow
    (fun n => by change toParDual ⟨(n : ℤ), 0⟩ = _; ext <;> simp)
    (fun n => by change toParDual ⟨n, 0⟩ = _; ext <;> simp)

/-- `⊕` and `∥` are `ℤ[ε]`, as a ring. -/
def ringEquiv : ParPosition ≃+* DualNumber ℤ where
  toEquiv := val.trans toParDual
  map_mul' := toP_mul
  map_add' x y := toParDual_oplus (val x) (val y)

/-- The reciprocal takes `⊕` and `+` onto `⊕` and `∥`. -/
def reciprocalEquiv : DualPosition ≃+* ParPosition where
  toFun x := of (reciprocal (DualPosition.val x))
  invFun x := DualPosition.of (reciprocal (val x))
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    change reciprocal (DualPosition.val x + DualPosition.val y)
      = reciprocal (DualPosition.val x) ∥ reciprocal (DualPosition.val y)
    exact (par_eq (reciprocal (DualPosition.val x)) (reciprocal (DualPosition.val y))).symm
  map_add' _ _ := rfl

end ParPosition

/-! ### In the docs' notation -/

/-- `(x ⊕ y) ∥ z = (x ∥ z) ⊕ (y ∥ z)`, exactly. -/
theorem oplus_par (x y z : T) : (x ⊕ y) ∥ z = ((x ∥ z) ⊕ (y ∥ z)) :=
  toParDual.injective (by simp only [toParDual_par, toParDual_oplus, add_mul])

theorem par_comm (x y : T) : x ∥ y = y ∥ x := by
  ext <;> simp only [par] <;> ring

theorem par_assoc (x y z : T) : x ∥ y ∥ z = x ∥ (y ∥ z) :=
  toParDual.injective (by simp only [toParDual_par, mul_assoc])

/-- An open circuit changes nothing: `ω` is the unit of `∥`. -/
theorem par_omega (x : T) : x ∥ «ω» = x := by
  ext <;> simp [par, «ω»]

/-- A short circuit is nilpotent: `0 ∥ 0 = 0ω`. -/
theorem zero_par_zero : (0 : T) ∥ 0 = «0ω» := by decide

/-- Against a short circuit, the answer is a zero: the residue `T(0, p)` (`Residue`). -/
theorem par_zero (x : T) : x ∥ 0 = ⟨0, x.p⟩ := by
  ext <;> simp [par]

/-! ## What `∥` can undo -/

/-- Against `k`, the other operand comes back exactly when `k` has a non-zero numerator. -/
theorem par_recoverable_iff (k : T) : Recoverable par k ↔ k.p ≠ 0 := by
  have key : ∀ a a', a ∥ k = a' ∥ k ↔ reciprocal a + reciprocal k = reciprocal a' + reciprocal k :=
    fun a a' => by
      rw [← reciprocal_par, ← reciprocal_par]
      exact ⟨congrArg reciprocal, fun h => by simpa [reciprocal_reciprocal] using congrArg reciprocal h⟩
  rw [← show (reciprocal k).q ≠ 0 ↔ k.p ≠ 0 from Iff.rfl, ← plus_recoverable_iff]
  constructor
  · intro h b b' hb
    have := h (reciprocal b) (reciprocal b') ((key _ _).mpr (by simpa [reciprocal_reciprocal] using hb))
    simpa [reciprocal_reciprocal] using congrArg reciprocal this
  · intro h a a' ha
    have := h _ _ ((key a a').mp ha)
    simpa [reciprocal_reciprocal] using congrArg reciprocal this

/-! ## The wheel's `xy / (x + y)` -/

/-- `xy / (x + y)`, in the value position's operations. -/
def parAdd (x y : T) : T := (x * y) * reciprocal (x + y)

/-- It is `∥` with both coordinates multiplied by `x.q · y.q`. -/
theorem parAdd_eq (x y : T) : parAdd x y = scale (x.q * y.q) (x ∥ y) := by
  ext <;> simp only [parAdd, add_def, mul_def, reciprocal, scale, par]; ring

/-- Against an open circuit, `∥` gives the other resistor scaled. -/
theorem par_of_q_eq_zero {x : T} (hq : x.q = 0) (y : T) : x ∥ y = scale x.p y := by
  ext <;> simp [par, scale, hq]

/-- Against an open circuit, `xy / (x + y)` forgets the other resistor, and `∥` forgets nothing. -/
theorem open_contrast {x : T} (hq : x.q = 0) (hx : x ≠ «0ω») :
    (∀ y, parAdd x y = «0ω») ∧ (∀ y y', x ∥ y = x ∥ y' → y = y') := by
  have hp : x.p ≠ 0 := fun hp => hx (by ext <;> simp [hp, hq, «0ω»])
  refine ⟨fun y => ?_, fun y y' h => ?_⟩
  · rw [parAdd_eq, hq, zero_mul]; ext <;> simp [scale, «0ω»]
  · exact (par_recoverable_iff x).mpr hp y y' (by rw [par_comm y, par_comm y']; exact h)

example : «ω» ∥ «1» = «1» := by decide
example : parAdd «ω» «1» = «0ω» := by decide

end T
