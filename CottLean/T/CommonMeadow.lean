import CottLean.T.Wheel

/-!
# T and the rational common meadow

A common meadow (Bergstra and Ponse, *Division by zero in common meadows*) is a field with a total
inverse, where `1/0` is an error element `a` that absorbs every operation. The rational one, `ℚₐ`, is
`ℚ` with `a` added, and it is modelled here as `Option ℚ` with `none` as `a`.

An involutive meadow instead sets `1/0 = 0`, keeping `(ℚ, +)` as its addition.

## What is proved

* `toQa_surjective`, `toQa_plus`, `toQa_times`, `toQa_neg`: the map sending `T(p,q)` to `p/q` where
  `q ≠ 0`, and to `a` where `q = 0`, is onto `ℚₐ` and respects `+`, `*` and `-` exactly.
* `toQa_reciprocal` / `toQa_reciprocal_quarterTurn`: it respects the reciprocal everywhere except at the
  quarter turns `T(p, 0)`, `p ≠ 0`. There T says `1/ω = 0` and the common meadow says `a⁻¹ = a`.
* `no_surjective_hom_Qa`: no map from T onto `ℚₐ` respects all four. The obstruction is forced:
  `0ω` must go to `a`, so `ω` must go to `a`, so `1/ω = 0` must go to `a⁻¹ = a`, but `0` goes to `0`.
* `no_surjective_add_hom_Q`: no map from T onto `ℚ` even respects `+`, since `0ω` would have to absorb
  under ordinary addition. So there is no homomorphism from T onto an involutive meadow.

The literature records the relationship as open: Bergstra and Ponse write that common meadows are
related to wheels but that they "have not yet found a structural connection". This file does not claim
to settle that. It records one: everything but the inverse of a quarter turn.
-/

namespace T

/-- The rational common meadow `ℚₐ`: `some r` is a rational and `none` is the error `a`. -/
abbrev Qa := Option ℚ

namespace Qa

/-- `+`, with `a` absorbing. -/
def add : Qa → Qa → Qa
  | some x, some y => some (x + y)
  | _, _ => none

/-- `·`, with `a` absorbing. -/
def mul : Qa → Qa → Qa
  | some x, some y => some (x * y)
  | _, _ => none

/-- `-`, with `a` absorbing. -/
def neg : Qa → Qa
  | some x => some (-x)
  | none => none

/-- The inverse: `0⁻¹ = a`, and `a⁻¹ = a`. -/
def inv : Qa → Qa
  | some x => if x = 0 then none else some x⁻¹
  | none => none

end Qa

/-- `T(p,q) ↦ p/q` where `q ≠ 0`, and `a` where `q = 0`. -/
def toQa (x : T) : Qa := if x.q = 0 then none else some ((x.p : ℚ) / x.q)

theorem toQa_surjective : Function.Surjective toQa := by
  rintro (_ | r)
  · exact ⟨«0ω», by simp [toQa, «0ω»]⟩
  · refine ⟨⟨r.num, r.den⟩, ?_⟩
    have hd : ((r.den : ℤ)) ≠ 0 := by exact_mod_cast r.den_nz
    simp only [toQa, hd, if_false]
    congr 1
    push_cast
    exact Rat.num_div_den r

theorem toQa_plus (x y : T) : toQa (x + y) = Qa.add (toQa x) (toQa y) := by
  by_cases hx : x.q = 0 <;> by_cases hy : y.q = 0 <;>
    simp [toQa, Qa.add, hx, hy]
  have hx' : (x.q : ℚ) ≠ 0 := by exact_mod_cast hx
  have hy' : (y.q : ℚ) ≠ 0 := by exact_mod_cast hy
  field_simp

theorem toQa_times (x y : T) : toQa (x * y) = Qa.mul (toQa x) (toQa y) := by
  by_cases hx : x.q = 0 <;> by_cases hy : y.q = 0 <;>
    simp [toQa, Qa.mul, hx, hy, div_mul_div_comm]

theorem toQa_neg (x : T) : toQa (-x) = Qa.neg (toQa x) := by
  by_cases hx : x.q = 0 <;> simp [toQa, Qa.neg, hx, neg_div]

/-- Away from the quarter turns, the reciprocal is the common meadow's inverse. -/
theorem toQa_reciprocal {x : T} (h : x.q ≠ 0 ∨ x.p = 0) :
    toQa (reciprocal x) = Qa.inv (toQa x) := by
  by_cases hq : x.q = 0 <;> by_cases hp : x.p = 0
  · simp [toQa, Qa.inv, reciprocal, hq, hp]
  · exact absurd (h.resolve_left (not_not.mpr hq)) hp
  · simp [toQa, Qa.inv, reciprocal, hq, hp]
  · have hp' : (x.p : ℚ) ≠ 0 := by exact_mod_cast hp
    have hq' : (x.q : ℚ) ≠ 0 := by exact_mod_cast hq
    simp [toQa, Qa.inv, reciprocal, hq, hp, hp', hq', inv_div]

/-- At a quarter turn it is not: T answers `0`, and the common meadow answers `a`. -/
theorem toQa_reciprocal_quarterTurn {x : T} (hq : x.q = 0) (hp : x.p ≠ 0) :
    toQa (reciprocal x) = some 0 ∧ Qa.inv (toQa x) = none := by
  simp [toQa, Qa.inv, reciprocal, hq, hp]

/-- No map onto `ℚₐ` respects `+`, `*` and the reciprocal together. -/
theorem no_surjective_hom_Qa :
    ¬ ∃ ψ : T → Qa, Function.Surjective ψ ∧ (∀ x y, ψ (x + y) = Qa.add (ψ x) (ψ y)) ∧
      (∀ x y, ψ (x * y) = Qa.mul (ψ x) (ψ y)) ∧ (∀ x, ψ (reciprocal x) = Qa.inv (ψ x)) := by
  rintro ⟨ψ, hs, hadd, hmul, hinv⟩
  -- `0` is the identity of `+`, so it goes to the rational zero.
  have h0 : ψ 0 = some 0 := by
    obtain ⟨z, hz⟩ := hs (some 0)
    have e := hadd 0 z
    rw [T.isWheel.zero_add, hz] at e
    rcases h : ψ 0 with _ | r
    · rw [h] at e; cases e
    · rw [h] at e; simp only [Qa.add, Option.some.injEq, add_zero] at e; rw [e]
  -- `0ω` absorbs `+`, so it goes to `a`.
  have hb : ψ «0ω» = none := by
    obtain ⟨z, hz⟩ := hs (some 1)
    have e := hadd «0ω» z
    rw [zeroOmega_plus, hz] at e
    rcases h : ψ «0ω» with _ | r
    · rfl
    · rw [h] at e; simp [Qa.add] at e
  -- `ω · 0 = 0ω`, so `ω` goes to `a` as well.
  have hω : ψ «ω» = none := by
    have e := hmul «ω» 0
    rw [show «ω» * (0 : T) = «0ω» by decide, hb, h0] at e
    rcases h : ψ «ω» with _ | r
    · rfl
    · rw [h] at e; simp [Qa.mul] at e
  -- and `1/ω = 0`, which goes to `0`, not to `a⁻¹ = a`.
  have e := hinv «ω»
  rw [show reciprocal «ω» = 0 by decide, h0, hω] at e
  simp [Qa.inv] at e

/-- No map onto `ℚ` respects `+`: `0ω` would have to absorb under ordinary addition. -/
theorem no_surjective_add_hom_Q :
    ¬ ∃ ψ : T → ℚ, Function.Surjective ψ ∧ ∀ x y, ψ (x + y) = ψ x + ψ y := by
  rintro ⟨ψ, hs, hadd⟩
  obtain ⟨z, hz⟩ := hs 1
  have e := hadd «0ω» z
  rw [zeroOmega_plus, hz] at e
  linarith

end T
