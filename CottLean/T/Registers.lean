import CottLean.T.Gaussian
import CottLean.T.Fraction
import Mathlib.Data.BitVec

/-!
# A traction in `w`-bit registers

Integer hardware holds a coordinate in a `w`-bit register, the ring `BitVec w`, and taking an integer to
its register is the ring map `ℤ → BitVec w` (`wrap`). Wrapping both coordinates of a traction gives the
pair of registers that holds it (`wrapPair`).

* `wrapPair_oplus`, `wrapPair_plus`, `wrapPair_times`, `wrapPair_otimes`: the wrap respects `⊕`, and also
  `+`, `*` and `⊗`, as every operation that is a polynomial in the coordinates does.
* `wrapPair_eq_iff`: two pairs wrap to the same register pair exactly when their coordinates agree
  modulo `2^w`.

## Against `Quotient.lean`

`T.oplus_respects_iff` shows that `⊕` survives no quotient by a multiplicative set, other than the two
degenerate ones: every invariant of the wheel kind, such as the ray or the ratio, loses the mediant.
Reducing the coordinates modulo `2^w` is a quotient of another kind. It identifies pairs whose
*difference* is divisible, not pairs that are *multiples* of each other, and it keeps `⊕` along with
every other operation. So the mediant has a quotient after all, just not one that reads the pair as a
ratio. That is the quotient integer hardware computes in.

What this means for a scatter run on such registers, where every schedule gives one grid, is proved in
vexelray-lean-proofs, `Scatter/`.
-/

namespace T

/-- An integer, as the `w`-bit register holding it: its residue modulo `2^w`. -/
def wrap (w : ℕ) : ℤ →+* BitVec w := Int.castRingHom (BitVec w)

/-- Read back signed, a register holds its integer's balanced residue. -/
theorem toInt_wrap (w : ℕ) (a : ℤ) : (wrap w a).toInt = a.bmod (2 ^ w) := by
  have : wrap w a = BitVec.ofInt w a := rfl
  rw [this, BitVec.toInt_ofInt]

/-- A traction, as the pair of registers holding its coordinates. -/
def wrapPair (w : ℕ) (x : T) : BitVec w × BitVec w := (wrap w x.p, wrap w x.q)

/-- `⊕` in registers is the registers' own addition, pair by pair. -/
theorem wrapPair_oplus (w : ℕ) (x y : T) : wrapPair w (x ⊕ y) = wrapPair w x + wrapPair w y := by
  simp [wrapPair, oplus]

/-- Fraction addition survives the wrap. -/
theorem wrapPair_plus (w : ℕ) (x y : T) :
    wrapPair w (x + y) =
      (wrap w x.p * wrap w y.q + wrap w y.p * wrap w x.q, wrap w x.q * wrap w y.q) := by
  change wrapPair w (plus x y) = _
  simp [wrapPair, plus]

/-- So does fraction multiplication. -/
theorem wrapPair_times (w : ℕ) (x y : T) :
    wrapPair w (x * y) = (wrap w x.p * wrap w y.p, wrap w x.q * wrap w y.q) := by
  change wrapPair w (times x y) = _
  simp [wrapPair, times]

/-- And angle addition. -/
theorem wrapPair_otimes (w : ℕ) (x y : T) :
    wrapPair w (x ⊗ y) =
      (wrap w x.p * wrap w y.q + wrap w y.p * wrap w x.q,
        wrap w x.q * wrap w y.q - wrap w x.p * wrap w y.p) := by
  simp [wrapPair, otimes]

/-- Two integers share a register exactly when they agree modulo `2^w`. -/
theorem wrap_eq_iff (w : ℕ) (a b : ℤ) : wrap w a = wrap w b ↔ (2 ^ w : ℤ) ∣ a - b := by
  have h0 : (0 : BitVec w).toInt = 0 := BitVec.toInt_zero
  rw [← sub_eq_zero, ← map_sub, ← BitVec.toInt_inj, toInt_wrap, h0]
  exact_mod_cast Int.dvd_iff_bmod_eq_zero.symm

/-- Two tractions share a register pair exactly when their coordinates agree modulo `2^w`: a
congruence of differences, where `Quotient.lean`'s are congruences of multiples. -/
theorem wrapPair_eq_iff (w : ℕ) (x y : T) :
    wrapPair w x = wrapPair w y ↔ (2 ^ w : ℤ) ∣ x.p - y.p ∧ (2 ^ w : ℤ) ∣ x.q - y.q := by
  simp only [wrapPair, Prod.ext_iff, wrap_eq_iff]

end T
