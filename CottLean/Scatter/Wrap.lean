import CottLean.Scatter.Accumulate
import Mathlib.Data.BitVec

/-!
# Scatter: integer registers wrap, and it costs nothing

A GPU integer atomic add works on a `w`-bit register (`w = 32`, or `64` where `shaderInt64Atomics` is
supported), and it wraps: the register holds the sum modulo `2^w`. Read back as signed, it is exact
when the true sum lies in `[-2^(w-1), 2^(w-1))`, and wrong by a multiple of `2^w` otherwise.

The register is Lean's `BitVec w`, which Mathlib makes a commutative ring. Taking an integer to its
register, `wrap w`, is the ring map `ℤ → BitVec w` (`wrap`, and `wrap_apply` for the bits). A ring map
commutes with every sum, so the grid of wrapped deposits is the wrap of the integer grid (`grid_wrap`),
in every order of the atomics (`run_wrap`).

## What is proved

* `read_exact`, `run_read_exact`: read back signed, a node's register is its exact integer total
  whenever *the total* fits in `w` signed bits. Nothing is asked of the partial sums. They may overflow
  and come back, in any order of the deposits, and the final value is still exact. For momentum, whose
  deposits have both signs, this is the difference between bounding the heaviest node and bounding
  every prefix of every schedule.
* `read_exact_of_bound`: a sufficient condition to size the register by. If a node receives at most
  `K` deposits, each at most `D` in size, and `2·K·D < 2^w`, it is read back exactly.
* `wrapPair_oplus` and the rest: wrapping both coordinates of a traction respects `⊕`, and also `+`,
  `*` and `⊗`, as every operation that is a polynomial in the coordinates does. `wrapPair_eq_iff`:
  two pairs wrap to the same register pair exactly when their coordinates agree modulo `2^w`.

## Against `Quotient.lean`

`T.oplus_respects_iff` shows that `⊕` survives no quotient by a multiplicative set, other than the two
degenerate ones: every invariant of the wheel kind, such as the ray or the ratio, loses the mediant.
Reducing the coordinates modulo `2^w` is a quotient of another kind. It identifies pairs whose
*difference* is divisible, not pairs that are *multiples* of each other, and it keeps `⊕` along with
every other operation. So the mediant has a quotient after all, just not one that reads the pair as a
ratio. That is the quotient integer hardware computes in.
-/

namespace Scatter

open Finset

variable {ι N : Type*} [DecidableEq N]

/-! ## The register -/

/-- An integer, as the `w`-bit register a GPU integer atomic holds: its residue modulo `2^w`. -/
def wrap (w : ℕ) : ℤ →+* BitVec w := Int.castRingHom (BitVec w)

theorem wrap_apply (w : ℕ) (a : ℤ) : wrap w a = BitVec.ofInt w a := rfl

/-- Read back signed, a register holds its integer's balanced residue. -/
theorem toInt_wrap (w : ℕ) (a : ℤ) : (wrap w a).toInt = a.bmod (2 ^ w) := by
  rw [wrap_apply, BitVec.toInt_ofInt]

/-- An integer in the signed range is read back as itself. -/
theorem toInt_wrap_of_fits {w : ℕ} {a : ℤ} (lo : -(2 ^ w : ℤ) ≤ 2 * a) (hi : 2 * a < 2 ^ w) :
    (wrap w a).toInt = a := by
  rw [toInt_wrap]
  exact Int.bmod_eq_of_le_mul_two (by push_cast; omega) (by push_cast; omega)

/-! ## The grid, in registers -/

/-- The grid of the wrapped deposits is the wrap of the integer grid. -/
theorem grid_wrap (w : ℕ) (node : ι → N) (a : ι → ℤ) (s : Finset ι) (n : N) :
    grid node (fun i => wrap w (a i)) s n = wrap w (grid node a s n) := by
  simp [grid, map_sum]

/-- In every order the atomics may take, the registers hold the wrap of the integer grid. -/
theorem run_wrap (w : ℕ) (node : ι → N) (a : ι → ℤ) [DecidableEq ι] {l : List ι} (hl : l.Nodup)
    (n : N) : run node (fun i => wrap w (a i)) l n = wrap w (grid node a l.toFinset n) := by
  rw [run_eq_grid _ _ hl, grid_wrap]

/-- Transient overflow is harmless: a node's register, read back signed, is its exact integer total
whenever that total fits, whatever the partial sums did on the way. -/
theorem read_exact (w : ℕ) (node : ι → N) (a : ι → ℤ) (s : Finset ι) (n : N)
    (lo : -(2 ^ w : ℤ) ≤ 2 * grid node a s n) (hi : 2 * grid node a s n < 2 ^ w) :
    (grid node (fun i => wrap w (a i)) s n).toInt = grid node a s n := by
  rw [grid_wrap, toInt_wrap_of_fits lo hi]

/-- The same, for the direct scatter in any order of its atomics. -/
theorem run_read_exact (w : ℕ) (node : ι → N) (a : ι → ℤ) [DecidableEq ι] {l : List ι}
    (hl : l.Nodup) (n : N) (lo : -(2 ^ w : ℤ) ≤ 2 * grid node a l.toFinset n)
    (hi : 2 * grid node a l.toFinset n < 2 ^ w) :
    (run node (fun i => wrap w (a i)) l n).toInt = grid node a l.toFinset n := by
  rw [run_wrap w node a hl, toInt_wrap_of_fits lo hi]

/-- A node's total is bounded by its number of deposits times the largest. -/
theorem abs_grid_le (node : ι → N) (a : ι → ℤ) (s : Finset ι) (n : N) {D : ℤ}
    (hD : ∀ i ∈ s, node i = n → |a i| ≤ D) :
    |grid node a s n| ≤ (#{i ∈ s | node i = n} : ℤ) * D := by
  unfold grid
  calc |∑ i ∈ s with node i = n, a i| ≤ ∑ i ∈ s with node i = n, |a i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s with node i = n, D :=
        sum_le_sum fun i hi => hD i (mem_filter.mp hi).1 (mem_filter.mp hi).2
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- Sizing the register: a node that receives at most `K` deposits, each at most `D` in size, is read
back exactly when `2·K·D < 2^w`. -/
theorem read_exact_of_bound (w : ℕ) (node : ι → N) (a : ι → ℤ) (s : Finset ι) (n : N) {K D : ℤ}
    (hD : ∀ i ∈ s, node i = n → |a i| ≤ D) (hK : (#{i ∈ s | node i = n} : ℤ) ≤ K)
    (hfit : 2 * K * D < 2 ^ w) :
    (grid node (fun i => wrap w (a i)) s n).toInt = grid node a s n := by
  by_cases h0 : #{i ∈ s | node i = n} = 0
  · have : grid node a s n = 0 := by unfold grid; rw [card_eq_zero.mp h0, sum_empty]
    have : (0 : ℤ) < 2 ^ w := by positivity
    apply read_exact <;> omega
  obtain ⟨i, hi⟩ := card_ne_zero.mp h0
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD i (mem_filter.mp hi).1 (mem_filter.mp hi).2)
  have hb : |grid node a s n| ≤ K * D :=
    (abs_grid_le node a s n hD).trans (mul_le_mul_of_nonneg_right hK hD0)
  have := abs_le.mp hb
  apply read_exact <;> linarith

/-! ## A traction in registers -/

open T

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

end Scatter
