import CottLean.T.Quadratic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith

/-!
# Triality and the light-like probe

Imports the product and unit from `T`, and adds the Eisenstein product and triality.
-/

namespace T

/-- Eisenstein product, `ω² = −1 − ω`. -/
def eis := qtimes (-1) (-1)

/-- Triality: reduction of `q + p·ζ₃` modulo `(1 − ζ₃)`, which sends `ζ₃ ↦ 1`. -/
def tri (x : T) : ZMod 3 := (x.p : ZMod 3) + x.q

theorem tri_oplus (x y : T) : tri (oplus x y) = tri x + tri y := by
  simp only [tri, oplus]; push_cast; ring

theorem tri_eis (x y : T) : tri (eis x y) = tri x * tri y := by
  have h : (3 : ZMod 3) = 0 := by decide
  simp only [tri, eis, qtimes]; push_cast
  linear_combination (-(x.p : ZMod 3) * y.p) * h

theorem tri_zero : tri «0» = 1 := by decide

/-- Triality is also `⊚`'s light-cone coordinate, multiplicative over ℤ, not just mod 3. -/
theorem lightCone_mul (x y : T) :
    (splitTimes x y).p + (splitTimes x y).q = (x.p + x.q) * (y.p + y.q) := by
  simp only [splitTimes, qtimes]; ring

/-- `⊗` does not respect triality: `tri (ω ⊗ ω) ≠ tri ω * tri ω`. -/
theorem tri_otimes_fails : tri (otimes ⟨1,0⟩ ⟨1,0⟩) ≠ tri ⟨1,0⟩ * tri ⟨1,0⟩ := by decide

/-- The coupling of `⊗`'s channel: the polarization of its norm `p² + q²` over `⊕`. -/
def couple (x u : T) : ℤ := x.p * u.p + x.q * u.q

theorem couple_polar (x u : T) :
    2 * couple x u = (oplus x u).p ^ 2 + (oplus x u).q ^ 2 - (x.p^2 + x.q^2) - (u.p^2 + u.q^2) := by
  simp only [couple, oplus]; ring

/-- `1` is light-like under `⊚`'s norm `q² − p²`. -/
theorem one_lightlike : «1».q ^ 2 - «1».p ^ 2 = 0 := by decide

/-- Coupling to `1` reads off triality. -/
theorem tri_eq_couple_one (x : T) : tri x = (couple x «1» : ZMod 3) := by
  simp only [tri, couple, «1»]; push_cast; ring

/-- Triality fixes the probe mod 3: a probe reads off triality for every `x` iff `u ≡ 1`. -/
theorem probe_iff (u : T) :
    (∀ x : T, (couple x u : ZMod 3) = tri x) ↔ ((u.p : ZMod 3) = 1 ∧ (u.q : ZMod 3) = 1) := by
  constructor
  · intro h
    have h1 := h ⟨1, 0⟩
    have h2 := h ⟨0, 1⟩
    simp only [couple, tri] at h1 h2; push_cast at h1 h2
    exact ⟨by simpa using h1, by simpa using h2⟩
  · rintro ⟨hp, hq⟩ x
    simp only [couple, tri]; push_cast; rw [hp, hq]; ring

/-- The light-like probes that read off triality are exactly `T(k, k)` with `k ≡ 1 (mod 3)`. -/
theorem lightlike_probe_iff (u : T) (hl : u.q ^ 2 - u.p ^ 2 = 0) :
    (∀ x : T, (couple x u : ZMod 3) = tri x) ↔ (u.q = u.p ∧ (u.p : ZMod 3) = 1) := by
  rw [probe_iff]
  have hsq : (u.q - u.p) * (u.q + u.p) = 0 := by linear_combination hl
  constructor
  · rintro ⟨hp, hq⟩
    rcases mul_eq_zero.mp hsq with h | h
    · exact ⟨by linarith, hp⟩
    · exfalso
      have : (u.q : ZMod 3) = -(u.p : ZMod 3) := by
        have : u.q = -u.p := by linarith
        rw [this]; push_cast; ring
      rw [hp, hq] at this; revert this; decide
  · rintro ⟨he, hp⟩; exact ⟨hp, he ▸ hp⟩

end T
