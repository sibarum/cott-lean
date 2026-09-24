import CottLean.T.Parallel
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The power sums

`(xⁿ + yⁿ)^(1/n)` is read exactly: `z` is a power sum of `x` and `y` when `zⁿ = xⁿ + yⁿ` on the
coordinates (`IsPowerSum`), with `xⁿ = T(pⁿ, qⁿ)`, and the reciprocal raised where `n` is negative.

* At `n = 1` the power sum is `+` (`isPowerSum_one_iff`), and at `n = −1` it is `∥`
  (`isPowerSum_negOne_iff`). Each is one pair, for every `x` and `y`.
* At every other `n` it leaves the integer pairs: for `x = y = 1` there is no `z`
  (`not_isPowerSum_one_one`), and none even at the same ratio but `0ω` (`sameRatio_one_one`). The sum is
  `T(2, 1)`, and `pⁿ = 2·qⁿ` has no solution but `p = q = 0` once `|n| ≥ 2` (`pow_eq_two_mul_pow`). At
  `n = 0` there is never a `z`, since every `z⁰` is `T(1,1)` and the sum is `T(2,1)`
  (`not_isPowerSum_zero`).
* That is "not for every pair", not "for no pair". At `n = 2` the Pythagorean triples stay:
  `3² + 4² = 5²`, and `1/(1/3² + 1/4²) = (12/5)²` (`isPowerSum_two`, `isPowerSum_negTwo`). At `n = 3`
  and `n = 4` they do not: the power sum is a pair only where one of `x.p·y.q`, `y.p·x.q` and `z.p` is
  zero (`isPowerSum_three`, `isPowerSum_four`). That is Fermat's Last Theorem at those exponents,
  which Mathlib has; the same statement at every `n ≥ 3` is Fermat's Last Theorem itself
  (`isPowerSum_trivial_of_flt`), which it does not.
-/

namespace T

/-! ## `pⁿ = 2·qⁿ` -/

/-- Two is not an `n`th power of a ratio once `n ≥ 2`: two's multiplicity in `pⁿ` is a multiple of `n`,
and in `2·qⁿ` it is one more than one. -/
theorem pow_eq_two_mul_pow {n : ℕ} (hn : 2 ≤ n) {p q : ℤ} (h : p ^ n = 2 * q ^ n) : p = 0 ∧ q = 0 := by
  have hn0 : n ≠ 0 := by omega
  by_cases hq : q = 0
  · subst hq
    simp only [zero_pow hn0, mul_zero, pow_eq_zero_iff hn0] at h
    exact ⟨h, rfl⟩
  exfalso
  have hp : p ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0, eq_comm, mul_eq_zero, pow_eq_zero_iff hn0] at h
    omega
  have hN : p.natAbs ^ n = 2 * q.natAbs ^ n := by
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_pow, Int.natAbs_mul] using this
  have hv := congrArg (padicValNat 2) hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.pow, padicValNat.mul (by norm_num) (pow_ne_zero _ (Int.natAbs_ne_zero.mpr hq)),
    padicValNat.pow, padicValNat_self] at hv
  have : n ∣ 1 := (Nat.dvd_add_left (dvd_mul_right n _)).mp (hv ▸ dvd_mul_right n _)
  have := Nat.le_of_dvd one_pos this
  omega

/-! ## The power, over the integers -/

/-- `xⁿ = T(pⁿ, qⁿ)` for `n ≥ 0`, and the reciprocal raised below zero. -/
def zpower (x : T) : ℤ → T
  | .ofNat n => power x n
  | .negSucc n => power (reciprocal x) (n + 1)

/-- `z` is a power sum `(xⁿ + yⁿ)^(1/n)` of `x` and `y`: `zⁿ = xⁿ + yⁿ`, exactly. -/
def IsPowerSum (n : ℤ) (x y z : T) : Prop := zpower z n = zpower x n + zpower y n

instance (n : ℤ) (x y z : T) : Decidable (IsPowerSum n x y z) := inferInstanceAs (Decidable (_ = _))

theorem power_one (x : T) : power x 1 = x := by ext <;> simp [power]

/-! ## The two that stay -/

/-- At `n = 1` the power sum is `+`. -/
theorem isPowerSum_one_iff (x y z : T) : IsPowerSum 1 x y z ↔ z = x + y := by
  change power z 1 = power x 1 + power y 1 ↔ _
  rw [power_one, power_one, power_one]

/-- At `n = −1` it is `∥`, the parallel sum. -/
theorem isPowerSum_negOne_iff (x y z : T) : IsPowerSum (-1) x y z ↔ z = x ∥ y := by
  change power (reciprocal z) 1 = power (reciprocal x) 1 + power (reciprocal y) 1 ↔ _
  rw [power_one, power_one, power_one, par_eq]
  exact ⟨fun h => by rw [← h, reciprocal_reciprocal], fun h => by rw [h, reciprocal_reciprocal]⟩

/-! ## Every other exponent -/

theorem zpower_one (n : ℤ) : zpower «1» n = «1» := by
  cases n <;> ext <;> simp [zpower, power, reciprocal, «1»]

theorem zpower_zero (x : T) : zpower x 0 = «1» := by ext <;> simp [zpower, power, «1»]

/-- At `n = 0` there is never a power sum: `z⁰` is `T(1,1)`, and `x⁰ + y⁰` is `T(2,1)`. -/
theorem not_isPowerSum_zero (x y z : T) : ¬ IsPowerSum 0 x y z := by
  unfold IsPowerSum; rw [zpower_zero, zpower_zero, zpower_zero]; decide

/-- For `x = y = 1`, the sum is `T(2,1)` at every exponent. -/
theorem zpower_one_add (n : ℤ) : zpower «1» n + zpower «1» n = ⟨2, 1⟩ := by
  rw [zpower_one]; decide

/-- Away from `n = ±1`, no pair but `0ω` has a power at the ratio of `1ⁿ + 1ⁿ`. -/
theorem sameRatio_one_one {n : ℤ} (h1 : n ≠ 1) (h2 : n ≠ -1) (z : T)
    (h : sameRatio (zpower z n) (zpower «1» n + zpower «1» n)) : z = «0ω» := by
  rw [zpower_one_add] at h
  simp only [sameRatio, mul_one] at h
  rcases n with m | m
  · rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · simp [zpower, power] at h
      · exact absurd rfl h1
    · obtain ⟨hp, hq⟩ := pow_eq_two_mul_pow hm (by simpa [zpower, power, mul_comm] using h)
      ext <;> simp [«0ω», hp, hq]
  · have hm : 2 ≤ m + 1 := by
      rcases m with _ | m
      · exact absurd rfl h2
      · omega
    obtain ⟨hq, hp⟩ := pow_eq_two_mul_pow hm (by simpa [zpower, power, reciprocal, mul_comm] using h)
    ext <;> simp [«0ω», hp, hq]

/-- **Away from `n = ±1`, the power sum leaves the integer pairs**: `1ⁿ + 1ⁿ` is no pair's `n`th
power. -/
theorem not_isPowerSum_one_one {n : ℤ} (h1 : n ≠ 1) (h2 : n ≠ -1) (z : T) :
    ¬ IsPowerSum n «1» «1» z := by
  intro h
  have hz := sameRatio_one_one h1 h2 z (h ▸ sameRatio_refl _)
  subst hz
  rw [IsPowerSum, zpower_one_add] at h
  rcases n with m | m
  · rcases m with _ | m
    · simp [zpower, power, «0ω»] at h
    · simp [zpower, power, «0ω»] at h
  · simp [zpower, power, reciprocal, «0ω»] at h

/-- So `+` and `∥` are the only power sums that stay on the pairs for every `x` and `y`. -/
theorem forall_isPowerSum_iff (n : ℤ) : (∀ x y, ∃ z, IsPowerSum n x y z) ↔ n = 1 ∨ n = -1 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨z, hz⟩ := h «1» «1»
    exact not_isPowerSum_one_one hn.1 hn.2 z hz
  · rintro (rfl | rfl) x y
    · exact ⟨x + y, (isPowerSum_one_iff x y _).mpr rfl⟩
    · exact ⟨x ∥ y, (isPowerSum_negOne_iff x y _).mpr rfl⟩

/-! ## Where some pairs stay -/

/-- `3² + 4² = 5²`. -/
theorem isPowerSum_two : IsPowerSum 2 ⟨3, 1⟩ ⟨4, 1⟩ ⟨5, 1⟩ := by decide

/-- `1/(1/3² + 1/4²) = (12/5)²`. -/
theorem isPowerSum_negTwo : IsPowerSum (-2) ⟨3, 1⟩ ⟨4, 1⟩ ⟨12, 5⟩ := by decide

/-- The numerator of a power sum, at a natural exponent. -/
theorem isPowerSum_ofNat_p {n : ℕ} {x y z : T} (h : IsPowerSum n x y z) :
    (x.p * y.q) ^ n + (y.p * x.q) ^ n = z.p ^ n := by
  have := congrArg T.p h
  simp only [zpower, power, add_def] at this
  rw [this, mul_pow, mul_pow]

/-- Wherever Fermat's Last Theorem holds at `n`, a power sum at `n` is a pair only where one of the
three numerators is zero. -/
theorem isPowerSum_trivial_of_flt {n : ℕ} (hn : FermatLastTheoremWith ℤ n) {x y z : T}
    (h : IsPowerSum n x y z) : x.p * y.q = 0 ∨ y.p * x.q = 0 ∨ z.p = 0 := by
  by_contra hc
  push Not at hc
  exact hn _ _ _ hc.1 hc.2.1 hc.2.2 (isPowerSum_ofNat_p h)

theorem isPowerSum_three {x y z : T} (h : IsPowerSum 3 x y z) :
    x.p * y.q = 0 ∨ y.p * x.q = 0 ∨ z.p = 0 :=
  isPowerSum_trivial_of_flt (fermatLastTheoremFor_iff_int.mp fermatLastTheoremThree) h

theorem isPowerSum_four {x y z : T} (h : IsPowerSum 4 x y z) :
    x.p * y.q = 0 ∨ y.p * x.q = 0 ∨ z.p = 0 :=
  isPowerSum_trivial_of_flt (fermatLastTheoremFor_iff_int.mp fermatLastTheoremFour) h

/-- Odd `n` has the third case: `1³ + (−1)³ = 0³`. -/
example : IsPowerSum 3 «1» «-1» 0 := by decide

end T
