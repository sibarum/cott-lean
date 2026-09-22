import CottLean.T.Gaussian
import CottLean.T.ValuePosition

/-!
# Where information is lost

Given a result and one operand, is the other recoverable? Recoverable here means its exact coordinates,
since equality is coordinate equality and no invariant is specified by default.

TLawsTest measures this over a 14-element sample and finds the losses land exactly where a coordinate is
zero. These are the universal statements, one per operation:

| operation | the other operand is recoverable exactly when the known one has |
|---|---|
| `⊕` | always |
| `⊗` | any pair but `0ω` |
| `+` | a denominator that is not zero |
| `*` | neither coordinate zero |

Each "exactly when" is two theorems. One says the operation cancels under the condition. The other says
that where the condition fails, EVERY operand has a distinct partner that gives the same result -- built
from it, not searched for -- so the loss is the operation being ambiguous there and not an inverse formula
being too weak. (Every operation commutes, so the same holds with the known operand on the left.)
-/

namespace T

/-- Knowing `k`, the operand `a` can be read back from `op a k`. -/
def Recoverable (op : T → T → T) (k : T) : Prop := ∀ a a', op a k = op a' k → a = a'

/-! ## `⊕`: never loses -/

/-- The exact inverse: subtract the known operand, coordinate by coordinate. -/
theorem oplus_oplusInverse_cancel (a k : T) : ((a ⊕ k) ⊕ oplusInverse k) = a := by
  ext <;> simp [oplus, oplusInverse]

theorem oplus_recoverable (k : T) : Recoverable oplus k := fun a a' h => by
  rw [← oplus_oplusInverse_cancel a k, h, oplus_oplusInverse_cancel]

/-! ## `⊗`: loses only against `0ω` -/

/-- The exact inverse, up to the norm: `(a ⊗ k) ⊗ -k` is `a` with both coordinates multiplied by
`p² + q²` of `k`. Dividing it back out is exact wherever that is not zero. -/
theorem otimes_otimes_neg (a k : T) : (a ⊗ k) ⊗ -k = scale (k.p ^ 2 + k.q ^ 2) a := by
  ext <;> simp [otimes, scale] <;> ring

/-- Against `0ω`, every operand gives `0ω`. -/
theorem otimes_zeroOmega (a : T) : a ⊗ «0ω» = «0ω» := by
  ext <;> simp [otimes, «0ω»]

theorem otimes_ambiguous (a : T) : ∃ a', a' ≠ a ∧ a' ⊗ «0ω» = a ⊗ «0ω» :=
  ⟨⟨a.p + 1, a.q⟩, fun h => by simpa using congrArg T.p h, by simp [otimes_zeroOmega]⟩

theorem otimes_recoverable_iff (k : T) : Recoverable otimes k ↔ k ≠ «0ω» := by
  constructor
  · rintro h rfl
    obtain ⟨a', hne, heq⟩ := otimes_ambiguous 0
    exact hne (h _ _ heq)
  · intro hk a a' h
    have hg : toGaussian k ≠ 0 := fun h0 =>
      hk (toGaussian_injective (h0.trans toGaussian_zeroOmega.symm))
    apply toGaussian_injective
    have := congrArg toGaussian h
    rw [toGaussian_otimes, toGaussian_otimes] at this
    exact mul_right_cancel₀ hg this

/-! ## `+`: loses at a zero denominator -/

theorem plus_ambiguous {k : T} (hk : k.q = 0) (a : T) : ∃ a', a' ≠ a ∧ a' + k = a + k :=
  ⟨⟨a.p + 1, a.q⟩, fun h => by simpa using congrArg T.p h, by ext <;> simp [hk]⟩

theorem plus_recoverable_iff (k : T) : Recoverable (· + ·) k ↔ k.q ≠ 0 := by
  constructor
  · intro h hk
    obtain ⟨a', hne, heq⟩ := plus_ambiguous hk 0
    exact hne (h _ _ heq)
  · intro hk a a' h
    have hp := congrArg T.p h
    have hq := congrArg T.q h
    simp only [add_def] at hp hq
    have eq_q : a.q = a'.q := mul_right_cancel₀ hk hq
    rw [eq_q] at hp
    have eq_p : a.p = a'.p := mul_right_cancel₀ hk (by linarith)
    exact T.ext eq_p eq_q

/-! ## `*`: loses at either zero coordinate -/

theorem times_ambiguous_of_p {k : T} (hk : k.p = 0) (a : T) : ∃ a', a' ≠ a ∧ a' * k = a * k :=
  ⟨⟨a.p + 1, a.q⟩, fun h => by simpa using congrArg T.p h, by ext <;> simp [hk]⟩

theorem times_ambiguous_of_q {k : T} (hk : k.q = 0) (a : T) : ∃ a', a' ≠ a ∧ a' * k = a * k :=
  ⟨⟨a.p, a.q + 1⟩, fun h => by simpa using congrArg T.q h, by ext <;> simp [hk]⟩

theorem times_recoverable_iff (k : T) : Recoverable (· * ·) k ↔ k.p ≠ 0 ∧ k.q ≠ 0 := by
  constructor
  · intro h
    constructor
    · intro hk
      obtain ⟨a', hne, heq⟩ := times_ambiguous_of_p hk 0
      exact hne (h _ _ heq)
    · intro hk
      obtain ⟨a', hne, heq⟩ := times_ambiguous_of_q hk 0
      exact hne (h _ _ heq)
  · rintro ⟨hp, hq⟩ a a' h
    exact T.ext (mul_right_cancel₀ hp (congrArg T.p h)) (mul_right_cancel₀ hq (congrArg T.q h))

/-! ## The sample, as TLawsTest counts it

Of the nine named values, the ones each operation cannot read past. -/

example : «0ω» ∈ nine ∧ ¬ Recoverable otimes «0ω» := ⟨by decide, fun h => (otimes_recoverable_iff _).mp h rfl⟩

/-- Five of the nine have a zero coordinate, and those are the five `*` cannot read past. -/
example : (nine.filter fun k => k.p = 0 ∨ k.q = 0).length = 5 := by decide

/-- Three have a zero denominator, and those are the three `+` cannot read past. -/
example : (nine.filter fun k => k.q = 0).length = 3 := by decide

end T
