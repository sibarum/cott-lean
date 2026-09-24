import CottLean.T.Angle

/-!
# `⊕` and division cannot share an equality

Each of the rings `⊕` makes with a product -- `⊗`, `+`, `⊚`, `*`, `∥` -- holds its ring laws exactly, at
coordinate equality. None of them has division there: a pair has an inverse only when its norm is `±1`
(`Norm`). Division does hold up to the ray or the ratio, and `⊕` does not survive either (`Quotient`).

This file proves the tension cannot be resolved by choosing some other equality. Take any equivalence
that `⊕` and the product both respect, in which every pair other than `0ω` has an inverse. Then that
equivalence identifies every pair with every other (`no_division_with_oplus`).

The proof is two cases. If some pair other than `0ω` is equivalent to `0ω`, its inverse makes the unit
equivalent to `0ω`, and then every `x = 1·x` is equivalent to `0ω·x = 0ω`. If no such pair exists, the
inverse of `1 ⊕ 1` is some `y` with `y ⊕ y` equivalent to the unit. Subtracting the unit with `⊕` makes
`(y ⊕ y) ⊕ -_1` equivalent to `0ω`, so it is `0ω`, and `y ⊕ y` is the unit. But `y ⊕ y` has even
coordinates, and each unit here has an odd one.

So division for the `⊕` rings cannot live beside `⊕` at any equality. It has to come from the level
above, where a pair of pairs is a fraction.
-/

namespace T

/-- A product with a unit `e` that `0ω` absorbs, on which doubling the unit doubles, and whose unit is
not a double. -/
theorem no_division_with_oplus (op : T → T → T) (e : T) (he : ∀ x, op e x = x)
    (hz : ∀ x, op «0ω» x = «0ω») (h2 : ∀ y, op (e ⊕ e) y = (y ⊕ y)) (hodd : ∀ y : T, (y ⊕ y) ≠ e)
    (r : Setoid T) (hplus : ∀ x x' y, r x x' → r (x ⊕ y) (x' ⊕ y))
    (htimes : ∀ x x' y, r x x' → r (op x y) (op x' y))
    (hinv : ∀ x, x ≠ «0ω» → ∃ y, r (op x y) e) :
    ∀ x y, r x y := by
  -- First, the unit is equivalent to `0ω`.
  have key : r e «0ω» := by
    by_cases h : ∃ z, z ≠ «0ω» ∧ r z «0ω»
    · obtain ⟨z, hz0, hzr⟩ := h
      obtain ⟨y, hy⟩ := hinv z hz0
      have := htimes _ _ y hzr
      rw [hz] at this
      exact Setoid.trans (Setoid.symm hy) this
    · push Not at h
      -- The unit is not `0ω`, so neither is its double.
      have hee : (e ⊕ e) ≠ «0ω» := by
        intro h0
        have hp := congrArg T.p h0
        have hq := congrArg T.q h0
        simp only [oplus, «0ω»] at hp hq
        apply hodd «0ω»
        ext <;> simp only [oplus, «0ω»] <;> omega
      obtain ⟨y, hy⟩ := hinv (e ⊕ e) hee
      rw [h2] at hy
      have hs := hplus _ _ (oplusInverse e) hy
      rw [oplus_oplusInverse] at hs
      by_contra
      -- Nothing but `0ω` is equivalent to `0ω`, so `(y ⊕ y) ⊕ -_e` is `0ω`, and `y ⊕ y` is `e`.
      have hzero : ((y ⊕ y) ⊕ oplusInverse e) = «0ω» := by
        by_contra hnz
        exact h _ hnz hs
      apply hodd y
      have hp := congrArg T.p hzero
      have hq := congrArg T.q hzero
      simp only [oplus, oplusInverse, «0ω»] at hp hq
      ext <;> simp only [oplus] <;> omega
  -- Then every pair is `e·x`, equivalent to `0ω·x = 0ω`.
  have all : ∀ x, r x «0ω» := fun x => by
    have := htimes _ _ x key
    rwa [he, hz] at this
  exact fun x y => Setoid.trans (all x) (Setoid.symm (all y))

/-- A unit with an odd coordinate is not a double. -/
theorem oplus_self_ne_of_odd {e : T} (h : e.p % 2 = 1 ∨ e.q % 2 = 1) (y : T) : (y ⊕ y) ≠ e := by
  intro hy
  have hp := congrArg T.p hy
  have hq := congrArg T.q hy
  simp only [oplus] at hp hq
  omega

/-! ## For each ring `⊕` makes -/

/-- For every `qtimes a b`, which covers `⊗`, `+` and `⊚`. -/
theorem no_division_qtimes (a b : ℤ) (r : Setoid T) (hplus : ∀ x x' y, r x x' → r (x ⊕ y) (x' ⊕ y))
    (htimes : ∀ x x' y, r x x' → r (qtimes a b x y) (qtimes a b x' y))
    (hinv : ∀ x, x ≠ «0ω» → ∃ y, r (qtimes a b x y) 0) : ∀ x y, r x y :=
  no_division_with_oplus (qtimes a b) 0
    (fun x => by ext <;> simp [qtimes])
    (fun x => by ext <;> simp [qtimes, «0ω»])
    (fun y => by ext <;> simp [qtimes, oplus] <;> ring)
    (oplus_self_ne_of_odd (by decide))
    r hplus htimes hinv

theorem no_division_times (r : Setoid T) (hplus : ∀ x x' y, r x x' → r (x ⊕ y) (x' ⊕ y))
    (htimes : ∀ x x' y, r x x' → r (x * y) (x' * y))
    (hinv : ∀ x, x ≠ «0ω» → ∃ y, r (x * y) «1») : ∀ x y, r x y :=
  no_division_with_oplus (· * ·) «1»
    (fun x => by ext <;> simp [«1»])
    (fun x => by ext <;> simp [«0ω»])
    (fun y => by ext <;> simp [oplus, «1»] <;> ring)
    (oplus_self_ne_of_odd (by decide))
    r hplus htimes hinv

theorem no_division_par (r : Setoid T) (hplus : ∀ x x' y, r x x' → r (x ⊕ y) (x' ⊕ y))
    (htimes : ∀ x x' y, r x x' → r (x ∥ y) (x' ∥ y))
    (hinv : ∀ x, x ≠ «0ω» → ∃ y, r (x ∥ y) «ω») : ∀ x y, r x y :=
  no_division_with_oplus par «ω»
    (fun x => by ext <;> simp [par, «ω»])
    (fun x => by ext <;> simp [par, «0ω»])
    (fun y => by ext <;> simp [par, oplus, «ω»] <;> ring)
    (oplus_self_ne_of_odd (by decide))
    r hplus htimes hinv

end T
