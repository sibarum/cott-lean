import CottLean.T.TangentAddition

/-!
# Choosing an invariant: the quotient by a multiplicative set

In wheel theory an invariant enters as a quotient. For a multiplicative set `S` of integers -- a
submonoid of `(ℤ, ·)` -- two pairs are identified when a multiplier from `S` takes each to the same
place:

```
x ~ y   ⟺   s·x = t·y   for some s, t ∈ S
```

`S = {1}` identifies nothing, which is `T`. The positive integers identify a pair with its positive
multiples, which is the ray. The non-zero integers give the ratio, with `0ω` kept apart
(`ratioRel_iff`), which is what `sameRatio` could not do.

## What is proved

* `~` is an equivalence for every `S` (`setoid`).
* `+`, `*`, `/`, `-`, `-_` and `⊗` respect it, so each is an operation on the quotient.
* The quotient is a wheel for every `S` (`Q.isWheel`): Carlström's theorem, for ℤ.
* `⊕` respects it only in the two degenerate cases: `S = {1}`, which identifies nothing, and `0 ∈ S`,
  which identifies everything (`oplus_respects_iff`). Every invariant in between loses the mediant.

So a wheel of fractions over ℤ can carry `⊗`, but not `⊕`. The mediant, and the mediant tree built on it,
exist only on the pairs as they are.
-/

namespace T

/-! ## The relation -/

variable (S : Submonoid ℤ)

/-- `x ~ y` when a multiplier from `S` takes each to the same pair. -/
def Rel (x y : T) : Prop := ∃ s ∈ S, ∃ t ∈ S, scale s x = scale t y

theorem scale_scale (s t : ℤ) (x : T) : scale s (scale t x) = scale (s * t) x := by
  ext <;> simp [scale] <;> ring

theorem rel_refl (x : T) : Rel S x x := ⟨1, S.one_mem, 1, S.one_mem, rfl⟩

theorem rel_symm {x y : T} : Rel S x y → Rel S y x := by
  rintro ⟨s, hs, t, ht, h⟩
  exact ⟨t, ht, s, hs, h.symm⟩

theorem rel_trans {x y z : T} : Rel S x y → Rel S y z → Rel S x z := by
  rintro ⟨s, hs, t, ht, h₁⟩ ⟨u, hu, v, hv, h₂⟩
  refine ⟨u * s, S.mul_mem hu hs, t * v, S.mul_mem ht hv, ?_⟩
  rw [← scale_scale, h₁, scale_scale, mul_comm u t, ← scale_scale, h₂, scale_scale]

/-- The relation, as a setoid. -/
def setoid : Setoid T := ⟨Rel S, rel_refl S, rel_symm S, rel_trans S⟩

/-! ## What a multiplier passes through -/

theorem scale_plus (k : ℤ) (x y : T) : scale k x + y = scale k (x + y) := by
  ext <;> simp [scale] <;> ring
theorem scale_times (k : ℤ) (x y : T) : scale k x * y = scale k (x * y) := by
  ext <;> simp [scale] <;> ring
theorem scale_reciprocal (k : ℤ) (x : T) : reciprocal (scale k x) = scale k (reciprocal x) := by
  ext <;> simp [scale, reciprocal]
theorem scale_neg (k : ℤ) (x : T) : -(scale k x) = scale k (-x) := by
  ext <;> simp [scale]
theorem scale_oplusInverse (k : ℤ) (x : T) : oplusInverse (scale k x) = scale k (oplusInverse x) := by
  ext <;> simp [scale, oplusInverse]
theorem scale_otimes (k : ℤ) (x y : T) : scale k x ⊗ y = scale k (x ⊗ y) := by
  ext <;> simp [scale, otimes] <;> ring

/-! ## The operations that respect it -/

variable {S}

theorem rel_plus_left {x x' : T} (y : T) : Rel S x x' → Rel S (x + y) (x' + y) := by
  rintro ⟨s, hs, t, ht, h⟩
  exact ⟨s, hs, t, ht, by rw [← scale_plus, h, scale_plus]⟩

theorem rel_times_left {x x' : T} (y : T) : Rel S x x' → Rel S (x * y) (x' * y) := by
  rintro ⟨s, hs, t, ht, h⟩
  exact ⟨s, hs, t, ht, by rw [← scale_times, h, scale_times]⟩

theorem rel_otimes_left {x x' : T} (y : T) : Rel S x x' → Rel S (x ⊗ y) (x' ⊗ y) := by
  rintro ⟨s, hs, t, ht, h⟩
  exact ⟨s, hs, t, ht, by rw [← scale_otimes, h, scale_otimes]⟩

theorem rel_reciprocal {x x' : T} : Rel S x x' → Rel S (reciprocal x) (reciprocal x') := by
  rintro ⟨s, hs, t, ht, h⟩
  exact ⟨s, hs, t, ht, by rw [← scale_reciprocal, h, scale_reciprocal]⟩

theorem rel_neg {x x' : T} : Rel S x x' → Rel S (-x) (-x') := by
  rintro ⟨s, hs, t, ht, h⟩
  exact ⟨s, hs, t, ht, by rw [← scale_neg, h, scale_neg]⟩

theorem rel_oplusInverse {x x' : T} : Rel S x x' → Rel S (oplusInverse x) (oplusInverse x') := by
  rintro ⟨s, hs, t, ht, h⟩
  exact ⟨s, hs, t, ht, by rw [← scale_oplusInverse, h, scale_oplusInverse]⟩

/-- Both arguments at once, through commutativity. -/
theorem rel_binary {op : T → T → T} (comm : ∀ a b, op a b = op b a)
    (left : ∀ {x x'} y, Rel S x x' → Rel S (op x y) (op x' y))
    {x x' y y' : T} (hx : Rel S x x') (hy : Rel S y y') : Rel S (op x y) (op x' y') := by
  refine rel_trans S (left y hx) ?_
  rw [comm x' y, comm x' y']
  exact left x' hy

/-! ## `⊕` does not, except where nothing is identified or everything is -/

/-- `⊕` respects `~` exactly when `S` is `{1}` or contains `0`. -/
theorem oplus_respects_iff :
    (∀ x x' y : T, Rel S x x' → Rel S (x ⊕ y) (x' ⊕ y)) ↔ (S = ⊥ ∨ (0 : ℤ) ∈ S) := by
  constructor
  · intro h
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨hbot, h0⟩ := hne
    rw [Submonoid.eq_bot_iff_forall] at hbot
    push Not at hbot
    obtain ⟨s, hs, hs1⟩ := hbot
    -- ω is identified with sω, so ω ⊕ 0 = T(1,1) would have to be identified with sω ⊕ 0 = T(s,1).
    have hrel : Rel S «ω» (scale s «ω») := ⟨s, hs, 1, S.one_mem, by rw [scale_one]⟩
    obtain ⟨u, hu, v, hv, e⟩ := h _ _ 0 hrel
    have ep : u = v * s := by simpa [scale, oplus, «ω»] using congrArg T.p e
    have eq : u = v := by simpa [scale, oplus, «ω»] using congrArg T.q e
    have : v * (s - 1) = 0 := by linear_combination ep.symm.trans eq
    rcases mul_eq_zero.mp this with hv0 | hs0
    · exact h0 (hv0 ▸ hv)
    · exact hs1 (by linarith)
  · rintro (hbot | h0) x x' y ⟨s, hs, t, ht, e⟩
    · -- nothing is identified: the multipliers are both 1
      rw [hbot, Submonoid.mem_bot] at hs ht
      subst hs ht
      rw [scale_one, scale_one] at e
      rw [e]
      exact rel_refl _ _
    · -- everything is identified: 0 takes every pair to 0ω
      exact ⟨0, h0, 0, h0, by ext <;> simp [scale]⟩

/-- With nothing identified, `~` is equality. -/
theorem rel_bot_iff {x y : T} : Rel ⊥ x y ↔ x = y := by
  constructor
  · rintro ⟨s, hs, t, ht, e⟩
    rw [Submonoid.mem_bot] at hs ht
    subst hs ht
    rwa [scale_one, scale_one] at e
  · rintro rfl; exact rel_refl _ _

/-! ## The ratio invariant, with `0ω` kept apart -/

theorem ratioRel_iff (x y : T) :
    Rel (nonZeroDivisors ℤ) x y ↔ ((x = «0ω» ↔ y = «0ω») ∧ sameRatio x y) := by
  simp only [Rel, mem_nonZeroDivisors_iff_ne_zero]
  constructor
  · rintro ⟨s, hs, t, ht, e⟩
    have hp : s * x.p = t * y.p := congrArg T.p e
    have hq : s * x.q = t * y.q := congrArg T.q e
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro rfl
      ext
      · exact (mul_eq_zero.mp (by simpa [«0ω»] using hp.symm)).resolve_left ht
      · exact (mul_eq_zero.mp (by simpa [«0ω»] using hq.symm)).resolve_left ht
    · rintro rfl
      ext
      · exact (mul_eq_zero.mp (by simpa [«0ω»] using hp)).resolve_left hs
      · exact (mul_eq_zero.mp (by simpa [«0ω»] using hq)).resolve_left hs
    · unfold sameRatio
      have : s * t * (x.p * y.q - y.p * x.q) = 0 := by
        linear_combination (t * y.q) * hp - (t * y.p) * hq
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero hs ht)
      · linarith
  · rintro ⟨hz, hr⟩
    unfold sameRatio at hr
    by_cases hx : x = «0ω»
    · have hy := hz.mp hx
      subst hx hy
      exact ⟨1, one_ne_zero, 1, one_ne_zero, rfl⟩
    have hy : y ≠ «0ω» := fun h => hx (hz.mpr h)
    by_cases hxq : x.q = 0
    · have hxp : x.p ≠ 0 := fun h => hx (T.ext h hxq)
      have hyq : y.q = 0 := by
        rw [hxq, mul_zero] at hr
        exact (mul_eq_zero.mp hr).resolve_left hxp
      have hyp : y.p ≠ 0 := fun h => hy (T.ext h hyq)
      exact ⟨y.p, hyp, x.p, hxp, by ext <;> simp [scale, hxq, hyq]; ring⟩
    · by_cases hyq : y.q = 0
      · exfalso
        have hyp : y.p = 0 := by
          rw [hyq, mul_zero] at hr
          exact (mul_eq_zero.mp hr.symm).resolve_right hxq
        exact hy (T.ext hyp hyq)
      · exact ⟨y.q, hyq, x.q, hxq, by ext <;> simp [scale] <;> linarith⟩

/-! ## The quotient is a wheel, and carries `⊗` -/

variable (S)

/-- `T` with the invariant `S` chosen. -/
def Q : Type := Quotient (setoid S)

namespace Q

/-- The class of a pair. -/
def mk (x : T) : Q S := Quotient.mk (setoid S) x

instance : Zero (Q S) := ⟨mk S 0⟩
/-- `1`, the class of `T(1,1)`. -/
def one : Q S := mk S «1»

/-- `+` on classes. -/
def add : Q S → Q S → Q S :=
  Quotient.map₂ (· + ·) fun _ _ hx _ _ hy => rel_binary plus_comm rel_plus_left hx hy
/-- `*` on classes. -/
def mul : Q S → Q S → Q S :=
  Quotient.map₂ (· * ·) fun _ _ hx _ _ hy => rel_binary times_comm rel_times_left hx hy
/-- `/` on classes. -/
def inv : Q S → Q S := Quotient.map reciprocal fun _ _ h => rel_reciprocal h
/-- `⊗` on classes. -/
def otimes : Q S → Q S → Q S :=
  Quotient.map₂ T.otimes fun _ _ hx _ _ hy => rel_binary otimes_comm rel_otimes_left hx hy

/-- Carlström's theorem, for ℤ: every quotient by a multiplicative set is a wheel. -/
theorem isWheel : IsWheel (0 : Q S) (one S) (add S) (mul S) (inv S) where
  add_comm x y := Quotient.inductionOn₂ x y fun a b => congrArg (mk S) (plus_comm a b)
  add_assoc x y z := Quotient.inductionOn₃ x y z fun a b c => congrArg (mk S) (plus_assoc a b c)
  zero_add x := Quotient.inductionOn x fun a => congrArg (mk S) (T.isWheel.zero_add a)
  mul_comm x y := Quotient.inductionOn₂ x y fun a b => congrArg (mk S) (times_comm a b)
  mul_assoc x y z := Quotient.inductionOn₃ x y z fun a b c => congrArg (mk S) (times_assoc a b c)
  one_mul x := Quotient.inductionOn x fun a => congrArg (mk S) (T.isWheel.one_mul a)
  inv_inv x := Quotient.inductionOn x fun a => congrArg (mk S) (reciprocal_reciprocal a)
  inv_mul x y := Quotient.inductionOn₂ x y fun a b => congrArg (mk S) (reciprocal_times a b)
  inv_one := congrArg (mk S) T.isWheel.inv_one
  distrib x y z :=
    Quotient.inductionOn₃ x y z fun a b c => congrArg (mk S) (T.isWheel.distrib a b c)
  div_add x y z :=
    Quotient.inductionOn₃ x y z fun a b c => congrArg (mk S) (T.isWheel.div_add a b c)
  zero_mul_zero := congrArg (mk S) T.isWheel.zero_mul_zero
  add_zero_mul x y z :=
    Quotient.inductionOn₃ x y z fun a b c => congrArg (mk S) (T.isWheel.add_zero_mul a b c)
  inv_add_zero x y :=
    Quotient.inductionOn₂ x y fun a b => congrArg (mk S) (T.isWheel.inv_add_zero a b)
  bottom_add x := Quotient.inductionOn x fun a => congrArg (mk S) (T.isWheel.bottom_add a)

/-- And the tangent-addition identity passes to every quotient. -/
theorem tanAdd_mk (x y : T) :
    mk S (tanAdd x y) = mk S (scale (x.q * y.q) (x ⊗ y)) := congrArg (mk S) (tanAdd_eq x y)

end Q

end T
