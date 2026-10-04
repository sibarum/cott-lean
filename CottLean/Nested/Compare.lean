import CottLean.Nested.RatioPoint

/-!
# What each construction of ℚ(i) can undo, and what each map forgets

`C(T, T)` (`Point`) and `T(C, C)` (`RatioPoint`) hold the same values. Here they are compared by the
question `Recovery` asks of flat `T`: given a result and one operand, does the other operand come back,
coordinate for coordinate? And for the two maps between them: exactly which points does each send to the
same place?

| | `C(T, T)` | `T(C, C)` |
|---|---|---|
| `+ k` undone exactly when | both denominators of `k` are non-zero (`oplus_cancel_iff`) | the denominator of `k` is non-zero (`TOver.plus_cancel_iff`) |
| `· k` undone exactly when | never (`otimes_never_injective`) | neither coordinate of `k` is zero (`TOver.times_cancel_iff`) |
| `1/x` | the conjugate over the norm | a swap, always undone |

## The product of `C(T, T)` forgets where a factor sits

For `X = c/d + (a/b)·i`, the product `X ⊗ K` depends on `X` only through `a·d`, `b·d` and `c·b`
(`otimes_eq_int`). Four integers go in and three come out. So a factor `k` can move from the real
coordinate to the imaginary one without changing any product (`otimes_transfer`): `T(a, b), T(ck, dk)` and
`T(ak, bk), T(c, d)` multiply alike. At `k = −1` that makes `⊗` not injective against any `K`, `1`
included.

Where `K` is finite and its norm is not zero, that is all it forgets: `X ⊗ K = X' ⊗ K` exactly when the
three agree (`otimes_eq_otimes_iff`).

## `combine` forgets the same thing

The three numbers are `combine`'s coordinates: `combine X = (cb + ad·i) / (bd)`. So `combine X =
combine X'` exactly when they agree (`combine_eq_iff`), and `combine` carries `C(T, T)`'s product to
`T(C, C)`'s, scaled by the product's own denominator (`combine_otimes`). `C(T, T)`'s product is `T(C, C)`'s
product read through `combine`, and it forgets exactly what `combine` forgets.

## `rationalize` forgets a unit

`rationalize x = rationalize x'` exactly when the denominators have the same norm and `z·w̄` agrees
(`rationalize_eq_iff`). Multiplying `z` and `w` by the same unit `±1, ±i` changes neither
(`rationalize_unit`), so `rationalize` is never injective either, and every direction at infinity goes to
the one point `T2(0ω, 0ω)` (`TC.rationalize_infinite`).

So each map forgets something, and the two forget different things. `combine` forgets how a factor is
shared between two ratio coordinates; `rationalize` forgets a unit common to numerator and denominator.
-/

open T TC

namespace T2

/-! ## `+` in `C(T, T)` -/

/-- `⊕ K` can be undone exactly when both denominators of `K` are non-zero. -/
theorem oplus_cancel_iff (K : T2) :
    (∀ X X' : T2, oplus X K = oplus X' K → X = X') ↔ K.p.q ≠ 0 ∧ K.q.q ≠ 0 := by
  constructor
  · intro h
    refine ⟨fun hp => ?_, fun hq => ?_⟩
    · obtain ⟨a', ha', he⟩ := plus_ambiguous hp (0 : T)
      exact ha' (congrArg T2.p (h ⟨a', 0⟩ ⟨0, 0⟩ (by ext1 <;> simp [oplus, he])))
    · obtain ⟨a', ha', he⟩ := plus_ambiguous hq (0 : T)
      exact ha' (congrArg T2.q (h ⟨0, a'⟩ ⟨0, 0⟩ (by ext1 <;> simp [oplus, he])))
  · rintro ⟨hp, hq⟩ X X' h
    ext1
    · exact (plus_recoverable_iff K.p).mpr hp _ _ (congrArg T2.p h)
    · exact (plus_recoverable_iff K.q).mpr hq _ _ (congrArg T2.q h)

/-! ## `⊗` in `C(T, T)` -/

/-- The product in integers: it sees `X = T2(T(a,b), T(c,d))` only through `a·d`, `b·d` and `c·b`. -/
theorem otimes_eq_int (a b c d a₂ b₂ c₂ d₂ : ℤ) :
    otimes ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ =
      ⟨⟨a * d * (c₂ * b₂) + c * b * (a₂ * d₂), b * d * (b₂ * d₂)⟩,
        ⟨c * b * (c₂ * b₂) - a * d * (a₂ * d₂), b * d * (b₂ * d₂)⟩⟩ := by
  ext <;> simp [otimes] <;> ring

/-- A factor moves from the real coordinate to the imaginary one without changing any product. -/
theorem otimes_transfer (a b c d k : ℤ) (K : T2) :
    otimes ⟨⟨a, b⟩, ⟨c * k, d * k⟩⟩ K = otimes ⟨⟨a * k, b * k⟩, ⟨c, d⟩⟩ K := by
  obtain ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ := K
  rw [otimes_eq_int, otimes_eq_int]; ext <;> simp only <;> ring

/-- So `⊗ K` is never injective, for any `K`, `1` included. -/
theorem otimes_never_injective (K : T2) : ∃ X X' : T2, X ≠ X' ∧ otimes X K = otimes X' K :=
  ⟨⟨⟨1, 1⟩, ⟨-1, -1⟩⟩, ⟨⟨-1, -1⟩, ⟨1, 1⟩⟩, by decide, by
    simpa using otimes_transfer 1 1 1 1 (-1) K⟩

/-! ## `combine` keeps exactly those three -/

theorem combine_eq_iff (X X' : T2) :
    combine X = combine X' ↔
      X.q.p * X.p.q = X'.q.p * X'.p.q ∧ X.p.p * X.q.q = X'.p.p * X'.q.q ∧
        X.p.q * X.q.q = X'.p.q * X'.q.q := by
  constructor
  · intro h
    have h1 := congrArg (fun x : TC => x.p.re) h
    have h2 := congrArg (fun x : TC => x.p.im) h
    have h3 := congrArg (fun x : TC => x.q.re) h
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    simp only [combine, h1, h2, h3]

/-- Where `K` is finite with a non-zero norm, `⊗ K` forgets exactly what `combine` forgets. -/
theorem otimes_eq_otimes_iff (a b c d a' b' c' d' a₂ b₂ c₂ d₂ : ℤ) (hK : b₂ * d₂ ≠ 0)
    (hM : lenSq a₂ b₂ c₂ d₂ ≠ 0) :
    otimes ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ = otimes ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ ↔
      combine ⟨⟨a, b⟩, ⟨c, d⟩⟩ = combine ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := by
  rw [otimes_eq_int, otimes_eq_int, combine_eq_iff]
  simp only
  constructor
  · intro h
    have e1 := congrArg (fun X : T2 => X.p.p) h
    have e2 := congrArg (fun X : T2 => X.p.q) h
    have e3 := congrArg (fun X : T2 => X.q.p) h
    simp only at e1 e2 e3
    have hbd : b * d = b' * d' := mul_right_cancel₀ hK e2
    have hα : (a * d - a' * d') * lenSq a₂ b₂ c₂ d₂ = 0 := by
      unfold lenSq; linear_combination (c₂ * b₂) * e1 - (a₂ * d₂) * e3
    have hβ : (c * b - c' * b') * lenSq a₂ b₂ c₂ d₂ = 0 := by
      unfold lenSq; linear_combination (a₂ * d₂) * e1 + (c₂ * b₂) * e3
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hβ).resolve_right hM),
      sub_eq_zero.mp ((mul_eq_zero.mp hα).resolve_right hM), hbd⟩
  · rintro ⟨h1, h2, h3⟩
    ext <;> simp only
    · linear_combination (c₂ * b₂) * h2 + (a₂ * d₂) * h1
    · linear_combination (b₂ * d₂) * h3
    · linear_combination (c₂ * b₂) * h1 - (a₂ * d₂) * h2
    · linear_combination (b₂ * d₂) * h3

/-- `combine` carries `C(T, T)`'s product to `T(C, C)`'s, scaled by that product's own denominator. -/
theorem combine_otimes (X K : T2) :
    combine (otimes X K) =
      ⟨(combine X * combine K).p * (combine X * combine K).q,
        (combine X * combine K).q * (combine X * combine K).q⟩ := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := X
  obtain ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ := K
  rw [otimes_eq_int]
  ext <;> simp only [combine, TOver.mul_p, TOver.mul_q, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

end T2

namespace TC

/-! ## `rationalize` forgets a unit -/

theorem rationalize_eq_iff (x x' : TC) :
    rationalize x = rationalize x' ↔
      nrm x.q = nrm x'.q ∧ x.p * star x.q = x'.p * star x'.q := by
  constructor
  · intro h
    have h1 := congrArg (fun X : T2 => X.p.p) h
    have h2 := congrArg (fun X : T2 => X.p.q) h
    have h3 := congrArg (fun X : T2 => X.q.p) h
    exact ⟨h2, Zsqrtd.ext h3 h1⟩
  · rintro ⟨h1, h2⟩
    simp only [rationalize, h1, h2]

/-- Multiplying numerator and denominator by the same unit changes nothing `rationalize` keeps. -/
theorem rationalize_unit (x : TC) (u : GaussianInt) (hu : u * star u = 1) :
    rationalize ⟨x.p * u, x.q * u⟩ = rationalize x := by
  rw [rationalize_eq_iff]
  have hn : ∀ w : GaussianInt, ((nrm w : ℤ) : GaussianInt) = w * star w := fun w => by
    apply Zsqrtd.ext <;>
      simp only [Zsqrtd.re_intCast, Zsqrtd.im_intCast, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_star,
        Zsqrtd.im_star, nrm] <;> ring
  refine ⟨?_, ?_⟩
  · have h : ((nrm (x.q * u) : ℤ) : GaussianInt) = ((nrm x.q : ℤ) : GaussianInt) := by
      rw [hn, hn, star_mul', show x.q * u * (star x.q * star u) = x.q * star x.q * (u * star u) by ring,
        hu, mul_one]
    exact_mod_cast h
  · rw [star_mul', show x.p * u * (star x.q * star u) = x.p * star x.q * (u * star u) by ring, hu, mul_one]

/-- `rationalize` is never injective: `i·z / i·w` lands where `z / w` does. -/
theorem rationalize_not_injective : ¬ Function.Injective rationalize := by
  intro h
  have := h (rationalize_unit ⟨1, 1⟩ ⟨0, 1⟩ (by decide))
  exact absurd (congrArg TOver.p this) (by decide)

end TC
