import CottLean.T.Fraction
import CottLean.T.Gaussian
import CottLean.T.Angle

/-!
# The ratio reading and the complex reading

One pair `T(p, q)` has two readings: the ratio `p/q`, with `+` and `*`, and the point `q + p·i`, with `⊕`
and `⊗`. Each reading has its own copy of the integers, on different pairs:

```
5 = 5/1     = T(5, 1)     the ratio reading      (ratioInt)
5 = 5 + 0·i = T(0, 5)     the complex reading    (complexInt)
```

This file says how the two copies relate.

* **On the integers they are the same.** `n ↦ T(n,1)` carries `+` and `*` to the integers' sum and
  product (`ratioInt_plus`, `ratioInt_times`), and `n ↦ T(0,n)` does the same for `⊕` and `⊗`
  (`complexInt_oplus`, `complexInt_otimes`). It is the integer cast of `GaussianPosition`
  (`complexInt_eq_intCast`).
* **The map between them is written in the model's operations.** `toComplex x = 0 / x`, that is
  `0 * reciprocal x`, which is `T(0, p)`. `toRatio y = reciprocal y ⊕ 0`, which is `T(q, p + 1)`. On the
  integers they invert each other (`toComplex_ratioInt`, `toRatio_complexInt`). So the complex `5` is the
  ratio `0/5`.
* **Off the integers, `toComplex` keeps `*` and forgets the denominator.** It sends `*` to `⊗` for every
  pair (`toComplex_times`), but `+` to `⊕` only when both denominators are `1`
  (`toComplex_plus_of_q_eq_one`, `toComplex_plus_ne`).
* **The two copies share one pair.** `T(0,1)` is the ratio `0` and the complex `1`, and no other pair
  is in both (`ratioInt_eq_complexInt_iff`).
* **Each reading sees the other's integers as something else.** Read as a ratio, every complex integer
  is a zero: `T(0,a) + T(0,b) = T(0,ab)`, so the ratio `+` multiplies them (`complexInt_plus`), and each
  has the ratio of `0` (`sameRatio_complexInt_zero`) and an angle of `0` or `π` (`theta_complexInt_pos`,
  `theta_complexInt_neg`). Read as a point, the ratio integer `n` is `1 + n·i` (`toC_ratioInt`), whose
  angle has tangent `n` (`tan_theta_ratioInt`). There `⊕` is the mean, `T(a+b, 2)`
  (`ratioInt_oplus`), and `⊗` is tangent addition, `T(a+b, 1−ab)` (`ratioInt_otimes`).
* **The two readings are not isomorphic.** No injective map sends `+` to `⊕` (`not_plus_embeds_oplus`),
  and none sends `*` to `⊗` (`not_times_embeds_otimes`). `ω + x` forgets `x`'s numerator, and `ω * x` can
  reach `0ω` from a pair other than `0ω`. `⊕` cancels, and `⊗` has no zero divisors.

Past the integers, the ratio reading holds ℚ, up to `sameRatio`, and the complex reading holds ℤ[i]. The
only integers they have in common are ℤ: `1/2` is not a Gaussian integer and `i` is not a ratio. Putting
the ratio `p/q` in the complex reading takes a fraction of Gaussian integers, `T(0,p) / T(0,q)`, which
is a pair of pairs. One pair is not enough.
-/

namespace T

open Complex

/-! ## The two copies of ℤ -/

/-- The integer `n` in the ratio reading: `T(n, 1)`, the ratio `n/1`. -/
def ratioInt (n : ℤ) : T := ⟨n, 1⟩

/-- The integer `n` in the complex reading: `T(0, n)`, the point `n + 0·i`. -/
def complexInt (n : ℤ) : T := ⟨0, n⟩

theorem ratioInt_injective : Function.Injective ratioInt := fun _ _ h => congrArg T.p h
theorem complexInt_injective : Function.Injective complexInt := fun _ _ h => congrArg T.q h

/-! ### The ratio copy under `+` and `*` -/

theorem ratioInt_plus (a b : ℤ) : ratioInt (a + b) = ratioInt a + ratioInt b := by
  ext <;> simp [ratioInt]

theorem ratioInt_times (a b : ℤ) : ratioInt (a * b) = ratioInt a * ratioInt b := by
  ext <;> simp [ratioInt]

theorem ratioInt_neg (a : ℤ) : ratioInt (-a) = -ratioInt a := by ext <;> simp [ratioInt]

theorem ratioInt_zero : ratioInt 0 = 0 := rfl
theorem ratioInt_one : ratioInt 1 = «1» := rfl

/-! ### The complex copy under `⊕` and `⊗` -/

theorem complexInt_oplus (a b : ℤ) : complexInt (a + b) = (complexInt a ⊕ complexInt b) := by
  ext <;> simp [complexInt, oplus]

theorem complexInt_otimes (a b : ℤ) : complexInt (a * b) = complexInt a ⊗ complexInt b := by
  ext <;> simp [complexInt, otimes]

theorem complexInt_neg (a : ℤ) : complexInt (-a) = oplusInverse (complexInt a) := by
  ext <;> simp [complexInt, oplusInverse]

theorem complexInt_zero : complexInt 0 = «0ω» := rfl
theorem complexInt_one : complexInt 1 = 0 := rfl

/-- The complex copy is the integer cast of the ring `GaussianPosition`. -/
theorem complexInt_eq_intCast (n : ℤ) : complexInt n = GaussianPosition.val (n : GaussianPosition) :=
  rfl

theorem toGaussian_complexInt (n : ℤ) : toGaussian (complexInt n) = n := by
  ext <;> simp [complexInt]

/-! ## The map between them -/

/-- The ratio `0/x`. It sends the ratio integer `n` to the complex integer `n`. -/
def toComplex (x : T) : T := 0 * reciprocal x

/-- `1/y ⊕ 0`. It sends the complex integer `n` to the ratio integer `n`. -/
def toRatio (y : T) : T := reciprocal y ⊕ 0

@[simp] theorem toComplex_def (x : T) : toComplex x = ⟨0, x.p⟩ := by
  ext <;> simp [toComplex, reciprocal]

@[simp] theorem toRatio_def (y : T) : toRatio y = ⟨y.q, y.p + 1⟩ := by
  ext <;> simp [toRatio, reciprocal, oplus]

/-- `0 / n = n`: the complex `n` is the ratio `0/n`. -/
theorem toComplex_ratioInt (n : ℤ) : toComplex (ratioInt n) = complexInt n := by
  simp [ratioInt, complexInt]

theorem toRatio_complexInt (n : ℤ) : toRatio (complexInt n) = ratioInt n := by
  simp [ratioInt, complexInt]

/-- `toComplex` takes `*` to `⊗` on every pair, not only on the integers. -/
theorem toComplex_times (x y : T) : toComplex (x * y) = toComplex x ⊗ toComplex y := by
  ext <;> simp [otimes]

/-- `toComplex` takes `+` to `⊕` where both denominators are `1`. -/
theorem toComplex_plus_of_q_eq_one {x y : T} (hx : x.q = 1) (hy : y.q = 1) :
    toComplex (x + y) = (toComplex x ⊕ toComplex y) := by
  ext <;> simp [oplus, hx, hy]

/-- And not otherwise: `1/2 + 1/2 = 4/4`, whose numerator is `4`, where `1 ⊕ 1 = 2`. -/
theorem toComplex_plus_ne :
    toComplex (⟨1, 2⟩ + ⟨1, 2⟩) ≠ (toComplex ⟨1, 2⟩ ⊕ toComplex ⟨1, 2⟩) := by
  simp [oplus]

/-- `T(0,1)` is the ratio `0` and the complex `1`, and it is the only pair in both copies. -/
theorem ratioInt_eq_complexInt_iff (a b : ℤ) : ratioInt a = complexInt b ↔ a = 0 ∧ b = 1 := by
  constructor
  · intro h
    exact ⟨congrArg T.p h, (congrArg T.q h).symm⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-! ## Each copy, read the other way -/

/-- The ratio `+` multiplies complex integers: `T(0,a) + T(0,b) = T(0,ab)`. -/
theorem complexInt_plus (a b : ℤ) : complexInt a + complexInt b = complexInt (a * b) := by
  ext <;> simp [complexInt]

theorem complexInt_times (a b : ℤ) : complexInt a * complexInt b = complexInt (a * b) := by
  ext <;> simp [complexInt]

/-- Every complex integer has the ratio of `0`. -/
theorem sameRatio_complexInt_zero (n : ℤ) : sameRatio (complexInt n) 0 := by
  simp [sameRatio, complexInt]

theorem toC_complexInt (n : ℤ) : toC (complexInt n) = ((n : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [complexInt]

theorem theta_complexInt_pos {n : ℤ} (hn : 0 < n) : theta (complexInt n) = 0 := by
  rw [theta, toC_complexInt]
  exact arg_ofReal_of_nonneg (by exact_mod_cast hn.le)

theorem theta_complexInt_neg {n : ℤ} (hn : n < 0) : theta (complexInt n) = Real.pi := by
  rw [theta, toC_complexInt]
  exact arg_ofReal_of_neg (by exact_mod_cast hn)

/-- The ratio integer `n` is the point `1 + n·i`. -/
theorem toC_ratioInt (n : ℤ) : toC (ratioInt n) = 1 + (n : ℂ) * I := by
  apply Complex.ext <;> simp [ratioInt]

/-- Whose angle has tangent `n`. -/
theorem tan_theta_ratioInt (n : ℤ) : Real.tan (theta (ratioInt n)) = n := by
  rw [tan_theta]; simp [ratioInt]

/-- `⊕` on ratio integers is the mean: `T(a+b, 2)`. -/
theorem ratioInt_oplus (a b : ℤ) : (ratioInt a ⊕ ratioInt b) = ⟨a + b, 2⟩ := by
  ext <;> simp [ratioInt, oplus]

/-- `⊗` on ratio integers is tangent addition: `T(a+b, 1−ab)`. -/
theorem ratioInt_otimes (a b : ℤ) : ratioInt a ⊗ ratioInt b = ⟨a + b, 1 - a * b⟩ := by
  ext <;> simp [ratioInt, otimes]

/-! ## No isomorphism -/

/-- No injective map takes `+` to `⊕`. `ω + 0 = ω + 1`, since `ω + x` forgets `x`'s numerator, and `⊕`
cancels. -/
theorem not_plus_embeds_oplus (f : T → T) (hf : Function.Injective f) :
    ¬ ∀ x y, f (x + y) = (f x ⊕ f y) := by
  intro h
  have e : «ω» + 0 = «ω» + «1» := by decide
  have g : toGaussian (f «ω») + toGaussian (f 0) = toGaussian (f «ω») + toGaussian (f «1») := by
    rw [← toGaussian_oplus, ← toGaussian_oplus, ← h, ← h, e]
  have := hf (toGaussian_injective (add_left_cancel g))
  exact absurd this (by decide)

/-- No injective map takes `*` to `⊗`. `ω * 0 = ω * 0ω` and `0 * ω = 0 * 0ω`, and at most one of `ω`
and `0` can land on `⊗`'s zero, which is the only element `⊗` cannot cancel. -/
theorem not_times_embeds_otimes (f : T → T) (hf : Function.Injective f) :
    ¬ ∀ x y, f (x * y) = f x ⊗ f y := by
  intro h
  have e₁ : «ω» * 0 = «ω» * «0ω» := by decide
  have e₂ : (0 : T) * «ω» = 0 * «0ω» := by decide
  have g₁ : toGaussian (f «ω») * toGaussian (f 0) = toGaussian (f «ω») * toGaussian (f «0ω») := by
    rw [← toGaussian_otimes, ← toGaussian_otimes, ← h, ← h, e₁]
  have g₂ : toGaussian (f 0) * toGaussian (f «ω») = toGaussian (f 0) * toGaussian (f «0ω») := by
    rw [← toGaussian_otimes, ← toGaussian_otimes, ← h, ← h, e₂]
  by_cases hw : toGaussian (f «ω») = 0
  · have h₀ : toGaussian (f 0) ≠ 0 := fun h₀ =>
      absurd (hf (toGaussian_injective (hw.trans h₀.symm))) (by decide)
    exact absurd (hf (toGaussian_injective (mul_left_cancel₀ h₀ g₂))) (by decide)
  · exact absurd (hf (toGaussian_injective (mul_left_cancel₀ hw g₁))) (by decide)

end T
