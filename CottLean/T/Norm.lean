import CottLean.T.Parallel

/-!
# One norm decides what each product can undo

Every product here is bilinear, so fixing the known operand `k` makes it a linear map of the other one,
and that map's determinant is the norm of `k` in the product's ring. In a quadratic ring over ℤ the norm
decides both questions the recovery tables ask:

* the other operand comes back exactly when `N(k) ≠ 0` (`recoverable_iff_norm`), since that is when `k`
  is not a zero divisor;
* `k` has an inverse in its ring exactly when `N(k) = ±1` (`exists_inverse_iff_norm`).

Reading `T(p, q)` as `q + p·ω` with `ω² = a + b·ω`, the norm is `q² + b·pq − a·p²`. So the five products:

| product | norm | undone exactly when | has an inverse exactly at |
|---|---|---|---|
| `⊗` | `p² + q²` | `k ≠ 0ω` | the four seeds `0, ω, _0, -ω` |
| `+` | `q²` | `q ≠ 0` | every `T(p, ±1)` |
| `⊚` | `q² − p²` | off the light lines | the four seeds again |
| `*` | `pq` | neither coordinate zero | `1, _1, -_1, -1` |
| `∥` | `p²` | `p ≠ 0` | every `T(±1, q)` |

The recovery conditions of `Recovery`, `Velocity` and `Parallel` are these norms read off, and the
inverse sets generalise `exists_otimes_eq_zero_iff`. `*` and `∥` are read through their own bases:
`q + (p − q)·ω` with `ω² = ω` for `*`, and `p + q·ω` with `ω² = 0` for `∥`.

## Two projections

Under `*`, `ω` and `0` are the complementary idempotents of `ℤ × ℤ`: each is its own square, their
product is `0ω` and their `⊕` is `1`. So `x * ω = T(p, 0)` and `x * 0 = T(0, q)` each keep one
coordinate, and `(x * ω) ⊕ (x * 0) = x` puts them back (`times_omega_oplus_times_zero`). A `*` that loses
information is a `*` against a pair on an axis, and what it loses is the other projection.
-/

namespace T

open QuadraticAlgebra nonZeroDivisors

/-! ## The two general statements -/

section General

variable {α β : ℤ} (op : T → T → T) (e : T ≃ QuadraticAlgebra ℤ α β)

/-- A product carried onto a quadratic ring can be undone against `k` exactly when `k`'s norm is not
zero. -/
theorem recoverable_iff_norm (he : ∀ x y, e (op x y) = e x * e y) (k : T) :
    Recoverable op k ↔ (e k).norm ≠ 0 := by
  rw [← mem_nonZeroDivisors_iff_ne_zero, norm_mem_nonZeroDivisors_iff]
  constructor
  · intro h
    rw [mem_nonZeroDivisors_iff_right]
    intro w hw
    have := h (e.symm w) (e.symm 0) (e.injective (by rw [he, he]; simp [hw]))
    simpa using congrArg e this
  · intro h x x' hx
    apply e.injective
    have := congrArg e hx
    rw [he, he] at this
    exact (mul_cancel_right_mem_nonZeroDivisors h).mp this

/-- It has an inverse exactly when the norm is a unit of ℤ. -/
theorem exists_inverse_iff_norm (he : ∀ x y, e (op x y) = e x * e y) (u : T) (hu : e u = 1) (k : T) :
    (∃ y, op k y = u) ↔ (e k).norm = 1 ∨ (e k).norm = -1 := by
  rw [← Int.isUnit_iff, ← isUnit_iff_norm_isUnit, isUnit_iff_exists_inv]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨e y, by rw [← he, hy, hu]⟩
  · rintro ⟨w, hw⟩
    exact ⟨e.symm w, e.injective (by rw [he, hu]; simpa using hw)⟩

end General

/-! ## The maps -/

theorem norm_toQuad (a b : ℤ) (k : T) : (toQuad a b k).norm = k.q ^ 2 + b * k.p * k.q - a * k.p ^ 2 := by
  simp [norm_def]; ring

theorem toQuad_otimes (x y : T) : toQuad (-1) 0 (x ⊗ y) = toQuad (-1) 0 x * toQuad (-1) 0 y := by
  rw [otimes_eq_qtimes]; exact toQuad_qtimes _ _ x y

theorem toQuad_plus (x y : T) : toQuad 0 0 (x + y) = toQuad 0 0 x * toQuad 0 0 y := by
  rw [plus_eq_qtimes]; exact toQuad_qtimes _ _ x y

theorem toQuad_splitTimes (x y : T) : toQuad 1 0 (x ⊚ y) = toQuad 1 0 x * toQuad 1 0 y :=
  toQuad_qtimes _ _ x y

theorem norm_toQuadProd (k : T) : (toQuadProd k).norm = k.p * k.q := by
  simp [norm_def, toQuadProd]; ring

/-- `T(p, q) ↦ p + q·ω`, with `ω² = 0`: `∥` in its own basis. -/
def toQuadPar : T ≃ QuadraticAlgebra ℤ 0 0 where
  toFun x := ⟨x.p, x.q⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem toQuadPar_par (x y : T) : toQuadPar (x ∥ y) = toQuadPar x * toQuadPar y := by
  ext <;> simp [toQuadPar, par]; ring

theorem norm_toQuadPar (k : T) : (toQuadPar k).norm = k.p ^ 2 := by
  simp [norm_def, toQuadPar]; ring

/-! ## What each product can undo -/

theorem otimes_recoverable_iff_norm (k : T) : Recoverable otimes k ↔ k.p ^ 2 + k.q ^ 2 ≠ 0 := by
  rw [recoverable_iff_norm _ _ toQuad_otimes, norm_toQuad]; ring_nf

theorem plus_recoverable_iff_norm (k : T) : Recoverable (· + ·) k ↔ k.q ^ 2 ≠ 0 := by
  rw [recoverable_iff_norm _ _ toQuad_plus, norm_toQuad]; ring_nf

theorem splitTimes_recoverable_iff_norm (k : T) : Recoverable splitTimes k ↔ k.q ^ 2 - k.p ^ 2 ≠ 0 := by
  rw [recoverable_iff_norm _ _ toQuad_splitTimes, norm_toQuad]; ring_nf

theorem times_recoverable_iff_norm (k : T) : Recoverable (· * ·) k ↔ k.p * k.q ≠ 0 := by
  rw [recoverable_iff_norm _ _ toQuadProd_times, norm_toQuadProd]

theorem par_recoverable_iff_norm (k : T) : Recoverable par k ↔ k.p ^ 2 ≠ 0 := by
  rw [recoverable_iff_norm _ _ toQuadPar_par, norm_toQuadPar]

/-! ## Where each product has an inverse -/

/-- Under `+`, the pairs with an inverse are those with denominator `±1`. -/
theorem exists_plus_eq_zero_iff (k : T) : (∃ y, k + y = 0) ↔ k.q = 1 ∨ k.q = -1 := by
  rw [exists_inverse_iff_norm _ _ toQuad_plus 0 (toQuad_zero 0 0), norm_toQuad]
  constructor
  · intro h
    have hu : IsUnit (k.q * k.q) := Int.isUnit_iff.mpr (by rcases h with h | h <;> [left; right] <;> linarith)
    exact Int.isUnit_iff.mp (IsUnit.mul_iff.mp hu).1
  · rintro (h | h) <;> simp [h]

/-- Under `⊚`, the pairs with an inverse are the four seeds, as under `⊗`. -/
theorem exists_splitTimes_eq_zero_iff (k : T) :
    (∃ y, k ⊚ y = 0) ↔ k = 0 ∨ k = «ω» ∨ k = «_0» ∨ k = «-ω» := by
  rw [exists_inverse_iff_norm _ _ toQuad_splitTimes 0 (toQuad_zero 1 0), norm_toQuad]
  simp only [T.ext_iff, zero_def, «ω», «_0», «-ω»]
  constructor
  · intro h
    have hu : IsUnit ((k.q - k.p) * (k.q + k.p)) :=
      Int.isUnit_iff.mpr (by rcases h with h | h <;> [left; right] <;> linarith)
    obtain ⟨h1, h2⟩ := IsUnit.mul_iff.mp hu
    rw [Int.isUnit_iff] at h1 h2
    omega
  · rintro (⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩) <;> simp [hp, hq]

/-- Under `*`, the pairs with an inverse are the four diagonal ones, `1, _1, -_1, -1`. -/
theorem exists_times_eq_one_iff (k : T) :
    (∃ y, k * y = «1») ↔ k = «1» ∨ k = «_1» ∨ k = «-_1» ∨ k = «-1» := by
  have hu1 : toQuadProd «1» = 1 := by ext <;> rfl
  rw [exists_inverse_iff_norm _ _ toQuadProd_times «1» hu1, norm_toQuadProd]
  simp only [T.ext_iff, «1», «_1», «-_1», «-1»]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := IsUnit.mul_iff.mp (Int.isUnit_iff.mpr h)
    rw [Int.isUnit_iff] at h1 h2
    omega
  · rintro (⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩) <;> simp [hp, hq]

/-- Under `∥`, the pairs with an inverse are those with numerator `±1`. -/
theorem exists_par_eq_omega_iff (k : T) : (∃ y, k ∥ y = «ω») ↔ k.p = 1 ∨ k.p = -1 := by
  have hu : toQuadPar «ω» = 1 := by ext <;> rfl
  rw [exists_inverse_iff_norm _ _ toQuadPar_par «ω» hu, norm_toQuadPar]
  constructor
  · intro h
    have hu : IsUnit (k.p * k.p) := Int.isUnit_iff.mpr (by rcases h with h | h <;> [left; right] <;> linarith)
    exact Int.isUnit_iff.mp (IsUnit.mul_iff.mp hu).1
  · rintro (h | h) <;> simp [h]

/-! ## The two projections -/

theorem zero_times_zero : (0 : T) * 0 = 0 := by decide
theorem omega_times_zero : «ω» * 0 = «0ω» := by decide
theorem omega_oplus_zero : («ω» ⊕ 0) = «1» := by decide

theorem times_omega (x : T) : x * «ω» = ⟨x.p, 0⟩ := by ext <;> simp [«ω»]
theorem times_zero (x : T) : x * 0 = ⟨0, x.q⟩ := by ext <;> simp

/-- Each projection keeps one coordinate, and `⊕` puts them back. -/
theorem times_omega_oplus_times_zero (x : T) : ((x * «ω») ⊕ (x * 0)) = x := by
  rw [times_omega, times_zero]; ext <;> simp [oplus]

end T
