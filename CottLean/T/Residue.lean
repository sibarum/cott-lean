import CottLean.T.Quotient
import CottLean.T.Mobius
import CottLean.T.Fracpair

/-!
# Every discrepancy is a residue

A *residue* is a zero-magnitude pair `T(0,k)`. Adding one multiplies both coordinates by `k`
(`plus_residue`), and `0·x` is the residue of `x`'s denominator (`zero_times`). So the wheel's
weakened laws, which are written with `+ 0·x` terms, are written with residues.

Every place a law of the model differs from T's exact coordinate result, the difference is one added
residue (`*_residue` below):

| law | residue |
|---|---|
| `x·z + y·z` against `(x + y)·z` | `z.q` |
| the wheel's tangent addition against `x ⊗ y` | `x.q · y.q` |
| the fracpair inverse against T's reciprocal | `x.q` |
| `T^m ⊗ T^n` against `T^(m+n)` | `(p² + q²)^turns` |
| `E⁻¹(E(x))`, read as a pair, against `x` | `2 · x.q` |
| `x + -x` against `0` | `x.q²` |
| `x ⊗ -x` against `0` | `p² + q²` |
| `x · (1/x)` against `1` | `x.p · x.q` |

Residues compose by multiplying: `T(0,j) + T(0,k) = T(0,j) · T(0,k) = T(0,jk)` (`residue_plus_residue`,
`residue_times_residue`). `T(0,1)` is `0`, and `T(0,0)` is `0ω` (`residue_eq_zeroOmega_iff`).

Under the ratio invariant a residue is invisible exactly when `k ≠ 0`: `y + T(0,k)` has `y`'s class
(`ratio_plus_residue`). When `k = 0` the residue is `0ω`, and it absorbs everything. So the classical law
holds, for the ratio, at exactly the inputs where the residue's `k` is not zero. Every `k` in the table is
zero only where some coordinate is zero: at the quarter turns for the denominator rows, only at `0ω` for
the norm rows, and also at the zeros `T(0,q)` for `x · (1/x)`.
-/

namespace T

/-! ## Residues -/

/-- `T(0,k)`: zero, carrying `k`. -/
def residue (k : ℤ) : T := ⟨0, k⟩

@[simp] theorem residue_p (k : ℤ) : (residue k).p = 0 := rfl
@[simp] theorem residue_q (k : ℤ) : (residue k).q = k := rfl

/-- Adding a residue multiplies both coordinates by it. -/
theorem plus_residue (y : T) (k : ℤ) : y + residue k = scale k y := by
  ext <;> simp [scale] <;> ring

/-- `0·x` is the residue of `x`'s denominator. -/
theorem zero_times (x : T) : 0 * x = residue x.q := by
  ext <;> simp

/-- So adding `0·x` multiplies by `x`'s denominator: the wheel's `+ 0x` terms are this. -/
theorem plus_zero_times (y x : T) : y + 0 * x = scale x.q y := by
  rw [zero_times, plus_residue]

theorem residue_one : residue 1 = 0 := rfl

theorem residue_eq_zeroOmega_iff (k : ℤ) : residue k = «0ω» ↔ k = 0 := by
  constructor
  · intro h; exact congrArg T.q h
  · rintro rfl; rfl

theorem residue_plus_residue (j k : ℤ) : residue j + residue k = residue (j * k) := by
  ext <;> simp

theorem residue_times_residue (j k : ℤ) : residue j * residue k = residue (j * k) := by
  ext <;> simp

/-! ## Each discrepancy, as a residue -/

theorem distrib_residue (x y z : T) : x * z + y * z = (x + y) * z + residue z.q := by
  rw [plus_residue, distrib_scaled]

theorem tanAdd_residue (x y : T) : tanAdd x y = (x ⊗ y) + residue (x.q * y.q) := by
  rw [plus_residue, tanAdd_eq]

theorem finv_residue (x : T) : finv x = reciprocal x + residue x.q := by
  rw [plus_residue, finv_eq_scale]

theorem otimesPower_add_residue (x : T) (m n : ℤ) :
    otimesPower x m ⊗ otimesPower x n
      = otimesPower x (m + n) + residue ((x.p ^ 2 + x.q ^ 2) ^ turns m n) := by
  rw [plus_residue, otimesPower_add]

theorem invMobius_residue (x : T) :
    invMobiusPair (doubleAngle x) (norm x) = x + residue (2 * x.q) := by
  rw [plus_residue, invMobius_mobius]

theorem plus_neg_residue (x : T) : x + -x = 0 + residue (x.q ^ 2) := by
  rw [plus_residue, plus_neg_self]; ext <;> simp [scale]

theorem otimes_neg_residue (x : T) : x ⊗ -x = 0 + residue (x.p ^ 2 + x.q ^ 2) := by
  rw [plus_residue, otimes_neg_self]; ext <;> simp [scale]

theorem times_reciprocal_residue (x : T) : x * reciprocal x = «1» + residue (x.p * x.q) := by
  rw [plus_residue, times_reciprocal_self]; ext <;> simp [scale, «1»]

/-! ## What the ratio does with a residue -/

/-- Under the ratio invariant, a residue is invisible where `k ≠ 0`. Where `k = 0` it is `0ω`, which
absorbs everything but itself. -/
theorem ratio_plus_residue (y : T) (k : ℤ) :
    Rel (nonZeroDivisors ℤ) (y + residue k) y ↔ (k ≠ 0 ∨ y = «0ω») := by
  rw [plus_residue]
  constructor
  · intro h
    by_cases hk : k = 0
    · right
      subst hk
      have hz : scale 0 y = «0ω» := by ext <;> simp [scale, «0ω»]
      rw [hz] at h
      exact ((ratioRel_iff _ _).mp h).1.mp rfl
    · exact Or.inl hk
  · rintro (hk | rfl)
    · exact ⟨1, one_mem _, k, mem_nonZeroDivisors_iff_ne_zero.mpr hk, by rw [scale_one]⟩
    · exact ⟨1, one_mem _, 1, one_mem _, by ext <;> simp [scale, «0ω»]⟩

/-- So the wheel's tangent addition and `⊗` have the same ratio exactly when neither argument is at a
quarter turn, or `⊗` itself landed on `0ω`. -/
theorem ratio_tanAdd (x y : T) :
    Rel (nonZeroDivisors ℤ) (tanAdd x y) (x ⊗ y) ↔ ((x.q ≠ 0 ∧ y.q ≠ 0) ∨ x ⊗ y = «0ω») := by
  rw [tanAdd_residue, ratio_plus_residue, mul_ne_zero_iff]

end T
