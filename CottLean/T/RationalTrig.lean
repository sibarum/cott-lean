import CottLean.T.Dial

/-!
# Rational trigonometry in turns

The cosine and sine of the turn `a/b`, as two rationals, from integers alone:

1. Halve the turn, `a/(2b)`, and split it into quarter turns: `a/(2b) = k/4 + c/(8b)` with `c` in
   `(0, 2b]` (`quarter_split`). Floor division, nothing more.
2. Dial `c/(8b)` for `n` steps (`Dial`), and keep the upper end `R`.
3. Turn `R` by `ω` if `k` is odd. Under the square, `ω` is a half turn, so this restores the quarter turns
   the split took off; even ones square away.
4. Square (`Spin`): `cosTurn = rotCos`, `sinTurn = rotSin` of that pair.

What is proved, for `b > 0`:

* `cosTurn_sq_add_sinTurn_sq`: `cos² + sin² = 1` exactly. The answer is always an exact rotation; only
  its angle is approximate.
* `cosTurn_err`, `sinTurn_err`: `(cosTurn − cos(2π·a/b))² ≤ π²/(n + 1)`, and the same for sine.
* `cosTurn_scale`, `sinTurn_scale`: `(k·a)/(k·b)` gives the same answer as `a/b` for every `k > 0`, at
  every depth: it is the turn that is dialed, not how it is written.

The bound is what the plain descent guarantees in the worst case; the descent usually does far better,
and the bracket it returns says exactly how well (`sin_sq_dial`). `spinTurn` is the pair itself, for
composing rotations as pairs before squaring (`rot_otimes`).
-/

namespace T

/-! ## The split into quarter turns -/

/-- `a/B` as `k/4 + c/(4B)`: `k = ⌊(4a − 1)/B⌋` and `c = (4a − 1) mod B + 1`. -/
def quarterSplit (a : ℤ) (B : ℕ) : ℤ × ℤ := ((4 * a - 1) / B, (4 * a - 1) % B + 1)

theorem quarter_split (a : ℤ) {B : ℕ} (hB : 0 < B) :
    0 < (quarterSplit a B).2 ∧ (quarterSplit a B).2 ≤ B ∧
      4 * a = (quarterSplit a B).1 * B + (quarterSplit a B).2 := by
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have h0 := Int.emod_nonneg (4 * a - 1) hB'.ne'
  have h1 := Int.emod_lt_of_pos (4 * a - 1) hB'
  have h2 := Int.ediv_mul_add_emod (4 * a - 1) (B : ℤ)
  simp only [quarterSplit]
  refine ⟨by omega, by omega, by linarith⟩

/-! ## The pair and its square -/

/-- The pair whose square is the rotation by `a/b` of a turn, to depth `n`. -/
def spinTurn (a : ℤ) (b : ℕ) (n : ℕ) : T :=
  let s := quarterSplit a (2 * b)
  (dial s.2 (4 * (2 * b)) n).2 ⊗ otimesPowNat «ω» (s.1 % 2).toNat

/-- `cos(2π·a/b)`, as a rational. -/
def cosTurn (a : ℤ) (b : ℕ) (n : ℕ) : ℚ := rotCos (spinTurn a b n)

/-- `sin(2π·a/b)`, as a rational. -/
def sinTurn (a : ℤ) (b : ℕ) (n : ℕ) : ℚ := rotSin (spinTurn a b n)

theorem rotCos_omegaPow (j : ℕ) : rotCos (otimesPowNat «ω» j) = (-1) ^ j ∧ rotSin (otimesPowNat «ω» j) = 0 := by
  induction j with
  | zero => constructor <;> simp [otimesPowNat, rotCos_eq, rotSin_eq, «0»]
  | succ j ih =>
    rw [otimesPowNat, rotCos_otimes, rotSin_otimes, ih.1, ih.2]
    exact ⟨by simp [rotCos_eq, rotSin_eq, «ω»]; ring, by simp [rotCos_eq, rotSin_eq, «ω»]⟩

theorem rotCos_otimes_omegaPow (x : T) (j : ℕ) :
    rotCos (x ⊗ otimesPowNat «ω» j) = (-1) ^ j * rotCos x ∧
      rotSin (x ⊗ otimesPowNat «ω» j) = (-1) ^ j * rotSin x := by
  rw [rotCos_otimes, rotSin_otimes, (rotCos_omegaPow j).1, (rotCos_omegaPow j).2]
  constructor <;> ring

theorem otimesPowNat_omega_ne (j : ℕ) : otimesPowNat «ω» j ≠ «0ω» := by
  induction j with
  | zero => decide
  | succ j ih =>
    intro h
    have := congrArg norm h
    rw [otimesPowNat, norm_otimes] at this
    have := norm_ne_zero_of_ne ih
    simp_all [norm, «ω», «0ω»]

theorem spinTurn_ne (a : ℤ) (b : ℕ) (n : ℕ) : spinTurn a b n ≠ «0ω» := by
  have h1 := norm_ne_zero_of_ne
    (ne_zeroOmega_of_det (det_dial (quarterSplit a (2 * b)).2 (4 * (2 * b)) n)).2
  have h2 := norm_ne_zero_of_ne (otimesPowNat_omega_ne ((quarterSplit a (2 * b)).1 % 2).toNat)
  intro h
  have := congrArg norm h
  simp only [spinTurn] at this
  rw [norm_otimes] at this
  exact mul_ne_zero h1 h2 (this.trans (by decide))

/-- **Exactly on the unit circle.** -/
theorem cosTurn_sq_add_sinTurn_sq (a : ℤ) (b : ℕ) (n : ℕ) : cosTurn a b n ^ 2 + sinTurn a b n ^ 2 = 1 :=
  rotCos_sq_add_rotSin_sq (spinTurn_ne a b n)

/-! ## The error -/

/-- `(−1)` to `k mod 2` is `(−1)^k`. -/
theorem neg_one_pow_toNat_emod_two (k : ℤ) : ((-1 : ℝ) ^ (k % 2).toNat) = (-1 : ℝ) ^ k := by
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, Even.neg_one_zpow (Int.even_iff.mpr h)]; simp
  · rw [h, Odd.neg_one_zpow (Int.odd_iff.mpr h)]; simp

/-- What both errors come down to: the target and the upper end, at `4π` times their turns, with the
quarter turns taken out the same way from both. -/
theorem turn_target (a : ℤ) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    let s := quarterSplit a (2 * b)
    2 * Real.pi * a / b = 4 * Real.pi * (s.2 / (4 * (2 * b : ℕ) : ℝ)) + s.1 * Real.pi ∧
      turn (dial s.2 (4 * (2 * b)) n).1 < s.2 / (4 * (2 * b : ℕ) : ℝ) ∧
      (s.2 : ℝ) / (4 * (2 * b : ℕ) : ℝ) ≤ turn (dial s.2 (4 * (2 * b)) n).2 := by
  intro s
  have hB : 0 < 2 * b := by omega
  obtain ⟨c0, c1, hsplit⟩ := quarter_split a hB
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  refine ⟨?_, ?_⟩
  · have e : (4 * a : ℝ) = s.1 * (2 * b : ℕ) + s.2 := by exact_mod_cast hsplit
    push_cast at e ⊢
    field_simp
    linear_combination e
  · have := dial_bracket (b := 4 * (2 * b)) c0 (by push_cast at c1 ⊢; omega) n
    push_cast at this ⊢
    exact this

/-- `|cos(4πu) − cos(4πv)| ≤ 4π·|u − v|`, squared, for the bracket's ends. -/
theorem err_sq {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ |x - y|) {sgn u v l : ℝ} (hs : sgn ^ 2 = 1)
    (hlv : l < v) (hvu : v ≤ u) (n : ℕ) (hw : (u - l) ^ 2 ≤ 1 / (16 * ((n : ℝ) + 1))) :
    (sgn * f (4 * Real.pi * u) - sgn * f (4 * Real.pi * v)) ^ 2 ≤ Real.pi ^ 2 / ((n : ℝ) + 1) := by
  have hπ := Real.pi_pos
  have h := hf (4 * Real.pi * u) (4 * Real.pi * v)
  have hd : |4 * Real.pi * u - 4 * Real.pi * v| ≤ 4 * Real.pi * (u - l) := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity), abs_of_nonneg (by linarith)]
    nlinarith
  have hfx : (f (4 * Real.pi * u) - f (4 * Real.pi * v)) ^ 2 ≤ (4 * Real.pi * (u - l)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_trans h hd) 2
  calc (sgn * f (4 * Real.pi * u) - sgn * f (4 * Real.pi * v)) ^ 2
      = sgn ^ 2 * (f (4 * Real.pi * u) - f (4 * Real.pi * v)) ^ 2 := by ring
    _ ≤ (4 * Real.pi * (u - l)) ^ 2 := by rw [hs, one_mul]; exact hfx
    _ = 16 * Real.pi ^ 2 * (u - l) ^ 2 := by ring
    _ ≤ 16 * Real.pi ^ 2 * (1 / (16 * ((n : ℝ) + 1))) := by gcongr
    _ = Real.pi ^ 2 / ((n : ℝ) + 1) := by field_simp

/-- **The cosine's error**: `(cosTurn − cos(2π·a/b))² ≤ π²/(n + 1)`. -/
theorem cosTurn_err (a : ℤ) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    ((cosTurn a b n : ℝ) - Real.cos (2 * Real.pi * a / b)) ^ 2 ≤ Real.pi ^ 2 / ((n : ℝ) + 1) := by
  obtain ⟨htarget, hl, hu⟩ := turn_target a hb n
  set s := quarterSplit a (2 * b)
  have hR := (ne_zeroOmega_of_det (det_dial s.2 (4 * (2 * b)) n)).2
  have hc : (cosTurn a b n : ℝ) = (-1) ^ s.1 * Real.cos (4 * Real.pi * turn (dial s.2 (4 * (2 * b)) n).2) := by
    simp only [cosTurn, spinTurn]
    rw [(rotCos_otimes_omegaPow _ _).1]
    push_cast
    rw [rotCos_eq_cos hR, neg_one_pow_toNat_emod_two]
    congr 2; simp only [turn]; field_simp; ring
  rw [hc, htarget, Real.cos_add_int_mul_pi]
  exact err_sq Real.abs_cos_sub_cos_le (by rw [← zpow_natCast, ← zpow_mul]; simp [Even.neg_one_zpow])
    hl hu n (turn_width_dial _ _ n)

/-- **The sine's error**: `(sinTurn − sin(2π·a/b))² ≤ π²/(n + 1)`. -/
theorem sinTurn_err (a : ℤ) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    ((sinTurn a b n : ℝ) - Real.sin (2 * Real.pi * a / b)) ^ 2 ≤ Real.pi ^ 2 / ((n : ℝ) + 1) := by
  obtain ⟨htarget, hl, hu⟩ := turn_target a hb n
  set s := quarterSplit a (2 * b)
  have hR := (ne_zeroOmega_of_det (det_dial s.2 (4 * (2 * b)) n)).2
  have hc : (sinTurn a b n : ℝ) = (-1) ^ s.1 * Real.sin (4 * Real.pi * turn (dial s.2 (4 * (2 * b)) n).2) := by
    simp only [sinTurn, spinTurn]
    rw [(rotCos_otimes_omegaPow _ _).2]
    push_cast
    rw [rotSin_eq_sin hR, neg_one_pow_toNat_emod_two]
    congr 2; simp only [turn]; field_simp; ring
  rw [hc, htarget, Real.sin_add_int_mul_pi]
  exact err_sq Real.abs_sin_sub_sin_le (by rw [← zpow_natCast, ← zpow_mul]; simp [Even.neg_one_zpow])
    hl hu n (turn_width_dial _ _ n)

/-! ## The turn, not its spelling

`a/b` and `(k·a)/(k·b)` are one turn, and the descent cannot tell them apart: the split's remainder
scales with `k` and its quotient does not, and every comparison inside the descent is `turn M < a/b`
itself (`turnLt_iff`). So `cos(2/12)` is `cos(1/6)` at every depth. -/

/-- A comparison with `(k·a)/(k·b)` is the comparison with `a/b`. -/
theorem turnLt_scale {x : T} (h : 0 < x.p ∨ (x.p = 0 ∧ 0 ≤ x.q)) (a : ℤ) {b k : ℕ} (hb : 0 < b)
    (hk : 0 < k) : turnLt x (k * a) (k * b) = turnLt x a b := by
  rw [Bool.eq_iff_iff, turnLt_iff h _ (Nat.mul_pos hk hb), turnLt_iff h _ hb]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  rw [mul_div_mul_left _ _ hk']

/-- The descent toward `(k·a)/(k·b)` is the descent toward `a/b`, step for step. -/
theorem dial_scale (a : ℤ) {b k : ℕ} (hb : 0 < b) (hk : 0 < k) (n : ℕ) :
    dial (k * a) (k * b) n = dial a b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hM : 0 < ((dial a b n).1 ⊕ (dial a b n).2).p ∨
        (((dial a b n).1 ⊕ (dial a b n).2).p = 0 ∧ 0 ≤ ((dial a b n).1 ⊕ (dial a b n).2).q) := by
      obtain ⟨h1, h2, h3, h4⟩ := dial_nonneg a b n
      simp only [oplus]; omega
    simp only [dial, ih, dialStep, turnLt_scale hM a hb hk]

/-- Splitting `(k·a)/(k·B)` gives the same quarter turns, and `k` times the remainder. -/
theorem quarterSplit_scale (a : ℤ) {B k : ℕ} (hB : 0 < B) (hk : 0 < k) :
    quarterSplit (k * a) (k * B) = ((quarterSplit a B).1, k * (quarterSplit a B).2) := by
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have h0 := Int.emod_nonneg (4 * a - 1) hB'.ne'
  have h1 := Int.emod_lt_of_pos (4 * a - 1) hB'
  have h2 := Int.ediv_mul_add_emod (4 * a - 1) (B : ℤ)
  have key := (Int.ediv_emod_unique (a := 4 * (k * a) - 1) (b := (k : ℤ) * B)
    (q := (4 * a - 1) / B) (r := k * ((4 * a - 1) % B + 1) - 1) (by positivity)).2
    ⟨by linear_combination (k : ℤ) * h2, by nlinarith, by nlinarith⟩
  simp only [quarterSplit]
  push_cast
  rw [key.1, key.2]
  simp

/-- **A positive multiple of the turn is the same turn**: `spinTurn (k·a) (k·b) = spinTurn a b`. -/
theorem spinTurn_scale (a : ℤ) {b k : ℕ} (hb : 0 < b) (hk : 0 < k) (n : ℕ) :
    spinTurn (k * a) (k * b) n = spinTurn a b n := by
  simp only [spinTurn]
  rw [show 2 * (k * b) = k * (2 * b) by ring, quarterSplit_scale a (by omega) hk,
    show 4 * (k * (2 * b)) = k * (4 * (2 * b)) by ring, dial_scale _ (by omega) hk]

theorem cosTurn_scale (a : ℤ) {b k : ℕ} (hb : 0 < b) (hk : 0 < k) (n : ℕ) :
    cosTurn (k * a) (k * b) n = cosTurn a b n := by
  simp only [cosTurn, spinTurn_scale a hb hk]

theorem sinTurn_scale (a : ℤ) {b k : ℕ} (hb : 0 < b) (hk : 0 < k) (n : ℕ) :
    sinTurn (k * a) (k * b) n = sinTurn a b n := by
  simp only [sinTurn, spinTurn_scale a hb hk]

/-! ## Examples -/

/-- A sixth of a turn, 60°, to depth 8: `cos = 1/2` is approached by `rotCos`, exactly on the circle. -/
example : cosTurn 1 6 8 ^ 2 + sinTurn 1 6 8 ^ 2 = 1 := cosTurn_sq_add_sinTurn_sq 1 6 8

end T
