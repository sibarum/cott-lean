import CottLean.T.Winding
import CottLean.T.Spin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Dialing in a turn: the mediant descent

To find the pairs nearest the turn `a/b`, start from the bracket `(0, ω)`, a quarter turn wide, and
repeat: take the mediant `M = L ⊕ R`, ask `turnLt M a b`, and let `M` replace `L` if the target is past
it and `R` otherwise. As arithmetic, with `s` the test's bit, the step is

```
L' = L ⊕ s·R        R' = R ⊕ (1 − s)·L
```

so it needs no branch, only the one comparison inside `turnLt`. It is the descent of the mediant tree
(`MediantTree`) under a comparison that never names π.

## What is proved, for every `a/b` in `(0, 1/4]`

* `det_dial`: the bracket always has `det L R = 1`. So `L` and `R` are coprime and neighbours in the
  tree, and `rot` from `Spin` applies to both.
* `dial_bracket`: `turn L < a/b ≤ turn R`, at every depth. The answer is certified, not rounded.
* `norm_dial`: `n + 2 ≤ N(L) + N(R)` after `n` steps, so the pairs keep growing.
* `sin_sq_dial`: the bracket's exact width: `sin²(θR − θL) = 1/(N(L)·N(R))`, a ratio of integers.
* `turn_width_dial`: so `(turn R − turn L)² ≤ 1/(16(n + 1))`: the bracket closes around the target.

The bound is the plain descent's. It is slow where the tree is (long runs of one direction), and it is
what the integers alone guarantee.
-/

namespace T

/-! ## The step -/

/-- One step of the descent: the mediant replaces `L` if the target is past it, `R` otherwise. -/
def dialStep (a : ℤ) (b : ℕ) (br : T × T) : T × T :=
  let s : ℤ := if turnLt (br.1 ⊕ br.2) a b then 1 else 0
  (br.1 ⊕ scale s br.2, br.2 ⊕ scale (1 - s) br.1)

/-- `n` steps from `(0, ω)`. -/
def dial (a : ℤ) (b : ℕ) : ℕ → T × T
  | 0 => (0, «ω»)
  | n + 1 => dialStep a b (dial a b n)

/-- The step without the arithmetic: which end the mediant replaces. -/
theorem dialStep_eq (a : ℤ) (b : ℕ) (L R : T) :
    dialStep a b (L, R) = if turnLt (L ⊕ R) a b then (L ⊕ R, R) else (L, L ⊕ R) := by
  unfold dialStep
  split_ifs <;> ext <;> simp [scale, oplus, add_comm]

/-! ## The bracket's integers -/

theorem det_dial (a : ℤ) (b : ℕ) (n : ℕ) : det (dial a b n).1 (dial a b n).2 = 1 := by
  induction n with
  | zero => simp only [dial]; decide
  | succ n ih =>
    rw [dial, dialStep_eq]
    split_ifs
    · rw [det_oplus_left, det_self, add_zero]; exact ih
    · rw [det_oplus_right, det_self, zero_add]; exact ih

/-- Both ends stay in the closed first quadrant. -/
theorem dial_nonneg (a : ℤ) (b : ℕ) (n : ℕ) :
    0 ≤ (dial a b n).1.p ∧ 0 ≤ (dial a b n).1.q ∧ 0 ≤ (dial a b n).2.p ∧ 0 ≤ (dial a b n).2.q := by
  induction n with
  | zero => simp only [dial]; decide
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [dial, dialStep_eq]
    split_ifs <;> simp only [oplus] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The neighbours are coprime. -/
theorem dial_isCoprime (a : ℤ) (b : ℕ) (n : ℕ) :
    IsCoprime (dial a b n).1.p (dial a b n).1.q ∧ IsCoprime (dial a b n).2.p (dial a b n).2.q := by
  have h := det_dial a b n
  refine ⟨?_, isCoprime_of_det_eq_one h⟩
  have h' : det (oplusInverse (dial a b n).2) (dial a b n).1 = 1 := by
    rw [← h]; simp [det, oplusInverse]; ring
  exact isCoprime_of_det_eq_one h'

/-- A pair with `det = 1` against anything is not `0ω`. -/
theorem ne_zeroOmega_of_det {x y : T} (h : det x y = 1) : x ≠ «0ω» ∧ y ≠ «0ω» := by
  constructor <;> rintro rfl <;> simp [det, «0ω»] at h

theorem one_le_norm {x : T} (hx : x ≠ «0ω») : 1 ≤ norm x := by
  have h1 := norm_ne_zero_of_ne hx
  have h2 : 0 ≤ norm x := by unfold norm; positivity
  omega

/-- The pairs keep growing: after `n` steps the norms sum to at least `n + 2`. -/
theorem norm_dial (a : ℤ) (b : ℕ) (n : ℕ) : (n : ℤ) + 2 ≤ norm (dial a b n).1 + norm (dial a b n).2 := by
  induction n with
  | zero => simp only [dial]; decide
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := dial_nonneg a b n
    obtain ⟨hL, hR⟩ := ne_zeroOmega_of_det (det_dial a b n)
    have nL := one_le_norm hL
    have nR := one_le_norm hR
    set L := (dial a b n).1
    set R := (dial a b n).2
    -- `N(L ⊕ R) = N(L) + N(R) + 2·(L · R)`, and the dot product is not negative here.
    have hM : norm L + norm R ≤ norm (L ⊕ R) := by
      simp only [norm, oplus]; nlinarith [mul_nonneg h1 h3, mul_nonneg h2 h4]
    rw [dial, dialStep_eq]
    split_ifs <;> push_cast <;> linarith

/-! ## The bracket's turns -/

/-- **The bracket is certified**: for a target `a/b` in `(0, 1/4]`, `turn L < a/b ≤ turn R` at every
depth. -/
theorem dial_bracket {a : ℤ} {b : ℕ} (ha : 0 < a) (hab : 4 * a ≤ b) (n : ℕ) :
    turn (dial a b n).1 < a / b ∧ (a : ℝ) / b ≤ turn (dial a b n).2 := by
  have hb : 0 < b := by omega
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  induction n with
  | zero =>
    simp only [dial]
    rw [turn_zero, turn_omega]
    constructor
    · exact div_pos (by exact_mod_cast ha) hb'
    · rw [div_le_iff₀ hb']; have : (4 * a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := dial_nonneg a b n
    set L := (dial a b n).1
    set R := (dial a b n).2
    have hM : 0 < (L ⊕ R).p ∨ ((L ⊕ R).p = 0 ∧ 0 ≤ (L ⊕ R).q) := by
      simp only [oplus]; omega
    rw [dial, dialStep_eq]
    by_cases ht : turnLt (L ⊕ R) a b = true
    · rw [if_pos ht]; exact ⟨(turnLt_iff hM a hb).mp ht, ih.2⟩
    · rw [if_neg ht]
      exact ⟨ih.1, not_lt.mp fun h => ht ((turnLt_iff hM a hb).mpr h)⟩

/-- The sine of the angle from `x` to `y` is their determinant over their lengths. -/
theorem sin_theta_sub {x y : T} (hx : x ≠ «0ω») (hy : y ≠ «0ω») :
    Real.sin (theta y - theta x) = det x y / (‖toC x‖ * ‖toC y‖) := by
  have zx := toC_ne_zero hx
  have zy := toC_ne_zero hy
  have nx : ‖toC x‖ ≠ 0 := norm_ne_zero_iff.mpr zx
  have ny : ‖toC y‖ ≠ 0 := norm_ne_zero_iff.mpr zy
  rw [Real.sin_sub, theta, theta, Complex.sin_arg, Complex.sin_arg, Complex.cos_arg zx, Complex.cos_arg zy]
  simp only [toC_re, toC_im, det]
  field_simp
  push_cast
  ring

theorem norm_toC_sq (x : T) : ‖toC x‖ ^ 2 = (norm x : ℝ) := by
  rw [Complex.sq_norm, Complex.normSq_apply, norm]; simp; ring

/-- **The bracket's exact width**: `sin²(θR − θL) = 1/(N(L)·N(R))`. -/
theorem sin_sq_dial (a : ℤ) (b : ℕ) (n : ℕ) :
    Real.sin (theta (dial a b n).2 - theta (dial a b n).1) ^ 2 =
      1 / ((norm (dial a b n).1 : ℝ) * norm (dial a b n).2) := by
  obtain ⟨hL, hR⟩ := ne_zeroOmega_of_det (det_dial a b n)
  rw [sin_theta_sub hL hR, det_dial, div_pow, mul_pow, norm_toC_sq, norm_toC_sq]
  simp

/-- In the closed first quadrant, `θ` is in `[0, π/2]`. -/
theorem theta_mem_quadrant {x : T} (hp : 0 ≤ x.p) (hq : 0 ≤ x.q) :
    0 ≤ theta x ∧ theta x ≤ Real.pi / 2 := by
  constructor
  · rw [theta, Complex.arg_nonneg_iff, toC_im]; exact_mod_cast hp
  · rw [theta, Complex.arg_le_pi_div_two_iff, toC_re]; exact Or.inl (by exact_mod_cast hq)

/-- **The bracket closes**: after `n` steps, `(turn R − turn L)² ≤ 1/(16(n + 1))`. -/
theorem turn_width_dial (a : ℤ) (b : ℕ) (n : ℕ) :
    (turn (dial a b n).2 - turn (dial a b n).1) ^ 2 ≤ 1 / (16 * ((n : ℝ) + 1)) := by
  have hπ := Real.pi_pos
  obtain ⟨h1, h2, h3, h4⟩ := dial_nonneg a b n
  obtain ⟨hL, hR⟩ := ne_zeroOmega_of_det (det_dial a b n)
  set L := (dial a b n).1
  set R := (dial a b n).2
  obtain ⟨l0, l1⟩ := theta_mem_quadrant h1 h2
  obtain ⟨r0, r1⟩ := theta_mem_quadrant h3 h4
  set w := theta R - theta L
  -- The width is positive: its sine is `1/(|L|·|R|) > 0`, and it is within a quarter turn either way.
  have hsin : 0 < Real.sin w := by
    rw [sin_theta_sub hL hR, det_dial]
    have := norm_ne_zero_iff.mpr (toC_ne_zero hL)
    have := norm_ne_zero_iff.mpr (toC_ne_zero hR)
    push_cast; positivity
  have w0 : 0 ≤ w := by
    by_contra hw
    have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_lt (not_le.mp hw)) (by linarith)
    linarith
  have w1 : w ≤ Real.pi / 2 := by linarith
  -- `sin w ≥ (2/π)·w`, and `sin² w = 1/(N(L)·N(R)) ≤ 1/(n + 1)`.
  have jordan := Real.mul_le_sin w0 w1
  have hs2 : Real.sin w ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
    rw [sin_sq_dial]
    have nL := one_le_norm hL
    have nR := one_le_norm hR
    have hsum := norm_dial a b n
    have hprod : (n : ℤ) + 1 ≤ norm L * norm R := by nlinarith
    have hprod' : (n : ℝ) + 1 ≤ (norm L : ℝ) * norm R := by exact_mod_cast hprod
    apply one_div_le_one_div_of_le (by positivity) hprod'
  have hw2 : (2 / Real.pi * w) ^ 2 ≤ 1 / ((n : ℝ) + 1) :=
    le_trans (pow_le_pow_left₀ (by positivity) jordan 2) hs2
  have hturn : turn R - turn L = (2 / Real.pi * w) / 4 := by
    simp only [turn, w]; field_simp; ring
  have e1 : 1 / (16 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 16 := by field_simp
  have e2 : (2 / Real.pi * w / 4) ^ 2 = (2 / Real.pi * w) ^ 2 / 16 := by ring
  rw [hturn, e1, e2]
  linarith

/-! ## Examples -/

/-- Five steps toward 1/12 of a turn, whose tangent is `1/√3`: `T(4,7) < 1/12 ≤ T(3,5)`. -/
example : dial 1 12 5 = (⟨4, 7⟩, ⟨3, 5⟩) := by decide

end T
