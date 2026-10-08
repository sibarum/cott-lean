import CottLean.T.LogPair

/-!
# The bridge to radians: `1^t`, `log` in base `e`, and the angle

`LogPair` reads a pair's logarithm as a scale and a turn, with no π stated. This file converts back:

* **The point from the pair.** `1^t` is the rotation by `t` turns (`oneTurn`): `1^(1/2) = −1`,
  `1^(1/4) = i`, `1^1 = 1`, and `1^(s + t) = 1^s · 1^t` (`oneTurn_half`, `oneTurn_quarter`, `oneTurn_one`,
  `oneTurn_add`). So `(−1)^t = 1^(t/2)` and `i^t = 1^(t/4)`. In any base `b > 0`, `b ≠ 1`, the scale and the
  turn give the point back: `C = b^(½·log_b N) · 1^turn` off the origin (`C_eq_logScale_turn`).
* **Base `e` and radians.** `Lrad = log(q + i·p)`, Lean's complex logarithm, is the pair in base `e` with
  the turn measured in radians: `Lrad = ½·log_e N + 2π·turn·i` (`Lrad_eq`). The angle `A = arg C` is
  `2π·turn` (`A_eq_turn`).

Everything below is stated with `π`, `exp` or `arg`.

* **The logarithm of the turn holds only on a branch.** `log(D + iS) = Lrad + ½ln 2 + iπ/4` exactly when
  `arg C ≤ 3π/4` (`log_sum_diff_iff`), since otherwise adding `π/4` leaves the principal range. It
  fails at `C = −1` (`log_sum_diff_ne`). Under `exp`, so modulo `2πi`, it holds off the origin
  (`exp_log_sum_diff`). `C = e^Lrad` off the origin (`exp_Lrad`).
* **Direction only.** `Q = tan(arg C) = tan(Im Lrad)` for every pair, the origin included
  (`Q_eq_tan_arg`, `Q_eq_tan_im_Lrad`). `D/S = tan(π/4 − arg C)` off the origin (`DS_eq_tan`), and at the
  origin it fails (`DS_eq_tan_fails`).
* **The angle keeps the ray.** `A = Im Lrad` (`A_eq_im_Lrad`), so `Q = tan A` and `D/S = tan(π/4 − A)`
  (`Q_eq_tan_A`, `DS_eq_tan_A`). A positive scaling keeps `A` and the half turn moves it (`A_smul`,
  `A_neg`), and off the origin two pairs have one `A` exactly when one is a positive multiple of the
  other (`A_eq_A_iff`). `⊗` adds it modulo `2π` (`A_pairOtimes`).
* **Scale only.** `S² + D² = 2e^(2 Re Lrad)` off the origin (`scale_eq`), and not at it (`scale_fails`).
* **Scale and angle together are `C`.** `C = |C|·e^(iA)` (`C_eq_polar`), and off the origin
  `C = e^(Re Lrad)·e^(iA)` (`C_eq_scale_angle`).
-/

namespace T.Unquotiented

open Complex
open scoped Real

/-- The logarithm in base `e`, with the turn in radians: Lean's `log(q + i·p)`. -/
noncomputable def Lrad (p q : ℝ) : ℂ := Complex.log (C p q)
/-- The angle in radians, `arg(q + i·p)`, in `(−π, π]`. -/
noncomputable def A (p q : ℝ) : ℝ := arg (C p q)

variable (p q : ℝ)

theorem exp_Lrad {p q : ℝ} (h : C p q ≠ 0) : Complex.exp (Lrad p q) = C p q := exp_log h
/-! ## The logarithm of the turn `1 + i` -/

theorem exp_half_log_two : Real.exp (Real.log 2 / 2) = √2 := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add, add_halves,
    Real.exp_log two_pos]

private theorem add_mul_I_eq (a b : ℝ) : (a : ℂ) + (b : ℂ) * I = ⟨a, b⟩ := by
  apply Complex.ext <;> simp

theorem log_one_add_I : Complex.log (1 + I) = (Real.log 2 / 2 : ℝ) + (π / 4 : ℝ) * I := by
  have h2 : √2 * (√2 / 2) = 1 := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hexp : Complex.exp ⟨Real.log 2 / 2, π / 4⟩ = 1 + I := by
    apply Complex.ext
    · rw [Complex.exp_re]
      change Real.exp (Real.log 2 / 2) * Real.cos (π / 4) = (1 + I).re
      rw [exp_half_log_two, Real.cos_pi_div_four, h2]; simp
    · rw [Complex.exp_im]
      change Real.exp (Real.log 2 / 2) * Real.sin (π / 4) = (1 + I).im
      rw [exp_half_log_two, Real.sin_pi_div_four, h2]; simp
  rw [add_mul_I_eq, ← hexp, log_exp]
  · change -π < π / 4; linarith [Real.pi_pos]
  · change π / 4 ≤ π; linarith [Real.pi_pos]

theorem arg_one_add_I : arg (1 + I) = π / 4 := by
  rw [← log_im, log_one_add_I, add_mul_I_eq]

/-- The branch condition: the turned logarithm is `Lrad + ½ln 2 + iπ/4` exactly when `arg C ≤ 3π/4`. -/
theorem log_sum_diff_iff {p q : ℝ} (h : C p q ≠ 0) :
    Complex.log (D p q + S p q * I) = Lrad p q + (Real.log 2 / 2 : ℝ) + (π / 4 : ℝ) * I ↔
      arg (C p q) ≤ 3 * π / 4 := by
  have hI : (1 + I : ℂ) ≠ 0 := by
    intro h0; simpa using congrArg im h0
  have : Lrad p q + (Real.log 2 / 2 : ℝ) + (π / 4 : ℝ) * I = Complex.log (1 + I) + Complex.log (C p q) := by
    rw [log_one_add_I, Lrad]; ring
  rw [this, sum_diff_eq, log_mul_eq_add_log_iff hI h, arg_one_add_I, Set.mem_Ioc]
  constructor
  · rintro ⟨-, h1⟩; linarith
  · intro h1; exact ⟨by linarith [neg_pi_lt_arg (C p q), Real.pi_pos], by linarith⟩

/-- At `C = −1` the turned logarithm leaves the principal range: the two sides differ by `2πi`. -/
theorem log_sum_diff_ne :
    Complex.log (D 0 (-1) + S 0 (-1) * I) ≠
      Lrad 0 (-1) + (Real.log 2 / 2 : ℝ) + (π / 4 : ℝ) * I := by
  intro h
  have him := congrArg im h
  have hl : C 0 (-1) = ((-1 : ℝ) : ℂ) := by apply Complex.ext <;> simp [C]
  rw [log_im] at him
  simp only [Lrad, add_im, log_im, hl, arg_ofReal_of_neg (show (-1 : ℝ) < 0 by norm_num), ofReal_re,
    ofReal_im, mul_im, I_re, I_im, mul_zero, mul_one, add_zero] at him
  linarith [arg_le_pi (↑(D 0 (-1)) + ↑(S 0 (-1)) * I), Real.pi_pos]

/-- Modulo `2πi`, that is under `exp`, the turned logarithm holds off the origin. -/
theorem exp_log_sum_diff {p q : ℝ} (h : C p q ≠ 0) :
    Complex.exp (Complex.log (D p q + S p q * I)) =
      Complex.exp (Lrad p q + (Real.log 2 / 2 : ℝ) + (π / 4 : ℝ) * I) := by
  have hI : (1 + I : ℂ) ≠ 0 := by
    intro h0; simpa using congrArg im h0
  have : Lrad p q + (Real.log 2 / 2 : ℝ) + (π / 4 : ℝ) * I = Complex.log (1 + I) + Complex.log (C p q) := by
    rw [log_one_add_I, Lrad]; ring
  rw [this, Complex.exp_add, exp_log hI, exp_log h, sum_diff_eq,
    exp_log (mul_ne_zero hI h)]

/-! ## Direction only -/

/-- The ratio is the tangent of the angle, for every pair: at the origin both are `0`. -/
theorem Q_eq_tan_arg : Q p q = Real.tan (arg (C p q)) := by
  by_cases h : C p q = 0
  · obtain ⟨rfl, rfl⟩ := (C_eq_zero_iff p q).mp h
    simp [Q, h]
  · rw [Real.tan_eq_sin_div_cos, sin_arg, cos_arg h, C_re, C_im, Q,
      div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr h)]

theorem Q_eq_tan_im_Lrad : Q p q = Real.tan (Lrad p q).im := by
  rw [Lrad, log_im, Q_eq_tan_arg]

theorem DS_eq_tan {p q : ℝ} (h : C p q ≠ 0) :
    D p q / S p q = Real.tan (π / 4 - arg (C p q)) := by
  have hr := norm_ne_zero_iff.mpr h
  have hk : √2 / 2 / ‖C p q‖ ≠ 0 := by positivity
  rw [Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four, sin_arg, cos_arg h, C_re, C_im]
  have hn : √2 / 2 * (q / ‖C p q‖) - √2 / 2 * (p / ‖C p q‖) = D p q * (√2 / 2 / ‖C p q‖) := by
    simp only [D]; ring
  have hd : √2 / 2 * (q / ‖C p q‖) + √2 / 2 * (p / ‖C p q‖) = S p q * (√2 / 2 / ‖C p q‖) := by
    simp only [S]; ring
  rw [hn, hd, mul_div_mul_right _ _ hk]

/-- At the origin `D/S` is `0` and `tan(π/4 − arg C)` is `1`. -/
theorem DS_eq_tan_fails : D 0 0 / S 0 0 ≠ Real.tan (π / 4 - arg (C 0 0)) := by
  have : C 0 0 = 0 := rfl
  rw [this, arg_zero, sub_zero, Real.tan_pi_div_four]
  norm_num [D, S]

/-! ## Scale only -/

theorem scale_eq {p q : ℝ} (h : C p q ≠ 0) :
    S p q ^ 2 + D p q ^ 2 = 2 * Real.exp (2 * (Lrad p q).re) := by
  have hr : 0 < ‖C p q‖ := norm_pos_iff.mpr h
  have : (2 : ℝ) * Real.log ‖C p q‖ = Real.log (‖C p q‖ ^ 2) := by
    rw [Real.log_pow]; norm_num
  rw [Lrad, log_re, this, Real.exp_log (by positivity), Complex.sq_norm, C, normSq_mk]
  simp only [S, D]; ring

/-- At the origin `S² + D²` is `0`, but `log 0 = 0` makes the right side `2`. -/
theorem scale_fails : S 0 0 ^ 2 + D 0 0 ^ 2 ≠ 2 * Real.exp (2 * (Lrad 0 0).re) := by
  have : C 0 0 = 0 := rfl
  simp [Lrad, this, S, D]

theorem Lrad_embL (n : ℝ) : Lrad (embL n).1 (embL n).2 = n := by
  have : C (embL n).1 (embL n).2 = ((Real.exp n : ℝ) : ℂ) := by apply Complex.ext <;> simp [embL, Complex.exp_ofReal_re]
  rw [Lrad, this, ← Complex.ofReal_log (Real.exp_pos n).le, Real.log_exp]
/-! ## The angle

`A` is the direction as a ray: `Q` and `D/S` are read from it, a positive scaling keeps it, and the half
turn moves it. With the scale `Re Lrad` it gives `C` back. -/

section Angle

variable (p q : ℝ)

theorem A_eq_im_Lrad : A p q = (Lrad p q).im := by rw [Lrad, log_im]; rfl

/-- On the integers, `A` is `θ`. -/
theorem A_theta (x : T) : A x.p x.q = theta x := rfl

theorem Q_eq_tan_A : Q p q = Real.tan (A p q) := Q_eq_tan_arg p q

theorem DS_eq_tan_A {p q : ℝ} (h : C p q ≠ 0) : D p q / S p q = Real.tan (π / 4 - A p q) :=
  DS_eq_tan h

/-- `C` in polar form: its norm, turned by `A`. -/
theorem C_eq_polar : C p q = ‖C p q‖ * exp (A p q * I) := (norm_mul_exp_arg_mul_I _).symm

/-- The scale `Re Lrad` and the angle `A` give `C` back, off the origin. -/
theorem C_eq_scale_angle {p q : ℝ} (h : C p q ≠ 0) :
    C p q = (Real.exp (Lrad p q).re : ℂ) * exp (A p q * I) := by
  rw [Lrad, log_re, Real.exp_log (norm_pos_iff.mpr h)]
  exact C_eq_polar p q

/-- A positive scaling keeps the angle. -/
theorem A_smul {t : ℝ} (ht : 0 < t) : A (t * p) (t * q) = A p q := by
  rw [A, C_smul, arg_real_mul _ ht]; rfl

/-- The half turn moves it, unlike `Q` and `D/S` (`Q_smul`, `DS_smul`). -/
theorem A_neg {p q : ℝ} (h : C p q ≠ 0) : A (-p) (-q) ≠ A p q := by
  intro heq
  have hn : C (-p) (-q) = -C p q := by apply Complex.ext <;> simp [C]
  have h1 := norm_mul_exp_arg_mul_I (C (-p) (-q))
  rw [hn, norm_neg] at h1
  rw [A, hn] at heq
  rw [heq, A, norm_mul_exp_arg_mul_I] at h1
  exact h (by linear_combination h1 / 2)

/-- Off the origin, two pairs have one angle exactly when one is a positive multiple of the other. -/
theorem A_eq_A_iff {p q p' q' : ℝ} (h : C p q ≠ 0) (h' : C p' q' ≠ 0) :
    A p q = A p' q' ↔ ∃ t : ℝ, 0 < t ∧ p' = t * p ∧ q' = t * q := by
  constructor
  · intro heq
    have hm := (arg_eq_arg_iff h h').mp heq
    refine ⟨‖C p' q'‖ / ‖C p q‖, div_pos (norm_pos_iff.mpr h') (norm_pos_iff.mpr h), ?_, ?_⟩
    · have := congrArg Complex.im hm
      simp only [C_im, ← ofReal_div, im_ofReal_mul] at this
      exact this.symm
    · have := congrArg Complex.re hm
      simp only [C_re, ← ofReal_div, re_ofReal_mul] at this
      exact this.symm
  · rintro ⟨t, ht, rfl, rfl⟩
    exact (A_smul p q ht).symm

/-- `⊗` adds angles, modulo `2π`, off the origin. -/
theorem A_pairOtimes {x y : ℝ × ℝ} (hx : C x.1 x.2 ≠ 0) (hy : C y.1 y.2 ≠ 0) :
    (A (pairOtimes x y).1 (pairOtimes x y).2 : Real.Angle) = A x.1 x.2 + A y.1 y.2 := by
  rw [A, C_pairOtimes]; exact arg_mul_coe_angle hx hy

end Angle

/-! ## `1^t`, and the point from the pair -/

/-- `1^t`: the rotation by `t` whole turns. -/
noncomputable def oneTurn (t : ℝ) : ℂ := Complex.exp (2 * π * t * I)

theorem oneTurn_add (s t : ℝ) : oneTurn (s + t) = oneTurn s * oneTurn t := by
  rw [oneTurn, oneTurn, oneTurn, ← Complex.exp_add]; congr 1; push_cast; ring

theorem oneTurn_zero : oneTurn 0 = 1 := by simp [oneTurn]

theorem oneTurn_one : oneTurn 1 = 1 := by
  simp only [oneTurn, ofReal_one, mul_one]; exact Complex.exp_two_pi_mul_I

theorem oneTurn_half : oneTurn (1 / 2) = -1 := by
  rw [oneTurn, show (2 * π * ((1 / 2 : ℝ) : ℂ) * I) = π * I by push_cast; ring]
  exact Complex.exp_pi_mul_I

theorem oneTurn_quarter : oneTurn (1 / 4) = I := by
  rw [oneTurn, show (2 * π * ((1 / 4 : ℝ) : ℂ) * I) = (π / 2 : ℂ) * I by push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

/-- A whole turn changes nothing: `1^t` has period `1`. -/
theorem oneTurn_add_one (t : ℝ) : oneTurn (t + 1) = oneTurn t := by
  rw [oneTurn_add, oneTurn_one, mul_one]

theorem A_eq_turn : A p q = 2 * π * turn p q := by
  rw [turn, A]; field_simp

theorem oneTurn_turn : oneTurn (turn p q) = Complex.exp (A p q * I) := by
  rw [oneTurn, A_eq_turn]; push_cast; ring_nf

/-- In any base, the scale and the turn give the point back: `C = b^(½·log_b N) · 1^turn`. -/
theorem C_eq_logScale_turn {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) {p q : ℝ} (h : C p q ≠ 0) :
    C p q = ((b ^ (logScale b p q / 2) : ℝ) : ℂ) * oneTurn (turn p q) := by
  have hn : b ^ (logScale b p q / 2) = ‖C p q‖ := by
    rw [logScale, show Real.logb b (N p q) / 2 = Real.logb b (N p q) * (1 / 2) by ring,
      Real.rpow_mul hb.le, Real.rpow_logb hb hb1 (N_pos h), N_eq_normSq,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rw [hn, oneTurn_turn]; exact C_eq_polar p q

/-- `Lrad` is the pair in base `e`, with the turn in radians. -/
theorem Lrad_eq : Lrad p q = ((Real.logb (Real.exp 1) (N p q) / 2 : ℝ) : ℂ) + ((2 * π * turn p q : ℝ) : ℂ) * I := by
  apply Complex.ext
  · rw [Lrad, log_re, N_eq_normSq, Real.logb, Real.log_exp, div_one, Real.log_pow]
    simp
  · rw [Lrad, log_im, ← A, A_eq_turn]; simp

end T.Unquotiented
