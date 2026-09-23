import CottLean.T.Loss
import CottLean.T.MediantTree
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The angle column

The model's first line is `T(p, q) = p/q ≈ tan(arg(q + i·p))`. This file makes it exact.

* `θ(x) = arg(q + p·i)`, a real in `(−π, π]`, and `tan θ = p/q` for every pair (`tan_theta`). At a
  quarter turn both sides are Lean's `x/0 = 0`, so the line holds there as an equation too.
* The nine named values have the angles in the model's table (`theta_zero`, …, `theta_negOne`).
* As an angle mod `2π` (`angle`), `⊗` adds (`angle_otimes`), `-x` negates (`angle_neg`), `-_x` adds a
  half turn (`angle_oplusInverse`), the reciprocal reflects to `π/2 − θ` (`angle_reciprocal`), and the
  `n`th `⊗` power multiplies by `n` (`angle_otimesPowNat`). Each needs its pairs to be other than `0ω`,
  which has no angle.
* **The angle is the ray.** Two pairs other than `0ω` have the same angle exactly when they are positive
  multiples of one pair (`theta_eq_theta_iff_sameRay`). So of the invariants the conventions name, the
  angle and the ray are one.
* **The mediant lies between.** The sign of the angle from `x` to `y` is the sign of `det x y`
  (`sign_angle_sub`), the determinant `MediantTree` runs on. Since `det x (x ⊕ y) = det (x ⊕ y) y =
  det x y`, the mediant turns the same way from `x` as `y` does, and the same way into `y`
  (`mediant_between`). That is the angle-side meaning of the mediant tree.
* `principal` keeps the tangent, and moves the angle by a half turn or not at all (`tan_theta_principal`).
-/

namespace T

open Complex

/-! ## The point in ℂ -/

/-- `T(p, q) ↦ q + p·i`, in ℂ. -/
def toC (x : T) : ℂ := ⟨x.q, x.p⟩

@[simp] theorem toC_re (x : T) : (toC x).re = x.q := rfl
@[simp] theorem toC_im (x : T) : (toC x).im = x.p := rfl

theorem toC_eq_zero_iff (x : T) : toC x = 0 ↔ x = «0ω» := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp at hr hi
    ext <;> simp [«0ω», hr, hi]
  · rintro rfl; apply Complex.ext <;> simp [«0ω»]

theorem toC_ne_zero {x : T} (hx : x ≠ «0ω») : toC x ≠ 0 := fun h => hx ((toC_eq_zero_iff x).mp h)

theorem toC_otimes (x y : T) : toC (x ⊗ y) = toC x * toC y := by
  apply Complex.ext <;> simp [otimes]; ring

theorem toC_neg (x : T) : toC (-x) = (starRingEnd ℂ) (toC x) := by
  apply Complex.ext <;> simp

theorem toC_oplusInverse (x : T) : toC (oplusInverse x) = -toC x := by
  apply Complex.ext <;> simp [oplusInverse]

theorem toC_scale (k : ℤ) (x : T) : toC (scale k x) = ((k : ℝ) : ℂ) * toC x := by
  apply Complex.ext <;> simp [scale]

theorem toC_otimesPowNat (x : T) (n : ℕ) : toC (otimesPowNat x n) = toC x ^ n := by
  induction n with
  | zero => apply Complex.ext <;> simp [otimesPowNat, «0»]
  | succ n ih => rw [otimesPowNat, toC_otimes, ih, pow_succ]

/-! ## θ and the angle -/

/-- `θ(x) = arg(q + p·i)`, in `(−π, π]`. -/
noncomputable def theta (x : T) : ℝ := arg (toC x)

/-- `θ` as an angle, mod `2π`. -/
noncomputable def angle (x : T) : Real.Angle := theta x

/-- The model's first line: `tan θ = p/q`, for every pair. -/
theorem tan_theta (x : T) : Real.tan (theta x) = x.p / x.q := by
  rw [theta, tan_arg]; simp

/-! ### The table -/

theorem theta_zero : theta 0 = 0 := by
  have : toC 0 = ((1 : ℝ) : ℂ) := by apply Complex.ext <;> simp
  rw [theta, this, arg_ofReal_of_nonneg zero_le_one]

theorem theta_omega : theta «ω» = Real.pi / 2 := by
  have : toC «ω» = I := by apply Complex.ext <;> simp [«ω»]
  rw [theta, this, arg_I]

theorem theta_underZero : theta «_0» = Real.pi := by
  have : toC «_0» = -1 := by apply Complex.ext <;> simp [«_0»]
  rw [theta, this, arg_neg_one]

theorem theta_negOmega : theta «-ω» = -(Real.pi / 2) := by
  have : toC «-ω» = -I := by apply Complex.ext <;> simp [«-ω»]
  rw [theta, this, arg_neg_I]

theorem arg_one_add_I : arg (1 + I) = Real.pi / 4 := by
  have s : √2 * (√2 / 2) = 1 := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num)]; norm_num
  have h : (1 + I : ℂ) = ((√2 : ℝ) : ℂ) * (((√2 / 2 : ℝ) : ℂ) + ((√2 / 2 : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp [s]
  have := arg_cos_add_sin_mul_I (θ := Real.pi / 4)
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four] at this
  rw [h, arg_real_mul _ (by positivity), this]

theorem theta_one : theta «1» = Real.pi / 4 := by
  have : toC «1» = 1 + I := by apply Complex.ext <;> simp [«1»]
  rw [theta, this, arg_one_add_I]

theorem theta_negOne : theta «-1» = -(Real.pi / 4) := by
  have : toC «-1» = (starRingEnd ℂ) (1 + I) := by apply Complex.ext <;> simp [«-1»]
  rw [theta, this, arg_conj, arg_one_add_I, if_neg (by linarith [Real.pi_pos])]

theorem theta_underOne : theta «_1» = 3 * Real.pi / 4 := by
  have : toC «_1» = -((starRingEnd ℂ) (1 + I)) := by apply Complex.ext <;> simp [«_1»]
  rw [theta, this, arg_neg_eq_arg_add_pi_of_im_neg (by simp), arg_conj, arg_one_add_I,
    if_neg (by linarith [Real.pi_pos])]
  ring

theorem theta_negUnderOne : theta «-_1» = -(3 * Real.pi / 4) := by
  have : toC «-_1» = -(1 + I) := by apply Complex.ext <;> simp [«-_1»]
  rw [theta, this, arg_neg_eq_arg_sub_pi_of_im_pos (by simp), arg_one_add_I]
  ring

/-! ### What each operation does to the angle -/

theorem angle_otimes {x y : T} (hx : x ≠ «0ω») (hy : y ≠ «0ω») :
    angle (x ⊗ y) = angle x + angle y := by
  simp only [angle, theta, toC_otimes]
  exact arg_mul_coe_angle (toC_ne_zero hx) (toC_ne_zero hy)

theorem angle_neg (x : T) : angle (-x) = -angle x := by
  simp only [angle, theta, toC_neg]
  exact arg_conj_coe_angle _

theorem angle_oplusInverse {x : T} (hx : x ≠ «0ω») : angle (oplusInverse x) = angle x + Real.pi := by
  simp only [angle, theta, toC_oplusInverse]
  exact arg_neg_coe_angle (toC_ne_zero hx)

theorem angle_omega : angle «ω» = (Real.pi / 2 : ℝ) := by rw [angle, theta_omega]

/-- The reciprocal is the reflection `θ ↦ π/2 − θ`, where tan and cot trade. -/
theorem angle_reciprocal {x : T} (hx : x ≠ «0ω») :
    angle (reciprocal x) = (Real.pi / 2 : ℝ) - angle x := by
  have hn : -x ≠ «0ω» := fun h => hx (by rw [← neg_neg x, h]; decide)
  rw [reciprocal_eq_omega_otimes_neg, angle_otimes (by decide) hn, angle_omega, angle_neg,
    sub_eq_add_neg]

theorem angle_otimesPowNat (x : T) (n : ℕ) : angle (otimesPowNat x n) = n • angle x := by
  simp only [angle, theta, toC_otimesPowNat]
  exact arg_pow_coe_angle _ _

/-! ## The angle is the ray -/

/-- A positive multiple keeps θ. -/
theorem theta_scale {k : ℤ} (hk : 0 < k) (x : T) : theta (scale k x) = theta x := by
  rw [theta, toC_scale, arg_real_mul _ (by exact_mod_cast hk), theta]

/-- The dot product of the two points. -/
def dot (x y : T) : ℤ := x.q * y.q + x.p * y.p

/-- The angle from `x` to `y` is the argument of `y · conj x`, whose parts are `dot` and `det`. -/
theorem angle_sub_eq {x y : T} (hx : x ≠ «0ω») (hy : y ≠ «0ω») :
    angle y - angle x = (arg (toC y * (starRingEnd ℂ) (toC x)) : Real.Angle) := by
  rw [arg_mul_coe_angle (toC_ne_zero hy) (by simpa using toC_ne_zero hx), arg_conj_coe_angle,
    ← sub_eq_add_neg]; rfl

theorem re_mul_conj (x y : T) : (toC y * (starRingEnd ℂ) (toC x)).re = dot x y := by
  simp [dot]; ring

theorem im_mul_conj (x y : T) : (toC y * (starRingEnd ℂ) (toC x)).im = det x y := by
  simp [det]; ring

/-- Same angle exactly when `det = 0` and `dot > 0`. -/
theorem theta_eq_theta_iff {x y : T} (hx : x ≠ «0ω») (hy : y ≠ «0ω») :
    theta x = theta y ↔ det x y = 0 ∧ 0 < dot x y := by
  have hz : toC y * (starRingEnd ℂ) (toC x) ≠ 0 :=
    mul_ne_zero (toC_ne_zero hy) (by simpa using toC_ne_zero hx)
  have key : theta x = theta y ↔ arg (toC y * (starRingEnd ℂ) (toC x)) = 0 := by
    have e2 : (arg (toC y * (starRingEnd ℂ) (toC x)) : Real.Angle) = arg 1 ↔
        arg (toC y * (starRingEnd ℂ) (toC x)) = arg 1 := arg_coe_angle_eq_iff
    rw [arg_one, Real.Angle.coe_zero, ← angle_sub_eq hx hy, sub_eq_zero] at e2
    rw [← e2]
    constructor
    · intro h; simp only [angle, h]
    · intro h; simp only [angle, theta] at h; exact (arg_coe_angle_eq_iff.mp h).symm
  rw [key, arg_eq_zero_iff, re_mul_conj, im_mul_conj]
  constructor
  · rintro ⟨hre, him⟩
    have hdet : det x y = 0 := by exact_mod_cast him
    refine ⟨hdet, ?_⟩
    rcases (show (0 : ℤ) ≤ dot x y by exact_mod_cast hre).lt_or_eq with h | h
    · exact h
    · exfalso; apply hz
      apply Complex.ext
      · rw [re_mul_conj]; simp [← h]
      · rw [im_mul_conj]; simp [hdet]
  · rintro ⟨hdet, hdot⟩
    exact ⟨by exact_mod_cast hdot.le, by exact_mod_cast hdet⟩

/-- **The angle is the ray**: two pairs other than `0ω` have the same θ exactly when they are positive
multiples of one another. -/
theorem theta_eq_theta_iff_sameRay {x y : T} (hx : x ≠ «0ω») (hy : y ≠ «0ω») :
    theta x = theta y ↔ ∃ s t : ℤ, 0 < s ∧ 0 < t ∧ scale s x = scale t y := by
  rw [theta_eq_theta_iff hx hy]
  have nx : 0 < x.p ^ 2 + x.q ^ 2 := by
    rcases (show x.p ≠ 0 ∨ x.q ≠ 0 by
      by_contra h; push Not at h; exact hx (by ext <;> simp [«0ω», h.1, h.2])) with h | h <;> positivity
  constructor
  · rintro ⟨hdet, hdot⟩
    refine ⟨dot x y, x.p ^ 2 + x.q ^ 2, hdot, nx, ?_⟩
    simp only [det, dot] at hdet ⊢
    ext
    · simp only [scale]; linear_combination (-x.q) * hdet
    · simp only [scale]; linear_combination x.p * hdet
  · rintro ⟨s, t, hs, ht, h⟩
    have hp := congrArg T.p h
    have hq := congrArg T.q h
    simp only [scale] at hp hq
    constructor
    · have : s * t * det x y = 0 := by
        simp only [det]
        linear_combination (t * y.p) * hq - (t * y.q) * hp
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (mul_pos hs ht).ne'
      · exact h0
    · have ny : 0 < y.p ^ 2 + y.q ^ 2 := by
        rcases (show y.p ≠ 0 ∨ y.q ≠ 0 by
          by_contra h; push Not at h; exact hy (by ext <;> simp [«0ω», h.1, h.2])) with h | h <;>
          positivity
      have : s * dot x y = t * (y.p ^ 2 + y.q ^ 2) := by
        simp only [dot]; linear_combination y.q * hq + y.p * hp
      by_contra hle
      push Not at hle
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hs.le hle, mul_pos ht ny]

/-! ## The mediant lies between -/

theorem sign_intCast' (z : ℤ) : SignType.sign (z : ℝ) = SignType.sign z := by
  rcases lt_trichotomy z 0 with h | rfl | h
  · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
  · simp
  · rw [sign_pos h, sign_pos (by exact_mod_cast h)]

theorem sign_div_of_pos {a b : ℝ} (hb : 0 < b) : SignType.sign (a / b) = SignType.sign a := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · rw [sign_neg (div_neg_of_neg_of_pos h hb), sign_neg h]
  · simp
  · rw [sign_pos (div_pos h hb), sign_pos h]

/-- The angle from `x` to `y` turns the way `det x y` says. -/
theorem sign_angle_sub {x y : T} (hx : x ≠ «0ω») (hy : y ≠ «0ω») :
    (angle y - angle x).sign = SignType.sign (det x y) := by
  have hz : toC y * (starRingEnd ℂ) (toC x) ≠ 0 :=
    mul_ne_zero (toC_ne_zero hy) (by simpa using toC_ne_zero hx)
  rw [angle_sub_eq hx hy, Real.Angle.sign, Real.Angle.sin_coe, sin_arg, im_mul_conj,
    sign_div_of_pos (norm_pos_iff.mpr hz), sign_intCast']

/-- The mediant turns from `x` the way `y` does, and into `y` the same way: it lies between them. -/
theorem mediant_between {x y : T} (hx : x ≠ «0ω») (hy : y ≠ «0ω») (hxy : (x ⊕ y) ≠ «0ω») :
    (angle (x ⊕ y) - angle x).sign = (angle y - angle x).sign ∧
      (angle y - angle (x ⊕ y)).sign = (angle y - angle x).sign := by
  rw [sign_angle_sub hx hxy, sign_angle_sub hxy hy, sign_angle_sub hx hy, det_oplus_right,
    det_oplus_left, det_self, det_self]
  simp

/-! ## `principal` -/

/-- `principal` keeps the tangent. -/
theorem tan_theta_principal (x : T) : Real.tan (theta (principal x)) = Real.tan (theta x) := by
  rw [tan_theta, tan_theta, principal]
  split_ifs
  · simp [oplusInverse, neg_div_neg_eq]
  · rfl

/-- And moves the angle by a half turn, or not at all. -/
theorem angle_principal {x : T} (hx : x ≠ «0ω») :
    angle (principal x) = angle x ∨ angle (principal x) = angle x + Real.pi := by
  rw [principal]
  split_ifs
  · exact Or.inr (angle_oplusInverse hx)
  · exact Or.inl rfl

end T
