import CottLean.T.Angle
import CottLean.T.Powers
import CottLean.T.PowerSum

/-!
# The power off the integers

The model writes `T(a,b)^T(c,d) = tan((c/d)·arctan(a/b))`: the angle scaled by `c/d`, read back as a
tangent. `Powers` has it at integer exponents as `otimesPower`, on the coordinates. This file reads it on
the angle, at every real exponent `r` (`anglePow x r = tan(r·θ(x))`), and says what happens off the
integers.

* **At the integers it is the power.** `tan(n·θ) = p/q` of `otimesPower x n`, for every pair and every
  `n : ℤ` (`anglePow_intCast`), since `otimesPower` scales the angle by `n` (`angle_otimesPower`).
* **`arctan(a/b)` is `θ` only up to a half turn**, and a half turn is invisible to an integer exponent and
  not to any other. Where `b ≠ 0`, the formula as written agrees with `anglePow` at every integer
  (`arctanPow_intCast`). At `r = 1/2` it does not: `_1 = T(1,−1)` and `-1 = T(−1,1)` have one ratio, so
  `arctan` gives them one half, `tan(−π/8)`, while their angles `3π/4` and `−π/4` have the halves
  `tan(3π/8)` and `tan(−π/8)` (`arctanPow_underOne_ne`). So off the integers the exponent reads the
  angle, not the ratio.
* **It leaves the pairs.** `1^(1/2) = tan(π/8) = √2 − 1` is no pair's ratio (`anglePow_one_half_ne`), and
  no pair's `⊗` square has the angle of `1` (`theta_otimes_self_ne_theta_one`): both come down to
  `2pq = q² − p²`, which is `(p + q)² = 2q²` (`pow_eq_two_mul_pow`). Some halves stay:
  `ω^(1/2) = 1` (`anglePow_omega_half`).
-/

namespace T

/-! ## The power on the angle -/

/-- `T(a,b)^r = tan(r·θ)`, at any real exponent `r`. -/
noncomputable def anglePow (x : T) (r : ℝ) : ℝ := Real.tan (r * theta x)

/-- The model's formula as written, through `arctan(a/b)`. -/
noncomputable def arctanPow (x : T) (r : ℝ) : ℝ := Real.tan (r * Real.arctan (x.p / x.q))

/-- The `n`th `⊗` power scales the angle by `n`, for every `n : ℤ`. -/
theorem angle_otimesPower (x : T) (n : ℤ) : angle (otimesPower x n) = n • angle x := by
  cases n with
  | ofNat n =>
    rw [show otimesPower x (Int.ofNat n) = otimesPowNat x n from rfl, angle_otimesPowNat,
      Int.ofNat_eq_natCast, natCast_zsmul]
  | negSucc n =>
    rw [show otimesPower x (Int.negSucc n) = otimesPowNat (-x) (n + 1) from rfl, angle_otimesPowNat,
      angle_neg, negSucc_zsmul, smul_neg]

/-- At an integer, `tan(n·θ)` is the ratio of the `n`th `⊗` power. -/
theorem anglePow_intCast (x : T) (n : ℤ) :
    anglePow x n = (otimesPower x n).p / (otimesPower x n).q := by
  rw [anglePow, ← tan_theta, ← Real.Angle.tan_coe, ← Real.Angle.tan_coe (theta (otimesPower x n))]
  congr 1
  change ((n * theta x : ℝ) : Real.Angle) = angle (otimesPower x n)
  rw [angle_otimesPower, angle, ← Real.Angle.coe_zsmul, zsmul_eq_mul]

/-! ## `arctan` and `θ` -/

/-- Off the quarter turns, `arctan(p/q)` is the angle of `principal x`. -/
theorem theta_principal_eq_arctan {x : T} (hq : x.q ≠ 0) :
    theta (principal x) = Real.arctan (x.p / x.q) := by
  have hpos : 0 < (principal x).q := by
    unfold principal
    split_ifs with h
    · simp only [oplusInverse]; omega
    · omega
  have hlt : |theta (principal x)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa using (show (0 : ℝ) < (principal x).q by
      exact_mod_cast hpos)))
  rw [← tan_theta, ← tan_theta_principal, Real.arctan_tan (abs_lt.mp hlt).1 (abs_lt.mp hlt).2]

/-- So `arctan(p/q)` is `θ` up to a whole number of half turns. -/
theorem arctan_eq_theta_add {x : T} (hq : x.q ≠ 0) :
    ∃ m : ℤ, Real.arctan (x.p / x.q) = theta x + m * Real.pi := by
  have hx : x ≠ «0ω» := fun h => hq (by simp [h, «0ω»])
  rw [← theta_principal_eq_arctan hq]
  rcases angle_principal hx with h | h
  · obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
    exact ⟨2 * k, by push_cast; linarith⟩
  · rw [angle, angle, ← Real.Angle.coe_add] at h
    obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
    exact ⟨2 * k + 1, by push_cast; linarith⟩

/-- At an integer the half turn washes out, and the formula as written is the power. -/
theorem arctanPow_intCast {x : T} (hq : x.q ≠ 0) (n : ℤ) : arctanPow x n = anglePow x n := by
  obtain ⟨m, hm⟩ := arctan_eq_theta_add hq
  rw [arctanPow, anglePow, hm, mul_add,
    show (n : ℝ) * (m * Real.pi) = ((n * m : ℤ) : ℝ) * Real.pi by push_cast; ring,
    Real.tan_add_int_mul_pi]

/-- `_1` and `-1` have one ratio, so `arctan` gives them one power at every exponent. -/
theorem arctanPow_underOne (r : ℝ) : arctanPow «_1» r = arctanPow «-1» r := by
  simp [arctanPow, «_1», «-1»]

theorem anglePow_underOne_half : anglePow «_1» (1 / 2) = Real.tan (3 * Real.pi / 8) := by
  rw [anglePow, theta_underOne]; ring_nf

theorem arctanPow_underOne_half : arctanPow «_1» (1 / 2) = Real.tan (-(Real.pi / 8)) := by
  simp only [arctanPow, «_1»]
  rw [show ((1 : ℤ) : ℝ) / ((-1 : ℤ) : ℝ) = -1 by norm_num, Real.arctan_neg, Real.arctan_one]; ring_nf

/-- **Off the integers the half turn shows**: at `r = 1/2`, the formula through `arctan` gives `_1` the
half of `-1`'s angle, `tan(−π/8)`, and the angle gives it `tan(3π/8)`. -/
theorem arctanPow_underOne_ne : arctanPow «_1» (1 / 2) ≠ anglePow «_1» (1 / 2) := by
  rw [arctanPow_underOne_half, anglePow_underOne_half]
  have := Real.pi_pos
  have hneg := Real.tan_neg_of_neg_of_pi_div_two_lt (x := -(Real.pi / 8)) (by linarith) (by linarith)
  have hpos := Real.tan_pos_of_pos_of_lt_pi_div_two (x := 3 * Real.pi / 8) (by positivity) (by linarith)
  exact ne_of_lt (hneg.trans hpos)

/-! ## Leaving the pairs -/

/-- `2pq = q² − p²` only at `p = q = 0`: it is `(p + q)² = 2q²`. -/
theorem two_mul_eq_sq_sub_sq {p q : ℤ} (h : 2 * p * q = q ^ 2 - p ^ 2) : p = 0 ∧ q = 0 := by
  obtain ⟨h1, h2⟩ := pow_eq_two_mul_pow le_rfl (show (p + q) ^ 2 = 2 * q ^ 2 by linear_combination h)
  exact ⟨by linarith, h2⟩

/-- `1^(1/2) = tan(π/8)`. -/
theorem anglePow_one_half : anglePow «1» (1 / 2) = Real.tan (Real.pi / 8) := by
  rw [anglePow, theta_one]; ring_nf

/-- **`1^(1/2)` is no pair's ratio.** `t = tan(π/8)` has `2t/(1 − t²) = tan(π/4) = 1`, and `t = p/q` would
make `2pq = q² − p²`. -/
theorem anglePow_one_half_ne (y : T) : anglePow «1» (1 / 2) ≠ y.p / y.q := by
  rw [anglePow_one_half]
  have := Real.pi_pos
  have ht : 0 < Real.tan (Real.pi / 8) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by linarith)
  have h2 : Real.tan (2 * (Real.pi / 8)) = 1 := by
    rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.tan_pi_div_four]
  rw [Real.tan_two_mul] at h2
  have hd : 1 - Real.tan (Real.pi / 8) ^ 2 ≠ 0 := by
    intro h; rw [h, div_zero] at h2; norm_num at h2
  have key : 2 * Real.tan (Real.pi / 8) = 1 - Real.tan (Real.pi / 8) ^ 2 := by
    field_simp at h2; linarith
  intro h
  by_cases hq : y.q = 0
  · rw [hq] at h; simp at h; linarith
  have hq' : (y.q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [h] at key
  field_simp at key
  have : 2 * y.p * y.q = y.q ^ 2 - y.p ^ 2 := by exact_mod_cast key
  exact hq (two_mul_eq_sq_sub_sq this).2

/-- In the pairs themselves: no `y ⊗ y` has the angle of `1`, so `1` has no `⊗` square root. -/
theorem theta_otimes_self_ne_theta_one (y : T) : theta (y ⊗ y) ≠ theta «1» := by
  rw [theta_one]
  by_cases hy : y ⊗ y = «0ω»
  · rw [hy, theta, (toC_eq_zero_iff _).mpr rfl, Complex.arg_zero]
    exact (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4).ne
  intro h
  rw [← theta_one, theta_eq_theta_iff_sameRay hy (by decide)] at h
  obtain ⟨s, t, hs, -, hst⟩ := h
  have hp := congrArg T.p hst
  have hq := congrArg T.q hst
  simp only [scale, otimes, «1»] at hp hq
  have : s * (2 * y.p * y.q - (y.q ^ 2 - y.p ^ 2)) = 0 := by linear_combination hp - hq
  have := two_mul_eq_sq_sub_sq (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hs.ne'))
  exact hy (by ext <;> simp [otimes, «0ω», this.1, this.2])

/-- Some halves stay: `ω^(1/2) = tan(π/4) = 1`. -/
theorem anglePow_omega_half : anglePow «ω» (1 / 2) = 1 := by
  rw [anglePow, theta_omega, show (1 / 2 : ℝ) * (Real.pi / 2) = Real.pi / 4 by ring, Real.tan_pi_div_four]

end T
