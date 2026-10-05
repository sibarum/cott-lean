import CottLean.T.Angle

/-!
# The winding count: comparing a pair's turn with a rational, in integers

A turn is an angle as a fraction of the whole circle: `turn x = θ(x)/2π`, so `turn 1 = 1/8` and
`turn ω = 1/4`. A rational turn `a/b` is generally no pair's turn; past the multiples of 1/8 its tangent is
irrational. But whether a pair's turn is below `a/b` can be decided exactly, with no π:

* Walk the `⊗` powers `x, x², …, x^b`. Each step turns by `turn x`.
* Count the steps that cross the positive real ray: the numerator goes from negative to non-negative.
  That is `winding x b`, integer comparisons and `⊗` only.
* While `turn x` is under a half turn, no step can cross without being counted, so the count is the
  number of whole turns made: `winding x b = ⌊b · turn x⌋` (`winding_eq_floor`).
* So `turn x < a/b` exactly when `winding x b < a` (`turnLt_iff`). `a` is an integer, so the equality
  case falls out with no special handling.

π appears only in `turn`, which says what the count means. `winding` and `turnLt` never touch it.
-/

namespace T

open Complex

/-- The turn: `θ(x)/2π`, in `(−1/2, 1/2]`. -/
noncomputable def turn (x : T) : ℝ := theta x / (2 * Real.pi)

/-- How many of the first `b` steps of `x, x², …` cross the positive real ray: the numerator goes from
negative to non-negative. -/
def winding (x : T) : ℕ → ℕ
  | 0 => 0
  | k + 1 => winding x k + if (otimesPowNat x k).p < 0 ∧ 0 ≤ (otimesPowNat x (k + 1)).p then 1 else 0

/-! ## The turn of the named values -/

theorem turn_zero : turn 0 = 0 := by rw [turn, theta_zero]; simp

theorem turn_one : turn «1» = 1 / 8 := by
  rw [turn, theta_one]; field_simp; ring

theorem turn_omega : turn «ω» = 1 / 4 := by
  rw [turn, theta_omega]; field_simp; ring

/-! ## The powers' half-plane, read from the turn -/

/-- The point's lower half-plane is the upper half of the turn's fractional part. -/
theorem im_pow_neg_iff (z : ℂ) (k : ℕ) :
    (z ^ k).im < 0 ↔ 1 / 2 < Int.fract (k * (arg z / (2 * Real.pi))) := by
  have hπ := Real.pi_pos
  obtain ⟨m, hm⟩ : ∃ m : ℤ, arg (z ^ k) - k * arg z = 2 * Real.pi * m := by
    rw [← Real.Angle.angle_eq_iff_two_pi_dvd_sub, arg_pow_coe_angle, ← Real.Angle.coe_nsmul, nsmul_eq_mul]
  set σ := arg (z ^ k) / (2 * Real.pi) with hσ
  have hk : (k : ℝ) * (arg z / (2 * Real.pi)) = σ - m := by
    have e : (k : ℝ) * arg z = arg (z ^ k) - 2 * Real.pi * m := by linarith
    rw [hσ, ← mul_div_assoc, e, sub_div, mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi) ≠ 0)]
  have lo : -(1 / 2) < σ := by
    rw [hσ, lt_div_iff₀ (by positivity)]; linarith [neg_pi_lt_arg (z ^ k)]
  have hi : σ ≤ 1 / 2 := by
    rw [hσ, div_le_iff₀ (by positivity)]; linarith [arg_le_pi (z ^ k)]
  rw [hk, Int.fract_sub_intCast, ← arg_neg_iff]
  have hneg : arg (z ^ k) < 0 ↔ σ < 0 := by
    rw [hσ, div_neg_iff]; constructor
    · intro h; exact Or.inr ⟨h, by positivity⟩
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · linarith
      · exact h
  rw [hneg]
  constructor
  · intro h
    have : Int.fract σ = σ + 1 := by
      rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [this]; linarith
  · intro h
    rcases lt_or_ge σ 0 with hs | hs
    · exact hs
    · rw [Int.fract_eq_self.mpr ⟨hs, by linarith⟩] at h
      linarith

/-! ## Counting whole turns -/

/-- One step of size under a half turn passes a whole number exactly when it goes from the upper half
of the fractional part to the lower. -/
theorem floor_add_small (u t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1 / 2) :
    ⌊u + t⌋ = ⌊u⌋ + if 1 / 2 < Int.fract u ∧ ¬ 1 / 2 < Int.fract (u + t) then 1 else 0 := by
  have hf0 := Int.fract_nonneg u
  have hf1 := Int.fract_lt_one u
  have hu : u = ⌊u⌋ + Int.fract u := (Int.floor_add_fract u).symm
  by_cases hw : Int.fract u + t < 1
  · have hfl : ⌊u + t⌋ = ⌊u⌋ := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [Int.floor_le u]
    have hfr : Int.fract (u + t) = Int.fract u + t := by
      rw [← Int.self_sub_floor, hfl]; linarith
    rw [hfl, hfr, if_neg (by intro ⟨a, b⟩; exact b (by linarith))]; ring
  · replace hw := not_lt.mp hw
    have hfl : ⌊u + t⌋ = ⌊u⌋ + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have hfr : Int.fract (u + t) = Int.fract u + t - 1 := by
      rw [← Int.self_sub_floor, hfl]; push_cast; linarith
    rw [hfl, hfr, if_pos ⟨by linarith, by linarith⟩]

/-- Off the closed lower half-plane's negative axis, the turn is in `[0, 1/2)`. -/
theorem turn_mem {x : T} (h : 0 < x.p ∨ (x.p = 0 ∧ 0 ≤ x.q)) : 0 ≤ turn x ∧ turn x < 1 / 2 := by
  have hπ := Real.pi_pos
  have hnn : 0 ≤ theta x := by
    rw [theta, arg_nonneg_iff, toC_im]
    rcases h with h | ⟨h, _⟩ <;> [exact_mod_cast h.le; simp [h]]
  have hlt : theta x < Real.pi := by
    rw [theta, arg_lt_pi_iff, toC_re, toC_im]
    rcases h with h | ⟨_, h⟩
    · exact Or.inr (by exact_mod_cast h.ne')
    · exact Or.inl (by exact_mod_cast h)
  refine ⟨div_nonneg hnn (by positivity), ?_⟩
  rw [turn, div_lt_iff₀ (by positivity)]; linarith

/-- The power's numerator is negative exactly when the fractional turn is past a half. -/
theorem pow_p_neg_iff (x : T) (k : ℕ) : (otimesPowNat x k).p < 0 ↔ 1 / 2 < Int.fract (k * turn x) := by
  have e := im_pow_neg_iff (toC x) k
  rw [← toC_otimesPowNat, toC_im] at e
  rw [turn, theta]
  exact_mod_cast e

/-- **The winding count is the number of whole turns**: `⌊b · turn x⌋`, for a pair in the upper
half-plane or on the positive real ray. -/
theorem winding_eq_floor {x : T} (h : 0 < x.p ∨ (x.p = 0 ∧ 0 ≤ x.q)) (b : ℕ) :
    (winding x b : ℤ) = ⌊(b : ℝ) * turn x⌋ := by
  obtain ⟨t0, t1⟩ := turn_mem h
  have half := pow_p_neg_iff x
  induction b with
  | zero => simp [winding]
  | succ k ih =>
    rw [winding]
    push_cast
    rw [ih, show ((k : ℝ) + 1) * turn x = k * turn x + turn x by ring, floor_add_small _ _ t0 t1]
    congr 1
    have e1 := half k
    have e2 := half (k + 1)
    push_cast at e2
    rw [show ((k : ℝ) + 1) * turn x = k * turn x + turn x by ring] at e2
    by_cases c : (otimesPowNat x k).p < 0 ∧ 0 ≤ (otimesPowNat x (k + 1)).p
    · rw [if_pos c, if_pos ⟨e1.mp c.1, fun hh => absurd (e2.mpr hh) (not_lt.mpr c.2)⟩]
    · rw [if_neg c, if_neg fun ⟨a1, a2⟩ => c ⟨e1.mpr a1, not_lt.mp fun hh => a2 (e2.mp hh)⟩]

/-! ## By squaring

`winding` walks every power, `b` products. Squaring halves the walk: a doubled power wraps once more
exactly when the power was in the closed lower half-plane, `⌊2u⌋ = 2⌊u⌋ + [fract u ≥ 1/2]`
(`winding_double`), and a single step is `winding`'s own. So `powWind` finds `x^b` and the count together
in `O(log b)` products (`powWind_eq`). -/

/-- The turn's fractional part, through a power: `fract(k · turn z) = fract(turn (z^k))`. -/
theorem fract_pow_turn (z : ℂ) (k : ℕ) :
    Int.fract (k * (arg z / (2 * Real.pi))) = Int.fract (arg (z ^ k) / (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  obtain ⟨m, hm⟩ : ∃ m : ℤ, arg (z ^ k) - k * arg z = 2 * Real.pi * m := by
    rw [← Real.Angle.angle_eq_iff_two_pi_dvd_sub, arg_pow_coe_angle, ← Real.Angle.coe_nsmul, nsmul_eq_mul]
  have e : (k : ℝ) * arg z = arg (z ^ k) - 2 * Real.pi * m := by linarith
  rw [← mul_div_assoc, e, sub_div, mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi) ≠ 0),
    Int.fract_sub_intCast]

/-- The fractional turn is exactly a half on the negative real axis, and only there. -/
theorem fract_turn_eq_half_iff (w : ℂ) : Int.fract (arg w / (2 * Real.pi)) = 1 / 2 ↔ arg w = Real.pi := by
  have hπ := Real.pi_pos
  set σ := arg w / (2 * Real.pi) with hσ
  have lo : -(1 / 2) < σ := by
    rw [hσ, lt_div_iff₀ (by positivity)]; linarith [neg_pi_lt_arg w]
  have hi : σ ≤ 1 / 2 := by
    rw [hσ, div_le_iff₀ (by positivity)]; linarith [arg_le_pi w]
  have hpi : arg w = Real.pi ↔ σ = 1 / 2 := by
    rw [hσ, div_eq_iff (by positivity)]; constructor <;> intro h <;> linarith
  rw [hpi]
  rcases lt_or_ge σ 0 with hs | hs
  · have : Int.fract σ = σ + 1 := by
      rw [Int.fract_eq_iff]; refine ⟨by linarith, by linarith, -1, by push_cast; ring⟩
    rw [this]; constructor <;> intro h <;> linarith
  · rw [Int.fract_eq_self.mpr ⟨hs, by linarith⟩]

/-- The closed lower half-plane is the fractional turn at least a half. -/
theorem pow_lower_iff (x : T) (k : ℕ) :
    ((otimesPowNat x k).p < 0 ∨ ((otimesPowNat x k).p = 0 ∧ (otimesPowNat x k).q < 0)) ↔
      1 / 2 ≤ Int.fract (k * turn x) := by
  have e := fract_turn_eq_half_iff (toC x ^ k)
  rw [arg_eq_pi_iff, ← fract_pow_turn, ← toC_otimesPowNat, toC_re, toC_im] at e
  have e' : Int.fract (k * turn x) = 1 / 2 ↔ (otimesPowNat x k).p = 0 ∧ (otimesPowNat x k).q < 0 := by
    rw [turn, theta, e]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
  rw [le_iff_lt_or_eq, ← pow_p_neg_iff, eq_comm (a := (1 / 2 : ℝ)), e']

/-- `⌊2u⌋ = 2⌊u⌋ + [fract u ≥ 1/2]`. -/
theorem floor_two_mul (u : ℝ) : ⌊2 * u⌋ = 2 * ⌊u⌋ + if 1 / 2 ≤ Int.fract u then 1 else 0 := by
  have hf0 := Int.fract_nonneg u
  have hf1 := Int.fract_lt_one u
  have hu : u = ⌊u⌋ + Int.fract u := (Int.floor_add_fract u).symm
  split_ifs with h
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith

/-- Doubling the walk doubles the count, plus one if the half-way power is in the lower half-plane. -/
theorem winding_double {x : T} (h : 0 < x.p ∨ (x.p = 0 ∧ 0 ≤ x.q)) (m : ℕ) :
    winding x (2 * m) = 2 * winding x m +
      if (otimesPowNat x m).p < 0 ∨ ((otimesPowNat x m).p = 0 ∧ (otimesPowNat x m).q < 0) then 1 else 0 := by
  have e : (winding x (2 * m) : ℤ) = 2 * winding x m +
      if (otimesPowNat x m).p < 0 ∨ ((otimesPowNat x m).p = 0 ∧ (otimesPowNat x m).q < 0) then 1 else 0 := by
    rw [winding_eq_floor h, winding_eq_floor h]
    push_cast
    rw [mul_assoc, floor_two_mul]
    simp only [pow_lower_iff]
  exact_mod_cast e

theorem toC_injective : Function.Injective toC := by
  intro x y h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [toC_re, toC_im, Int.cast_inj] at hr hi
  ext <;> assumption

theorem otimesPowNat_add (x : T) (m n : ℕ) : otimesPowNat x (m + n) = otimesPowNat x m ⊗ otimesPowNat x n := by
  apply toC_injective
  rw [toC_otimes, toC_otimesPowNat, toC_otimesPowNat, toC_otimesPowNat, pow_add]

/-- `(x^b, winding x b)` by squaring, with `fuel` halvings available. -/
def powWindAux (x : T) : ℕ → ℕ → T × ℕ
  | 0, _ => (0, 0)
  | fuel + 1, b =>
    if b = 0 then (0, 0) else
      let r := powWindAux x fuel (b / 2)
      let y := r.1 ⊗ r.1
      let w := 2 * r.2 + if r.1.p < 0 ∨ (r.1.p = 0 ∧ r.1.q < 0) then 1 else 0
      if b % 2 = 0 then (y, w) else
        (y ⊗ x, w + if y.p < 0 ∧ 0 ≤ (y ⊗ x).p then 1 else 0)

/-- `(x^b, winding x b)` in `O(log b)` products. -/
def powWind (x : T) (b : ℕ) : T × ℕ := powWindAux x b b

theorem powWindAux_eq {x : T} (h : 0 < x.p ∨ (x.p = 0 ∧ 0 ≤ x.q)) (fuel : ℕ) :
    ∀ b ≤ fuel, powWindAux x fuel b = (otimesPowNat x b, winding x b) := by
  induction fuel with
  | zero => intro b hb; obtain rfl : b = 0 := by omega
            rfl
  | succ f ih =>
    intro b hb
    by_cases h0 : b = 0
    · subst h0; simp [powWindAux, otimesPowNat, winding, «0»]
    have hm := ih (b / 2) (by omega)
    have hb2 := Nat.div_add_mod b 2
    simp only [powWindAux, if_neg h0, hm]
    have hsq : otimesPowNat x (b / 2) ⊗ otimesPowNat x (b / 2) = otimesPowNat x (2 * (b / 2)) := by
      rw [two_mul, otimesPowNat_add]
    rw [hsq, ← winding_double h]
    by_cases hpar : b % 2 = 0
    · rw [if_pos hpar, show 2 * (b / 2) = b by omega]
    · rw [if_neg hpar]
      have hb' : b = 2 * (b / 2) + 1 := by omega
      generalize b / 2 = m at hb' ⊢
      subst hb'
      rfl

theorem powWind_eq {x : T} (h : 0 < x.p ∨ (x.p = 0 ∧ 0 ≤ x.q)) (b : ℕ) :
    powWind x b = (otimesPowNat x b, winding x b) :=
  powWindAux_eq h b b le_rfl

/-- `turn x < a/b`, decided by the winding count, found by squaring. -/
def turnLt (x : T) (a : ℤ) (b : ℕ) : Bool := decide (((powWind x b).2 : ℤ) < a)

/-- **The comparison, exactly**: `turn x < a/b` is decided by integers. -/
theorem turnLt_iff {x : T} (h : 0 < x.p ∨ (x.p = 0 ∧ 0 ≤ x.q)) (a : ℤ) {b : ℕ} (hb : 0 < b) :
    turnLt x a b = true ↔ turn x < a / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [turnLt, decide_eq_true_iff, powWind_eq h, winding_eq_floor h, Int.floor_lt, lt_div_iff₀ hb', mul_comm]

/-! ## Examples -/

/-- `T(1,2)` is under 1/12 of a turn (`arctan(1/2) ≈ 0.0738`), and over 1/14. -/
example : turnLt ⟨1, 2⟩ 1 12 = true ∧ turnLt ⟨1, 2⟩ 1 14 = false := by decide

/-- Sixteen steps of `T(1,2)` wind once: `⌊16 · 0.0738⌋ = 1`. -/
example : winding ⟨1, 2⟩ 16 = 1 := by decide

end T
