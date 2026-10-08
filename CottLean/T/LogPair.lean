import CottLean.T.Unquotiented
import CottLean.T.Winding
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The logarithm as a pair: a scale in any base, and a turn

```
L_b(p,q) = (log_b N, turn)        N = p² + q²
```

* **The scale** is `log_b N`, the logarithm of the squared norm, so no square root is taken. The base `b`
  is chosen only when converting. Changing it multiplies the scale by one constant and leaves the turn
  alone (`logScale_change_base`).
* **The turn** is the direction as a fraction of a whole turn, so `1/4` is a quarter turn. On the integers
  it is `T.turn` (`turn_toT`), and comparing it with a rational is decided in integers by the winding
  count (`turnLt_iff_turn`).

`⊗` adds both: the scale exactly (`logScale_pairOtimes`), the turn modulo `1` (`turn_pairOtimes`). So `L`
carries `⊗` to `+` coordinatewise (`L_pairOtimes`). A positive scaling keeps the turn (`turn_smul`), and two
pairs off the origin have one turn exactly when one is a positive multiple of the other
(`turn_eq_turn_iff`): the turn keeps the ray.

The real relations hold in any base `b > 0`: `Q(bᵖ, b^q) = b^(−D)` and `P(bᵖ, b^q) = b^S` (`Q_rpow`,
`P_rpow`), and for `p, q > 0`, `D(log_b p, log_b q) = −log_b Q` and `S(log_b p, log_b q) = log_b P`
(`D_logb`, `S_logb`).

Lean's circle is built from π, so `turn` is defined as `arg C / 2π`. That definition is the only place π
appears in this file; no statement mentions it. `Radians` turns the pair back into the point,
`C = b^(½·log_b N) · 1^turn`, with `1^t` the rotation by `t` turns.
-/

namespace T.Unquotiented

open Complex
open scoped Real

/-- The squared norm `p² + q²`: the scale, without a square root. -/
def N (p q : ℝ) : ℝ := p ^ 2 + q ^ 2

/-- The scale in base `b`: `log_b N`. -/
noncomputable def logScale (b p q : ℝ) : ℝ := Real.logb b (N p q)

/-- The direction as a fraction of a whole turn, in `(−1/2, 1/2]`. -/
noncomputable def turn (p q : ℝ) : ℝ := arg (C p q) / (2 * π)

/-- The logarithm as a pair: the scale in base `b`, and the turn. -/
noncomputable def L (b p q : ℝ) : ℝ × ℝ := (logScale b p q, turn p q)

theorem N_eq_normSq (p q : ℝ) : N p q = ‖C p q‖ ^ 2 := by
  rw [Complex.sq_norm, C, normSq_mk, N]; ring

theorem N_pos {p q : ℝ} (h : C p q ≠ 0) : 0 < N p q := by
  rw [N_eq_normSq]; exact pow_pos (norm_pos_iff.mpr h) 2

theorem N_pairOtimes (x y : ℝ × ℝ) :
    N (pairOtimes x y).1 (pairOtimes x y).2 = N x.1 x.2 * N y.1 y.2 := by
  simp only [N, pairOtimes]; ring

/-! ## `⊗` adds the scale and the turn -/

theorem logScale_pairOtimes (b : ℝ) {x y : ℝ × ℝ} (hx : C x.1 x.2 ≠ 0) (hy : C y.1 y.2 ≠ 0) :
    logScale b (pairOtimes x y).1 (pairOtimes x y).2 = logScale b x.1 x.2 + logScale b y.1 y.2 := by
  rw [logScale, N_pairOtimes, Real.logb_mul (N_pos hx).ne' (N_pos hy).ne']; rfl

theorem turn_pairOtimes {x y : ℝ × ℝ} (hx : C x.1 x.2 ≠ 0) (hy : C y.1 y.2 ≠ 0) :
    ∃ k : ℤ, turn (pairOtimes x y).1 (pairOtimes x y).2 = turn x.1 x.2 + turn y.1 y.2 + k := by
  have h := arg_mul_coe_angle hx hy
  rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have hpi : (2 * π) ≠ 0 := by positivity
  rw [turn, C_pairOtimes, show arg (C x.1 x.2 * C y.1 y.2) =
    arg (C x.1 x.2) + arg (C y.1 y.2) + 2 * π * k by linarith, turn, turn]
  field_simp

theorem L_pairOtimes (b : ℝ) {x y : ℝ × ℝ} (hx : C x.1 x.2 ≠ 0) (hy : C y.1 y.2 ≠ 0) :
    ∃ k : ℤ, L b (pairOtimes x y).1 (pairOtimes x y).2 = L b x.1 x.2 + L b y.1 y.2 + ((0 : ℝ), (k : ℝ)) := by
  obtain ⟨k, hk⟩ := turn_pairOtimes hx hy
  refine ⟨k, ?_⟩
  ext
  · simp [L, logScale_pairOtimes b hx hy]
  · simp [L, hk]

/-! ## The turn keeps the ray -/

theorem turn_smul (p q : ℝ) {t : ℝ} (ht : 0 < t) : turn (t * p) (t * q) = turn p q := by
  rw [turn, C_smul, arg_real_mul _ ht, turn]

theorem turn_eq_turn_iff {p q p' q' : ℝ} (h : C p q ≠ 0) (h' : C p' q' ≠ 0) :
    turn p q = turn p' q' ↔ ∃ t : ℝ, 0 < t ∧ p' = t * p ∧ q' = t * q := by
  have hpi : (2 * π) ≠ 0 := by positivity
  constructor
  · intro heq
    have ha : arg (C p q) = arg (C p' q') := by
      simp only [turn] at heq; field_simp at heq; exact heq
    have hm := (arg_eq_arg_iff h h').mp ha
    refine ⟨‖C p' q'‖ / ‖C p q‖, div_pos (norm_pos_iff.mpr h') (norm_pos_iff.mpr h), ?_, ?_⟩
    · have := congrArg Complex.im hm
      simp only [C_im, ← ofReal_div, im_ofReal_mul] at this
      exact this.symm
    · have := congrArg Complex.re hm
      simp only [C_re, ← ofReal_div, re_ofReal_mul] at this
      exact this.symm
  · rintro ⟨t, ht, rfl, rfl⟩
    exact (turn_smul p q ht).symm

/-- On the integers the turn is `T.turn`. -/
theorem turn_toT (x : T) : turn x.p x.q = T.turn x := rfl

/-- So comparing a pair's turn with `a/b` is decided by the winding count, in integers. -/
theorem turnLt_iff_turn {x : T} (h : 0 < x.p ∨ (x.p = 0 ∧ 0 ≤ x.q)) (a : ℤ) {b : ℕ} (hb : 0 < b) :
    turnLt x a b = true ↔ turn x.p x.q < a / b := by
  rw [turn_toT]; exact turnLt_iff h a hb

/-! ## Choosing the base -/

/-- Changing the base multiplies the scale by one constant, `log_c b`. The turn does not change. -/
theorem logScale_change_base {b : ℝ} (c : ℝ) (hb : Real.log b ≠ 0) (p q : ℝ) :
    logScale c p q = logScale b p q * Real.logb c b := by
  simp only [logScale, Real.logb]
  rw [div_mul_div_comm, mul_comm (Real.log (N p q)) (Real.log b), mul_div_mul_left _ _ hb]

theorem Q_rpow {b : ℝ} (hb : 0 < b) (p q : ℝ) : Q (b ^ p) (b ^ q) = b ^ (-D p q) := by
  rw [Q, D, neg_sub, Real.rpow_sub hb]

theorem P_rpow {b : ℝ} (hb : 0 < b) (p q : ℝ) : P (b ^ p) (b ^ q) = b ^ (S p q) := by
  rw [P, S, Real.rpow_add hb]

theorem D_logb (b : ℝ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    D (Real.logb b p) (Real.logb b q) = -Real.logb b (Q p q) := by
  rw [Q, Real.logb_div hp.ne' hq.ne', D, neg_sub]

theorem S_logb (b : ℝ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    S (Real.logb b p) (Real.logb b q) = Real.logb b (P p q) := by
  rw [P, Real.logb_mul hp.ne' hq.ne', S]

end T.Unquotiented
