import CottLean.T.Bases
import CottLean.T.Radians

/-!
# `b^x` from a base's units

A base holds a scale unit and a turn unit (`Bases`). Raising it to `x` scales both units by `x`: the
magnitude is `e^(x·s/2)`, with `s` the scale unit `log N_b`, and the rotation is `1^(x·t)`, with `t` the turn
unit (`basePow`).

* `1` as a full turn gives `1^x`, `−1` gives `1^(x/2)`, `i` gives `1^(x/4)`, and `1` as the identity gives `1`
  (`basePow_one`, `basePow_negOne`, `basePow_i`, `basePow_unit`).
* `b^(x + y) = b^x · b^y` for every base (`basePow_add`).
* The base of a point raised to `1` is the point (`basePow_ofPoint_one`).

`basePow` reads each unit through its ratio, and Lean's `x / 0 = 0` makes an infinite unit read as `0`. So
it is stated only for bases whose units have non-zero denominators. The bases `0` and `ω`, whose scale
units are over zero, are the pairs in `Bases` (`logBase_zero`, `logBase_omega`, `zeroPow`).
-/

namespace T.Unquotiented

open Complex
open scoped Real

/-- `b^x`: the magnitude `e^(x·s/2)` and the rotation `1^(x·t)`, from the units `s` and `t`. -/
noncomputable def basePow (B : Base) (x : ℝ) : ℂ :=
  (Real.exp (x * Q B.scaleUnit.1 B.scaleUnit.2 / 2) : ℂ) * oneTurn (x * Q B.turnUnit.1 B.turnUnit.2)

theorem basePow_one (x : ℝ) : basePow Base.one x = oneTurn x := by
  simp [basePow, Base.one, Q]

theorem basePow_negOne (x : ℝ) : basePow Base.negOne x = oneTurn (x / 2) := by
  simp [basePow, Base.negOne, Q]; ring_nf

theorem basePow_i (x : ℝ) : basePow Base.i x = oneTurn (x / 4) := by
  simp [basePow, Base.i, Q]; ring_nf

theorem basePow_unit (x : ℝ) : basePow Base.unit x = 1 := by
  simp [basePow, Base.unit, Q, oneTurn_zero]

theorem basePow_add (B : Base) (x y : ℝ) : basePow B (x + y) = basePow B x * basePow B y := by
  simp only [basePow, add_mul, add_div, Real.exp_add, ofReal_mul, oneTurn_add]
  ring

/-- The base of a point, raised to `1`, is the point. -/
theorem basePow_ofPoint_one {p q : ℝ} (h : C p q ≠ 0) : basePow (Base.ofPoint p q) 1 = C p q := by
  have hn : Real.exp (Real.log (N p q) / 2) = ‖C p q‖ := by
    rw [show Real.log (N p q) / 2 = Real.log (N p q) * (1 / 2) by ring, Real.exp_mul,
      Real.exp_log (N_pos h), N_eq_normSq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  simp only [basePow, Base.ofPoint, Q, div_one, one_mul]
  rw [hn, oneTurn_turn]
  exact (C_eq_polar p q).symm

end T.Unquotiented
