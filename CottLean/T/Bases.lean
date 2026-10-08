import CottLean.T.LogPair

/-!
# A base is held by its units, and `log_b` is defined for every base

`log_b z = log z / log b`, so a base enters only through its own logarithm. In the pair form of `L` that is
two units, each a ratio kept unreduced: the scale unit `log N_b` and the turn unit `turn b`. Then

```
log_b z = ( log N_z ÷ scale unit ,  turn z ÷ turn unit )
```

with `÷` traction's division of ratios, `(a : b) ÷ (c : d) = (a·d : b·c)` (`rdiv`), defined for every
divisor. So `log_b` is defined for every base, including those where the classical value is not.

| base | scale unit | turn unit | `log_b z` | Lean |
|---|---|---|---|---|
| `1`, a full turn | `0 : 1` | `1 : 1` | scale over `0`; the turn itself | `logBase_one` |
| `1`, the identity | `0 : 1` | `0 : 1` | both over `0` | `logBase_unit` |
| `−1` | `0 : 1` | `1/2 : 1` | scale over `0`; the turn in half turns | `logBase_negOne` |
| `i` | `0 : 1` | `1/4 : 1` | scale over `0`; the turn in quarter turns | `logBase_i` |
| `0` | `−1 : 0` | `0 : 0` | scale `0 : −1`; turn `0 : 0` | `logBase_zero` |
| `ω`, as a ratio | `1 : 0` | `0 : 0` | scale `0 : 1`; turn `0 : 0` | `logBase_omega` |

* **The named values are bases.** The base of the point `q + i·p` is `Base.ofPoint p q`. Traction's
  `0 = T(0,1)` is the point `1`, and its base is the identity `1`; `_0 = T(0,−1)` gives `−1`, and `ω = T(1,0)`
  read as a point gives `i` (`ofPoint_zero_one`, `ofPoint_zero_negOne`, `ofPoint_one_zero`).
* **The full-turn `1` is no point's base** (`ofPoint_ne_one`): a point's turn is at most a half. Its value
  cannot say which `1` it is; only the unreduced units can.
* **`ω` depends on the reading.** As a ratio, `1/0`, its scale unit is infinite; as a point it is `i`
  (`omega_ne_ofPoint_one_zero`).

## The rules for `0^(p/q)`

`zeroPow p q` states James's rules exactly, as the pair `L` of the result, a scale ratio and a turn ratio:

* `p` and `q` both non-zero: a rotation of zero magnitude, scale `−1 : 0` and turn `p : q`. Reading the
  rotation as `p/q` turns is this file's reading of "the rotation".
* `p = 0`: an oriented magnitude, `1` when `q > 0` and `−1` when `q < 0`.
* `q = 0`: the opposite orientation, `−1` when `p > 0` and `1` when `p < 0`.
* `p = q = 0`: no rule is given, so `none`.

So `0^(1/0) = −1`, `0^(0/1) = 1`, and `0^(1/1)` is the zero-magnitude rotation by one turn (`zeroPow_one_zero`,
`zeroPow_zero_one`, `zeroPow_one_one`). On the axes the orientation is the sign of `D = q − p`
(`zeroPow_axis_iff`).

Multiplying values adds their `L`, coordinatewise with fraction `+` (`Lmul`), and the exponents add with
fraction `+` too. Which exponent laws then hold, stated and not ruled on:

* On the axes the law holds: `0^0 · 0^ω = 0^(0 + ω)` (`zeroPow_axis_hom`).
* With a zero-magnitude factor it does not: `0^1 · 0^ω` keeps a zero magnitude, and `0^(1 + ω) = 0^ω = −1`
  (`zeroPow_hom_fails`).
* `0^ω · 0^ω` is the full-turn `1`, unreduced (`zeroPow_omega_sq`), and `ω + ω = 0ω` lands on the case with
  no rule (`zeroPow_omega_add_omega`). So the law would ask `0^(0/0)` to be the full-turn `1`.
* `(−1)·(−1)` is the full-turn `1`, not the identity, while the turns are kept unreduced (`Lr_negOne_sq`).
-/

namespace T.Unquotiented

open Complex
open scoped Real

/-- A ratio `p : q`, read `p/q`, unreduced; `q` may be `0`. -/
abbrev Ratio := ℝ × ℝ

/-- Traction's division of ratios, `(a : b) ÷ (c : d) = (a·d : b·c)`: defined for every divisor. -/
def rdiv (x y : Ratio) : Ratio := (x.1 * y.2, x.2 * y.1)

/-- A base, held by its units: the scale unit and the turn unit. -/
structure Base where
  scaleUnit : Ratio
  turnUnit : Ratio

/-- The base of the point `q + i·p`: its `log N` and its turn. -/
noncomputable def Base.ofPoint (p q : ℝ) : Base := ⟨(Real.log (N p q), 1), (turn p q, 1)⟩

/-- `1` as a full turn. -/
def Base.one : Base := ⟨(0, 1), (1, 1)⟩
/-- `1` as the identity. -/
def Base.unit : Base := ⟨(0, 1), (0, 1)⟩
/-- `−1`, a half turn. -/
noncomputable def Base.negOne : Base := ⟨(0, 1), (1 / 2, 1)⟩
/-- `i`, a quarter turn. -/
noncomputable def Base.i : Base := ⟨(0, 1), (1 / 4, 1)⟩
/-- `0`: an infinite negative scale unit, and no turn. -/
def Base.zero : Base := ⟨(-1, 0), (0, 0)⟩
/-- `ω` read as a ratio, `1/0`: an infinite positive scale unit, and no turn. -/
def Base.omega : Base := ⟨(1, 0), (0, 0)⟩

/-- `L` of the point `q + i·p` as a pair of ratios: `(log N : 1, turn : 1)`. -/
noncomputable def Lr (p q : ℝ) : Ratio × Ratio := ((Real.log (N p q), 1), (turn p q, 1))

/-- `log_b z` as a pair of ratios: the scale over the scale unit, the turn over the turn unit. -/
noncomputable def logBase (B : Base) (p q : ℝ) : Ratio × Ratio :=
  (rdiv (Lr p q).1 B.scaleUnit, rdiv (Lr p q).2 B.turnUnit)

/-! ## `log_b` at each base -/

theorem logBase_one (p q : ℝ) :
    logBase Base.one p q = ((Real.log (N p q), 0), (turn p q, 1)) := by
  simp [logBase, Lr, rdiv, Base.one]

theorem logBase_unit (p q : ℝ) :
    logBase Base.unit p q = ((Real.log (N p q), 0), (turn p q, 0)) := by
  simp [logBase, Lr, rdiv, Base.unit]

theorem logBase_negOne (p q : ℝ) :
    logBase Base.negOne p q = ((Real.log (N p q), 0), (turn p q, 1 / 2)) := by
  simp [logBase, Lr, rdiv, Base.negOne]

theorem logBase_i (p q : ℝ) :
    logBase Base.i p q = ((Real.log (N p q), 0), (turn p q, 1 / 4)) := by
  simp [logBase, Lr, rdiv, Base.i]

theorem logBase_zero (p q : ℝ) : logBase Base.zero p q = ((0, -1), (0, 0)) := by
  simp [logBase, Lr, rdiv, Base.zero]

theorem logBase_omega (p q : ℝ) : logBase Base.omega p q = ((0, 1), (0, 0)) := by
  simp [logBase, Lr, rdiv, Base.omega]

/-- Read as a ratio, `log_{−1}` counts half turns and `log_i` quarter turns. -/
theorem Q_logBase_negOne (p q : ℝ) :
    Q (logBase Base.negOne p q).2.1 (logBase Base.negOne p q).2.2 = 2 * turn p q := by
  rw [logBase_negOne, Q]; ring

theorem Q_logBase_i (p q : ℝ) :
    Q (logBase Base.i p q).2.1 (logBase Base.i p q).2.2 = 4 * turn p q := by
  rw [logBase_i, Q]; ring

/-- At a base with non-zero units, both coordinates read as the ratio of logarithms. -/
theorem Q_logBase_ofPoint (p q b c : ℝ) :
    Q (logBase (Base.ofPoint b c) p q).1.1 (logBase (Base.ofPoint b c) p q).1.2 =
      Real.logb (N b c) (N p q) ∧
    Q (logBase (Base.ofPoint b c) p q).2.1 (logBase (Base.ofPoint b c) p q).2.2 = turn p q / turn b c := by
  simp [logBase, Lr, rdiv, Base.ofPoint, Q, Real.logb]

/-! ## The named values as bases -/

theorem turn_zero_one : turn 0 1 = 0 := by
  have : C 0 1 = 1 := by apply Complex.ext <;> simp [C]
  simp [turn, this]

theorem turn_zero_negOne : turn 0 (-1) = 1 / 2 := by
  have : C 0 (-1) = -1 := by apply Complex.ext <;> simp [C]
  rw [turn, this, arg_neg_one]; field_simp

theorem turn_one_zero : turn 1 0 = 1 / 4 := by
  have : C 1 0 = I := by apply Complex.ext <;> simp [C]
  rw [turn, this, arg_I]; field_simp; ring

/-- Traction's `0 = T(0,1)`, the point `1`, is the identity base. -/
theorem ofPoint_zero_one : Base.ofPoint 0 1 = Base.unit := by
  simp [Base.ofPoint, Base.unit, N, turn_zero_one]

/-- Traction's `_0 = T(0,−1)`, the point `−1`, is the half-turn base. -/
theorem ofPoint_zero_negOne : Base.ofPoint 0 (-1) = Base.negOne := by
  simp [Base.ofPoint, Base.negOne, N, turn_zero_negOne]

/-- Traction's `ω = T(1,0)`, read as the point `i`, is the quarter-turn base. -/
theorem ofPoint_one_zero : Base.ofPoint 1 0 = Base.i := by
  simp [Base.ofPoint, Base.i, N, turn_one_zero]

theorem turn_le_half (p q : ℝ) : turn p q ≤ 1 / 2 := by
  rw [turn, div_le_iff₀ (by positivity)]
  linarith [arg_le_pi (C p q)]

/-- The full-turn `1` is no point's base: a point's turn is at most a half. -/
theorem ofPoint_ne_one (p q : ℝ) : Base.ofPoint p q ≠ Base.one := by
  intro h
  have := congrArg (fun B => B.turnUnit.1) h
  simp only [Base.ofPoint, Base.one] at this
  linarith [turn_le_half p q]

/-- `ω` as a ratio is not `ω` as a point. -/
theorem omega_ne_ofPoint_one_zero : Base.omega ≠ Base.ofPoint 1 0 := by
  rw [ofPoint_one_zero]
  intro h
  have := congrArg (fun B => B.scaleUnit.2) h
  simp [Base.omega, Base.i] at this

/-! ## The rules for `0^(p/q)` -/

theorem Lr_zero_one : Lr 0 1 = ((0, 1), (0, 1)) := by simp [Lr, N, turn_zero_one]

theorem Lr_zero_negOne : Lr 0 (-1) = ((0, 1), (1 / 2, 1)) := by simp [Lr, N, turn_zero_negOne]

/-- James's rules for `0^(p/q)`, as the pair `L` of the result. `none` where no rule is given. -/
noncomputable def zeroPow (p q : ℝ) : Option (Ratio × Ratio) :=
  if p = 0 ∧ q = 0 then none
  else if p = 0 then some (if 0 < q then Lr 0 1 else Lr 0 (-1))
  else if q = 0 then some (if 0 < p then Lr 0 (-1) else Lr 0 1)
  else some ((-1, 0), (p, q))

theorem zeroPow_one_zero : zeroPow 1 0 = some (Lr 0 (-1)) := by simp [zeroPow]
theorem zeroPow_zero_one : zeroPow 0 1 = some (Lr 0 1) := by simp [zeroPow]
theorem zeroPow_one_one : zeroPow 1 1 = some ((-1, 0), (1, 1)) := by simp [zeroPow]
theorem zeroPow_zero_zero : zeroPow 0 0 = none := by simp [zeroPow]

/-- On the axes, `0^(p/q)` is `1` exactly when `D = q − p` is positive, and `−1` otherwise. -/
theorem zeroPow_axis_iff {p q : ℝ} (hax : p = 0 ∨ q = 0) (hne : ¬(p = 0 ∧ q = 0)) :
    zeroPow p q = some (Lr 0 1) ↔ 0 < D p q := by
  have h1 : Lr 0 1 ≠ Lr 0 (-1) := by
    rw [Lr_zero_one, Lr_zero_negOne]; intro h; have := congrArg (fun x => x.2.1) h; norm_num at this
  rcases hax with rfl | rfl
  · have hq : q ≠ 0 := fun h => hne ⟨rfl, h⟩
    by_cases h : 0 < q
    · simp [zeroPow, hq, h, D]
    · have : q < 0 := lt_of_le_of_ne (not_lt.mp h) hq
      simp [zeroPow, hq, h, D, h1.symm]
  · have hp : p ≠ 0 := fun h => hne ⟨h, rfl⟩
    by_cases h : 0 < p
    · simp [zeroPow, hp, h, D, h1.symm, h.le]
    · have : p < 0 := lt_of_le_of_ne (not_lt.mp h) hp
      simp [zeroPow, hp, h, D, this]

/-- Multiplying two values adds their `L`, each coordinate with fraction `+`. -/
def Lmul (x y : Ratio × Ratio) : Ratio × Ratio := (pairPlus x.1 y.1, pairPlus x.2 y.2)

/-- On the axes the exponent law holds: `0^0 · 0^ω = 0^(0 + ω)`, both `−1`. -/
theorem zeroPow_axis_hom :
    zeroPow (pairPlus (0, 1) (1, 0)).1 (pairPlus (0, 1) (1, 0)).2 = some (Lmul (Lr 0 1) (Lr 0 (-1))) := by
  rw [Lr_zero_one, Lr_zero_negOne]
  simp [zeroPow, pairPlus, Lmul, Lr_zero_negOne]

/-- With a zero-magnitude factor it fails: `0^1 · 0^ω` keeps the zero magnitude, `0^(1 + ω) = −1`. -/
theorem zeroPow_hom_fails :
    zeroPow (pairPlus (1, 1) (1, 0)).1 (pairPlus (1, 1) (1, 0)).2 ≠
      some (Lmul ((-1, 0), (1, 1)) (Lr 0 (-1))) := by
  rw [Lr_zero_negOne]
  simp [zeroPow, pairPlus, Lmul, Lr_zero_negOne]

/-- `(−1)·(−1)` is the full-turn `1`, not the identity, while the turns are kept unreduced. -/
theorem Lr_negOne_sq : Lmul (Lr 0 (-1)) (Lr 0 (-1)) = ((0, 1), (1, 1)) := by
  rw [Lr_zero_negOne]; simp [Lmul, pairPlus]; norm_num

/-- So `0^ω · 0^ω` is the full-turn `1`. -/
theorem zeroPow_omega_sq : zeroPow 1 0 = some (Lr 0 (-1)) ∧
    Lmul (Lr 0 (-1)) (Lr 0 (-1)) = ((0, 1), (1, 1)) := ⟨zeroPow_one_zero, Lr_negOne_sq⟩

/-- And `ω + ω = 0ω` lands on the case with no rule. -/
theorem zeroPow_omega_add_omega :
    zeroPow (pairPlus (1, 0) (1, 0)).1 (pairPlus (1, 0) (1, 0)).2 = none := by
  simp [zeroPow, pairPlus]

end T.Unquotiented
