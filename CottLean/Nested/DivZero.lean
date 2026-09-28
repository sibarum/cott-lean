import CottLean.Nested.Basic
import CottLean.T.Angle

/-!
# `p/0 = tan(arg(p·i))`

The model's first line is `p/q = tan(arg(q + i·p))`. At `q = 0` it reads `p/0 = tan(arg(i·p))`. This file
asks what that rule gives, first for an integer `p`, then for a pair.

## An integer over zero

* `arg_intCast_mul_I_pos`, `arg_intCast_mul_I_neg`: for an integer `n ≠ 0`, `arg(n·i)` is `π/2` or `−π/2`.
  The rule sees the sign of `n` and nothing else.
* `tan_arg_intCast_mul_I`: and in Lean `tan(±π/2) = 0`, since `cos(π/2)` is exactly `0` and `x/0 = 0`. So
  the rule answers `0` for every integer, as Lean's own division does. Classically it answers `±∞`.

## A pair over zero

For a pair `p = T(a, b)`, the point is `b + a·i`, and `p·i` is `p ⊗ ω`, since `ω` is the point `i`.

* `divZero p = p ⊗ ω = T(b, −a)`, the quarter turn (`divZero_def`).
* `tan_arg_mul_I`: the rule is exact on it. `tan(arg(p·i)) = −b/a`, the negated reciprocal of `a/b`: the
  perpendicular slope.
* `divZero_otimes_negOmega`, `divZero_injective`: nothing is lost. Turning back with `⊗ −ω` recovers `p`.
* `divZero_times_zero`: but ordinary cancellation does not undo it. `(p/0)·0` has lost `b`
  (`divZero_times_zero_not_injective`).
* `divZero_perp`: `p/0` is perpendicular to `p`.

## Where `flatten` loses the numerator

`T2.flatten ⟨A, 0⟩ = T(a, 0)` drops `b` (`flatten_zero`, `flatten_zero_not_injective`). `divide` is
`flatten` with the rule at a zero denominator, and at `0` it keeps the whole numerator
(`divide_zero_injective`).

## Parallel lines

The lines `a₁x + b₁y = c₁` and `a₂x + b₂y = c₂` meet at `(Nx, Ny) / D` by Cramer's rule. When they are
parallel, `D = 0` and the division stops.

* `cramer_homogeneous`: `(Nx, Ny, D)` satisfies `a·x + b·y = c·w` for both lines, whatever `D` is. So at
  `D = 0`, `N` runs along both lines: it is the direction of the point at infinity where they meet
  (`along_line_of_parallel`).
* `direction` is that point as a pair, `T(Ny, Nx)`, and `tan(arg)` of it is the along-line slope `Ny/Nx`
  (`tan_arg_direction`).
* `rule_normal_of_parallel`: the rule applied to it lies along the normal `(a₁, b₁)` instead. It is off by
  exactly the quarter turn in `·i`, which the first line needs for an integer `p` and which is one turn
  too many once `p` is already a pair.
* `parallel_example`: `y = 0` and `y = 1`. The meeting point is horizontal, `T(0, −1)`, and the rule gives
  `−ω`, vertical.

## Without the `·i`

`divAlong p = p`, read by `tan(arg p) = a/b`: a pair over zero is its own direction, the point at infinity
of homogeneous coordinates.

* `divZero_eq_divAlong_otimes`: the first rule is this one turned by `⊗ ω`.
* `tan_arg_divAlong_intCast`: the two agree on integers. The integer `n` over zero is the pair `T(n, 0)`,
  and this rule on it is the first rule's `tan(arg(n·i))`. So the `·i` came from writing `n` over zero as
  a pair, and a pair needs no second one.
* `divAlong_injective`, `divideAlong_zero_injective`: it loses nothing either, and keeps what `flatten`
  drops. `·0` does not undo it (`divAlong_times_zero`).
* `divAlong_along_of_parallel`: for parallel lines it lies along both lines.
* `slope_meet_eq_tan_arg_divAlong`: where the lines do meet, its slope is the slope of the meeting point.
  So it gives the same answer on both sides of `D = 0`.
* `parallel_example_along`: `y = 0` and `y = 1` give `_0`, horizontal.
-/

open Complex T

namespace DivZero

/-! ## An integer over zero -/

theorem toC_intCast_omega (n : ℤ) : toC ⟨n, 0⟩ = (n : ℂ) * I := by
  apply Complex.ext <;> simp

/-- A positive integer over zero is at `π/2`. -/
theorem arg_intCast_mul_I_pos {n : ℤ} (hn : 0 < n) : arg ((n : ℂ) * I) = Real.pi / 2 := by
  have h : ((n : ℂ)) = ((n : ℝ) : ℂ) := by push_cast; rfl
  rw [h, arg_real_mul _ (by exact_mod_cast hn), arg_I]

/-- A negative integer over zero is at `−π/2`. -/
theorem arg_intCast_mul_I_neg {n : ℤ} (hn : n < 0) : arg ((n : ℂ) * I) = -(Real.pi / 2) := by
  have h : (n : ℂ) * I = ((-n : ℤ) : ℝ) * -I := by push_cast; ring
  rw [h, arg_real_mul _ (by exact_mod_cast neg_pos.mpr hn), arg_neg_I]

/-- In Lean the rule answers `0` for every integer, as `n / 0` does. -/
theorem tan_arg_intCast_mul_I (n : ℤ) : Real.tan (arg ((n : ℂ) * I)) = 0 := by
  have h := tan_theta ⟨n, 0⟩
  rw [theta, toC_intCast_omega] at h
  rw [h]; simp

/-! ## A pair over zero -/

/-- `p/0 = p ⊗ ω`: the point turned a quarter turn. -/
def divZero (p : T) : T := p ⊗ «ω»

@[simp] theorem divZero_def (p : T) : divZero p = ⟨p.q, -p.p⟩ := by
  ext <;> simp [divZero, otimes, «ω»]

theorem toC_omega : toC «ω» = I := by
  apply Complex.ext <;> simp [«ω»]

theorem toC_divZero (p : T) : toC (divZero p) = toC p * I := by
  rw [divZero, toC_otimes, toC_omega]

/-- The rule is exact on pairs: `tan(arg(p·i)) = −b/a`, the perpendicular slope. -/
theorem tan_arg_mul_I (p : T) : Real.tan (arg (toC p * I)) = -(p.q : ℝ) / p.p := by
  rw [← toC_divZero, ← theta, tan_theta]
  simp [div_neg, neg_div]

theorem divZero_otimes_negOmega (p : T) : divZero p ⊗ «-ω» = p := by
  ext <;> simp [otimes, «-ω»]

theorem divZero_injective : Function.Injective divZero := by
  intro p p' h
  rw [← divZero_otimes_negOmega p, h, divZero_otimes_negOmega]

/-- Cancelling by `0` does not undo it: only the numerator survives. -/
theorem divZero_times_zero (p : T) : divZero p * 0 = ⟨0, -p.p⟩ := by
  ext <;> simp [show (0 : T) = ⟨0, 1⟩ from rfl]

theorem divZero_times_zero_not_injective :
    divZero ⟨1, 1⟩ * 0 = divZero ⟨1, 2⟩ * 0 := by
  rw [divZero_times_zero, divZero_times_zero]

/-- `p/0` is perpendicular to `p`. -/
theorem divZero_perp (p : T) : dot p (divZero p) = 0 := by
  simp [dot]; ring

/-! ## Where `flatten` loses the numerator -/

theorem flatten_zero (A : T) : T2.flatten ⟨A, 0⟩ = ⟨A.p, 0⟩ := by
  ext <;> simp [show (0 : T) = ⟨0, 1⟩ from rfl]

theorem flatten_zero_not_injective : T2.flatten ⟨⟨1, 1⟩, 0⟩ = T2.flatten ⟨⟨1, 2⟩, 0⟩ := by
  rw [flatten_zero, flatten_zero]

/-- `A / B`, by `flatten`, with the rule at a zero denominator. -/
def divide (A B : T) : T := if B = 0 then divZero A else T2.flatten ⟨A, B⟩

theorem divide_zero (A : T) : divide A 0 = divZero A := if_pos rfl

theorem divide_ne_zero {B : T} (hB : B ≠ 0) (A : T) : divide A B = T2.flatten ⟨A, B⟩ := if_neg hB

/-- At a zero denominator the whole numerator comes back. -/
theorem divide_zero_injective : Function.Injective (fun A => divide A 0) := by
  intro A A' h
  simp only [divide_zero] at h
  exact divZero_injective h

/-! ## Parallel lines -/

/-- The line `a·x + b·y = c`. -/
structure Line where
  a : ℤ
  b : ℤ
  c : ℤ

/-- Cramer's denominator. The lines are parallel exactly when it is `0`. -/
def D (l m : Line) : ℤ := l.a * m.b - m.a * l.b
/-- Cramer's numerator for `x`. -/
def Nx (l m : Line) : ℤ := l.c * m.b - m.c * l.b
/-- Cramer's numerator for `y`. -/
def Ny (l m : Line) : ℤ := l.a * m.c - m.a * l.c

/-- `(Nx, Ny, D)` lies on both lines in homogeneous coordinates, whatever `D` is. -/
theorem cramer_homogeneous (l m : Line) :
    l.a * Nx l m + l.b * Ny l m = l.c * D l m ∧ m.a * Nx l m + m.b * Ny l m = m.c * D l m := by
  constructor <;> simp only [Nx, Ny, D] <;> ring

/-- Where `D ≠ 0`, that is the meeting point. -/
theorem cramer_meet (l m : Line) (hD : D l m ≠ 0) :
    (l.a : ℚ) * (Nx l m / D l m) + l.b * (Ny l m / D l m) = l.c ∧
      (m.a : ℚ) * (Nx l m / D l m) + m.b * (Ny l m / D l m) = m.c := by
  have hD' : (D l m : ℚ) ≠ 0 := by exact_mod_cast hD
  obtain ⟨h₁, h₂⟩ := cramer_homogeneous l m
  constructor <;> field_simp
  · rw [mul_comm (D l m : ℚ)]; exact_mod_cast h₁
  · rw [mul_comm (D l m : ℚ)]; exact_mod_cast h₂

/-- Where `D = 0`, `N` runs along both lines. -/
theorem along_line_of_parallel {l m : Line} (hD : D l m = 0) :
    l.a * Nx l m + l.b * Ny l m = 0 ∧ m.a * Nx l m + m.b * Ny l m = 0 := by
  obtain ⟨h₁, h₂⟩ := cramer_homogeneous l m
  rw [hD, mul_zero] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- The meeting point as a pair: the point `Nx + Ny·i`. -/
def direction (l m : Line) : T := ⟨Ny l m, Nx l m⟩

/-- Without the `·i`, `tan(arg)` is the slope `Ny/Nx` of the meeting point. -/
theorem tan_arg_direction (l m : Line) :
    Real.tan (arg (toC (direction l m))) = (Ny l m : ℝ) / Nx l m :=
  tan_theta (direction l m)

/-- The rule lies along the normal `(a₁, b₁)` of the first line, not along the line. -/
theorem rule_normal_of_parallel {l m : Line} (hD : D l m = 0) :
    l.a * (divZero (direction l m)).p - l.b * (divZero (direction l m)).q = 0 := by
  simp only [divZero_def, direction, mul_neg, sub_neg_eq_add]
  exact (along_line_of_parallel hD).1

/-- `y = 0` and `y = 1`: parallel, meeting horizontally at infinity, and the rule answers vertically. -/
theorem parallel_example :
    let l : Line := ⟨0, 1, 0⟩
    let m : Line := ⟨0, 1, 1⟩
    D l m = 0 ∧ direction l m = «_0» ∧ divZero (direction l m) = «-ω» := by
  refine ⟨rfl, rfl, ?_⟩
  rw [divZero_def]; rfl

/-! ## Without the `·i` -/

/-- `p/0 = p`, read by `tan(arg p)`: a pair over zero is its own direction. -/
def divAlong (p : T) : T := p

/-- The rule without the `·i` is `tan(arg p) = a/b`. -/
theorem tan_arg_divAlong (p : T) : Real.tan (arg (toC (divAlong p))) = (p.p : ℝ) / p.q :=
  tan_theta p

/-- The first rule is this one turned a quarter turn. -/
theorem divZero_eq_divAlong_otimes (p : T) : divZero p = divAlong p ⊗ «ω» := rfl

/-- On an integer over zero, the pair `T(n, 0)`, it is the first rule's `tan(arg(n·i))`. -/
theorem tan_arg_divAlong_intCast (n : ℤ) :
    Real.tan (arg (toC (divAlong ⟨n, 0⟩))) = Real.tan (arg ((n : ℂ) * I)) := by
  rw [divAlong, toC_intCast_omega]

theorem divAlong_injective : Function.Injective divAlong := fun _ _ h => h

/-- `·0` does not undo it either: only the denominator survives. -/
theorem divAlong_times_zero (p : T) : divAlong p * 0 = ⟨0, p.q⟩ := by
  ext <;> simp [divAlong, show (0 : T) = ⟨0, 1⟩ from rfl]

/-- `A / B`, by `flatten`, with `A` its own direction at a zero denominator. -/
def divideAlong (A B : T) : T := if B = 0 then divAlong A else T2.flatten ⟨A, B⟩

theorem divideAlong_zero (A : T) : divideAlong A 0 = A := if_pos rfl

theorem divideAlong_zero_injective : Function.Injective (fun A => divideAlong A 0) := by
  intro A A' h
  simpa only [divideAlong_zero] using h

/-- For parallel lines it lies along both lines. -/
theorem divAlong_along_of_parallel {l m : Line} (hD : D l m = 0) :
    l.a * (divAlong (direction l m)).q + l.b * (divAlong (direction l m)).p = 0 ∧
      m.a * (divAlong (direction l m)).q + m.b * (divAlong (direction l m)).p = 0 :=
  along_line_of_parallel hD

/-- Its slope is the slope of the meeting point where the lines do meet, so it gives the same answer on
both sides of `D = 0`. -/
theorem slope_meet_eq_tan_arg_divAlong (l m : Line) (hD : D l m ≠ 0) :
    ((Ny l m : ℝ) / D l m) / ((Nx l m : ℝ) / D l m) =
      Real.tan (arg (toC (divAlong (direction l m)))) := by
  have hD' : (D l m : ℝ) ≠ 0 := by exact_mod_cast hD
  rw [tan_arg_divAlong, div_div_div_cancel_right₀ hD']
  rfl

/-- `y = 0` and `y = 1`: it answers horizontally, where the lines meet. -/
theorem parallel_example_along :
    let l : Line := ⟨0, 1, 0⟩
    let m : Line := ⟨0, 1, 1⟩
    divAlong (direction l m) = «_0» := rfl

end DivZero
