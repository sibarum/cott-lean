import CottLean.T.Ternary
import CottLean.T.CommonMeadow

/-!
# The division form `T(a,m,b) = a / m + b` in three meadows

A planar ternary ring with `a·m` replaced by `a / m`, so that division is total. Which of Hall's five
axioms survive depends on what `0⁻¹` is.

| meadow | `0⁻¹` | axioms that hold | axioms that fail |
|---|---|---|---|
| involutive (Lean's own `ℚ`, any `Field`) | `0` | 1, `2a`, 3, 4, 5 | `2b`: `T(1,a,0) = 1/a ≠ a` |
| common (`ℚₐ`, `a` absorbing) | `a` | `2a` | 1 (`T(a,0,b) = a`), 3 (an absorbed `T` has no unique `b`) |
| neutral (`none = e`) | `e` | `2a` | 1 (`T(a,0,b) = a + b`) |

* `divT_eq_field`: `a / m + b = a·m⁻¹ + b`. The division form is the product form with the slope
  reciprocated, and `x ↦ x⁻¹` is a bijection of an involutive meadow, so axioms 3, 4 and 5 carry over.
* `divT_not_one_left`: axiom `2b` fails in any division form, not just here. `a / m` has a right identity
  `1` but no left identity. Hall's axiom 2 needs `1` on both sides. So the division form is a planar
  ternary ring only after the slope is reparametrized.
* `common_not_zero_mid`, `common_not_solvable`: an absorbing `a` destroys axioms 1 and 3.
* `neutral_zero_mid_fails`: with `e` neutral, `0⁻¹ = e` reads as the slope `1`, so the slope-`0` line is the
  slope-`1` line. This is the collision from the discussion of `T(a,e,b)`.
-/

section Involutive

variable {F : Type*} [Field F]

/-- `a / m + b`, with Lean's `0⁻¹ = 0`. -/
def divT (a m b : F) : F := a / m + b

theorem divT_eq_field (a m b : F) : divT a m b = (PlanarTernaryRing.ofField F).T a m⁻¹ b := by
  simp [divT, PlanarTernaryRing.ofField, div_eq_mul_inv]

theorem divT_zero_mid (a b : F) : divT a 0 b = b := by simp [divT]
theorem divT_zero_left (m b : F) : divT 0 m b = b := by simp [divT]
theorem divT_one_mid (a : F) : divT a 1 0 = a := by simp [divT]

theorem divT_solve_b (a m c : F) : ∃! b, divT a m b = c :=
  ⟨c - a / m, by simp [divT], fun y hy => by simp only [divT] at hy; linear_combination hy⟩

theorem divT_line_through (a a' b b' : F) (h : a ≠ a') :
    ∃! p : F × F, divT a p.1 p.2 = b ∧ divT a' p.1 p.2 = b' := by
  have hd : a - a' ≠ 0 := sub_ne_zero.mpr h
  refine ⟨(((b - b') / (a - a'))⁻¹, b - a * ((b - b') / (a - a'))), ⟨?_, ?_⟩, ?_⟩
  · simp [divT, div_eq_mul_inv]
  · simp only [divT, div_eq_mul_inv, inv_inv]
    field_simp
    ring
  · rintro ⟨m, k⟩ ⟨h1, h2⟩
    simp only [divT, div_eq_mul_inv] at h1 h2
    have e1 : m⁻¹ = (b - b') / (a - a') := by
      field_simp
      linear_combination h1 - h2
    have e2 : m = ((b - b') / (a - a'))⁻¹ := by rw [← e1, inv_inv]
    subst e2
    ext
    · rfl
    · simp only [inv_inv] at h1 ⊢
      linear_combination h1

theorem divT_meet (m m' k k' : F) (h : m ≠ m') : ∃! x, divT x m k = divT x m' k' := by
  have hd : m⁻¹ - m'⁻¹ ≠ 0 := sub_ne_zero.mpr (inv_injective.ne h)
  simp only [divT, div_eq_mul_inv]
  generalize m⁻¹ = u at hd ⊢
  generalize m'⁻¹ = v at hd ⊢
  refine ⟨(k' - k) / (u - v), ?_, fun x hx => ?_⟩
  · field_simp
    ring
  · rw [eq_div_iff hd]
    linear_combination hx

/-- Axiom `2b` fails: `a / m` has a right identity and no left identity. -/
theorem divT_not_one_left : ¬ ∀ a : ℚ, divT 1 a 0 = a := by
  intro h
  have := h 2
  norm_num [divT] at this

end Involutive

section Common

open T

/-- The common meadow's division form: `a / m + b`, with `a` absorbing. -/
def commonT (a m b : Qa) : Qa := Qa.add (Qa.mul a (Qa.inv m)) b

/-- Axiom 1 fails: a slope-`0` line is absorbed, `T(1,0,2) = a`, not `2`. -/
theorem common_not_zero_mid : ¬ ∀ a b : Qa, commonT a (some 0) b = b := by
  intro h
  have := h (some 1) (some 2)
  simp [commonT, Qa.inv, Qa.mul, Qa.add] at this

/-- Axiom 3 fails: once `T` is absorbed, every `b` gives it, so none is unique. -/
theorem common_not_solvable : ¬ ∀ a m c : Qa, ∃! b, commonT a m b = c := by
  intro h
  obtain ⟨b, _, hb⟩ := h none (some 1) none
  have h0 := hb (some 0) (by simp [commonT, Qa.mul, Qa.add])
  have h1 := hb (some 1) (by simp [commonT, Qa.mul, Qa.add])
  rw [← h1] at h0
  simp at h0

end Common

section Neutral

/-- `Option ℚ` with `none = e`, neutral for both `+` and `·`, and `0⁻¹ = e`. -/
def nAdd : Option ℚ → Option ℚ → Option ℚ
  | some x, some y => some (x + y)
  | none, y => y
  | x, none => x

def nMul : Option ℚ → Option ℚ → Option ℚ
  | some x, some y => some (x * y)
  | none, y => y
  | x, none => x

def nInv : Option ℚ → Option ℚ
  | some x => if x = 0 then none else some x⁻¹
  | none => none

def neutralT (a m b : Option ℚ) : Option ℚ := nAdd (nMul a (nInv m)) b

/-- Axiom 1 fails: `T(2,0,3) = 2/0 + 3 = 2 + 3`. The slope `0` reads as the slope `1`. -/
theorem neutral_zero_mid_fails : neutralT (some 2) (some 0) (some 3) = some 5 := by
  simp [neutralT, nInv, nMul, nAdd]
  norm_num

theorem neutral_not_zero_mid : ¬ ∀ a b : Option ℚ, neutralT a (some 0) b = b := by
  intro h
  have := h (some 2) (some 3)
  rw [neutral_zero_mid_fails] at this
  simp at this

end Neutral
