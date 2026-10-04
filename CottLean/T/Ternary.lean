import Mathlib.Tactic

/-!
# Planar ternary rings

Hall's coordinatization of a projective plane: a set `R` with `0 ≠ 1` and a ternary operation
`T(a, m, b)`, read `y = a·m + b`, with the point `a`, the slope `m` and the intercept `b`.

```
1.  T(a,0,b) = b = T(0,a,b)            2.  T(a,1,0) = a = T(1,a,0)
3.  a, m, c  ->  exactly one b with T(a,m,b) = c
4.  a ≠ a'   ->  exactly one line (m,k) through (a,b) and (a',b')
5.  m ≠ m'   ->  two lines meet in exactly one point
```

Nothing here asks for associativity or distributivity. Only unique solvability is required, which is the
weak form of reversibility that `Neutral` asks for.

* `PlanarTernaryRing`: the five axioms.
* `PlanarTernaryRing.ofField`: the baseline. Every field gives one, with `T(a,m,b) = a·m + b`. This is the
  Desarguesian plane. Everything else in the literature (Cartesian groups, quasifields, nearfields,
  Hall planes) is what happens when `a·m + b` is replaced by something less than a field.
-/

/-- A planar ternary ring: `T(a,m,b)` is the `y` of the line of slope `m` and intercept `b`, at the point `a`. -/
structure PlanarTernaryRing (R : Type*) where
  T : R → R → R → R
  zero : R
  one : R
  zero_ne_one : zero ≠ one
  T_zero_mid : ∀ a b, T a zero b = b
  T_zero_left : ∀ m b, T zero m b = b
  T_one_mid : ∀ a, T a one zero = a
  T_one_left : ∀ a, T one a zero = a
  solve_b : ∀ a m c, ∃! b, T a m b = c
  line_through : ∀ a a' b b', a ≠ a' → ∃! p : R × R, T a p.1 p.2 = b ∧ T a' p.1 p.2 = b'
  meet : ∀ m m' k k', m ≠ m' → ∃! x, T x m k = T x m' k'

namespace PlanarTernaryRing

/-- Every field is a planar ternary ring: the Desarguesian plane. -/
def ofField (F : Type*) [Field F] : PlanarTernaryRing F where
  T a m b := a * m + b
  zero := 0
  one := 1
  zero_ne_one := _root_.zero_ne_one
  T_zero_mid a b := by simp
  T_zero_left m b := by simp
  T_one_mid a := by simp
  T_one_left a := by simp
  solve_b a m c := ⟨c - a * m, by ring, fun y hy => by linear_combination hy⟩
  line_through a a' b b' h := by
    have hd : a - a' ≠ 0 := sub_ne_zero.mpr h
    refine ⟨((b - b') / (a - a'), b - a * ((b - b') / (a - a'))), ⟨by ring, ?_⟩, ?_⟩
    · field_simp
      ring
    · rintro ⟨m, k⟩ ⟨h1, h2⟩
      simp only at h1 h2
      have hm : m = (b - b') / (a - a') := by
        field_simp
        linear_combination h1 - h2
      subst hm
      ext
      · rfl
      · simp only; linear_combination h1
  meet m m' k k' h := by
    have hd : m - m' ≠ 0 := sub_ne_zero.mpr h
    refine ⟨(k' - k) / (m - m'), ?_, fun x hx => ?_⟩
    · field_simp
      ring
    · field_simp
      linear_combination hx

end PlanarTernaryRing
