import CottLean.Float.Tropical
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Tropical grades, and the bookkeeping stays

`Tropical` drops the higher term of a sum, so `+` forgets. Keep it instead. A coordinate is a formal
sum of terms `c·ε^k`, a finitely supported map `ℤ →₀ ℚ` from grade to coefficient, and:

* its **grade** is the lowest `k` with `c ≠ 0`. That is all the value sees (`val`).
* every other term is **bookkeeping**: it stays in the sum, has no influence on the grade, and comes
  back when the terms below it cancel.

Then `+` is tropical on grades and lossless on terms.

* `val_add_ge`: `val (x + y) ≥ min (val x) (val y)`.
* `val_add_of_lt`: with different grades it is exactly the `min`, and the higher term is still there
  (`add_sub_cancel_left`).
* `val_add_gt`: equal grades whose leading coefficients cancel do not make a `none`. The grade
  rises, and the next term of the bookkeeping is the new leading one (`cancel_example`).
* `val_shift`: multiplying by `c·ε^k` (`c ≠ 0`) shifts the grade by `k` and nothing else.
* `val_eq_top`: only the empty sum has no grade. That is the additive zero, and it is the one case that
  `Res` had to call `none`.

Multiplying two full sums (convolution) is not done here; multiplying by a single term is.
-/

namespace Tail

/-- A coordinate: grade ↦ coefficient. -/
abbrev Coord := ℤ →₀ ℚ

/-- The grade: the lowest power present. `⊤` for the empty sum. -/
noncomputable def val (x : Coord) : WithTop ℤ := x.support.min

theorem val_eq_top {x : Coord} : val x = ⊤ ↔ x = 0 := by
  simp [val, Finset.min_eq_top]

/-- The tropical inequality. -/
theorem val_add_ge (x y : Coord) : min (val x) (val y) ≤ val (x + y) := by
  unfold val
  rw [← Finset.min_union]
  exact Finset.min_mono Finsupp.support_add

/-- A term below the grade is not there. -/
theorem apply_of_lt {x : Coord} {k : ℤ} (h : (k : WithTop ℤ) < val x) : x k = 0 := by
  by_contra hne
  exact absurd (Finset.min_le (Finsupp.mem_support_iff.mpr hne)) (not_le.mpr h)

/-- The term at the grade is there. -/
theorem apply_val_ne {x : Coord} {k : ℤ} (h : val x = k) : x k ≠ 0 := by
  have hne : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro e; simp [val, e] at h
  have h1 : x.support.min = ((x.support.min' hne : ℤ) : WithTop ℤ) := (Finset.coe_min' hne).symm
  have hk : x.support.min' hne = k := by
    have : ((x.support.min' hne : ℤ) : WithTop ℤ) = k := h1.symm.trans h
    exact_mod_cast this
  exact Finsupp.mem_support_iff.mp (hk ▸ Finset.min'_mem _ hne)

/-- If every term below `k` is absent, the grade is at least `k`. -/
theorem le_val {x : Coord} {k : ℤ} (h : ∀ j < k, x j = 0) : (k : WithTop ℤ) ≤ val x := by
  apply Finset.le_min
  intro j hj
  have : x j ≠ 0 := Finsupp.mem_support_iff.mp hj
  exact_mod_cast not_lt.mp fun hjk => this (h j hjk)

/-- The grade is `k` exactly when the term at `k` is there and nothing is below it. -/
theorem val_eq_iff {x : Coord} {k : ℤ} : val x = k ↔ x k ≠ 0 ∧ ∀ j < k, x j = 0 := by
  constructor
  · intro h
    exact ⟨apply_val_ne h, fun j hj => apply_of_lt (h ▸ by exact_mod_cast hj)⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm (Finset.min_le (Finsupp.mem_support_iff.mpr h1)) (le_val h2)

/-- Different grades: the sum has the smaller one. -/
theorem val_add_of_lt {x y : Coord} (h : val x < val y) : val (x + y) = val x := by
  cases hx : val x with
  | top => rw [hx] at h; exact absurd h (not_lt_of_ge le_top)
  | coe a =>
    rw [hx] at h
    rw [val_eq_iff]
    have hxa := val_eq_iff.mp hx
    refine ⟨?_, fun j hj => ?_⟩
    · simp [apply_of_lt h, hxa.1]
    · simp [hxa.2 j hj, apply_of_lt (lt_trans (by exact_mod_cast hj) h)]

/-- Nothing is dropped: the higher term is still recoverable. -/
theorem add_sub_cancel_left (x y : Coord) : x + y - x = y := by simp

/-- Equal grades whose leading coefficients cancel: the grade rises. -/
theorem val_add_gt {x y : Coord} {k : ℤ} (hx : val x = k) (hy : val y = k) (hc : x k + y k = 0) :
    val x < val (x + y) := by
  have hxk := val_eq_iff.mp hx
  have hyk := val_eq_iff.mp hy
  have hge : (k : WithTop ℤ) ≤ val (x + y) := le_val fun j hj => by simp [hxk.2 j hj, hyk.2 j hj]
  rcases hge.lt_or_eq with hlt | heq
  · rwa [hx]
  · exfalso
    exact apply_val_ne heq.symm (by simpa using hc)

/-! ## Shifting -/

/-- Multiply by the single term `c·ε^k`. -/
noncomputable def shift (k : ℤ) (c : ℚ) (x : Coord) : Coord :=
  c • Finsupp.mapDomain (· + k) x

theorem shift_apply (k : ℤ) (c : ℚ) (x : Coord) (b : ℤ) : shift k c x b = c * x (b - k) := by
  have := Finsupp.mapDomain_apply (f := (· + k)) (add_left_injective k) x (b - k)
  simp only [sub_add_cancel] at this
  simp [shift, this]

theorem val_shift (k : ℤ) {c : ℚ} (hc : c ≠ 0) {x : Coord} {a : ℤ} (hx : val x = a) :
    val (shift k c x) = ((a + k : ℤ) : WithTop ℤ) := by
  have h := val_eq_iff.mp hx
  rw [val_eq_iff]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [shift_apply]; simpa [hc] using h.1
  · rw [shift_apply, h.2 (j - k) (by omega), mul_zero]

/-! ## Examples -/

/-- `ε + ε²` and `−ε`: the leading terms cancel and the bookkeeping `ε²` becomes the value. -/
theorem cancel_example :
    val ((Finsupp.single 1 1 + Finsupp.single 2 1 : Coord) + Finsupp.single 1 (-1)) = ((2 : ℤ) : WithTop ℤ) := by
  rw [val_eq_iff]
  refine ⟨by simp, fun j hj => ?_⟩
  have h2 : j ≠ 2 := by omega
  by_cases h1 : j = 1 <;> simp [Finsupp.single_apply, h1, h2, eq_comm]

end Tail
