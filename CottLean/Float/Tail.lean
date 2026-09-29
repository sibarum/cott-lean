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

* `mul`: the product of two full sums. `val_mul` gives `val (x·y) = val x + val y`. `card_support_mul_le`
  bounds the terms of a product by the product of the term counts, which is how the bookkeeping grows.
  Nothing caps it, because nothing needs to: the product conserves what the terms add up to.
* `ev_mul`, `total_mul`: evaluating at any `ε = t ≠ 0` is multiplicative, and `total` is `t = 1`. A total of
  `1` stays `1` (`total_mul_one`) and a total of `0` stays `0` (`total_mul_zero`), through every product.
  `total_add` makes it additive too. The grade (`val_mul`) is conserved the same way, additively.
* `recover`: the total fixes any one term from the rest, so a tail is one term shorter than it looks.
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


/-! ## Full multiplication -/

/-- The product of two sums: every term of `x` shifts `y`, and the shifts add. No term is dropped and
none is merged unless the grades meet. -/
noncomputable def mul (x y : Coord) : Coord := x.sum fun a c => shift a c y

theorem mul_apply (x y : Coord) (n : ℤ) : mul x y n = x.sum fun a c => c * y (n - a) := by
  simp only [mul, Finsupp.sum, Finsupp.finset_sum_apply, shift_apply]

/-- The grade of a product is the sum of the grades. -/
theorem val_mul {x y : Coord} {a b : ℤ} (hx : val x = a) (hy : val y = b) :
    val (mul x y) = ((a + b : ℤ) : WithTop ℤ) := by
  have h1 := val_eq_iff.mp hx
  have h2 := val_eq_iff.mp hy
  rw [val_eq_iff]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [mul_apply, Finsupp.sum_eq_single a]
    · have : a + b - a = b := by omega
      rw [this]; exact mul_ne_zero h1.1 h2.1
    · intro i hi hia
      have hai : a < i := lt_of_le_of_ne (by
        by_contra hlt
        exact hi (h1.2 i (not_le.mp hlt))) (Ne.symm hia)
      show x i * y (a + b - i) = 0
      rw [h2.2 (a + b - i) (by omega), mul_zero]
    · intro h; exact absurd (h1.1) (by simpa using h)
  · rw [mul_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hai : a ≤ i := by
      by_contra hlt
      exact (Finsupp.mem_support_iff.mp hi) (h1.2 i (not_le.mp hlt))
    show x i * y (j - i) = 0
    rw [h2.2 (j - i) (by omega), mul_zero]

/-- A product has at most as many terms as the pairs of terms. This is how the bookkeeping grows. -/
theorem card_support_mul_le (x y : Coord) :
    (mul x y).support.card ≤ x.support.card * y.support.card := by
  classical
  have hsub : (mul x y).support ⊆ x.support.biUnion fun a => y.support.image (· + a) := by
    intro n hn
    rw [Finsupp.mem_support_iff, mul_apply] at hn
    obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    rw [Finset.mem_biUnion]
    refine ⟨a, ha, Finset.mem_image.mpr ⟨n - a, ?_, by omega⟩⟩
    exact Finsupp.mem_support_iff.mpr fun h => hne (by simp [h])
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  rw [mul_comm]
  refine (Finset.sum_le_card_nsmul _ _ y.support.card fun a _ => Finset.card_image_le).trans ?_
  simp [mul_comm]


/-! ## What the product conserves -/

/-- Evaluate at `ε = t`: the coordinate as a number, every term counted. -/
noncomputable def ev (t : ℚ) (x : Coord) : ℚ := x.sum fun k c => c * t ^ k

/-- The total: all coefficients, ignoring grade. `ε = 1`. -/
noncomputable def total (x : Coord) : ℚ := ev 1 x

theorem ev_add (t : ℚ) (x y : Coord) : ev t (x + y) = ev t x + ev t y := by
  unfold ev
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem ev_single (t : ℚ) (k : ℤ) (c : ℚ) : ev t (Finsupp.single k c) = c * t ^ k := by
  unfold ev; rw [Finsupp.sum_single_index]; simp

theorem ev_shift {t : ℚ} (ht : t ≠ 0) (k : ℤ) (c : ℚ) (x : Coord) :
    ev t (shift k c x) = c * t ^ k * ev t x := by
  unfold shift ev
  rw [Finsupp.sum_smul_index' (by simp), Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => by ring),
    Finsupp.mul_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  rw [zpow_add₀ ht]; ring

/-- `ε = t` is multiplicative: the product of two sums evaluates to the product of their values. -/
theorem ev_mul {t : ℚ} (ht : t ≠ 0) (x y : Coord) : ev t (mul x y) = ev t x * ev t y := by
  unfold mul
  have : ∀ s : Finset ℤ, ev t (∑ a ∈ s, shift a (x a) y) = ∑ a ∈ s, x a * t ^ a * ev t y := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp [ev]
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ev_add, ih, ev_shift ht]
  rw [Finsupp.sum, this, ← Finset.sum_mul]
  rfl

/-- The total is multiplicative. If two coordinates each total `1`, so does their product; if either
totals `0`, so does the product. -/
theorem total_mul (x y : Coord) : total (mul x y) = total x * total y := ev_mul one_ne_zero x y

theorem total_add (x y : Coord) : total (x + y) = total x + total y := ev_add 1 x y

theorem total_mul_one {x y : Coord} (hx : total x = 1) (hy : total y = 1) : total (mul x y) = 1 := by
  rw [total_mul, hx, hy, one_mul]

/-- Total zero is absorbing: a coordinate whose terms sum to zero keeps that in every product. -/
theorem total_mul_zero {x : Coord} (hx : total x = 0) (y : Coord) : total (mul x y) = 0 := by
  rw [total_mul, hx, zero_mul]

/-- The total is what lets one term be dropped: erase the term at `k`, and it is recovered from the
total of the rest. So a coordinate whose total is known carries one term fewer than it seems. -/
theorem recover (x : Coord) (k : ℤ) : x k = total x - total (x.erase k) := by
  have : x = x.erase k + Finsupp.single k (x k) := (Finsupp.erase_add_single k x).symm
  conv_rhs => rw [this, total_add]
  simp [total, ev_single]

end Tail
