import CottLean.Nested.NoRing
import Mathlib.RingTheory.LaurentSeries

/-!
# Room for the zero

A structure in which `n + (−n)` erases `n`, and `m · (n − n)` does not erase `m`.

Take a field `K` and a corridor `e 0, e 1, e 2, …` of distinct non-zero elements (in the model, the
powers `ε, ε², ε³, …`). The carrier is `Kˣ`, the non-zero elements, under the field's own `·`. Addition is
the field's, moved one room along the corridor: `shift` sends `0 ↦ e 0` and `e k ↦ e (k + 1)` and fixes
everything else. Every element of the corridor gains a layer, and the zero gets the room that frees.

## The two groups

* `Held.mul_val`: `·` is the field's.
* `Held.add_val`: `x + y` is `shift (unshift x + unshift y)`, and both `+` and `·` are commutative groups,
  since `shift` is a bijection `K ≃ Kˣ` (`hotel`).
* `Held.zero_val`: the zero is `e 0`.

## The mandate

* `Held.universal_invariant`: `n + (−n) = 0` for every `n`, so it erases `n`.
* `Held.mandate`: `m ↦ m · (n + (−n))` is injective. Multiplying by any element is, the zero included.
* `Held.zero_mul_zero_ne_zero`: `0 · 0 ≠ 0`.
* `Held.zero_mul_inv`: the zero has an inverse.

## What it costs

* `Held.not_left_distrib`: `·` does not distribute over `+`. It cannot: `NoRing.left_distrib_zero`.
* `Held.distrib_of_plain`: but it does wherever every value involved is off the corridor, where `shift`
  does nothing.

## The standard part

Given a subring of finite elements `ι : A → K` with a standard part `st : A → L`, and a corridor of
infinitesimals (`st` of each `e k` is `0`), `stK` reads the standard part of an element of `K`.

* `Held.st_add`, `Held.st_mul`: on finite elements the standard part respects both `+` and `·`, so every
  law, distributivity included, holds after it (`Held.st_distrib`).
* `Held.st_zero`: the zero resolves to `0`.

## A model

`laurent` is the corridor `ε, ε², ε³, …` in the Laurent series over `ℚ`, with the power series as the
finite elements and the constant coefficient as the standard part (`laurent_infinitesimal`).
-/

open Function

namespace Hotel

variable {K : Type*} [Field K]

/-- A corridor: distinct non-zero elements, the first of which is not `1`. -/
structure Corridor (K : Type*) [Field K] where
  /-- The rooms. -/
  e : ℕ → K
  injective : Injective e
  ne_zero : ∀ k, e k ≠ 0
  ne_one : e 0 ≠ 1

variable (c : Corridor K)

open Classical in
/-- `0 ↦ e 0`, `e k ↦ e (k + 1)`, and everything else fixed. -/
noncomputable def shift (x : K) : K :=
  if x = 0 then c.e 0 else if h : ∃ k, c.e k = x then c.e (h.choose + 1) else x

open Classical in
/-- The inverse of `shift`: `e 0 ↦ 0`, `e (k + 1) ↦ e k`, and everything else fixed. -/
noncomputable def unshift (y : K) : K :=
  if h : ∃ k, c.e k = y then (match h.choose with | 0 => 0 | k + 1 => c.e k) else y

theorem choose_eq {k : ℕ} (h : ∃ j, c.e j = c.e k) : h.choose = k :=
  c.injective h.choose_spec

theorem shift_zero : shift c 0 = c.e 0 := by simp [shift]

theorem shift_e (k : ℕ) : shift c (c.e k) = c.e (k + 1) := by
  have h : ∃ j, c.e j = c.e k := ⟨k, rfl⟩
  rw [shift, if_neg (c.ne_zero k), dif_pos h, choose_eq c h]

theorem shift_of_plain {x : K} (hx : x ≠ 0) (he : ∀ k, c.e k ≠ x) : shift c x = x := by
  rw [shift, if_neg hx, dif_neg (not_exists.mpr he)]

theorem unshift_e_zero : unshift c (c.e 0) = 0 := by
  have h : ∃ j, c.e j = c.e 0 := ⟨0, rfl⟩
  rw [unshift, dif_pos h]
  simp only [choose_eq c h]

theorem unshift_e_succ (k : ℕ) : unshift c (c.e (k + 1)) = c.e k := by
  have h : ∃ j, c.e j = c.e (k + 1) := ⟨k + 1, rfl⟩
  rw [unshift, dif_pos h]
  simp only [choose_eq c h]

theorem unshift_of_plain {y : K} (he : ∀ k, c.e k ≠ y) : unshift c y = y := by
  rw [unshift, dif_neg (not_exists.mpr he)]

theorem shift_ne_zero (x : K) : shift c x ≠ 0 := by
  by_cases hx : x = 0
  · rw [hx, shift_zero]; exact c.ne_zero 0
  by_cases he : ∃ k, c.e k = x
  · obtain ⟨k, rfl⟩ := he
    rw [shift_e]; exact c.ne_zero _
  · rw [shift_of_plain c hx (not_exists.mp he)]; exact hx

theorem unshift_shift (x : K) : unshift c (shift c x) = x := by
  by_cases hx : x = 0
  · rw [hx, shift_zero, unshift_e_zero]
  by_cases he : ∃ k, c.e k = x
  · obtain ⟨k, rfl⟩ := he
    rw [shift_e, unshift_e_succ]
  · have he' := not_exists.mp he
    rw [shift_of_plain c hx he', unshift_of_plain c he']

theorem shift_unshift {y : K} (hy : y ≠ 0) : shift c (unshift c y) = y := by
  by_cases he : ∃ k, c.e k = y
  · obtain ⟨k, rfl⟩ := he
    cases k with
    | zero => rw [unshift_e_zero, shift_zero]
    | succ k => rw [unshift_e_succ, shift_e]
  · have he' := not_exists.mp he
    rw [unshift_of_plain c he', shift_of_plain c hy he']

/-- `shift` is a bijection from `K` onto its non-zero elements. -/
noncomputable def hotel : K ≃ {y : K // y ≠ 0} where
  toFun x := ⟨shift c x, shift_ne_zero c x⟩
  invFun y := unshift c y
  left_inv x := unshift_shift c x
  right_inv y := Subtype.ext (shift_unshift c y.2)

/-- The carrier: the non-zero elements, which have room for a zero. -/
def Held (_c : Corridor K) : Type _ := Kˣ

namespace Held

/-- The element of `K` it is. -/
def val {c : Corridor K} (x : Held c) : K := Units.val (α := K) x

/-- The carrier and `K`, through `unshift`. -/
noncomputable def equiv : Held c ≃ K := unitsEquivNeZero.trans (hotel c).symm

noncomputable instance : CommGroup (Held c) := inferInstanceAs (CommGroup Kˣ)
noncomputable instance : AddCommGroup (Held c) := (equiv c).addCommGroup

variable {c}

theorem val_injective : Injective (val : Held c → K) := Units.val_injective (α := K)

theorem val_ne_zero (x : Held c) : x.val ≠ 0 := Units.ne_zero (M₀ := K) x

theorem equiv_apply (x : Held c) : equiv c x = unshift c x.val := rfl

theorem val_equiv_symm (z : K) : ((equiv c).symm z).val = shift c z := rfl

theorem mul_val (x y : Held c) : (x * y).val = x.val * y.val := rfl

theorem one_val : (1 : Held c).val = 1 := rfl

theorem inv_val (x : Held c) : (x⁻¹).val = (x.val)⁻¹ :=
  Units.val_inv_eq_inv_val (show Kˣ from x)

theorem add_val (x y : Held c) : (x + y).val = shift c (unshift c x.val + unshift c y.val) := rfl

theorem zero_val : (0 : Held c).val = c.e 0 := by
  change shift c 0 = c.e 0
  exact shift_zero c

theorem neg_val (x : Held c) : (-x).val = shift c (-unshift c x.val) := rfl

/-! ## The mandate -/

/-- `n + (−n) = 0`: the universal invariant erases `n`. -/
theorem universal_invariant (n : Held c) : n + -n = 0 := add_neg_cancel n

/-- `m · (n + (−n))` does not erase `m`. -/
theorem mandate (n : Held c) : Injective (fun m : Held c => m * (n + -n)) :=
  mul_left_injective _

theorem zero_ne_one : (0 : Held c) ≠ 1 := by
  intro h
  have := congrArg val h
  rw [zero_val, one_val] at this
  exact c.ne_one this

/-- `0 · 0 ≠ 0`. -/
theorem zero_mul_zero_ne_zero : (0 : Held c) * 0 ≠ 0 := by
  intro h
  exact zero_ne_one (mul_eq_left.mp h)

/-- The zero has an inverse. -/
theorem zero_mul_inv : (0 : Held c) * 0⁻¹ = 1 := mul_inv_cancel _

/-! ## What it costs -/

/-- `·` does not distribute over `+`. -/
theorem not_left_distrib : ¬ ∀ x y z : Held c, x * (y + z) = x * y + x * z := by
  intro hd
  exact zero_mul_zero_ne_zero (NoRing.left_distrib_zero (fun m => hd m 0 0) 0)

/-- Off the corridor, where `shift` does nothing. -/
def Plain (c : Corridor K) (v : K) : Prop := v ≠ 0 ∧ ∀ k, c.e k ≠ v

/-- It distributes wherever every value involved is off the corridor. -/
theorem distrib_of_plain {x y z : Held c} (hy : Plain c y.val) (hz : Plain c z.val)
    (hxy : Plain c (x * y).val) (hxz : Plain c (x * z).val) (hs : Plain c (y.val + z.val))
    (hxs : Plain c (x.val * (y.val + z.val))) : x * (y + z) = x * y + x * z := by
  apply val_injective
  rw [mul_val, add_val, add_val, unshift_of_plain c hy.2, unshift_of_plain c hz.2,
    unshift_of_plain c hxy.2, unshift_of_plain c hxz.2, shift_of_plain c hs.1 hs.2, mul_val, mul_val,
    ← mul_add, shift_of_plain c hxs.1 hxs.2]

/-! ## The standard part -/

section Standard

variable {A L : Type*} [CommRing A] [CommRing L] (ι : A →+* K) (st : A →+* L)

/-- An element of `K` is finite when it comes from `A`. -/
def Finite (v : K) : Prop := ∃ a, ι a = v

open Classical in
/-- The standard part of a finite element, and `0` otherwise. -/
noncomputable def stK (v : K) : L := if h : Finite ι v then st h.choose else 0

variable {ι} (hι : Injective ι)
include hι

theorem stK_of (a : A) : stK ι st (ι a) = st a := by
  have h : Finite ι (ι a) := ⟨a, rfl⟩
  rw [stK, dif_pos h, hι h.choose_spec]

/-- A corridor of infinitesimals. -/
def Infinitesimal (c : Corridor K) (ι : A →+* K) (st : A →+* L) : Prop :=
  ∀ k, ∃ a, ι a = c.e k ∧ st a = 0

variable {st} (hc : Infinitesimal c ι st)
include hc

omit hι in
theorem finite_e (k : ℕ) : Finite ι (c.e k) := by
  obtain ⟨a, ha, -⟩ := hc k; exact ⟨a, ha⟩

theorem stK_e (k : ℕ) : stK ι st (c.e k) = 0 := by
  obtain ⟨a, ha, hs⟩ := hc k
  rw [← ha, stK_of st hι, hs]

theorem shift_finite {v : K} (hv : Finite ι v) :
    Finite ι (shift c v) ∧ stK ι st (shift c v) = stK ι st v := by
  by_cases h0 : v = 0
  · subst h0
    rw [shift_zero, stK_e hι hc, ← map_zero ι, stK_of st hι, map_zero]
    exact ⟨finite_e hc 0, rfl⟩
  by_cases he : ∃ k, c.e k = v
  · obtain ⟨k, rfl⟩ := he
    rw [shift_e, stK_e hι hc, stK_e hι hc]
    exact ⟨finite_e hc _, rfl⟩
  · rw [shift_of_plain c h0 (not_exists.mp he)]
    exact ⟨hv, rfl⟩

theorem unshift_finite {v : K} (hv : Finite ι v) :
    Finite ι (unshift c v) ∧ stK ι st (unshift c v) = stK ι st v := by
  by_cases he : ∃ k, c.e k = v
  · obtain ⟨k, rfl⟩ := he
    cases k with
    | zero =>
      rw [unshift_e_zero, stK_e hι hc, ← map_zero ι, stK_of st hι, map_zero]
      exact ⟨⟨0, by simp⟩, by simp⟩
    | succ k =>
      rw [unshift_e_succ, stK_e hι hc, stK_e hι hc]
      exact ⟨finite_e hc _, rfl⟩
  · rw [unshift_of_plain c (not_exists.mp he)]
    exact ⟨hv, rfl⟩

omit hc in
theorem finite_add {u v : K} (hu : Finite ι u) (hv : Finite ι v) :
    Finite ι (u + v) ∧ stK ι st (u + v) = stK ι st u + stK ι st v := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  rw [← map_add, stK_of st hι, stK_of st hι, stK_of st hι, map_add]
  exact ⟨⟨a + b, by simp⟩, by simp⟩

omit hc in
theorem finite_mul {u v : K} (hu : Finite ι u) (hv : Finite ι v) :
    Finite ι (u * v) ∧ stK ι st (u * v) = stK ι st u * stK ι st v := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  rw [← map_mul, stK_of st hι, stK_of st hι, stK_of st hι, map_mul]
  exact ⟨⟨a * b, by simp⟩, by simp⟩

/-- On finite elements the standard part respects `+`. -/
theorem st_add {x y : Held c} (hx : Finite ι x.val) (hy : Finite ι y.val) :
    Finite ι (x + y).val ∧ stK ι st (x + y).val = stK ι st x.val + stK ι st y.val := by
  obtain ⟨hx', ex⟩ := unshift_finite hι hc hx
  obtain ⟨hy', ey⟩ := unshift_finite hι hc hy
  obtain ⟨hs, es⟩ := finite_add (st := st) hι hx' hy'
  obtain ⟨hr, er⟩ := shift_finite hι hc hs
  rw [add_val]
  exact ⟨hr, by rw [er, es, ex, ey]⟩

omit hc in
/-- And `·`. -/
theorem st_mul {x y : Held c} (hx : Finite ι x.val) (hy : Finite ι y.val) :
    Finite ι (x * y).val ∧ stK ι st (x * y).val = stK ι st x.val * stK ι st y.val := by
  rw [mul_val]; exact finite_mul (st := st) hι hx hy

/-- So distributivity holds after the standard part. -/
theorem st_distrib {x y z : Held c} (hx : Finite ι x.val) (hy : Finite ι y.val)
    (hz : Finite ι z.val) : stK ι st (x * (y + z)).val = stK ι st (x * y + x * z).val := by
  obtain ⟨hyz, eyz⟩ := st_add hι hc hy hz
  obtain ⟨hxy, exy⟩ := st_mul (st := st) hι hx hy
  obtain ⟨hxz, exz⟩ := st_mul (st := st) hι hx hz
  rw [(st_mul (st := st) hι hx hyz).2, eyz, (st_add hι hc hxy hxz).2, exy, exz, mul_add]

/-- The zero resolves to `0`. -/
theorem st_zero : stK ι st (0 : Held c).val = 0 := by
  rw [zero_val, stK_e hι hc]

end Standard

end Held

/-! ## A model: the Laurent series over `ℚ` -/

open PowerSeries in
/-- `ε, ε², ε³, …` in the Laurent series over `ℚ`. -/
noncomputable def laurent : Corridor (LaurentSeries ℚ) where
  e k := HahnSeries.ofPowerSeries ℤ ℚ (X ^ (k + 1))
  injective := by
    intro j k h
    have h' := HahnSeries.ofPowerSeries_injective h
    have := congrArg (coeff (j + 1)) h'
    simp only [coeff_X_pow_self, coeff_X_pow] at this
    split_ifs at this with hjk
    · omega
    · exact absurd this one_ne_zero
  ne_zero k := by
    rw [map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective]
    exact pow_ne_zero _ X_ne_zero
  ne_one := by
    rw [← map_one (HahnSeries.ofPowerSeries ℤ ℚ)]
    intro h
    have := congrArg (coeff 0) (HahnSeries.ofPowerSeries_injective h)
    simp at this

open PowerSeries in
/-- Its rooms are infinitesimal: the constant coefficient of each is `0`. -/
theorem laurent_infinitesimal :
    Held.Infinitesimal laurent (HahnSeries.ofPowerSeries ℤ ℚ) (constantCoeff (R := ℚ)) :=
  fun k => ⟨X ^ (k + 1), rfl, by simp [constantCoeff_X]⟩

end Hotel
