import CottLean.T.Angle
import CottLean.T.Parallel

/-!
# The law atlas

`scripts/LawAtlas.lean` searches a grid for the strongest grade at which each of sixteen laws holds, for
every pairing of an addition `A` and a multiplication `M` among `⊕`, `+`, `*`, `⊗`, `⊚` and `∥`. This file
proves every cell of that table (`atlas`). The law holds at the cell's grade for every input, and a witness
fails every stronger grade. Each cell has two grades: one over all pairs, and one over *generic* pairs,
where both coordinates are non-zero and off the light lines (`p² ≠ q²`).

The grades, strongest first (`Holds`):

* `exact` -- coordinate equality
* `ray` -- a positive multiple, or both sides `0ω`
* `ratio` -- a non-zero multiple, or both sides `0ω`
* `par` -- `det = 0`: one side is a multiple of the other, `0ω` allowed
* `fails` -- nothing

Each grade implies the next (`holds_mono`), so a witness that fails the grade just above the cell's fails
all of them.

## What the table says

* **Eleven laws are exact in all 36 pairings**: both commutative and associative laws, both units,
  `-(x+y) = -x + -y`, `1/(xy) = (1/x)(1/y)`, `--x = x`, `//x = x` and `(x/y)(z/w) = (xz)/(yw)`. Each is a
  fact about one operation, so it holds whichever operation it is paired with (`op_comm`, …, `op_frac`).
* **Only `⊕` has an exact inverse.** For every other operation `x ∘ x⁻¹` is the unit scaled by `k`: `q²`
  for `+`, `pq` for `*`, `p² + q²` for `⊗`, `q² − p²` for `⊚`, and `p²` for `∥` (`inv_eq_scale`). So it
  is `par` everywhere, and on generic pairs `ray` where `k` is a square or a sum of squares, and `ratio`
  otherwise.
* **Distributivity is exact exactly when `A` is `⊕` and `M` is not.** It is off by a scale in two more
  pairings, `(+, *)` by `z.q` and `(∥, *)` by `z.p`, and fails in the other 29.
* **`0·x = 0`** is exact for `⊕` with any product but itself, off by a scale in nine pairings, `par` for
  `(⊕, ⊕)`, and fails in the rest. **`(−x)·y = −(x·y)`** is exact in the ten pairings of `⊕` with a
  product and `(+, *)`, `(*, ⊚)`, `(⊗, *)`, `(⊚, *)`, `(∥, *)`, and fails in the rest.

Every scale here is a polynomial in the inputs, so every non-exact grade short of `fails` comes from three
lemmas: scaling by any `k` keeps `par`, by `k ≠ 0` keeps `ratio`, and by `k > 0` keeps `ray`
(`holds_par_scale`, `holds_ratio_scale`, `holds_ray_scale`).
-/

namespace T

namespace Atlas

/-! ## The operations -/

/-- The six operations the atlas pairs. -/
inductive Op
  | oplus | plus | times | otimes | split | par
  deriving DecidableEq, Repr

/-- The operation. -/
def Op.f : Op → T → T → T
  | .oplus => T.oplus
  | .plus => fun x y => x + y
  | .times => fun x y => x * y
  | .otimes => T.otimes
  | .split => splitTimes
  | .par => T.par

/-- Its unit. -/
def Op.e : Op → T
  | .oplus => «0ω»
  | .plus => 0
  | .times => «1»
  | .otimes => 0
  | .split => 0
  | .par => «ω»

/-- Its inverse. -/
def Op.inv : Op → T → T
  | .oplus => oplusInverse
  | .plus => fun x => -x
  | .times => reciprocal
  | .otimes => fun x => -x
  | .split => fun x => -x
  | .par => fun x => ⟨x.p, -x.q⟩

/-! ## The grades -/

/-- How closely two pairs agree, strongest first. -/
inductive Grade
  | exact | ray | ratio | par | fails
  deriving DecidableEq, Repr

/-- The grade's place in the order, strongest first. -/
def Grade.rank : Grade → ℕ
  | .exact => 0 | .ray => 1 | .ratio => 2 | .par => 3 | .fails => 4

/-- `a` and `b` agree at grade `g`. -/
def Holds : Grade → T → T → Prop
  | .exact, a, b => a = b
  | .ray, a, b => (a = «0ω» ∧ b = «0ω») ∨ (a ≠ «0ω» ∧ b ≠ «0ω» ∧ det a b = 0 ∧ 0 < dot a b)
  | .ratio, a, b => (a = «0ω» ∧ b = «0ω») ∨ (a ≠ «0ω» ∧ b ≠ «0ω» ∧ det a b = 0)
  | .par, a, b => det a b = 0
  | .fails, _, _ => True

instance (g : Grade) (a b : T) : Decidable (Holds g a b) := by
  cases g <;> unfold Holds <;> infer_instance

/-- Both coordinates non-zero, and off the light lines. -/
def Generic (x : T) : Prop := x.p ≠ 0 ∧ x.q ≠ 0 ∧ x.p * x.p ≠ x.q * x.q

instance (x : T) : Decidable (Generic x) := by unfold Generic; infer_instance

/-! ## The laws -/

/-- Up to four inputs. A law in fewer ignores the rest. -/
structure In where
  x : T
  y : T
  z : T
  w : T
  deriving DecidableEq, Repr

/-- Every input generic. -/
def In.Generic (v : In) : Prop := Atlas.Generic v.x ∧ Atlas.Generic v.y ∧ Atlas.Generic v.z ∧ Atlas.Generic v.w

instance (v : In) : Decidable v.Generic := by unfold In.Generic; infer_instance

/-- The sixteen laws. -/
inductive Law
  | aComm | aAssoc | aUnit | aInv | mComm | mAssoc | mUnit | mInv
  | distrib | zeroMul | negMul | negAdd | invMul | negNeg | invInv | fracMul
  deriving DecidableEq, Repr

/-- The two sides of a law, for the addition `A` and the multiplication `M`. -/
def Law.sides (A M : Op) (v : In) : Law → T × T
  | .aComm => (A.f v.x v.y, A.f v.y v.x)
  | .aAssoc => (A.f (A.f v.x v.y) v.z, A.f v.x (A.f v.y v.z))
  | .aUnit => (A.f v.x A.e, v.x)
  | .aInv => (A.f v.x (A.inv v.x), A.e)
  | .mComm => (M.f v.x v.y, M.f v.y v.x)
  | .mAssoc => (M.f (M.f v.x v.y) v.z, M.f v.x (M.f v.y v.z))
  | .mUnit => (M.f v.x M.e, v.x)
  | .mInv => (M.f v.x (M.inv v.x), M.e)
  | .distrib => (M.f (A.f v.x v.y) v.z, A.f (M.f v.x v.z) (M.f v.y v.z))
  | .zeroMul => (M.f A.e v.x, A.e)
  | .negMul => (M.f (A.inv v.x) v.y, A.inv (M.f v.x v.y))
  | .negAdd => (A.inv (A.f v.x v.y), A.f (A.inv v.x) (A.inv v.y))
  | .invMul => (M.inv (M.f v.x v.y), M.f (M.inv v.x) (M.inv v.y))
  | .negNeg => (A.inv (A.inv v.x), v.x)
  | .invInv => (M.inv (M.inv v.x), v.x)
  | .fracMul => (M.f (M.f v.x (M.inv v.y)) (M.f v.z (M.inv v.w)), M.f (M.f v.x v.z) (M.inv (M.f v.y v.w)))

/-- The law holds at `g` between its two sides, at the input `v`. -/
def Law.Holds (L : Law) (A M : Op) (g : Grade) (v : In) : Prop :=
  Atlas.Holds g (L.sides A M v).1 (L.sides A M v).2

instance (L : Law) (A M : Op) (g : Grade) (v : In) : Decidable (L.Holds A M g v) := by
  unfold Law.Holds; infer_instance

/-! ## The table -/

/-- `x ∘ x⁻¹ = e`: exact for `⊕`; for the rest `par`, and on generic pairs `ray` or `ratio`. -/
def invGrade : Op → Grade × Grade
  | .oplus => (.exact, .exact)
  | .plus => (.par, .ray)
  | .times => (.par, .ratio)
  | .otimes => (.par, .ray)
  | .split => (.par, .ratio)
  | .par => (.par, .ray)

/-- `(x A y) M z = (x M z) A (y M z)`. -/
def distribGrade : Op → Op → Grade × Grade
  | .oplus, .oplus => (.fails, .fails)
  | .oplus, _ => (.exact, .exact)
  | .plus, .times => (.par, .ratio)
  | .par, .times => (.par, .ratio)
  | _, _ => (.fails, .fails)

/-- `e_A M x = e_A`. -/
def zeroMulGrade : Op → Op → Grade × Grade
  | .oplus, .oplus => (.par, .par)
  | .oplus, _ => (.exact, .exact)
  | .plus, .times | .plus, .par | .times, .split | .otimes, .times | .otimes, .par
  | .split, .times | .split, .par | .par, .plus | .par, .times => (.par, .ratio)
  | _, _ => (.fails, .fails)

/-- `(A⁻¹ x) M y = A⁻¹ (x M y)`. -/
def negMulGrade : Op → Op → Grade × Grade
  | .oplus, .oplus => (.fails, .fails)
  | .oplus, _ => (.exact, .exact)
  | .plus, .times | .times, .split | .otimes, .times | .split, .times | .par, .times => (.exact, .exact)
  | _, _ => (.fails, .fails)

/-- The atlas: each law's grade over all pairs, and over generic pairs. -/
def table (A M : Op) : Law → Grade × Grade
  | .aInv => invGrade A
  | .mInv => invGrade M
  | .distrib => distribGrade A M
  | .zeroMul => zeroMulGrade A M
  | .negMul => negMulGrade A M
  | _ => (.exact, .exact)

/-! ## The grades are ordered -/

theorem holds_exact_ray {a b : T} (h : a = b) : Holds .ray a b := by
  subst h
  by_cases ha : a = «0ω»
  · exact Or.inl ⟨ha, ha⟩
  · refine Or.inr ⟨ha, ha, det_self a, ?_⟩
    have : a.p ≠ 0 ∨ a.q ≠ 0 := by
      by_contra hc; push Not at hc; exact ha (by ext <;> simp [«0ω», hc.1, hc.2])
    simp only [dot]
    rcases this with h | h <;> nlinarith [mul_self_pos.mpr h, mul_self_nonneg a.p, mul_self_nonneg a.q]

theorem holds_ray_ratio {a b : T} (h : Holds .ray a b) : Holds .ratio a b := by
  rcases h with h | ⟨ha, hb, hd, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨ha, hb, hd⟩

theorem holds_ratio_par {a b : T} (h : Holds .ratio a b) : Holds .par a b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨-, -, hd⟩
  · exact det_self _
  · exact hd

/-- Each grade implies every weaker one. -/
theorem holds_mono {g h : Grade} (hgh : g.rank ≤ h.rank) {a b : T} (H : Holds g a b) : Holds h a b := by
  cases g <;> cases h <;> simp only [Grade.rank] at hgh <;> first
    | omega
    | trivial
    | exact H
    | exact holds_exact_ray H
    | exact holds_ray_ratio (holds_exact_ray H)
    | exact holds_ratio_par (holds_ray_ratio (holds_exact_ray H))
    | exact holds_ray_ratio H
    | exact holds_ratio_par (holds_ray_ratio H)
    | exact holds_ratio_par H

/-! ## Scaling -/

/-- Scaling by any `k` keeps `par`. -/
theorem holds_par_scale (k : ℤ) (a : T) : Holds .par (scale k a) a := by
  simp only [Holds, det, scale]; ring

theorem scale_ne_zeroOmega {k : ℤ} (hk : k ≠ 0) {a : T} (ha : a ≠ «0ω») : scale k a ≠ «0ω» := by
  intro h
  apply ha
  have hp := congrArg T.p h
  have hq := congrArg T.q h
  simp only [scale, «0ω», mul_eq_zero, hk, false_or] at hp hq
  ext <;> simp [«0ω», hp, hq]

theorem scale_zeroOmega (k : ℤ) : scale k «0ω» = «0ω» := by ext <;> simp [scale, «0ω»]

/-- Scaling by `k ≠ 0` keeps `ratio`. -/
theorem holds_ratio_scale {k : ℤ} (hk : k ≠ 0) (a : T) : Holds .ratio (scale k a) a := by
  by_cases ha : a = «0ω»
  · subst ha; exact Or.inl ⟨scale_zeroOmega k, rfl⟩
  · exact Or.inr ⟨scale_ne_zeroOmega hk ha, ha, holds_par_scale k a⟩

/-- Scaling by `k > 0` keeps `ray`. -/
theorem holds_ray_scale {k : ℤ} (hk : 0 < k) (a : T) : Holds .ray (scale k a) a := by
  by_cases ha : a = «0ω»
  · subst ha; exact Or.inl ⟨scale_zeroOmega k, rfl⟩
  · refine Or.inr ⟨scale_ne_zeroOmega hk.ne' ha, ha, holds_par_scale k a, ?_⟩
    have := (holds_exact_ray (rfl : a = a))
    rcases this with ⟨h, -⟩ | ⟨-, -, -, hd⟩
    · exact absurd h ha
    · simp only [dot, scale] at hd ⊢
      nlinarith

theorem holds_symm {g : Grade} {a b : T} (h : Holds g a b) : Holds g b a := by
  cases g
  · exact h.symm
  · rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hd, hdot⟩
    · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨hb, ha, by rw [det_swap, hd, neg_zero], by simp only [dot] at hdot ⊢; linarith⟩
  · rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hd⟩
    · exact Or.inl ⟨hb, ha⟩
    · exact Or.inr ⟨hb, ha, by rw [det_swap, hd, neg_zero]⟩
  · change det b a = 0; rw [det_swap, show det a b = 0 from h, neg_zero]
  · trivial

theorem holds_of_scale {g : Grade} {a b : T} (k : ℤ) (h : a = scale k b)
    (hg : Holds g (scale k b) b) : Holds g a b := h ▸ hg

theorem holds_of_scale' {g : Grade} {a b : T} (k : ℤ) (h : b = scale k a)
    (hg : Holds g (scale k a) a) : Holds g a b := h ▸ holds_symm hg

/-! ## The laws of one operation -/

/-- Every operation, and every unit and inverse, in coordinates; then `ring`. -/
macro "atlas_ring" : tactic =>
  `(tactic| (ext <;> simp only [Law.sides, Op.f, Op.e, Op.inv, add_def, mul_def, neg_def, zero_def, T.oplus,
    T.otimes, splitTimes, qtimes, T.par, reciprocal, oplusInverse, «0ω», «1», «ω», scale] <;> ring1))

/-- The same, for a `det`. -/
macro "atlas_det" : tactic =>
  `(tactic| (simp only [det, Op.f, Op.e, Op.inv, add_def, mul_def, neg_def, zero_def, T.oplus,
    T.otimes, splitTimes, qtimes, T.par, reciprocal, oplusInverse, «0ω», «1», «ω», scale]; ring1))

theorem op_comm (o : Op) (x y : T) : o.f x y = o.f y x := by cases o <;> atlas_ring

theorem op_assoc (o : Op) (x y z : T) : o.f (o.f x y) z = o.f x (o.f y z) := by cases o <;> atlas_ring

theorem op_unit (o : Op) (x : T) : o.f x o.e = x := by cases o <;> atlas_ring

theorem op_inv_f (o : Op) (x y : T) : o.inv (o.f x y) = o.f (o.inv x) (o.inv y) := by
  cases o <;> atlas_ring

theorem op_inv_inv (o : Op) (x : T) : o.inv (o.inv x) = x := by cases o <;> atlas_ring

theorem op_frac (o : Op) (x y z w : T) :
    o.f (o.f x (o.inv y)) (o.f z (o.inv w)) = o.f (o.f x z) (o.inv (o.f y w)) := by
  cases o <;> atlas_ring

/-- The scale `x ∘ x⁻¹` carries: `1` for `⊕`, whose `0ω` absorbs it. -/
def invScale : Op → T → ℤ
  | .oplus => 1
  | .plus => fun x => x.q ^ 2
  | .times => fun x => x.p * x.q
  | .otimes => fun x => x.p ^ 2 + x.q ^ 2
  | .split => fun x => x.q ^ 2 - x.p ^ 2
  | .par => fun x => x.p ^ 2

/-- `x ∘ x⁻¹` is the unit, scaled. -/
theorem inv_eq_scale (o : Op) (x : T) : o.f x (o.inv x) = scale (invScale o x) o.e := by
  cases o <;> simp only [invScale] <;> atlas_ring

theorem inv_all (o : Op) (x : T) : Holds (invGrade o).1 (o.f x (o.inv x)) o.e := by
  cases o
  · exact (inv_eq_scale .oplus x).trans (scale_zeroOmega 1)
  all_goals exact holds_of_scale _ (inv_eq_scale _ x) (holds_par_scale _ _)

theorem inv_generic (o : Op) {x : T} (hx : Generic x) : Holds (invGrade o).2 (o.f x (o.inv x)) o.e := by
  obtain ⟨hp, hq, hl⟩ := hx
  cases o
  · exact (inv_eq_scale .oplus x).trans (scale_zeroOmega 1)
  · exact holds_of_scale _ (inv_eq_scale _ x) (holds_ray_scale (by simp only [invScale]; positivity) _)
  · exact holds_of_scale _ (inv_eq_scale _ x) (holds_ratio_scale (by simp [invScale, hp, hq]) _)
  · exact holds_of_scale _ (inv_eq_scale _ x) (holds_ray_scale (by simp only [invScale]; positivity) _)
  · exact holds_of_scale _ (inv_eq_scale _ x)
      (holds_ratio_scale (by simp only [invScale]; intro h; apply hl; linear_combination -h) _)
  · exact holds_of_scale _ (inv_eq_scale _ x) (holds_ray_scale (by simp only [invScale]; positivity) _)

/-! ## Every cell holds at its grade -/

/-- Over all pairs. -/
theorem holds_all (A M : Op) (L : Law) (v : In) : L.Holds A M (table A M L).1 v := by
  cases L
  case aComm => exact op_comm A _ _
  case aAssoc => exact op_assoc A _ _ _
  case aUnit => exact op_unit A _
  case aInv => exact inv_all A _
  case mComm => exact op_comm M _ _
  case mAssoc => exact op_assoc M _ _ _
  case mUnit => exact op_unit M _
  case mInv => exact inv_all M _
  case negAdd => exact op_inv_f A _ _
  case invMul => exact op_inv_f M _ _
  case negNeg => exact op_inv_inv A _
  case invInv => exact op_inv_inv M _
  case fracMul => exact op_frac M _ _ _ _
  all_goals cases A <;> cases M <;>
    simp only [Law.Holds, Law.sides, table, distribGrade, zeroMulGrade, negMulGrade, Holds] <;>
    first | trivial | atlas_ring | atlas_det

theorem ne_neg_of_sq_ne {p q : ℤ} (h : p * p ≠ q * q) : p + q ≠ 0 := by
  intro h'; apply h; rw [show p = -q by linarith]; ring

/-- Over generic pairs. -/
theorem holds_generic (A M : Op) (L : Law) {v : In} (hv : v.Generic) : L.Holds A M (table A M L).2 v := by
  cases L
  case aInv => exact inv_generic A hv.1
  case mInv => exact inv_generic M hv.1
  case distrib =>
    have hzp := hv.2.2.1.1
    have hzq := hv.2.2.1.2.1
    cases A <;> cases M <;> first
      | exact holds_all _ _ .distrib v
      | (refine holds_of_scale' v.z.q ?_ (holds_ratio_scale hzq _); atlas_ring)
      | (refine holds_of_scale' v.z.p ?_ (holds_ratio_scale hzp _); atlas_ring)
  case zeroMul =>
    obtain ⟨hp, hq, hl⟩ := hv.1
    cases A <;> cases M <;> first
      | exact holds_all _ _ .zeroMul v
      | (refine holds_of_scale v.x.q ?_ (holds_ratio_scale hq _); atlas_ring)
      | (refine holds_of_scale v.x.p ?_ (holds_ratio_scale hp _); atlas_ring)
      | (refine holds_of_scale (v.x.p + v.x.q) ?_ (holds_ratio_scale (ne_neg_of_sq_ne hl) _); atlas_ring)
  all_goals cases A <;> cases M <;> exact holds_all _ _ _ v

/-! ## Every cell holds at no stronger grade -/

/-- The grade just above. -/
def Grade.prev : Grade → Grade
  | .exact => .exact | .ray => .exact | .ratio => .ray | .par => .ratio | .fails => .par

/-- Five inputs, which between them fail every cell one grade above its own. -/
def witnesses : List In :=
  [ ⟨⟨-2, 1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-2, -1⟩⟩,
    ⟨⟨0, 0⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -1⟩⟩,
    ⟨⟨-1, -2⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩⟩,
    ⟨⟨-2, -2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨-2, -1⟩⟩,
    ⟨⟨-2, -2⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨-2, -1⟩⟩ ]

theorem witnesses_fail (A M : Op) (L : Law) :
    ((table A M L).1 ≠ .exact → ∃ v ∈ witnesses, ¬ L.Holds A M (table A M L).1.prev v) ∧
      ((table A M L).2 ≠ .exact → ∃ v ∈ witnesses, v.Generic ∧ ¬ L.Holds A M (table A M L).2.prev v) := by
  cases A <;> cases M <;> cases L <;> decide

/-- A law holds at `g` for every input `P` allows, and there is an input where each stronger grade
fails. -/
def Strongest (P : In → Prop) (L : Law) (A M : Op) (g : Grade) : Prop :=
  (∀ v, P v → L.Holds A M g v) ∧ ∀ h : Grade, h.rank < g.rank → ∃ v, P v ∧ ¬ L.Holds A M h v

theorem rank_le_prev {g h : Grade} (hgh : h.rank < g.rank) : h.rank ≤ g.prev.rank := by
  cases g <;> cases h <;> simp_all [Grade.rank, Grade.prev]

theorem ne_exact_of_rank {g h : Grade} (hgh : h.rank < g.rank) : g ≠ .exact := by
  rintro rfl; simp [Grade.rank] at hgh

/-- **The atlas**: every cell of the table is the strongest grade at which its law holds, over all pairs
and over generic pairs. -/
theorem atlas (A M : Op) (L : Law) :
    Strongest (fun _ => True) L A M (table A M L).1 ∧ Strongest In.Generic L A M (table A M L).2 := by
  obtain ⟨w1, w2⟩ := witnesses_fail A M L
  refine ⟨⟨fun v _ => holds_all A M L v, fun h hh => ?_⟩, ⟨fun v hv => holds_generic A M L hv, fun h hh => ?_⟩⟩
  · obtain ⟨v, -, hv⟩ := w1 (ne_exact_of_rank hh)
    exact ⟨v, trivial, fun H => hv (holds_mono (rank_le_prev hh) H)⟩
  · obtain ⟨v, -, hg, hv⟩ := w2 (ne_exact_of_rank hh)
    exact ⟨v, hg, fun H => hv (holds_mono (rank_le_prev hh) H)⟩

end Atlas

end T
