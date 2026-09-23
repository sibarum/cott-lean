import CottLean.T.Mobius

/-!
# The iterated mediant from the four seeds

Traction-Model.md, last line: *"Every traction other than 0ω is reached exactly once by iterated mediant
from the four seeds."*

The seeds are `0`, `ω`, `_0` and `-ω`, around the circle in that order. Between each pair of neighbouring
seeds, the mediant `⊕` is inserted, and then again between every pair of neighbours, forever. A pair
reached that way is named by which gap it is in and the left/right path taken to get to it (`tree`).
The first round puts `1`, `_1`, `-_1` and `-1` in the four gaps, which with the seeds and `0ω` is the
model's table of nine.

## What is proved

* `reach_injective`: nothing is reached twice. No two paths, and no path and a seed, land on the same
  pair.
* `range_reach`: the pairs reached are exactly those whose coordinates are coprime.

Both are at coordinate equality. So, read at coordinate equality, "every traction" does not hold:
`T(2,4)`, `T(2,2)` and `T(0,2)` are never reached (`not_reached_*`). Read up to the same ray -- a
positive multiple of both coordinates -- it holds exactly: every pair but `0ω` is a positive multiple of
exactly one reached pair (`exists_unique_reached_ray`). Which reading the line means is not decided here.

## How

Everything runs on `det a b = a.q·b.p − a.p·b.q`. Each pair of neighbouring seeds has `det = 1`, and the
mediant keeps it: `det a (a ⊕ b) = det (a ⊕ b) b = det a b`. With `det a b = 1`, every pair is
`x = det x b · a + det a x · b` exactly (`cramer_p`, `cramer_q`), and the two coefficients locate it: a
pair is reached in the gap `(a, b)` exactly when both are at least one and coprime. That is Euclid's
algorithm run on the coefficients, which is the whole of the classical proof.
-/

namespace T

/-! ## The determinant -/

/-- `a.q·b.p − a.p·b.q`: positive when `b` is a turn ahead of `a` by less than a half turn. -/
def det (a b : T) : ℤ := a.q * b.p - a.p * b.q

theorem det_self (a : T) : det a a = 0 := by simp [det]; ring
theorem det_swap (a b : T) : det b a = -det a b := by simp [det]; ring
theorem det_oplus_left (a b c : T) : det (a ⊕ b) c = det a c + det b c := by
  simp [det, oplus]; ring
theorem det_oplus_right (a b c : T) : det a (b ⊕ c) = det a b + det a c := by
  simp [det, oplus]; ring

/-- With `det a b = 1`, a pair is its two coefficients against `a` and `b`, exactly. -/
theorem cramer_p {a b : T} (h : det a b = 1) (x : T) : x.p = det x b * a.p + det a x * b.p := by
  unfold det at *; linear_combination (-x.p) * h

theorem cramer_q {a b : T} (h : det a b = 1) (x : T) : x.q = det x b * a.q + det a x * b.q := by
  unfold det at *; linear_combination (-x.q) * h

/-- A pair with `det a x = 1` against anything has coprime coordinates. -/
theorem isCoprime_of_det_eq_one {a x : T} (h : det a x = 1) : IsCoprime x.p x.q :=
  ⟨a.q, -a.p, by unfold det at h; linear_combination h⟩

/-- The coefficients are coprime exactly when the coordinates are. -/
theorem isCoprime_coeffs {a b : T} (h : det a b = 1) {x : T} (hc : IsCoprime x.p x.q) :
    IsCoprime (det x b) (det a x) := by
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨u * a.p + v * a.q, u * b.p + v * b.q, ?_⟩
  have c1 := cramer_p h x
  have c2 := cramer_q h x
  linear_combination huv - u * c1 - v * c2

/-! ## The tree between two neighbours -/

/-- The pair reached from the gap `(a, b)` by a path: `false` goes left, `true` goes right. The empty
path is the mediant of the two. -/
def tree (a b : T) : List Bool → T
  | [] => a ⊕ b
  | false :: w => tree a (a ⊕ b) w
  | true :: w => tree (a ⊕ b) b w

/-- Every pair in the tree is strictly inside its gap. -/
theorem tree_inside {a b : T} (h : 1 ≤ det a b) (w : List Bool) :
    1 ≤ det a (tree a b w) ∧ 1 ≤ det (tree a b w) b := by
  induction w generalizing a b with
  | nil =>
    simp only [tree, det_oplus_left, det_oplus_right, det_self]
    omega
  | cons d w ih =>
    cases d with
    | false =>
      have h' : 1 ≤ det a (a ⊕ b) := by rw [det_oplus_right, det_self]; omega
      obtain ⟨h1, h2⟩ := ih h'
      simp only [tree]
      refine ⟨h1, ?_⟩
      rw [det_oplus_right, det_swap a (tree a (a ⊕ b) w)] at h2
      omega
    | true =>
      have h' : 1 ≤ det (a ⊕ b) b := by rw [det_oplus_left, det_self]; omega
      obtain ⟨h1, h2⟩ := ih h'
      simp only [tree]
      refine ⟨?_, h2⟩
      rw [det_oplus_left, det_swap (tree (a ⊕ b) b w) b] at h1
      omega

/-- Every pair in the tree has coprime coordinates. -/
theorem tree_isCoprime {a b : T} (h : det a b = 1) (w : List Bool) :
    IsCoprime (tree a b w).p (tree a b w).q := by
  induction w generalizing a b with
  | nil =>
    exact isCoprime_of_det_eq_one (a := a) (by rw [tree, det_oplus_right, det_self, h]; rfl)
  | cons d w ih =>
    cases d with
    | false => exact ih (by rw [det_oplus_right, det_self, h]; rfl)
    | true => exact ih (by rw [det_oplus_left, det_self, h]; rfl)

/-- No pair is reached by two paths. -/
theorem tree_injective {a b : T} (h : 1 ≤ det a b) {w w' : List Bool}
    (e : tree a b w = tree a b w') : w = w' := by
  induction w generalizing a b w' with
  | nil =>
    cases w' with
    | nil => rfl
    | cons d v =>
      exfalso
      cases d with
      | false =>
        have := (tree_inside (a := a) (b := a ⊕ b) (by rw [det_oplus_right, det_self]; omega) v).2
        simp only [tree] at e
        rw [← e, det_self] at this
        omega
      | true =>
        have := (tree_inside (a := a ⊕ b) (b := b) (by rw [det_oplus_left, det_self]; omega) v).1
        simp only [tree] at e
        rw [← e, det_self] at this
        omega
  | cons d w ih =>
    have hl : 1 ≤ det a (a ⊕ b) := by rw [det_oplus_right, det_self]; omega
    have hr : 1 ≤ det (a ⊕ b) b := by rw [det_oplus_left, det_self]; omega
    cases w' with
    | nil =>
      exfalso
      cases d with
      | false =>
        have := (tree_inside hl w).2
        simp only [tree] at e
        rw [e, det_self] at this
        omega
      | true =>
        have := (tree_inside hr w).1
        simp only [tree] at e
        rw [e, det_self] at this
        omega
    | cons d' v =>
      cases d <;> cases d' <;> simp only [tree] at e
      · rw [ih hl e]
      · exfalso
        have h1 := (tree_inside hl w).2
        have h2 := (tree_inside hr v).1
        rw [e, det_swap] at h1
        omega
      · exfalso
        have h1 := (tree_inside hr w).1
        have h2 := (tree_inside hl v).2
        rw [e, det_swap] at h1
        omega
      · rw [ih hr e]

/-- And every pair strictly inside the gap with coprime coefficients is reached. -/
theorem tree_surjective {a b : T} (h : det a b = 1) {x : T} (hα : 1 ≤ det x b) (hβ : 1 ≤ det a x)
    (hc : IsCoprime (det x b) (det a x)) : ∃ w, tree a b w = x := by
  suffices key : ∀ n : ℕ, ∀ a b x : T, det a b = 1 → 1 ≤ det x b → 1 ≤ det a x →
      IsCoprime (det x b) (det a x) → det x b + det a x ≤ n → ∃ w, tree a b w = x from
    key _ a b x h hα hβ hc (Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ det x b + det a x)).symm.le
  intro n
  induction n with
  | zero => intro a b x _ hα hβ _ hn; omega
  | succ n ih =>
    intro a b x h hα hβ hc hn
    rcases lt_trichotomy (det x b) (det a x) with hlt | heq | hgt
    · -- right of the mediant
      have h' : det (a ⊕ b) b = 1 := by rw [det_oplus_left, det_self, h]; rfl
      have e : det (a ⊕ b) x = det a x - det x b := by rw [det_oplus_left, det_swap b]; ring
      obtain ⟨u, v, huv⟩ := hc
      obtain ⟨w, hw⟩ := ih (a ⊕ b) b x h' hα (by omega)
        ⟨u + v, v, by rw [e]; linear_combination huv⟩ (by omega)
      exact ⟨true :: w, hw⟩
    · -- the mediant itself: coprime and equal means both are one
      have hu : IsUnit (det x b) := isCoprime_self.mp (heq ▸ hc)
      have h1 : det x b = 1 := by
        rcases Int.isUnit_iff.mp hu with h1 | h1
        · exact h1
        · omega
      have h2 : det a x = 1 := by omega
      refine ⟨[], ?_⟩
      have c1 := cramer_p h x
      have c2 := cramer_q h x
      rw [h1, h2] at c1 c2
      ext <;> simp [tree, oplus] <;> linarith
    · -- left of the mediant
      have h' : det a (a ⊕ b) = 1 := by rw [det_oplus_right, det_self, h]; rfl
      have e : det x (a ⊕ b) = det x b - det a x := by rw [det_oplus_right, det_swap x a]; ring
      obtain ⟨u, v, huv⟩ := hc
      obtain ⟨w, hw⟩ := ih a (a ⊕ b) x h' (by omega) hβ
        ⟨u, u + v, by rw [e]; linear_combination huv⟩ (by omega)
      exact ⟨false :: w, hw⟩

/-! ## The four seeds, and everything reached from them -/

/-- `0`, `ω`, `_0`, `-ω`: the four points on the axes, around the circle. -/
def seed : Fin 4 → T := ![«0», «ω», «_0», «-ω»]

/-- The seed after `seed i`, going round. -/
def nextSeed : Fin 4 → T := ![«ω», «_0», «-ω», «0»]

theorem nextSeed_eq (i : Fin 4) : nextSeed i = seed (i + 1) := by fin_cases i <;> rfl

theorem det_seed (i : Fin 4) : det (seed i) (nextSeed i) = 1 := by fin_cases i <;> decide

/-- A seed, or a path in one of the four gaps. -/
def reach : Fin 4 ⊕ (Fin 4 × List Bool) → T
  | .inl i => seed i
  | .inr (i, w) => tree (seed i) (nextSeed i) w

/-- The first round, with the seeds and `0ω`, is the model's table of nine. -/
example : reach (.inr (0, [])) = «1» ∧ reach (.inr (1, [])) = «_1» ∧
    reach (.inr (2, [])) = «-_1» ∧ reach (.inr (3, [])) = «-1» := by decide

/-- Going left then right from `0`–`ω`: `T(1,2)`, then `T(2,3)`. -/
example : tree «0» «ω» [false] = ⟨1, 2⟩ := by decide
example : tree «0» «ω» [false, true] = ⟨2, 3⟩ := by decide

/-- Which quadrant a pair is strictly inside, by the signs of its coordinates. -/
def signs (x : T) : Bool × Bool := (decide (0 < x.p), decide (0 < x.q))

def quadrant : Fin 4 → Bool × Bool := ![(true, true), (true, false), (false, false), (false, true)]

/-- A pair reached in gap `i` is strictly inside quadrant `i`: neither coordinate zero, and the signs of
that quadrant. -/
theorem tree_signs (i : Fin 4) (w : List Bool) :
    (tree (seed i) (nextSeed i) w).p ≠ 0 ∧ (tree (seed i) (nextSeed i) w).q ≠ 0 ∧
      signs (tree (seed i) (nextSeed i) w) = quadrant i := by
  have ⟨h1, h2⟩ := tree_inside (le_of_eq (det_seed i).symm) w
  generalize tree (seed i) (nextSeed i) w = x at h1 h2 ⊢
  fin_cases i <;>
    simp [det, seed, nextSeed, quadrant, signs, «0», «ω», «_0», «-ω»] at h1 h2 ⊢ <;> omega

theorem seed_has_zero (i : Fin 4) : (seed i).p = 0 ∨ (seed i).q = 0 := by fin_cases i <;> decide

/-! ## Nothing is reached twice -/

theorem reach_injective : Function.Injective reach := by
  rintro (i | ⟨i, w⟩) (j | ⟨j, v⟩) e <;> simp only [reach] at e
  · congr 1; revert e; fin_cases i <;> fin_cases j <;> decide
  · exfalso
    obtain ⟨hp, hq, -⟩ := tree_signs j v
    rcases seed_has_zero i with h | h
    · exact hp (e ▸ h)
    · exact hq (e ▸ h)
  · exfalso
    obtain ⟨hp, hq, -⟩ := tree_signs i w
    rcases seed_has_zero j with h | h
    · exact hp (e.symm ▸ h)
    · exact hq (e.symm ▸ h)
  · have hij : i = j := by
      have si := (tree_signs i w).2.2
      have sj := (tree_signs j v).2.2
      rw [e] at si
      have := si.symm.trans sj
      revert this; fin_cases i <;> fin_cases j <;> decide
    subst hij
    rw [tree_injective (le_of_eq (det_seed i).symm) e]

/-! ## What is reached is exactly the coprime pairs -/

theorem seed_isCoprime (i : Fin 4) : IsCoprime (seed i).p (seed i).q := by
  fin_cases i
  · exact ⟨0, 1, by decide⟩
  · exact ⟨1, 0, by decide⟩
  · exact ⟨0, -1, by decide⟩
  · exact ⟨-1, 0, by decide⟩

theorem range_reach : Set.range reach = {x | IsCoprime x.p x.q} := by
  ext x
  constructor
  · rintro ⟨i | ⟨i, w⟩, rfl⟩
    · exact seed_isCoprime i
    · exact tree_isCoprime (det_seed i) w
  · intro hc
    change IsCoprime x.p x.q at hc
    -- On an axis, coprime means a unit, and that is a seed.
    by_cases hp : x.p = 0
    · rw [hp, isCoprime_zero_left, Int.isUnit_iff] at hc
      rcases hc with hq | hq
      · exact ⟨.inl 0, T.ext hp.symm hq.symm⟩
      · exact ⟨.inl 2, T.ext hp.symm hq.symm⟩
    by_cases hq : x.q = 0
    · rw [hq, isCoprime_zero_right, Int.isUnit_iff] at hc
      rcases hc with hp' | hp'
      · exact ⟨.inl 1, T.ext hp'.symm hq.symm⟩
      · exact ⟨.inl 3, T.ext hp'.symm hq.symm⟩
    -- Off the axes, the signs pick the gap, and the gap's tree reaches it.
    have reachIn : ∀ i : Fin 4, 1 ≤ det x (nextSeed i) → 1 ≤ det (seed i) x → x ∈ Set.range reach :=
      fun i hα hβ => by
        obtain ⟨w, hw⟩ := tree_surjective (det_seed i) hα hβ (isCoprime_coeffs (det_seed i) hc)
        exact ⟨.inr (i, w), hw⟩
    rcases lt_or_gt_of_ne hp with hp | hp <;> rcases lt_or_gt_of_ne hq with hq | hq
    · exact reachIn 2 (by simp [det, nextSeed, «-ω»]; omega) (by simp [det, seed, «_0»]; omega)
    · exact reachIn 3 (by simp [det, nextSeed, «0»]; omega) (by simp [det, seed, «-ω»]; omega)
    · exact reachIn 1 (by simp [det, nextSeed, «_0»]; omega) (by simp [det, seed, «ω»]; omega)
    · exact reachIn 0 (by simp [det, nextSeed, «ω»]; omega) (by simp [det, seed, «0»]; omega)

/-! ## The two readings of "every traction" -/

/-- At coordinate equality, pairs off the coprime ones are never reached. -/
theorem not_reached_of_not_isCoprime {x : T} (h : ¬ IsCoprime x.p x.q) : x ∉ Set.range reach := by
  rw [range_reach]; exact h

theorem not_reached_two_four : (⟨2, 4⟩ : T) ∉ Set.range reach :=
  not_reached_of_not_isCoprime (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)

theorem not_reached_two_two : (⟨2, 2⟩ : T) ∉ Set.range reach :=
  not_reached_of_not_isCoprime (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)

theorem not_reached_zero_two : (⟨0, 2⟩ : T) ∉ Set.range reach :=
  not_reached_of_not_isCoprime (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)

/-- Up to the same ray, it holds exactly: every pair but `0ω` is a positive multiple of exactly one
reached pair. -/
theorem exists_unique_reached_ray (x : T) (hx : x ≠ «0ω») :
    ∃! y, y ∈ Set.range reach ∧ ∃ k : ℤ, 0 < k ∧ x = scale k y := by
  rw [range_reach]
  have hg : 0 < Int.gcd x.p x.q := by
    rw [Nat.pos_iff_ne_zero, Ne, Int.gcd_eq_zero_iff]
    rintro ⟨h1, h2⟩
    exact hx (T.ext h1 h2)
  refine ⟨⟨x.p / Int.gcd x.p x.q, x.q / Int.gcd x.p x.q⟩, ⟨?_, Int.gcd x.p x.q, by omega, ?_⟩, ?_⟩
  · change IsCoprime _ _
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact Int.gcd_div_gcd_div_gcd hg
  · ext <;> simp only [scale]
    · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left _ _)).symm
    · exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)).symm
  · rintro y ⟨hy, k, hk, rfl⟩
    change IsCoprime y.p y.q at hy
    rw [Int.isCoprime_iff_gcd_eq_one] at hy
    have hgk : Int.gcd (k * y.p) (k * y.q) = k.natAbs := by rw [Int.gcd_mul_left, hy, mul_one]
    simp only [scale, hgk]
    have hk' : ((k.natAbs : ℕ) : ℤ) = k := Int.natAbs_of_nonneg hk.le
    rw [hk']
    ext <;> simp [Int.mul_ediv_cancel_left _ hk.ne']

end T
