import CottLean.Scatter.Quantise

/-!
# Scatter: what floating point loses, and when fixed point loses less

On `f32` the scatter is not exact. How far off it is follows from the standard model of rounding: a
rounding function `rnd` with `|rnd x − x| ≤ u·|x|`, where `u` is the unit roundoff, `2⁻²⁴` for `f32`
(`Rounding`). IEEE rounding to nearest satisfies it away from underflow and overflow. It is a hypothesis
on a function, not an axiom, and nothing below depends on which function it is.

A schedule of additions over a node's deposits is a binary tree (`Tree`): the leaves are the deposits,
and each inner node is one rounded addition. The direct scatter's atomics on one node are a chain, one
addition after another in the order the hardware chooses (`chain`). The segmented scatter sums each run
across a subgroup as a tree of depth at most five, then chains the runs (`chainT`). The register starts
at zero, and `0 + a = a` exactly in IEEE, so the first deposit is a leaf.

## What is proved

* `eval_error`: every schedule of depth `d` is within `γ d · A` of the exact sum, where
  `γ d = (1 + u)^d − 1` is about `d·u`, and `A` is the sum of the deposits' absolute values.
* `schedules_differ`: two schedules of the same deposits differ by at most `(γ d₁ + γ d₂)·A`. This is
  what "conservation, but not the bits" means, as a number.
* `eval_error_nonneg`: mass deposits are all positive, so `A` is the total itself and the error is
  relative, `γ d` of the mass. Momentum cancels, so its error is relative only to `Σ|mv|`: where
  opposing flows meet, the net momentum can be small against its error.
* `chain_depth`, `chainT_depth_le`: `n` atomics on one node form a chain of depth `n − 1`; `r` runs of
  depth at most `D`, chained, have depth at most `D + r`. So the segmented scatter's bound is smaller
  than the direct one's whenever its runs are longer than a few deposits.

## Against fixed point

A fixed-point scatter has no schedule error at all: every order gives the same grid (`Scatter.Wrap`).
Its error is fixed at deposit time, by rounding the shares (`Scatter.Quantise`): less than three quanta
a share (`fixed_error_le`). `fixed_le_float_bound` gives the scale at which that is no worse than the
float bound for `n` atomics: a quantum `δ` with `3·n·δ ≤ (n − 1)·u·A`. These are worst-case bounds
against each other, not measured errors, but they give the scale a principle.

## Underflow and the order of the product

The model above ignores underflow. With it, a product small enough rounds to zero, and then the order
of `w · m · v` matters. Computing the momentum share as `(w·m)·v` gives zero momentum wherever the mass
share rounded to zero (`massFirst_zero`), for every rounding with `rnd 0 = 0`. Computing it as
`w·(m·v)` does not: with flush-to-zero rounding, the mass share can vanish while the momentum share
does not, and the node holds momentum with no mass (`momentumFirst_omega`). `particle.Scatter`'s
direct and pre-reduced kernels compute `w·(m·v)`; its gather computes `(w·m)·v`.
-/

namespace Scatter

open Finset

/-! ## The model -/

/-- A rounding function within a relative error `u` of the exact value. -/
structure Rounding where
  /-- The rounding. -/
  rnd : ℝ → ℝ
  /-- The unit roundoff. -/
  u : ℝ
  u_nonneg : 0 ≤ u
  error : ∀ x, |rnd x - x| ≤ u * |x|

/-- `γ d = (1 + u)^d − 1`: the relative error that `d` rounded additions in sequence can reach. -/
def gamma (u : ℝ) (d : ℕ) : ℝ := (1 + u) ^ d - 1

theorem gamma_nonneg {u : ℝ} (hu : 0 ≤ u) (d : ℕ) : 0 ≤ gamma u d := by
  unfold gamma; linarith [one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + u) (n := d)]

theorem gamma_mono {u : ℝ} (hu : 0 ≤ u) {d e : ℕ} (h : d ≤ e) : gamma u d ≤ gamma u e := by
  unfold gamma; linarith [pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + u) h]

theorem gamma_succ (u : ℝ) (d : ℕ) : gamma u (d + 1) = (1 + u) * gamma u d + u := by
  unfold gamma; ring

/-- `γ d` is at least `d·u`: Bernoulli's inequality. -/
theorem le_gamma {u : ℝ} (hu : 0 ≤ u) (d : ℕ) : d * u ≤ gamma u d := by
  unfold gamma; linarith [one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ u) d]

/-! ## Schedules -/

/-- A schedule of additions: the deposits at the leaves, one rounded addition at each inner node. -/
inductive Tree (ι : Type*) where
  | leaf : ι → Tree ι
  | node : Tree ι → Tree ι → Tree ι

namespace Tree

variable {ι : Type*}

/-- The deposits a schedule adds, in order. -/
def leaves : Tree ι → List ι
  | leaf i => [i]
  | node l r => leaves l ++ leaves r

/-- The longest chain of additions. -/
def depth : Tree ι → ℕ
  | leaf _ => 0
  | node l r => max (depth l) (depth r) + 1

/-- The exact sum. -/
def sum (a : ι → ℝ) (t : Tree ι) : ℝ := (t.leaves.map a).sum

/-- The sum of the deposits' sizes, which bounds the error. -/
def absSum (a : ι → ℝ) (t : Tree ι) : ℝ := (t.leaves.map fun i => |a i|).sum

/-- The schedule as floating point computes it. -/
def eval (R : Rounding) (a : ι → ℝ) : Tree ι → ℝ
  | leaf i => a i
  | node l r => R.rnd (eval R a l + eval R a r)

@[simp] theorem sum_node (a : ι → ℝ) (l r : Tree ι) : (node l r).sum a = l.sum a + r.sum a := by
  simp [sum, leaves]

@[simp] theorem absSum_node (a : ι → ℝ) (l r : Tree ι) :
    (node l r).absSum a = l.absSum a + r.absSum a := by
  simp [absSum, leaves]

theorem absSum_nonneg (a : ι → ℝ) (t : Tree ι) : 0 ≤ t.absSum a :=
  List.sum_nonneg (by simp)

theorem abs_sum_le (a : ι → ℝ) (t : Tree ι) : |t.sum a| ≤ t.absSum a := by
  unfold sum absSum
  induction t.leaves with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons]; exact (abs_add_le _ _).trans (by linarith)

/-- Every schedule is within `γ (depth) · A` of the exact sum. -/
theorem eval_error (R : Rounding) (a : ι → ℝ) (t : Tree ι) :
    |t.eval R a - t.sum a| ≤ gamma R.u t.depth * t.absSum a := by
  induction t with
  | leaf i => simp [eval, sum, leaves, gamma, depth]
  | node l r ihl ihr =>
    simp only [eval, sum_node, absSum_node, depth]
    set x := l.eval R a + r.eval R a
    set d := max l.depth r.depth
    have hu := R.u_nonneg
    have el : |l.eval R a - l.sum a| ≤ gamma R.u d * l.absSum a :=
      ihl.trans (mul_le_mul_of_nonneg_right (gamma_mono hu (le_max_left _ _)) (absSum_nonneg _ _))
    have er : |r.eval R a - r.sum a| ≤ gamma R.u d * r.absSum a :=
      ihr.trans (mul_le_mul_of_nonneg_right (gamma_mono hu (le_max_right _ _)) (absSum_nonneg _ _))
    have hE : |x - (l.sum a + r.sum a)| ≤ gamma R.u d * (l.absSum a + r.absSum a) := by
      calc |x - (l.sum a + r.sum a)|
          = |(l.eval R a - l.sum a) + (r.eval R a - r.sum a)| := by congr 1; simp only [x]; ring
        _ ≤ _ := (abs_add_le _ _).trans (by linarith)
    have hx : |x| ≤ (1 + gamma R.u d) * (l.absSum a + r.absSum a) := by
      have := abs_sum_le a l; have := abs_sum_le a r
      calc |x| = |(x - (l.sum a + r.sum a)) + l.sum a + r.sum a| := by ring_nf
        _ ≤ |x - (l.sum a + r.sum a)| + |l.sum a| + |r.sum a| :=
            (abs_add_le _ _).trans (by linarith [abs_add_le (x - (l.sum a + r.sum a)) (l.sum a)])
        _ ≤ _ := by linarith
    calc |R.rnd x - (l.sum a + r.sum a)|
        ≤ |R.rnd x - x| + |x - (l.sum a + r.sum a)| := abs_sub_le _ _ _
      _ ≤ R.u * ((1 + gamma R.u d) * (l.absSum a + r.absSum a)) +
            gamma R.u d * (l.absSum a + r.absSum a) :=
          add_le_add ((R.error x).trans (mul_le_mul_of_nonneg_left hx hu)) hE
      _ = gamma R.u (d + 1) * (l.absSum a + r.absSum a) := by rw [gamma_succ]; ring

/-- Two schedules of the same deposits differ by at most the sum of their bounds. -/
theorem schedules_differ (R : Rounding) (a : ι → ℝ) (t₁ t₂ : Tree ι)
    (h : t₁.leaves.Perm t₂.leaves) :
    |t₁.eval R a - t₂.eval R a| ≤ (gamma R.u t₁.depth + gamma R.u t₂.depth) * t₁.absSum a := by
  have hs : t₁.sum a = t₂.sum a := (h.map a).sum_eq
  have hA : t₁.absSum a = t₂.absSum a := (h.map _).sum_eq
  have e₁ := eval_error R a t₁
  have e₂ := eval_error R a t₂
  rw [← hs, ← hA] at e₂
  calc |t₁.eval R a - t₂.eval R a| = |(t₁.eval R a - t₁.sum a) - (t₂.eval R a - t₁.sum a)| := by
        ring_nf
    _ ≤ _ := (abs_sub _ _).trans (by linarith)

/-- For deposits that are not negative, such as mass, the error is relative to the total itself. -/
theorem eval_error_nonneg (R : Rounding) (a : ι → ℝ) (t : Tree ι) (ha : ∀ i ∈ t.leaves, 0 ≤ a i) :
    |t.eval R a - t.sum a| ≤ gamma R.u t.depth * t.sum a := by
  have : t.absSum a = t.sum a := by
    unfold absSum sum
    exact congrArg List.sum (List.map_congr_left fun i hi => abs_of_nonneg (ha i hi))
  have e := eval_error R a t
  rw [this] at e
  exact e

/-! ## The direct and segmented schedules -/

/-- Schedules added one after another onto an accumulator, as atomics on one node add them. -/
def chainT : Tree ι → List (Tree ι) → Tree ι
  | t, [] => t
  | t, s :: ts => chainT (node t s) ts

/-- Deposits added one after another: the direct scatter on one node. -/
def chain (i : ι) (l : List ι) : Tree ι := chainT (leaf i) (l.map leaf)

theorem chainT_depth_le (t : Tree ι) (ts : List (Tree ι)) {D : ℕ} (ht : t.depth ≤ D)
    (hts : ∀ s ∈ ts, s.depth ≤ D) : (chainT t ts).depth ≤ D + ts.length := by
  induction ts generalizing t D with
  | nil => simpa [chainT]
  | cons s ts ih =>
    simp only [chainT, List.length_cons]
    have := ih (node t s) (D := D + 1)
      (by simp only [depth]; have := hts s (by simp); omega)
      (fun s' hs' => (hts s' (by simp [hs'])).trans (Nat.le_succ _))
    omega

theorem chain_depth (i : ι) (l : List ι) : (chain i l).depth = l.length := by
  suffices ∀ (t : Tree ι), (chainT t (l.map leaf)).depth = t.depth + l.length by
    simpa [chain, depth] using this (leaf i)
  induction l with
  | nil => simp [chainT]
  | cons j l ih => intro t; simp [chainT, ih, depth]; omega

theorem chain_leaves (i : ι) (l : List ι) : (chain i l).leaves = i :: l := by
  suffices ∀ (t : Tree ι), (chainT t (l.map leaf)).leaves = t.leaves ++ l by
    simpa [chain, leaves] using this (leaf i)
  induction l with
  | nil => simp [chainT]
  | cons j l ih => intro t; simp [chainT, ih, leaves]

end Tree

/-! ## Against fixed point -/

/-- A fixed-point node's error: shares each within three quanta `δ` of exact, over `n` deposits. -/
theorem fixed_error_le {ι : Type*} (s : Finset ι) (x q : ι → ℝ) {δ : ℝ}
    (h : ∀ i ∈ s, |q i - x i| ≤ 3 * δ) :
    |∑ i ∈ s, q i - ∑ i ∈ s, x i| ≤ 3 * #s * δ := by
  rw [← sum_sub_distrib]
  calc |∑ i ∈ s, (q i - x i)| ≤ ∑ i ∈ s, |q i - x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, 3 * δ := sum_le_sum h
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- The scale at which fixed point is no worse than floating point's worst case on `n + 1` atomics:
when `3·(n+1)·δ ≤ n·u·A`, the fixed-point bound is within the float chain's bound, for every order. -/
theorem fixed_le_float_bound (R : Rounding) {n : ℕ} {δ A : ℝ} (hA : 0 ≤ A)
    (hδ : 3 * (n + 1) * δ ≤ n * R.u * A) :
    3 * (n + 1) * δ ≤ gamma R.u n * A :=
  hδ.trans (mul_le_mul_of_nonneg_right (le_gamma R.u_nonneg n) hA)

/-! ## Underflow and the order of the product -/

/-- Mass first: when the mass share `rnd (w·m)` rounds to zero, so does the momentum share
`rnd (rnd (w·m) · v)`, for every rounding that keeps zero. -/
theorem massFirst_zero (rnd : ℝ → ℝ) (h0 : rnd 0 = 0) (w m v : ℝ) (h : rnd (w * m) = 0) :
    rnd (rnd (w * m) * v) = 0 := by
  rw [h, zero_mul, h0]

/-- Flush to zero: every value smaller than `t` becomes zero. Within `t` of exact, which is the
standard model's allowance for underflow. -/
noncomputable def flushToZero (t : ℝ) (x : ℝ) : ℝ := if |x| < t then 0 else x

theorem flushToZero_error {t : ℝ} (x : ℝ) : |flushToZero t x - x| ≤ max t 0 := by
  unfold flushToZero
  split_ifs with h
  · simp only [zero_sub, abs_neg]; exact h.le.trans (le_max_left _ _)
  · simp

/-- Momentum first: the mass share `rnd (w·m)` flushes to zero while the momentum share
`rnd (w · rnd (m·v))` does not, and the node holds momentum with no mass. -/
theorem momentumFirst_omega :
    flushToZero 1 ((1 / 2) * 1) = 0 ∧ flushToZero 1 ((1 / 2) * flushToZero 1 (1 * 4)) = 2 := by
  unfold flushToZero
  norm_num [abs_of_pos]

end Scatter
