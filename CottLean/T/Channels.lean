import CottLean.T.Interference
import CottLean.T.Radians

/-!
# The hidden channels of `Q` and `D`, and how they mix

A pair has two coordinates and a reading keeps one number, so each reading has a **hidden channel**: what
can change about the pair without changing what the reading says.

* `Q`'s hidden channel is a **coefficient**: `6/2 = 2·(3/1)`. Scaling by `k ≠ 0` keeps `Q` (`Q_scaleBy`).
* `D`'s hidden channel is an **offset**: `(695, 700) = (0, 5) + 695·(1, 1)`. Shifting along the diagonal
  keeps `D` (`D_shiftBy`), and every pair is its `D`-representative `(0, D)` shifted by its `p`
  (`eq_shiftBy_D`).

## The channels cross unequally

* **The coefficient acts on `D` as a coefficient**: `D(k·x) = k·D(x)` (`D_scaleBy`). No offset appears.
* **The offset acts on `Q` as neither.** `Q(x + t·(1, 1)) = (p + t)/(q + t)` (`Q_shiftBy`), and that is not a
  function of `Q` at all (`shiftBy_not_function_of_Q`): `3/1` and `6/2` both read `3`, and shifted by `1` they
  read `2` and `7/3`. What the offset does depends on `Q`'s hidden coefficient.
* **Only the offset per unit of coefficient matters.** On `k·v` the shift by `t` reads as the shift of `v` by
  `t/k` (`Q_shiftBy_scaleBy`). For `(695, 700) = 5·(139, 140)`, offset `695` from `(0, 5) = 5·(0, 1)`,
  `t/k = 139` and `Q = 139/140` (`example_695_700`).

## Why: the two channels do not commute

Scaling after a shift is a larger shift after scaling: `k·(x + t·d) = k·x + (k·t)·d` (`scaleBy_shiftBy`). They
commute only when the shift is `0` or the scale is `1` (`shiftBy_scaleBy_comm_iff`). Together they are the
maps `x ↦ k·x + t·d`, the `ax + b` group of a line, which is not commutative. So the mixing cannot be undone
by choosing coordinates, and `t/k` is the one combination `Q` sees.

## Through `L`: the coefficient is pure scale, the offset moves both

* A positive coefficient moves only the scale: `L_b(k·x) = (log_b N + log_b k², turn)` (`logScale_scaleBy`,
  `turn_scaleBy`). `6/2` is `3/1` with the scale moved by `log_b 4` and the turn unchanged. It is not a
  winding number: no turn is added.
* The offset moves the turn (`shiftBy_moves_turn`), and as it grows every pair's turn tends to `1/8`, the
  diagonal's (`tendsto_turn_shiftBy`). The offset carries the pair onto the line it shifts along.
-/

namespace T.Unquotiented

open Complex Filter Topology
open scoped Real

/-! ## The two channels -/

/-- `Q`'s hidden channel: scale by `k`. -/
def scaleBy (k : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (k * x.1, k * x.2)

/-- `D`'s hidden channel: shift by `t` along the diagonal `(1, 1)`. -/
def shiftBy (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (x.1 + t, x.2 + t)

theorem Q_scaleBy {k : ℝ} (hk : k ≠ 0) (x : ℝ × ℝ) :
    Q (scaleBy k x).1 (scaleBy k x).2 = Q x.1 x.2 := Q_smul x.1 x.2 hk

theorem D_shiftBy (t : ℝ) (x : ℝ × ℝ) : D (shiftBy t x).1 (shiftBy t x).2 = D x.1 x.2 := by
  simp [D, shiftBy]

/-- Every pair is its `D`-representative `(0, D)`, shifted by its `p`. -/
theorem eq_shiftBy_D (x : ℝ × ℝ) : x = shiftBy x.1 (0, D x.1 x.2) := by
  ext <;> simp [shiftBy, D]

/-! ## How they cross -/

/-- The coefficient acts on `D` as a coefficient. -/
theorem D_scaleBy (k : ℝ) (x : ℝ × ℝ) : D (scaleBy k x).1 (scaleBy k x).2 = k * D x.1 x.2 := by
  simp [D, scaleBy]; ring

/-- And on `S` too. -/
theorem S_scaleBy (k : ℝ) (x : ℝ × ℝ) : S (scaleBy k x).1 (scaleBy k x).2 = k * S x.1 x.2 := by
  simp [S, scaleBy]; ring

/-- The offset moves `S` by `2t`. -/
theorem S_shiftBy (t : ℝ) (x : ℝ × ℝ) : S (shiftBy t x).1 (shiftBy t x).2 = S x.1 x.2 + 2 * t := by
  simp [S, shiftBy]; ring

theorem Q_shiftBy (t : ℝ) (x : ℝ × ℝ) : Q (shiftBy t x).1 (shiftBy t x).2 = (x.1 + t) / (x.2 + t) := rfl

/-- The offset's effect on `Q` is not a function of `Q`: `3/1` and `6/2` shift to `2` and `7/3`. -/
theorem shiftBy_not_function_of_Q :
    ¬ ∃ f : ℝ → ℝ, ∀ x : ℝ × ℝ, Q (shiftBy 1 x).1 (shiftBy 1 x).2 = f (Q x.1 x.2) := by
  rintro ⟨f, hf⟩
  have h1 := hf (3, 1)
  have h2 := hf (6, 2)
  simp only [Q, shiftBy] at h1 h2
  norm_num at h1 h2
  rw [← h1] at h2
  norm_num at h2

/-- On `k·v` the shift by `t` is `k` times the shift of `v` by `t/k`. -/
theorem shiftBy_scaleBy {k : ℝ} (hk : k ≠ 0) (t : ℝ) (v : ℝ × ℝ) :
    shiftBy t (scaleBy k v) = scaleBy k (shiftBy (t / k) v) := by
  ext <;> simp [shiftBy, scaleBy] <;> field_simp

/-- So `Q` sees only the offset per unit of coefficient, `t/k`. -/
theorem Q_shiftBy_scaleBy {k : ℝ} (hk : k ≠ 0) (t : ℝ) (v : ℝ × ℝ) :
    Q (shiftBy t (scaleBy k v)).1 (shiftBy t (scaleBy k v)).2 =
      Q (shiftBy (t / k) v).1 (shiftBy (t / k) v).2 := by
  rw [shiftBy_scaleBy hk]; exact Q_scaleBy hk _

/-- `700 − 695`: offset `695` from `(0, 5) = 5·(0, 1)`, so `t/k = 139`, and `Q = 139/140`. -/
theorem example_695_700 :
    ((695, 700) : ℝ × ℝ) = shiftBy 695 (scaleBy 5 (0, 1)) ∧ ((695, 700) : ℝ × ℝ) = scaleBy 5 (139, 140) ∧
      Q (shiftBy 695 (scaleBy 5 (0, 1))).1 (shiftBy 695 (scaleBy 5 (0, 1))).2 =
        Q (shiftBy 139 (0, 1)).1 (shiftBy 139 (0, 1)).2 ∧
      Q (695 : ℝ) 700 = 139 / 140 := by
  refine ⟨by ext <;> norm_num [shiftBy, scaleBy], by ext <;> norm_num [scaleBy], ?_, by norm_num [Q]⟩
  rw [Q_shiftBy_scaleBy (by norm_num)]; norm_num

/-! ## The channels do not commute -/

/-- Scaling after a shift is a larger shift after scaling. -/
theorem scaleBy_shiftBy (k t : ℝ) (x : ℝ × ℝ) :
    scaleBy k (shiftBy t x) = shiftBy (k * t) (scaleBy k x) := by
  ext <;> simp [shiftBy, scaleBy] <;> ring

/-- They commute only when the shift is `0` or the scale is `1`. -/
theorem shiftBy_scaleBy_comm_iff (k t : ℝ) :
    (∀ x, shiftBy t (scaleBy k x) = scaleBy k (shiftBy t x)) ↔ t = 0 ∨ k = 1 := by
  constructor
  · intro h
    have := congrArg Prod.fst (h (0, 0))
    simp only [shiftBy, scaleBy, mul_zero, zero_add] at this
    have : t * (1 - k) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) x <;> ext <;> simp [shiftBy, scaleBy]

/-! ## Through `L` -/

theorem N_scaleBy (k : ℝ) (x : ℝ × ℝ) : N (scaleBy k x).1 (scaleBy k x).2 = k ^ 2 * N x.1 x.2 := by
  simp [N, scaleBy]; ring

/-- A coefficient moves the scale by `log_b k²`. -/
theorem logScale_scaleBy (b : ℝ) {k : ℝ} (hk : k ≠ 0) {x : ℝ × ℝ} (hx : C x.1 x.2 ≠ 0) :
    logScale b (scaleBy k x).1 (scaleBy k x).2 = logScale b x.1 x.2 + Real.logb b (k ^ 2) := by
  rw [logScale, N_scaleBy, Real.logb_mul (pow_ne_zero 2 hk) (N_pos hx).ne', logScale, add_comm]

/-- A positive coefficient leaves the turn. -/
theorem turn_scaleBy {k : ℝ} (hk : 0 < k) (x : ℝ × ℝ) :
    turn (scaleBy k x).1 (scaleBy k x).2 = turn x.1 x.2 := turn_smul _ _ hk

/-- The offset moves the turn: `(0, 1)` has turn `0`, and `(1, 2)` does not. -/
theorem shiftBy_moves_turn : turn (shiftBy 1 (0, 1)).1 (shiftBy 1 (0, 1)).2 ≠ turn 0 1 := by
  have h0 : turn 0 1 = 0 := by
    have : C 0 1 = 1 := by apply Complex.ext <;> simp [C]
    rw [turn, this, arg_one, zero_div]
  rw [h0, turn, div_ne_zero_iff]
  refine ⟨?_, by positivity⟩
  rw [Ne, Complex.arg_eq_zero_iff]
  simp [shiftBy, C]

private theorem C_eq_add (a b : ℝ) : C a b = (b : ℂ) + (a : ℂ) * I := by
  apply Complex.ext <;> simp [C]

/-- As the offset grows, every pair's turn tends to `1/8`, the diagonal's. -/
theorem tendsto_turn_shiftBy (x : ℝ × ℝ) :
    Tendsto (fun t => turn (shiftBy t x).1 (shiftBy t x).2) atTop (𝓝 (1 / 8)) := by
  set g : ℝ → ℝ := fun u => arg (C (x.1 * u + 1) (x.2 * u + 1)) / (2 * π)
  have hC : Continuous fun u : ℝ => C (x.1 * u + 1) (x.2 * u + 1) := by
    simp only [C_eq_add]; fun_prop
  have hg : ContinuousAt g 0 := by
    have hmem : C (x.1 * 0 + 1) (x.2 * 0 + 1) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left; simp [C]
    exact (ContinuousAt.comp (g := arg) (f := fun u : ℝ => C (x.1 * u + 1) (x.2 * u + 1))
      (continuousAt_arg hmem) hC.continuousAt).div_const _
  have hg0 : g 0 = 1 / 8 := by
    have : C (x.1 * 0 + 1) (x.2 * 0 + 1) = 1 + I := by apply Complex.ext <;> simp [C]
    simp only [g, this, arg_one_add_I]
    field_simp; ring
  have hlim := hg.tendsto.comp tendsto_inv_atTop_zero
  rw [hg0] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp, g, shiftBy]
  have e1 : x.1 + t = t * (x.1 * t⁻¹ + 1) := by field_simp
  have e2 : x.2 + t = t * (x.2 * t⁻¹ + 1) := by field_simp
  rw [e1, e2, turn_smul _ _ ht, turn]

end T.Unquotiented
