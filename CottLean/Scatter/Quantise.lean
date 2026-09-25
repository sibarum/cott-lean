import CottLean.Scatter.Accumulate

/-!
# Scatter: quantising a particle's shares so conservation stays exact

A fixed-point scatter deposits integers, so each particle's four bilinear shares have to be rounded.
Rounding each on its own would make the four no longer sum to the particle's amount. The remedy in
vexelray-sim-fluid's `docs/TODO.md` is to round three corners and give the fourth the rest:

```
share k = ⌊w k · M⌋          for k = 0, 1, 2
share 3 = M − (share 0 + share 1 + share 2)
```

Amounts are in quanta of the fixed-point scale: `M` is an integer, and the weights `w` are the
bilinear ones (`bilinear`), which are non-negative and sum to one (`bilinear_nonneg`, `sum_bilinear`).

## What is proved

* `sum_shares`: a particle's four shares sum to its amount, exactly. With
  `Scatter.total_grid_particles` the grid holds exactly the particles' total.
* `shares_nonneg`: no share is negative. A light particle's share can round to zero, and then its mass
  moves to the fourth corner rather than being lost. So how small a deposit may be is a question of
  accuracy only, never of conservation.
* `share_error`: each share is within `(-1, 3)` quanta of its exact value `w k · M`, the three floored
  ones within `(-1, 0]` and the remainder within `[0, 3)`.

## Momentum

Momentum should not be rounded independently of mass. If it is, the mass share at a corner can round to
zero while the momentum share does not, and the node holds `T(k, 0)`, a multiple of `ω`: momentum with
no mass, which is an infinite velocity at the division (`independent_rounding_omega`).

Depositing `share k · v` instead, with `v` the particle's fixed-point velocity, fixes this at the
cost of range, since the product must fit in the register:

* `sum_momentumShares`: momentum is conserved exactly, `Σ share k · v = M · v`.
* `momentumShares_eq_zero`: a corner with no mass gets no momentum.
* `node_velocity_between`: a node's momentum is between its mass times the least and the greatest
  velocity of the particles that reached it. So the node's velocity, the mediant of theirs, lies
  between theirs, as `T.MediantTree` has it for two parents.
* `node_momentum_eq_zero`: a node with no mass has no momentum, so it is `0ω`, never `ω`.
-/

namespace Scatter

open Finset

/-! ## The bilinear weights -/

/-- The bilinear weights of a particle at offset `(fx, fy)` in its cell, corner by corner: the lower
left, the lower right, the upper left and the upper right. -/
def bilinear (fx fy : ℚ) : Fin 4 → ℚ :=
  ![(1 - fx) * (1 - fy), fx * (1 - fy), (1 - fx) * fy, fx * fy]

theorem sum_bilinear (fx fy : ℚ) : ∑ k, bilinear fx fy k = 1 := by
  simp [bilinear, Fin.sum_univ_four]; ring

theorem bilinear_nonneg {fx fy : ℚ} (hx₀ : 0 ≤ fx) (hx₁ : fx ≤ 1) (hy₀ : 0 ≤ fy) (hy₁ : fy ≤ 1)
    (k : Fin 4) : 0 ≤ bilinear fx fy k := by
  have a : 0 ≤ 1 - fx := by linarith
  have b : 0 ≤ 1 - fy := by linarith
  fin_cases k
  · exact mul_nonneg a b
  · exact mul_nonneg hx₀ b
  · exact mul_nonneg a hy₀
  · exact mul_nonneg hx₀ hy₀

/-! ## The shares -/

/-- A particle's integer shares: three corners floored, and the fourth the rest of `M`. -/
def shares (w : Fin 4 → ℚ) (M : ℤ) : Fin 4 → ℤ :=
  ![⌊w 0 * M⌋, ⌊w 1 * M⌋, ⌊w 2 * M⌋, M - (⌊w 0 * M⌋ + ⌊w 1 * M⌋ + ⌊w 2 * M⌋)]

/-- The four shares sum to the particle's amount, exactly. -/
theorem sum_shares (w : Fin 4 → ℚ) (M : ℤ) : ∑ k, shares w M k = M := by
  simp [shares, Fin.sum_univ_four]

/-- The remainder corner exceeds its exact share by what the other three lost to the floor. -/
theorem shares_three (w : Fin 4 → ℚ) (M : ℤ) (hw : ∑ k, w k = 1) :
    (shares w M 3 : ℚ) - w 3 * M =
      (w 0 * M - ⌊w 0 * M⌋) + (w 1 * M - ⌊w 1 * M⌋) + (w 2 * M - ⌊w 2 * M⌋) := by
  rw [Fin.sum_univ_four] at hw
  have : w 3 = 1 - w 0 - w 1 - w 2 := by linarith
  rw [show shares w M 3 = M - (⌊w 0 * M⌋ + ⌊w 1 * M⌋ + ⌊w 2 * M⌋) from rfl, this]
  push_cast; ring

/-- Each share is within `(-1, 3)` quanta of its exact value: the floored three lose less than one,
and the remainder gains less than three. -/
theorem share_error (w : Fin 4 → ℚ) (M : ℤ) (hw : ∑ k, w k = 1) (k : Fin 4) :
    -1 < (shares w M k : ℚ) - w k * M ∧ (shares w M k : ℚ) - w k * M < 3 := by
  have f := fun j : Fin 4 => Int.floor_le (w j * M)
  have g := fun j : Fin 4 => Int.lt_floor_add_one (w j * M)
  have h3 := shares_three w M hw
  fin_cases k
  · simp [shares]; constructor <;> linarith [f 0, g 0]
  · simp [shares]; constructor <;> linarith [f 1, g 1]
  · simp [shares]; constructor <;> linarith [f 2, g 2]
  · simp only [Fin.reduceFinMk, Fin.isValue] at h3 ⊢
    rw [h3]; constructor <;> linarith [f 0, g 0, f 1, g 1, f 2, g 2]

/-- No share is negative, for a non-negative amount and weights. -/
theorem shares_nonneg (w : Fin 4 → ℚ) (M : ℤ) (hw : ∑ k, w k = 1) (hw0 : ∀ k, 0 ≤ w k)
    (hM : 0 ≤ M) (k : Fin 4) : 0 ≤ shares w M k := by
  have hMq : (0 : ℚ) ≤ M := by exact_mod_cast hM
  have floor_nonneg : ∀ j, 0 ≤ ⌊w j * M⌋ := fun j => Int.floor_nonneg.mpr (mul_nonneg (hw0 j) hMq)
  fin_cases k
  · exact floor_nonneg 0
  · exact floor_nonneg 1
  · exact floor_nonneg 2
  · have h3 := shares_three w M hw
    have f := fun j : Fin 4 => Int.floor_le (w j * M)
    have : (0 : ℚ) ≤ shares w M 3 := by
      linarith [f 0, f 1, f 2, mul_nonneg (hw0 3) hMq]
    exact_mod_cast this

/-! ## Momentum -/

/-- The momentum shares: each corner's mass share times the particle's velocity. -/
def momentumShares (w : Fin 4 → ℚ) (M v : ℤ) (k : Fin 4) : ℤ := shares w M k * v

/-- Momentum is conserved exactly. -/
theorem sum_momentumShares (w : Fin 4 → ℚ) (M v : ℤ) : ∑ k, momentumShares w M v k = M * v := by
  simp [momentumShares, ← sum_mul, sum_shares]

/-- A corner with no mass gets no momentum. -/
theorem momentumShares_eq_zero (w : Fin 4 → ℚ) (M v : ℤ) (k : Fin 4) (h : shares w M k = 0) :
    momentumShares w M v k = 0 := by
  simp [momentumShares, h]

/-- A node's momentum lies between its mass times the least and the greatest of the velocities that
reached it, when the masses are not negative. -/
theorem node_velocity_between {ι : Type*} (s : Finset ι) (m v : ι → ℤ) {lo hi : ℤ}
    (hm : ∀ i ∈ s, 0 ≤ m i) (hv : ∀ i ∈ s, lo ≤ v i ∧ v i ≤ hi) :
    lo * ∑ i ∈ s, m i ≤ ∑ i ∈ s, m i * v i ∧ ∑ i ∈ s, m i * v i ≤ hi * ∑ i ∈ s, m i := by
  rw [mul_sum, mul_sum]
  constructor
  · exact sum_le_sum fun i hi' => by nlinarith [hm i hi', (hv i hi').1]
  · exact sum_le_sum fun i hi' => by nlinarith [hm i hi', (hv i hi').2]

/-- A node with no mass has no momentum: it holds `0ω`, never a multiple of `ω`. -/
theorem node_momentum_eq_zero {ι : Type*} (s : Finset ι) (m v : ι → ℤ) (hm : ∀ i ∈ s, 0 ≤ m i)
    (h : ∑ i ∈ s, m i = 0) : ∑ i ∈ s, m i * v i = 0 := by
  have := (sum_eq_zero_iff_of_nonneg hm).mp h
  exact sum_eq_zero fun i hi => by rw [this i hi, zero_mul]

/-- Rounding momentum on its own goes wrong: a particle of one quantum of mass at velocity `10`,
halfway along its cell's bottom edge, gives its lower-left corner no mass but five quanta of
momentum. -/
theorem independent_rounding_omega :
    shares (bilinear (1 / 2) 0) 1 0 = 0 ∧ ⌊bilinear (1 / 2) 0 0 * (1 * 10 : ℤ)⌋ = 5 := by
  constructor
  · simp only [shares, bilinear]; norm_num
  · simp only [bilinear]; norm_num

end Scatter
