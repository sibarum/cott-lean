import CottLean.Scatter.Quantise

/-!
# Scatter: quantised shares on any stencil

`Scatter/Quantise.lean` quantises a particle's four bilinear shares. MLS-MPM deposits on a 3×3 stencil
with quadratic B-spline weights instead (vexelray-sim-fluid's `particle.Flip`), and other kernels use
other stencils. The scheme is the same on all of them: every node but one takes the floor of its exact
share, and the one left, the *remainder node* `r`, takes what is left of the particle's amount:

```
share k = ⌊w k · M⌋                          for k ≠ r
share r = M − Σ_{k ≠ r} ⌊w k · M⌋
```

## What is proved, for any finite stencil and any remainder node

* `sum_remainderShares`: the shares sum to the particle's amount, exactly.
* `remainderShares_nonneg`: none is negative, when the weights are not and sum to one.
* `remainderShares_error`: every node but `r` is within `(-1, 0]` quanta of its exact share, and `r`
  within `[0, n − 1)`, for a stencil of `n` nodes. The error the floors leave all lands on `r`.
* `sum_remainderShares_mul`, `remainderShares_mul_eq_zero`: momentum as the mass share times the
  velocity is conserved exactly and leaves a massless node no momentum, as for four corners;
  `Scatter.node_velocity_between` and `Scatter.node_momentum_eq_zero` apply unchanged.
* `shares_eq_remainderShares`: the four-corner scheme is this one, with the north-east corner as `r`.

## The weights

* `tensor`: the weights of a stencil in two dimensions are the product of one per axis, numbered
  `k = i + n·j` for `i` along and `j` up, as `Scatter.segmentedDeposit` numbers them. They sum to one
  and are non-negative when each axis's are (`sum_tensor`, `tensor_nonneg`).
* `bilinear_eq_tensor`: the bilinear weights are the tensor of the linear ones, `[1 − f, f]`.
* `quadratic`: the quadratic B-spline weights `½(3/2 − f)²`, `3/4 − (f − 1)²`, `½(f − ½)²` along one
  axis. They sum to one for every `f` (`sum_quadratic`), and are non-negative for `f` in `[½, 3/2]`,
  the interval `Flip.Stencil` clamps to (`quadratic_nonneg`). Outside it the middle weight can go
  negative (`quadratic_one_neg`).

## Which node takes the remainder

The remainder node's error is up to `n − 1` quanta, so it should be the node whose exact share is
largest. On the quadratic stencil that is the centre: its weight is at least `¼` wherever the particle
is (`quadratic_center_ge`), while a corner's can be as small as zero. With the centre as `r`, the
remainder's error of under eight quanta is on a share of at least a quarter of the particle.
-/

namespace Scatter

open Finset

/-! ## Shares with a remainder node -/

section Remainder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A particle's integer shares on a stencil: every node but `r` floored, and `r` the rest of `M`. -/
def remainderShares (w : ι → ℚ) (M : ℤ) (r : ι) (k : ι) : ℤ :=
  if k = r then M - ∑ j ∈ univ.erase r, ⌊w j * M⌋ else ⌊w k * M⌋

theorem remainderShares_of_ne (w : ι → ℚ) (M : ℤ) {r k : ι} (h : k ≠ r) :
    remainderShares w M r k = ⌊w k * M⌋ := if_neg h

theorem remainderShares_self (w : ι → ℚ) (M : ℤ) (r : ι) :
    remainderShares w M r r = M - ∑ j ∈ univ.erase r, ⌊w j * M⌋ := if_pos rfl

/-- The shares sum to the particle's amount, exactly. -/
theorem sum_remainderShares (w : ι → ℚ) (M : ℤ) (r : ι) : ∑ k, remainderShares w M r k = M := by
  rw [← add_sum_erase _ _ (mem_univ r), remainderShares_self,
    sum_congr rfl fun k hk => remainderShares_of_ne w M (ne_of_mem_erase hk)]
  ring

/-- The remainder node exceeds its exact share by what the floors took from the others. -/
theorem remainderShares_self_sub (w : ι → ℚ) (M : ℤ) (r : ι) (hw : ∑ k, w k = 1) :
    (remainderShares w M r r : ℚ) - w r * M = ∑ j ∈ univ.erase r, (w j * M - ⌊w j * M⌋) := by
  rw [← add_sum_erase _ _ (mem_univ r)] at hw
  have : w r = 1 - ∑ j ∈ univ.erase r, w j := by linarith
  rw [remainderShares_self, this, sum_sub_distrib, ← sum_mul]
  push_cast; ring

/-- Every node but `r` is within `(-1, 0]` quanta of its exact share. -/
theorem remainderShares_error_of_ne (w : ι → ℚ) (M : ℤ) {r k : ι} (h : k ≠ r) :
    -1 < (remainderShares w M r k : ℚ) - w k * M ∧ (remainderShares w M r k : ℚ) - w k * M ≤ 0 := by
  rw [remainderShares_of_ne w M h]
  constructor <;> linarith [Int.floor_le (w k * M), Int.lt_floor_add_one (w k * M)]

/-- The remainder node is within `[0, n − 1)` quanta of its exact share, on a stencil of `n` nodes
(for `n ≥ 2`; on a stencil of one node the share is exact). -/
theorem remainderShares_error_self (w : ι → ℚ) (M : ℤ) (r : ι) (hw : ∑ k, w k = 1) :
    0 ≤ (remainderShares w M r r : ℚ) - w r * M ∧
      (remainderShares w M r r : ℚ) - w r * M ≤ Fintype.card ι - 1 := by
  rw [remainderShares_self_sub w M r hw]
  have hcard : ((univ.erase r).card : ℚ) = Fintype.card ι - 1 := by
    rw [card_erase_of_mem (mem_univ r), card_univ, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨r⟩)]
    simp
  constructor
  · exact sum_nonneg fun j _ => by linarith [Int.floor_le (w j * M)]
  · rw [← hcard, ← nsmul_one, ← sum_const]
    exact sum_le_sum fun j _ => by linarith [Int.lt_floor_add_one (w j * M)]

/-- Strictly under `n − 1`, when the stencil has another node. -/
theorem remainderShares_error_self_lt (w : ι → ℚ) (M : ℤ) (r : ι) (hw : ∑ k, w k = 1)
    (hn : (univ.erase r).Nonempty) :
    (remainderShares w M r r : ℚ) - w r * M < Fintype.card ι - 1 := by
  rw [remainderShares_self_sub w M r hw]
  have hcard : ((univ.erase r).card : ℚ) = Fintype.card ι - 1 := by
    rw [card_erase_of_mem (mem_univ r), card_univ, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨r⟩)]
    simp
  rw [← hcard, ← nsmul_one, ← sum_const]
  exact sum_lt_sum_of_nonempty hn fun j _ => by linarith [Int.lt_floor_add_one (w j * M)]

/-- No share is negative, for a non-negative amount and non-negative weights summing to one. -/
theorem remainderShares_nonneg (w : ι → ℚ) (M : ℤ) (r : ι) (hw : ∑ k, w k = 1)
    (hw0 : ∀ k, 0 ≤ w k) (hM : 0 ≤ M) (k : ι) : 0 ≤ remainderShares w M r k := by
  have hMq : (0 : ℚ) ≤ M := by exact_mod_cast hM
  by_cases h : k = r
  · subst h
    have := (remainderShares_error_self w M k hw).1
    have : (0 : ℚ) ≤ remainderShares w M k k := by linarith [mul_nonneg (hw0 k) hMq]
    exact_mod_cast this
  · rw [remainderShares_of_ne w M h]
    exact Int.floor_nonneg.mpr (mul_nonneg (hw0 k) hMq)

/-- Momentum as the mass share times the velocity is conserved exactly. -/
theorem sum_remainderShares_mul (w : ι → ℚ) (M v : ℤ) (r : ι) :
    ∑ k, remainderShares w M r k * v = M * v := by
  rw [← sum_mul, sum_remainderShares]

/-- And a node with no mass gets no momentum. -/
theorem remainderShares_mul_eq_zero (w : ι → ℚ) (M v : ℤ) (r k : ι)
    (h : remainderShares w M r k = 0) : remainderShares w M r k * v = 0 := by
  rw [h, zero_mul]

end Remainder

/-- The four-corner scheme of `Scatter/Quantise.lean` is this one, with the north-east corner, `3`, as
the remainder node. -/
theorem shares_eq_remainderShares (w : Fin 4 → ℚ) (M : ℤ) : shares w M = remainderShares w M 3 := by
  funext k
  fin_cases k <;> simp [shares, remainderShares, Finset.sum_erase_eq_sub, Fin.sum_univ_succ]
  ring

/-! ## Weights in two dimensions -/

/-- The weights of a two-dimensional stencil, as the product of one axis's along and one's up. Node
`k = i + n·j` is `i` along and `j` up. -/
def tensor {n m : ℕ} (wx : Fin n → ℚ) (wy : Fin m → ℚ) (k : Fin (m * n)) : ℚ :=
  wx (finProdFinEquiv.symm k).2 * wy (finProdFinEquiv.symm k).1

theorem tensor_apply {n m : ℕ} (wx : Fin n → ℚ) (wy : Fin m → ℚ) (j : Fin m) (i : Fin n) :
    tensor wx wy (finProdFinEquiv (j, i)) = wx i * wy j := by
  simp [tensor]

/-- Node `k` of the stencil is `k % n` along (`Fin.modNat`) and `k / n` up (`Fin.divNat`). -/
theorem tensor_apply' {n m : ℕ} (wx : Fin n → ℚ) (wy : Fin m → ℚ) (k : Fin (m * n)) :
    tensor wx wy k = wx k.modNat * wy k.divNat := by
  simp [tensor]

theorem sum_tensor {n m : ℕ} (wx : Fin n → ℚ) (wy : Fin m → ℚ) :
    ∑ k, tensor wx wy k = (∑ i, wx i) * ∑ j, wy j := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, sum_mul_sum, sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [tensor_apply]

theorem tensor_nonneg {n m : ℕ} {wx : Fin n → ℚ} {wy : Fin m → ℚ} (hx : ∀ i, 0 ≤ wx i)
    (hy : ∀ j, 0 ≤ wy j) (k : Fin (m * n)) : 0 ≤ tensor wx wy k :=
  mul_nonneg (hx _) (hy _)

/-- The linear weights along one axis: `1 − f` on the node behind, `f` on the node ahead. -/
def linear (f : ℚ) : Fin 2 → ℚ := ![1 - f, f]

/-- The bilinear weights are the linear ones, tensored. -/
theorem bilinear_eq_tensor (fx fy : ℚ) : bilinear fx fy = tensor (linear fx) (linear fy) := by
  funext k
  fin_cases k <;> simp [bilinear, linear, tensor_apply'] <;> rfl

/-! ## Quadratic B-spline weights -/

/-- The quadratic B-spline weights along one axis, for a particle at `f` from the stencil's first
node: `½(3/2 − f)²`, `3/4 − (f − 1)²` and `½(f − ½)²`. -/
def quadratic (f : ℚ) : Fin 3 → ℚ :=
  ![(3 / 2 - f) ^ 2 / 2, 3 / 4 - (f - 1) ^ 2, (f - 1 / 2) ^ 2 / 2]

/-- They sum to one for every `f`. -/
theorem sum_quadratic (f : ℚ) : ∑ k, quadratic f k = 1 := by
  simp [quadratic, Fin.sum_univ_three]; ring

/-- The middle weight is at least `½` for `f` in `[½, 3/2]`. -/
theorem quadratic_one_ge {f : ℚ} (h₀ : 1 / 2 ≤ f) (h₁ : f ≤ 3 / 2) : 1 / 2 ≤ quadratic f 1 := by
  simp only [quadratic]
  change 1 / 2 ≤ 3 / 4 - (f - 1) ^ 2
  nlinarith

/-- They are non-negative for `f` in `[½, 3/2]`, where `Flip.Stencil` keeps every particle. -/
theorem quadratic_nonneg {f : ℚ} (h₀ : 1 / 2 ≤ f) (h₁ : f ≤ 3 / 2) (k : Fin 3) :
    0 ≤ quadratic f k := by
  fin_cases k
  · change 0 ≤ (3 / 2 - f) ^ 2 / 2; positivity
  · exact (by norm_num : (0 : ℚ) ≤ 1 / 2).trans (quadratic_one_ge h₀ h₁)
  · change 0 ≤ (f - 1 / 2) ^ 2 / 2; positivity

/-- Outside that interval the middle weight can be negative: at `f = 2` it is `-¼`. -/
theorem quadratic_one_neg : quadratic 2 1 < 0 := by
  simp only [quadratic]; norm_num

/-- The quadratic weights of a 3×3 stencil, numbered as `Flip.Stencil` numbers them. -/
def quadratic2 (fx fy : ℚ) : Fin 9 → ℚ := tensor (quadratic fx) (quadratic fy)

theorem sum_quadratic2 (fx fy : ℚ) : ∑ k, quadratic2 fx fy k = 1 := by
  have := sum_tensor (quadratic fx) (quadratic fy)
  rw [sum_quadratic, sum_quadratic, one_mul] at this
  exact this

theorem quadratic2_nonneg {fx fy : ℚ} (hx₀ : 1 / 2 ≤ fx) (hx₁ : fx ≤ 3 / 2) (hy₀ : 1 / 2 ≤ fy)
    (hy₁ : fy ≤ 3 / 2) (k : Fin 9) : 0 ≤ quadratic2 fx fy k :=
  tensor_nonneg (quadratic_nonneg hx₀ hx₁) (quadratic_nonneg hy₀ hy₁) k

/-- The centre of the stencil, node `4`, always weighs at least a quarter. -/
theorem quadratic_center_ge {fx fy : ℚ} (hx₀ : 1 / 2 ≤ fx) (hx₁ : fx ≤ 3 / 2) (hy₀ : 1 / 2 ≤ fy)
    (hy₁ : fy ≤ 3 / 2) : 1 / 4 ≤ quadratic2 fx fy 4 := by
  have hx := quadratic_one_ge hx₀ hx₁
  have hy := quadratic_one_ge hy₀ hy₁
  have : quadratic2 fx fy 4 = quadratic fx 1 * quadratic fy 1 := by
    rw [quadratic2, tensor_apply']; rfl
  rw [this]; nlinarith

/-! ## The 3×3 stencil, quantised -/

/-- A particle's integer shares on the quadratic 3×3 stencil, with the centre taking the remainder. -/
def quadraticShares (fx fy : ℚ) (M : ℤ) : Fin 9 → ℤ := remainderShares (quadratic2 fx fy) M 4

/-- Exact conservation. -/
theorem sum_quadraticShares (fx fy : ℚ) (M : ℤ) : ∑ k, quadraticShares fx fy M k = M :=
  sum_remainderShares _ _ _

/-- No share is negative, wherever `Flip.Stencil` puts the particle. -/
theorem quadraticShares_nonneg {fx fy : ℚ} (hx₀ : 1 / 2 ≤ fx) (hx₁ : fx ≤ 3 / 2) (hy₀ : 1 / 2 ≤ fy)
    (hy₁ : fy ≤ 3 / 2) {M : ℤ} (hM : 0 ≤ M) (k : Fin 9) : 0 ≤ quadraticShares fx fy M k :=
  remainderShares_nonneg _ _ _ (sum_quadratic2 fx fy) (quadratic2_nonneg hx₀ hx₁ hy₀ hy₁) hM k

/-- The centre's share is within `[0, 8)` quanta of exact, and exact is at least a quarter of `M`. -/
theorem quadraticShares_center {fx fy : ℚ} (hx₀ : 1 / 2 ≤ fx) (hx₁ : fx ≤ 3 / 2) (hy₀ : 1 / 2 ≤ fy)
    (hy₁ : fy ≤ 3 / 2) {M : ℤ} (hM : 0 ≤ M) :
    0 ≤ (quadraticShares fx fy M 4 : ℚ) - quadratic2 fx fy 4 * M ∧
      (quadraticShares fx fy M 4 : ℚ) - quadratic2 fx fy 4 * M < 8 ∧
      (M : ℚ) / 4 ≤ quadratic2 fx fy 4 * M := by
  refine ⟨(remainderShares_error_self _ M 4 (sum_quadratic2 fx fy)).1, ?_, ?_⟩
  · have := remainderShares_error_self_lt (quadratic2 fx fy) M 4 (sum_quadratic2 fx fy)
      ⟨0, by simp⟩
    unfold quadraticShares; norm_num at this ⊢; linarith
  · have := quadratic_center_ge hx₀ hx₁ hy₀ hy₁
    have hMq : (0 : ℚ) ≤ M := by exact_mod_cast hM
    nlinarith

end Scatter
