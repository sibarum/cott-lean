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


/-! ## The full momentum deposit

MLS-MPM's momentum deposit is not only the mass share times the velocity. Node `k`, at offset
`d = xₖ − xₚ` from the particle, receives `(w·m)·(v + C·d) + w·s·d`: the affine velocity `C·d` and the
pressure impulse `s·d`, both signed and neither proportional to the mass share. In exact arithmetic their
sums over the stencil vanish, because the weights' first moment `Σ w·d` is zero (`sum_quadratic_moment`,
`sum_quadratic2_moment_x`, `sum_quadratic2_moment_y`), so the particle's total is `m·v`
(`sum_affine_amount`). Flooring each node's amount on its own would lose that.

The remedy is the remainder again, with a mask: every node but the remainder takes the floor of its amount,
or nothing if its mass share is zero, and the remainder takes the rest of the exact total
(`maskedShares`). Then:

* `sum_maskedShares`: the momentum shares sum to the exact total, so momentum is conserved exactly, the
  affine and pressure terms included.
* `maskedShares_eq_zero`: a node with no mass gets no momentum, whatever its amount.
* `maskedShares_error_of_ne`, `maskedShares_self_sub`: every other node is within one quantum of its
  amount or holds nothing, and the remainder takes up exactly what they missed.
* `quadraticShares_center_pos`, `quadraticMomentum_eq_zero`: on the quadratic stencil the centre, which
  takes the remainder, always has mass when the particle does, so no node of the stencil ever holds
  momentum without mass.
-/

section Masked

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Momentum shares: every node but `r` takes the floor of its amount `p k`, or nothing when its mass
share is zero; `r` takes the rest of the total `P`. -/
def maskedShares (mass : ι → ℤ) (p : ι → ℚ) (P : ℤ) (r : ι) (k : ι) : ℤ :=
  if k = r then P - ∑ j ∈ univ.erase r, (if mass j = 0 then 0 else ⌊p j⌋)
  else if mass k = 0 then 0 else ⌊p k⌋

/-- Momentum is conserved exactly. -/
theorem sum_maskedShares (mass : ι → ℤ) (p : ι → ℚ) (P : ℤ) (r : ι) :
    ∑ k, maskedShares mass p P r k = P := by
  rw [← add_sum_erase _ _ (mem_univ r)]
  unfold maskedShares
  rw [if_pos rfl, sum_congr rfl fun k hk => if_neg (ne_of_mem_erase hk)]
  ring

/-- A node with no mass, other than the remainder, gets no momentum. -/
theorem maskedShares_eq_zero (mass : ι → ℤ) (p : ι → ℚ) (P : ℤ) {r k : ι} (hk : k ≠ r)
    (h : mass k = 0) : maskedShares mass p P r k = 0 := by
  simp [maskedShares, hk, h]

/-- A node with mass, other than the remainder, is within `(-1, 0]` quanta of its amount. -/
theorem maskedShares_error_of_ne (mass : ι → ℤ) (p : ι → ℚ) (P : ℤ) {r k : ι} (hk : k ≠ r)
    (h : mass k ≠ 0) :
    -1 < (maskedShares mass p P r k : ℚ) - p k ∧ (maskedShares mass p P r k : ℚ) - p k ≤ 0 := by
  simp only [maskedShares, if_neg hk, if_neg h]
  constructor <;> linarith [Int.floor_le (p k), Int.lt_floor_add_one (p k)]

/-- When the amounts sum to the total, the remainder exceeds its amount by exactly what the other
nodes missed. -/
theorem maskedShares_self_sub (mass : ι → ℤ) (p : ι → ℚ) (P : ℤ) (r : ι) (hp : ∑ k, p k = P) :
    (maskedShares mass p P r r : ℚ) - p r =
      ∑ j ∈ univ.erase r, (p j - maskedShares mass p P r j) := by
  have hs := sum_maskedShares mass p P r
  rw [← add_sum_erase _ _ (mem_univ r)] at hs hp
  have hs' : ((maskedShares mass p P r r : ℤ) : ℚ) +
      ∑ j ∈ univ.erase r, ((maskedShares mass p P r j : ℤ) : ℚ) = P := by exact_mod_cast hs
  rw [sum_sub_distrib]
  linarith

end Masked

/-- A node's amount with an affine velocity and a pressure impulse, per axis:
`w·(M·(V + cx·dx + cy·dy) + S·dx)`. The weights' first moments make the two offset terms cancel. -/
theorem sum_affine_amount {ι : Type*} [Fintype ι] (w dx dy : ι → ℚ) (M V cx cy S : ℚ)
    (hw : ∑ k, w k = 1) (hx : ∑ k, w k * dx k = 0) (hy : ∑ k, w k * dy k = 0) :
    ∑ k, w k * (M * (V + cx * dx k + cy * dy k) + S * dx k) = M * V := by
  have : ∀ k, w k * (M * (V + cx * dx k + cy * dy k) + S * dx k) =
      M * V * w k + (M * cx + S) * (w k * dx k) + M * cy * (w k * dy k) := fun k => by ring
  simp_rw [this, sum_add_distrib, ← mul_sum, hw, hx, hy]
  ring

/-- The quadratic weights' first moment is zero: `Σ w k · (k − f) = 0`, node `k` at `k` and the
particle at `f`. -/
theorem sum_quadratic_moment (f : ℚ) : ∑ k : Fin 3, quadratic f k * ((k : ℚ) - f) = 0 := by
  simp [quadratic, Fin.sum_univ_three]; ring

theorem modNat_finProdFinEquiv {n m : ℕ} (q : Fin m × Fin n) : (finProdFinEquiv q).modNat = q.2 := by
  have h := finProdFinEquiv.symm_apply_apply q
  rw [finProdFinEquiv_symm_apply] at h
  exact congrArg Prod.snd h

theorem divNat_finProdFinEquiv {n m : ℕ} (q : Fin m × Fin n) : (finProdFinEquiv q).divNat = q.1 := by
  have h := finProdFinEquiv.symm_apply_apply q
  rw [finProdFinEquiv_symm_apply] at h
  exact congrArg Prod.fst h

/-- A stencil weight times a function of the node's column sums as the column's weights times that. -/
theorem sum_tensor_mul_modNat {n m : ℕ} (wx : Fin n → ℚ) (wy : Fin m → ℚ) (g : Fin n → ℚ) :
    ∑ k, tensor wx wy k * g k.modNat = (∑ i, wx i * g i) * ∑ j, wy j := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, sum_mul_sum, sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [tensor_apply, modNat_finProdFinEquiv]
  ring

/-- And of the node's row. -/
theorem sum_tensor_mul_divNat {n m : ℕ} (wx : Fin n → ℚ) (wy : Fin m → ℚ) (g : Fin m → ℚ) :
    ∑ k, tensor wx wy k * g k.divNat = (∑ i, wx i) * ∑ j, wy j * g j := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, sum_mul_sum, sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [tensor_apply, divNat_finProdFinEquiv]
  ring

/-- The 3×3 stencil's first moment along x is zero: node `k` at column `k % 3`, the particle at `fx`. -/
theorem sum_quadratic2_moment_x (fx fy : ℚ) :
    ∑ k : Fin (3 * 3), quadratic2 fx fy k * ((k.modNat : ℚ) - fx) = 0 := by
  have := sum_tensor_mul_modNat (quadratic fx) (quadratic fy) fun i => (i : ℚ) - fx
  rw [sum_quadratic_moment, zero_mul] at this
  exact this

/-- And along y: node `k` at row `k / 3`, the particle at `fy`. -/
theorem sum_quadratic2_moment_y (fx fy : ℚ) :
    ∑ k : Fin (3 * 3), quadratic2 fx fy k * ((k.divNat : ℚ) - fy) = 0 := by
  have := sum_tensor_mul_divNat (quadratic fx) (quadratic fy) fun j => (j : ℚ) - fy
  rw [sum_quadratic_moment, mul_zero] at this
  exact this

/-- The centre always has mass when the particle does, so it can take the momentum remainder. -/
theorem quadraticShares_center_pos {fx fy : ℚ} (hx₀ : 1 / 2 ≤ fx) (hx₁ : fx ≤ 3 / 2)
    (hy₀ : 1 / 2 ≤ fy) (hy₁ : fy ≤ 3 / 2) {M : ℤ} (hM : 0 < M) : 0 < quadraticShares fx fy M 4 := by
  obtain ⟨h₀, -, h₄⟩ := quadraticShares_center hx₀ hx₁ hy₀ hy₁ hM.le
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have : (0 : ℚ) < quadraticShares fx fy M 4 := by linarith
  exact_mod_cast this

/-- The particle step's momentum deposit on the 3×3 stencil, along one axis: mass shares from
`quadraticShares`, and momentum shares masked by them with the centre taking the rest of `M·V`. -/
def quadraticMomentum (fx fy : ℚ) (M V : ℤ) (p : Fin 9 → ℚ) : Fin 9 → ℤ :=
  maskedShares (quadraticShares fx fy M) p (M * V) 4

/-- It conserves momentum exactly, the affine and pressure terms included. -/
theorem sum_quadraticMomentum (fx fy : ℚ) (M V : ℤ) (p : Fin 9 → ℚ) :
    ∑ k, quadraticMomentum fx fy M V p k = M * V :=
  sum_maskedShares _ _ _ _

/-- And no node of the stencil holds momentum without mass. -/
theorem quadraticMomentum_eq_zero {fx fy : ℚ} (hx₀ : 1 / 2 ≤ fx) (hx₁ : fx ≤ 3 / 2)
    (hy₀ : 1 / 2 ≤ fy) (hy₁ : fy ≤ 3 / 2) {M V : ℤ} (hM : 0 ≤ M) (p : Fin 9 → ℚ) (k : Fin 9)
    (h : quadraticShares fx fy M k = 0) : quadraticMomentum fx fy M V p k = 0 := by
  by_cases hk : k = 4
  · subst hk
    rcases hM.lt_or_eq with hM | hM
    · exact absurd h (quadraticShares_center_pos hx₀ hx₁ hy₀ hy₁ hM).ne'
    · subst hM
      have hz : ∀ j, quadraticShares fx fy 0 j = 0 := fun j =>
        (sum_eq_zero_iff_of_nonneg fun i _ => quadraticShares_nonneg hx₀ hx₁ hy₀ hy₁ le_rfl i).mp
          (sum_quadraticShares fx fy 0) j (mem_univ j)
      unfold quadraticMomentum maskedShares
      simp [hz]
  · exact maskedShares_eq_zero _ _ _ hk h

end Scatter
