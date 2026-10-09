import CottLean.T.Coherence

/-!
# Interference between the additive and the multiplicative embeddings

`Coherence` compares embeddings within one family. Here the two families meet: the additive embeddings
`embC n = (0, n)` and `embS n = (n, 0)`, and the multiplicative ones `embQ n = (n, 1)`, `embP n = (1, n)`
and `embL n = (0, eⁿ)`.

## Each multiplicative embedding is an additive one, displaced by the other's `1`

```
embQ n = embS n ⊕ embC 1        embP n = embC n ⊕ embS 1
```

(`embQ_eq_add`, `embP_eq_add`). So a linear reading sees a multiplicative embedding as its additive part
plus a constant bias, the reading of the other additive embedding's `1`:

| | `S` | `D` | `C` |
|---|---|---|---|
| `embQ n` | `n + 1` | `1 − n` | `1 + n·i` |
| `embP n` | `n + 1` | `n − 1` | `n + i` |

(`S_embQ`, `D_embQ`, `C_embQ`, `S_embP`, `D_embP`, `C_embP`). The other way, the multiplicative readings
annihilate the additive embeddings: `P` is `0` on both axes, which are exactly its null set
(`P_embC`, `P_embS`, `P_eq_zero_iff`), and `Q(0, n) = 0` (`Q_embC`).

## Where they mix without interference

* **Translation.** `⊕` with an additive embedding moves along a multiplicative one:
  `embS m ⊕ embQ n = embQ (m + n)` and `embC m ⊕ embP n = embP (m + n)` (`embS_add_embQ`, `embC_add_embP`).
  `embS` is the additive direction of `embQ`, and `embC` of `embP`.
* **Scaling.** `*` with a multiplicative embedding multiplies an additive one, or leaves it alone:
  `embS m * embQ n = embS (m·n)`, `embC m * embP n = embC (m·n)`, `embC m * embQ n = embC m`,
  `embS m * embP n = embS m` (`embS_times_embQ`, `embC_times_embP`, `embC_times_embQ`, `embS_times_embP`).

## Where they interfere, and by how much

Crossed, `embC m ⊕ embQ n = (n, 1 + m)`. `Q` reads `n / (1 + m)` and `P` reads `n·(1 + m)`
(`embC_add_embQ`): the additive `m` enters the multiplicative readings as the factor `1 + m`, the bias plus
`m`. At `m = −1` it cancels the bias completely, and the pair falls onto `S`'s axis:
`embC (−1) ⊕ embQ n = embS n` (`embC_neg_one_add_embQ`). `embS m ⊕ embP n` is the mirror image
(`embS_add_embP`).

The measure. In the exponents, where `P`'s `×` is `+` (`P_exp`), a coherent additive `m` would add `m`.
It adds `log (1 + m)` instead (`log_P_embC_add_embQ`). The interference is the gap

```
δ(m) = m − log(1 + m),        0 ≤ δ(m) ≤ m² / (1 + m)   for m > −1
```

(`interference_nonneg`, `interference_le`), and `δ(m) = 0` only at `m = 0` (`interference_eq_zero_iff`).
So it vanishes to first order and grows as `m²`: small additive perturbations are nearly coherent with
the multiplicative reading, and the bound blows up only as `m` approaches `−1`, the total cancellation.

## The logarithm: the sign becomes a turn

`embC m ⊗ embL n = (0, m·eⁿ)`. In base `e²`, where `embL` is coherent (`L_embL`), it reads
`(n + log |m|, 0)` for `m > 0` and `(n + log |m|, 1/2)` for `m < 0` (`L_embC_otimes_embL_pos`,
`L_embC_otimes_embL_neg`): the magnitude of the additive embedding becomes a shift of the scale, and its
sign becomes half a turn.
-/

namespace T.Unquotiented

open Complex
open scoped Real

/-! ## Each multiplicative embedding is an additive one, displaced -/

theorem embQ_eq_add (n : ℝ) : embQ n = embS n + embC 1 := by ext <;> simp [embQ, embS, embC]
theorem embP_eq_add (n : ℝ) : embP n = embC n + embS 1 := by ext <;> simp [embP, embS, embC]

theorem S_embQ (n : ℝ) : S (embQ n).1 (embQ n).2 = n + 1 := by simp [S, embQ]
theorem D_embQ (n : ℝ) : D (embQ n).1 (embQ n).2 = 1 - n := by simp [D, embQ]
theorem C_embQ (n : ℝ) : C (embQ n).1 (embQ n).2 = 1 + n * I := by
  apply Complex.ext <;> simp [C, embQ]
theorem S_embP (n : ℝ) : S (embP n).1 (embP n).2 = n + 1 := by simp [S, embP]; ring
theorem D_embP (n : ℝ) : D (embP n).1 (embP n).2 = n - 1 := by simp [D, embP]
theorem C_embP (n : ℝ) : C (embP n).1 (embP n).2 = n + I := by
  apply Complex.ext <;> simp [C, embP]

/-- `P` is `0` exactly on the two axes. -/
theorem P_eq_zero_iff (x : ℝ × ℝ) : P x.1 x.2 = 0 ↔ x.1 = 0 ∨ x.2 = 0 := by
  simp [P]
theorem P_embC (n : ℝ) : P (embC n).1 (embC n).2 = 0 := by simp [P, embC]
theorem P_embS (n : ℝ) : P (embS n).1 (embS n).2 = 0 := by simp [P, embS]
theorem Q_embC (n : ℝ) : Q (embC n).1 (embC n).2 = 0 := by simp [Q, embC]

/-! ## Translation and scaling -/

theorem embS_add_embQ (m n : ℝ) : embS m + embQ n = embQ (m + n) := by
  ext <;> simp [embS, embQ]
theorem embC_add_embP (m n : ℝ) : embC m + embP n = embP (m + n) := by
  ext <;> simp [embC, embP]

theorem embS_times_embQ (m n : ℝ) : pairTimes (embS m) (embQ n) = embS (m * n) := by
  ext <;> simp [pairTimes, embS, embQ]
theorem embC_times_embP (m n : ℝ) : pairTimes (embC m) (embP n) = embC (m * n) := by
  ext <;> simp [pairTimes, embC, embP]
theorem embC_times_embQ (m n : ℝ) : pairTimes (embC m) (embQ n) = embC m := by
  ext <;> simp [pairTimes, embC, embQ]
theorem embS_times_embP (m n : ℝ) : pairTimes (embS m) (embP n) = embS m := by
  ext <;> simp [pairTimes, embS, embP]

/-! ## The crossed sums -/

/-- `C`'s `m` enters `Q` and `P` as the factor `1 + m`. -/
theorem embC_add_embQ (m n : ℝ) :
    embC m + embQ n = (n, 1 + m) ∧
      Q (embC m + embQ n).1 (embC m + embQ n).2 = n / (1 + m) ∧
      P (embC m + embQ n).1 (embC m + embQ n).2 = n * (1 + m) := by
  refine ⟨by ext <;> simp [embC, embQ]; ring, ?_, ?_⟩ <;> simp [Q, P, embC, embQ, add_comm]

/-- `S`'s `m` enters them as the factor `1 + m`, on the other side. -/
theorem embS_add_embP (m n : ℝ) :
    embS m + embP n = (1 + m, n) ∧
      Q (embS m + embP n).1 (embS m + embP n).2 = (1 + m) / n ∧
      P (embS m + embP n).1 (embS m + embP n).2 = (1 + m) * n := by
  refine ⟨by ext <;> simp [embS, embP]; ring, ?_, ?_⟩ <;> simp [Q, P, embS, embP, add_comm]

/-- At `m = −1` the bias is cancelled, and the pair falls onto `S`'s axis. -/
theorem embC_neg_one_add_embQ (n : ℝ) : embC (-1) + embQ n = embS n := by
  ext <;> simp [embC, embQ, embS]

/-! ## The measure -/

/-- In the exponents, `C`'s `m` adds `log (1 + m)` to `P`, not `m`. -/
theorem log_P_embC_add_embQ {m n : ℝ} (hm : -1 < m) (hn : 0 < n) :
    Real.log (P (embC m + embQ n).1 (embC m + embQ n).2) = Real.log n + Real.log (1 + m) := by
  rw [(embC_add_embQ m n).2.2, Real.log_mul hn.ne' (by linarith)]

/-- The interference of an additive `m` with a multiplicative reading: `m − log (1 + m)`. -/
noncomputable def interference (m : ℝ) : ℝ := m - Real.log (1 + m)

theorem interference_nonneg {m : ℝ} (hm : -1 < m) : 0 ≤ interference m := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + m by linarith)
  simp only [interference]; linarith

theorem interference_le {m : ℝ} (hm : -1 < m) : interference m ≤ m ^ 2 / (1 + m) := by
  have h1 : 0 < 1 + m := by linarith
  have := Real.one_sub_inv_le_log_of_pos h1
  have e : m ^ 2 / (1 + m) = m - (1 - (1 + m)⁻¹) := by field_simp; ring
  simp only [interference]; rw [e]; linarith

theorem interference_eq_zero_iff {m : ℝ} (hm : -1 < m) : interference m = 0 ↔ m = 0 := by
  constructor
  · intro h
    have h1 : 0 < 1 + m := by linarith
    by_contra hm0
    have hl : Real.log (1 + m) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one h1 (by intro h'; apply hm0; linarith)
    have := Real.add_one_lt_exp hl
    rw [Real.exp_log h1] at this
    simp only [interference] at h; linarith
  · rintro rfl; simp [interference]

/-! ## The logarithm: the sign becomes a turn -/

theorem embC_otimes_embL (m n : ℝ) : pairOtimes (embC m) (embL n) = (0, m * Real.exp n) := by
  ext <;> simp [pairOtimes, embC, embL]

private theorem logScale_axis {x : ℝ} (n : ℝ) (m : ℝ) (hx : x = m * Real.exp n) (hm : m ≠ 0) :
    logScale (Real.exp 2) 0 x = n + Real.log m := by
  subst hx
  simp only [logScale, N, Real.logb, Real.log_exp]
  rw [zero_pow two_ne_zero, zero_add, Real.log_pow, Real.log_mul hm (Real.exp_pos n).ne', Real.log_exp]
  push_cast; ring

theorem L_embC_otimes_embL_pos {m : ℝ} (hm : 0 < m) (n : ℝ) :
    L (Real.exp 2) (pairOtimes (embC m) (embL n)).1 (pairOtimes (embC m) (embL n)).2 =
      (n + Real.log |m|, 0) := by
  rw [embC_otimes_embL, Real.log_abs]
  refine Prod.ext (logScale_axis n m rfl hm.ne') ?_
  show arg (C 0 (m * Real.exp n)) / (2 * π) = 0
  have : C 0 (m * Real.exp n) = ((m * Real.exp n : ℝ) : ℂ) := by apply Complex.ext <;> simp [C, Complex.exp_ofReal_re]
  rw [this, Complex.arg_ofReal_of_nonneg (by positivity), zero_div]

theorem L_embC_otimes_embL_neg {m : ℝ} (hm : m < 0) (n : ℝ) :
    L (Real.exp 2) (pairOtimes (embC m) (embL n)).1 (pairOtimes (embC m) (embL n)).2 =
      (n + Real.log |m|, 1 / 2) := by
  rw [embC_otimes_embL, Real.log_abs]
  refine Prod.ext (logScale_axis n m rfl hm.ne) ?_
  show arg (C 0 (m * Real.exp n)) / (2 * π) = 1 / 2
  have : C 0 (m * Real.exp n) = ((m * Real.exp n : ℝ) : ℂ) := by apply Complex.ext <;> simp [C, Complex.exp_ofReal_re]
  rw [this, Complex.arg_ofReal_of_neg (mul_neg_of_neg_of_pos hm (Real.exp_pos n))]
  field_simp

end T.Unquotiented
