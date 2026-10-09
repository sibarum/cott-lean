import CottLean.T.PairAlgebras
import CottLean.T.LogPair

/-!
# Coherence and interference of the embeddings

Each reading has its own embedding (`Unquotiented`): a way of writing the number `n` as a pair that the
reading reads back as `n`. An embedding is **coherent** with a reading when that reading, too, gives `n`
back. The same `n` embedded two ways is two different pairs. Combined, they can reinforce under one
reading and cancel under another, and that is their **interference**.

## The linear readings: a phase for each embedding

`C`, `S` and `D` are linear, so an embedding along a line, `n ↦ n·v`, is read as `n` times one constant,
`R v` (`C_lin`, `S_lin`, `D_lin`). That constant is the embedding's phase under `R`, and coherence is phase
`1`. `C`'s embedding is the line `(0, 1)` and `S`'s is `(1, 0)`. Against `C`'s, `S`'s embedding reads

```
S(n, 0) =  n     in phase              (no turn)
D(n, 0) = −n     in antiphase          (half a turn)
C(n, 0) =  n·i   in quadrature         (a quarter turn)
```

(`S_embS`, `D_embS`, `C_embS`). Under `⊕` the readings superpose (`C_superpose`, `S_superpose`,
`D_superpose`). So `embC n ⊕ embS n = (n, n)` reads `S = 2n`, all reinforcement, and `D = 0`, all
cancellation (`interfere_embC_embS`).

## Coherence is decided by the readings, and fixes the line

* `C` alone decides it: the only line coherent with `C` is `(0, 1)` (`coherent_C_iff`).
* `S` and `D` together decide it as well: the only line coherent with both is `(0, 1)`, the same one
  (`coherent_S_D_iff`). So a line is coherent with `C` exactly when it is coherent with `S` and `D`.
* One of `S` or `D` alone does not. Two lines coherent with the same one of them differ by a pair that
  reading reads as `0` (`S_sub_of_coherent`, `D_sub_of_coherent`). Such a pair is exactly one on a light
  line, a zero divisor of `⊚` (`S_eq_zero_iff`, `D_eq_zero_iff`).

So interference has one null set for each of `S` and `D`. Their total cancellation happens exactly on the
light lines, `p = −q` for `S` and `p = q` for `D`: the lines where `⊚`, the product that `S` and `D`
multiply, has its zero divisors.

## The multiplicative readings: the same picture in exponents

`Q` and `P` are multiplicative, and for `n > 0` the family `n ↦ (n^α, n^β)` plays the part of the lines.
`Q` reads `n^(α − β)` and `P` reads `n^(α + β)` (`Q_powEmb`, `P_powEmb`), which are `D` and `S` of the
exponents with `D`'s sign turned. The only member coherent with both is `(n, 1)`, `Q`'s own embedding
(`coherent_Q_P_iff`), just as `(0, 1)` was for `S` and `D`. `P`'s embedding is in antiphase under `Q`,
`Q(1, n) = n⁻¹` (`Q_embP`). The two interfere on the same diagonal:
`embQ n * embP n = (n, n) = embC n ⊕ embS n` (`interfere_embQ_embP`, `diagonal_meet`). There `Q` reads `1`,
all cancellation, and `P` reads `n²`.

So the additive and the multiplicative interference cancel on one pair `(n, n)`: an eighth of a turn, a
zero divisor of `⊚`, read `0` by `D` and `1` by `Q`.

## The logarithm's embedding

`embL n = (0, eⁿ)` is coherent with `L` in base `e²`: the scale is `log N = 2n` over `log e² = 2`, and the
turn is `0` (`L_embL`). Base `e²` is the one where the logarithm of a squared norm is the logarithm of
the norm. In base `e` it reads `2n` (`L_e_embL`).
-/

namespace T.Unquotiented

open Complex

/-! ## Lines and their phases -/

/-- The embedding along the line through `v`: `n ↦ n·v`. -/
def lin (v : ℝ × ℝ) (n : ℝ) : ℝ × ℝ := n • v

theorem embC_eq_lin : embC = lin (0, 1) := by funext n; ext <;> simp [embC, lin]
theorem embS_eq_lin : embS = lin (1, 0) := by funext n; ext <;> simp [embS, lin]

theorem C_lin (v : ℝ × ℝ) (n : ℝ) : C (lin v n).1 (lin v n).2 = n * C v.1 v.2 := by
  apply Complex.ext <;> simp [lin, C]
theorem S_lin (v : ℝ × ℝ) (n : ℝ) : S (lin v n).1 (lin v n).2 = n * S v.1 v.2 := by
  simp [lin, S]; ring
theorem D_lin (v : ℝ × ℝ) (n : ℝ) : D (lin v n).1 (lin v n).2 = n * D v.1 v.2 := by
  simp [lin, D]; ring

/-- `S`'s embedding under `D`: in antiphase. -/
theorem D_embS (n : ℝ) : D (embS n).1 (embS n).2 = -n := by simp [D, embS]
/-- `S`'s embedding under `C`: in quadrature. -/
theorem C_embS (n : ℝ) : C (embS n).1 (embS n).2 = n * I := by
  apply Complex.ext <;> simp [C, embS]

/-! ## Superposition -/

theorem C_superpose (u v : ℝ × ℝ) (m n : ℝ) :
    C (lin u m + lin v n).1 (lin u m + lin v n).2 = m * C u.1 u.2 + n * C v.1 v.2 := by
  apply Complex.ext <;> simp [lin, C]
theorem S_superpose (u v : ℝ × ℝ) (m n : ℝ) :
    S (lin u m + lin v n).1 (lin u m + lin v n).2 = m * S u.1 u.2 + n * S v.1 v.2 := by
  simp [lin, S]; ring
theorem D_superpose (u v : ℝ × ℝ) (m n : ℝ) :
    D (lin u m + lin v n).1 (lin u m + lin v n).2 = m * D u.1 u.2 + n * D v.1 v.2 := by
  simp [lin, D]; ring

/-- `C`'s and `S`'s embeddings of the same `n`: `S` reinforces, `D` cancels, `C` reads them a quarter
turn apart. -/
theorem interfere_embC_embS (n : ℝ) :
    embC n + embS n = (n, n) ∧ S (embC n + embS n).1 (embC n + embS n).2 = 2 * n ∧
      D (embC n + embS n).1 (embC n + embS n).2 = 0 ∧
      C (embC n + embS n).1 (embC n + embS n).2 = n * (1 + I) := by
  refine ⟨by ext <;> simp [embC, embS], by simp [S, embC, embS]; ring, by simp [D, embC, embS], ?_⟩
  apply Complex.ext <;> simp [C, embC, embS]

/-! ## Coherence fixes the line -/

/-- The only line coherent with `C` is `(0, 1)`. -/
theorem coherent_C_iff (v : ℝ × ℝ) : (∀ n, C (lin v n).1 (lin v n).2 = n) ↔ v = (0, 1) := by
  constructor
  · intro h
    have h1 := h 1
    rw [C_lin, Complex.ofReal_one, one_mul] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp only [C_re, C_im, Complex.one_re, Complex.one_im] at hre him
    exact Prod.ext him hre
  · rintro rfl n; rw [← embC_eq_lin]; exact C_embC n

/-- The only line coherent with both `S` and `D` is `(0, 1)`, `C`'s. -/
theorem coherent_S_D_iff (v : ℝ × ℝ) :
    ((∀ n, S (lin v n).1 (lin v n).2 = n) ∧ ∀ n, D (lin v n).1 (lin v n).2 = n) ↔ v = (0, 1) := by
  constructor
  · rintro ⟨hS, hD⟩
    have h1 := hS 1
    have h2 := hD 1
    rw [S_lin, one_mul, S] at h1
    rw [D_lin, one_mul, D] at h2
    exact Prod.ext (by linarith) (by linarith)
  · rintro rfl
    exact ⟨fun n => by rw [← embC_eq_lin]; exact S_embC n, fun n => by rw [← embC_eq_lin]; exact D_embC n⟩

/-- So a line is coherent with `C` exactly when it is coherent with `S` and `D`. -/
theorem coherent_C_iff_S_D (v : ℝ × ℝ) :
    (∀ n, C (lin v n).1 (lin v n).2 = n) ↔
      (∀ n, S (lin v n).1 (lin v n).2 = n) ∧ ∀ n, D (lin v n).1 (lin v n).2 = n := by
  rw [coherent_C_iff, coherent_S_D_iff]

/-! ## The null sets are the light lines -/

/-- `S` reads `0` exactly on the light line `p = −q`, where `⊚ (1, 1)` vanishes. -/
theorem S_eq_zero_iff (x : ℝ × ℝ) : S x.1 x.2 = 0 ↔ pairSplit x (1, 1) = 0 := by
  simp only [S, pairSplit, mul_one, one_mul, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  constructor
  · intro h; constructor <;> linarith
  · intro h; linarith [h.1]

/-- `D` reads `0` exactly on the light line `p = q`, where `⊚ (−1, 1)` vanishes. -/
theorem D_eq_zero_iff (x : ℝ × ℝ) : D x.1 x.2 = 0 ↔ pairSplit x (-1, 1) = 0 := by
  simp only [D, pairSplit, mul_one, mul_neg, neg_mul, one_mul, Prod.ext_iff, Prod.fst_zero,
    Prod.snd_zero]
  constructor
  · intro h; constructor <;> linarith
  · intro h; linarith [h.2]

/-- Two lines coherent with `S` differ, at every `n`, by a pair on `S`'s light line. -/
theorem S_sub_of_coherent {u v : ℝ × ℝ} (hu : S u.1 u.2 = 1) (hv : S v.1 v.2 = 1) (n : ℝ) :
    pairSplit (lin u n - lin v n) (1, 1) = 0 := by
  rw [← S_eq_zero_iff]
  simp only [lin, S] at hu hv ⊢
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination n * hu - n * hv

/-- Two lines coherent with `D` differ, at every `n`, by a pair on `D`'s light line. -/
theorem D_sub_of_coherent {u v : ℝ × ℝ} (hu : D u.1 u.2 = 1) (hv : D v.1 v.2 = 1) (n : ℝ) :
    pairSplit (lin u n - lin v n) (-1, 1) = 0 := by
  rw [← D_eq_zero_iff]
  simp only [lin, D] at hu hv ⊢
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination n * hu - n * hv

/-! ## The multiplicative readings -/

/-- `P`'s embedding under `Q`: in antiphase, `n⁻¹`. -/
theorem Q_embP (n : ℝ) : Q (embP n).1 (embP n).2 = n⁻¹ := by simp [Q, embP]

/-- The exponent family `n ↦ (n^α, n^β)`, for `n > 0`. -/
noncomputable def powEmb (α β n : ℝ) : ℝ × ℝ := (n ^ α, n ^ β)

theorem embQ_eq_powEmb (n : ℝ) : embQ n = powEmb 1 0 n := by
  simp [embQ, powEmb]

theorem Q_powEmb (α β : ℝ) {n : ℝ} (hn : 0 < n) : Q (powEmb α β n).1 (powEmb α β n).2 = n ^ (α - β) := by
  simp only [Q, powEmb]; rw [Real.rpow_sub hn]
theorem P_powEmb (α β : ℝ) {n : ℝ} (hn : 0 < n) : P (powEmb α β n).1 (powEmb α β n).2 = n ^ (α + β) := by
  simp only [P, powEmb]; rw [Real.rpow_add hn]

private theorem exponent_eq_one {c : ℝ} (h : (2 : ℝ) ^ c = 2) : c = 1 := by
  have := congrArg Real.log h
  rw [Real.log_rpow (by norm_num)] at this
  have h2 : Real.log 2 ≠ 0 := by positivity
  field_simp at this
  linarith

/-- The only member of the family coherent with both `Q` and `P` is `(n, 1)`, `Q`'s own embedding. -/
theorem coherent_Q_P_iff (α β : ℝ) :
    ((∀ n, 0 < n → Q (powEmb α β n).1 (powEmb α β n).2 = n) ∧
      ∀ n, 0 < n → P (powEmb α β n).1 (powEmb α β n).2 = n) ↔ α = 1 ∧ β = 0 := by
  constructor
  · rintro ⟨hQ, hP⟩
    have h1 := hQ 2 two_pos
    have h2 := hP 2 two_pos
    rw [Q_powEmb _ _ two_pos] at h1
    rw [P_powEmb _ _ two_pos] at h2
    have e1 := exponent_eq_one h1
    have e2 := exponent_eq_one h2
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    exact ⟨fun n hn => by rw [Q_powEmb _ _ hn]; norm_num, fun n hn => by rw [P_powEmb _ _ hn]; norm_num⟩

/-- `Q`'s and `P`'s embeddings of the same `n` under `*`: `Q` cancels to `1`, `P` reinforces to `n²`. -/
theorem interfere_embQ_embP {n : ℝ} (hn : n ≠ 0) :
    pairTimes (embQ n) (embP n) = (n, n) ∧
      Q (pairTimes (embQ n) (embP n)).1 (pairTimes (embQ n) (embP n)).2 = 1 ∧
      P (pairTimes (embQ n) (embP n)).1 (pairTimes (embQ n) (embP n)).2 = n ^ 2 := by
  refine ⟨by ext <;> simp [pairTimes, embQ, embP], by simp [Q, pairTimes, embQ, embP, hn], ?_⟩
  simp [P, pairTimes, embQ, embP]; ring

/-- The additive and the multiplicative interference meet on one pair, `(n, n)`. -/
theorem diagonal_meet (n : ℝ) : embC n + embS n = pairTimes (embQ n) (embP n) := by
  ext <;> simp [embC, embS, pairTimes, embQ, embP]

/-! ## The logarithm's embedding -/

private theorem turn_embL (n : ℝ) : turn (embL n).1 (embL n).2 = 0 := by
  have : C (embL n).1 (embL n).2 = ((Real.exp n : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [C, embL, Complex.exp_ofReal_re]
  rw [turn, this, Complex.arg_ofReal_of_nonneg (Real.exp_pos n).le, zero_div]

private theorem log_N_embL (n : ℝ) : Real.log (N (embL n).1 (embL n).2) = 2 * n := by
  simp only [N, embL]
  rw [show (0 : ℝ) ^ 2 + Real.exp n ^ 2 = Real.exp (2 * n) by
    rw [zero_pow two_ne_zero, zero_add, ← Real.exp_nat_mul]; norm_num]
  exact Real.log_exp _

/-- `L`'s embedding is coherent with `L` in base `e²`. -/
theorem L_embL (n : ℝ) : L (Real.exp 2) (embL n).1 (embL n).2 = (n, 0) := by
  refine Prod.ext ?_ (turn_embL n)
  show Real.logb _ _ = n
  rw [Real.logb, log_N_embL, Real.log_exp]; ring

/-- In base `e` it reads `2n`: the logarithm of the squared norm. -/
theorem L_e_embL (n : ℝ) : L (Real.exp 1) (embL n).1 (embL n).2 = (2 * n, 0) := by
  refine Prod.ext ?_ (turn_embL n)
  show Real.logb _ _ = 2 * n
  rw [Real.logb, log_N_embL, Real.log_exp, div_one]

end T.Unquotiented
