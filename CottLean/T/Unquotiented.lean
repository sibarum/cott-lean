import CottLean.T.Readings
import CottLean.T.Quadratic

/-!
# Unquotiented pairs: the readings that need no π

A pair of reals `(p, q)`, not yet divided by anything, is read as

```
C(p,q) = q + i·p        the complex number      (on the integers, `toC`)
D(p,q) = q − p          the difference
S(p,q) = p + q          the sum
Q(p,q) = p / q          the ratio
P(p,q) = p · q          the product
```

The logarithm `L` is in `LogPair`: a pair of a scale, in any base, and a turn. The angle in radians, and
every relation that needs π or Euler's formula, is in `Radians`, the bridge to classical trigonometry.
Nothing stated in this file mentions π.

All the relations come from one fact: `(S, D)` is the pair `⊗ T(1,1)`, traction's `1`, an eighth of a
turn scaled by `√2` (`pairOtimes_one`). As points, `C(S, D) = (1 + i)·C` and `D + iS = (1 + i)·C`
(`C_sum_diff`, `sum_diff_eq`).

* **Exact.** `C = ((1 − i)/2)(D + iS)` (`C_eq`), `C² = SD + 2iP` (`C_sq`), `P = (S² − D²)/4` (`P_eq`),
  `Q(eᵖ, e^q) = e^(−D)` and `P(eᵖ, e^q) = e^S` (`Q_exp`, `P_exp`), and for `p, q > 0`,
  `D(log p, log q) = −log Q` and `S(log p, log q) = log P` (`D_log`, `S_log`). `LogPair` has these in
  any base.
* **Direction only.** `D/S = (1 − Q)/(1 + Q)` needs `q ≠ 0` (`DS_eq_Q`, `DS_eq_Q_fails`). The direction
  is a line, not a ray: `Q` and `D/S` do not change when the pair is scaled by any `t ≠ 0`, `t = −1`
  among them (`Q_smul`, `DS_smul`).

## Each reading has its own embedding

```
C(0, n)  = n      embC    + → ⊕,  × → ⊗          (complexInt on ℤ)
L(0, eⁿ) = n      embL    + → ⊗ and *,  × fails  (read in radians, `Radians.Lrad_embL`)
D(0, n)  = n      embD    + → ⊕,  × → ⊚           (the same pair as embC)
S(n, 0)  = n      embS    + → ⊕,  × → ⊚ fails
Q(n, 1)  = n      embQ    + → fraction +,  × → *  (ratioInt on ℤ)
P(1, n)  = n      embP    × → *,  + → ⊕ fails
```

Each is a section of its reading (`C_embC`, …, `P_embP`). `⊚` makes `D` and `S` multiplicative
(`D_pairSplit`, `S_pairSplit`), and `D`'s embedding is `C`'s, so it carries `×` to `⊚` (`embD_mul`). `S`'s
own embedding does not, and the `q`-axis repairs it: `(0, n)` is a section of `C`, `S` and `D` at once, and
there `⊚` and `⊗` agree (`embC_mul_split`, `S_embC`, `D_embC`). `(n, 1)` is also a section of `P`
(`P_embQ`), and it is the only embedding with a true quotient that carries `×` to `*` (`embQ_unique`).
Under `x / 0 = 0` it is not: `n ↦ (n³, n²)` also works (`embQ_unique_fails`).
-/

namespace T.Unquotiented

open Complex

/-- The complex reading `q + i·p`. -/
def C (p q : ℝ) : ℂ := ⟨q, p⟩
/-- The difference reading `q − p`, the sign `⊚` multiplies. -/
def D (p q : ℝ) : ℝ := q - p
/-- The sum reading `p + q`. -/
def S (p q : ℝ) : ℝ := p + q
/-- The ratio reading `p / q`. -/
noncomputable def Q (p q : ℝ) : ℝ := p / q
/-- The product reading `p · q`. -/
def P (p q : ℝ) : ℝ := p * q

@[simp] theorem C_re (p q : ℝ) : (C p q).re = q := rfl
@[simp] theorem C_im (p q : ℝ) : (C p q).im = p := rfl

theorem C_eq_zero_iff (p q : ℝ) : C p q = 0 ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro h; exact ⟨by simpa using congrArg im h, by simpa using congrArg re h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- On integer pairs the complex reading is `toC`. -/
theorem C_toC (x : T) : C x.p x.q = toC x := rfl

variable (p q : ℝ)

/-! ## Exact relations -/

/-- As a point, `(S, D)` is `C` times `1 + i`. -/
theorem C_sum_diff : C (S p q) (D p q) = (1 + I) * C p q := by
  apply Complex.ext <;> simp [S, D, C]

theorem sum_diff_eq : (D p q + S p q * I : ℂ) = (1 + I) * C p q := by
  apply Complex.ext <;> simp [S, D]

theorem C_eq : C p q = (1 - I) / 2 * (D p q + S p q * I) := by
  apply Complex.ext <;> simp [S, D] <;> ring


theorem C_sq : C p q ^ 2 = S p q * D p q + 2 * I * P p q := by
  apply Complex.ext <;> simp [sq, S, D, P] <;> ring

theorem P_eq : P p q = (S p q ^ 2 - D p q ^ 2) / 4 := by simp only [P, S, D]; ring

theorem Q_exp : Q (Real.exp p) (Real.exp q) = Real.exp (-D p q) := by
  rw [D, neg_sub]; exact (Real.exp_sub p q).symm

theorem P_exp : P (Real.exp p) (Real.exp q) = Real.exp (S p q) := (Real.exp_add p q).symm

theorem D_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    D (Real.log p) (Real.log q) = -Real.log (Q p q) := by
  rw [Q, Real.log_div hp.ne' hq.ne', D, neg_sub]

theorem S_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    S (Real.log p) (Real.log q) = Real.log (P p q) := (Real.log_mul hp.ne' hq.ne').symm

theorem DS_eq_Q {p q : ℝ} (hq : q ≠ 0) : D p q / S p q = (1 - Q p q) / (1 + Q p q) := by
  have h1 : 1 - Q p q = D p q / q := by simp only [Q, D]; field_simp
  have h2 : 1 + Q p q = S p q / q := by simp only [Q, S]; field_simp; ring
  rw [h1, h2, div_div_div_cancel_right₀ hq]

/-- On the vertical axis the ratio form gives `1` where `D/S` is `−1`. -/
theorem DS_eq_Q_fails : D 1 0 / S 1 0 ≠ (1 - Q 1 0) / (1 + Q 1 0) := by
  norm_num [D, S, Q]

/-- Scaling by any `t ≠ 0`, the half-turn `t = −1` included, keeps the ratio. -/
theorem Q_smul {t : ℝ} (ht : t ≠ 0) : Q (t * p) (t * q) = Q p q := by
  simp only [Q]; exact mul_div_mul_left p q ht

theorem DS_smul {t : ℝ} (ht : t ≠ 0) : D (t * p) (t * q) / S (t * p) (t * q) = D p q / S p q := by
  simp only [D, S, ← mul_sub, ← mul_add]; exact mul_div_mul_left _ _ ht

/-! ## Embeddings: a pair for each reading

Each reading has its own way to put a number `n` on a pair, a section `R (emb n) = n`. Pairs are
`ℝ × ℝ`, with `x.1 = p` and `x.2 = q`, and the operations on them are the real versions of `T`'s
(`toPair_oplus`, `toPair_otimes`, `toPair_splitTimes`, `toPair_times`, `toPair_plus`). -/

/-- `⊗`, the product of the points `q + i·p`. -/
def pairOtimes (x y : ℝ × ℝ) : ℝ × ℝ := (x.1 * y.2 + y.1 * x.2, x.2 * y.2 - x.1 * y.1)
/-- `⊚`, the split-complex product, with unit `(0, 1)`. -/
def pairSplit (x y : ℝ × ℝ) : ℝ × ℝ := (x.1 * y.2 + y.1 * x.2, x.2 * y.2 + x.1 * y.1)
/-- `*`, coordinatewise. -/
def pairTimes (x y : ℝ × ℝ) : ℝ × ℝ := (x.1 * y.1, x.2 * y.2)
/-- `+`, the sum of fractions. -/
def pairPlus (x y : ℝ × ℝ) : ℝ × ℝ := (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

/-- An integer pair as a real one. -/
def toPair (x : T) : ℝ × ℝ := (x.p, x.q)

/-- `(S, D)` is the pair `⊗ T(1,1)`, traction's `1`: an eighth of a turn, scaled by `√2`. -/
theorem pairOtimes_one (p q : ℝ) : pairOtimes (p, q) (1, 1) = (S p q, D p q) := by
  ext <;> simp [pairOtimes, S, D]

theorem toPair_oplus (x y : T) : toPair (x ⊕ y) = toPair x + toPair y := by
  ext <;> simp [toPair, oplus]
theorem toPair_otimes (x y : T) : toPair (x ⊗ y) = pairOtimes (toPair x) (toPair y) := by
  ext <;> simp [toPair, pairOtimes, otimes]
theorem toPair_splitTimes (x y : T) : toPair (x ⊚ y) = pairSplit (toPair x) (toPair y) := by
  ext <;> simp [toPair, pairSplit, splitTimes, qtimes]
theorem toPair_times (x y : T) : toPair (x * y) = pairTimes (toPair x) (toPair y) := by
  ext <;> simp [toPair, pairTimes, show x * y = times x y from rfl, times]
theorem toPair_plus (x y : T) : toPair (x + y) = pairPlus (toPair x) (toPair y) := by
  ext <;> simp [toPair, pairPlus, show x + y = plus x y from rfl, plus]

/-- `C`: `n ↦ (0, n)`, the point `n + 0·i`. -/
def embC (n : ℝ) : ℝ × ℝ := (0, n)
/-- `L`: `n ↦ (0, eⁿ)`, the point whose logarithm is `n`. -/
noncomputable def embL (n : ℝ) : ℝ × ℝ := (0, Real.exp n)
/-- `D`: `n ↦ (0, n)`, since `n − 0 = n`. The same pair as `embC`. -/
def embD (n : ℝ) : ℝ × ℝ := (0, n)
/-- `S`: `n ↦ (n, 0)`. -/
def embS (n : ℝ) : ℝ × ℝ := (n, 0)
/-- `Q`: `n ↦ (n, 1)`, the ratio `n/1`. -/
def embQ (n : ℝ) : ℝ × ℝ := (n, 1)
/-- `P`: `n ↦ (1, n)`. -/
def embP (n : ℝ) : ℝ × ℝ := (1, n)

/-! ### Each is a section of its reading -/

theorem C_embC (n : ℝ) : C (embC n).1 (embC n).2 = n := by apply Complex.ext <;> simp [embC]
theorem D_embD (n : ℝ) : D (embD n).1 (embD n).2 = n := by simp [D, embD]
theorem S_embS (n : ℝ) : S (embS n).1 (embS n).2 = n := by simp [S, embS]
theorem Q_embQ (n : ℝ) : Q (embQ n).1 (embQ n).2 = n := by simp [Q, embQ]
theorem P_embP (n : ℝ) : P (embP n).1 (embP n).2 = n := by simp [P, embP]

/-- On the integers, `C`'s embedding is the complex reading's copy of ℤ. -/
theorem embC_complexInt (n : ℤ) : embC n = toPair (complexInt n) := by
  simp [embC, toPair, complexInt]
/-- On the integers, `Q`'s embedding is the ratio reading's copy of ℤ. -/
theorem embQ_ratioInt (n : ℤ) : embQ n = toPair (ratioInt n) := by
  simp [embQ, toPair, ratioInt]

/-! ### What each carries -/

theorem embC_add (m n : ℝ) : embC (m + n) = embC m + embC n := by ext <;> simp [embC]
theorem embC_mul (m n : ℝ) : embC (m * n) = pairOtimes (embC m) (embC n) := by
  ext <;> simp [embC, pairOtimes]

/-- `L`'s embedding carries `+` to `⊗`, and to `*`. -/
theorem embL_add (m n : ℝ) : embL (m + n) = pairOtimes (embL m) (embL n) := by
  ext <;> simp [embL, pairOtimes, Real.exp_add]
theorem embL_add_times (m n : ℝ) : embL (m + n) = pairTimes (embL m) (embL n) := by
  ext <;> simp [embL, pairTimes, Real.exp_add]
/-- It does not carry `×`: `e^(1·1) ≠ e·e`. -/
theorem embL_mul_fails : embL (1 * 1) ≠ pairOtimes (embL 1) (embL 1) := by
  intro h
  have h2 := congrArg Prod.snd h
  simp only [embL, pairOtimes, mul_one, mul_zero, sub_zero, ← Real.exp_add] at h2
  have := Real.exp_injective h2
  norm_num at this

theorem embD_add (m n : ℝ) : embD (m + n) = embD m + embD n := by ext <;> simp [embD]
/-- `⊚` makes `D` multiplicative. -/
theorem D_pairSplit (x y : ℝ × ℝ) :
    D (pairSplit x y).1 (pairSplit x y).2 = D x.1 x.2 * D y.1 y.2 := by
  simp only [D, pairSplit]; ring
theorem S_pairSplit (x y : ℝ × ℝ) :
    S (pairSplit x y).1 (pairSplit x y).2 = S x.1 x.2 * S y.1 y.2 := by
  simp only [S, pairSplit]; ring
/-- So `D`'s embedding carries `×` to `⊚`. -/
theorem embD_mul (m n : ℝ) : embD (m * n) = pairSplit (embD m) (embD n) := by
  ext <;> simp [embD, pairSplit]

theorem embS_add (m n : ℝ) : embS (m + n) = embS m + embS n := by ext <;> simp [embS]
/-- `S`'s embedding does not carry `×` to `⊚`: `(1, 0) ⊚ (1, 0) = (0, 1)`. -/
theorem embS_mul_fails : embS (1 * 1) ≠ pairSplit (embS 1) (embS 1) := by
  simp [embS, pairSplit]

/-- On the `q`-axis, `⊚` and `⊗` agree, and `C`'s embedding is a section of `S` and of `D`.
So `(0, n)` serves `C`, `S` and `D` at once, carrying `+` and `×`. -/
theorem embC_mul_split (m n : ℝ) : embC (m * n) = pairSplit (embC m) (embC n) := by
  ext <;> simp [embC, pairSplit]
theorem S_embC (n : ℝ) : S (embC n).1 (embC n).2 = n := by simp [S, embC]
theorem D_embC (n : ℝ) : D (embC n).1 (embC n).2 = n := by simp [D, embC]
theorem embD_eq_embC : embD = embC := rfl

theorem embQ_add (m n : ℝ) : embQ (m + n) = pairPlus (embQ m) (embQ n) := by
  ext <;> simp [embQ, pairPlus]
theorem embQ_mul (m n : ℝ) : embQ (m * n) = pairTimes (embQ m) (embQ n) := by
  ext <;> simp [embQ, pairTimes]
/-- `⊕` takes `Q`'s embedding to the mean: `(1, 1) ⊕ (1, 1) = (2, 2)`. -/
theorem embQ_oplus_fails : embQ (1 + 1) ≠ embQ 1 + embQ 1 := by
  simp [embQ]

/-- `(n, 1)` is the only embedding with a true quotient that carries `×` to `*`. -/
theorem embQ_unique (X : ℝ → ℝ × ℝ) (hq : ∀ n, (X n).2 ≠ 0) (hQ : ∀ n, Q (X n).1 (X n).2 = n)
    (hmul : ∀ m n, X (m * n) = pairTimes (X m) (X n)) : X = embQ := by
  funext n
  have h1 : (X n).2 = 1 := by
    have h := congrArg Prod.snd (hmul 0 n)
    simp only [zero_mul, pairTimes] at h
    have := hq 0
    field_simp at h
    exact h.symm
  have h2 := hQ n
  simp only [Q, h1, div_one] at h2
  exact Prod.ext h2 h1

/-- Under `x / 0 = 0` the uniqueness fails: `n ↦ (n³, n²)` also reads `n` and carries `×` to `*`. -/
theorem embQ_unique_fails :
    ∃ X : ℝ → ℝ × ℝ, (∀ n, Q (X n).1 (X n).2 = n) ∧
      (∀ m n, X (m * n) = pairTimes (X m) (X n)) ∧ X ≠ embQ := by
  refine ⟨fun n => (n ^ 3, n ^ 2), fun n => ?_, fun m n => ?_, fun h => ?_⟩
  · by_cases hn : n = 0
    · simp [Q, hn]
    · simp only [Q]; field_simp
  · ext <;> simp [pairTimes] <;> ring
  · have := congrArg (fun X => (X 0).2) h
    simp [embQ] at this

theorem embP_mul (m n : ℝ) : embP (m * n) = pairTimes (embP m) (embP n) := by
  ext <;> simp [embP, pairTimes]
/-- `P`'s embedding does not carry `+` to `⊕`: `(1, 1) ⊕ (1, 1) = (2, 2)`, not `(1, 2)`. -/
theorem embP_add_fails : embP (1 + 1) ≠ embP 1 + embP 1 := by
  simp [embP]
/-- `Q`'s embedding is also a section of `P`, so `(n, 1)` serves both multiplicative readings. -/
theorem P_embQ (n : ℝ) : P (embQ n).1 (embQ n).2 = n := by simp [P, embQ]


/-! ## Scaling, and the product of the points -/

theorem C_smul (t : ℝ) : C (t * p) (t * q) = (t : ℂ) * C p q := by
  apply Complex.ext <;> simp [C]

theorem C_pairOtimes (x y : ℝ × ℝ) :
    C (pairOtimes x y).1 (pairOtimes x y).2 = C x.1 x.2 * C y.1 y.2 := by
  apply Complex.ext <;> simp [C, pairOtimes]
  ring


end T.Unquotiented
