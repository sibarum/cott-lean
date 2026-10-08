import CottLean.T.Readings
import CottLean.T.Quadratic

/-!
# Unquotiented pairs: six readings of one pair

A pair of reals `(p, q)`, not yet divided by anything, read six ways:

```
C(p,q) = q + i·p        the complex number      (on the integers, `toC`)
L(p,q) = log(q + i·p)   its logarithm
D(p,q) = p − q          the difference
S(p,q) = p + q          the sum
Q(p,q) = p / q          the ratio
P(p,q) = p · q          the product
```

All the relations between them come from one fact: `(S, D)` is `C` turned by `−π/4` and scaled by
`√2`, that is `S + iD = (1 − i)·C` (`sum_diff_eq`). Then `exp` and `log` exchange `+` with `*`.

* **Exact.** `C = ((1 + i)/2)(S + iD)` (`C_eq`), `C = e^L` off the origin (`exp_L`), `C² = −SD + 2iP`
  (`C_sq`), `P = (S² − D²)/4` (`P_eq`), `Q(eᵖ, e^q) = e^D` and `P(eᵖ, e^q) = e^S` (`Q_exp`, `P_exp`),
  and for `p, q > 0`, `D(log p, log q) = log Q` and `S(log p, log q) = log P` (`D_log`, `S_log`).
* **The logarithm of the turn holds only on a branch.** `log(S + iD) = L + ½ln 2 − iπ/4` exactly when
  `arg C > −3π/4` (`log_sum_diff_iff`), since otherwise subtracting `π/4` leaves the principal range. It
  fails at `C = −1 − i` (`log_sum_diff_ne`). Under `exp`, so modulo `2πi`, it holds off the origin
  (`exp_log_sum_diff`).
* **Direction only.** `Q = tan(arg C) = tan(Im L)` for every pair, the origin included
  (`Q_eq_tan_arg`, `Q_eq_tan_im_L`). `D/S = tan(arg C − π/4)` off the origin (`DS_eq_tan`), and at the
  origin it fails (`DS_eq_tan_fails`). `D/S = (Q − 1)/(Q + 1)` needs `q ≠ 0` (`DS_eq_Q`,
  `DS_eq_Q_fails`). The direction is a line, not a ray: `Q` and `D/S` do not change when the pair is
  scaled by any `t ≠ 0`, `t = −1` among them (`Q_smul`, `DS_smul`).
* **Scale only.** `S² + D² = 2e^(2 Re L)` off the origin (`scale_eq`), and not at it (`scale_fails`).

## Each reading has its own embedding

```
C(0, n)  = n      embC    + → ⊕,  × → ⊗          (complexInt on ℤ)
L(0, eⁿ) = n      embL    + → ⊗ and *,  × fails
D(0, −n) = n      embD    + → ⊕,  × → ⊚ fails
S(n, 0)  = n      embS    + → ⊕,  × → ⊚ fails
Q(n, 1)  = n      embQ    + → fraction +,  × → *  (ratioInt on ℤ)
P(1, n)  = n      embP    × → *,  + → ⊕ fails
```

Each is a section of its reading (`C_embC`, …, `P_embP`). The failures of `D` and `S` are repaired by
the `q`-axis: `(0, n)` is a section of `S`, of `D` up to sign, and of `C`, and there `⊚` and `⊗` agree, so
it carries `×` (`embC_mul_split`, `S_embC`, `D_embC`). The sign is because `⊚` makes `q − p`
multiplicative, not `p − q` (`D_pairSplit`). `(n, 1)` is also a section of `P` (`P_embQ`), and it is the
only embedding with a true quotient that carries `×` to `*` (`embQ_unique`). Under `x / 0 = 0` it is not:
`n ↦ (n³, n²)` also works (`embQ_unique_fails`).
-/

namespace T.Unquotiented

open Complex
open scoped Real

/-- The complex reading `q + i·p`. -/
def C (p q : ℝ) : ℂ := ⟨q, p⟩
/-- The logarithm reading `log(q + i·p)`. -/
noncomputable def L (p q : ℝ) : ℂ := Complex.log (C p q)
/-- The difference reading `p − q`. -/
def D (p q : ℝ) : ℝ := p - q
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

theorem C_eq : C p q = (1 + I) / 2 * (S p q + D p q * I) := by
  apply Complex.ext <;> simp [S, D] <;> ring

theorem sum_diff_eq : (S p q + D p q * I : ℂ) = (1 - I) * C p q := by
  apply Complex.ext <;> simp [S, D] <;> ring

theorem exp_L {p q : ℝ} (h : C p q ≠ 0) : Complex.exp (L p q) = C p q := exp_log h

theorem C_sq : C p q ^ 2 = -(S p q * D p q) + 2 * I * P p q := by
  apply Complex.ext <;> simp [sq, S, D, P] <;> ring

theorem P_eq : P p q = (S p q ^ 2 - D p q ^ 2) / 4 := by simp only [P, S, D]; ring

theorem Q_exp : Q (Real.exp p) (Real.exp q) = Real.exp (D p q) := (Real.exp_sub p q).symm

theorem P_exp : P (Real.exp p) (Real.exp q) = Real.exp (S p q) := (Real.exp_add p q).symm

theorem D_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    D (Real.log p) (Real.log q) = Real.log (Q p q) := (Real.log_div hp.ne' hq.ne').symm

theorem S_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    S (Real.log p) (Real.log q) = Real.log (P p q) := (Real.log_mul hp.ne' hq.ne').symm

/-! ## The logarithm of the turn `1 − i` -/

theorem exp_half_log_two : Real.exp (Real.log 2 / 2) = √2 := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add, add_halves,
    Real.exp_log two_pos]

private theorem sub_mul_I_eq (a b : ℝ) : (a : ℂ) - (b : ℂ) * I = ⟨a, -b⟩ := by
  apply Complex.ext <;> simp

theorem log_one_sub_I : Complex.log (1 - I) = (Real.log 2 / 2 : ℝ) - (π / 4 : ℝ) * I := by
  have h2 : √2 * (√2 / 2) = 1 := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hexp : Complex.exp ⟨Real.log 2 / 2, -(π / 4)⟩ = 1 - I := by
    apply Complex.ext
    · rw [Complex.exp_re]
      change Real.exp (Real.log 2 / 2) * Real.cos (-(π / 4)) = (1 - I).re
      rw [Real.cos_neg, exp_half_log_two, Real.cos_pi_div_four, h2]; simp
    · rw [Complex.exp_im]
      change Real.exp (Real.log 2 / 2) * Real.sin (-(π / 4)) = (1 - I).im
      rw [Real.sin_neg, exp_half_log_two, Real.sin_pi_div_four, mul_neg, h2]; simp
  rw [sub_mul_I_eq, ← hexp, log_exp]
  · change -π < -(π / 4); linarith [Real.pi_pos]
  · change -(π / 4) ≤ π; linarith [Real.pi_pos]

theorem arg_one_sub_I : arg (1 - I) = -(π / 4) := by
  rw [← log_im, log_one_sub_I, sub_mul_I_eq]

/-- The branch condition: the turned logarithm is `L + ½ln 2 − iπ/4` exactly when `arg C > −3π/4`. -/
theorem log_sum_diff_iff {p q : ℝ} (h : C p q ≠ 0) :
    Complex.log (S p q + D p q * I) = L p q + (Real.log 2 / 2 : ℝ) - (π / 4 : ℝ) * I ↔
      -(3 * π / 4) < arg (C p q) := by
  have hI : (1 - I : ℂ) ≠ 0 := by
    intro h0; simpa using congrArg im h0
  have : L p q + (Real.log 2 / 2 : ℝ) - (π / 4 : ℝ) * I = Complex.log (1 - I) + Complex.log (C p q) := by
    rw [log_one_sub_I, L]; ring
  rw [this, sum_diff_eq, log_mul_eq_add_log_iff hI h, arg_one_sub_I, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, -⟩; linarith
  · intro h1; exact ⟨by linarith, by linarith [arg_le_pi (C p q), Real.pi_pos]⟩

/-- At `C = −1 − i` the turned logarithm leaves the principal range: the two sides differ by `2πi`. -/
theorem log_sum_diff_ne :
    Complex.log (S (-1) (-1) + D (-1) (-1) * I) ≠
      L (-1) (-1) + (Real.log 2 / 2 : ℝ) - (π / 4 : ℝ) * I := by
  intro h
  have him := congrArg im h
  have hl : (S (-1) (-1) + D (-1) (-1) * I : ℂ) = ((-2 : ℝ) : ℂ) := by
    apply Complex.ext <;> norm_num [S, D]
  rw [hl, log_im, arg_ofReal_of_neg (by norm_num)] at him
  simp [L, log_im] at him
  linarith [arg_le_pi (C (-1) (-1)), Real.pi_pos]

/-- Modulo `2πi`, that is under `exp`, the turned logarithm holds off the origin. -/
theorem exp_log_sum_diff {p q : ℝ} (h : C p q ≠ 0) :
    Complex.exp (Complex.log (S p q + D p q * I)) =
      Complex.exp (L p q + (Real.log 2 / 2 : ℝ) - (π / 4 : ℝ) * I) := by
  have hI : (1 - I : ℂ) ≠ 0 := by
    intro h0; simpa using congrArg im h0
  have : L p q + (Real.log 2 / 2 : ℝ) - (π / 4 : ℝ) * I = Complex.log (1 - I) + Complex.log (C p q) := by
    rw [log_one_sub_I, L]; ring
  rw [this, Complex.exp_add, exp_log hI, exp_log h, sum_diff_eq,
    exp_log (mul_ne_zero hI h)]

/-! ## Direction only -/

/-- The ratio is the tangent of the angle, for every pair: at the origin both are `0`. -/
theorem Q_eq_tan_arg : Q p q = Real.tan (arg (C p q)) := by
  by_cases h : C p q = 0
  · obtain ⟨rfl, rfl⟩ := (C_eq_zero_iff p q).mp h
    simp [Q, h]
  · rw [Real.tan_eq_sin_div_cos, sin_arg, cos_arg h, C_re, C_im, Q,
      div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr h)]

theorem Q_eq_tan_im_L : Q p q = Real.tan (L p q).im := by
  rw [L, log_im, Q_eq_tan_arg]

theorem DS_eq_Q {p q : ℝ} (hq : q ≠ 0) : D p q / S p q = (Q p q - 1) / (Q p q + 1) := by
  have h1 : Q p q - 1 = D p q / q := by simp only [Q, D]; field_simp
  have h2 : Q p q + 1 = S p q / q := by simp only [Q, S]; field_simp
  rw [h1, h2, div_div_div_cancel_right₀ hq]

/-- On the vertical axis the ratio form gives `−1` where `D/S` is `1`. -/
theorem DS_eq_Q_fails : D 1 0 / S 1 0 ≠ (Q 1 0 - 1) / (Q 1 0 + 1) := by
  norm_num [D, S, Q]

theorem DS_eq_tan {p q : ℝ} (h : C p q ≠ 0) :
    D p q / S p q = Real.tan (arg (C p q) - π / 4) := by
  have hr := norm_ne_zero_iff.mpr h
  have hk : √2 / 2 / ‖C p q‖ ≠ 0 := by positivity
  rw [Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four, sin_arg, cos_arg h, C_re, C_im]
  have hn : p / ‖C p q‖ * (√2 / 2) - q / ‖C p q‖ * (√2 / 2) = D p q * (√2 / 2 / ‖C p q‖) := by
    simp only [D]; ring
  have hd : q / ‖C p q‖ * (√2 / 2) + p / ‖C p q‖ * (√2 / 2) = S p q * (√2 / 2 / ‖C p q‖) := by
    simp only [S]; ring
  rw [hn, hd, mul_div_mul_right _ _ hk]

/-- At the origin `D/S` is `0` and `tan(arg C − π/4)` is `−1`. -/
theorem DS_eq_tan_fails : D 0 0 / S 0 0 ≠ Real.tan (arg (C 0 0) - π / 4) := by
  have : C 0 0 = 0 := rfl
  rw [this, arg_zero, zero_sub, Real.tan_neg, Real.tan_pi_div_four]
  norm_num [D, S]

/-- Scaling by any `t ≠ 0`, the half-turn `t = −1` included, keeps the ratio. -/
theorem Q_smul {t : ℝ} (ht : t ≠ 0) : Q (t * p) (t * q) = Q p q := by
  simp only [Q]; exact mul_div_mul_left p q ht

theorem DS_smul {t : ℝ} (ht : t ≠ 0) : D (t * p) (t * q) / S (t * p) (t * q) = D p q / S p q := by
  simp only [D, S, ← mul_sub, ← mul_add]; exact mul_div_mul_left _ _ ht

/-! ## Scale only -/

theorem scale_eq {p q : ℝ} (h : C p q ≠ 0) :
    S p q ^ 2 + D p q ^ 2 = 2 * Real.exp (2 * (L p q).re) := by
  have hr : 0 < ‖C p q‖ := norm_pos_iff.mpr h
  have : (2 : ℝ) * Real.log ‖C p q‖ = Real.log (‖C p q‖ ^ 2) := by
    rw [Real.log_pow]; norm_num
  rw [L, log_re, this, Real.exp_log (by positivity), Complex.sq_norm, C, normSq_mk]
  simp only [S, D]; ring

/-- At the origin `S² + D²` is `0`, but `log 0 = 0` makes the right side `2`. -/
theorem scale_fails : S 0 0 ^ 2 + D 0 0 ^ 2 ≠ 2 * Real.exp (2 * (L 0 0).re) := by
  have : C 0 0 = 0 := rfl
  simp [L, this, S, D]

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
/-- `D`: `n ↦ (0, −n)`, since `0 − (−n) = n`. -/
def embD (n : ℝ) : ℝ × ℝ := (0, -n)
/-- `S`: `n ↦ (n, 0)`. -/
def embS (n : ℝ) : ℝ × ℝ := (n, 0)
/-- `Q`: `n ↦ (n, 1)`, the ratio `n/1`. -/
def embQ (n : ℝ) : ℝ × ℝ := (n, 1)
/-- `P`: `n ↦ (1, n)`. -/
def embP (n : ℝ) : ℝ × ℝ := (1, n)

/-! ### Each is a section of its reading -/

theorem C_embC (n : ℝ) : C (embC n).1 (embC n).2 = n := by apply Complex.ext <;> simp [embC]
theorem L_embL (n : ℝ) : L (embL n).1 (embL n).2 = n := by
  have : C (embL n).1 (embL n).2 = ((Real.exp n : ℝ) : ℂ) := by apply Complex.ext <;> simp [embL, Complex.exp_ofReal_re]
  rw [L, this, ← Complex.ofReal_log (Real.exp_pos n).le, Real.log_exp]
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

theorem embD_add (m n : ℝ) : embD (m + n) = embD m + embD n := by
  ext <;> simp [embD]; ring
/-- `⊚` makes `q − p` multiplicative, not `p − q`. -/
theorem D_pairSplit (x y : ℝ × ℝ) :
    D (pairSplit x y).1 (pairSplit x y).2 = -(D x.1 x.2 * D y.1 y.2) := by
  simp only [D, pairSplit]; ring
theorem S_pairSplit (x y : ℝ × ℝ) :
    S (pairSplit x y).1 (pairSplit x y).2 = S x.1 x.2 * S y.1 y.2 := by
  simp only [S, pairSplit]; ring
/-- So `D`'s embedding does not carry `×` to `⊚`: `(0, −1) ⊚ (0, −1) = (0, 1)`, which reads `−1`. -/
theorem embD_mul_fails : embD (1 * 1) ≠ pairSplit (embD 1) (embD 1) := by
  simp [embD, pairSplit]; norm_num

theorem embS_add (m n : ℝ) : embS (m + n) = embS m + embS n := by ext <;> simp [embS]
/-- `S`'s embedding does not carry `×` to `⊚`: `(1, 0) ⊚ (1, 0) = (0, 1)`. -/
theorem embS_mul_fails : embS (1 * 1) ≠ pairSplit (embS 1) (embS 1) := by
  simp [embS, pairSplit]

/-- On the `q`-axis, `⊚` and `⊗` agree, and `C`'s embedding is a section of `S` and, up to sign, of `D`.
So `(0, n)` serves `C`, `S` and `q − p` at once, carrying `+` and `×`. -/
theorem embC_mul_split (m n : ℝ) : embC (m * n) = pairSplit (embC m) (embC n) := by
  ext <;> simp [embC, pairSplit]
theorem S_embC (n : ℝ) : S (embC n).1 (embC n).2 = n := by simp [S, embC]
theorem D_embC (n : ℝ) : D (embC n).1 (embC n).2 = -n := by simp [D, embC]

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

end T.Unquotiented
