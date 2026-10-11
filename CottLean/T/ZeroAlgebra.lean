import CottLean.T.ZeroScale
import CottLean.T.Quadratic
import Mathlib.Algebra.Polynomial.Laurent

/-!
# `Z(p, q) = p·0^q`, `E(p, q) = q + log₀ p` and `B(p, q) = log_p q`

In all three `p` is the coefficient and `q` the order of zero. `Z` is the value, `E` its logarithm in base
`0`, and `B` the ratio of two of those logarithms.

## The pair `p + 0q`: its `+` is `⊕`, and its product is forced up to `0²`

`(p + 0q) + (r + 0s) = (p + r) + 0(q + s)` by distributing, which is `⊕` on the pairs. For the product, any
operation on pairs that distributes over `⊕`, takes out integer factors, commutes and has a unit `e` is
fixed by one value: the square of the other basis element. With `e = 0 = T(0,1)` and the other element
`ω = T(1,0)`, it is `qtimes a b` of `Quadratic`, where `ω² = a + b·ω` (`eq_qtimes`). So the whole family
of products is already in `T/Quadratic.lean`, and `⊗`, `+` and `⊚` are its rows `ω² = −1, 0, 1`.

In those rows the unit is traction's `0` and the element that squares is traction's `ω`. So `p + 0q`, with
`0` playing `i`, is `⊗` with traction's `ω` in that role and traction's `0` as the `1`. In the `C` reading
that is the pair of unit vectors `1` and `i`.

Read instead with traction's own `0` and `1`, `p + 0q = p·T(1,1) ⊕ q·T(0,1)`, the product needs `1 = T(1,1)`
as its unit. Of traction's products that is `*` (`one_times`). There `0` is idempotent, `0·0 = 0`
(`zero_times_zero`), and has no inverse: its reciprocal `ω` gives `0·ω = 0ω` (`zero_times_omega`).

`E` has this shape, `q + 0·(−ln p)`, but it is a logarithm: its `+` is `Z`'s product, and a product of two
`E`s multiplies logarithms. So these products are not `E`'s operations.

## `Z`: its product is forced, and its `+` makes Laurent polynomials

`Z(a, m)·Z(b, n) = Z(ab, m + n)` is the exponent law. `+` distributes, so it is defined on equal orders,
`Z(a, n) + Z(b, n) = Z(a + b, n)`, and sums of different orders are new elements. The ring they make is
the Laurent polynomials `ℤ[0, 0⁻¹]`, with `Z(p, q) = p·0^q` as its monomials (`toLaurent_mul`,
`toLaurent_add_same`), faithfully (`toLaurent_injective`). There is no relation on `0`: that is what keeps
every order.

## `Z` in traction's products

A product in which `0` stands for an invertible `u` sends `Z(p, q) ↦ p·u^q`, multiplicatively (`toUnit_mul`).
In the `qtimes` rows, `ω` is invertible exactly where `ω² = ±1`:

* `⊗`: `ω⁻¹ = −ω` (`omegaGauss`). `Z(1, 2) ↦ −1 = Z(−1, 0)`, and `Z(1, 4) ↦ 1` (`gauss_two`, `gauss_four`).
* `⊚`: `ω⁻¹ = ω` (`omegaSplit`). `Z(1, 2) ↦ 1` (`split_two`).
* `+` and `*`: `ω` and traction's `0` are not invertible, so `Z`'s negative orders have no image.

So each traction product is `ℤ[0, 0⁻¹]`, or `ℤ[0]` where `0` has no inverse, with one relation imposed,
`0² = a + b·0`, and the relation is exactly what it loses of `Z`: `0² = −1` under `⊗`, `0² = 1` under `⊚`,
`0² = 0` under `+`, and `0² = 0` idempotent under `*`.

## `E = log₀ Z`

`ln 0 = −ω`, zero's scale unit `−1 : 0` of `Bases`, and `0ω = 1` give `log₀ p = −0·ln p`
(`logZero_mul_lnZero`). So `E(p, q) = q + log₀ p = q − 0·ln p`, and `Z = 0^E`:

| on `Z` | on `E` | Lean |
|---|---|---|
| `Z(a, m)·Z(b, n) = Z(ab, m + n)` | `E(a, m) + E(b, n) = E(ab, m + n)` | `E_add`, `Z.log_mul` |
| `Z(p, q)ᵏ = Z(pᵏ, kq)` | `k·E(p, q) = E(pᵏ, kq)` | `E_nsmul` |
| `0ʳ·Z(p, q) = Z(p, q + r)` | `E(p, q) + r = E(p, q + r)` | `E_add_C` |

`E` keeps both parts on positive coefficients (`E_injective`). `0 = Z(1, 1)` goes to `1`, `ω = Z(1, −1)` to
`−1`, and `k = Z(k, 0)` to `log₀ k` (`Z.log_zero`, `Z.log_omega`, `Z.log_ofInt`).

`ln 0` is `−ω`, never `0` (`ln`, where Lean's `Real.log 0 = 0`). Then `log₀ 0 = ln 0 / ln 0`, an `ω/ω`,
and `logZero_zero` takes it as `1` by `Z`'s law `0·ω = 1`. That cancels a `0/0`, which nothing else here
does; in `T/Residual.lean` a coefficient `0` is never reached, so `E` never needs it.

Nothing normalizes: `Z(0, q)` is not `Z(1, q + 1)` (`Z.coeff_zero_ne`), though `E` reads both as the same
value (`E_zero`, `Z.log_coeff_zero`), as `Q` reads `6/2` and `3/1`. Against a coefficient `0`, `E`'s sum
keeps the other coefficient, `E(0, m) + E(b, n) = E(b, m + n + 1)` (`E_add_zero`). `Z`'s product does not:
it evaluates the coefficients in `ℤ`, `0·b = 0`, and drops `b`. So `log₀` stops being a homomorphism
exactly there (`Z.log_mul_coeff_zero_ne`). That is where the `0/0` is lost: the classical `0·b = 0`, the
same absorption traction's `0ω` shows on the other side. `T/Residual.lean` closes it: with an unreduced ratio
as coefficient, a product never makes a coefficient `0`, and an exact cancellation leaves the residual `0·x`.

## `B = E ÷ E` at order `0`

`B(p, q) = log_p q`. `E(q, 0)` and `E(p, 0)` are both multiples of `0`, so their ratio is a `0/0`, and the
`0` cancels: `E(q, 0) = B(p, q)·E(p, 0)` (`E_eq_B_mul`). `B` composes, `B(p, q)·B(q, r) = B(p, r)`
(`B_mul_B`). At base `0`, `log₀ q` is `E(q, 0)` itself, not a real number, so `B` is stated for real bases.

The same `0/0` read as a direction: the point `E(q, 0) + i·E(p, 0)` is `−0·(ln q + i·ln p)`. `0 = Z(1, 1)`
has a positive coefficient and keeps the direction, and the `−` from `ln 0 = −ω` adds half a turn, so its
angle is `atan2(ln p, ln q) + π` (`zeroRatio_arg`). Its tangent is `B(q, p)`; the angle also keeps the
quadrant.
-/

namespace T

/-! ## The products of `p + 0q` are forced -/

/-- `n·x`, coordinatewise. -/
def zsmul' (n : ℤ) (x : T) : T := ⟨n * x.p, n * x.q⟩

/-- Every product on pairs that distributes over `⊕`, takes out integer factors, commutes and has `0` as
its unit is `qtimes a b`, with `ω² = a + b·ω` read from the product itself. -/
theorem eq_qtimes (op : T → T → T)
    (hadd : ∀ x w y, op (x ⊕ w) y = op x y ⊕ op w y)
    (hsmul : ∀ (n : ℤ) x y, op (zsmul' n x) y = zsmul' n (op x y))
    (hcomm : ∀ x y, op x y = op y x)
    (hone : ∀ x, op «0» x = x) (x y : T) :
    op x y = qtimes (op «ω» «ω»).q (op «ω» «ω»).p x y := by
  have hdec : ∀ x : T, x = zsmul' x.p «ω» ⊕ zsmul' x.q «0» := fun x => by
    ext <;> simp [zsmul', oplus, «ω», «0»]
  have hlin : ∀ x w, op x w = zsmul' x.p (op «ω» w) ⊕ zsmul' x.q (op «0» w) := fun x w => by
    conv_lhs => rw [hdec x]
    rw [hadd, hsmul, hsmul]
  have hω : op «ω» y = zsmul' y.p (op «ω» «ω») ⊕ zsmul' y.q «ω» := by
    rw [hcomm «ω» y, hlin y «ω», hone]
  rw [hlin, hone, hω]
  ext <;> simp [zsmul', oplus, qtimes, «ω»] <;> ring

/-! ## With traction's own `0` and `1`: `*` -/

theorem one_times (x : T) : «1» * x = x := by
  change times «1» x = x; ext <;> simp [times, «1»]

end T

namespace T.ZeroScale

open scoped QuadraticAlgebra

/-! ## `Z`'s ring: Laurent polynomials -/

/-- `Z(p, q) ↦ p·0^q` in `ℤ[0, 0⁻¹]`. -/
noncomputable def toLaurent (x : Z) : LaurentPolynomial ℤ := LaurentPolynomial.C x.p * LaurentPolynomial.T x.q

theorem toLaurent_mul (x y : Z) : toLaurent (x * y) = toLaurent x * toLaurent y := by
  simp only [toLaurent, Z.mul_def, map_mul, LaurentPolynomial.T_add]; ring

theorem toLaurent_add_same (a b n : ℤ) : toLaurent ⟨a + b, n⟩ = toLaurent ⟨a, n⟩ + toLaurent ⟨b, n⟩ := by
  simp only [toLaurent, map_add]; ring

theorem toLaurent_omega : toLaurent Z.zero * toLaurent Z.omega = 1 := by
  rw [← toLaurent_mul, Z.zero_mul_omega]; simp [toLaurent]

/-- Off a zero coefficient, `Z` is faithful in `ℤ[0, 0⁻¹]`. -/
theorem toLaurent_injective {x y : Z} (hx : x.p ≠ 0) (h : toLaurent x = toLaurent y) : x = y := by
  simp only [toLaurent, ← LaurentPolynomial.single_eq_C_mul_T] at h
  rcases AddMonoidAlgebra.single_inj.mp h with ⟨hn, hc⟩ | ⟨hc, _⟩
  · exact Z.ext hc hn
  · exact absurd hc hx

/-! ## `Z` where `0` is a unit -/

/-- `Z(p, q) ↦ p·u^q`, for a unit `u` standing for `0`. -/
def toUnit {R : Type*} [CommRing R] (u : Rˣ) (x : Z) : R := x.p * ((u ^ x.q : Rˣ) : R)

theorem toUnit_mul {R : Type*} [CommRing R] (u : Rˣ) (x y : Z) :
    toUnit u (x * y) = toUnit u x * toUnit u y := by
  simp only [toUnit, Z.mul_def, zpow_add, Units.val_mul, Int.cast_mul]; ring

theorem toUnit_zero {R : Type*} [CommRing R] (u : Rˣ) : toUnit u Z.zero = u := by
  simp [toUnit, Z.zero]

open QuadraticAlgebra in
/-- Under `⊗`, `ω⁻¹ = −ω`. -/
def omegaGauss : (QuadraticAlgebra ℤ (-1) 0)ˣ where
  val := ω
  inv := -ω
  val_inv := by rw [mul_neg, omega_mul_omega_eq_mk]; ext <;> simp
  inv_val := by rw [neg_mul, omega_mul_omega_eq_mk]; ext <;> simp

open QuadraticAlgebra in
/-- Under `⊚`, `ω⁻¹ = ω`. -/
def omegaSplit : (QuadraticAlgebra ℤ 1 0)ˣ where
  val := ω
  inv := ω
  val_inv := by rw [omega_mul_omega_eq_mk]; ext <;> simp
  inv_val := by rw [omega_mul_omega_eq_mk]; ext <;> simp

/-- `0` goes to traction's `ω`, read in the ring. -/
theorem gauss_zero : toUnit omegaGauss Z.zero = T.toQuad (-1) 0 T.«ω» := by
  rw [toUnit_zero, T.toQuad_omega]; rfl

/-- Under `⊗`, `0² = −1`: `Z(1, 2)` and `Z(−1, 0)` meet. -/
theorem gauss_two : toUnit omegaGauss ⟨1, 2⟩ = toUnit omegaGauss ⟨-1, 0⟩ := by
  simp only [toUnit, zpow_ofNat, Units.val_pow_eq_pow_val]
  change (1 : ℤ) * (QuadraticAlgebra.omega * QuadraticAlgebra.omega ^ 1 : QuadraticAlgebra ℤ (-1) 0) = _
  rw [pow_one, QuadraticAlgebra.omega_mul_omega_eq_mk]; ext <;> simp

theorem gauss_four : toUnit omegaGauss ⟨1, 4⟩ = toUnit omegaGauss ⟨1, 0⟩ := by
  have h2 : ((omegaGauss ^ (2 : ℤ) : (QuadraticAlgebra ℤ (-1) 0)ˣ) : QuadraticAlgebra ℤ (-1) 0) = -1 := by
    have := gauss_two; simpa [toUnit] using this
  have : (omegaGauss ^ (4 : ℤ)) = omegaGauss ^ (2 : ℤ) * omegaGauss ^ (2 : ℤ) := by
    rw [← zpow_add]; norm_num
  simp only [toUnit, this, Units.val_mul, h2, zpow_zero, Units.val_one]; ring

/-- Under `⊚`, `0² = 1`: `Z(1, 2)` and `Z(1, 0)` meet. -/
theorem split_two : toUnit omegaSplit ⟨1, 2⟩ = toUnit omegaSplit ⟨1, 0⟩ := by
  simp only [toUnit, zpow_ofNat, Units.val_pow_eq_pow_val]
  change (1 : ℤ) * (QuadraticAlgebra.omega * QuadraticAlgebra.omega ^ 1 : QuadraticAlgebra ℤ 1 0) = _
  rw [pow_one, QuadraticAlgebra.omega_mul_omega_eq_mk]; ext <;> simp

end T.ZeroScale

namespace T.ZeroScale

open LaurentPolynomial

/-! ## `E = log₀ Z` -/

/-- `ln 0 = −ω`. -/
noncomputable def lnZero : LaurentPolynomial ℝ := -T (-1)

/-- `ln p`, with `ln 0 = −ω`: never `0` at `0`, where `Real.log 0 = 0`. -/
noncomputable def ln (p : ℝ) : LaurentPolynomial ℝ := if p = 0 then lnZero else C (Real.log p)

theorem ln_zero : ln 0 = lnZero := if_pos rfl

theorem ln_of_ne {p : ℝ} (hp : p ≠ 0) : ln p = C (Real.log p) := if_neg hp

/-- `log₀ p = ln p / ln 0 = −0·ln p`. -/
noncomputable def logZero (p : ℝ) : LaurentPolynomial ℝ := -(ln p * T 1)

/-- `log₀ p · ln 0 = ln p`: it is the logarithm in base `0`. -/
theorem logZero_mul_lnZero (p : ℝ) : logZero p * lnZero = ln p := by
  simp only [logZero, lnZero, neg_mul_neg, mul_assoc, ← T_add]; simp

/-- `log₀ 0 = 1`. -/
theorem logZero_zero : logZero 0 = 1 := by
  simp only [logZero, ln_zero, lnZero, neg_mul, ← T_add]; simp

theorem logZero_of_ne {p : ℝ} (hp : p ≠ 0) : logZero p = C (-Real.log p) * T 1 := by
  simp [logZero, ln_of_ne hp]

/-- `E(p, q) = q + log₀ p`, with `p` the coefficient and `q` the order. -/
noncomputable def E (p q : ℝ) : LaurentPolynomial ℝ := C q + logZero p

theorem E_eq {p : ℝ} (hp : p ≠ 0) (q : ℝ) : E p q = C q + C (-Real.log p) * T 1 := by
  rw [E, logZero_of_ne hp]

/-- `E(0, q)` and `E(1, q + 1)` have the same value. The pairs stay apart; only the reading meets. -/
theorem E_zero (q : ℝ) : E 0 q = E 1 (q + 1) := by
  simp [E, logZero_zero, logZero_of_ne one_ne_zero]

/-- `Z`'s product is `E`'s `+`. -/
theorem E_add {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (m n : ℝ) : E a m + E b n = E (a * b) (m + n) := by
  simp only [E_eq ha, E_eq hb, E_eq (mul_ne_zero ha hb), Real.log_mul ha hb, map_add, neg_add, map_neg]
  ring

/-- Against a coefficient `0`, the sum keeps the other coefficient: `E(0, m) + E(b, n) = E(b, m + n + 1)`. -/
theorem E_add_zero (b m n : ℝ) : E 0 m + E b n = E b (m + n + 1) := by
  simp only [E, logZero_zero, map_add, map_one]; ring

/-- So the sum is not `E(0, m + n)`, the reading of `Z`'s product `Z(0·b, m + n)`. -/
theorem E_zero_add_ne {b x y : ℝ} (hb : Real.log b ≠ 0) : E 0 (x + y) ≠ E 0 x + E b y := by
  have hb0 : b ≠ 0 := by rintro rfl; exact hb Real.log_zero
  intro h
  rw [E_add_zero, E_zero, E_eq one_ne_zero, E_eq hb0] at h
  simp only [← single_eq_C_mul_T] at h
  have h1 := congrArg (fun f : LaurentPolynomial ℝ => f.coeff 1) h
  have : (0 : ℝ) = -Real.log b := by
    simpa [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single, -single_eq_C_mul_T] using h1
  exact hb (by linarith)

/-- `Z`'s power is `E`'s multiple. -/
theorem E_nsmul {p : ℝ} (hp : p ≠ 0) (q : ℝ) (k : ℕ) : C (k : ℝ) * E p q = E (p ^ k) (k * q) := by
  simp only [E_eq hp, E_eq (pow_ne_zero k hp), Real.log_pow, map_mul, map_neg]; ring

/-- Multiplying `Z` by `0ʳ` adds `r` to `E`. -/
theorem E_add_C (p q r : ℝ) : E p q + C r = E p (q + r) := by
  simp only [E, map_add]; ring

/-- On positive coefficients `E` keeps both the coefficient and the order. -/
theorem E_injective {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {m n : ℝ} (h : E a m = E b n) :
    a = b ∧ m = n := by
  simp only [E_eq ha.ne', E_eq hb.ne', ← single_eq_C_mul_T] at h
  have h0 := congrArg (fun f : LaurentPolynomial ℝ => f.coeff 0) h
  have h1 := congrArg (fun f : LaurentPolynomial ℝ => f.coeff 1) h
  have h0' : m = n := by
    simpa [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single, -single_eq_C_mul_T] using h0
  have h1' : Real.log a = Real.log b := by
    simpa [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single, -single_eq_C_mul_T] using h1
  exact ⟨Real.log_injOn_pos ha hb h1', h0'⟩

/-- `Z` read through `log₀`. -/
noncomputable def Z.log (x : Z) : LaurentPolynomial ℝ := E x.p x.q

theorem Z.log_mul {x y : Z} (hx : x.p ≠ 0) (hy : y.p ≠ 0) : (x * y).log = x.log + y.log := by
  simp only [Z.log, Z.mul_def, Int.cast_mul, Int.cast_add]
  exact (E_add (by exact_mod_cast hx) (by exact_mod_cast hy) _ _).symm

/-- `0 = Z(1, 1)` goes to `1`, `ω = Z(1, −1)` to `−1`, and `k = Z(k, 0)` to `log₀ k`. -/
theorem Z.log_zero : Z.zero.log = 1 := by simp [Z.log, Z.zero, E, logZero_of_ne one_ne_zero]
theorem Z.log_omega : Z.omega.log = -1 := by simp [Z.log, Z.omega, E, logZero_of_ne one_ne_zero]
theorem Z.log_ofInt (k : ℤ) : (Z.ofInt k).log = logZero k := by simp [Z.log, Z.ofInt, E]

/-- `Z(0, q)` is not `Z(1, q + 1)`: nothing moves the coefficient's `0` into the order. -/
theorem Z.coeff_zero_ne (q : ℤ) : (⟨0, q⟩ : Z) ≠ ⟨1, q + 1⟩ := by
  intro h; have := congrArg Z.p h; simp at this

/-- But `log₀` reads them the same, as `Q` reads `6/2` and `3/1` the same. -/
theorem Z.log_coeff_zero (q : ℤ) : (⟨0, q⟩ : Z).log = (⟨1, q + 1⟩ : Z).log := by
  simp only [Z.log, Int.cast_zero, Int.cast_one, Int.cast_add, E_zero]

/-- Where `0/0` is lost: `Z`'s product evaluates the coefficients in `ℤ`, `0·b = 0`, and drops `b`, which
`E`'s sum keeps. So `log₀` is not a homomorphism against a coefficient `0`. -/
theorem Z.log_mul_coeff_zero_ne {b m n : ℤ} (hb : Real.log b ≠ 0) :
    ((⟨0, m⟩ : Z) * ⟨b, n⟩).log ≠ (⟨0, m⟩ : Z).log + (⟨b, n⟩ : Z).log := by
  simpa [Z.log] using E_zero_add_ne (x := m) (y := n) hb

/-! ## `B = E ÷ E` at order `0` -/

/-- `B(p, q) = log_p q`. -/
noncomputable def B (p q : ℝ) : ℝ := Real.logb p q

/-- `E(q, 0) = B(p, q)·E(p, 0)`: the `0` of the ratio cancels. At `q = 0`, `log_p 0 = −ω / ln p` is not
real. -/
theorem E_eq_B_mul {p q : ℝ} (hp : Real.log p ≠ 0) (hq : q ≠ 0) : E q 0 = C (B p q) * E p 0 := by
  have hp0 : p ≠ 0 := by rintro rfl; exact hp Real.log_zero
  simp only [E_eq hp0, E_eq hq, B, map_zero, zero_add, ← mul_assoc, ← map_mul, Real.logb, mul_neg]
  congr 3; field_simp

/-- `B` composes. -/
theorem B_mul_B {p q r : ℝ} (h₁ : q ≠ 0) (h₂ : q ≠ 1) (h₃ : q ≠ -1) : B p q * B q r = B p r :=
  Real.mul_logb h₁ h₂ h₃

/-- With `s > 0` the magnitude of `0`, the point `E(q, 0) + i·E(p, 0)` turns by `atan2(ln p, ln q) + π`. -/
theorem zeroRatio_arg {s p q : ℝ} (hs : 0 < s) (h : (⟨Real.log q, Real.log p⟩ : ℂ) ≠ 0) :
    (Complex.arg ⟨-s * Real.log q, -s * Real.log p⟩ : Real.Angle) =
      Complex.arg ⟨Real.log q, Real.log p⟩ + Real.pi := by
  have : (⟨-s * Real.log q, -s * Real.log p⟩ : ℂ) = -((s : ℂ) * ⟨Real.log q, Real.log p⟩) := by
    apply Complex.ext <;> simp
  rw [this, Complex.arg_neg_coe_angle (mul_ne_zero (by exact_mod_cast hs.ne') h),
    Complex.arg_real_mul _ hs]

end T.ZeroScale
