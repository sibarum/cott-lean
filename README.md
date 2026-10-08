# cott-lean

[![Build and check axioms](https://github.com/sibarum/cott-lean/actions/workflows/build.yml/badge.svg)](https://github.com/sibarum/cott-lean/actions/workflows/build.yml)

A Lean 4 formalization of **traction**, the number model of [cott-engine](../cott-engine). This repository is
the specification: the engine implements what is proved here and cites it by name.

A traction is an **unquotiented pair** `T(p, q)`. Nothing is reduced. `T(1,2)` and `T(2,4)` are different
values, `q = 0` is allowed, and `0/0` is a value like any other. The pair is the ground truth, and every
number it stands for is a reading of it. There are six:

```
C(p,q) = q + i·p             as a complex number
D(p,q) = q − p               as a difference
S(p,q) = p + q               as a sum
Q(p,q) = p / q               as a ratio
P(p,q) = p · q               as a product
L(p,q) = (log_b N, turn)     as a logarithm: a scale in any base b, and a turn     N = p² + q²
```

None of them needs π. The base of `L` is chosen only when converting, and its turn is the direction as a
fraction of a whole turn. Radians, `e^(iθ)` and every relation that needs π are kept apart, in a bridge
to classical trigonometry.

The readings are not independent. They all follow from the definitions, and
[The pair and its readings](#the-pair-and-its-readings) proves how they relate. On that one set of pairs,
traction defines several arithmetics at once. Each of them is the arithmetic of one or more readings: `⊕`
adds `C`, `⊗` multiplies it and adds `L`, `*` multiplies `Q`, and `+` adds `Q`. The design goal is a
runtime in which a value can be read under any of them, and moving between them is always an explicit
conversion. This repository proves what each arithmetic is, which laws it keeps, and where it loses
information.

Every theorem holds for every pair; none is checked on a sample. Every declaration is machine-checked to
use only Lean's standard axioms, in CI (see [Checking the axioms](#checking-the-axioms)).

## The pair and its readings

Here the pair is real, `(p, q) ∈ ℝ²`, so that `bᵖ` and `log_b p` make sense. On the integers `C` is `toC`
(`C_toC`). The difference is `D = q − p`, the sign `⊚` multiplies. Every relation comes from one fact:
`(S, D)` is the pair `⊗ T(1,1)`, traction's `1`, an eighth of a turn scaled by `√2` (`pairOtimes_one`). As
points, `C(S, D) = (1 + i)·C` and `D + iS = (1 + i)·C` (`C_sum_diff`, `sum_diff_eq`). Then `exp` and `log`
exchange `+` with `*`.

The theorems are in three files. `T/Unquotiented.lean` has `C`, `D`, `S`, `Q` and `P`, and states nothing
with π. `T/LogPair.lean` has `L`. `T/Radians.lean` is the bridge: it converts `L` back to the point and to
radians, and holds everything stated with π.

**Exact: `C` is equivalent to `(D, S)`.** In `T/Unquotiented.lean`.

| relation | holds | Lean |
|---|---|---|
| `C = ((1 − i)/2)(D + iS)` | always | `C_eq` |
| `D + iS = (1 + i)·C` | always | `sum_diff_eq` |
| `C(S, D) = (1 + i)·C(p, q)` | always | `C_sum_diff` |
| `P = (S² − D²)/4` | always | `P_eq` |
| `C² = S·D + 2i·P` | always | `C_sq` |
| `Q(eᵖ, e^q) = e^(−D)` | always | `Q_exp` |
| `P(eᵖ, e^q) = e^S` | always | `P_exp` |
| `D(log p, log q) = −log Q` | `p, q > 0` | `D_log` |
| `S(log p, log q) = log P` | `p, q > 0` | `S_log` |

**Direction only, as a line.** `Q` and `D/S` do not change when the pair is scaled by any `t ≠ 0`, the half
turn `t = −1` among them (`Q_smul`, `DS_smul`). `D/S = (1 − Q)/(1 + Q)` needs `q ≠ 0` (`DS_eq_Q`,
`DS_eq_Q_fails`).

**The logarithm as a pair.** In `T/LogPair.lean`. `L_b(p,q) = (log_b N, turn)`, with `N = p² + q²` the
squared norm, so no square root is taken.

| relation | holds | Lean |
|---|---|---|
| `N(x ⊗ y) = N(x)·N(y)` | always | `N_pairOtimes` |
| `log_b N(x ⊗ y) = log_b N(x) + log_b N(y)` | off the origin, any `b` | `logScale_pairOtimes` |
| `turn(x ⊗ y) = turn(x) + turn(y)` | modulo `1`, off the origin | `turn_pairOtimes` |
| `L(x ⊗ y) = L(x) + L(y)` | the turn modulo `1`, off the origin | `L_pairOtimes` |
| `turn(t·p, t·q) = turn(p, q)` | `t > 0` | `turn_smul` |
| equal turns exactly when one pair is a positive multiple of the other | off the origin | `turn_eq_turn_iff` |
| `turn = T.turn` | integer pairs | `turn_toT` |
| `turn < a/b` decided by the winding count, in integers | integer pairs in the upper half-plane | `turnLt_iff_turn` |
| `log_c N = log_b N · log_c b`, the turn unchanged | `log b ≠ 0` | `logScale_change_base` |
| `Q(bᵖ, b^q) = b^(−D)`, `P(bᵖ, b^q) = b^S` | `b > 0` | `Q_rpow`, `P_rpow` |
| `D(log_b p, log_b q) = −log_b Q`, `S(log_b p, log_b q) = log_b P` | `p, q > 0` | `D_logb`, `S_logb` |

The turn keeps the ray, which `Q` and `D/S` lose. Lean's circle is built from π, so `turn` is defined as
`arg C / 2π`; that definition is the only π in the file, and no statement there mentions it.

**The bridge to radians.** In `T/Radians.lean`. `1^t` is the rotation by `t` whole turns, and the scale and
the turn give the point back in any base.

| relation | holds | Lean |
|---|---|---|
| `1^(s + t) = 1^s · 1^t`, `1^(t + 1) = 1^t` | always | `oneTurn_add`, `oneTurn_add_one` |
| `1^1 = 1`, `1^(1/2) = −1`, `1^(1/4) = i` | always | `oneTurn_one`, `oneTurn_half`, `oneTurn_quarter` |
| `C = b^(½·log_b N) · 1^turn` | `b > 0`, `b ≠ 1`, off the origin | `C_eq_logScale_turn` |
| `Lrad = ½·log_e N + 2π·turn·i` | always | `Lrad_eq` |
| `A = 2π·turn` | always | `A_eq_turn` |

So `(−1)^t = 1^(t/2)` and `i^t = 1^(t/4)`. `Lrad = log(q + i·p)` is Lean's complex logarithm: the pair `L` in
base `e`, with the turn measured in radians. `A = arg C` is the angle in radians. The rest is stated with
them.

| relation | holds | Lean |
|---|---|---|
| `C = e^Lrad` | off the origin | `exp_Lrad` |
| `log(D + iS) = Lrad + ½·log 2 + iπ/4` | exactly when `arg C ≤ 3π/4`; modulo `2πi` off the origin; fails at `C = −1` | `log_sum_diff_iff`, `exp_log_sum_diff`, `log_sum_diff_ne` |
| `Q = tan A = tan(Im Lrad)` | every pair, the origin included | `Q_eq_tan_A`, `Q_eq_tan_im_Lrad` |
| `D/S = tan(π/4 − A)` | off the origin | `DS_eq_tan_A`, `DS_eq_tan_fails` |
| `A = Im Lrad` | every pair | `A_eq_im_Lrad` |
| `A = θ` | integer pairs | `A_theta` |
| `A(t·p, t·q) = A(p, q)`, and `A(−p, −q) ≠ A(p, q)` | `t > 0`; off the origin | `A_smul`, `A_neg` |
| `A` equal exactly when one pair is a positive multiple of the other | off the origin | `A_eq_A_iff` |
| `A(x ⊗ y) = A(x) + A(y)` | modulo `2π`, off the origin | `A_pairOtimes` |
| `S² + D² = 2·e^(2 Re Lrad)` | off the origin | `scale_eq`, `scale_fails` |
| `C = \|C\|·e^(iA)`, and `C = e^(Re Lrad)·e^(iA)` | always; off the origin | `C_eq_polar`, `C_eq_scale_angle` |

The logarithm of the turn `1 + i` is the one relation that needs a branch. Adding `π/4` takes an argument
above `3π/4` out of the principal range, so it holds exactly only on the rest of the plane. A pair `L` with
its turn kept modulo `1` has no branch.

**Each reading has its own embedding of a number.** Each is a section of its reading
(`C_embC`, …, `P_embP`), and each carries some of the number's arithmetic into the pairs:

| embedding | reads `n` under | carries | fails | Lean |
|---|---|---|---|---|
| `(0, n)` | `C`, `D` and `S` | `+` to `⊕`, `×` to `⊗` and to `⊚` | | `embC_add`, `embC_mul`, `embC_mul_split`, `embD_mul`, `S_embC`, `D_embC` |
| `(0, eⁿ)` | `Lrad` | `+` to `⊗` and to `*` | `×` | `Lrad_embL`, `embL_add`, `embL_add_times`, `embL_mul_fails` |
| `(n, 0)` | `S` | `+` to `⊕` | `×` to `⊚` | `embS_add`, `embS_mul_fails` |
| `(n, 1)` | `Q`, and `P` | `+` to fraction `+`, `×` to `*` | `+` to `⊕` | `embQ_add`, `embQ_mul`, `embQ_oplus_fails`, `P_embQ` |
| `(1, n)` | `P` | `×` to `*` | `+` to `⊕` | `embP_mul`, `embP_add_fails` |

On ℤ, `(0, n)` is the complex reading's integers and `(n, 1)` the ratio reading's (`embC_complexInt`,
`embQ_ratioInt`); [Two readings](#two-readings-and-the-inverse-one-level-up) shows they share only `0`. `D`'s
embedding is `C`'s (`embD_eq_embC`), and `S`'s own embedding is repaired by it: on the `q`-axis `⊚` and `⊗`
agree, so it carries `×`. `(n, 1)` is the only embedding with a true quotient that carries `×` to `*`
(`embQ_unique`). Under Lean's `x / 0 = 0` it is not, since `n ↦ (n³, n²)` also works
(`embQ_unique_fails`).

### Each reading is an algebra on the pairs

`T/PairAlgebras.lean`. For each reading `R`, the operations on pairs that `R` turns into `+` and `×`. Read
through `toPair`, each operation of `T` is the real pair operation of the same name (`toPair_oplus`,
`toPair_otimes`, `toPair_splitTimes`, `toPair_times`, `toPair_plus`).

| reading | `+` on pairs | `×` on pairs | the algebra | Lean |
|---|---|---|---|---|
| `C` | `⊕` | `⊗` | ℂ, since `C` loses nothing | `C_add`, `C_pairOtimes`, `C_injective` |
| `D`, `S` | `⊕` | `⊚` | ℝ × ℝ in the coordinates `(S, D)` | `D_add`, `S_add`, `D_pairSplit`, `S_pairSplit`, `SD_injective` |
| `Q` | `+` | `*` | a wheel: `*` distributes over `+` only up to the scale `z.q` | `Q_pairPlus`, `Q_pairTimes`, `pairPlus_pairTimes`, `pairPlus_pairTimes_ne` |
| `P` | none that is homogeneous | `*` | needs a layer | `P_pairTimes`, `no_homogeneous_P_add`, `oplus_P_add_fails` |
| `L` | `⊗`, the turn modulo `1` | none flat | needs a layer | `L_pairOtimes`, `logScale_pairOtimes`, `turn_pairOtimes` |
| `1/Q` | `∥` | `*` | `+` on `Q` through the reciprocal | `reciprocal_par` |

`Q_pairPlus` needs both denominators non-zero. `P` has no flat addition because of degrees: every bilinear
operation is homogeneous in its left argument (`pairPlus_homogeneous`, `pairOtimes_homogeneous`,
`pairSplit_homogeneous`, `pairTimes_homogeneous`), so scaling that argument by `t` scales `P` of the result
by `t²`, while `P x + P y` scales only its first term. `P(eᵖ, e^q) = e^S` puts `P`'s `×` one layer down, as
`S`'s `+` on the exponents.

**Converting between algebras.** `toSD`, the conversion `(p, q) ↦ (S, D)`, is `⊗ T(1,1)` and invertible
(`toSD_apply`). It carries `⊕` exactly (`toSD_add`), and `⊗` only up to the residue `T(1,1)`
(`toSD_pairOtimes`). It does not carry `⊗` to `⊚` (`toSD_not_split`), and no conversion can: `⊚` has zero
divisors on the light lines, `(1, 1) ⊚ (−1, 1) = (0, 0)` (`pairSplit_light`), so no bijection fixing `0`
takes `⊗` to `⊚` (`no_otimes_to_split`). ℂ and ℝ × ℝ are different rings on the same pairs. What a
conversion always does is carry a product across, `g⁻¹(g x · g y)` (`carry`), and the result keeps the
product's laws (`carry_comm`, `carry_assoc`, `carry_add`). `⊚` carried back through `toSD` is
`(p, q) · (r, s) = (−2pr, 2qs)` in the original coordinates (`carry_split_eq`), a third algebra on the same
pairs.

## What it shows

**Every inverse returns to 1 up to its own norm.** Multiplying by a fixed pair is a linear map of the
other pair, and its determinant is the product's norm. Since traction never reduces, where classical
arithmetic divides by the determinant, traction keeps the adjugate, and the determinant stays in the
coordinates as a residue: `x · (1/x)` is `1` with both coordinates scaled by the norm. The inverse fails
exactly where the norm is zero, and that is exactly where multiplying by the pair loses information. One
level up, where the coordinates are themselves ratios, every quadratic ring gets an exact inverse this
way, and the same rule holds: `z · (1/z)` is `1` scaled by one integer, which is zero exactly at a zero
denominator or a zero norm. On the integer points that is the flat product's own loss.

**One carrier holds every quadratic ring, exactly.** Traction's mediant `⊕` adds pairs coordinatewise.
With it, a single parametric product makes the pairs into the Gaussian integers, the dual numbers, the
split-complex integers, ℤ × ℤ, the Eisenstein integers and every other ring of rank two over ℤ. It uses
the same reading of the pair each time and needs no quotient. The model's own operations are members of
this family: angle addition `⊗` is the Gaussian product, and ordinary fraction addition `+` is the
dual-number product.

**Each product is a family of Möbius transformations.** Multiplying by a fixed pair is a 2×2 integer
matrix acting on the ratio. Its classical type, elliptic, parabolic or hyperbolic, is the ring's
discriminant. Its determinant is the norm, the quantity that decides whether the product can be undone.
Its fixed points are exactly the directions in which the product loses information. So each product is
fixed by a pair of points on the line of ratios. Carrying a product through another Möbius transformation
keeps all its laws and moves those points.

**The pair operations keep what classical formulas lose.** Written with ordinary fraction arithmetic,
tangent addition, relativistic velocity addition and the parallel sum all break down to `0/0` at an
infinite argument. The corresponding pair operations, `⊗`, the split-complex `⊚` and the parallel `∥`, lose
nothing there. The classical formula turns out to be the pair operation with both coordinates multiplied by
a factor that happens to be zero.

**Information loss is exact and bounded.** Given a result and one operand, the other operand comes back
exactly when the known one has non-zero norm. When it doesn't come back, the product has forgotten
exactly one integer of it, and keeping that one integer alongside the result is enough to recover it.

**The tower is forced, not chosen.** The mediant survives no quotient: no invariant coarser than the pair
itself, such as the ray or the ratio, is respected by it. No equality at all lets it stand beside
division. So each ring keeps its laws on the bare pairs, and division has to come from a second level,
pairs of pairs. That level gives each ring its exact inverse. It also builds ℚ(i) in two ways, as a
complex number with ratio coordinates and as a ratio of two Gaussian integers. The two hold the same
values, pay for division in opposite places, and each loses something the other keeps. Among the named
invariants, the angle and the ray turn out to be the same one, and the mediant always lies strictly
between its two parents.

## What is classical and what is new

Most of the individual facts are classical. ℤ[i] is ℤ[i] and a quadratic ring is a quadratic ring; the
wheel result is a case of Carlström's theorem; the mediant tree is the Stern–Brocot tree, extended to the
four signed quadrants; and the elliptic, parabolic and hyperbolic types are the classical classification
of Möbius transformations.

What belongs to traction is all of them sharing one set of unreduced pairs, and the exactness that sharing
forces:

- which of the model's lines hold at coordinate equality, which hold only under a named invariant, and
  what the exact coordinate result is otherwise;
- `0ω = 0/0` as the zero of every one of the rings and the bottom element of the wheel, at once;
- each product completing a classical formula at exactly the inputs where that formula collapses;
- the mediant as the one operation every ring shares and no quotient keeps;
- each inverse leaving its own norm behind as a residue, failing exactly where that product loses
  information, at both levels.

The second level's values are classical too: the Gaussian rationals, the inverse `z̄/|z|²`, the
adjugate identity behind Cramer's rule, and the bicomplex numbers. What is new is the unreduced
bookkeeping, which keeps the determinant where classical arithmetic divides it away.

## Reading the notation

- **No invariant is specified by default.** Two pairs are equal exactly when their coordinates are, so
  `T(1,2) ≠ T(2,4)`. The ratio, the ray (a positive multiple of both coordinates), the angle and the norm
  are invariants a use may specify, and a result that holds only under one of them says which. Each is
  read from the pair, never stored in place of it: the ratio is `Q`, the angle is `A`, and the norm is
  `|C|²`. Away from `0ω`, the angle and the ray are the same invariant (`theta_eq_theta_iff_sameRay`).
- **The nine named values** are spelled the model's way. The four seeds are `0 = T(0,1)`, `ω = T(1,0)`,
  `_0 = T(0,-1)` and `-ω = T(-1,0)`. Between them are `1 = T(1,1)`, `_1 = T(1,-1)`, `-_1 = T(-1,-1)` and
  `-1 = T(-1,1)`, and `0ω = T(0,0)` is the ninth. In Lean they are `T.«0»`, `T.«ω»`, `T.«_0»`, and so on.
- **`-x` is `T(-p, q)`**, the numerator turned. So `-0 = 0`, and `T(0,-1)` is `_0`. The mediant's
  inverse `T(-p,-q)` is `-_x`.
- **The operations.**

  | | formula | reading |
  |---|---|---|
  | `x + y` | `T(ps + rq, qs)` | fraction addition |
  | `x * y` | `T(pr, qs)` | fraction multiplication |
  | `x ⊕ y` | `T(p + r, q + s)` | the mediant; the sum of the points |
  | `x ⊗ y` | `T(ps + rq, qs − pr)` | angle addition; the product of the points |
  | `x ⊚ y` | `T(ps + rq, qs + pr)` | the split-complex product; velocity addition |
  | `x ∥ y` | `T(pr, ps + rq)` | the parallel sum, `1/(1/x + 1/y)` |

  In each row `x = T(p,q)` and `y = T(r,s)`.

## The results in detail

### The rings on one carrier

**The mediant and `⊗` are the Gaussian integers** (`T/Gaussian.lean`). `T(p, q)` is the point `q + p·i`.
`⊕` is addition, `⊗` is multiplication, `-x` is the complex conjugate and `-_x` is the negative, exactly:
`GaussianPosition.ringEquiv : GaussianPosition ≃+* ℤ[i]`. The four seeds are exactly the pairs `⊗` can
undo (`exists_otimes_eq_zero_iff`).

**Fraction arithmetic is a wheel** (`T/Wheel.lean`). `(T, 0, 1, +, *, /)` satisfies every wheel axiom at
coordinate equality (`isWheel`). It is Carlström's wheel of fractions over ℤ with `S = {1}`, the choice
that identifies nothing. The wheel's bottom element `0/0` is `0ω`, and so is `0·ω` (`bottom_eq`,
`zero_times_omega`). `0ω` absorbs under `+`, `*` and `⊗`, is the identity of `⊕`, and is the only pair all
three inverses leave fixed (`zeroOmega_*`, `fixed_by_all_inverses_iff`).

**The mediant with `+` is the dual numbers, and with `*` it is ℤ × ℤ** (`T/Dual.lean`). Under the reading
`T(p, q) ↦ q + p·ε`, `+` is dual-number multiplication: `(b + aε)(d + cε) = bd + (ad+bc)ε`, which is
`T(ad+bc, bd)`. `0` is the unit, `ω` is `ε` (`ω + ω = 0ω`), and `-x` is the dual conjugate
(`DualPosition.ringEquiv`). `*` is coordinatewise, so `⊕` and `*` are ℤ × ℤ (`ProdPosition.ringEquiv`).
`(x ⊕ y) + z = (x + z) ⊕ (y + z)` holds exactly (`oplus_plus`), where `+` over `*` needs a scale.

**Every quadratic ring is one product** (`T/Quadratic.lean`). Read `T(p, q)` as `q + p·ω` with
`ω² = a + b·ω`. Then `qtimes a b (T(p,q)) (T(r,s)) = T(ps + rq + b·pr, qs + a·pr)` makes `(T, ⊕, qtimes a b)`
Mathlib's `QuadraticAlgebra ℤ a b`, for every `a` and `b`, by the same map (`QuadPosition.ringEquiv`).

| `ω²` | ring | discriminant | in T |
|---|---|---|---|
| `−1` | Gaussian integers ℤ[i] | `−4` | `⊗` (`otimes_eq_qtimes`) |
| `0` | dual numbers ℤ[ε] | `0` | `+` (`plus_eq_qtimes`) |
| `1` | split-complex integers ℤ[j] | `4` | `⊚` (`splitTimes`) |
| `ω` | ℤ × ℤ | `1` | `*`, read as `q + (p − q)·ω` (`ProdPosition.quadEquiv`) |
| `−1 − ω` | Eisenstein integers ℤ[ζ₃] | `−3` | `qtimes (-1) (-1)` |

The complex, dual and split-complex numbers are the rows with `b = 0`. `*` is not the split-complex
product over ℤ: its ring has the idempotent `ω`, and ℤ[j] has none but `0` and `1` (`split_not_prod`).
The two agree only once 2 is invertible.

**The parallel sum is `+` through the reciprocal** (`T/Parallel.lean`). Of the power sums
`(xⁿ + yⁿ)^(1/n)`, two stay on the integer pairs: `n = 1`, which is `+`, and `n = −1`, the rule for
resistors in parallel, `x ∥ y = T(ac, ad + bc)` (`reciprocal_par`). `(T, ⊕, ∥)` is ℤ[ε] again with `0` and
`ω` exchanged (`ParPosition.ringEquiv`), and the reciprocal is a ring isomorphism onto it from `(T, ⊕, +)`
(`ParPosition.reciprocalEquiv`).

**Every other power sum leaves the pairs** (`T/PowerSum.lean`). Read exactly, `z` is a power sum of `x`
and `y` when `zⁿ = xⁿ + yⁿ` on the coordinates (`IsPowerSum`). At `n = 1` and `n = −1` that is one pair,
`x + y` or `x ∥ y`, for every `x` and `y`. At every other `n`, `1ⁿ + 1ⁿ = T(2,1)` is no pair's `n`th power,
and no pair but `0ω` has an `n`th power at its ratio (`not_isPowerSum_one_one`, `sameRatio_one_one`),
because `pⁿ = 2qⁿ` forces `p = q = 0` (`pow_eq_two_mul_pow`). So `+` and `∥` are the only power sums
defined for every pair (`forall_isPowerSum_iff`). Some pairs stay at other exponents: `3² + 4² = 5²`
(`isPowerSum_two`). At `n = 3` and `n = 4` a power sum is a pair only where one numerator is zero, which
is Fermat's Last Theorem at those exponents (`isPowerSum_three`, `isPowerSum_four`). At every `n ≥ 3` the
same statement is Fermat's Last Theorem itself, which Mathlib does not have (`isPowerSum_trivial_of_flt`).

### Every product is a family of Möbius transformations

`T/Transform.lean`. A Möbius transformation of the ratio, `p/q ↦ (αp + βq)/(γp + δq)`, is a 2×2 integer
matrix acting on the pair (`act`), and composing two multiplies their matrices (`act_mul`). These are
exactly the maps that respect `⊕` (`eq_act_of_oplus`). The reciprocal, `-x`, `-_x` and a quarter turn
are among them. Multiplying by a fixed `y = T(r, s)` is one too:

| product | multiply by `T(r, s)` | `trace² − 4·det` | type | fixed points |
|---|---|---|---|---|
| `⊗` | `[[s, r], [−r, s]]` | `−4r²` | elliptic | none but `0ω` |
| `+` | `[[s, r], [0, s]]` | `0` | parabolic | `ω`'s ray |
| `⊚` | `[[s, r], [r, s]]` | `4r²` | hyperbolic | the light lines |
| `*` | `[[r, 0], [0, s]]` | `(r − s)²` | hyperbolic | the two axes |
| `∥` | `[[r, 0], [s, r]]` | `0` | parabolic | `0`'s ray |

For the whole family `ω² = a + b·ω`, the determinant of multiplying by `y` is `y`'s norm (`det_qmat`),
and the discriminant is `y.p²·(b² + 4a)` (`disc_qmat`). So the ring's type is the type of all its
non-scalar elements. A ray is fixed exactly when `det(x, x·y) = y.p·N(x)` is zero (`det_qtimes_self`), so
the fixed points are the rays of the zero divisors.

**Sandwiches.** Carrying a product through a bijection and back, `g⁻¹(g x · g y)`, keeps commutativity,
associativity and, when `g` respects `⊕`, distributivity over `⊕` (`sandwich_comm`, `sandwich_assoc`,
`sandwich_oplus`).
- `∥` is `+` through the reciprocal (`par_eq_sandwich`).
- `*` is `qtimes 0 1` through `T(p, q) ↦ T(p − q, q)` (`times_eq_sandwich`).
- The light-cone map, of determinant 2, takes `⊚` into `*` (`lightConeMap_splitTimes`). It is a
  homomorphism and not an isomorphism, which is `split_not_prod` again.

Conjugating by an invertible matrix keeps every discriminant (`disc_conj`), so a sandwich moves a
product's fixed points and keeps its type. The model's `E` is the complex Cayley transform. It sends `⊗` to
multiplication on the unit circle, since `z(x ⊗ y) = z(x) ⊗ z(y)` and `N(x ⊗ y) = N(x)·N(y)`
(`doubleAngle_otimes`, `norm_otimes`).

### Where classical formulas collapse

**`⊗` is tangent addition, without the collapse** (`T/TangentAddition.lean`). Written with fraction
arithmetic, `tan(α + β) = (x + y)/(1 − x·y)` is `x ⊗ y` with both coordinates multiplied by `x.q · y.q`
(`tanAdd_eq`). So it lands on `0ω` exactly when a denominator is zero (`tanAdd_eq_zeroOmega_iff`), while
`⊗` lands on `0ω` only from `0ω` (`otimes_eq_zeroOmega_iff`). At a quarter turn the classical formula
forgets the other angle entirely, and `⊗` forgets nothing (`quarterTurn_contrast`). For example,
`ω ⊗ 1 = _1`, where the formula gives `0ω`. A quarter turn in the *result* is not a collapse:
`tan(45° + 45°)` gives `T(2,0)` both ways. Where `x.q · y.q < 0`, the formula's answer is on the opposite
ray: `_1 ⊗ 1 = T(0,-2)`, at 180°, where it gives `T(0,2)`, at 0°.

**`⊚` is velocity addition, in the same way** (`T/Velocity.lean`). `(u + v)/(1 + u·v)`, with `1` as the
speed of light, is `x ⊚ y` scaled by `x.q · y.q` (`velAdd_eq`). The formula divides by zero in three
places:
- `uv = −1` is a pole, not a collapse, and both sides answer `T(k, 0)`.
- An argument with `q = 0` collapses the formula to `0ω`, and `⊚` loses nothing (`infinity_contrast`).
- The two light lines are `⊚`'s own zero divisors. In light-cone coordinates `(q + p, q − p)` it
  multiplies coordinatewise (`lightCone_splitTimes`), so `x ⊚ y = 0ω` exactly when each light-cone
  coordinate is zero in one of the two (`splitTimes_eq_zeroOmega_iff`). `1 ⊚ -1 = 0ω` is `c` plus `−c`,
  where the classical formula is `0/0` too.

`1 ⊚ y` is a multiple of `1` for every `y` (`one_splitTimes`): light plus any velocity is light.

**The parallel sum's two classical forms differ.** `1/(1/x + 1/y)` is `∥` exactly, and `xy/(x + y)` is
`∥` scaled by `x.q · y.q` (`parAdd_eq`). So the second collapses against an open circuit, where
`ω ∥ y = y` (`open_contrast`).

### Loss and recovery

Given a result and one operand, when does the other come back exactly? (`T/Recovery.lean`)

| operation | the other operand comes back exactly when the known one is |
|---|---|
| `⊕` | anything |
| `⊗` | anything but `0ω` |
| `+` | a pair with a non-zero denominator |
| `*` | a pair with neither coordinate zero |
| `⊚` | a pair off the light lines, `p² ≠ q²` (`splitTimes_recoverable_iff`) |
| `∥` | a pair with a non-zero numerator (`par_recoverable_iff`) |

Where it doesn't come back, every operand has a distinct partner that gives the same result. So the loss
is the operation being ambiguous there, not an inverse that is too weak.

**One norm decides every row but `⊕`** (`T/Norm.lean`). The other operand comes back exactly when `k`'s
norm is non-zero (`recoverable_iff_norm`), and `k` has an inverse exactly when the norm is `±1`
(`exists_inverse_iff_norm`).

| product | norm of `k` | has an inverse exactly at |
|---|---|---|
| `⊗` | `p² + q²` | the four seeds (`exists_otimes_eq_zero_iff`) |
| `+` | `q²` | every `T(p, ±1)` (`exists_plus_eq_zero_iff`) |
| `⊚` | `q² − p²` | the four seeds again (`exists_splitTimes_eq_zero_iff`) |
| `*` | `pq` | `1, _1, -_1, -1` (`exists_times_eq_one_iff`) |
| `∥` | `p²` | every `T(±1, q)` (`exists_par_eq_omega_iff`) |

The same norm decides where each ring's exact inverse fails one level up (`Nested/QuadPoint.lean`, in
[Two readings, and the inverse one level up](#two-readings-and-the-inverse-one-level-up)).

**Every product loses at most one integer** (`T/Loss.lean`). Against `k ≠ 0ω` of norm zero, a result
`r = x · k` satisfies `k.p · r.q = k.q · r.p`, so the whole result is its numerator, one linear form in
`x` (`qtimes_eq_qtimes_iff`). Keeping `x.p` beside it gives `x` back (`qtimes_recover_with_numerator`).

| product | against | keeps | loses |
|---|---|---|---|
| `+` | `T(c, 0)` | `x.q` | `x.p` |
| `⊚` | `T(c, c)` | `x.q + x.p` | `x.q − x.p` |
| `⊚` | `T(c, −c)` | `x.q − x.p` | `x.q + x.p` |
| `*` | `T(c, 0)` | `x.p` | `x.q` |
| `*` | `T(0, c)` | `x.q` | `x.p` |
| `∥` | `T(0, c)` | `x.p` | `x.q` |

Against `0ω` every product loses both integers.

**`*` is the only product with projections** (`T/Projection.lean`). In the family `ω² = a + b·ω`, an
idempotent other than the zero and the unit exists exactly when `b² + 4a = 1` (`qtimes_idempotent_iff`).
That is ℤ × ℤ, where `ω` and `0` split a pair into its coordinates: `(x * ω) ⊕ (x * 0) = x`
(`times_omega_oplus_times_zero`). What `*` loses against a pair on an axis is exactly one projection, and
keeping the other gives the operand back (`times_recover_with_complement`).

### Angles and the mediant

**The angle column** (`T/Angle.lean`). `θ(x) = arg(q + p·i)` is a real in `(−π, π]`, and `tan θ = p/q` for
every pair (`tan_theta`). At a quarter turn both sides are Lean's `x/0 = 0`. The nine named values have
the angles of the model's table (`theta_zero`, …, `theta_negOne`). `0ω` has no angle, and the theorems
below exclude it. As an angle mod `2π`:

| operation | angle |
|---|---|
| `x ⊗ y` | `θx + θy` (`angle_otimes`) |
| `-x` | `−θx` (`angle_neg`) |
| `-_x` | `θx + π` (`angle_oplusInverse`) |
| `1/x` | `π/2 − θx` (`angle_reciprocal`) |
| `⊗` power `n` | `n·θx` (`angle_otimesPowNat`) |
| `principal x` | `θx` or `θx + π`, with the same tangent (`angle_principal`, `tan_theta_principal`) |

**The angle is the ray.** Two pairs other than `0ω` have the same θ exactly when they are positive
multiples of one pair (`theta_eq_theta_iff_sameRay`), which is when `det x y = 0` and `dot x y > 0`
(`theta_eq_theta_iff`).

**The mediant lies between.** The angle from `x` to `y` turns the way the sign of `det x y` says
(`sign_angle_sub`). `det x (x ⊕ y)` and `det (x ⊕ y) y` both equal `det x y`, so `x ⊕ y` turns from `x` the
way `y` does, and turns into `y` the same way (`mediant_between`).

**The power off the integers** (`T/AnglePower.lean`). `T(a,b)^r = tan(r·θ)` at any real `r`
(`anglePow`). At every integer `n` it is the ratio of `otimesPower x n` (`anglePow_intCast`). The model's
`tan((c/d)·arctan(a/b))` agrees with it at the integers wherever `b ≠ 0` (`arctanPow_intCast`), because
`arctan(a/b)` is `θ` up to half turns. At `r = 1/2` the half turn shows. `_1` and `-1` have one ratio, so
`arctan` gives both of them `tan(−π/8)`, while their angles give `tan(3π/8)` and `tan(−π/8)`
(`arctanPow_underOne_ne`). So off the integers the exponent reads the angle and not the ratio. It also
leaves the pairs: `1^(1/2) = tan(π/8)` is no pair's ratio (`anglePow_one_half_ne`), and no `y ⊗ y` has the
angle of `1` (`theta_otimes_self_ne_theta_one`). Some halves stay: `ω^(1/2) = 1` (`anglePow_omega_half`).

**The spin cover** (`T/Spin.lean`). Under `⊗` a pair turns and scales, so only the four units are
rotations as they stand. Its square `x ⊗ x` has norm `N²`, which divides out exactly: `rot x` is the matrix
of `(q² − p², 2pq)/N`, rational, orthogonal, with determinant one (`rot_mem_specialOrthogonalGroup`).
`rot (x ⊗ y) = rot x * rot y` for every pair (`rot_otimes`), so rotations compose as pairs and the squaring
can wait until the end. Off `0ω`, two pairs give one rotation exactly when `det x y = 0`
(`rot_eq_rot_iff`): `x` and `-_x` give the same one, the double cover. Every rotation with rational
entries is some `rot x` (`rot_surjective`). Read classically it is the rotation by `2θ` (`rotCos_eq_cos`,
`rotSin_eq_sin`), the only place π enters.

**The winding count** (`T/Winding.lean`). Whether a pair's turn `θ/2π` is below a rational `a/b` is
decided in integers. Walk the `⊗` powers `x, …, x^b` and count the steps whose numerator goes from negative
to non-negative. For a pair in the upper half-plane each step is under a half turn, so none crosses
uncounted, and the count is `⌊b · turn x⌋` (`winding_eq_floor`). So `turn x < a/b` exactly when the count is
below `a` (`turnLt_iff`). Doubling the walk doubles the count, plus one if the half-way power is in the
closed lower half-plane (`winding_double`), so `powWind` finds the count in `O(log b)` products
(`powWind_eq`).

**Dialing a turn** (`T/Dial.lean`). From `(0, ω)`, the mediant replaces whichever end the target is past:
`L' = L ⊕ s·R`, `R' = R ⊕ (1 − s)·L`, with `s` the test's bit. For any target in `(0, 1/4]` the ends stay
neighbours, `det L R = 1` (`det_dial`), and the target stays between them, `turn L < a/b ≤ turn R`
(`dial_bracket`). The width is exact in integers, `sin²(θR − θL) = 1/(N(L)·N(R))` (`sin_sq_dial`), and closes:
`(turn R − turn L)² ≤ 1/(16(n + 1))` after `n` steps (`turn_width_dial`).

**Rational trigonometry** (`T/RationalTrig.lean`). `cosTurn a b n` and `sinTurn a b n` are rationals: dial
half the turn past its quarter turns, turn by `ω` for an odd quarter, and square. They are exactly on the
unit circle (`cosTurn_sq_add_sinTurn_sq`), and within `π/√(n + 1)` of `cos(2π·a/b)` and `sin(2π·a/b)`
(`cosTurn_err`, `sinTurn_err`). The computation is integers, floor division and one comparison per step;
π is only in the error statements.

**The mediant from the four seeds** (`T/MediantTree.lean`). The model's last line says every traction
other than `0ω` is reached exactly once by iterated mediant from the four seeds. Inserting `⊕` between
neighbours, starting from `0, ω, _0, -ω` around the circle, first gives `1, _1, -_1, -1`, the table of nine.
Nothing is reached twice (`reach_injective`), and the pairs reached are exactly those with
`gcd(p, q) = 1` (`range_reach`). So the line holds up to the ray: every pair except `0ω` is a positive
multiple of exactly one reached pair (`exists_unique_reached_ray`). The proof runs on `det`: neighbouring
seeds have determinant 1, the mediant preserves it, and going down the tree is Euclid's algorithm.

### The tower: quotients, division, and a second level

**The mediant survives no quotient** (`T/Quotient.lean`). For every multiplicative set `S` the quotient
`s·x ~ t·y` is a wheel (`Q.isWheel`), and `+`, `*`, `/`, `-`, `-_` and `⊗` survive it. `⊕` survives only
`S = {1}`, which identifies nothing, and `0 ∈ S`, which identifies everything (`oplus_respects_iff`).

**The mediant and division cannot share an equality** (`T/NoDivision.lean`). Take any equivalence that
`⊕` and a product both respect, in which every pair other than `0ω` has an inverse. It identifies every
pair with every other (`no_division_with_oplus`, for all five products). So division for the `⊕` rings
has to come from the level above.

**A pair of pairs** (`CottLean/Nested/Basic.lean`). `T2(p, q)` is a traction whose coordinates are
tractions, under fraction arithmetic. `T` sits inside it as `T(a,b) ↦ T2(T(a,1), T(b,1))`, respecting `+`,
`*`, `-` and the reciprocal exactly (`of_plus`, `of_times`, `of_neg`, `of_reciprocal`). The projection
`flatten` reads `T2(A, B)` as `A / B`. It respects `*`, `-` and the reciprocal, and `+` up to one residue
(`flatten_plus`), exactly on the image of `T`. With `B` fixed it is the Möbius transformation
`[[B.q, 0], [0, B.p]]` of the numerator (`flatten_eq_act`), so dividing by `B` respects `⊕`, and the
numerator comes back exactly when `B` is off both axes (`flatten_recoverable_iff`).

**`p/0 = tan(arg(p·i))`** (`CottLean/Nested/DivZero.lean`). This is the model's first line at `q = 0`. For
an integer `p` it sees only the sign, `arg(p·i) = ±π/2`, and in Lean it answers `0`
(`tan_arg_intCast_mul_I`). For a pair it is the quarter turn `p ⊗ ω = T(b, −a)`, and `tan` of it is the
perpendicular slope `−b/a` (`tan_arg_mul_I`). It loses nothing (`divZero_injective`), so at a zero
denominator it keeps the numerator that `flatten` drops (`divide_zero_injective`). Only `⊗ −ω` undoes it,
not `· 0`. On parallel lines, Cramer's numerator runs along both lines (`along_line_of_parallel`). The rule
answers along the normal instead (`rule_normal_of_parallel`): the `·i` is one quarter turn too many once
`p` is already a pair. Without it, `p/0 = p` read by `tan(arg p)` is the point at infinity of homogeneous
coordinates, and the parallel-lines results are the projective-geometry ones: this section restates prior
art rather than extending it. What it adds is that the two rules agree on integers, since `n` over zero is
the pair `T(n, 0)` (`tan_arg_divAlong_intCast`), so the `·i` of the model's first line is the step from an
integer over zero to a pair. The rule without it lies along parallel lines
(`divAlong_along_of_parallel`), and its slope is the meeting point's wherever the lines do meet, so it
answers the same on both sides of `D = 0` (`slope_meet_eq_tan_arg_divAlong`).

**A pair of pairs of pairs** (`CottLean/Nested/T3.lean`). `T3(P, Q)` has `T2` coordinates under the same
fraction arithmetic. `T2` embeds respecting every operation, and a flat pair taken two levels up over unit
denominators computes exactly what the flat pair does (`flatten2_plus_of_of`). The projection
`flatten : T3 → T2` respects all but `+`, and `+` survives up to the same law as one level down, moved up a
level: both coordinates are multiplied by the pair `x.q.q · y.q.q` where below they were multiplied by an
integer (`flatten_plus`). Down to `T` the two residues compound (`flatten2_plus`). Read in one step, the
numerator is the product of the leaves an even number of denominator steps down and the denominator of the
odd ones (`flatten2_def`). With `Q` fixed, the numerator comes back only when all four integers of `Q` are
non-zero (`flatten_recoverable_iff`), where level 2 needed two.

**Starting from all ones** (`CottLean/Nested/Ones.lean`). `· 1` is the identity at every depth, and in `T`
`+ 1` loses nothing (`plus_one_injective`). From `T2` on, `+ 1` erases: `X` comes back from `X + 1`
exactly when the denominator `X.q` is off the axis of `ω` (`T2.plus_one_recoverable_iff`). In particular
`a/ω + 1 = ω/ω` for every `a` (`T2.held_plus_one`), so the held form of `a · 0` does not survive adding
`1`. `1 + (−1) = 0` at every depth, and then `0 ·` erases exactly one integer, the leaf reached by taking
the numerator at every step: one of two, four and eight in `T`, `T2` and `T3` (`T3.zero_times`).

**A zero that adds a layer** (`CottLean/Nested/Epsilon.lean`). Let a component that meets a zero gain a
layer, `(a, b) · (0, 1) = ((0, a), b)`, and read an inner pair `(x, y)` as `x + ε·y`. The layers are then
Horner form, and holding is multiplying by `ε` (`Nest.eval_hold`). `TE` is `T` over `ℤ[ε]`: `T` sits inside
exactly, `x · 0` is the rule (`of_times_zero`), and neither `· 0` nor `· ω` loses anything
(`times_zero_injective`). `0 · 0` is not `0` (`zero_sq_not_equiv`), and `x · 0 · ω` is `x` again
(`times_zero_times_omega`). A common `ε` cancels exactly (`cancel_step`), and once the denominator is
non-zero at `ε = 0`, setting `ε = 0` respects `+`, `·` and `−` and gives the classical value (`st_plus`,
`st_of`). The zero that `+` produces, `1 + (−1)`, cannot be held, since in any ring `a · 0 = b · 0`
(`additive_zero_erases`). With one `ε`, `0/0 = 1` (`zero_div_zero`). This is the formal infinitesimal of
`ℚ(ε)`, and the standard part is `ε → 0`; what the model adds is that its nested pairs, read by Horner, are
the rule.

**Which laws make `m · (n − n)` erase `m`** (`CottLean/Nested/NoRing.lean`). In an additive group, the one
instance `m · (0 + 0) = m·0 + m·0` of left distributivity forces `m · 0 = 0` (`left_distrib_zero`), and so
does distributing over any cancelling sum with the sign rule (`cancel_sum`). On the right, `z + z = z` gives
`2 · z = 1 · z` (`right_distrib_zero`). And a multiplication that agrees with a field's away from `0` and
loses nothing has `0 · m = 0` (`field_no_room`): the zero needs an element the field does not have.

**Room for the zero** (`CottLean/Nested/Hotel.lean`). Take a field and a corridor of distinct non-zero
elements `e 0, e 1, …`, in the model `ε, ε², …`. The carrier is the non-zero elements under the field's `·`,
and `+` is the field's moved one room along the corridor: `0 ↦ e 0`, `e k ↦ e (k + 1)`. Both are commutative
groups. `n + (−n) = 0` erases `n` (`Held.universal_invariant`), while multiplying by any element, the zero
included, loses nothing (`Held.mandate`), `0 · 0 ≠ 0`, and the zero has an inverse. Distributivity fails
(`Held.not_left_distrib`, as it must), holds wherever every value is off the corridor
(`Held.distrib_of_plain`), and holds after the standard part, which respects both `+` and `·` on finite
elements (`Held.st_add`, `Held.st_mul`, `Held.st_distrib`). The Laurent series over `ℚ` are a model
(`laurent`, `laurent_infinitesimal`).

### Two readings, and the inverse one level up

**The two readings agree on ℤ and nowhere else** (`T/Readings.lean`). Of the six readings, the integer
arithmetic of `T` is built on two, `Q` and `C`. The integer `n` is `T(n, 1)` in the ratio reading and
`T(0, n)` in the complex reading. Each copy respects its own reading's operations
(`ratioInt_plus`, `ratioInt_times`, `complexInt_oplus`, `complexInt_otimes`). The maps between them are
written in the model's operations, `0 / x` one way and `1/y ⊕ 0` the other, and they invert each other on
the integers (`toComplex_ratioInt`, `toRatio_complexInt`). `T(0, 1)` is in both copies, as the ratio `0`
and the complex `1`, and no other pair is (`ratioInt_eq_complexInt_iff`). The readings are not
isomorphic. No injective map takes `+` to `⊕`, since `ω + 0 = ω + 1` and `⊕` cancels
(`not_plus_embeds_oplus`). No injective map takes `*` to `⊗`, since `ω * 0` and `0 * ω` are both `0ω`
and ℤ[i] has no zero divisors (`not_times_embeds_otimes`).

**The complex reading has no inverse of its own.** `1/(q + p·i) = (q − p·i)/(p² + q²)`, and a Gaussian
integer has nowhere to keep the denominator. `T/Drift.lean` carries both readings side by side with the
conjugate standing in for the inverse. The gap between the two sides is additive and obeys a product rule
(`drift_add`, `drift_mul`), and most of it is the missing denominator.

**With ratio coordinates the inverse is exact** (`Nested/Point.lean`). Read `T2(A, B)` as the point
`B + A·i`, with `A` and `B` ratios. `⊕` and `⊗` are the flat formulas with `T`'s `+`, `*` and `-` inside
each coordinate. On values they are the sum and product of ℚ(i), and
`1 / T2(T(a,b), T(c,d)) = T2(T(−a·b²·d², b·D), T(c·b²·d², d·D))` with `D = a²d² + b²c²` is its inverse
(`val_oplus`, `val_otimes`, `val_pointInv`, `pointInv_eq`). Multiplying back gives
`T2(T(0, k), T(k, k))` with `k = (b·d·D)²`: `1`, scaled by one integer, over the residue `T(0, k)`
(`otimes_pointInv`). `k` is zero exactly when a coordinate has a zero denominator or the point is zero
(`inverse_residue_eq_zero_iff`). A Gaussian integer gets the inverse it lacked, `(q − p·i)/(p² + q²)`
(`pointInv_ofPoint`). A flat ratio `x = T(p, q)`, read as the real point `T2(0, x)`, gets `T`'s
reciprocal scaled by `p·q` (`pointInv_ofRatio`). So the complex inverse collapses to `0ω` exactly where
`* x` cannot be undone in the ratio reading (`pointInv_collapses_iff_times_ambiguous`). At `1/0` the
ratio reading answers `ω` and the point reading `0ω` (`pointInv_ofRatio_zero`).

**Every quadratic ring, the same way** (`Nested/QuadPoint.lean`). Read `T2(A, B)` as `B + A·ω` with
`ω² = a + b·ω`. Write `A = T(u, v)` and `B = T(s, t)`. The norm with the denominators cleared is
`M = s²v² + b·uvst − a·u²t²`. The inverse, the conjugate `(B + b·A) − A·ω` over the norm, is
`T2(T(−u·v²·t², v·M), T((sv + but)·v·t², t·M))` (`qinv`). At `ω² = −1` the product and inverse are
`Point`'s, coordinate for coordinate (`qmul_gaussian`, `qinv_gaussian`). For every `a` and `b`:

- `z · (1/z) = T2(T(0, k), T(k, k))` with `k = (v·t·M)²` (`qmul_qinv`).
- `k` is zero exactly at a zero denominator or a zero norm (`qinv_residue_eq_zero_iff`).
- On integer points `M` is the flat norm, so the inverse collapses exactly where the flat product cannot
  be undone (`qinv_ofPoint_collapses_iff`): only at `0ω` for `⊗`, on the light lines for `⊚`, and at
  `q = 0` for the dual numbers.
- Read into `QuadraticAlgebra ℚ a b`, the product is the ring's, and the inverse is its inverse wherever
  the denominators and the norm are non-zero (`qval_qmul`, `qval_qinv`).

**ℚ(i) as a ratio of complex numbers** (`T/Over.lean`, `Nested/RatioPoint.lean`). `TOver R` is `T`'s
value-position formulas over any commutative ring. Over ℤ it is `T`, with each operation carried across
as `rfl` (`ofT_plus` and the rest). Over the Gaussian integers it is `T(C, C)`, a ratio `z / w`, holding
the same values as `C(T, T)` above. On values `·` and the reciprocal are ℚ(i)'s product and inverse, and
so is `+` where both denominators are non-zero (`val_times`, `val_reciprocal`, `val_plus`). Two maps
connect the constructions. `rationalize` multiplies through by the conjugate of the denominator,
`z·w̄ / N(w)`. `combine` puts both coordinates over one denominator, `(cb + ad·i) / (bd)`. Both keep every
finite value (`val_rationalize`, `val_combine`), and the two inverses agree through them
(`val_rationalize_reciprocal`). Neither is the identity on coordinates. Each round trip multiplies the
coordinates by a residue (`combine_rationalize`, `rationalize_combine`).

**What each construction keeps** (`Nested/Compare.lean`). Asking `Recovery`'s question of both:

| | `C(T, T)`, a complex number of ratios | `T(C, C)`, a ratio of complex numbers |
|---|---|---|
| `+ k` undone exactly when | both denominators of `k` are non-zero (`oplus_cancel_iff`) | the denominator of `k` is non-zero (`plus_cancel_iff`) |
| `· k` undone exactly when | never (`otimes_never_injective`) | neither coordinate of `k` is zero (`times_cancel_iff`) |
| `1/x` | the conjugate over the norm | a swap |
| `x · (1/x)` | `1` scaled by `(b·d·D)²` | `1` scaled by `z·w` (`times_reciprocal_self`) |
| at infinity | an infinite coordinate beside a finite one | one point `z / 0` for every direction `z` |

The product of `C(T, T)` sees `c/d + (a/b)·i` only through `a·d`, `b·d` and `c·b` (`otimes_eq_int`). Four
integers go in and three come out. So a factor moves between the two coordinates without changing any
product (`otimes_transfer`), and `⊗ K` loses information against every `K`, `1` included. Where `K` is
finite with a non-zero norm, that is all it loses (`otimes_eq_otimes_iff`). Those three numbers are exactly
`combine`'s coordinates (`combine_eq_iff`), and `combine` carries `C(T, T)`'s product to `T(C, C)`'s, scaled
by its own denominator (`combine_otimes`). So `C(T, T)`'s product is `T(C, C)`'s, read through `combine`.
`rationalize` loses something else: it identifies `z / w` with `u·z / u·w` for each unit `u`
(`rationalize_eq_iff`, `rationalize_unit`). At infinity, `rationalize` sends every direction `z / 0` to
`T2(0ω, 0ω)` (`rationalize_infinite`). `combine` sends exactly the points with an infinite coordinate to a
zero denominator (`combine_q_eq_zero_iff`), and an infinite imaginary part drops the real part
(`combine_imag_infinite`).

**Complex coordinates: the bicomplex integers** (`Nested/Bicomplex.lean`). `C(C, C)` reads a pair of
Gaussian integers as the point `B + A·j`. It is `QuadraticAlgebra ℤ[i] (−1) 0` (`toQuad_otimes`), with two
square roots of `−1`. A flat point placed on the inner `i` and on the outer `j` carries `⊕` and `⊗` exactly
either way (`ofInner_otimes`, `ofOuter_otimes`), and the two placements differ (`inner_ne_outer`). Reading
`j` as `i` makes them coincide, so that reading is not injective (`evPlus_inner_eq_outer`,
`evPlus_not_injective`). Reading `j` as `i` and as `−i` together loses nothing (`ev_injective`), but the
pair does not reach `(1, 0)` (`ev_not_surjective`), as `split_not_prod` found for ℤ[j]. `(i·j)² = 1`, so
`(1 + ij)(1 − ij) = 0` (`zero_divisors`), and `T(p, q) ↦ C(p·i, q)` carries `⊚` to `⊗` (`ofSplit_otimes`).
Angle addition and velocity addition are one product here. The norm `B² + A²` is itself a Gaussian
integer, and `z ⊗ conj z` leaves it standing (`otimes_conj`). `⊗ k` can be undone exactly when it is
non-zero (`otimes_cancel_iff`), which fails on the light lines `B = ±i·A` (`nrm_eq_zero_iff`). Through each
placement it is that flat product's norm: `p² + q²`, `q² − p²` and `(q + p·i)²` (`nrm_ofOuter`,
`nrm_ofSplit`, `nrm_ofInner`).

**The bicomplex inverse** (`Nested/BicomplexRatio.lean`). `C(T(C, C), T(C, C))` gives each coordinate of
the bicomplex point its own denominator, a ratio of Gaussian integers, and uses `Point`'s formulas word for
word. Write `A = T(u, v)`, `B = T(s, t)` and `D = u²t² + v²s²`. The inverse is
`C(T(−u·v²·t², v·D), T(s·v²·t², t·D))` (`inv_eq`), and `z ⊗ (1/z)` is `1` scaled by one Gaussian integer
`k = (v·t·D)²` (`otimes_inv`), which is zero exactly at a zero denominator or `D = 0`
(`inv_residue_eq_zero_iff`). In `Point` the matching `D` is a sum of two squares, zero only at the zero
point. Here it factors as `(vs + i·ut)(vs − i·ut)` and is zero on the light lines `B = ±i·A`
(`den_eq_mul`, `den_eq_zero_iff`). The other three corners sit inside it:

- `C(C, C)` carries `⊕` and `⊗` across exactly (`ofCC_oplus`, `ofCC_otimes`). Its points get the inverse
  `(B − A·j) / (B² + A²)` (`inv_ofCC`), which collapses exactly where `C(C, C)`'s `⊗` cannot be undone
  (`inv_ofCC_collapses_iff`). The zero divisor `1 + i·j` gets `C(−i/0, 1/0)`, and multiplying back gives
  `C(0/0, 0/0)` (`otimes_zeroDivisor_inv`).
- `C(T, T)` carries `⊕`, `⊗` and its inverse across exactly (`inv_ofT2`), so `Point`'s `i` is this `j`.
- The inverse of a real `T(C, C)` value is its swap scaled by its residue `z·w` (`inv_ofTC`). That is the
  split `Point` found between its two inverses.

Read into the bicomplex numbers `QuadraticAlgebra ℂ (−1) 0`, `⊕` and `⊗` are their sum and product, and
`inv` is the inverse wherever the denominators and `D` are non-zero (`val_oplus`, `val_otimes`, `val_inv`).
The light lines are not a defect of the encoding. A finite point is a unit exactly when `D ≠ 0`
(`isUnit_val_iff`), and on the light lines `z · conj z = 0` (`val_otimes_conj`).

The four ways to nest the two readings:

| | ratio coordinates | complex coordinates |
|---|---|---|
| **read as a ratio** | `T(T, T)` = `T2`: a ratio of ratios, with values in ℚ | `T(C, C)`: ℚ(i); the inverse is a swap |
| **read as a point** | `C(T, T)`: ℚ(i); the inverse is the conjugate over the norm | `C(C, C)`: the bicomplex integers, with zero divisors on the light lines; over `T(C, C)` coordinates they get an exact inverse everywhere else |

**How the corners fit together** (`Nested/Embeddings.lean`). Every route up from flat `T` to
`C(T(C, C), T(C, C))` lands on the same point. A flat point goes through `C(T, T)` or through `C(C, C)`
(`face_point`), a point on the inner `i` through `C(C, C)` or `T(C, C)` (`face_inner`), and a flat ratio
through `C(T, T)` or `T(C, C)` (`face_ratio`). On real ratios `combine` is just the cast (`face_combine`),
while `rationalize` comes back only up to a residue (`rationalize_castT`). ℚ(i) sits in the top corner
twice: `ofT2` puts the imaginary part on the outer `j` and carries `⊗` exactly, and `ofTC ∘ combine` puts
the whole number on the inner `i` and carries `*` up to the residue `T(0, w₁·w₂)` (`ofTC_times`). The two
copies agree exactly on the real axis (`val_outer_eq_inner_iff`). Reading `j` as `i` identifies them, and
reading it as `−i` makes them complex conjugates (`evP_outer`, `evM_outer`). That is `Bicomplex`'s inner
and outer placement, one level up. Over ℂ the two readings of `j` together are a ring isomorphism from the
bicomplex numbers onto `ℂ × ℂ` (`split`). On the integers it is `Bicomplex`'s two evaluations
(`split_val_ofCC`), and the `(1, 0)` that ℤ misses is the value of `C(−i/2, 1/2)`, the idempotent
`(1 − i·j)/2` (`split_val_half`). With unreduced coordinates it is idempotent up to scaling every coordinate
by `8` (`otimes_half`). The light lines are the two axes of `ℂ × ℂ`: a finite point has `D ≠ 0` exactly when
neither evaluation is zero (`den_ne_zero_iff`), and the zero divisor `1 + i·j` goes to `(0, 2)`. Because of
the zero divisors, no injective map from `C(C, C)` to a domain is multiplicative
(`not_otimes_embeds_domain`). In particular none takes its `⊗` to flat `⊗` (`not_otimes_embeds_flat`).

### The mediant on integer hardware

**Registers keep `⊕`** (`T/Registers.lean`). A `w`-bit register is the ring `BitVec w`, and wrapping both
coordinates respects `⊕`, `+`, `*` and `⊗` (`wrapPair_oplus` and the rest). Reduction modulo `2^w` is a
quotient that `⊕` survives, unlike every quotient of `T/Quotient.lean`: it identifies pairs whose
difference is divisible, not pairs that are multiples of each other (`wrapPair_eq_iff`). The scatter
that sums these pairs on a GPU, and why every schedule of it gives one grid, is proved in
[vexelray-lean-proofs](https://github.com/sibarum/vexelray-lean-proofs).

### Next to the division-by-zero literature

`T(p,q) ↦ p/q`, with every `T(p,0)` going to the error element, maps T onto the rational common meadow
(`T/CommonMeadow.lean`). It respects `+`, `*` and `-` exactly, and the reciprocal everywhere but at the
quarter turns, and no map onto the common meadow respects all four (`no_surjective_hom_Qa`). Bergstra and
Ponse's fracpairs are T with the reciprocal multiplied by the denominator (`T/Fracpair.lean`,
`finv_eq_scale`). Every law of the model that differs from its written form differs by one added residue
`T(0,k)`, where `x + T(0,k)` is `x` with both coordinates multiplied by `k` (`T/Residue.lean`,
`plus_residue`).

### The model's laws, stated exactly

These are the model's laws, with the exact coordinate result wherever it differs from the law as written.

| law | result | file |
|---|---|---|
| `(x ⊕ y) ⊗ z = (x ⊗ z) ⊕ (y ⊗ z)` | exact | `Gaussian` |
| `(x + y) * z = (x * z) + (y * z)` | the right side is the left with both coordinates multiplied by `z.q`, which is the wheel's distributive law (`distrib_scaled`) | `Fraction` |
| `(T^m)^n = T^(m·n)` | exact, both signs | `Powers` |
| `T^(m+n) = T^m ⊗ T^n` | exact for same-sign exponents; otherwise off by `(p²+q²)^min(\|m\|,\|n\|)`, one norm per cancelled turn (`otimesPower_add`) | `Powers` |
| each operation against its inverse | `⊕` lands on `0ω` exactly; `⊗`, `+` and `*` land on `T(0, p²+q²)`, `T(0, q²)` and `T(pq, pq)`; `⊚` on `T(0, q²−p²)` | `Gaussian`, `Fraction`, `Velocity` |
| `z(T) = T(2ab, b²−a²)`, "a unit vector" | `z(T) = T²`, with norm `(a²+b²)²`, so `z(T)/(a²+b²)` is the unit vector, and that is `E(T)` (`mobius_eq`, `doubleAngle_norm`) | `Mobius` |

### The law atlas

`T/Atlas.lean`. Pair any addition `A` with any multiplication `M` among `⊕`, `+`, `*`, `⊗`, `⊚` and `∥`,
each with its own unit and inverse, and grade sixteen laws. The grades are `exact`, `ray` (a positive
multiple), `ratio` (a non-zero multiple), `par` (`det = 0`) and `fails`, and each cell has two: one over
all pairs, and one over generic pairs, off the axes and the light lines. `atlas` proves that every cell
of the 36 × 16 table is the strongest grade at which its law holds. The law holds there for every input,
and one of five fixed inputs fails every stronger grade (`witnesses_fail`, checked by `decide`).

- Eleven laws are exact in every pairing: both commutative, associative and unit laws, `-(x+y)`,
  `1/(xy)`, `--x`, `//x` and `(x/y)(z/w) = (xz)/(yw)` (`op_comm`, …, `op_frac`).
- Only `⊕` has an exact inverse. For each other operation, `x ∘ x⁻¹` is the unit scaled by `q²`, `pq`,
  `p² + q²`, `q² − p²` or `p²` (`inv_eq_scale`).
- Distributivity is exact exactly when `A` is `⊕` and `M` is not. It is off by a scale for `(+, *)` and
  `(∥, *)`, and fails for the other 29 pairings.
- `0·x = 0` is exact for `⊕` with every product but itself, off by a scale in nine pairings, and fails in
  the rest. `(−x)·y = −(x·y)` is exact in ten pairings and fails in the rest.

Every grade short of `fails` that is not exact comes from one side being the other scaled by a
polynomial `k`. Scaling by any `k` keeps `par`, by `k ≠ 0` keeps `ratio`, and by `k > 0` keeps `ray`
(`holds_par_scale`, `holds_ratio_scale`, `holds_ray_scale`). `scripts/LawAtlas.lean` reruns the grid
search and checks it against the proved `table` cell by cell.

## Not covered

- `L` has `⊗` as its `+`, but its `×` is a power, a nested pair. That no flat pair operation multiplies
  it is not proved; `P`'s case is (`no_homogeneous_P_add`).
- On real pairs `turn` is defined through Lean's `arg`, which is built from π. Only on integer pairs is it
  decided without π, by the winding count (`turnLt_iff_turn`), and that is for the upper half-plane.
- The `respected` column of `scripts/LawAtlas.lean`, whether each operation keeps the equivalence a
  pairing needs, is still a search result.
- Each operation's hyperoperation, the exponentials between operations, and rational exponents of every
  power but `⊗`'s, which `T/AnglePower.lean` has on the angle. These have been searched and worked by
  hand, but none of it is in Lean yet.
- The wheel axioms were checked against the statements on Wikipedia and nLab. Carlström's paper itself
  has not been read against them.
- The ratio reading's `*` is in the quadratic family only through another basis, so `Point`'s result for
  real ratios is proved on its own, not as a case of `QuadPoint`'s.
- The points at infinity of `T2`, in the terms `Compare` uses for the two constructions of ℚ(i).

## Files

| file | contents |
|---|---|
| `CottLean/T/Basic.lean` | the pair, the nine values, the operations |
| `CottLean/T/Gaussian.lean` | `⊕` and `⊗` are ℤ\[i] |
| `CottLean/T/Fraction.lean` | `+` and `*`; distributivity exactly; the same-ratio relation |
| `CottLean/T/Recovery.lean` | when an operand can be read back |
| `CottLean/T/Powers.lean` | the integer exponent laws |
| `CottLean/T/Mobius.lean` | `z`, `E` and `E⁻¹` |
| `CottLean/T/MediantTree.lean` | the mediant from the four seeds |
| `CottLean/T/Wheel.lean` | fraction arithmetic is a wheel; `0ω` across both |
| `CottLean/T/TangentAddition.lean` | `⊗` against the wheel's tangent addition |
| `CottLean/T/Quotient.lean` | the quotient by a multiplicative set; it is a wheel, and `⊕` does not survive it |
| `CottLean/T/CommonMeadow.lean` | T against the rational common meadow |
| `CottLean/T/Fracpair.lean` | Bergstra and Ponse's fracpairs, read in T |
| `CottLean/T/Residue.lean` | each law's discrepancy is one added residue `T(0,k)` |
| `CottLean/T/Dual.lean` | `⊕` with `+` is ℤ\[ε]; `⊕` with `*` is ℤ × ℤ |
| `CottLean/T/Quadratic.lean` | one product for every quadratic ring; split-complex; ℤ[j] is not ℤ × ℤ |
| `CottLean/T/Velocity.lean` | `⊚` against the wheel's velocity addition; the light cone |
| `CottLean/T/Parallel.lean` | the parallel sum `∥`; ℤ[ε] through the reciprocal |
| `CottLean/T/Norm.lean` | one norm decides recovery and inverses for every product; the two projections |
| `CottLean/T/Projection.lean` | the idempotents of every product; `*` alone has projections |
| `CottLean/T/Loss.lean` | what each product loses at a zero divisor, and the one integer that restores it |
| `CottLean/T/Angle.lean` | θ, `tan θ = p/q`, the table's angles, what each operation does to the angle; the angle is the ray; the mediant lies between |
| `CottLean/T/AnglePower.lean` | `tan(r·θ)` at any real exponent; the power at the integers; `arctan`'s half turn off them; `1^(1/2)` is no pair |
| `CottLean/T/Spin.lean` | the square of a pair as an exact rational rotation; composition; the double cover; every rotation of `SO(2, ℚ)` |
| `CottLean/T/Winding.lean` | the turn; comparing it with a rational by counting crossings; the count by squaring |
| `CottLean/T/Dial.lean` | the mediant descent toward a turn: neighbours, a certified bracket, its exact width, and its closing |
| `CottLean/T/RationalTrig.lean` | cosine and sine of a rational turn as rationals: exactly on the circle, with a proved error |
| `CottLean/T/PowerSum.lean` | `zⁿ = xⁿ + yⁿ` exactly; only `n = ±1` stay for every pair; `pⁿ = 2qⁿ`; Fermat at 3 and 4 |
| `CottLean/T/Atlas.lean` | the law atlas: every law, every pairing of an addition and a multiplication, graded and proved strongest |
| `CottLean/T/NoDivision.lean` | no equality lets `⊕` and division coexist, for any of the five products |
| `CottLean/T/Transform.lean` | Möbius transformations as matrices; every product as a family of them; discriminants, fixed points, sandwiches |
| `CottLean/T/Registers.lean` | a traction in `w`-bit registers: the wrap keeps every operation, `⊕` included; a quotient of differences |
| `CottLean/T/Readings.lean` | the integers in the ratio and complex readings; the maps between them; no isomorphism |
| `CottLean/T/Unquotiented.lean` | the readings of a real pair that need no π (complex, difference, sum, ratio, product), how they relate, and each one's embedding of a number |
| `CottLean/T/LogPair.lean` | the logarithm as a pair: a scale in any base and a turn; `⊗` adds both; the turn keeps the ray and is decided by the winding count |
| `CottLean/T/Radians.lean` | the bridge to radians: `1^t`, the point from the scale and the turn, `log` in base `e`, the angle, and every relation stated with π |
| `CottLean/T/PairAlgebras.lean` | each reading as the homomorphism of an algebra on the pairs; no flat addition for `P`; converting between `C` and `(S, D)`, and carrying a product across |
| `CottLean/T/Drift.lean` | both readings side by side, with the conjugate for the complex inverse; the drift between them |
| `CottLean/T/Over.lean` | `T`'s formulas over any commutative ring; `x · (1/x) = T(pq, pq)`; when `+` and `·` can be undone in a domain |
| `CottLean/Nested/Basic.lean` | `T2`, a pair of pairs: the embedding of `T`, the projection `flatten` as a Möbius transformation of the numerator, and `T2` against the common meadow |
| `CottLean/Nested/DivZero.lean` | `p/0 = tan(arg(p·i))`: sign-only on integers, the quarter turn on pairs, the numerator `flatten` loses at `0`, and parallel lines, with and without the `·i` |
| `CottLean/Nested/T3.lean` | `T3`, a pair of `T2`s: the embedding of `T2`, the projection's residue one level up, the two levels compounded into `T`, the leaves read by parity, and what a denominator erases |
| `CottLean/Nested/Ones.lean` | what erases against `1` at each depth, `a/ω + 1 = ω/ω`, and `0 ·` erasing one leaf at every depth |
| `CottLean/Nested/Epsilon.lean` | a zero that adds a layer: the Horner reading, `T` over `ℤ[ε]`, holding and releasing without loss, cancellation, and the standard part |
| `CottLean/Nested/NoRing.lean` | the laws that make `m · (n − n)` erase `m`, each isolated, and why the zero needs new room |
| `CottLean/Nested/Hotel.lean` | room for the zero: two groups on one carrier, `+` erasing and `·` never, distributivity after the standard part, and a Laurent-series model |
| `CottLean/Nested/Point.lean` | `T2` read as a point: ℚ(i), the exact inverse in integers, its residue, and where it splits from the reciprocal |
| `CottLean/Nested/QuadPoint.lean` | every quadratic ring over ratio coordinates: the inverse, its residue, and its collapse at the flat product's loss |
| `CottLean/Nested/RatioPoint.lean` | `T(C, C)`, a ratio of Gaussian integers: values, `rationalize` and `combine`, the round trips, the infinities |
| `CottLean/Nested/Compare.lean` | what each construction of ℚ(i) can undo, and exactly what each map identifies |
| `CottLean/Nested/Bicomplex.lean` | `C(C, C)`, the bicomplex integers: two units, the evaluations, zero divisors, `⊗` and `⊚` together, the complex norm |
| `CottLean/Nested/BicomplexRatio.lean` | `C(T(C, C), T(C, C))`: the exact bicomplex inverse, its residue, the light lines, the other three corners inside it, the bicomplex units |
| `CottLean/Nested/Embeddings.lean` | how the corners fit together: the commuting cube, ℚ(i) twice in the top corner, the bicomplex numbers as `ℂ × ℂ`, and what cannot embed |
| `scripts/LawAtlas.lean` | not part of the library: the grid search behind the atlas, checked against `T.Atlas.table` |
| `scripts/Declarations.lean` | not part of the library: writes `declarations.txt`, the name of every citable declaration. cott-engine cites these names, and CI fails if the file is out of date |
| `declarations.txt` | the generated list of every citable declaration, sorted |

## Building

Lean `v4.33.0` and Mathlib `v4.33.0`, pinned in `lean-toolchain` and `lakefile.toml`.

```
lake exe cache get
lake build
```

`lake exe cache get` downloads Mathlib's prebuilt files. Without it, the first build compiles Mathlib
from source.

## Checking the axioms

```
lake env lean AxiomCheck.lean
```

After a build, this walks every declaration in every `CottLean` module, not a chosen list. It fails if any
of them depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`. A `sorry` is the
axiom `sorryAx` and a `native_decide` adds one of its own, so either would fail it. On success it prints
how many declarations and modules it checked.

CI runs the build and this check on every push (`.github/workflows/build.yml`). It also regenerates
`declarations.txt` and fails if the committed copy differs.
