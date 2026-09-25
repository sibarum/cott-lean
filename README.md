# cott-lean

[![Build and check axioms](https://github.com/sibarum/cott-lean/actions/workflows/build.yml/badge.svg)](https://github.com/sibarum/cott-lean/actions/workflows/build.yml)

A Lean 4 formalization of **traction**, the number model of [cott-engine](../cott-engine), whose
`docs/Traction-Model.md` is the definitive statement of it.

A traction is a pair of integers `T(p, q)`, read as the ratio `p/q` and, at the same time, as the point
`q + p·i` in the plane:

```
T(p, q) = p/q ≈ tan(arg(q + i·p))
```

Nothing is reduced. `T(1,2)` and `T(2,4)` are different values, `q = 0` is allowed, and `0/0` is a value like
any other. On that one set of pairs, traction defines several arithmetics at once. The design goal is a
runtime in which a value can be read under any of them, and moving between them is always an explicit
conversion. This repository proves what each arithmetic is, which laws it keeps, and where it loses
information.

Every theorem holds for every pair; none is checked on a sample. Every declaration is machine-checked to
use only Lean's standard axioms, in CI (see [Checking the axioms](#checking-the-axioms)).

## What it shows

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
pairs of pairs. That level is begun here. Among the named invariants, the angle and the ray turn out to
be the same one, and the mediant always lies strictly between its two parents.

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
- the mediant as the one operation every ring shares and no quotient keeps.

## Reading the notation

- **No invariant is specified by default.** Two pairs are equal exactly when their coordinates are, so
  `T(1,2) ≠ T(2,4)`. The ratio, the ray (a positive multiple of both coordinates), the angle and the norm
  are invariants a use may specify, and a result that holds only under one of them says which. Away from
  `0ω`, the angle and the ray are the same invariant (`theta_eq_theta_iff_sameRay`).
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

### The mediant on integer hardware

These files apply `⊕` to vexelray-sim-fluid's particle-to-grid scatter, where a grid node accumulates the
conserved pair `(Σ w·m·v, Σ w·m)`. They are stated for any additive commutative monoid, so they hold for
`T` under `⊕` (`GaussianPosition`), for the three-field nodes of two dimensions, and for machine registers.
Under `⊕` a pair of pairs is four integers added coordinatewise, so nesting changes nothing here.

**Any schedule gives the same grid** (`Scatter/Accumulate.lean`). Atomic adds in any order that applies
each deposit once leave exactly the grid (`run_eq_grid`, `run_perm`). Summing groups first, as the
pre-reduced and segmented kernels do, gives it again (`grouped_eq_grid`), and so does the gather
(`gather_eq_grid`). The grid holds exactly the particles' total (`total_grid_particles`). Regrouping needs
only associativity (`grid_flatten`); the atomics' arbitrary order is what needs commutativity. An empty
node is `0ω` (`pairGrid_empty`).

**Wrapping registers cost nothing** (`Scatter/Wrap.lean`). A `w`-bit register is the ring `BitVec w`, and
the map from ℤ to it is a ring map, so the registers hold the wrap of the integer grid in every order
(`run_wrap`). Read back signed, a node is exact whenever its *final* total fits in `w` bits, however much
the partial sums overflowed (`read_exact`, `run_read_exact`); `2·K·D < 2^w` for `K` deposits of size at
most `D` is enough (`read_exact_of_bound`). Reduction modulo `2^w` is a quotient that `⊕` survives,
together with `+`, `*` and `⊗` (`wrapPair_oplus` and the rest), unlike every quotient of
`T/Quotient.lean`: it identifies pairs whose difference is divisible, not pairs that are multiples of each
other (`wrapPair_eq_iff`).

**Quantised shares conserve exactly** (`Scatter/Quantise.lean`). Three bilinear shares floored and the
fourth taking the rest sum to the particle's amount exactly (`sum_shares`). None is negative
(`shares_nonneg`), and each is within `(-1, 3)` quanta of exact (`share_error`). Rounding momentum
separately from mass can give a corner momentum with no mass, a multiple of `ω`
(`independent_rounding_omega`). Depositing the mass share times the velocity conserves momentum exactly
(`sum_momentumShares`), gives a massless node no momentum (`node_momentum_eq_zero`), and keeps each node's
velocity between its particles' (`node_velocity_between`).

**Any stencil, and the quadratic one** (`Scatter/Stencil.lean`). On any finite stencil, flooring every
share but one and giving that one, the remainder node, the rest conserves exactly
(`sum_remainderShares`), leaves no share negative (`remainderShares_nonneg`), and puts all of the floors'
error, under `n − 1` quanta on `n` nodes, on the remainder node (`remainderShares_error_self`). The
four-corner scheme is the case with the north-east corner as remainder (`shares_eq_remainderShares`).
Two-dimensional weights are a tensor of one axis's (`tensor`, `sum_tensor`), and the bilinear ones are the
linear ones tensored (`bilinear_eq_tensor`). MLS-MPM's quadratic B-spline weights sum to one for every
offset (`sum_quadratic`) and are non-negative on `[½, 3/2]`, the interval the kernel clamps to
(`quadratic_nonneg`), and not outside it (`quadratic_one_neg`). The centre of the 3×3 stencil always
weighs at least a quarter (`quadratic_center_ge`), so it is the node to take the remainder
(`quadraticShares`, `quadraticShares_center`).

**What floating point loses** (`Scatter/Rounding.lean`). In the standard rounding model with unit
roundoff `u`, a schedule is a tree of rounded additions, and one of depth `d` is within
`((1+u)^d − 1)·Σ|a|` of the exact sum (`eval_error`). Two schedules differ by at most the sum of their
bounds (`schedules_differ`). For mass, which is never negative, the error is relative to the total
(`eval_error_nonneg`). `n` atomics on a node have depth `n − 1` (`chain_depth`); runs summed first and then
chained have depth at most the run depth plus the number of runs (`chainT_depth_le`). Fixed point's error,
under three quanta a share and the same for every order (`fixed_error_le`), is no worse than that bound
once `3·(n+1)·δ ≤ n·u·Σ|a|` (`fixed_le_float_bound`). With underflow, computing momentum as `(w·m)·v`
gives a flushed mass share zero momentum (`massFirst_zero`), and `w·(m·v)` does not
(`momentumFirst_omega`).

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

- The `respected` column of `scripts/LawAtlas.lean`, whether each operation keeps the equivalence a
  pairing needs, is still a search result.
- Each operation's hyperoperation, the exponentials between operations, and rational exponents of every
  power but `⊗`'s, which `T/AnglePower.lean` has on the angle. These have been searched and worked by
  hand, but none of it is in Lean yet.
- For the scatter: that the segmented kernel's subgroup scan leaves each run's sum in its last lane, and
  a concrete IEEE `f32` counterexample to associativity. `Scatter/Rounding.lean` bounds floating point
  through a rounding model, not IEEE bits, and none of it checks the Java or SPIR-V kernels themselves.
- The wheel axioms were checked against the statements on Wikipedia and nLab. Carlström's paper itself
  has not been read against them.

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
| `CottLean/T/PowerSum.lean` | `zⁿ = xⁿ + yⁿ` exactly; only `n = ±1` stay for every pair; `pⁿ = 2qⁿ`; Fermat at 3 and 4 |
| `CottLean/T/Atlas.lean` | the law atlas: every law, every pairing of an addition and a multiplication, graded and proved strongest |
| `CottLean/T/NoDivision.lean` | no equality lets `⊕` and division coexist, for any of the five products |
| `CottLean/T/Transform.lean` | Möbius transformations as matrices; every product as a family of them; discriminants, fixed points, sandwiches |
| `CottLean/Nested/Basic.lean` | `T2`, a pair of pairs: the embedding of `T`, the projection `flatten` as a Möbius transformation of the numerator, and `T2` against the common meadow |
| `CottLean/Scatter/Accumulate.lean` | the particle-to-grid scatter over any additive monoid: every schedule gives the same grid, and it conserves |
| `CottLean/Scatter/Wrap.lean` | wrapping `w`-bit registers: exact whenever a node's final total fits; the mod-`2^w` quotient keeps `⊕` |
| `CottLean/Scatter/Quantise.lean` | integer bilinear shares that conserve exactly; momentum as mass share times velocity |
| `CottLean/Scatter/Rounding.lean` | floating point's error for every schedule; the scale at which fixed point is no worse; underflow and the order of the product |
| `CottLean/Scatter/Stencil.lean` | quantised shares on any stencil with a chosen remainder node; tensor weights; the quadratic B-spline 3×3 stencil, remainder at the centre |
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
