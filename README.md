# cott-lean

[![Build and check axioms](https://github.com/sibarum/cott-lean/actions/workflows/build.yml/badge.svg)](https://github.com/sibarum/cott-lean/actions/workflows/build.yml)

A Lean 4 formalization of traction: the pair `T(p, q)` of
[cott-engine](../cott-engine)'s `docs/Traction-Model.md`, which is the definitive statement of the model.

```
T(p, q) = p/q ≈ tan(arg(q + i·p))
```

Every theorem here holds for every pair. None is checked on a sample. Every proof depends only on Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and nothing is assumed beyond Mathlib. That is
checked for every declaration, not claimed: see [Checking the axioms](#checking-the-axioms).

## Conventions

- **No invariant is specified by default.** Two pairs are equal exactly when their coordinates are, so
  `T(1,2) ≠ T(2,4)`. The ratio, the ray (a positive multiple of both coordinates), the angle and the norm
  are invariants that a use may specify. Away from `0ω`, the angle and the ray turn out to be the same
  invariant (`theta_eq_theta_iff_sameRay`). A result that holds only under one of them says which.
  Everything is proved at coordinate equality first.
- **`0` is `T(0,1)`** by default. The other zero-magnitude pairs stay available by name.
- **`-x` is `T(-p, q)`.** So `-0 = 0`, and `T(0,-1)` is `_0`. The `⊕` inverse `T(-p,-q)` is `-_x`.
- The nine named values are spelled the model's way: `T.«0»`, `T.«ω»`, `T.«_0»`, `T.«-_1»`, `T.«0ω»`, …

## The results

### The two halves

T carries two arithmetics on one set of pairs. Each half, on its own, turns out to be a known structure.

**The exponent position is the Gaussian integers** (`T/Gaussian.lean`). `T(p, q)` is the point `q + p·i`.
Under that reading, `⊕` is addition, `⊗` is multiplication, `-x` is the complex conjugate and `-_x` is
the negative. The correspondence is exact, term by term: `ExponentPosition.ringEquiv : ExponentPosition ≃+* ℤ[i]`.
So every ring law holds of `⊕` and `⊗`. The four seeds `0, ω, _0, -ω` are exactly the pairs `⊗` can undo
(`exists_otimes_eq_zero_iff`).

**The value position is a wheel** (`T/Wheel.lean`). `(T, 0, 1, +, *, /)` satisfies every wheel axiom at
coordinate equality (`isWheel`). It is Carlström's wheel of fractions over ℤ with `S = {1}`, which is the
choice that identifies nothing. The wheel's bottom element `0/0` is `0ω`, and so is `0·ω`
(`bottom_eq`, `zero_times_omega`). In wheel theory, choosing an invariant is choosing `S`: the positive
integers give the ray and the non-zero integers give the ratio. For every multiplicative `S` the quotient
is a wheel (`T/Quotient.lean`, `Q.isWheel`), and `+`, `*`, `/`, `-`, `-_` and `⊗` survive it. `⊕`
survives only `S = {1}` and `0 ∈ S` (`oplus_respects_iff`).

**Next to the division-by-zero literature.** `T(p,q) ↦ p/q`, with every `T(p,0)` going to the error
element, maps T onto the rational common meadow (`T/CommonMeadow.lean`). It respects `+`, `*` and `-`
exactly, and the reciprocal everywhere but at the quarter turns. No map onto the common meadow respects
all four (`no_surjective_hom_Qa`). Bergstra and Ponse's fracpairs are T with the reciprocal multiplied by
the denominator (`T/Fracpair.lean`, `finv_eq_scale`). And every law below that differs from its written
form differs by one added residue `T(0,k)`, where `x + T(0,k)` is `x` with both coordinates multiplied by
`k` (`T/Residue.lean`, `plus_residue`).

**`0ω` across both halves.** It absorbs under `+`, `*` and `⊗`, and it is the identity of `⊕`. It is also
the only pair that all three inverses leave fixed (`zeroOmega_*`, `fixed_by_all_inverses_iff`).

**`⊕` also makes a ring with each value-position product** (`T/Dual.lean`). Under the same reading
`T(p, q) ↦ q + p·ε`, `+` is multiplication in the dual numbers `ℤ[ε]`: `(b + aε)(d + cε) = bd + (ad+bc)ε`,
which is `T(ad+bc, bd)`. `⊕` is addition, `0` is the unit, `ω` is `ε` (`ω + ω = 0ω`), and `-x` is the dual
conjugate (`DualPosition.ringEquiv : DualPosition ≃+* ℤ[ε]`). `*` is coordinatewise, so `⊕` and `*` are
`ℤ × ℤ` (`ProdPosition.ringEquiv`). The two positions share `⊕`, and `(x ⊕ y) + z = (x + z) ⊕ (y + z)`
holds exactly (`oplus_plus`), where `+` over `*` needs the scale.

**Every quadratic ring is one product on `(T, ⊕)`** (`T/Quadratic.lean`). Read `T(p, q)` as `q + p·ω` with
`ω² = a + b·ω`. Then one formula, `qtimes a b (T(p,q)) (T(r,s)) = T(ps + rq + b·pr, qs + a·pr)`, makes
`(T, ⊕, qtimes a b)` Mathlib's `QuadraticAlgebra ℤ a b`, for every `a` and `b`, by the same map
(`QuadPosition.ringEquiv`). That covers every ring free of rank two over ℤ with `1` in a basis.

| `ω²` | ring | discriminant | in T |
|---|---|---|---|
| `−1` | Gaussian integers ℤ[i] | `−4` | `⊗` (`otimes_eq_qtimes`) |
| `0` | dual numbers ℤ[ε] | `0` | `+` (`plus_eq_qtimes`) |
| `1` | split-complex integers ℤ[j] | `4` | `⊚` (`splitTimes`), new here |
| `ω` | ℤ × ℤ | `1` | `*`, read as `q + (p − q)·ω` (`ProdPosition.quadEquiv`) |
| `−1 − ω` | Eisenstein integers ℤ[ζ₃] | `−3` | `qtimes (-1) (-1)` |

The complex, dual and split-complex numbers are the rows with `b = 0`, where `a` is the sign of `ω²`.
`⊗` and `+` are two of them, and the third, `⊚`, is `⊗` with the sign of the `pr` term turned. `*`
is not the split-complex product over ℤ: its ring has the idempotent `ω`, and ℤ[j] has none but `0` and
`1` (`split_not_prod`). The two agree only once `2` is invertible.

### Where the halves meet

**`⊗` is the wheel's tangent addition, without the wheel's collapse** (`T/TangentAddition.lean`).
Write the classical formula with the value position's own operations:

```
tanAdd(x, y) = (x + y) / (1 − x·y)
```

It is `x ⊗ y` with both coordinates multiplied by `x.q · y.q` (`tanAdd_eq`). The wheel's version lands on
`0ω` exactly when a denominator is zero (`tanAdd_eq_zeroOmega_iff`). `⊗` lands on `0ω` only from `0ω`
(`otimes_eq_zeroOmega_iff`). At a quarter turn, then, the wheel's formula forgets the other angle
entirely, while `⊗` forgets nothing (`quarterTurn_contrast`). For example, `ω ⊗ 1 = _1`, where the
wheel's formula gives `0ω`. The collapse happens only when an *argument* is a quarter turn:
`tan(45° + 45°)` gives `T(2,0)` both ways.

A direct consequence, not stated as a separate theorem: where `x.q · y.q < 0`, the wheel's answer is on
the ray opposite to `⊗`'s. `_1 ⊗ 1 = T(0,-2)` is 180°, and the wheel's formula gives `T(0,2)`, at 0°.

**`⊚` is the wheel's velocity addition, in the same way** (`T/Velocity.lean`). Relativistic velocity
addition, `(u + v) / (1 + u·v)` with `1` as the speed of light, written with the value position's
operations, is `x ⊚ y` with both coordinates multiplied by `x.q · y.q` (`velAdd_eq`). The formula divides
by zero in three places, and they behave differently:

- `uv = −1` is a pole, not a collapse. `⊚` and the wheel both answer `T(k, 0)` and agree, as at
  `tan(45° + 45°)`.
- An argument with `q = 0` collapses the wheel's formula to `0ω`, and `⊚` loses nothing
  (`infinity_contrast`). This is the tangent contrast again.
- Opposite light lines are `⊚`'s own collapse, which `⊗` has no counterpart to. In light-cone
  coordinates `(q + p, q − p)`, `⊚` multiplies coordinatewise (`lightCone_splitTimes`). So `x ⊚ y = 0ω`
  exactly when each light-cone coordinate is zero in one of the two (`splitTimes_eq_zeroOmega_iff`). For
  example, `1 ⊚ -1 = 0ω` is `c` plus `−c`, where the classical formula is `0/0` too.

`1` is the speed of light exactly: `1 ⊚ y` is a multiple of `1` for every `y` (`one_splitTimes`). `-x` is
the split conjugate, and `x ⊚ -x = T(0, q² − p²)` is the split norm.

**The parallel sum is `+` through the reciprocal** (`T/Parallel.lean`). Of the power sums
`(xⁿ + yⁿ)^(1/n)`, two stay on the integer pairs: `n = 1`, which is `+`, and `n = −1`, the rule for
resistors in parallel, `x ∥ y = 1/(1/x + 1/y) = T(ac, ad + bc)` (`reciprocal_par`). `(T, ⊕, ∥)` is ℤ[ε]
again, with the coordinates swapped (`ParPosition.ringEquiv`), and the reciprocal is a ring isomorphism
onto it from `(T, ⊕, +)` (`ParPosition.reciprocalEquiv`). Its unit is `ω`, an open circuit, and `0 ∥ 0 = 0ω`.
Classically `1/(1/x + 1/y)` and `xy/(x + y)` are the same, but in the value position only the first is
`∥`. The second is `∥` scaled by `x.q · y.q` (`parAdd_eq`), so it collapses against an open circuit,
where `ω ∥ y = y` (`open_contrast`).

### The angle column

`T/Angle.lean` makes the model's first line exact. `θ(x) = arg(q + p·i)` is a real in `(−π, π]`, and
`tan θ = p/q` for every pair (`tan_theta`). At a quarter turn both sides are Lean's `x/0 = 0`. The nine
named values have the angles of the model's table (`theta_zero`, `theta_one`, …, `theta_negOne`). `0ω`
has no angle, and the theorems below exclude it.

As an angle mod `2π`:

| operation | angle |
|---|---|
| `x ⊗ y` | `θx + θy` (`angle_otimes`) |
| `-x` | `−θx` (`angle_neg`) |
| `-_x` | `θx + π` (`angle_oplusInverse`) |
| `1/x` | `π/2 − θx` (`angle_reciprocal`) |
| `⊗` power `n` | `n·θx` (`angle_otimesPowNat`) |
| `principal x` | `θx` or `θx + π`, with the same tangent (`angle_principal`, `tan_theta_principal`) |

**The angle is the ray.** Two pairs other than `0ω` have the same θ exactly when they are positive
multiples of one pair (`theta_eq_theta_iff_sameRay`). Equivalently, `det x y = 0` and `dot x y > 0`
(`theta_eq_theta_iff`). So of the invariants the conventions name, the angle and the ray are the same
one.

**The mediant lies between.** The angle from `x` to `y` turns the way the sign of `det x y` says
(`sign_angle_sub`). This is the determinant the mediant tree runs on. `det x (x ⊕ y)` and `det (x ⊕ y) y`
both equal `det x y`, so `x ⊕ y` turns from `x` the way `y` does, and turns into `y` the same way
(`mediant_between`).

### The mediant from the four seeds

`T/MediantTree.lean` settles the model's last line: *"every traction other than 0ω is reached exactly
once by iterated mediant from the four seeds."* The process inserts `⊕` between neighbours, starting from
`0, ω, _0, -ω` around the circle. Its first round gives `1, _1, -_1, -1`, which is the model's table of nine.

- Nothing is reached twice (`reach_injective`).
- The pairs reached are exactly those with `gcd(p, q) = 1` (`range_reach`).

So the line splits by invariant. At coordinate equality, `T(2,4)`, `T(2,2)` and `T(0,2)` are never
reached. Up to the ray it holds exactly: every pair except `0ω` is a positive multiple of exactly one
reached pair (`exists_unique_reached_ray`). The proof runs on `det(a,b) = a.q·b.p − a.p·b.q`. Neighbouring
seeds have determinant 1, and the mediant preserves it. Going down the tree is then Euclid's algorithm on
the two coefficients.

### The laws, stated exactly

These are the model's laws, with the exact coordinate result given wherever one differs from the law as written.

| law | result | file |
|---|---|---|
| `(x ⊕ y) ⊗ z = (x ⊗ z) ⊕ (y ⊗ z)` | exact | `Gaussian` |
| `(x + y) * z = (x * z) + (y * z)` | the right side is the left with both coordinates multiplied by `z.q`, which is the wheel's distributive law (`distrib_scaled`) | `ValuePosition` |
| `(T^m)^n = T^(m·n)` | exact, both signs | `Powers` |
| `T^(m+n) = T^m ⊗ T^n` | exact for same-sign exponents; otherwise off by `(p²+q²)^min(\|m\|,\|n\|)`, one norm per cancelled turn (`otimesPower_add`) | `Powers` |
| each operation against its inverse | `⊕` lands on `0ω` exactly; `⊗`, `+` and `*` land on `T(0, p²+q²)`, `T(0, q²)` and `T(pq, pq)` | `Gaussian`, `ValuePosition` |
| `z(T) = T(2ab, b²−a²)`, "a unit vector" | `z(T) = T²`, with norm `(a²+b²)²`, so `z(T)/(a²+b²)` is the unit vector, and that is `E(T)` (`mobius_eq`, `doubleAngle_norm`) | `Mobius` |

### Recovery

Given a result and one operand, when does the other come back exactly? (`T/Recovery.lean`)

| operation | the other operand comes back exactly when the known one is |
|---|---|
| `⊕` | anything |
| `⊗` | anything but `0ω` |
| `+` | a pair with a non-zero denominator |
| `*` | a pair with neither coordinate zero |
| `⊚` | a pair off the light lines, `p² ≠ q²` (`splitTimes_recoverable_iff`, in `Velocity`) |
| `∥` | a pair with a non-zero numerator (`par_recoverable_iff`, in `Parallel`) |

Where it doesn't come back, every operand has a distinct partner that gives the same result. So the loss
is the operation being ambiguous there, not an inverse that is too weak.

**One norm decides every row but `⊕`** (`T/Norm.lean`). Each product is bilinear, so fixing `k` makes it a
linear map of the other operand. Its determinant is the norm of `k` in that product's ring, which for
`q + p·ω` with `ω² = a + b·ω` is `q² + b·pq − a·p²`. The other operand comes back exactly when the norm
is non-zero (`recoverable_iff_norm`), and `k` has an inverse exactly when the norm is `±1`
(`exists_inverse_iff_norm`). The first is recovery on the image; only the second gives every result a
preimage.

| product | norm of `k` | has an inverse exactly at |
|---|---|---|
| `⊗` | `p² + q²` | the four seeds `0, ω, _0, -ω` (`exists_otimes_eq_zero_iff`) |
| `+` | `q²` | every `T(p, ±1)` (`exists_plus_eq_zero_iff`) |
| `⊚` | `q² − p²` | the four seeds again (`exists_splitTimes_eq_zero_iff`) |
| `*` | `pq` | `1, _1, -_1, -1` (`exists_times_eq_one_iff`) |
| `∥` | `p²` | every `T(±1, q)` (`exists_par_eq_omega_iff`) |

`*` and `∥` are read in their own bases: `q + (p − q)·ω` with `ω² = ω`, and `p + q·ω` with `ω² = 0`.

Under `*`, `ω` and `0` are the complementary idempotents of ℤ × ℤ. `x * ω = T(p, 0)` and `x * 0 = T(0, q)`
each keep one coordinate, and `(x * ω) ⊕ (x * 0) = x` restores both (`times_omega_oplus_times_zero`).

**`*` is the only product with projections** (`T/Projection.lean`). A projection is an idempotent other
than the ring's zero and unit. In the family `ω² = a + b·ω`, one exists exactly when the discriminant
`b² + 4a` is `1`, and it is then `p = ±1`, `2q = 1 − b·p` (`qtimes_idempotent_iff`). That is ℤ × ℤ.
So `⊗`, `+`, `⊚` and the Eisenstein product have only `0ω` and `0` as idempotents, `∥` has only `0ω`
and `ω`, and `*` has four: `0ω`, `0`, `ω` and `1` (`times_idempotent_iff`). `split_not_prod` is the
case `a = 1`, `b = 0`. What `*` loses against a pair on an axis is exactly one projection. Against
`T(a, 0)` with `a ≠ 0`, two operands give the same result exactly when their `ω` projections agree
(`times_eq_times_iff_of_q_eq_zero`). So keeping the other projection alongside the result gives the operand
back (`times_recover_with_complement`).

**Every product loses at most one integer** (`T/Loss.lean`). Against `k ≠ 0ω` with norm zero, a result
`r = x · k` in the family `ω² = a + b·ω` satisfies `k.p · r.q = k.q · r.p`, so the whole result is its
numerator, one linear form in `x` (`qtimes_eq_qtimes_iff`). Keeping `x.p` alongside it gives `x` back
(`qtimes_recover_with_numerator`). Read off for each product:

| product | against | keeps | loses |
|---|---|---|---|
| `+` | `T(c, 0)` | `x.q` | `x.p` |
| `⊚` | `T(c, c)` | `x.q + x.p` | `x.q − x.p` |
| `⊚` | `T(c, −c)` | `x.q − x.p` | `x.q + x.p` |
| `*` | `T(c, 0)` | `x.p` | `x.q` |
| `*` | `T(0, c)` | `x.q` | `x.p` |
| `∥` | `T(0, c)` | `x.p` | `x.q` |

`⊗` loses nothing except against `0ω`, and against `0ω` every product loses both integers. So a
reversible use of any of these products, against anything but `0ω`, needs one integer of state beyond the
result at most.

## What is classical and what is not

Most of the individual facts are classical. ℤ[i] is ℤ[i] and a quadratic ring is a quadratic ring; the wheel
result is a case of Carlström's theorem; the mediant tree is the Stern–Brocot tree, extended to the four
signed quadrants. What the formalization adds is exactness about the model: which of its lines hold at
coordinate equality, which hold only under a named invariant, and what the exact coordinate result is in
each case.

The part that belongs to traction, and not to any one known structure, is the structures sharing one set
of pairs. The exponent position and the value position share `⊕`, and every quadratic ring over ℤ is a
product on it, by one map. `⊗` is the complex one and `+` the dual one; the split-complex one completes
the three. `0ω` is the zero of every one of these rings and the bottom element of the wheel. And `⊗`
completes the wheel's tangent addition at exactly the inputs where the wheel collapses.

`⊕` is also the reason the pairs cannot be quotiented. It survives no invariant between identifying
nothing and identifying everything, while `+`, `*`, `/` and `⊗` survive every one (`oplus_respects_iff`
in `T/Quotient.lean`). So the rings exist only on the pairs as they are. Under the ray or the ratio,
what is left is the wheel, with `⊗`.

## Not covered

- `T(a,b)^T(c,d) = tan((c/d)·arctan(a/b))` off the integers.
- That the power sum `(xⁿ + yⁿ)^(1/n)` leaves the integer pairs for `n ∉ {1, −1}`.
- The wheel axioms were checked against the statements on Wikipedia and nLab. Carlström's paper itself
  has not been read against them.

## Files

| file | contents |
|---|---|
| `CottLean/T/Basic.lean` | the pair, the nine values, both positions' operations |
| `CottLean/T/Gaussian.lean` | the exponent position is ℤ\[i] |
| `CottLean/T/ValuePosition.lean` | `+` and `*`; distributivity exactly; the same-ratio relation |
| `CottLean/T/Recovery.lean` | when an operand can be read back |
| `CottLean/T/Powers.lean` | the integer exponent laws |
| `CottLean/T/Mobius.lean` | `z`, `E` and `E⁻¹` |
| `CottLean/T/MediantTree.lean` | the mediant from the four seeds |
| `CottLean/T/Wheel.lean` | the value position is a wheel; `0ω` across both halves |
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

CI runs the build and this check on every push (`.github/workflows/build.yml`).
