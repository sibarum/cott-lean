# cott-lean

A Lean 4 formalization of traction: the pair `T(p, q)` of
[cott-engine](../cott-engine)'s `docs/Traction-Model.md`, which is the definitive statement of the model.

```
T(p, q) = p/q ≈ tan(arg(q + i·p))
```

Every theorem here holds for every pair. None is checked on a sample. Every proof depends only on Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and nothing is assumed beyond Mathlib.

## Conventions

- **No invariant is specified by default.** Two pairs are equal exactly when their coordinates are, so
  `T(1,2) ≠ T(2,4)`. The ratio, the ray (a positive multiple of both coordinates), the angle and the norm
  are invariants that a use may specify. A result that holds only under one of them says which.
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
integers give the ray and the non-zero integers give the ratio. That part is wheel theory's and isn't
proved here.

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
| `1` | split-complex integers ℤ[j] | `4` | `⊛` (`splitTimes`), new here |
| `ω` | ℤ × ℤ | `1` | `*`, read as `q + (p − q)·ω` (`ProdPosition.quadEquiv`) |
| `−1 − ω` | Eisenstein integers ℤ[ζ₃] | `−3` | `qtimes (-1) (-1)` |

The complex, dual and split-complex numbers are the rows with `b = 0`, where `a` is the sign of `ω²`.
`⊗` and `+` are two of them, and the third, `⊛`, is `⊗` with the sign of the `pr` term turned. `*`
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

Where it doesn't come back, every operand has a distinct partner that gives the same result. So the loss
is the operation being ambiguous there, not an inverse that is too weak.

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

- The angle column: θ as `arg(q + p·i)`, and `principal`.
- `T(a,b)^T(c,d) = tan((c/d)·arctan(a/b))` off the integers.
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

## Building

Lean `v4.33.0` and Mathlib `v4.33.0`, pinned in `lean-toolchain` and `lakefile.toml`.

```
lake exe cache get
lake build
```

`lake exe cache get` downloads Mathlib's prebuilt files. Without it, the first build compiles Mathlib
from source.
