import CottLean.T.Powers

/-!
# The Möbius transform, and `z`

Traction-Model.md's extra utilities:

```
z(T(a, b))  =  T( 2ab , b^2 − a^2 )     "returns a unit vector at double the angle"
E(T) = (1 + iT)/(1 − iT)                 traction → unit circle
E^{-1}(v) = Im(v)/(1 + Re(v))            unit circle → traction
```

Everything here is an exact identity on integers, so nothing is divided and nothing is approximated.

* `E(T)` at `T = p/q` is `(q + p·i)/(q − p·i)`, which is `z(T)` divided by the norm `N = p² + q²`
  (`mobius_eq`). So `z` is the numerator of `E`: the point at double the angle, before the norm is taken
  out.
* `z(T)` has norm `N²` (`doubleAngle_norm`), so `z(T)/N` is on the unit circle -- that is the exact sense
  in which `z` returns a unit vector.
* Reading `E^{-1}` back as a pair, `T(Im, 1 + Re)` with the norm cleared from both coordinates, gives
  `T(p, q)` with both coordinates multiplied by `2q` (`invMobius_mobius`). At the two quarter turns, where
  `q = 0`, that is `0ω`.
-/

namespace T

/-- The norm `p² + q²`. -/
def norm (x : T) : ℤ := x.p ^ 2 + x.q ^ 2

/-- `E(T) = (q + p·i)/(q − p·i)`, held as `z(T)` over `N`: this is the whole content of `mobius_eq`. -/
theorem mobius_eq (x : T) :
    star (toGaussian x) * toGaussian (doubleAngle x) = (norm x : GaussianInt) * toGaussian x := by
  rw [doubleAngle, toGaussian_otimes, norm, norm_eq_mul_star]
  ring

/-- `z(T)` has norm `N²`, so `z(T) ÷ N` is a unit vector. -/
theorem doubleAngle_norm (x : T) : norm (doubleAngle x) = norm x ^ 2 := by
  simp only [norm, doubleAngle_eq]
  ring

/-- `E^{-1}` read as a pair: `T(Im v, 1 + Re v)` at `v = z ÷ N`, with `N` cleared from both
coordinates. -/
def invMobiusPair (z : T) (n : ℤ) : T := ⟨z.p, n + z.q⟩

/-- Round trip: the pair comes back with both coordinates multiplied by `2q`. -/
theorem invMobius_mobius (x : T) : invMobiusPair (doubleAngle x) (norm x) = scale (2 * x.q) x := by
  ext <;> simp [invMobiusPair, doubleAngle_eq, norm, scale] <;> ring

/-- So at a quarter turn it is `0ω`. -/
theorem invMobius_mobius_of_q_eq_zero (x : T) (h : x.q = 0) :
    invMobiusPair (doubleAngle x) (norm x) = «0ω» := by
  rw [invMobius_mobius, h]; ext <;> simp [scale, «0ω»]

example : doubleAngle «ω» = «_0» := by decide
example : invMobiusPair (doubleAngle «ω») (norm «ω») = «0ω» := by decide
example : invMobiusPair (doubleAngle «1») (norm «1») = ⟨2, 2⟩ := by decide

end T
