import CottLean.T.Transform
import CottLean.T.Angle
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The spin cover: a pair squares to an exact rotation

Under `⊗` a pair is a spiral: it turns by its angle and scales by its norm. On the ray the turn is exact,
but the only pairs of norm one are the four units, so no other pair is a rotation as it stands. Squaring
fixes that. `z(x) = x ⊗ x` (`doubleAngle`) has norm `N²` (`doubleAngle_norm`), a perfect square, so it
can be divided by `N` exactly, and what is left is a rotation with rational entries:

```
rot T(p, q)  =  1/N · [ q² − p²   −2pq    ]        N = p² + q²
                      [ 2pq        q² − p² ]
```

No π and no analytic function is involved: the entries are ratios of integers.

## What is proved

* `rot_mem_specialOrthogonalGroup`: off `0ω`, `rot x` is exactly orthogonal with determinant one.
* `rot_otimes`: `rot (x ⊗ y) = rot x * rot y`, for every pair. So rotations compose by composing pairs,
  and the squaring can be left to the end.
* `rot_eq_rot_iff`: off `0ω`, two pairs give the same rotation exactly when they lie on one line through
  the origin, `det x y = 0`. In particular `x` and `oplusInverse x`, half a turn apart, give the same
  rotation (`rot_oplusInverse`). That is the double cover: a pair carries twice the angle information of
  its rotation, as a quaternion does in three dimensions.
* `exists_rot`, `rot_surjective`: every rotation with rational entries is `rot x` for some pair. So
  nothing is missed: the squares of the pairs are all of `SO(2, ℚ)`.
* `rotCos_eq_cos`, `rotSin_eq_sin`: the bridge to the classical angle. `rot x` is the rotation by
  `2θ(x)`. This is the only place π is in the file, and only to say what the rest means.
-/

namespace T

/-- Off `0ω` the norm is not zero. -/
theorem norm_ne_zero_of_ne {x : T} (hx : x ≠ «0ω») : norm x ≠ 0 := by
  intro h
  apply hx
  have hp : x.p = 0 := by unfold norm at h; nlinarith [sq_nonneg x.p, sq_nonneg x.q]
  have hq : x.q = 0 := by unfold norm at h; nlinarith [sq_nonneg x.p, sq_nonneg x.q]
  ext <;> simp [«0ω», hp, hq]

/-- The norm in `ℚ`, off `0ω`. -/
theorem normQ_ne_zero {x : T} (hx : x ≠ «0ω») : ((x.p : ℚ) ^ 2 + (x.q : ℚ) ^ 2) ≠ 0 := by
  have := norm_ne_zero_of_ne hx
  unfold norm at this
  exact_mod_cast this

/-! ## The rotation -/

/-- `cos 2θ`, exactly: `(q² − p²)/N`. -/
def rotCos (x : T) : ℚ := (doubleAngle x).q / norm x

/-- `sin 2θ`, exactly: `2pq/N`. -/
def rotSin (x : T) : ℚ := (doubleAngle x).p / norm x

/-- The rotation a pair squares to. At `0ω` it is the zero matrix. -/
def rot (x : T) : Matrix (Fin 2) (Fin 2) ℚ := !![rotCos x, -rotSin x; rotSin x, rotCos x]

theorem rotCos_eq (x : T) : rotCos x = ((x.q : ℚ) ^ 2 - x.p ^ 2) / (x.p ^ 2 + x.q ^ 2) := by
  simp [rotCos, doubleAngle_eq, norm]

theorem rotSin_eq (x : T) : rotSin x = (2 * x.p * x.q : ℚ) / (x.p ^ 2 + x.q ^ 2) := by
  simp [rotSin, doubleAngle_eq, norm]

/-- On the unit circle, exactly. -/
theorem rotCos_sq_add_rotSin_sq {x : T} (hx : x ≠ «0ω») : rotCos x ^ 2 + rotSin x ^ 2 = 1 := by
  have h := normQ_ne_zero hx
  rw [rotCos_eq, rotSin_eq]
  field_simp
  ring

/-- Exactly orthogonal, with determinant one. -/
theorem rot_mem_specialOrthogonalGroup {x : T} (hx : x ≠ «0ω») :
    rot x ∈ Matrix.specialOrthogonalGroup (Fin 2) ℚ := by
  have h := rotCos_sq_add_rotSin_sq hx
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · have e : rot x * (rot x).transpose =
        !![rotCos x ^ 2 + rotSin x ^ 2, 0; 0, rotCos x ^ 2 + rotSin x ^ 2] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    rw [e, h, Matrix.one_fin_two]
  · rw [rot, Matrix.det_fin_two_of]
    linear_combination h

/-! ## Composing -/

theorem rotCos_otimes (x y : T) : rotCos (x ⊗ y) = rotCos x * rotCos y - rotSin x * rotSin y := by
  simp only [rotCos, rotSin, doubleAngle_otimes, norm_otimes, div_mul_div_comm, ← sub_div]
  simp [otimes]

theorem rotSin_otimes (x y : T) : rotSin (x ⊗ y) = rotSin x * rotCos y + rotCos x * rotSin y := by
  simp only [rotCos, rotSin, doubleAngle_otimes, norm_otimes, div_mul_div_comm, ← add_div]
  simp [otimes]; ring

/-- `⊗` is composition of rotations, for every pair. -/
theorem rot_otimes (x y : T) : rot (x ⊗ y) = rot x * rot y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two, rotCos_otimes, rotSin_otimes] <;> ring

theorem rot_zero : rot 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, rotCos, rotSin, doubleAngle_eq, norm]

/-! ## The double cover -/

/-- Off `0ω`, two pairs give one rotation exactly when they lie on one line. -/
theorem rot_eq_rot_iff {x y : T} (hx : x ≠ «0ω») (hy : y ≠ «0ω») : rot x = rot y ↔ det x y = 0 := by
  have h1 := normQ_ne_zero hx
  have h2 := normQ_ne_zero hy
  have hc : rot x = rot y ↔ rotCos x = rotCos y ∧ rotSin x = rotSin y := by
    constructor
    · intro h
      exact ⟨by simpa [rot] using congrFun (congrFun h 0) 0, by simpa [rot] using congrFun (congrFun h 1) 0⟩
    · rintro ⟨hc, hs⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [rot, hc, hs]
  rw [hc, rotCos_eq, rotCos_eq, rotSin_eq, rotSin_eq, div_eq_div_iff h1 h2, div_eq_div_iff h1 h2]
  unfold det
  constructor
  · rintro ⟨hc, hs⟩
    -- `2·N(y)·det² = −c(y)·(c-equation) − s(y)·(s-equation)`, and `N(y) ≠ 0`.
    have key : (2 * ((y.p : ℚ) ^ 2 + y.q ^ 2)) * ((x.q : ℚ) * y.p - x.p * y.q) ^ 2 = 0 := by
      linear_combination (-((y.q : ℚ) ^ 2 - y.p ^ 2)) * hc + (-(2 * (y.p : ℚ) * y.q)) * hs
    have hd : ((x.q : ℚ) * y.p - x.p * y.q) = 0 := by
      have := mul_eq_zero.mp key
      rcases this with h | h
      · exact absurd (by linarith : ((y.p : ℚ) ^ 2 + y.q ^ 2) = 0) h2
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    exact_mod_cast hd
  · intro hd
    have hd' : ((x.q : ℚ) * y.p - x.p * y.q) = 0 := by exact_mod_cast hd
    constructor
    · linear_combination (2 * ((x.q : ℚ) * y.p + x.p * y.q)) * hd'
    · linear_combination (2 * ((x.p : ℚ) * y.p - x.q * y.q)) * hd'

/-- Half a turn apart, one rotation. -/
theorem rot_oplusInverse (x : T) : rot (oplusInverse x) = rot x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, rotCos, rotSin, doubleAngle_eq, norm, oplusInverse]

/-- A non-zero multiple, of either sign, gives the same rotation. -/
theorem rot_scale {k : ℤ} (hk : k ≠ 0) (x : T) : rot (scale k x) = rot x := by
  by_cases hx : x = «0ω»
  · subst hx; simp [scale, «0ω»]
  have hsx : scale k x ≠ «0ω» := by
    intro h; apply hx
    have hp := congrArg T.p h; have hq := congrArg T.q h
    simp [scale, «0ω»] at hp hq
    ext <;> simp [«0ω», hp.resolve_left hk, hq.resolve_left hk]
  rw [rot_eq_rot_iff hsx hx]
  simp [det, scale]; ring

/-- The identity comes from exactly the pairs on the real axis. -/
theorem rot_eq_one_iff {x : T} (hx : x ≠ «0ω») : rot x = 1 ↔ x.p = 0 := by
  rw [← rot_zero, rot_eq_rot_iff hx (by decide)]
  simp [det]

/-! ## Every rational rotation -/

/-- Every rational point of the unit circle is `(rotCos x, rotSin x)` for some pair: `T(s, 1 + c)`
cleared of denominators, or `ω` at `c = −1`. -/
theorem exists_rot {c s : ℚ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ x : T, x ≠ «0ω» ∧ rotCos x = c ∧ rotSin x = s := by
  by_cases hc : c = -1
  · subst hc
    have : s = 0 := by nlinarith [sq_nonneg s]
    subst this
    exact ⟨«ω», by decide, by simp [rotCos_eq, «ω»], by simp [rotSin_eq, «ω»]⟩
  set u := 1 + c with hu
  have hu0 : u ≠ 0 := fun h0 => hc (by linarith)
  set d : ℤ := s.den * u.den
  have hd : (d : ℚ) ≠ 0 := by simp [d]
  have hsd : ((s.num * u.den : ℤ) : ℚ) = s * d := by
    simp only [d]; push_cast; rw [← Rat.mul_den_eq_num]; ring
  have hud : ((u.num * s.den : ℤ) : ℚ) = u * d := by
    simp only [d]; push_cast; rw [← Rat.mul_den_eq_num]; ring
  refine ⟨⟨s.num * u.den, u.num * s.den⟩, ?_, ?_, ?_⟩
  · have hq : u.num * (s.den : ℤ) ≠ 0 :=
      mul_ne_zero (Rat.num_ne_zero.mpr hu0) (by exact_mod_cast s.den_nz)
    intro h0
    exact hq (congrArg T.q h0)
  · rw [rotCos_eq]; simp only [hsd, hud]
    have hN : (s * d) ^ 2 + (u * d) ^ 2 = 2 * u * d ^ 2 := by rw [hu]; linear_combination d ^ 2 * h
    rw [hN]; field_simp; rw [hu]; linear_combination (-(1 : ℚ)) * h
  · rw [rotSin_eq]; simp only [hsd, hud]
    have hN : (s * d) ^ 2 + (u * d) ^ 2 = 2 * u * d ^ 2 := by rw [hu]; linear_combination d ^ 2 * h
    rw [hN]; field_simp

/-- The squares of the pairs are all of `SO(2, ℚ)`. -/
theorem rot_surjective {A : Matrix (Fin 2) (Fin 2) ℚ} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℚ) :
    ∃ x : T, x ≠ «0ω» ∧ rot x = A := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff] at hA
  obtain ⟨ho, hdet⟩ := hA
  have e00 : A 0 0 ^ 2 + A 0 1 ^ 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, sq] using congrFun (congrFun ho 0) 0
  have e11 : A 1 0 ^ 2 + A 1 1 ^ 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, sq] using congrFun (congrFun ho 1) 1
  rw [Matrix.det_fin_two] at hdet
  -- `(d − a)² + (c + b)² = 2 − 2·det = 0`.
  have hsum : (A 1 1 - A 0 0) ^ 2 + (A 1 0 + A 0 1) ^ 2 = 0 := by
    linear_combination e00 + e11 - 2 * hdet
  have h11 : A 1 1 = A 0 0 := by nlinarith [sq_nonneg (A 1 1 - A 0 0), sq_nonneg (A 1 0 + A 0 1)]
  have h01 : A 0 1 = -A 1 0 := by nlinarith [sq_nonneg (A 1 1 - A 0 0), sq_nonneg (A 1 0 + A 0 1)]
  obtain ⟨x, hx, hc, hs⟩ := exists_rot (c := A 0 0) (s := A 1 0) (by
    have : A 0 0 ^ 2 + A 1 0 ^ 2 = 1 := by rw [h01] at e00; linear_combination e00
    exact this)
  refine ⟨x, hx, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rot, hc, hs, h11, h01]

/-! ## What it means: the rotation by `2θ` -/

theorem rotCos_eq_cos {x : T} (hx : x ≠ «0ω») : (rotCos x : ℝ) = Real.cos (2 * theta x) := by
  have hz := toC_ne_zero hx
  have hn : ‖toC x‖ ^ 2 = (x.p : ℝ) ^ 2 + (x.q : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hn0 : ‖toC x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [Real.cos_two_mul, theta, Complex.cos_arg hz, rotCos_eq]
  simp only [toC_re]
  push_cast
  rw [div_pow, hn]
  have : ((x.p : ℝ) ^ 2 + (x.q : ℝ) ^ 2) ≠ 0 := by
    have := normQ_ne_zero hx; exact_mod_cast this
  field_simp
  ring

theorem rotSin_eq_sin {x : T} (hx : x ≠ «0ω») : (rotSin x : ℝ) = Real.sin (2 * theta x) := by
  have hz := toC_ne_zero hx
  have hn : ‖toC x‖ ^ 2 = (x.p : ℝ) ^ 2 + (x.q : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [Real.sin_two_mul, theta, Complex.sin_arg, Complex.cos_arg hz, rotSin_eq]
  simp only [toC_re, toC_im]
  push_cast
  have : ((x.p : ℝ) ^ 2 + (x.q : ℝ) ^ 2) ≠ 0 := by
    have := normQ_ne_zero hx; exact_mod_cast this
  rw [show (2 : ℝ) * (x.p / ‖toC x‖) * (x.q / ‖toC x‖) = 2 * (x.p * x.q) / ‖toC x‖ ^ 2 by ring, hn]
  ring

/-! ## Examples -/

/-- `T(1,2)` squares to the 3-4-5 rotation. -/
example : rotCos ⟨1, 2⟩ = 3 / 5 ∧ rotSin ⟨1, 2⟩ = 4 / 5 := by
  simp [rotCos_eq, rotSin_eq]; norm_num

/-- `1 = T(1,1)` squares to the quarter turn, and `ω` to the half turn. -/
example : rot «1» = !![0, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, rotCos_eq, rotSin_eq, «1»] <;> norm_num

example : rot «ω» = !![-1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, rotCos_eq, rotSin_eq, «ω»]

end T
