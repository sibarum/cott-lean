import CottLean.T.NoDivision
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Every product is a family of Möbius transformations

A Möbius transformation of the ratio, `p/q ↦ (αp + βq)/(γp + δq)`, is a 2×2 integer matrix acting on the
pair (`act`). Composing two is multiplying their matrices (`act_mul`). These are exactly the maps that
respect `⊕` (`eq_act_of_oplus`), and several operations already are some: the reciprocal, `-x`, `-_x`,
and a quarter turn (`act_swap`, `act_negP`, `act_negOne`, `act_quarterTurn`).

Multiplying by a fixed `y = T(r, s)` is linear in the other operand, so it is a matrix too, and every
product is a family of Möbius transformations:

| product | multiply by `T(r, s)` | discriminant `trace² − 4·det` | kind | fixed points |
|---|---|---|---|---|
| `qtimes a b` | `[[s + b·r, r], [a·r, s]]` | `r²·(b² + 4a)` | by the sign of `b² + 4a` | where `N = 0` |
| `⊗` | `[[s, r], [−r, s]]` | `−4r²` | elliptic | none but `0ω` |
| `+` | `[[s, r], [0, s]]` | `0` | parabolic | `ω`'s ray |
| `⊚` | `[[s, r], [r, s]]` | `4r²` | hyperbolic | the light lines |
| `*` | `[[r, 0], [0, s]]` | `(r − s)²` | hyperbolic | the two axes |
| `∥` | `[[r, 0], [s, r]]` | `0` | parabolic | `0`'s ray |

The determinant of multiplying by `y` is `y`'s norm (`det_qmat`), so the norm that decides recovery in
`Norm` is literally a determinant. The discriminant is `y.p²` times the ring's discriminant
(`disc_qmat`), so the ring's type -- complex, dual, or split -- is the type of every one of its
non-scalar elements as a Möbius map. A ray `x` is a fixed point of multiplying by `y` exactly when
`det(x, x·y) = 0`. For `qtimes` that is `y.p · N(x)` (`det_qtimes_self`), so the fixed points are the
rays of the zero divisors: what `Loss` found each product loses, seen from the other side.

## Sandwiches

Carrying a product through a bijection `g` and back, `x ⋄ y = g⁻¹(g x · g y)`, gives an operation that
keeps every law the original had: commutativity, associativity and, when `g` respects `⊕`,
distributivity over `⊕` (`sandwich_comm`, `sandwich_assoc`, `sandwich_oplus`). The zoo already contains
three sandwiches:

* `∥` is `+` carried through the reciprocal (`par_eq_sandwich`), which exchanges `0` and `ω`.
* `*` is `qtimes 0 1` carried through `T(p, q) ↦ T(p − q, q)` (`times_eq_sandwich`).
* `⊚` becomes `*` under the light-cone map `T(p, q) ↦ T(p + q, q − p)` (`lightConeMap_splitTimes`). That
  map has determinant `2`, so it is a homomorphism into `*` and not an isomorphism, which is
  `split_not_prod` again.

A sandwich by a matrix of determinant `±1` changes a product's matrices by conjugation, which keeps every
discriminant (`disc_conj`). So a sandwich moves a product's fixed points and keeps its type.

The model's `E(T) = (1 + iT)/(1 − iT)` is the complex Cayley transform. It sends `⊗` to multiplication on
the unit circle: `E(x ⊗ y) = E(x)·E(y)`, held here as `z(x ⊗ y) = z(x) ⊗ z(y)` over
`N(x ⊗ y) = N(x)·N(y)` (`doubleAngle_otimes`, `norm_otimes`).
-/

namespace T

open Matrix

/-! ## The action -/

/-- A Möbius transformation of the ratio, acting on the pair: `T(p, q) ↦ T(αp + βq, γp + δq)`. -/
def act (M : Matrix (Fin 2) (Fin 2) ℤ) (x : T) : T :=
  ⟨M 0 0 * x.p + M 0 1 * x.q, M 1 0 * x.p + M 1 1 * x.q⟩

@[simp] theorem act_p (M : Matrix (Fin 2) (Fin 2) ℤ) (x : T) : (act M x).p = M 0 0 * x.p + M 0 1 * x.q :=
  rfl
@[simp] theorem act_q (M : Matrix (Fin 2) (Fin 2) ℤ) (x : T) : (act M x).q = M 1 0 * x.p + M 1 1 * x.q :=
  rfl

theorem act_one (x : T) : act 1 x = x := by
  ext <;> simp [act]

/-- Composing two transformations is multiplying their matrices. -/
theorem act_mul (M N : Matrix (Fin 2) (Fin 2) ℤ) (x : T) : act (M * N) x = act M (act N x) := by
  ext <;> simp [act, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem act_oplus (M : Matrix (Fin 2) (Fin 2) ℤ) (x y : T) : act M (x ⊕ y) = (act M x ⊕ act M y) := by
  ext <;> simp [act, oplus] <;> ring

theorem act_swap (x : T) : act !![0, 1; 1, 0] x = reciprocal x := by
  ext <;> simp [reciprocal]

theorem act_negP (x : T) : act !![-1, 0; 0, 1] x = -x := by
  ext <;> simp

theorem act_negOne (x : T) : act (-1) x = oplusInverse x := by
  ext <;> simp [oplusInverse]

theorem act_quarterTurn (x : T) : act !![0, 1; -1, 0] x = «ω» ⊗ x := by
  ext <;> simp [otimes, «ω»]

/-! ## The Möbius transformations are the maps that respect `⊕` -/

/-- Every map that respects `⊕` is a Möbius transformation: the matrix whose columns are the images of
`ω` and `0`. -/
theorem eq_act_of_oplus (f : T → T) (hf : ∀ x y, f (x ⊕ y) = (f x ⊕ f y)) :
    f = act !![(f «ω»).p, (f 0).p; (f «ω»).q, (f 0).q] := by
  have h0 : f «0ω» = «0ω» := by
    have h := hf «0ω» «0ω»
    rw [oplus_zeroOmega] at h
    generalize f «0ω» = a at h ⊢
    have hp := congrArg T.p h
    have hq := congrArg T.q h
    simp only [oplus] at hp hq
    ext <;> simp [«0ω»] <;> omega
  have hneg : ∀ x, f (oplusInverse x) = oplusInverse (f x) := fun x => by
    have h := hf x (oplusInverse x)
    rw [oplus_oplusInverse, h0] at h
    generalize f (oplusInverse x) = b at h ⊢
    have hp := congrArg T.p h
    have hq := congrArg T.q h
    simp only [oplus, «0ω»] at hp hq
    ext <;> simp only [oplusInverse] <;> omega
  have hnat : ∀ n : ℕ, ∀ x, f (scale n x) = scale n (f x) := by
    intro n
    induction n with
    | zero =>
      intro x
      have hs : scale ((0 : ℕ) : ℤ) x = «0ω» := by ext <;> simp [scale, «0ω»]
      rw [hs, h0]
      ext <;> simp [scale, «0ω»]
    | succ n ih =>
      intro x
      have hs : scale ((n + 1 : ℕ) : ℤ) x = (scale n x ⊕ x) := by
        ext <;> simp [scale, oplus] <;> ring
      rw [hs, hf, ih]
      ext <;> simp [scale, oplus] <;> ring
  have hint : ∀ n : ℤ, ∀ x, f (scale n x) = scale n (f x) := by
    intro n x
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · exact hnat m x
    · have hs : scale (-(m : ℤ)) x = oplusInverse (scale m x) := by
        ext <;> simp [scale, oplusInverse]
      rw [hs, hneg, hnat]
      ext <;> simp [scale, oplusInverse]
  funext x
  have hx : x = (scale x.p «ω» ⊕ scale x.q 0) := by
    ext <;> simp [scale, oplus, «ω»]
  rw [hx, hf, hint, hint]
  ext <;> simp [scale, oplus, act, «ω»] <;> ring

/-! ## Each product as a family -/

/-- Multiplying by `y` in `ω² = a + b·ω`, as a matrix. -/
def qmat (a b : ℤ) (y : T) : Matrix (Fin 2) (Fin 2) ℤ := !![y.q + b * y.p, y.p; a * y.p, y.q]

theorem qtimes_eq_act (a b : ℤ) (x y : T) : qtimes a b x y = act (qmat a b y) x := by
  ext <;> simp [qtimes, qmat] <;> ring

/-- `trace² − 4·det`: negative for elliptic, zero for parabolic, positive for hyperbolic. -/
def disc (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := M.trace ^ 2 - 4 * M.det

/-- The determinant of multiplying by `y` is `y`'s norm. -/
theorem det_qmat (a b : ℤ) (y : T) : (qmat a b y).det = y.q ^ 2 + b * y.p * y.q - a * y.p ^ 2 := by
  simp [qmat, det_fin_two_of]; ring

/-- The discriminant of multiplying by `y` is `y.p²` times the ring's discriminant. -/
theorem disc_qmat (a b : ℤ) (y : T) : disc (qmat a b y) = y.p ^ 2 * (b ^ 2 + 4 * a) := by
  simp [disc, qmat, det_fin_two_of, trace_fin_two_of]; ring

theorem otimes_eq_act (x y : T) : x ⊗ y = act !![y.q, y.p; -y.p, y.q] x := by
  ext <;> simp [otimes] <;> ring

theorem plus_eq_act (x y : T) : x + y = act !![y.q, y.p; 0, y.q] x := by
  ext <;> simp <;> ring

theorem splitTimes_eq_act (x y : T) : x ⊚ y = act !![y.q, y.p; y.p, y.q] x := by
  ext <;> simp [splitTimes, qtimes] <;> ring

theorem times_eq_act (x y : T) : x * y = act !![y.p, 0; 0, y.q] x := by
  ext <;> simp <;> ring

theorem par_eq_act (x y : T) : x ∥ y = act !![y.p, 0; y.q, y.p] x := by
  ext <;> simp [par] <;> ring

theorem disc_otimes (y : T) : disc !![y.q, y.p; -y.p, y.q] = -4 * y.p ^ 2 := by
  simp [disc, det_fin_two_of, trace_fin_two_of]; ring

theorem disc_plus (y : T) : disc !![y.q, y.p; 0, y.q] = 0 := by
  simp [disc, det_fin_two_of, trace_fin_two_of]; ring

theorem disc_splitTimes (y : T) : disc !![y.q, y.p; y.p, y.q] = 4 * y.p ^ 2 := by
  simp [disc, det_fin_two_of, trace_fin_two_of]; ring

theorem disc_times (y : T) : disc !![y.p, 0; 0, y.q] = (y.p - y.q) ^ 2 := by
  simp [disc, det_fin_two_of, trace_fin_two_of]; ring

theorem disc_par (y : T) : disc !![y.p, 0; y.q, y.p] = 0 := by
  simp [disc, det_fin_two_of, trace_fin_two_of]; ring

/-! ## Fixed points are the zero divisors -/

/-- A ray `x` is fixed by multiplying by `y` exactly when this is `0`, and it is `y.p` times `x`'s norm. -/
theorem det_qtimes_self (a b : ℤ) (x y : T) :
    det x (qtimes a b x y) = y.p * (x.q ^ 2 + b * x.p * x.q - a * x.p ^ 2) := by
  simp [det, qtimes]; ring

theorem fixed_iff_norm_eq_zero (a b : ℤ) {y : T} (hy : y.p ≠ 0) (x : T) :
    det x (qtimes a b x y) = 0 ↔ x.q ^ 2 + b * x.p * x.q - a * x.p ^ 2 = 0 := by
  rw [det_qtimes_self, mul_eq_zero, or_iff_right hy]

theorem det_times_self (x y : T) : det x (x * y) = x.p * x.q * (y.p - y.q) := by
  simp [det]; ring

theorem det_par_self (x y : T) : det x (x ∥ y) = -(x.p ^ 2 * y.q) := by
  simp [det, par]; ring

/-! ## Sandwiches -/

/-- `op` carried through `g` and back. -/
def sandwich (g : T ≃ T) (op : T → T → T) (x y : T) : T := g.symm (op (g x) (g y))

/-- `g` takes the sandwich to the original: it is an isomorphism, by construction. -/
theorem sandwich_hom (g : T ≃ T) (op : T → T → T) (x y : T) :
    g (sandwich g op x y) = op (g x) (g y) := by
  simp [sandwich]

theorem sandwich_comm (g : T ≃ T) {op : T → T → T} (h : ∀ x y, op x y = op y x) (x y : T) :
    sandwich g op x y = sandwich g op y x := by
  simp [sandwich, h]

theorem sandwich_assoc (g : T ≃ T) {op : T → T → T} (h : ∀ x y z, op (op x y) z = op x (op y z))
    (x y z : T) : sandwich g op (sandwich g op x y) z = sandwich g op x (sandwich g op y z) := by
  simp [sandwich, h]

theorem sandwich_oplus (g : T ≃ T) (hg : ∀ x y, g (x ⊕ y) = (g x ⊕ g y)) {op : T → T → T}
    (h : ∀ x y z, op (x ⊕ y) z = (op x z ⊕ op y z)) (x y z : T) :
    sandwich g op (x ⊕ y) z = (sandwich g op x z ⊕ sandwich g op y z) := by
  apply g.injective
  rw [sandwich_hom, hg, h, hg, sandwich_hom, sandwich_hom]

/-- The reciprocal, as an equivalence. -/
def reciprocalEquiv' : T ≃ T := ⟨reciprocal, reciprocal, fun _ => rfl, fun _ => rfl⟩

/-- `∥` is `+` carried through the reciprocal. -/
theorem par_eq_sandwich (x y : T) : x ∥ y = sandwich reciprocalEquiv' (· + ·) x y :=
  par_eq x y

/-- `T(p, q) ↦ T(p − q, q)`, the basis in which `*` is `qtimes 0 1`. -/
def prodBasis : T ≃ T where
  toFun x := ⟨x.p - x.q, x.q⟩
  invFun x := ⟨x.p + x.q, x.q⟩
  left_inv x := by cases x; simp
  right_inv x := by cases x; simp

/-- `*` is `qtimes 0 1` carried through `prodBasis`. -/
theorem times_eq_sandwich (x y : T) : x * y = sandwich prodBasis (qtimes 0 1) x y := by
  ext <;> simp [sandwich, prodBasis, qtimes]; ring

/-- The light-cone map, `T(p, q) ↦ T(p + q, q − p)`: a Möbius transformation of determinant `2`. -/
def lightConeMap (x : T) : T := act !![1, 1; -1, 1] x

theorem det_lightConeMap : (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 2 := by
  simp [det_fin_two_of]

/-- It takes `⊚` to `*`. -/
theorem lightConeMap_splitTimes (x y : T) : lightConeMap (x ⊚ y) = lightConeMap x * lightConeMap y := by
  ext <;> simp [lightConeMap, splitTimes, qtimes] <;> ring

/-- Conjugating by an invertible matrix keeps the discriminant: a sandwich keeps a product's type. -/
theorem disc_conj (P P' M : Matrix (Fin 2) (Fin 2) ℤ) (h : P' * P = 1) : disc (P * M * P') = disc M := by
  have ht : (P * M * P').trace = M.trace := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.one_mul]
  have hd : (P * M * P').det = M.det := by
    have hu : P'.det * P.det = 1 := by rw [← det_mul, h, det_one]
    rw [det_mul, det_mul]
    linear_combination M.det * hu
  simp [disc, ht, hd]

/-! ## The model's `E` -/

/-- `z(x ⊗ y) = z(x) ⊗ z(y)`: the doubled angle is multiplicative. -/
theorem doubleAngle_otimes (x y : T) : doubleAngle (x ⊗ y) = doubleAngle x ⊗ doubleAngle y := by
  ext <;> simp [doubleAngle, otimes] <;> ring

/-- And the norm is. So `E = z / N` sends `⊗` to multiplication on the unit circle. -/
theorem norm_otimes (x y : T) : norm (x ⊗ y) = norm x * norm y := by
  simp [norm, otimes]; ring

end T
