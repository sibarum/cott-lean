import CottLean.Nested.BicomplexRatio

/-!
# The embeddings between the corners

The grid has five corners: flat `T`, `C(T, T)` (`Point`), `T(C, C)` (`RatioPoint`), `C(C, C)`
(`Bicomplex`) and `C(T(C, C), T(C, C))` (`BicomplexRatio`) over all of them. Each file proved its own maps
one at a time. This one fits them together.

## The cube commutes

Every way up from flat `T` to `C(T(C, C), T(C, C))` lands on the same point:

* `face_point`: a flat point through `C(T, T)` or through `C(C, C)`, `ofT2 ∘ ofPoint = ofCC ∘ ofOuter`.
* `face_inner`: a flat point on the inner `i`, through `C(C, C)` or through `T(C, C)`,
  `ofCC ∘ ofInner = ofTC ∘ ofGauss ∘ toGaussian`.
* `face_ratio`: a flat ratio through `C(T, T)` or through `T(C, C)`, `ofT2 ∘ ofRatio = ofTC ∘ castT`.
* `face_combine`: on real ratios, `combine` is the cast, `combine ∘ ofRatio = castT`.

`castT` (a flat ratio, read over ℤ[i]) carries `+`, `*`, `−` and the reciprocal exactly, and `ofGauss`
(`z ↦ z / 1`) carries the ring operations exactly. `rationalize` goes the other way only up to a residue:
`rationalize (castT x)` is `ofRatio x` with the real coordinate scaled by `q` and the imaginary one over
`q²` (`rationalize_castT`).

## ℚ(i) sits in the top corner twice

A point `X` of `C(T, T)` goes up in two ways. `outer X = ofT2 X` puts its imaginary part on the outer `j`.
`inner X = ofTC (combine X)` puts the whole complex number on the inner `i`. They carry the product
differently: `ofT2` carries `⊗` exactly (`CTC.ofT2_otimes`), while `ofTC` carries `*` with the `j` part
left as the residue `T(0, w₁·w₂)` (`ofTC_times`), as `ofRatio` carries `*` in `Point`.

On values (`val_outer`, `val_inner`) the two copies agree exactly on the real axis (`val_outer_eq_inner_iff`).
Reading `j` as `i` identifies them (`evP_outer`, `evP_inner`); reading `j` as `−i` sends one to the
complex conjugate of the other (`evM_outer`, `evM_inner`). That is `Bicomplex`'s inner and outer placements
of a flat point, one level up.

## Once `2` is invertible the two readings are an isomorphism

`Bicomplex` found that reading `j` as `i` and as `−i` together loses nothing but misses `(1, 0)` over ℤ
(`CC.ev_not_surjective`). On the bicomplex numbers it is a ring isomorphism onto `ℂ × ℂ` (`split`), with
inverse `(a, b) ↦ (a + b)/2 − (i·(a − b)/2)·j`.

* `split_val_ofCC`: on a bicomplex integer it is `Bicomplex`'s two evaluations.
* `split_val_half`: the missing `(1, 0)` is the value of `C(−i/2, 1/2)`, a point of
  `C(T(C, C), T(C, C))`. It is the idempotent `(1 − i·j)/2`: `half ⊗ half` is `half` with every
  coordinate scaled by `8` (`otimes_half`).
* `split_val_zeroDivisor`: the zero divisor `1 + i·j` goes to `(0, 2)`.
* `den_ne_zero_iff`: a finite point has `D ≠ 0` exactly when neither evaluation is zero. The light lines
  are the two axes of `ℂ × ℂ`.

## What cannot embed

`C(C, C)`'s product has zero divisors, so it embeds in no domain. No injective map from `C(C, C)` to a
domain is multiplicative (`not_otimes_embeds_domain`). In particular none takes `C(C, C)`'s `⊗` to flat
`⊗`, which is ℤ[i] (`not_otimes_embeds_flat`).
-/

open T Complex

namespace Embeddings

open CC (gi)
open TC (combine rationalize)

/-! ## The edges -/

/-- A flat ratio `T(p, q)` read over the Gaussian integers. -/
def castT (x : T) : TC := ⟨x.p, x.q⟩

theorem castT_injective : Function.Injective castT := fun x y h => by
  have h1 := congrArg TOver.p h
  have h2 := congrArg TOver.q h
  simp only [castT, Int.cast_inj] at h1 h2
  exact T.ext h1 h2

theorem castT_plus (x y : T) : castT (x + y) = castT x + castT y := by
  ext : 1 <;> simp [castT, T.add_def]

theorem castT_times (x y : T) : castT (x * y) = castT x * castT y := by
  ext : 1 <;> simp [castT, T.mul_def]

theorem castT_neg (x : T) : castT (-x) = -castT x := by
  ext : 1 <;> simp [castT, T.neg_def]

theorem castT_reciprocal (x : T) : castT (T.reciprocal x) = TOver.reciprocal (castT x) := rfl

/-- A Gaussian integer `z`, as the ratio `z / 1`. -/
def ofGauss (z : GaussianInt) : TC := ⟨z, 1⟩

theorem ofGauss_injective : Function.Injective ofGauss := fun _ _ h => congrArg TOver.p h

theorem ofGauss_add (z w : GaussianInt) : ofGauss (z + w) = ofGauss z + ofGauss w := by
  ext : 1 <;> simp [ofGauss]

theorem ofGauss_mul (z w : GaussianInt) : ofGauss (z * w) = ofGauss z * ofGauss w := by
  ext : 1 <;> simp [ofGauss]

/-! ## The faces -/

/-- A flat point through `C(T, T)` or through `C(C, C)`. -/
theorem face_point (z : T) : CTC.ofT2 (T2.ofPoint z) = CTC.ofCC (CC.ofOuter z) := by
  ext : 2 <;> simp [CTC.ofT2, T2.ofPoint, ratioInt, CTC.ofCC, CC.ofOuter]

/-- A flat point on the inner unit, through `C(C, C)` or through `T(C, C)`. -/
theorem face_inner (z : T) : CTC.ofCC (CC.ofInner z) = CTC.ofTC (ofGauss (toGaussian z)) := rfl

/-- A flat ratio through `C(T, T)` or through `T(C, C)`. -/
theorem face_ratio (x : T) : CTC.ofT2 (T2.ofRatio x) = CTC.ofTC (castT x) := by
  ext : 2 <;> simp [CTC.ofT2, T2.ofRatio, CTC.ofTC, castT]

/-- On real ratios, `combine` is the cast. -/
theorem face_combine (x : T) : combine (T2.ofRatio x) = castT x := by
  ext <;> simp [combine, T2.ofRatio, castT]

/-- `rationalize` comes back only up to a residue: the real part scaled by `q`, the imaginary over `q²`. -/
theorem rationalize_castT (x : T) :
    rationalize (castT x) = ⟨⟨0, x.q ^ 2⟩, scale x.q x⟩ := by
  ext <;> simp [rationalize, castT, TC.nrm, scale, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

/-! ## Two copies of ℚ(i) -/

/-- A point of `C(T, T)` with its imaginary part on the outer `j`. -/
def outer (X : T2) : CTC := CTC.ofT2 X

/-- A point of `C(T, T)` as one complex number on the inner `i`. -/
def inner (X : T2) : CTC := CTC.ofTC (combine X)

theorem ofTC_oplus (x y : TC) : CTC.oplus (CTC.ofTC x) (CTC.ofTC y) = CTC.ofTC (x + y) := by
  ext : 2 <;> simp [CTC.oplus, CTC.ofTC]

/-- `ofTC` carries `*` with the `j` part left as the residue `T(0, w₁·w₂)`. -/
theorem ofTC_times (x y : TC) :
    CTC.otimes (CTC.ofTC x) (CTC.ofTC y) = ⟨⟨0, y.q * x.q⟩, x * y⟩ := by
  ext : 2 <;> simp [CTC.otimes, CTC.ofTC]

theorem toComplex_gi : GaussianInt.toComplex gi = I := by
  rw [GaussianInt.toComplex_def₂]; apply Complex.ext <;> simp [gi]

theorem val_castT (x : T) : TC.val (castT x) = (T2.rv x : ℂ) := by
  simp [TC.val, castT, T2.rv]

/-- The outer copy: real part on `1`, imaginary part on `j`. -/
theorem val_outer (X : T2) :
    CTC.val (outer X) = ⟨((T2.val X).re : ℂ), ((T2.val X).im : ℂ)⟩ := by
  ext
  · exact val_castT X.q
  · exact val_castT X.p

/-- The inner copy: the whole complex number on `1`. -/
theorem val_inner {X : T2} (hX : T2.Finite X) : CTC.val (inner X) = ⟨T2.val X, 0⟩ := by
  ext
  · show TC.val (combine X) = T2.val X
    exact TC.val_combine hX
  · show TC.val ⟨0, 1⟩ = 0
    simp [TC.val]

/-- The two copies agree exactly on the real axis. -/
theorem val_outer_eq_inner_iff {X : T2} (hX : T2.Finite X) :
    CTC.val (outer X) = CTC.val (inner X) ↔ (T2.val X).im = 0 := by
  rw [val_outer, val_inner hX]
  constructor
  · intro h; have := congrArg QuadraticAlgebra.im h; simpa using this
  · intro h
    ext
    · simp only; apply Complex.ext <;> simp [h]
    · simp [h]

/-! ## Reading `j` as `±i` -/

/-- `j ↦ i`. -/
def evP (z : QuadraticAlgebra ℂ (-1) 0) : ℂ := z.re + I * z.im

/-- `j ↦ −i`. -/
def evM (z : QuadraticAlgebra ℂ (-1) 0) : ℂ := z.re - I * z.im

theorem evP_outer (X : T2) : evP (CTC.val (outer X)) = T2.val X := by
  rw [val_outer]; apply Complex.ext <;> simp [evP]

theorem evP_inner {X : T2} (hX : T2.Finite X) : evP (CTC.val (inner X)) = T2.val X := by
  rw [val_inner hX]; simp [evP]

theorem evM_outer (X : T2) : evM (CTC.val (outer X)) = (starRingEnd ℂ) (T2.val X) := by
  rw [val_outer]; apply Complex.ext <;> simp [evM]

theorem evM_inner {X : T2} (hX : T2.Finite X) : evM (CTC.val (inner X)) = T2.val X := by
  rw [val_inner hX]; simp [evM]

/-! ## The isomorphism once `2` is invertible -/

/-- The bicomplex numbers are `ℂ × ℂ`, by reading `j` as `i` and as `−i`. -/
noncomputable def split : QuadraticAlgebra ℂ (-1) 0 ≃+* ℂ × ℂ where
  toFun z := (evP z, evM z)
  invFun w := ⟨(w.1 + w.2) / 2, -I * (w.1 - w.2) / 2⟩
  left_inv z := by
    ext
    · simp only [evP, evM]; ring
    · simp only [evP, evM]; linear_combination (-z.im) * I_sq
  right_inv w := by
    ext
    · simp only [evP]; linear_combination (-(w.1 - w.2) / 2) * I_sq
    · simp only [evM]; linear_combination ((w.1 - w.2) / 2) * I_sq
  map_mul' z w := by
    ext
    · simp only [evP, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, Prod.fst_mul]
      linear_combination (-(z.im * w.im)) * I_sq
    · simp only [evM, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, Prod.snd_mul]
      linear_combination (-(z.im * w.im)) * I_sq
  map_add' z w := by
    ext
    · simp only [evP, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, Prod.fst_add]; ring
    · simp only [evM, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, Prod.snd_add]; ring

theorem split_apply (z : QuadraticAlgebra ℂ (-1) 0) : split z = (evP z, evM z) := rfl

/-- On a bicomplex integer, `split` is `Bicomplex`'s two evaluations. -/
theorem split_val_ofCC (z : CC) :
    split (CTC.val (CTC.ofCC z)) =
      (GaussianInt.toComplex (CC.evPlus z), GaussianInt.toComplex (CC.evMinus z)) := by
  simp [split_apply, evP, evM, CTC.val, CTC.ofCC, TC.val, CC.evPlus, CC.evMinus, toComplex_gi]

/-- `C(−i/2, 1/2)`: the bicomplex number `(1 − i·j)/2`. -/
def half : CTC := ⟨⟨-gi, 2⟩, ⟨1, 2⟩⟩

/-- The `(1, 0)` that `C(C, C)` misses is the value of `half`. -/
theorem split_val_half : split (CTC.val half) = (1, 0) := by
  have h2 : GaussianInt.toComplex 2 = 2 := map_ofNat _ 2
  simp only [split_apply, evP, evM, CTC.val, half, TC.val, map_neg, toComplex_gi, map_one, h2]
  refine Prod.ext ?_ ?_
  · simp only; linear_combination (-1 / 2 : ℂ) * I_sq
  · simp only; linear_combination (1 / 2 : ℂ) * I_sq

/-- `half` is idempotent up to scaling every coordinate by `8`. -/
theorem otimes_half : CTC.otimes half half = ⟨⟨8 * -gi, 8 * 2⟩, ⟨8 * 1, 8 * 2⟩⟩ := by
  ext : 2 <;> simp [CTC.otimes, half] <;>
    first | ring1 | linear_combination (-4 : GaussianInt) * CC.gi_mul_gi

/-- The zero divisor `1 + i·j` goes to `(0, 2)`: one evaluation kills it. -/
theorem split_val_zeroDivisor : split (CTC.val CTC.zeroDivisor) = (0, 2) := by
  rw [CTC.zeroDivisor, split_val_ofCC]
  refine Prod.ext ?_ ?_
  · simp only; rw [show CC.evPlus ⟨gi, 1⟩ = 0 by decide, map_zero]
  · simp only; rw [show CC.evMinus ⟨gi, 1⟩ = 2 by decide]; exact map_ofNat _ 2

/-- A finite point has `D ≠ 0` exactly when neither evaluation is zero. -/
theorem den_ne_zero_iff {x : CTC} (hx : CTC.Finite x) :
    CTC.den x ≠ 0 ↔ evP (CTC.val x) ≠ 0 ∧ evM (CTC.val x) ≠ 0 := by
  rw [← CTC.isUnit_val_iff hx, ← MulEquiv.isUnit_map split.toMulEquiv, Prod.isUnit_iff]
  simp [split_apply]

/-! ## What cannot embed -/

/-- No injective map from `C(C, C)` to a domain is multiplicative: the zero divisors have nowhere to go. -/
theorem not_otimes_embeds_domain {R : Type*} [CommRing R] [IsDomain R] (f : CC → R)
    (hf : Function.Injective f) : ¬ ∀ x y, f (CC.otimes x y) = f x * f y := by
  intro h
  have h0 : ∀ x, CC.otimes ⟨0, 0⟩ x = ⟨0, 0⟩ := fun x => by ext1 <;> simp [CC.otimes]
  obtain ⟨hzd, ha, hb⟩ := CC.zero_divisors
  by_cases hf0 : f ⟨0, 0⟩ = 0
  · have := h ⟨gi, 1⟩ ⟨-gi, 1⟩
    rw [hzd, hf0] at this
    rcases mul_eq_zero.mp this.symm with h' | h'
    · exact ha (hf (h'.trans hf0.symm))
    · exact hb (hf (h'.trans hf0.symm))
  · have h1 : ∀ x, f x = 1 := fun x => by
      have := h ⟨0, 0⟩ x
      rw [h0] at this
      exact (mul_left_cancel₀ hf0 (this.symm.trans (mul_one _).symm))
    exact absurd (hf ((h1 ⟨0, 0⟩).trans (h1 ⟨0, 1⟩).symm)) (by decide)

/-- In particular none takes `C(C, C)`'s `⊗` to flat `⊗`, which is ℤ[i]. -/
theorem not_otimes_embeds_flat (f : CC → T) (hf : Function.Injective f) :
    ¬ ∀ x y, f (CC.otimes x y) = f x ⊗ f y := by
  intro h
  refine not_otimes_embeds_domain (toGaussian ∘ f) (toGaussian_injective.comp hf) fun x y => ?_
  simp only [Function.comp, h, toGaussian_otimes]

end Embeddings
