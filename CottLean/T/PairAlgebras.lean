import CottLean.T.Unquotiented

/-!
# Each reading is the homomorphism of an algebra on the pairs

`Unquotiented` reads one pair seven ways. Here each reading `R` gets the operations on pairs that it
turns into `+` and `×`: `R (x ⊞ y) = R x + R y` and `R (x ⊠ y) = R x · R y`. The pairs are `ℝ × ℝ`, with
`x.1 = p` and `x.2 = q`.

| reading | `+` on pairs | `×` on pairs | the algebra |
|---|---|---|---|
| `C` | `+` (`⊕`) | `⊗` | ℂ: `C` loses nothing (`C_add`, `C_pairOtimes`, `C_injective`) |
| `D`, `S` | `+` (`⊕`) | `⊚` | ℝ × ℝ in the coordinates `(S, D)` (`D_add`, `S_add`, `D_pairSplit`, `S_pairSplit`, `SD_injective`) |
| `Q` | `+`, fractions | `*` | a wheel: `*` distributes over `+` only up to the scale `z.q` (`Q_pairPlus`, `Q_pairTimes`, `pairPlus_pairTimes`) |
| `P` | none homogeneous | `*` | `P_pairTimes`; no operation homogeneous in one argument adds `P` (`no_homogeneous_P_add`) |

The degree argument behind the `P` row: an operation that is homogeneous in its left argument, as every
bilinear one is (`pairPlus_homogeneous`, `pairOtimes_homogeneous`, `pairSplit_homogeneous`,
`pairTimes_homogeneous`), scales `P` of its result by `t²` when the left argument is scaled by `t`. But
`P x + P y` scales only its first term. So `P`'s addition needs a layer: `P(eᵖ, e^q) = e^S` (`P_exp`) makes
`P`'s `×` the `S` of the exponents, and its `+` is not a flat pair operation.

## Converting between algebras

The conversion to `(S, D)` is `⊗ T(1,1)` (`pairOtimes_one`), invertible (`toSD`). It carries `+` exactly
(`toSD_add`), and `⊗` up to the residue `T(1,1)` (`toSD_pairOtimes`). It does not carry `⊗` to `⊚`
(`toSD_not_split`), and nothing can: `⊚` has zero divisors on the light lines (`pairSplit_light`), so no
injective map that fixes `0` takes `⊗` to `⊚` (`no_otimes_to_split`). ℂ and ℝ × ℝ are different rings on
the same pairs.

What a conversion always does is carry a product across, `g⁻¹(g x · g y)` (`carry`). Carrying `⊚` back
through `toSD` gives `(−2pr, 2qs)` in the original coordinates (`carry_split_eq`), the third algebra, which
keeps `⊚`'s laws (`carry_comm`, `carry_assoc`, `carry_add`).

Not here: `L` has `⊗` as its `+` (`L_pairOtimes`, in `LogPair`), but no flat product. Its `×` is a
power, a nested pair; no statement that a flat one is impossible is proved.
-/

namespace T.Unquotiented

open Complex

/-! ## `C`: `+` and `⊗` are ℂ -/

theorem C_add (x y : ℝ × ℝ) : C (x + y).1 (x + y).2 = C x.1 x.2 + C y.1 y.2 := by
  apply Complex.ext <;> simp [C]

theorem C_injective {x y : ℝ × ℝ} (h : C x.1 x.2 = C y.1 y.2) : x = y := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [C_re, C_im] at h1 h2
  exact Prod.ext h2 h1

/-! ## `D` and `S`: `+` and `⊚` are ℝ × ℝ -/

theorem D_add (x y : ℝ × ℝ) : D (x + y).1 (x + y).2 = D x.1 x.2 + D y.1 y.2 := by
  simp only [D, Prod.fst_add, Prod.snd_add]; ring

theorem S_add (x y : ℝ × ℝ) : S (x + y).1 (x + y).2 = S x.1 x.2 + S y.1 y.2 := by
  simp only [S, Prod.fst_add, Prod.snd_add]; ring

/-- `S` and `D` together lose nothing. -/
theorem SD_injective {x y : ℝ × ℝ} (hS : S x.1 x.2 = S y.1 y.2) (hD : D x.1 x.2 = D y.1 y.2) :
    x = y := by
  simp only [S, D] at hS hD
  ext <;> linarith

/-- `⊚` has zero divisors: `(1, 1) ⊚ (−1, 1) = (0, 0)`, a product of the two light lines. -/
theorem pairSplit_light : pairSplit (1, 1) (-1, 1) = (0, 0) := by
  ext <;> norm_num [pairSplit]

/-! ## `Q`: `+` and `*` are a wheel -/

theorem Q_pairTimes (x y : ℝ × ℝ) :
    Q (pairTimes x y).1 (pairTimes x y).2 = Q x.1 x.2 * Q y.1 y.2 := by
  simp only [Q, pairTimes]; exact (div_mul_div_comm _ _ _ _).symm

theorem Q_pairPlus {x y : ℝ × ℝ} (hx : x.2 ≠ 0) (hy : y.2 ≠ 0) :
    Q (pairPlus x y).1 (pairPlus x y).2 = Q x.1 x.2 + Q y.1 y.2 := by
  simp only [Q, pairPlus]; field_simp

/-- `*` distributes over `+` up to the scale `z.q`, the wheel's law. -/
theorem pairPlus_pairTimes (x y z : ℝ × ℝ) :
    pairPlus (pairTimes x z) (pairTimes y z) = z.2 • pairTimes (pairPlus x y) z := by
  ext <;> simp [pairPlus, pairTimes] <;> ring

theorem pairPlus_pairTimes_ne :
    pairPlus (pairTimes (1, 1) (1, 2)) (pairTimes (1, 1) (1, 2)) ≠
      pairTimes (pairPlus (1, 1) (1, 1)) (1, 2) := by
  intro h
  have := congrArg Prod.snd h
  norm_num [pairPlus, pairTimes] at this

/-! ## `P`: `*` multiplies, and no homogeneous operation adds -/

theorem P_pairTimes (x y : ℝ × ℝ) :
    P (pairTimes x y).1 (pairTimes x y).2 = P x.1 x.2 * P y.1 y.2 := by
  simp only [P, pairTimes]; ring

theorem pairPlus_homogeneous (t : ℝ) (x y : ℝ × ℝ) : pairPlus (t • x) y = t • pairPlus x y := by
  ext <;> simp [pairPlus] <;> ring
theorem pairOtimes_homogeneous (t : ℝ) (x y : ℝ × ℝ) :
    pairOtimes (t • x) y = t • pairOtimes x y := by
  ext <;> simp [pairOtimes] <;> ring
theorem pairSplit_homogeneous (t : ℝ) (x y : ℝ × ℝ) : pairSplit (t • x) y = t • pairSplit x y := by
  ext <;> simp [pairSplit] <;> ring
theorem pairTimes_homogeneous (t : ℝ) (x y : ℝ × ℝ) : pairTimes (t • x) y = t • pairTimes x y := by
  ext <;> simp [pairTimes] <;> ring

/-- No operation homogeneous in its left argument adds `P`. At `x = y = (1, 1)`, scaling `x` by `2` makes
`P` of the result `4·2 = 8`, while `P(2x) + P(y) = 4 + 1 = 5`. -/
theorem no_homogeneous_P_add (op : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ)
    (hom : ∀ (t : ℝ) x y, op (t • x) y = t • op x y)
    (hP : ∀ x y, P (op x y).1 (op x y).2 = P x.1 x.2 + P y.1 y.2) : False := by
  have a := hP ((2 : ℝ) • ((1 : ℝ), (1 : ℝ))) (1, 1)
  have b := hP (1, 1) (1, 1)
  rw [hom] at a
  simp only [P, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at a b
  nlinarith

/-- `⊕` does not add `P` either: `(1, 1) + (1, 1) = (2, 2)`, with `P = 4`, not `2`. -/
theorem oplus_P_add_fails :
    P ((1, 1) + (1, 1) : ℝ × ℝ).1 ((1, 1) + (1, 1) : ℝ × ℝ).2 ≠ P 1 1 + P 1 1 := by
  norm_num [P]

/-! ## Converting between `C` and `(S, D)` -/

/-- The conversion `(p, q) ↦ (S, D)`, which is `⊗ T(1,1)`, with its inverse. -/
noncomputable def toSD : ℝ × ℝ ≃ ℝ × ℝ where
  toFun x := (S x.1 x.2, D x.1 x.2)
  invFun v := ((v.1 - v.2) / 2, (v.1 + v.2) / 2)
  left_inv x := by ext <;> simp [S, D] <;> ring
  right_inv v := by ext <;> simp [S, D] <;> ring

theorem toSD_apply (x : ℝ × ℝ) : toSD x = pairOtimes x (1, 1) := by
  rw [show x = (x.1, x.2) from rfl, pairOtimes_one]; rfl

theorem toSD_add (x y : ℝ × ℝ) : toSD (x + y) = toSD x + toSD y := by
  ext <;> simp [toSD, S, D] <;> ring

/-- `toSD` carries `⊗` up to the residue `T(1,1)`: both sides are `x ⊗ y ⊗ T(1,1) ⊗ T(1,1)`. -/
theorem toSD_pairOtimes (x y : ℝ × ℝ) :
    pairOtimes (toSD (pairOtimes x y)) (1, 1) = pairOtimes (toSD x) (toSD y) := by
  ext <;> simp [toSD, pairOtimes, S, D] <;> ring

/-- It does not carry `⊗` to `⊚`: `1 ⊗ 1 = 1` as points, `(0, 1)`, and `toSD` of it is `(1, 1)`,
while `(1, 1) ⊚ (1, 1) = (2, 2)`. -/
theorem toSD_not_split :
    toSD (pairOtimes (0, 1) (0, 1)) ≠ pairSplit (toSD (0, 1)) (toSD (0, 1)) := by
  intro h
  have := congrArg Prod.fst h
  norm_num [toSD, pairOtimes, pairSplit, S, D] at this

/-- No injective map fixing `0` takes `⊗` to `⊚`: ℂ has no zero divisors and `⊚` does. -/
theorem no_otimes_to_split (f : ℝ × ℝ → ℝ × ℝ) (hf : Function.Bijective f) (h0 : f (0, 0) = (0, 0))
    (hm : ∀ x y, f (pairOtimes x y) = pairSplit (f x) (f y)) : False := by
  obtain ⟨a, ha⟩ := hf.2 (1, 1)
  obtain ⟨b, hb⟩ := hf.2 (-1, 1)
  have hab : pairOtimes a b = (0, 0) := hf.1 (by rw [hm, ha, hb, pairSplit_light, h0])
  have hC : C a.1 a.2 * C b.1 b.2 = 0 := by
    rw [← C_pairOtimes, hab]; rfl
  rcases mul_eq_zero.mp hC with hz | hz
  · obtain ⟨h1, h2⟩ := (C_eq_zero_iff _ _).mp hz
    have : a = (0, 0) := Prod.ext h1 h2
    rw [this, h0] at ha
    simp at ha
  · obtain ⟨h1, h2⟩ := (C_eq_zero_iff _ _).mp hz
    have : b = (0, 0) := Prod.ext h1 h2
    rw [this, h0] at hb
    simp at hb

/-! ### Carrying a product across a conversion -/

/-- A product carried through an invertible conversion: `g⁻¹(g x · g y)`. -/
def carry (g : ℝ × ℝ ≃ ℝ × ℝ) (op : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (x y : ℝ × ℝ) : ℝ × ℝ :=
  g.symm (op (g x) (g y))

theorem carry_hom (g : ℝ × ℝ ≃ ℝ × ℝ) (op : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ) (x y : ℝ × ℝ) :
    g (carry g op x y) = op (g x) (g y) := by
  simp [carry]

theorem carry_comm (g : ℝ × ℝ ≃ ℝ × ℝ) {op : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ} (h : ∀ x y, op x y = op y x)
    (x y : ℝ × ℝ) : carry g op x y = carry g op y x := by
  simp [carry, h]

theorem carry_assoc (g : ℝ × ℝ ≃ ℝ × ℝ) {op : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ}
    (h : ∀ x y z, op (op x y) z = op x (op y z)) (x y z : ℝ × ℝ) :
    carry g op (carry g op x y) z = carry g op x (carry g op y z) := by
  simp [carry, h]

theorem carry_add (g : ℝ × ℝ ≃ ℝ × ℝ) (hg : ∀ x y, g (x + y) = g x + g y)
    {op : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ} (h : ∀ x y z, op (x + y) z = op x z + op y z) (x y z : ℝ × ℝ) :
    carry g op (x + y) z = carry g op x z + carry g op y z := by
  apply g.injective
  rw [carry_hom, hg, h, hg, carry_hom, carry_hom]

theorem pairSplit_add (x y z : ℝ × ℝ) : pairSplit (x + y) z = pairSplit x z + pairSplit y z := by
  ext <;> simp [pairSplit] <;> ring

/-- `⊚` carried back through `toSD`, in the original coordinates: `(p, q) · (r, s) = (−2pr, 2qs)`. -/
theorem carry_split_eq (x y : ℝ × ℝ) :
    carry toSD pairSplit x y = (-2 * x.1 * y.1, 2 * x.2 * y.2) := by
  ext <;> simp [carry, toSD, pairSplit, S, D] <;> ring

/-- It keeps `⊚`'s laws: commutative, associative, and distributive over `+`. -/
theorem carry_split_comm (x y : ℝ × ℝ) : carry toSD pairSplit x y = carry toSD pairSplit y x :=
  carry_comm toSD (fun x y => by ext <;> simp [pairSplit] <;> ring) x y

theorem carry_split_assoc (x y z : ℝ × ℝ) :
    carry toSD pairSplit (carry toSD pairSplit x y) z =
      carry toSD pairSplit x (carry toSD pairSplit y z) :=
  carry_assoc toSD (fun x y z => by ext <;> simp [pairSplit] <;> ring) x y z

theorem carry_split_add (x y z : ℝ × ℝ) :
    carry toSD pairSplit (x + y) z = carry toSD pairSplit x z + carry toSD pairSplit y z :=
  carry_add toSD toSD_add pairSplit_add x y z

end T.Unquotiented
