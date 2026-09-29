import CottLean.Physics.Center

/-!
# Vertices that cannot violate the ℤ₆ quotient

A center charge is an element of `ZMod 6`, carried into T as a power of `1` under the Eisenstein
product (`Charge.toT`). That map is an isomorphism onto the six units (`toT_add`, `toT_injective`,
`toT_mem`), so adding charges is multiplying units.

A `Vertex` carries a proof that its legs are neutral. It cannot be constructed otherwise, so a
process that breaks the quotient cannot be written down. Gluing two vertices along an internal line
gives a vertex again (`glue`), so every diagram built from vertices is neutral too.

**The limit of what this enforces.** Only the center is checked. `center_too_weak` is a vertex the
ℤ₆ accepts and the full hypercharge rejects.
-/

namespace T

/-- A center charge: the exponent of `1` in the Eisenstein unit group. -/
abbrev Charge := ZMod 6

/-- The charge as a traction. -/
def Charge.toT (k : Charge) : T := eisPow «1» k.val

theorem toT_zero : (0 : Charge).toT = «0» := by decide
theorem toT_add : ∀ k l : Charge, (k + l).toT = eis k.toT l.toT := by decide
theorem toT_injective : ∀ k l : Charge, k.toT = l.toT → k = l := by decide
theorem toT_mem : ∀ k : Charge, k.toT ∈ units6 := by decide
/-- The antiparticle's charge is the Eisenstein inverse. -/
theorem toT_neg : ∀ k : Charge, eis k.toT (-k).toT = «0» := by decide

/-- A vertex: its legs, all taken as incoming, and the proof that they are neutral. -/
structure Vertex where
  legs : List Charge
  neutral : legs.sum = 0

/-- Contracting a leg `c` of one vertex against a leg `−c` of another keeps neutrality. -/
theorem contract (A B : List Charge) (c : Charge)
    (hA : (A ++ [c]).sum = 0) (hB : ((-c) :: B).sum = 0) : (A ++ B).sum = 0 := by
  simp only [List.sum_append, List.sum_cons, List.sum_nil] at *
  linear_combination hA + hB

/-- Two vertices glued along an internal line are a vertex. -/
def glue (A B : List Charge) (c : Charge)
    (hA : (A ++ [c]).sum = 0) (hB : ((-c) :: B).sum = 0) : Vertex :=
  ⟨A ++ B, contract A B c hA hB⟩

/-- In T: the Eisenstein product of a list's charges is the charge of its sum. -/
theorem foldr_toT (l : List Charge) : (l.map Charge.toT).foldr eis «0» = l.sum.toT := by
  induction l with
  | nil => simp [toT_zero]
  | cons a l ih => simp [ih, toT_add]

/-- Every vertex multiplies out to `0`, the Eisenstein unit, in T itself. -/
theorem Vertex.toT_neutral (v : Vertex) : (v.legs.map Charge.toT).foldr eis «0» = «0» := by
  rw [foldr_toT, v.neutral, toT_zero]

/-! ## Standard Model fields, by `6Y` (input, as in `Center`) -/

def cQ : Charge := 1
def cU : Charge := 4
def cD : Charge := -2
def cL : Charge := -3
def cE : Charge := -6
def cH : Charge := 3

/-- The three Yukawa vertices are constructible. -/
def yukawaDown : Vertex := ⟨[-cQ, cH, cD], by decide⟩
def yukawaUp : Vertex := ⟨[-cQ, -cH, cU], by decide⟩
def yukawaE : Vertex := ⟨[-cL, cH, cE], by decide⟩

/-- `Q̄ H e_R` is not: no `Vertex` has these legs. -/
theorem no_QHe : ¬ ∃ v : Vertex, v.legs = [-cQ, cH, cE] := by
  rintro ⟨v, hv⟩; have := v.neutral; rw [hv] at this; revert this; decide

/-- The center is weaker than hypercharge: `Q̄ H u_R` passes the ℤ₆ check,
but its hypercharges sum to `(−1 + 3 + 4)/6 = 1`, not `0`. -/
theorem center_too_weak :
    ([-cQ, cH, cU] : List Charge).sum = 0 ∧ (-1 + 3 + 4 : ℤ) ≠ 0 := by decide

end T
