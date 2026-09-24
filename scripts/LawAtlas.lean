import CottLean

/-!
# The law atlas, by search

The search behind `CottLean/T/Atlas.lean`: this runs T's real operations over a grid of pairs and reports, for
every pairing of an addition and a multiplication, the strongest grade at which each law holds on the grid.
`T.Atlas.atlas` proves every grade in the table, and this script checks that the grid agrees with
`T.Atlas.table` cell by cell. The `respected` column is still search only.

Run with `lake env lean scripts/LawAtlas.lean`.

Each operation keeps its own unit and inverse. The grades, strongest first:

* `=`  exact, at coordinate equality
* `R`  up to the ray (a positive multiple), or both sides `0ω`
* `Q`  up to the ratio (a non-zero multiple), or both sides `0ω`
* `∥`  parallel: one side a multiple of the other, `0ω` allowed -- the residue grade
* `✗`  fails

A cell `a/b` is grade `a` everywhere and grade `b` on generic inputs: both coordinates non-zero and off
the light lines, `p² ≠ q²`.
-/

open T

structure Op where
  name : String
  f : T → T → T
  e : T
  inv : T → T

def ops : List Op :=
  [ ⟨"⊕", oplus, «0ω», oplusInverse⟩,
    ⟨"+", fun x y => x + y, 0, fun x => -x⟩,
    ⟨"*", fun x y => x * y, «1», reciprocal⟩,
    ⟨"⊗", otimes, 0, fun x => -x⟩,
    ⟨"⊚", splitTimes, 0, fun x => -x⟩,
    ⟨"∥", par, «ω», fun x => ⟨x.p, -x.q⟩⟩ ]

def cross (a b : T) : Int := a.q * b.p - a.p * b.q
def dotp (a b : T) : Int := a.q * b.q + a.p * b.p
def isZ (a : T) : Bool := a.p == 0 && a.q == 0

def agree : Nat → T → T → Bool
  | 0, a, b => a == b
  | 1, a, b => (isZ a && isZ b) || (!isZ a && !isZ b && cross a b == 0 && dotp a b > 0)
  | 2, a, b => (isZ a && isZ b) || (!isZ a && !isZ b && cross a b == 0)
  | 3, a, b => cross a b == 0
  | _, _, _ => true

def gradeName : Nat → String
  | 0 => "=" | 1 => "R" | 2 => "Q" | 3 => "∥" | _ => "✗"

def generic (x : T) : Bool := x.p != 0 && x.q != 0 && x.p * x.p != x.q * x.q

def grid (n : Int) : List T :=
  (List.range (2 * n.toNat + 1)).flatMap fun i =>
    (List.range (2 * n.toNat + 1)).map fun j => ⟨(i : Int) - n, (j : Int) - n⟩

def pts3 : List T := grid 2          -- 25 pairs, for laws in up to three variables
def pts4 : List T := (grid 2).filter fun x => (x.p + 2 * x.q) % 3 == 0  -- a spread subset, for four

def tuples : Nat → List T → List (List T)
  | 0, _ => [[]]
  | k + 1, s => s.flatMap fun x => (tuples k s).map (x :: ·)

structure Law where
  name : String
  arity : Nat
  sides : Op → Op → List T → T × T

def v (l : List T) (i : Nat) : T := l.getD i «0ω»

def laws : List Law :=
  [ ⟨"A comm", 2, fun A _ l => (A.f (v l 0) (v l 1), A.f (v l 1) (v l 0))⟩,
    ⟨"A assoc", 3, fun A _ l => (A.f (A.f (v l 0) (v l 1)) (v l 2), A.f (v l 0) (A.f (v l 1) (v l 2)))⟩,
    ⟨"A unit", 1, fun A _ l => (A.f (v l 0) A.e, v l 0)⟩,
    ⟨"A inv", 1, fun A _ l => (A.f (v l 0) (A.inv (v l 0)), A.e)⟩,
    ⟨"M comm", 2, fun _ M l => (M.f (v l 0) (v l 1), M.f (v l 1) (v l 0))⟩,
    ⟨"M assoc", 3, fun _ M l => (M.f (M.f (v l 0) (v l 1)) (v l 2), M.f (v l 0) (M.f (v l 1) (v l 2)))⟩,
    ⟨"M unit", 1, fun _ M l => (M.f (v l 0) M.e, v l 0)⟩,
    ⟨"M inv", 1, fun _ M l => (M.f (v l 0) (M.inv (v l 0)), M.e)⟩,
    ⟨"distrib", 3, fun A M l =>
      (M.f (A.f (v l 0) (v l 1)) (v l 2), A.f (M.f (v l 0) (v l 2)) (M.f (v l 1) (v l 2)))⟩,
    ⟨"zero·x", 1, fun A M l => (M.f A.e (v l 0), A.e)⟩,
    ⟨"(-x)y", 2, fun A M l => (M.f (A.inv (v l 0)) (v l 1), A.inv (M.f (v l 0) (v l 1)))⟩,
    ⟨"-(x+y)", 2, fun A _ l => (A.inv (A.f (v l 0) (v l 1)), A.f (A.inv (v l 0)) (A.inv (v l 1)))⟩,
    ⟨"/(xy)", 2, fun _ M l => (M.inv (M.f (v l 0) (v l 1)), M.f (M.inv (v l 0)) (M.inv (v l 1)))⟩,
    ⟨"--x", 1, fun A _ l => (A.inv (A.inv (v l 0)), v l 0)⟩,
    ⟨"//x", 1, fun _ M l => (M.inv (M.inv (v l 0)), v l 0)⟩,
    ⟨"x/y·z/w", 4, fun _ M l =>
      (M.f (M.f (v l 0) (M.inv (v l 1))) (M.f (v l 2) (M.inv (v l 3))),
       M.f (M.f (v l 0) (v l 2)) (M.inv (M.f (v l 1) (v l 3))))⟩ ]

/-- The strongest grade that holds on every tuple, and a tuple where exact fails. -/
def grade (A M : Op) (law : Law) (inputs : List (List T)) : Nat × Option (List T) :=
  let g := ([0, 1, 2, 3].find? fun g => inputs.all fun l => let (a, b) := law.sides A M l; agree g a b).getD 4
  let cex := inputs.find? fun l => let (a, b) := law.sides A M l; !agree 0 a b
  (g, cex)

def showT (x : T) : String := s!"T({x.p},{x.q})"

/-- Scaling by `k`, which moves a pair along its ray (`k > 0`) or its ratio (`k ≠ 0`). -/
def sc (k : Int) (x : T) : T := ⟨k * x.p, k * x.q⟩

/-- Does the binary operation respect grade `g` as an equality, on the grid? -/
def respects2 (g : Nat) (f : T → T → T) : Bool :=
  g == 0 || (([2, 3] ++ if g == 2 then [-1, -2] else []).all fun k =>
    pts3.all fun x => pts3.all fun y => agree g (f (sc k x) y) (f x y) && agree g (f y (sc k x)) (f y x))

def respects1 (g : Nat) (f : T → T) : Bool :=
  g == 0 || (([2, 3] ++ if g == 2 then [-1, -2] else []).all fun k =>
    pts3.all fun x => agree g (f (sc k x)) (f x))

/-- The same operations and laws, as `T.Atlas` names them, in the same order. -/
def atlasOps : List Atlas.Op := [.oplus, .plus, .times, .otimes, .split, .par]

def atlasLaws : List Atlas.Law :=
  [.aComm, .aAssoc, .aUnit, .aInv, .mComm, .mAssoc, .mUnit, .mInv,
    .distrib, .zeroMul, .negMul, .negAdd, .invMul, .negNeg, .invInv, .fracMul]

def main : IO Unit := do
  IO.println ("| add | mul | " ++ String.intercalate " | " (laws.map (·.name)) ++ " | needs | respected |")
  IO.println ("|---|---|" ++ String.join (laws.map fun _ => "---|") ++ "---|---|")
  let mut notes : Array String := #[]
  let mut mismatches : Array String := #[]
  for (A, A') in ops.zip atlasOps do
    for (M, M') in ops.zip atlasOps do
      let mut cells : Array String := #[]
      let mut need := 0
      let mut broken : Array String := #[]
      for (law, law') in laws.zip atlasLaws do
        let base := if law.arity == 4 then pts4 else pts3
        let all := tuples law.arity base
        let gen := all.filter (·.all generic)
        let (g, _) := grade A M law all
        let (g', cex) := grade A M law gen
        let (t, t') := Atlas.table A' M' law'
        if g != t.rank || g' != t'.rank then
          mismatches := mismatches.push s!"({A.name}, {M.name}) {law.name}: grid {gradeName g}/{gradeName g'}"
        cells := cells.push (if g == g' then gradeName g else s!"{gradeName g}/{gradeName g'}")
        need := max need g'
        if g' ≥ 3 then
          broken := broken.push law.name
          if let some l := cex then
            notes := notes.push s!"({A.name}, {M.name}) {law.name}: generic counterexample {l.map showT}"
      -- Parallel is not an equivalence, so a law needing it has no equality to hold at.
      let resp :=
        if need ≥ 3 then s!"— ({String.intercalate ", " broken.toList})"
        else
          let checks := [("A", respects2 need A.f), ("M", respects2 need M.f),
            ("A⁻¹", respects1 need A.inv), ("M⁻¹", respects1 need M.inv)]
          let bad := checks.filter (!·.2) |>.map (·.1)
          if bad.isEmpty then "all four" else s!"not by {String.intercalate ", " bad}"
      IO.println s!"| {A.name} | {M.name} | {String.intercalate " | " cells.toList} | {gradeName need} | {resp} |"
  IO.println ""
  for n in notes.toList.take 40 do IO.println n
  IO.println ""
  if mismatches.isEmpty then IO.println "The grid agrees with T.Atlas.table in every cell."
  else for m in mismatches do IO.println s!"MISMATCH {m}"

#eval main
