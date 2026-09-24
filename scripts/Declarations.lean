import CottLean

/-!
# The name of every declaration

Run with `lake env lean scripts/Declarations.lean` after `lake build`. It writes `declarations.txt`: the
name of every declaration in every `CottLean` module, one per line, sorted. cott-engine cites these
names for what each of its operations and tests rests on, and fails its build on a citation that is not
in the file. Compiler-generated names (`match_1`, `proof_2`, `eq_1`, private names, ...) are left out,
since nothing can cite them. The model's own `_0` and `_1` are kept, though Lean's `isInternalDetail`
would drop them for their leading underscore.
-/

open Lean Elab Command

/-- `s` is `pre` followed by digits, possibly separated by underscores (`match_1_1`). -/
def numbered (pre s : String) : Bool :=
  s.startsWith pre && s.length > pre.length && (s.drop pre.length).all (fun ch => ch.isDigit || ch == '_')

/-- A component the compiler generated: `match_1`, `proof_2`, `eq_1`, `_private`, and the like. A
leading underscore followed by digits is the model's spelling (`_0`, `_1`) and is kept. -/
def generated (s : String) : Bool :=
  numbered "match_" s || numbered "proof_" s || numbered "eq_" s ||
    (s.startsWith "_" && !numbered "_" s)

/-- A name nothing can cite: private, or with a generated or numeric component. -/
def uncitable (c : Name) : Bool :=
  isPrivateName c || c.components.any fun
    | .str _ s => generated (s.splitOn "." |>.getLast!)
    | _ => true

elab "#write_declarations " pfx:ident path:str : command => do
  let env ← getEnv
  let mut names : Array String := #[]
  for h : i in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]
    unless pfx.getId.isPrefixOf mod do continue
    for c in env.header.moduleData[i]!.constNames do
      unless uncitable c do names := names.push c.toString
  if names.isEmpty then
    throwError "no declarations under {pfx.getId}"
  let sorted := names.qsort (· < ·)
  IO.FS.writeFile path.getString (String.intercalate "\n" sorted.toList ++ "\n")
  logInfo m!"{sorted.size} declarations written to {path.getString}"

#write_declarations CottLean "declarations.txt"
