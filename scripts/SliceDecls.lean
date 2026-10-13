import Lean

/-!
# The declaration closure of a slice

`SliceDecls.run out targets` walks, from the target declarations, every constant that their
types and values use, following only constants defined in `LinearAQFT`, `LocalAlgebrasLean` or
`BosonicLean` modules; Mathlib and Lean core are the boundary. This is the traversal of `#print axioms`,
stopped at the library boundary. It writes a JSON record to `out` with:
* `declarations`: the closure, grouped by module;
* `unused`: declarations of those modules that the closure does not use. They measure how
  cleanly the files are split for this slice; they are not an error.

"Used" means "referenced by a type or proof term". A lemma that a tactic used without leaving a
trace in the term (for example a `rfl` lemma applied by `dsimp`) counts as unused, although the
source may still need it to compile; so deleting unused declarations must be followed by a
rebuild. Compiler-generated auxiliary names are omitted from `unused`.

It is run on the environment of a file that imports `LinearAQFT`, through
`python tools/slice_closure.py --decls <manifest>`, which writes that file and calls
`lake env lean` on it.
-/

open Lean

namespace SliceDecls

/-- The module of `n`, if it is one of ours. -/
def ourModule? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let mod ← env.header.moduleNames[idx.toNat]?
  if (`LinearAQFT).isPrefixOf mod || (`LocalAlgebrasLean).isPrefixOf mod ||
      (`BosonicLean).isPrefixOf mod then some mod else none

/-- Auxiliary names that the compiler generates; not reported as unused. -/
def isAux (n : Name) : Bool :=
  n.isInternalDetail || n.components.any fun c =>
    let s := c.toString
    s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
      ["inj", "injEq", "sizeOf_spec", "noConfusion", "noConfusionType", "recOn", "casesOn",
        "below", "brecOn", "binductionOn", "ibelow", "ext_iff", "rec", "ctorIdx"].contains s

/-- The closure of `todo` under "uses", inside our modules. -/
partial def walk (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n || (ourModule? env n).isNone then walk env rest seen
    else
      let used := match env.find? n with
        | some ci => ci.getUsedConstantsAsSet.toList
        | none => []
      walk env (used ++ rest) (seen.insert n)

/-- Write the closure record of `targets` to `out`. -/
def run (out : System.FilePath) (targets : List Name) : CoreM Unit := do
  let env ← getEnv
  for t in targets do
    unless env.contains t do throwError "unknown declaration: {t}"
  let closure := walk env targets {}
  let mods : NameSet := closure.foldl (init := {}) fun s n =>
    match ourModule? env n with | some m => s.insert m | none => s
  -- Our declarations by module, reading only the constants of the closure's modules.
  let mut used : Std.HashMap Name (Array String) := {}
  let mut unused : Std.HashMap Name (Array String) := {}
  for (m, data) in env.header.moduleNames.zip env.header.moduleData do
    if mods.contains m then
      for n in data.constNames do
        if closure.contains n then
          used := used.insert m ((used.getD m #[]).push n.toString)
        else if !isAux n then
          unused := unused.insert m ((unused.getD m #[]).push n.toString)
  let obj := fun (h : Std.HashMap Name (Array String)) =>
    Json.mkObj <| (h.toArray.qsort (fun a b => a.1.toString < b.1.toString)).toList.map
      fun (m, ns) => (m.toString, Json.arr ((ns.qsort (· < ·)).map Json.str))
  let modNames := (mods.toList.map toString).toArray.qsort (· < ·)
  let unusedCount : Nat := unused.fold (init := 0) fun k _ v => k + v.size
  let j := Json.mkObj [
    ("targets", Json.arr (targets.toArray.map (Json.str ∘ toString))),
    ("modules", Json.arr (modNames.map Json.str)),
    ("count", toJson closure.size),
    ("unused_count", toJson unusedCount),
    ("declarations", obj used),
    ("unused", obj unused)]
  IO.FS.writeFile out (j.pretty ++ "\n")
  logInfo m!"{closure.size} declarations in {mods.size} modules; written to {out}"

end SliceDecls
