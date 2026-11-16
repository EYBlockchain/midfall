import Lean

/-!
Dependency-cone queries, the progress and scope measures of EXECUTION-V2 §6.

* `#cone_sorries foo` — declarations in `foo`'s dependency cone whose own type or value uses `sorryAx`.
* `#cone_in foo M` — declarations in `foo`'s cone that live in module `M`.
* `#cone_avoids foo [M₁, …]` — an error if `foo`'s cone touches any listed module.
* `#imports_avoid [M₁, …]` — an error if the current file transitively imports any listed module.
-/

namespace Midfall.Tools
open Lean Elab Command

/-- Visited declarations, and those whose own type or value uses `sorryAx`. -/
structure Cone where
  all : Array Name := #[]
  sorries : Array Name := #[]

partial def coneGo (env : Environment) : List Name → NameSet → Cone → Cone
  | [], _, acc => acc
  | n :: rest, seen, acc =>
    if seen.contains n then coneGo env rest seen acc
    else
      let seen := seen.insert n
      match env.find? n with
      | none => coneGo env rest seen acc
      | some ci =>
        let used : Array Name := ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
        let acc := { acc with
          all := acc.all.push n
          sorries := if used.contains ``sorryAx then acc.sorries.push n else acc.sorries }
        coneGo env (used.foldl (fun l c => if seen.contains c then l else c :: l) rest) seen acc

def cone (env : Environment) (root : Name) : Cone := coneGo env [root] {} {}

/-- The module a declaration comes from (`none` for the current file). -/
def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  env.header.moduleNames[i.toNat]?

def sortNames (xs : Array Name) : Array Name := xs.qsort (fun a b => Name.lt a b)

def lines (xs : Array Name) : String := "\n".intercalate (xs.toList.map toString)

def resolve (id : TSyntax `ident) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

elab "#cone_sorries " id:ident : command => do
  let n ← resolve id
  let xs := sortNames (cone (← getEnv) n).sorries
  if xs.isEmpty then logInfo m!"cone_sorries {n}: 0"
  else logInfo m!"cone_sorries {n}: {xs.size}\n{lines xs}"

elab "#cone_in " id:ident ppSpace m:ident : command => do
  let n ← resolve id
  let env ← getEnv
  let xs := sortNames <| (cone env n).all.filter fun c =>
    !c.isInternal && moduleOf? env c == some m.getId
  logInfo m!"cone_in {n} {m.getId}: {xs.size}\n{lines xs}"

elab "#cone_avoids " id:ident " [" ms:ident,* "]" : command => do
  let n ← resolve id
  let env ← getEnv
  let avoid := ms.getElems.map (·.getId)
  let c := cone env n
  let hit := avoid.filter fun m => c.all.any fun d => moduleOf? env d == some m
  if hit.isEmpty then logInfo m!"cone_avoids {n}: ok ({avoid.size} modules)"
  else logError m!"cone_avoids {n}: touches {", ".intercalate (hit.toList.map toString)}"

elab "#imports_avoid " " [" ms:ident,* "]" : command => do
  let mods := (← getEnv).header.moduleNames
  let hit := ms.getElems.map (·.getId) |>.filter mods.contains
  if hit.isEmpty then logInfo m!"imports_avoid: ok ({ms.getElems.size} modules)"
  else logError m!"imports_avoid: imports {", ".intercalate (hit.toList.map toString)}"

end Midfall.Tools
