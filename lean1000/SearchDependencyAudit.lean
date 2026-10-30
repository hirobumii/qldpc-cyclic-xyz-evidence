import Qldpc1000
import Lean

open Lean Elab Command

/-- Reviewer tooling only: walk project-local type and proof dependencies.
Core declarations cannot refer to later project declarations, so excluding
their bodies cannot hide a project-local search dependency. -/
partial def projectClosure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then projectClosure env rest seen
    else
      let seen := seen.insert n
      let next := match env.find? n with
        | none => []
        | some ci => ci.getUsedConstantsAsSet.toList.filter
            (fun name => name.toString.startsWith "Qldpc1000.")
      projectClosure env (next ++ rest) seen

elab "#review_search_dependencies" : command => do
  let env ← getEnv
  for root in [`Qldpc1000.exact_distance, `Qldpc1000.certified_public_code] do
    let deps := (projectClosure env [root] {}).toList
    let search := deps.filter (fun name =>
      let s := name.toString
      s == "Qldpc1000.rejects" || s == "Qldpc1000.rejects_sound" ||
      s == "Qldpc1000.LocalFormula.representative_checks" ||
      s == "Qldpc1000.bulk_nonedge")
    logInfo m!"ROOT {root}: {deps.length} project dependencies; SEARCH {search}"

#review_search_dependencies
