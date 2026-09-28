import DoCarmoLib.Riemannian.Geodesic.HopfRinow
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.EVariationLePathELength
import DoCarmoLib.Riemannian.Geodesic.SymmetryLemma
import Lean

/-!
Extract a content-addressable Lean hypergraph from the Hopf–Rinow modules.

Walks the environment, and for every declaration defined in the target modules
emits `{name, module, kind, type, deps, sorry}`. The Python side turns these
into `source: lean` nodes + dependency edges in the Astrolabe store.
-/

open Lean Elab Command

/-- Modules whose declarations become Lean nodes. -/
def targetModules : List String :=
  ["DoCarmoLib.Riemannian.Geodesic.HopfRinow",
   "DoCarmoLib.Riemannian.Geodesic.HopfRinow.EVariationLePathELength",
   "DoCarmoLib.Riemannian.Geodesic.SymmetryLemma"]

/-- The module a constant was defined in (project constants only). -/
def constModule (env : Environment) (d : Name) : Option String :=
  (env.getModuleIdxFor? d).bind fun i =>
    (env.header.moduleNames[i.toNat]?).map (·.toString)

run_cmd do
  let env ← getEnv
  let mut entries : Array Json := #[]
  for (name, ci) in env.constants.toList do
    if name.isInternal then continue
    let some idx := env.getModuleIdxFor? name | continue
    let some modName := env.header.moduleNames[idx.toNat]? | continue
    let m := modName.toString
    -- extract from the whole DoCarmoLib library (every concept gets a node)
    if !m.startsWith "DoCarmoLib" then continue
    let typeStr ← liftTermElabM do
      let f ← Meta.ppExpr ci.type
      return f.pretty
    let typeConsts := ci.type.getUsedConstants
    let valConsts := (ci.value?.map Expr.getUsedConstants).getD #[]
    let allConsts := typeConsts ++ valConsts
    -- edges: dependencies that are themselves target-module declarations
    let deps := allConsts.filter
        (fun d => d != name && ((constModule env d).map (·.startsWith "DoCarmoLib") |>.getD false))
      |>.map (·.toString)
    let axs ← Lean.collectAxioms name
    let hasSorry := axs.any (fun a => a == ``sorryAx || a.toString.endsWith "sorryAx")
    let line := ((← Lean.findDeclarationRanges? name).map (·.range.pos.line)).getD 0
    let kind := match ci with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .axiomInfo _ => "axiom"
      | _ => "other"
    entries := entries.push <| Json.mkObj [
      ("name", Json.str name.toString),
      ("module", Json.str m),
      ("kind", Json.str kind),
      ("type", Json.str typeStr),
      ("deps", Json.arr (deps.map Json.str)),
      ("sorry", Json.bool hasSorry),
      ("line", Json.num line)]
  IO.FS.writeFile "/tmp/lean_graph.json" (Json.arr entries).pretty
  logInfo s!"wrote {entries.size} Lean declarations to /tmp/lean_graph.json"
