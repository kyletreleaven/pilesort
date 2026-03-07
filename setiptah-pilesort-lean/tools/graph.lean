/-
  Theorem dependency graph extractor.

  Walks the elaborated Lean environment and emits a Graphviz DOT file showing
  which theorems and definitions in the PileSort project depend on which.

  Usage:
    lake env lean --run tools/graph.lean | dot -Tsvg -o graph.svg
    lake env lean --run tools/graph.lean > graph.dot

  Or via the Python wrapper:
    python tools/graph.py
-/
import Lean
open Lean

/-- True iff the constant was defined in a PileSort.* module. -/
def isProjectConst (env : Environment) (n : Name) : Bool :=
  match env.const2ModIdx[n]? with
  | some idx =>
    (env.header.moduleNames.getD idx .anonymous).toString.startsWith "PileSort"
  | none => false

/-- Include theorems and definitions; skip constructors, recursors, instances, etc. -/
def isWanted (info : ConstantInfo) : Bool :=
  match info with
  | .thmInfo _ => true
  | _ => false

/-- Last component of a dotted name. -/
def baseName : Name → String
  | .str _ s => s
  | n => n.toString

/-- True iff the theorem was explicitly written by the user (has a source range). -/
def isExplicit (env : Environment) (n : Name) : Bool :=
  (declRangeExt.find? env n).isSome

/-- Wrap a string in DOT double-quotes, escaping internal quotes. -/
def dq (s : String) : String := "\"" ++ s.replace "\"" "\\\"" ++ "\""

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← importModules #[{ module := `PileSort }] {}

  -- Collect all project nodes, sorted for deterministic output.
  let mut nodes : Array (Name × ConstantInfo) := #[]
  for (n, info) in env.constants do
    if isProjectConst env n && isWanted info && isExplicit env n then
      nodes := nodes.push (n, info)
  nodes := nodes.qsort (fun (a, _) (b, _) => a.toString < b.toString)

  let nodeNames : Array Name := nodes.map (·.1)

  -- Build dependency edges: n → dep iff dep appears in n's proof term.
  let mut edges : Array (Name × Name) := #[]
  for (n, info) in nodes do
    if let some v := info.value? then
      for dep in v.getUsedConstants do
        if nodeNames.contains dep && dep != n then
          edges := edges.push (n, dep)

  -- Group nodes by module (preserving insertion order).
  let mut byMod : Array (Name × Array Name) := #[]
  for (n, _) in nodes do
    if let some idx := env.const2ModIdx[n]? then
      let m := env.header.moduleNames.getD idx .anonymous
      match byMod.findIdx? (fun (mod, _) => mod == m) with
      | some i =>
        let (mod, ns) := byMod[i]!
        byMod := byMod.set! i (mod, ns.push n)
      | none =>
        byMod := byMod.push (m, #[n])

  -- Emit DOT.
  IO.println "digraph pilesort {"
  IO.println "  rankdir=BT;"
  IO.println "  node [fontname=monospace fontsize=10];"
  IO.println "  graph [fontname=monospace fontsize=12];"
  IO.println ""

  let mut ci := 0
  for (m, ns) in byMod do
    IO.println ("  subgraph cluster_" ++ toString ci ++ " {")
    IO.println ("    label=" ++ dq (baseName m) ++ ";")
    IO.println "    style=rounded;"
    for n in ns do
      let nq := dq n.toString
      let lq := dq (baseName n)
      IO.println ("    " ++ nq ++ " [label=" ++ lq ++ "];")
    IO.println "  }"
    ci := ci + 1

  IO.println ""
  for (src, tgt) in edges do
    let sq := dq src.toString
    let tq := dq tgt.toString
    IO.println ("  " ++ sq ++ " -> " ++ tq ++ ";")

  IO.println "}"
