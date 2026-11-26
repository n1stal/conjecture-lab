module

public import Lean

open Lean

private def checkConst (left right : Environment) (n : Name) (compareValue : Bool) : IO Unit := do
  let some d := left.find? n | throw (IO.userError s!"Challenge lacks {n}")
  let some e := right.find? n | throw (IO.userError s!"Solution lacks {n}")
  unless d.levelParams == e.levelParams && d.type == e.type do
    throw (IO.userError s!"Statement differs across environments: {n}")
  if compareValue && d.value? != e.value? then
    throw (IO.userError s!"Statement-side definition differs across environments: {n}")

/-- Exact local comparison of elaborated statement types and model definitions.
It does not replay proofs or replace the official sandboxed Comparator. -/
public def main : IO Unit := do
  initSearchPath (← findSysroot)
  let statement ← importModules #[{module := `Palomar.Turau.Challenge}] {} 0
  let solution ← importModules #[{module := `Palomar.Turau.Solution}] {} 0
  for n in [`ConjectureLab.TurauSubmission.conjecture_false,
      `ConjectureLab.TurauSubmission.concrete_counterexample,
      `ConjectureLab.TurauSubmission.infinite_family] do
    checkConst statement solution n false
    IO.println s!"Matching exact elaborated theorem type: {n}"
  -- Only declarations that enter the mathematical statement, plus the
  -- indexed Walk constructors and kernel recursors. Compiler-generated
  -- unsafe evaluators and simplifier equations are not statement definitions.
  let models : List Name := [
      `Flooding.Arc,  `Flooding.Edges,  `Flooding.symmetric,
      `Flooding.loopless,  `Flooding.Walk,  `Flooding.connected,
      `Flooding.bipartite,  `Flooding.radiusAtMost,  `Flooding.first,
      `Flooding.next,  `Flooding.messages,  `Flooding.quietAfter,
      `Flooding.isFloodNumber,  `Flooding.isRadius,  `Flooding.TurauConjecture,
      `Flooding.V,  `Flooding.core,  `Flooding.graph,
      `Flooding.seed,  `Flooding.Walk.nil,  `Flooding.Walk.cons,
      `Flooding.Walk.rec,  `FloodFamily.Role,  `FloodFamily.Vertex,
      `FloodFamily.Matrix,  `FloodFamily.roleEdges,  `FloodFamily.localAdj,
      `FloodFamily.linked,  `FloodFamily.adj,  `FloodFamily.Msg,
      `FloodFamily.next,  `FloodFamily.Walk,  `FloodFamily.radiusAtMost,
      `FloodFamily.roundsFrom,  `FloodFamily.hasKSeeds,  `FloodFamily.quietAfter,
      `FloodFamily.isFloodNumber,  `FloodFamily.isRadius,  `FloodFamily.Walk.nil,
      `FloodFamily.Walk.cons,  `FloodFamily.Walk.rec]
  for n in models do
    checkConst statement solution n true
  IO.println s!"Matching elaborated statement-model constants: {models.length}"
