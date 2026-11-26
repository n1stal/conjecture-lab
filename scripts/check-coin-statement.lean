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
  let statement ← importModules #[{module := `Palomar.CoinFamily.Challenge}] {} 0
  let solution ← importModules #[{module := `Palomar.CoinFamily.Solution}] {} 0
  for n in [`CoinOrder.Family.every_length_ge_eleven, `CoinOrder.Family.general_prohibition_fails,
      `CoinOrder.Family.classification_fails, `CoinOrder.Family.conjecture523_false] do
    checkConst statement solution n false
    IO.println s!"Matching elaborated theorem type: {n}"
  let models : List Name := [`CoinOrder.greedyCoins, `CoinOrder.Represents, `CoinOrder.Orderly,
      `CoinOrder.coinPrefix, `CoinOrder.Family.dValue, `CoinOrder.Family.gValue,
      `CoinOrder.Family.IsD, `CoinOrder.Family.IsG, `CoinOrder.Family.HasPrefixPattern,
      `CoinOrder.Family.Conjecture523]
  for n in models do
    checkConst statement solution n true
  IO.println s!"Matching elaborated statement-model constants: {models.length}"
