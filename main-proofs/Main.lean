import KripkeGameAnalysis.Game.Basic

def countInTwoWays (n : Nat) : IO Unit := do
  timeit s!"counting of UptoIso {n}:" do
    IO.println "begin"
    let r := (Finset.univ (α := FiniteKripkeFrame.UptoIso n))
    IO.println s!"end: {r.card}"

def main : IO Unit := do
  countInTwoWays 1
  countInTwoWays 2
  countInTwoWays 3
  countInTwoWays 4
