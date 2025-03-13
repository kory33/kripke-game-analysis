import KripkeGameAnalysis.Basic

def countInTwoWays (n : Nat) : IO Unit := do
  timeit s!"counting canonical frames of size {n}:" do
    IO.println "begin"
    let r := (Finset.univ (α := FiniteKripkeFrame n)).filter (fun f => f.canonicalize = f)
    IO.println s!"end: {r.card}"
  timeit s!"counting of UptoIso {n}:" do
    IO.println "begin"
    let r := (Finset.univ (α := FiniteKripkeFrame.UptoIso n))
    IO.println s!"end: {r.card}"

def main : IO Unit := do
  countInTwoWays 1
  countInTwoWays 2
  countInTwoWays 3
  countInTwoWays 4
