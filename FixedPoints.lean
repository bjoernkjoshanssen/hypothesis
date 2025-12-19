import Std

open Std

def randomPermutation (m : Nat) : IO (Array Nat) := do
  let mut a := Array.range m
  let mut i := m
  while i > 1 do
    let j ← IO.rand 0 (i - 1)
    let i' := i - 1
    let vi := a.getD i' 0
    let vj := a.getD j 0
    a := a.set! i' vj
    a := a.set! j vi
    i := i'
  return a

def fixedPoints (n m : Nat) (significant : Float) : IO Unit := do
  if n = 0 then
    IO.println "n must be > 0"
    return

  let mut counts : Array Nat := Array.replicate (m + 1) 0

  for _ in [0:n] do
    let perm ← randomPermutation m
    let mut fp := 0
    for j in [0:m] do
      if perm.getD j 0 = j then
        fp := fp + 1
    let old := counts.getD fp 0
    counts := counts.set! fp (old + 1)

  for k in [0:(m + 1)] do
    let freq : Float :=
      (Float.ofNat (counts.getD k 0)) / (Float.ofNat n)
    if freq > significant then
      IO.println s!"{k}\t{freq}"

#eval fixedPoints 1000 20 0.0001
