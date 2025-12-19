import Std

open Std

/-- Generate a random permutation of `[0, 1, ..., n-1]` as Nats -/
def randomPermutation (n : Nat) : IO (Array Nat) := do
  -- Start with the array [0, 1, ..., n-1]
  let mut arr : Array Nat := Array.ofFn (fun i : Fin n => (i : Nat))

  -- Fisher–Yates shuffle
  for i in [0:n] do
    let j ← IO.rand i (n - 1)
    let ai := arr[i]!
    let aj := arr[j]!
    arr := arr.set! i aj
    arr := arr.set! j ai

  pure arr

/-- Count the number of "records" in a permutation -/
def countRecords (perm : Array Nat) : Nat := Id.run do
  if perm.isEmpty then
    return 0

  let mut recs := 1
  let mut current := perm[0]!

  for i in [1:perm.size] do
    let x := perm[i]!
    if x > current then
      recs := recs + 1
      current := x

  return recs

/-- Monte‑Carlo estimate of the average number of records in random permutations -/
def Records (num n : Nat) : IO Float := do
  let mut total := 0
  for _ in [0:num] do
    let perm ← randomPermutation n
    total := total + countRecords perm
  pure (Float.ofNat total / Float.ofNat num)

#eval Records 100 7 -- 100 choices of a permutation of 7 items
