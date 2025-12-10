import Mathlib

/-- Roll an `s`-sided die and return a number from 1 to `s`. -/
def rollDie (s : Nat) : IO Nat := do
  let r ← IO.rand 1 s   -- IO.rand : Nat → Nat → IO Nat
  pure r

/-- Create a list of `s` zeros. -/
def mkZeros : Nat → List Nat
  | 0       => []
  | n + 1   => 0 :: mkZeros n

/-- Update the element at index `idx` in a list using function `f`.
    If the index is out of range, the list is returned unchanged. -/
def updateAt (xs : List Nat) (idx : Nat) (f : Nat → Nat) : List Nat :=
  match xs, idx with
  | [], _ => []
  | x :: xs', 0 => f x :: xs'
  | x :: xs', i + 1 => x :: updateAt xs' i f

/-- Recursively simulate `m` remaining trials of the experiment,
    keeping track of the frequencies (list of length `s`)
    and the total gain (an `Int`). -/
def simulate (s : Nat) : Nat → List Nat → Int → IO (List Nat × Int)
  | 0, freq, totalGain => pure (freq, totalGain)
  | (m + 1), freq, totalGain => do
      let outcome ← rollDie s        -- Nat between 1 and s
      let idx := outcome - 1
      let freq' := updateAt freq idx (fun x => x + 1)
      let outcomeInt : Int := Int.ofNat outcome
      let totalGain' :=
        if outcome % 2 = 1 then
          totalGain + outcomeInt     -- odd: win
        else
          totalGain - outcomeInt     -- even: lose
      simulate s m freq' totalGain'

/--
PROGRAM: Die
CALLING SEQUENCE: Die n s

Simulates the experiment n times:
- an s-sided die is rolled,
- odd outcome → win that amount,
- even outcome → lose that amount.

Prints:
- frequency and relative frequency (as a percentage) of each face,
- average gain over n trials.

Returns:
- the average gain (as an `Int`).
-/
def Die (n s : Nat) : IO Int := do
  let freq0 := mkZeros s
  let (freq, totalGain) ← simulate s n freq0 0

  IO.println "Outcome  Frequency  RelativeFrequency"
  IO.println "-------------------------------------"

  if n = 0 then
    IO.println "No trials (n = 0)."
    IO.println "Average gain undefined (no trials)."
    return 0
  else
    -- print each face 1..s with its frequency & relative frequency
    let rec printFaces (face : Nat) (fs : List Nat) : IO Unit := do
      match fs with
      | [] => pure ()
      | count :: rest =>
          let relPercent : Nat := count * 100 / n
          IO.println s!"{face}        {count}          {relPercent}%"
          printFaces (face + 1) rest

    printFaces 1 freq

    let avgGain : Int := totalGain / Int.ofNat n
    IO.println s!"Average gain over {n} trials = {avgGain}"
    return avgGain

/- Example run: 20 trials of a 6-sided die. -/
#eval! Die 20 6
