import Std

open Std

/--
Compute (n choose k) as a Nat using an iterative multiplicative formula.
-/
def choose (n k : Nat) : Nat :=
  if k > n then
    0
  else
    let k := Nat.min k (n - k)  -- symmetry: C(n,k)=C(n,n-k)
    Id.run do
      let mut acc : Nat := 1
      -- i runs 0..k-1, so i1 runs 1..k
      for i in [0 : k] do
        let i1 := i + 1
        acc := (acc * (n - k + i1)) / i1
      return acc

/-- x^k for Float, computed by repeated multiplication. -/
def powFloat (x : Float) (k : Nat) : Float :=
  Id.run do
    let mut acc : Float := 1.0
    for _ in [0 : k] do
      acc := acc * x
    return acc

/-- Binomial probability b(n,p,k) = choose(n,k) * p^k * (1-p)^(n-k). -/
def binomProb (n k : Nat) (p : Float) : Float :=
  let q := 1.0 - p
  (Float.ofNat (choose n k)) * (powFloat p k) * (powFloat q (n - k))

def main : IO Unit := do
  let n : Nat := 100
  let p : Float := 0.5
  let kmin : Nat := 45
  let kmax : Nat := 55

  IO.println s!"Binomial probabilities b(n,p,k) for n={n}, p={p}"
  IO.println "k\tb(n,p,k)"
  let mut total : Float := 0.0

  for k in [kmin : kmax + 1] do
    let b := binomProb n k p
    total := total + b
    IO.println s!"{k}\t{b}"

  IO.println s!"sum = {total}"

#eval main
