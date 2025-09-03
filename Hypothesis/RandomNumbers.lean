
def generateRandomFloat (minVal maxVal wantMax : Nat) : IO Float := do
  let randNat ← IO.rand minVal maxVal  -- Generate random Nat
  let scaledFloat := (wantMax.toFloat) *
    (randNat.toFloat / (maxVal.toFloat))

  return scaledFloat

-- #eval (5: Nat).toFloat / (3 : Nat).toFloat


def main : IO Unit := do
  let min := 0
  let max := 10000000
  let wantMax := 20
  for _ in [0 : 20] do
    let randomFloat ← generateRandomFloat min max wantMax
    IO.println s!"Random float: {randomFloat}"

#eval main


-- #eval getRandomBool -- Evaluate and print a random boolean
