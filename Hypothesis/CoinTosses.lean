-- #eval (5: Nat).toFloat / (3 : Nat).toFloat

def getRandomBool : IO Bool := do
  let r ← IO.rand 0 1  -- Generate a random number either 0 or 1
  pure (r == 1)      -- Return true if the number is 1, false otherwise

def main : IO Unit := do
  let mut numberOfTrue := 0
  for _ in [0 : 200] do
    let randomBool ← getRandomBool
    if randomBool then
      numberOfTrue := numberOfTrue + 1
    IO.println s!"Random bool: {randomBool}"
  IO.println s!"Number of heads: {numberOfTrue}"

#eval main


-- #eval getRandomBool -- Evaluate and print a random boolean
