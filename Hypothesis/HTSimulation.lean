import Mathlib.Data.Fin.Tuple.Basic

def generateRandomFloat (minVal maxVal wantMax : Nat) : IO Float := do
  let randNat ← IO.rand minVal maxVal  -- Generate random Nat
  -- let scaledFloat := minVal.toFloat + (maxVal.toFloat - minVal.toFloat) * (randNat.toFloat / (maxVal.toFloat - minVal.toFloat))
  let scaledFloat := (wantMax.toFloat) *
    (randNat.toFloat / (maxVal.toFloat))

  return scaledFloat

-- #eval (5: Nat).toFloat / (3 : Nat).toFloat


def getRandomBool : IO Bool := do
  let r ← IO.rand 0 1  -- Generate a random number either 0 or 1
  pure (r == 1)      -- Return true if the number is 1, false otherwise

def main : IO Unit := do
  let numberOfSimulations := 100
  let numberOfTries := 20
  let mut empDistNumberOfTrue : Fin numberOfTries → Nat := fun _ => 0
  -- "empDist" is short for "empirical distribution"
  let mut empDistNumberOfHLeads : Fin (numberOfTries + 1) → Nat := fun _ => 0
  for _ in [0 : numberOfSimulations] do
    let mut numberOfTrue := 0
    let mut numberOfFalse := 0
    let mut leader : Bool := true
    let mut oldLeader : Bool := true
    let mut timesNewLeader := 0
    let mut timesHeadsLeads := 0
    let mut timesTailsLeads := 0
    for _ in [0 : numberOfTries] do
      let randomBool ← getRandomBool

      if randomBool then
        numberOfTrue := numberOfTrue + 1
      else
        numberOfFalse := numberOfFalse + 1

      -- IO.print s!"{i} : {randomBool}; "

      if numberOfTrue > numberOfFalse then
        leader := true
        timesHeadsLeads := timesHeadsLeads + 1
      else
        if numberOfTrue < numberOfFalse then
          leader := false
          timesTailsLeads := timesTailsLeads + 1
        else
          if leader then timesHeadsLeads := timesHeadsLeads + 1
          else timesTailsLeads := timesTailsLeads + 1
      -- IO.println s!"({leader} is leading)"
      if leader ≠ oldLeader then
        -- IO.println s!"New leader!"
        timesNewLeader := timesNewLeader + 1
      oldLeader := leader
    IO.println s!""

    IO.println s!"Number of heads: {numberOfTrue} out of {numberOfTries}"
    empDistNumberOfTrue := fun k => if (k = numberOfTrue)
      then (empDistNumberOfTrue k + 1)
      else (empDistNumberOfTrue k)
    empDistNumberOfHLeads := fun k => if (k = timesHeadsLeads)
      then (empDistNumberOfHLeads k + 1)
      else (empDistNumberOfHLeads k)
    IO.println s!"Number of times new leader: {timesNewLeader}"
    IO.println s!"Number of times H leads: {timesHeadsLeads}"
  IO.println s!""
  IO.println s!"#Overall results#"
  IO.println "---"

  IO.println ""
  IO.println "Empirical distribution of number of H"
  for j in List.finRange numberOfTries do
    IO.print s!"."
    for _ in [0 : empDistNumberOfTrue j] do
      IO.print s!"□ "
    IO.println s!" ({j})"
  IO.println ""
  IO.println "Empirical distribution of number of H leads"
  for j in List.finRange (numberOfTries + 1) do
    IO.print s!"."
    for _ in [0 : empDistNumberOfHLeads j] do
      IO.print s!"□ "
    IO.println s!" ({j})"


#eval! main


-- #eval getRandomBool -- Evaluate and print a random boolean
