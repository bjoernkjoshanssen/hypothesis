
def random_dice_experiment_count := 5


def tossDice : IO Unit := do
  IO.println "De Mere 1 results"
  let tries := 10
  let mut numTimes := 0
  for _ in [0 : tries] do
    IO.println s!""
    let mut found := false
    for _ in [0 : 4] do
      let myDie₀ ← IO.rand 1 6
      IO.print s!"{myDie₀}, "
      if (myDie₀ == 6) then

        found := true
    if found then
      IO.print s!"which did contain a six!"
      numTimes := numTimes + 1
    else
      IO.print s!"(no six)"
  IO.println ""
  IO.println s!"Number of times: {numTimes} out of {tries}"

#eval tossDice
