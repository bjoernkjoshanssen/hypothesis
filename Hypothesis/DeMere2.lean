
def random_dice_experiment_count := 5


def tossDice : IO Unit := do
  for _ in [0 : 24] do
    let myDie₀ ← IO.rand 1 6
    let myDie₁ ← IO.rand 1 6
    IO.println s!"Random dice: {myDie₀}, {myDie₁}"
    if (myDie₀ == 6 ∧ myDie₁ == 6) then
      IO.println s!"Six!"
#eval tossDice
