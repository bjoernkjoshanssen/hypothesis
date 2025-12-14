-- Craps simulator in Lean 4
-- Uses IO.rand for every die roll (no deterministic PRNG)

structure Stats where
  games  : Nat
  wins   : Nat
  losses : Nat
  rolls  : Nat
  deriving Repr

namespace CrapsIO

/-- Roll one die using IO randomness (1..6) -/
def rollDie : IO Nat :=
  IO.rand 1 6

/-- Roll two dice -/
def rollDice : IO (Nat × Nat) := do
  let d1 ← rollDie
  let d2 ← rollDie
  return (d1, d2)

/-- Play one round of Pass Line craps.
    Returns (won?, rollsUsed). -/
partial def playOnce : IO (Bool × Nat) := do
  let (a, b) ← rollDice
  let total := a + b

  -- come-out roll
  if total == 7 || total == 11 then
    return (true, 1)
  else if total == 2 || total == 3 || total == 12 then
    return (false, 1)
  else
    let point := total

    -- roll until point or 7
    let rec loop (count : Nat) : IO (Bool × Nat) := do
      let (x, y) ← rollDice
      let t := x + y
      if t == point then
        return (true, count + 1)
      else if t == 7 then
        return (false, count + 1)
      else
        loop (count + 1)

    loop 1

/-- Simulate n games -/
partial def simulateMany (n : Nat) : IO Stats := do
  let mut acc : Stats := { games := 0, wins := 0, losses := 0, rolls := 0 }

  for _ in [0:n] do
    let (won, rollsUsed) ← playOnce
    acc := { acc with
      games  := acc.games + 1
      wins   := acc.wins + (if won then 1 else 0)
      losses := acc.losses + (if won then 0 else 1)
      rolls  := acc.rolls + rollsUsed
    }

  return acc

end CrapsIO

open CrapsIO

/-- Pretty-print stats -/
def printStats (st : Stats) : IO Unit := do
  IO.println s!"Games: {st.games}"
  IO.println s!"Wins : {st.wins}"
  IO.println s!"Losses: {st.losses}"

  let winPct :=
    if st.games == 0 then 0.0
    else st.wins.toFloat / st.games.toFloat * 100.0
  IO.println s!"Win % : {winPct}%"

  let avgRolls :=
    if st.games == 0 then 0.0
    else st.rolls.toFloat / st.games.toFloat
  IO.println s!"Avg rolls per game: {avgRolls}"

  let ev :=
    if st.games == 0 then 0.0
    else (st.wins.toFloat - st.losses.toFloat) / st.games.toFloat
  IO.println s!"Expected winnings per $1 bet: {ev}"

/-- main -/
def main : IO Unit := do
  let numGames := 1000
  IO.println s!"Running {numGames} games (IO.rand only)"
  let stats ← simulateMany numGames
  printStats stats

  #eval main 
  
