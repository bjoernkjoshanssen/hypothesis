-- Craps simulator in Lean 4 (single-file)
-- Simple pseudo-random generator (LCG) and simulation of the Pass/Come-out rules.
-- This version removes IO.getArgs usage and instead uses constants for number of games and seed.

structure Stats where
  games : Nat
  wins  : Nat
  losses: Nat
  rolls : Nat
  deriving Repr

namespace Craps

/-- A tiny 64-bit linear congruential generator. Deterministic and pure. -/
def lcgNext (s : UInt64) : UInt64 :=
  s * 6364136223846793005 + 1

/-- Produce one die roll (1..6) and advance RNG state. -/
def randDie (s : UInt64) : UInt64 × Nat :=
  let s' := lcgNext s
  let v := (s'.toNat % 6) + 1
  (s', v)

/-- Roll two dice, returning the new state and the two face values. -/
def rollDice (s : UInt64) : UInt64 × Nat × Nat :=
  let (s1, d1) := randDie s
  let (s2, d2) := randDie s1
  (s2, d1, d2)

/-- Play one round of craps (come-out + point rounds).
    Returns (newState, won?, rollsUsed). -/
partial def playOnce (s : UInt64) : UInt64 × Bool × Nat :=
  let (s1, a, b) := rollDice s
  let total := a + b
  if total == 7 || total == 11 then
    (s1, true, 1)
  else if total == 2 || total == 3 || total == 12 then
    (s1, false, 1)
  else
    let point := total
    -- roll until we hit point (win) or 7 (lose)
    let rec loop (st : UInt64) (count : Nat) : UInt64 × Bool × Nat :=
      let (st', x, y) := rollDice st
      let t := x + y
      if t == point then (st', true, count + 1)
      else if t == 7 then (st', false, count + 1)
      else loop st' (count + 1)
    loop s1 1

/-- Simulate n games, returning final stats and final RNG state. -/
partial def simulateMany (n : Nat) (s : UInt64) : UInt64 × Stats :=
  let rec go (remaining : Nat) (st : UInt64) (acc : Stats) : UInt64 × Stats :=
    if remaining == 0 then (st, acc)
    else
      let (st', won, rollsUsed) := playOnce st
      let acc' := { acc with
        games := acc.games + 1,
        wins  := acc.wins + (if won then 1 else 0),
        losses:= acc.losses + (if won then 0 else 1),
        rolls := acc.rolls + rollsUsed }
      go (remaining - 1) st' acc'
  go n s { games := 0, wins := 0, losses := 0, rolls := 0 }

end Craps

open Craps

def printStats (st : Stats) : IO Unit := do
  IO.println s!"Games: {st.games}"
  IO.println s!"Wins : {st.wins}"
  IO.println s!"Losses: {st.losses}"
  let winPct := if st.games == 0 then 0.0 else (st.wins.toFloat / st.games.toFloat * 100.0)
  IO.println s!"Win % : {winPct}%"
  IO.println s!"Total rolls: {st.rolls}"
  let avgRolls := if st.games == 0 then 0.0 else (st.rolls.toFloat / st.games.toFloat)
  IO.println s!"Avg rolls per game: {avgRolls}"

  let dollarWinnings := if st.games == 0 then 0.0 else (st.wins.toFloat - st.losses.toFloat) / st.games.toFloat
  IO.println s!"Expected winnings per $1 bet: ${dollarWinnings}"
/-- main: constants for number of games and seed -/
def main : IO Unit := do
  let numGames := 1000
  let seed : UInt64 := 41
  IO.println s!"Running {numGames} games"
  let (_, stats) := simulateMany numGames seed
  printStats stats

#eval main
