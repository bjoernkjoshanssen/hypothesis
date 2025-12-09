/-
  MontyHall.lean

  Simple Monte Carlo simulation of the Monty Hall problem,
  based on Grinstead and Snell, Example 4.6 and Exercise 11.

  Assumptions (standard version):
  - Car is placed uniformly at random behind door 1, 2, or 3.
  - Player chooses a door uniformly at random from {1, 2, 3}.
  - Monty knows where the car is and always opens a door with a goat.
  - Monty never opens the player's chosen door.
  - If Monty has a choice of two goat doors, he picks each with probability one-half.
  - Stay strategy means the player keeps the original door.
  - Switch strategy means the player switches to the remaining unopened door.

  The simulation estimates the probability of winning under both strategies.
-/

import Std
open Std

def doors : List Nat := [1, 2, 3]

def randomDoor : IO Nat := do
  IO.rand 1 3

def chooseMontyDoor (carDoor playerDoor : Nat) : IO Nat := do
  let candidates :=
    doors.filter (fun d => (d ≠ carDoor) ∧ (d ≠ playerDoor))
  match candidates with
  | [d] =>
      pure d
  | [d1, d2] =>
      let r ← IO.rand 0 1
      pure (if r = 0 then d1 else d2)
  | _ =>
      pure 1

def switchDoor (playerDoor montyDoor : Nat) : Nat :=
  match doors.filter (fun d => (d ≠ playerDoor) ∧ (d ≠ montyDoor)) with
  | [d] => d
  | _ => playerDoor

def simulateOnce (switch : Bool) : IO Bool := do
  let carDoor ← randomDoor
  let playerDoor ← randomDoor
  let montyDoor ← chooseMontyDoor carDoor playerDoor
  let finalDoor :=
    if switch then switchDoor playerDoor montyDoor else playerDoor
  pure (finalDoor = carDoor)

partial def simulateManyAux (switch : Bool) (n wins : Nat) : IO Nat := do
  if n = 0 then
    pure wins
  else
    let win ← simulateOnce switch
    let wins' := if win then wins + 1 else wins
    simulateManyAux switch (n - 1) wins'

def simulateMany (trials : Nat) (switch : Bool) : IO Nat :=
  simulateManyAux switch trials 0

def main : IO Unit := do
  let trials := 10000
  let stayWins ← simulateMany trials false
  let switchWins ← simulateMany trials true

  IO.println s!"Number of trials: {trials}"
  IO.println s!"Stay strategy wins:   {stayWins}"
  IO.println s!"Switch strategy wins: {switchWins}"

  let stayProb := (Float.ofNat stayWins) / (Float.ofNat trials)
  let switchProb := (Float.ofNat switchWins) / (Float.ofNat trials)

  IO.println s!"Estimated prob win if staying:  {stayProb}"
  IO.println s!"Estimated prob win if switching: {switchProb}"

#eval main
