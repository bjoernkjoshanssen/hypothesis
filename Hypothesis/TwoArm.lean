/-!
# Two-Armed Bandit Problem Simulator

This program simulates two strategies for the Two-Armed Bandit problem:
1. Play-the-better-machine: Always play the machine with higher estimated probability
2. Play-the-winner: Continue playing the same machine after a win, switch after a loss

The program tracks the Bayesian posterior distributions for the success probabilities
of both machines.
-/

namespace TwoArm

/-- Represents which machine is being played -/
inductive Machine
  | one
  | two
deriving DecidableEq, Repr

/-- Represents the outcome of a play -/
inductive Outcome
  | win
  | lose
deriving DecidableEq, Repr

/-- Strategy for playing the two-armed bandit -/
inductive Strategy
  | playBetter  -- Always play the machine with higher estimated probability
  | playWinner  -- Continue with winner, switch after loss
deriving DecidableEq, Repr

/-- State of the game including machine probabilities and play history -/
structure GameState where
  trueProb1 : Nat  -- True probability machine 1 pays off (as percentage 0-100)
  trueProb2 : Nat  -- True probability machine 2 pays off (as percentage 0-100)
  wins1 : Nat      -- Number of wins on machine 1
  losses1 : Nat    -- Number of losses on machine 1
  wins2 : Nat      -- Number of wins on machine 2
  losses2 : Nat    -- Number of losses on machine 2
  lastMachine : Option Machine  -- Last machine played (for play-winner strategy)
  lastOutcome : Option Outcome  -- Last outcome
deriving Repr

/-- Initialize a new game state with given probabilities -/
def GameState.init (p1 p2 : Nat) : GameState :=
  { trueProb1 := p1
  , trueProb2 := p2
  , wins1 := 0
  , losses1 := 0
  , wins2 := 0
  , losses2 := 0
  , lastMachine := none
  , lastOutcome := none }

/-- Compute the posterior mean probability for a machine using Beta distribution
    With uniform prior Beta(1,1), posterior is Beta(wins+1, losses+1)
    The mean of Beta(α, β) is α/(α+β)
    Returns percentage (0-100) -/
def posteriorMean (wins losses : Nat) : Nat :=
  let alpha := wins + 1
  let beta := losses + 1
  (alpha * 100) / (alpha + beta)

/-- Choose which machine to play based on strategy -/
def chooseMachine (state : GameState) (strategy : Strategy) : Machine :=
  match strategy with
  | Strategy.playBetter =>
      let est1 := posteriorMean state.wins1 state.losses1
      let est2 := posteriorMean state.wins2 state.losses2
      if est1 >= est2 then Machine.one else Machine.two
  | Strategy.playWinner =>
      match state.lastMachine, state.lastOutcome with
      | some m, some Outcome.win => m  -- Continue with winner
      | some Machine.one, some Outcome.lose => Machine.two  -- Switch after loss
      | some Machine.two, some Outcome.lose => Machine.one
      | _, _ => Machine.one  -- Default to machine 1 for first play

/-- Simulate a play on a machine using a random value (0-100) -/
def simulatePlay (machine : Machine) (state : GameState) (random : Nat) : Outcome :=
  let prob := match machine with
    | Machine.one => state.trueProb1
    | Machine.two => state.trueProb2
  if random < prob then Outcome.win else Outcome.lose

/-- Update game state after a play -/
def updateState (state : GameState) (machine : Machine) (outcome : Outcome) : GameState :=
  match machine, outcome with
  | Machine.one, Outcome.win =>
      { state with
        wins1 := state.wins1 + 1
        lastMachine := some Machine.one
        lastOutcome := some Outcome.win }
  | Machine.one, Outcome.lose =>
      { state with
        losses1 := state.losses1 + 1
        lastMachine := some Machine.one
        lastOutcome := some Outcome.lose }
  | Machine.two, Outcome.win =>
      { state with
        wins2 := state.wins2 + 1
        lastMachine := some Machine.two
        lastOutcome := some Outcome.win }
  | Machine.two, Outcome.lose =>
      { state with
        losses2 := state.losses2 + 1
        lastMachine := some Machine.two
        lastOutcome := some Outcome.lose }

/-- Play record for a single turn -/
structure PlayRecord where
  turn : Nat
  machine : Machine
  outcome : Outcome
  est1 : Nat  -- Estimated probability for machine 1 after this play (percentage)
  est2 : Nat  -- Estimated probability for machine 2 after this play (percentage)
deriving Repr

/-- Simulate n plays and return the history -/
def simulatePlays (initialState : GameState) (strategy : Strategy)
    (randomValues : List Nat) (n : Nat) : GameState × List PlayRecord :=
  let rec loop (state : GameState) (randoms : List Nat) (turn : Nat) (acc : List PlayRecord) : GameState × List PlayRecord :=
    if turn >= n then (state, acc.reverse)
    else
      match randoms with
      | [] => (state, acc.reverse)  -- No more random values
      | r :: rs =>
          let machine := chooseMachine state strategy
          let outcome := simulatePlay machine state r
          let newState := updateState state machine outcome
          let record : PlayRecord := {
            turn := turn + 1
            machine := machine
            outcome := outcome
            est1 := posteriorMean newState.wins1 newState.losses1
            est2 := posteriorMean newState.wins2 newState.losses2
          }
          loop newState rs (turn + 1) (record :: acc)
  loop initialState randomValues 0 []

/-- Calculate total winnings -/
def totalWins (state : GameState) : Nat :=
  state.wins1 + state.wins2

/-- Format machine as string -/
def Machine.toString : Machine → String
  | Machine.one => "1"
  | Machine.two => "2"

/-- Format outcome as string -/
def Outcome.toString : Outcome → String
  | Outcome.win => "Win"
  | Outcome.lose => "Loss"

/-- Format a play record as a string -/
def PlayRecord.toString (r : PlayRecord) : String :=
  s!"Turn {r.turn}: Machine {r.machine.toString} → {r.outcome.toString}, " ++
  s!"Est(M1)={r.est1}%, Est(M2)={r.est2}%"

/-- Example usage with specific parameters -/
def exampleRun : IO Unit := do
  let p1 : Nat := 30  -- Machine 1 pays 30% of the time
  let p2 : Nat := 60  -- Machine 2 pays 60% of the time
  let initialState := GameState.init p1 p2
  
  -- Example random values for 10 plays (0-100 range)
  let randomValues : List Nat := [20, 70, 40, 80, 10, 90, 30, 50, 40, 65]
  
  IO.println "=== Two-Armed Bandit Simulation ==="
  IO.println s!"True probabilities: M1 = {p1}%, M2 = {p2}%"
  IO.println ""
  
  -- Play-the-better-machine strategy
  IO.println "Strategy: Play-the-Better-Machine"
  let (finalState1, history1) := simulatePlays initialState Strategy.playBetter randomValues 10
  for record in history1 do
    IO.println (PlayRecord.toString record)
  IO.println s!"Total wins: {totalWins finalState1}"
  IO.println ""
  
  -- Play-the-winner strategy
  IO.println "Strategy: Play-the-Winner"
  let (finalState2, history2) := simulatePlays initialState Strategy.playWinner randomValues 10
  for record in history2 do
    IO.println (PlayRecord.toString record)
  IO.println s!"Total wins: {totalWins finalState2}"

end TwoArm

-- Run the example
#eval TwoArm.exampleRun