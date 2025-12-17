/-
  DeMere Problem 1: Simulation of rolling a die 4 times
  
  This program simulates the Chevalier de Méré's first problem:
  What is the probability of getting at least one 6 in 4 rolls of a fair die?
  
  Theoretical probability: 1 - (5/6)^4 ≈ 0.5177 (51.77%)
-/

namespace DeMere1

/-- Represents the outcome of rolling a die (1-6) -/
def DieRoll := Fin 6

/-- Convert a natural number to a die roll (mod 6) -/
def natToDieRoll (n : Nat) : DieRoll :=
  ⟨n % 6, by omega⟩

/-- Simple linear congruential generator for pseudo-random numbers -/
structure RNG where
  seed : Nat

/-- Generate next random number and new RNG state -/
def RNG.next (rng : RNG) : Nat × RNG :=
  let newSeed := (1103515245 * rng.seed + 12345) % (2^31)
  (newSeed, { seed := newSeed })

/-- Generate a random die roll -/
def RNG.rollDie (rng : RNG) : DieRoll × RNG :=
  let (n, newRng) := rng.next
  (natToDieRoll n, newRng)

/-- Roll the die n times and return list of outcomes -/
def rollDieNTimes (n : Nat) (rng : RNG) : List DieRoll × RNG :=
  match n with
  | 0 => ([], rng)
  | m + 1 =>
    let (roll, newRng) := rng.rollDie
    let (rest, finalRng) := rollDieNTimes m newRng
    (roll :: rest, finalRng)

/-- Check if a die roll is a 6 (represented as Fin value 5, since 0-indexed) -/
def isSix (roll : DieRoll) : Bool :=
  roll.val == 5

/-- Check if at least one 6 appears in a list of rolls -/
def hasAtLeastOneSix (rolls : List DieRoll) : Bool :=
  rolls.any isSix

/-- Simulate one trial: roll 4 times and check for at least one 6 -/
def simulateOneTrial (rng : RNG) : Bool × RNG :=
  let (rolls, newRng) := rollDieNTimes 4 rng
  (hasAtLeastOneSix rolls, newRng)

/-- Simulate n trials and count successes (tail-recursive version) -/
def simulateNTrials (n : Nat) (rng : RNG) (acc : Nat := 0) : Nat × RNG :=
  match n with
  | 0 => (acc, rng)
  | m + 1 =>
    let (success, newRng) := simulateOneTrial rng
    let newAcc := if success then acc + 1 else acc
    simulateNTrials m newRng newAcc

/-- Calculate probability as a float approximation -/
def calculateProbability (successes trials : Nat) : Float :=
  if trials == 0 then 0.0 else (successes.toFloat / trials.toFloat)

/-- Main simulation function -/
def runSimulation (numTrials : Nat) (seed : Nat := 42) : Float :=
  let rng : RNG := { seed := seed }
  let (successes, _) := simulateNTrials numTrials rng
  calculateProbability successes numTrials

/-- Example runs with smaller trial counts to avoid overflow -/
def exampleRuns : IO Unit := do
  IO.println "DeMere Problem 1: Probability of at least one 6 in 4 rolls"
  IO.println "Theoretical probability: 1 - (5/6)^4 ≈ 0.5177"
  IO.println ""
  
  -- Using smaller numbers to avoid stack overflow in the playground
  let trials := [100, 1000, 5000]
  
  for n in trials do
    let prob := runSimulation n
    IO.println s!"Trials: {n}  |  Probability: {prob}"

end DeMere1