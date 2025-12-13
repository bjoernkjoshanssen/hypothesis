/-
This program computes and prints a table of factorials, their Stirling approximations,
and the ratio of the exact factorial to the approximation. 

It is based on the textbook's Table 3.4 and Theorem 3.3, which states that 
n! is asymptotically equal to sqrt(2πn) * (n/e)^n. 

The program demonstrates how the Stirling approximation becomes increasingly 
accurate in terms of ratio as n grows, even though the absolute difference between 
n! and its approximation also grows. This illustrates the concept of asymptotic 
equality (an ∼ bn) discussed in Definition 3.3 and Example 3.4.
-/


-- Approximation of π
def pi : Float := 3.141592653589793

/-- repeat a string n times (manual implementation) -/
def strRepeat : String → Nat → String
  | _, 0 => ""
  | s, n+1 => s ++ strRepeat s n

/-- pad a string on the right to width w -/
def pad (s : String) (w : Nat) : String :=
  let len := String.length s
  if len ≥ w then s
  else s ++ strRepeat " " (w - len)

/-- simple factorial function -/
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

/-- raise Float `x` to natural power `n` -/
def floatPow (x : Float) (n : Nat) : Float :=
  let rec loop : Nat → Float → Float
    | 0, acc => acc
    | k+1, acc => loop k (acc * x)
  loop n 1

/-- Stirling's approximation as Float -/
def stirling (n : Nat) : Float :=
  let nf := n.toFloat
  let term1 := Float.sqrt (2.0 * pi * nf)
  let term2 := floatPow (nf / Float.exp 1.0) n
  term1 * term2

/-- convert Nat factorial to Float -/
def factFloat (n : Nat) : Float :=
  (fact n).toFloat

/-- print one line of the table, aligned --/
def printLine (n : Nat) : IO Unit := do
  let f := toString (factFloat n)
  let s := toString (stirling n)
  let r := toString (factFloat n / stirling n)
  IO.println (
    pad (toString n) 6 ++
    pad f 20 ++
    pad s 22 ++
    pad r 12
  )

def main : IO Unit := do
  IO.println (
    pad "n" 6 ++
    pad "n!" 20 ++
    pad "Stirling Approx.  " 22 ++
    pad "Ratio" 12
  )
  IO.println "---------------------------------------------------------"
  for n in [1:11] do
    printLine n

#eval main
