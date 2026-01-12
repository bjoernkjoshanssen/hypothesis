/-
Program: Bayes posterior table
Source: Grinstead and Snell, Chapter 4 (Bayes’ rule program)
Output: posterior probabilities P(h | e) for each evidence pattern
-/

import Mathlib

open Std

/-- Round a Float to `n` digits after the decimal point. -/
def roundTo (n : Nat) (x : Float) : Float :=
  let scale : Float := Float.ofNat (10 ^ n)
  Float.round (x * scale) / scale

/-- Dot product of two Float lists (truncates to the shorter length). -/
def dot (a b : List Float) : Float :=
  (List.zipWith (· * ·) a b).foldl (· + ·) 0.0

/--
Bayes posterior matrix:

- `prior[j]` is P(h_j)
- `conditional[j][i]` is P(e_i | h_j)
- Output is a matrix `post[i][j] = P(h_j | e_i)` (rows = evidences, cols = hypotheses),
  rounded to 5 decimal places.
-/
def bayes (prior : List Float) (conditional : List (List Float)) : List (List Float) :=
  let m : Nat := match conditional with
    | []      => 0
    | row::_  => row.length  -- number of evidences (columns in each conditional row)

  (List.range m).map (fun i =>
    -- column i: [P(e_i|h_1), P(e_i|h_2), ...]
    let col : List Float := conditional.map (fun row => row.getD i 0.0)
    -- probe = Σ_k P(h_k) P(e_i | h_k)
    let probe : Float := dot prior col
    -- posterior row: for each hypothesis j
    (List.range prior.length).map (fun j =>
      let p := prior.getD j 0.0
      let c := col.getD j 0.0
      roundTo 5 (p * c / probe)
    )
  )

def padRight (n : Nat) (s : String) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

def fmtFloat (w : Nat) (x : Float) : String :=
  padRight w (toString x)

def showPosterior (rowLabels colLabels : List String) (mat : List (List Float)) : String :=
  let colWidth := 10
  let header :=
    padRight colWidth "" ++
    (colLabels.map (padRight colWidth) |> String.join)

  let rows :=
    (List.zip rowLabels mat).map (fun (lbl, row) =>
      padRight colWidth lbl ++
      (row.map (fmtFloat colWidth) |> String.join)
    )

  String.intercalate "\n" (header :: rows)

-- ==== Example from Mathematica file ==== 

def hlist : List String := ["d1", "d2", "d3"] -- column names
def elist : List String := ["++", "+-", "-+", "--"] -- row names

def prior : List Float := [0.322, 0.214, 0.464] -- controls the prior distribution

-- conditional[j][i] = P(e_i | h_j) (controls the likelihoods)
def conditional : List (List Float) :=
  [ [0.656, 0.094, 0.219, 0.031]
  , [0.186, 0.062, 0.559, 0.424]
  , [0.109, 0.766, 0.016, 0.109]
  ]

#eval showPosterior elist hlist (bayes prior conditional)
