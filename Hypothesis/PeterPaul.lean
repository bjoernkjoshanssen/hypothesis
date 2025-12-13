import Std

open Std

private def joinLines (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: rest => rest.foldl (fun acc s => acc ++ "\n" ++ s) x

private def tryWriteFile (path : String) (content : String) : IO Unit := do
  try
    IO.FS.writeFile path content
  catch _ =>
    pure ()

def peterPaul (n : Nat) : IO Unit := do
  let mut j : Int := 0
  let mut lines : List String := ["0 0"]  -- file-style lines (reverse order)

  -- coin tosses: print only H/T characters
  for roll in [1 : n + 1] do
    let r ← IO.rand 0 1
    if r = 0 then
      IO.print "H"
      j := j + 1
    else
      IO.print "T"
      j := j - 1
    lines := s!"{roll} {j}" :: lines

  IO.println ""  -- newline after H/T stream

  -- Show what would have gone to the file (useful in read-only environments)
  IO.println "Trace (roll winnings):"
  for line in lines.reverse do
    IO.println line

  -- Try writing like the python script (works locally; ignored in read-only)
  let content := joinLines lines.reverse ++ "\n"
  tryWriteFile "peterpauloutput.txt" content

def main : IO Unit := do
  peterPaul 40

#eval main
