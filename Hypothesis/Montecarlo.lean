import Batteries.Data.Rat.Float
import Mathlib.Analysis.InnerProductSpace.PiL2


#eval Float.cos 0.1
def generateRandomFloat (minVal maxVal : Nat) (wantMax : ℚ) : IO Float := do
  let randNat ← IO.rand minVal maxVal  -- Generate random Nat
  let scaledFloat := (wantMax.toFloat) *
    (randNat.toFloat / (maxVal.toFloat))

  return scaledFloat



def main : IO Unit := do
  let min := 0
  let max := 100000 -- precision
  let mut above := 0
  let mut below := 0
  let wantMax := 1 --20
  let myPi : ℚ := 3.1415926535
  let wantMaxX : ℚ := myPi
  let rounds := 20
  for _ in [0 : rounds] do
    let randomFloat₁ ← generateRandomFloat min max wantMaxX
    let randomFloat₂ ← generateRandomFloat min max wantMax
    -- IO.println s!"Random floats: {randomFloat₁}, {randomFloat₂}"
    if randomFloat₂ < Float.sin randomFloat₁ then
      -- IO.println "Below the graph of sin"
      below := below + 1
    else
      above := above + 1
  IO.println s!"Above: {above}"
  IO.println s!"Below: {below}"
  IO.println s!"Approximate value  of ∫ sin x dx, 0 to {myPi.toFloat}:"
  IO.println s!"{(myPi * (below:ℚ) / rounds).toFloat} "
#eval main
