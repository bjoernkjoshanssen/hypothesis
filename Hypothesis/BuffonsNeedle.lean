import Batteries.Data.Rat.Float
import Mathlib.Analysis.InnerProductSpace.PiL2

def generateRandomFloat (minVal maxVal : Nat) (wantMax : ℚ) : IO Float := do
  let randNat ← IO.rand minVal maxVal  -- Generate random Nat
  let scaledFloat := (wantMax.toFloat) *
    (randNat.toFloat / (maxVal.toFloat))

  return scaledFloat

def main : IO Unit := do
  let myPi : ℚ := 3.1415926535
  let n := 100000 -- The Number of Needles used
  let mut center_x : Float := 0
  let mut center_y : Float := 0
  let mut delta_x : Float := 0
  let mut delta_y : Float := 0
  let length : Float := 0.5
  let mut theta : Float := 0
  let mut needle₀ : Fin 2 → Float := ![0,0]
  let mut needle₁ : Fin 2 → Float := ![0,0]
  let mut lesser_y : Float := 0
  let mut greater_y : Float := 0
  let mut intersecting_needle_count := 0
  let mut pi_estimated_value : Float := 0
  let precision : Nat := 1000
  for _ in [0 : n] do
    center_x ← generateRandomFloat 0 precision 1
    center_y ← generateRandomFloat 0 precision 1
    theta ← generateRandomFloat 0 precision myPi
    delta_x := length / 2 * Float.cos (theta)
    delta_y := length / 2 * Float.sin (theta)
    needle₀ := ![center_x - delta_x, center_y - delta_y]
    needle₁ := ![center_x + delta_x, center_y + delta_y]
    -- IO.println s!"center_x: {center_x}"
    lesser_y := min (needle₀ 1) (needle₁ 1)
    greater_y := max (needle₀ 1) (needle₁ 1)
--         # If the needle is intersecting with a line
    if lesser_y ≤ 0 ∧ 0 ≤ greater_y then
            -- IO.println "."
            intersecting_needle_count := intersecting_needle_count + 1
    if lesser_y ≤ 1 ∧ 1 ≤ greater_y then
            -- IO.println "."
            intersecting_needle_count := intersecting_needle_count + 1
  pi_estimated_value := n.toFloat / intersecting_needle_count
  IO.println s!"The simulated estimate for pi is: {pi_estimated_value}"

#eval main
