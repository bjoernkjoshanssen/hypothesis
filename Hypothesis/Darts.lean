-- Darts   (DARTS Chapter 2)
--
--makes a bargraph that simulates throwing "input" amount of darts at a board and listing the distance

import Std
import Mathlib.Logic.Basic
import Mathlib.Computability.Reduce

def main : IO Unit := do
  let input: Nat := 6                           --input for amount of darts thrown
  IO.println s!"Darts thrown: {input} \n"       
  let mut numbers : Array Float := Array.empty 

  let mut count := 0
  while count <= input do
    let d1 ← IO.rand 0 100
    let d1 : Float := d1.toFloat / 100.0
    let d2 ← IO.rand 0 100
    let d2 : Float := d2.toFloat / 100.0
    IO.println s!"Random float: {d1} {d2}"
    let distance : Float := (d1^2 +d2^2).sqrt --Distance to center
    IO.println s!"Distance: {distance}"
    if (distance <= 1.0) then                 --See if dart hits target
        count := count + 1
        numbers := numbers.push distance
        IO.println ""
    else
    IO.println "!!THIS IS REJECTED!!"
    IO.println ""
    
  IO.println s!"Final distances: {numbers}"

  -- Plot bargraph of results
  let mut bins : Array Nat := #[0,0,0,0,0,0,0,0,0,0]  -- 10 bins
  for d in numbers do
    let idx := (d*10)
    if idx<=1.0
      then
        bins := bins.set! 0 (bins[0]! + 1)
    else if idx<=2.0
      then
        bins := bins.set! 1 (bins[1]! + 1)
    else if idx<=3.0
      then
        bins := bins.set! 2 (bins[2]! + 1)
    else if idx<=4.0
      then
        bins := bins.set! 3 (bins[3]! + 1)
    else if idx<=5.0
      then
        bins := bins.set! 4 (bins[4]! + 1)
    else if idx<=6.0
      then
        bins := bins.set! 5 (bins[5]! + 1)
    else if idx<=7.0
      then
        bins := bins.set! 6 (bins[6]! + 1)
    else if idx<=8.0
      then
        bins := bins.set! 7 (bins[7]! + 1)
    else if idx<=9.0
      then
        bins := bins.set! 8 (bins[8]! + 1)
    else if idx<=10.0
      then
        bins := bins.set! 9 (bins[9]! + 1)


  -- Print text-based bar graph
  IO.println "\n\n !Bargraph!"
  IO.println "\n * = data point where distance is between this point and next point (a point in 0.2 is in between 0.2 and 0.3) (points in 0.9 are in between 0.9 and 1.0)"
  IO.println "_________________________________________________"
  for b in [0:10] do
    IO.print s!"{(b.toFloat / 10.0)} | "
    for n in [0:bins[b]!] do
      IO.print "*"
    IO.println ""  

  IO.println "_________________________________________________"


#eval main