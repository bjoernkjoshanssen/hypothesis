import Init

def simulateRaces (n : Nat) : IO Unit := do
  let rec run (i : Nat) (acorn balky chestnut dolby : Nat) : IO Unit := do
    if i ≥ n then
      let total := n.toFloat
      IO.println ""
      IO.println s!"Acorn wins: {acorn}"
      IO.println s!"Acorn won {acorn.toFloat / total * 100} percent of the time."
      IO.println ""
      IO.println s!"Balky wins: {balky}"
      IO.println s!"Balky won {balky.toFloat / total * 100} percent of the time."
      IO.println ""
      IO.println s!"Chestnut wins: {chestnut}"
      IO.println s!"Chestnut won {chestnut.toFloat / total * 100} percent of the time."
      IO.println ""
      IO.println s!"Dolby wins: {dolby}"
      IO.println s!"Dolby won {dolby.toFloat / total * 100} percent of the time."
      pure ()
    else
      let randNat ← IO.rand 0 999
      let x : Float := randNat.toFloat / 1000.0
      let (newAcorn, newBalky, newChestnut, newDolby) :=
        if x < 0.3 then
          (acorn + 1, balky, chestnut, dolby)
        else if x < 0.7 then
          (acorn, balky + 1, chestnut, dolby)
        else if x < 0.9 then
          (acorn, balky, chestnut + 1, dolby)
        else
          (acorn, balky, chestnut, dolby + 1)
      run (i + 1) newAcorn newBalky newChestnut newDolby

  run 0 0 0 0 0

-- Change the number here to run more or fewer races

#eval simulateRaces 10000
