import Degreeeq

open DegreeEq

def main : IO Unit := do
  let tight := digitsOf [0, 1, 2, 2, 2, 2, 2]
  IO.println s!"s (all-2 digits), j=0..6: {(List.range 7).map (s tight)}"
  IO.println s!"(T 6, s 6) tight case:   {(T tight 6, s tight 6)}"
  let loose := digitsOf [0, 1, 2, 2, 3, 2, 2]
  IO.println s!"s (digit 3 at j=4):      {(List.range 7).map (s loose)}"
  IO.println s!"(T 6, s 6) loose case:   {(T loose 6, s loose 6)}"
