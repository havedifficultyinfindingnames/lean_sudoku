import Mathlib

namespace Vector
def modify (v : Vector α n) (i : Fin n) (f : α → α) : Vector α n :=
  v.set i (f <| v.get i)
end Vector

namespace List
def finRangeFromTo {n : Nat} (start ending : Fin n) : List (Fin n) :=
  if h : start.val ≤ ending.val then
    (List.finRange (ending.val - start.val + 1)).map fun i ↦
      let k := start.val + i.val
      have hkLe : k ≤ ending.val := by
        have hiLe : i.val ≤ ending.val - start.val := Nat.lt_succ_iff.mp i.isLt
        calc
          start.val + i.val ≤ start.val + (ending.val - start.val) := Nat.add_le_add_left hiLe start.val
          _ = ending.val := Nat.add_sub_of_le h
      have hkLt : k < n := Nat.lt_of_le_of_lt hkLe ending.isLt
      ⟨k, hkLt⟩
  else
    []
end List


namespace LeanSudoku

-- variable {dimension : Nat}
def dimension := 3
abbrev indexRange := dimension * dimension
def indices := List.finRange indexRange
def coordPairs : List (Fin indexRange × Fin indexRange) :=
  indices.flatMap fun r ↦ indices.map fun c ↦ (r, c)

def SudokuInt := Fin indexRange
deriving Repr, DecidableEq

end LeanSudoku
