import LeanSudoku.Utils

namespace LeanSudoku

inductive SudokuCell
  | Fixed (value : SudokuInt)
  | Notes (candidates : List SudokuInt)
deriving Repr, DecidableEq

instance : ToString SudokuCell where
  toString
  | .Fixed n => s!"<{n.toNat}>"
  | .Notes candidates => candidates.foldl (fun s n ↦ s ++ s!"{n.toNat}") "[" ++ "]"

namespace SudokuCell

def invalid := Notes []
def empty := Notes indices

def isFixed : SudokuCell → Bool
  | Fixed _ => true
  | Notes _ => false

def isNotes : SudokuCell → Bool
  | Fixed _ => false
  | Notes _ => true

def reduce : SudokuCell → SudokuCell
  | Fixed value => Fixed value
  | Notes [] => Notes []
  | Notes [c] => Fixed c
  | Notes candidates => Notes candidates

def deleteNote (cell : SudokuCell) (num : SudokuInt) : SudokuCell :=
  match cell with
  | Fixed _ => cell
  | Notes candidates => Notes (candidates.filter (fun c ↦ c ≠ num))

theorem deleteNote_notes_ne_fixed
  (candidates : List SudokuInt)
  (num n : SudokuInt) :
  deleteNote (Notes candidates) num ≠ Fixed n := by
  simp [deleteNote]

def addNote (cell : SudokuCell) (num : SudokuInt) : SudokuCell :=
  match cell with
  | Fixed _ => cell
  | Notes candidates =>
    if num ∈ candidates then
      cell
    else
      Notes (num :: candidates)

def toggleNote (cell : SudokuCell) (num : SudokuInt) : SudokuCell :=
  match cell with
  | Fixed _ => cell
  | Notes candidates =>
    if num ∈ candidates then
      deleteNote cell num
    else
      addNote cell num

def allCandidates (cell : SudokuCell) : List SudokuInt :=
  match cell with
  | Fixed value => [value]
  | Notes candidates => candidates

end SudokuCell

end LeanSudoku
