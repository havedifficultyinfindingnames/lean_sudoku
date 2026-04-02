import LeanSudoku

open LeanSudoku

def row0 : Fin indexRange := ⟨0, by decide⟩
def row8 : Fin indexRange := ⟨8, by decide⟩
def col0 : Fin indexRange := ⟨0, by decide⟩
def col1 : Fin indexRange := ⟨1, by decide⟩
def col8 : Fin indexRange := ⟨8, by decide⟩

def n1 : SudokuInt := ⟨1, by decide⟩
def n2 : SudokuInt := ⟨2, by decide⟩

def myCell := SudokuCell.Notes [n1, n2]
def myBoard := Vector.replicate indexRange (Vector.replicate indexRange myCell)
def mySukaku : Sukaku := ⟨myBoard, by native_decide⟩

def mySudoku := Sudoku.mk myBoard

def afterOneFill := Sudoku.mk <| Sukaku.fillNumberHelper (Sukaku.remainingBlanks mySukaku) myBoard (row0, col0) n1

def main : IO Unit := do
  IO.println <| repr afterOneFill.cells
