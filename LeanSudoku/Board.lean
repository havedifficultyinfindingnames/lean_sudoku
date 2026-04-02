import LeanSudoku.SudokuCell

namespace LeanSudoku

def Board := Vector (Vector SudokuCell indexRange) indexRange
deriving instance Repr, DecidableEq for Board

instance : ToString Board where
  toString (board : Board) :=
    let rowStrings := board.map (fun row ↦
      let cellStrings := row.map toString
      String.intercalate " " cellStrings.toList)
    String.intercalate "\n" rowStrings.toList

namespace Board

def getCell (cells : Board) (row col : Fin indexRange) : SudokuCell :=
  cells.get row |>.get col

def setCell (cells : Board) (row col : Fin indexRange) (cell : SudokuCell) : Board :=
  cells.modify row (fun r ↦ r.modify col (fun _ ↦ cell))

theorem getCell_setCell (cells : Board) (row col : Fin indexRange) (cell : SudokuCell) :
  getCell (setCell cells row col cell) row col = cell := by
  simp [getCell, setCell, Vector.modify, Vector.get]

theorem setCell_getCell_same (cells : Board) (row col : Fin indexRange) :
  setCell cells row col (getCell cells row col) = cells := by
  simp [setCell, getCell, Vector.modify, Vector.get]

theorem setCell_overwrite (cells : Board) (row col : Fin indexRange) (cell₁ cell₂ : SudokuCell) :
  setCell (setCell cells row col cell₁) row col cell₂ = setCell cells row col cell₂ := by
  simp [Board.setCell, Vector.modify, Vector.get]

theorem getCell_setCell_sameRow_of_neCol (cells : Board) (row col col' : Fin indexRange) (cell : SudokuCell) (hcol : col' ≠ col) :
  getCell (setCell cells row col cell) row col' = getCell cells row col' := by
  unfold getCell setCell Vector.modify
  have hNat : (col : Nat) ≠ (col' : Nat) := by
    intro hEq
    apply hcol
    exact Fin.ext hEq.symm
  simpa [Vector.get] using
    (Vector.getElem_set_ne
      (xs := cells.get row)
      (i := col)
      (x := cell)
      (j := col')
      col.isLt
      col'.isLt
      hNat)

theorem getCell_setCell_of_neRow
  (cells : Board)
  (row row' col col' : Fin indexRange)
  (cell : SudokuCell)
  (hrow : row' ≠ row) :
  getCell (setCell cells row col cell) row' col' = getCell cells row' col' := by
  have hNat : (row : Nat) ≠ (row' : Nat) := by
    intro hEq
    apply hrow
    exact Fin.ext hEq.symm
  have hOuter :
      (cells.set row (cells.get row |>.set col cell)).get row' = cells.get row' := by
    simpa [Vector.get] using
      (Vector.getElem_set_ne
        (xs := cells)
        (i := row)
        (x := cells.get row |>.set col cell)
        (j := row')
        row.isLt
        row'.isLt
        hNat)
  exact congrArg (fun r ↦ r.get col') hOuter

def fixedPositions (cells : Board) : List (Fin indexRange × Fin indexRange × SudokuInt) :=
  List.product indices indices |>.filterMap fun (r, c) ↦
    match cells.getCell r c with
    | .Fixed num => some (r, c, num)
    | _ => none

theorem getCell_fixed_iff_fixedPositions {cells : Board}:
    (r, c, num) ∈ cells.fixedPositions ↔ cells.getCell r c = SudokuCell.Fixed num := by
  constructor
  · intro hMem
    rcases (by
      simpa [fixedPositions, List.product, indices] using hMem :
      ∃ a b, (match cells.getCell a b with
        | .Fixed n => some (a, b, n)
        | _ => none)
      = some (r, c, num)) with ⟨a, b, hEq⟩
    cases hCell : cells.getCell a b with
    | Fixed n =>
      simp [hCell] at hEq
      rcases hEq with ⟨ha, hb, hn⟩
      rw [ha, hb, hn] at hCell
      simpa using hCell
    | Notes candidates =>
      simp [hCell] at hEq
  · intro hCell
    have hMem :
        ∃ a b, (match cells.getCell a b with
          | .Fixed n => some (a, b, n)
          | _ => none)
        = some (r, c, num) := by
      refine ⟨r, c, ?_⟩
      simp [hCell]
    simpa [fixedPositions, List.product, indices] using hMem

private theorem boxCoordLtIndexRange
  (box off : Nat)
  (hBox : box < dimension)
  (hOff : off < dimension) :
  box * dimension + off < indexRange := by
  have hLt : box * dimension + off < box * dimension + dimension :=
    Nat.add_lt_add_left hOff (box * dimension)
  have hLe : box * dimension + dimension ≤ indexRange := by
    have hBoxSucc : box.succ ≤ dimension := Nat.succ_le_of_lt hBox
    have hMul : box.succ * dimension ≤ dimension * dimension :=
      Nat.mul_le_mul_right dimension hBoxSucc
    simpa [indexRange, Nat.succ_mul] using hMul
  exact Nat.lt_of_lt_of_le hLt hLe

def peersOf (row col : Fin indexRange) : List (Fin indexRange × Fin indexRange) :=
  let rows := indices.filterMap fun c ↦
    if c ≠ col then some (row, c) else none
  let cols := indices.filterMap fun r ↦
    if r ≠ row then some (r, col) else none
  let boxRow := row.val / dimension
  let boxCol := col.val / dimension
  have hBoxRow : boxRow < dimension := by
    have hPos : 0 < dimension := by decide
    have hRowIndex : row.val < indexRange := row.isLt
    have hRow : row.val < dimension * dimension := hRowIndex
    exact (Nat.div_lt_iff_lt_mul hPos).2 hRow
  have hBoxCol : boxCol < dimension := by
    have hPos : 0 < dimension := by decide
    have hColIndex : col.val < indexRange := col.isLt
    have hCol : col.val < dimension * dimension := hColIndex
    exact (Nat.div_lt_iff_lt_mul hPos).2 hCol
  let rowStart : Fin indexRange :=
    ⟨boxRow * dimension, boxCoordLtIndexRange boxRow 0 hBoxRow (by decide)⟩
  let rowEnd : Fin indexRange :=
    ⟨boxRow * dimension + (dimension - 1), boxCoordLtIndexRange boxRow (dimension - 1) hBoxRow (by decide)⟩
  let colStart : Fin indexRange :=
    ⟨boxCol * dimension, boxCoordLtIndexRange boxCol 0 hBoxCol (by decide)⟩
  let colEnd : Fin indexRange :=
    ⟨boxCol * dimension + (dimension - 1), boxCoordLtIndexRange boxCol (dimension - 1) hBoxCol (by decide)⟩
  let boxes : List (Fin indexRange × Fin indexRange) :=
    (List.finRangeFromTo rowStart rowEnd).flatMap
      (fun r ↦ (List.finRangeFromTo colStart colEnd).map fun c ↦ (r, c)) |>.filter
      fun (r, c) ↦ (r, c) ≠ (row, col)
  rows ++ cols ++ boxes

def iterUnits : List (List (Fin indexRange × Fin indexRange)) :=
  coordPairs.map fun (r, c) ↦ (r, c) :: (peersOf r c)

theorem not_mem_peersOf_self
  (row col : Fin indexRange) :
  (row, col) ∉ peersOf row col := by
  native_decide +revert

theorem mem_peersOf_sameRow_neCol
  (row col col' : Fin indexRange)
  (hcol : col' ≠ col) :
  (row, col') ∈ Board.peersOf row col := by
  native_decide +revert

theorem mem_peersOf_sameCol_neRow
  (row row' col : Fin indexRange)
  (hrow : row' ≠ row) :
  (row', col) ∈ Board.peersOf row col := by
  native_decide +revert

theorem mem_peersOf_sameBox_neCell
  (row col row' col' : Fin indexRange)
  (hRowBox : row' / dimension = row / dimension)
  (hColBox : col' / dimension = col / dimension)
  (hCell : (row', col') ≠ (row, col)) :
  (row', col') ∈ Board.peersOf row col := by
  native_decide +revert

theorem mem_peersOf_symm
  {row col pr pc : Fin indexRange}
  (hMem : (pr, pc) ∈ peersOf row col) :
  (row, col) ∈ peersOf pr pc := by
  native_decide +revert

end Board

end LeanSudoku
