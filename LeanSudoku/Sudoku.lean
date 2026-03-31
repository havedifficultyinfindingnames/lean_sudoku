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
def product {α β} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun x ↦ ys.map fun y ↦ (x, y)
end List

namespace leanSudoku

-- variable {dimension : Nat}
def dimension := 3
abbrev indexRange := dimension * dimension
def indices := List.finRange indexRange
def coordPairs : List (Fin indexRange × Fin indexRange) :=
  indices.flatMap fun r ↦ indices.map fun c ↦ (r, c)

def SudokuInt := Fin indexRange
deriving Repr, DecidableEq

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
  unfold getCell setCell Vector.modify
  simp [Vector.get]

theorem setCell_getCell_same (cells : Board) (row col : Fin indexRange) :
  setCell cells row col (getCell cells row col) = cells := by
  unfold setCell getCell Vector.modify
  simp [Vector.get]

theorem setCell_overwrite (cells : Board) (row col : Fin indexRange) (cell₁ cell₂ : SudokuCell) :
  setCell (setCell cells row col cell₁) row col cell₂ = setCell cells row col cell₂ := by
  unfold Board.setCell Vector.modify
  simp [Vector.get]

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
  unfold getCell setCell Vector.modify
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

private theorem getCell_fixed_iff_fixedPositions {cells : Board}:
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

theorem mem_peersOf_symm
  {row col pr pc : Fin indexRange}
  (hMem : (pr, pc) ∈ peersOf row col) :
  (row, col) ∈ peersOf pr pc := by
  native_decide +revert

theorem not_mem_peersOf_self
  (row col : Fin indexRange) :
  (row, col) ∉ peersOf row col := by
  native_decide +revert

end Board

structure Sudoku where
  cells : Board

namespace Sudoku

def empty : Sudoku :=
  { cells := Vector.replicate indexRange (Vector.replicate indexRange SudokuCell.invalid) }

def isValid (s : Sudoku) : Bool :=
  s.cells.fixedPositions.all fun (r, c, num) ↦
    Board.peersOf r c |>.all fun (pr, pc) ↦
      match s.cells.getCell pr pc with
      | .Fixed n => n ≠ num
      | _ => true

def isFullyValid (s : Sudoku) : Bool :=
  s.cells.fixedPositions.all fun (r, c, num) ↦
    Board.peersOf r c |>.all fun (pr, pc) ↦
      match s.cells.getCell pr pc with
      | .Fixed n => n ≠ num
      | .Notes candidates => num ∉ candidates

theorem isValid_of_isFullyValid {s : Sudoku} (h : s.isFullyValid = true) : s.isValid = true := by
  unfold isFullyValid at h
  unfold isValid
  apply List.all_eq_true.mpr
  rintro ⟨r, c, num⟩ hTriple
  have hPeersFullyValid :
      (Board.peersOf r c).all
        (fun (pr, pc) ↦
          match s.cells.getCell pr pc with
          | .Fixed n => n ≠ num
          | .Notes candidates => num ∉ candidates) = true :=
    (List.all_eq_true.mp h) (r, c, num) hTriple
  apply List.all_eq_true.mpr
  rintro ⟨pr, pc⟩ hPeer
  have hThisPeerFullyValid :
      (match s.cells.getCell pr pc with
      | .Fixed n => n ≠ num
      | .Notes candidates => num ∉ candidates) = true :=
    (List.all_eq_true.mp hPeersFullyValid) (pr, pc) hPeer
  cases hCell : s.cells.getCell pr pc with
  | Fixed n =>
    simpa [hCell] using hThisPeerFullyValid
  | Notes candidates =>
    simp [hCell]

theorem emptyIsFullyValid : isFullyValid empty = true := by decide

def isComplete (s : Sudoku) : Bool :=
  coordPairs.all fun (r, c) ↦
    match s.cells.getCell r c with
    | .Fixed _ => true
    | _ => false

def fillNumber (s : Sudoku) (row col : Fin indexRange) (num : SudokuInt) : Sudoku :=
  Sudoku.mk <| s.cells.setCell row col (.Fixed num)

def deleteNote (s : Sudoku) (row col : Fin indexRange) (num : SudokuInt) : Sudoku :=
  Sudoku.mk <| s.cells.setCell row col (SudokuCell.deleteNote (s.cells.getCell row col) num)

def modifyNote (s : Sudoku) (row col : Fin indexRange) (modifier : SudokuCell → SudokuCell) : Sudoku :=
  Sudoku.mk <| s.cells.setCell row col (modifier (s.cells.getCell row col))

def setCellInvalid (s : Sudoku) (row col : Fin indexRange) : Sudoku :=
  Sudoku.mk <| s.cells.setCell row col SudokuCell.invalid

theorem deleteNote_keeps_isFullyValid {s : Sudoku} (h : s.isFullyValid = true) (row col : Fin indexRange) (num : SudokuInt) :
    (s.deleteNote row col num).isFullyValid = true := by
  let s' := s.deleteNote row col num
  unfold isFullyValid at h ⊢
  apply List.all_eq_true.mpr
  rintro ⟨r, c, fixedNum⟩ hTriple
  have hFixedNew : s'.cells.getCell r c = SudokuCell.Fixed fixedNum :=
    Board.getCell_fixed_iff_fixedPositions.mp hTriple
  have hFixedOld : s.cells.getCell r c = SudokuCell.Fixed fixedNum := by
    by_cases hr : r = row
    · subst r
      by_cases hc : c = col
      · subst c
        have hTarget :
            s'.cells.getCell row col = SudokuCell.deleteNote (s.cells.getCell row col) num := by
          unfold s' Sudoku.deleteNote
          simpa using Board.getCell_setCell s.cells row col
            (SudokuCell.deleteNote (s.cells.getCell row col) num)
        have hDelFixed :
            SudokuCell.deleteNote (s.cells.getCell row col) num = SudokuCell.Fixed fixedNum := by
          simpa [hTarget] using hFixedNew
        cases hCell : s.cells.getCell row col with
        | Fixed n =>
          have hEq : n = fixedNum := by
            simpa [SudokuCell.deleteNote, hCell] using hDelFixed
          subst n
          simp
        | Notes candidates =>
          simp [SudokuCell.deleteNote, hCell] at hDelFixed
      · have hSame : s'.cells.getCell row c = s.cells.getCell row c := by
          unfold s' Sudoku.deleteNote
          simpa using Board.getCell_setCell_sameRow_of_neCol s.cells row col c
            (SudokuCell.deleteNote (s.cells.getCell row col) num) hc
        simpa [hSame] using hFixedNew
    · have hSame : s'.cells.getCell r c = s.cells.getCell r c := by
        unfold s' Sudoku.deleteNote
        simpa using Board.getCell_setCell_of_neRow s.cells row r col c
          (SudokuCell.deleteNote (s.cells.getCell row col) num) hr
      simpa [hSame] using hFixedNew
  have hTripleOld : (r, c, fixedNum) ∈ s.cells.fixedPositions :=
    Board.getCell_fixed_iff_fixedPositions.mpr hFixedOld
  have hPeersOld :
      (Board.peersOf r c).all
        (fun (pr, pc) ↦
          match s.cells.getCell pr pc with
          | .Fixed n => n ≠ fixedNum
          | .Notes candidates => fixedNum ∉ candidates) = true :=
    (List.all_eq_true.mp h) (r, c, fixedNum) hTripleOld
  apply List.all_eq_true.mpr
  intro peer hPeer
  rcases peer with ⟨pr, pc⟩
  have hPeerOld :
      (match s.cells.getCell pr pc with
      | .Fixed n => n ≠ fixedNum
      | .Notes candidates => fixedNum ∉ candidates) = true :=
    (List.all_eq_true.mp hPeersOld) (pr, pc) hPeer
  by_cases hpr : pr = row
  · subst pr
    by_cases hpc : pc = col
    · subst pc
      have hTarget :
          s'.cells.getCell row col = SudokuCell.deleteNote (s.cells.getCell row col) num := by
        unfold s' Sudoku.deleteNote
        simpa using Board.getCell_setCell s.cells row col
          (SudokuCell.deleteNote (s.cells.getCell row col) num)
      cases hOldCell : s.cells.getCell row col with
      | Fixed n =>
        have hPeerOldTarget :
            (match s.cells.getCell row col with
            | .Fixed k => k ≠ fixedNum
            | .Notes candidates => fixedNum ∉ candidates) = true := by
          simpa [hOldCell] using hPeerOld
        simpa [s', hTarget, hOldCell, SudokuCell.deleteNote] using hPeerOldTarget
      | Notes candidates =>
        have hNotMem : fixedNum ∉ candidates := by
          simpa [hOldCell] using hPeerOld
        have hNotMemOr : ¬fixedNum ∈ candidates ∨ fixedNum = num := Or.inl hNotMem
        have hTargetGoal :
            (match s'.cells.getCell row col with
            | .Fixed n => n ≠ fixedNum
            | .Notes cs => fixedNum ∉ cs) = true := by
          simpa [hTarget, hOldCell, SudokuCell.deleteNote] using hNotMemOr
        simpa using hTargetGoal
    · have hCellEq : s'.cells.getCell row pc = s.cells.getCell row pc := by
        unfold s' Sudoku.deleteNote
        simpa using Board.getCell_setCell_sameRow_of_neCol s.cells row col pc
          (SudokuCell.deleteNote (s.cells.getCell row col) num) hpc
      simpa [s', hCellEq] using hPeerOld
  · have hCellEq : s'.cells.getCell pr pc = s.cells.getCell pr pc := by
      unfold s' Sudoku.deleteNote
      simpa using Board.getCell_setCell_of_neRow s.cells row pr col pc
        (SudokuCell.deleteNote (s.cells.getCell row col) num) hpr
    simpa [s', hCellEq] using hPeerOld

theorem setCellInvalid_iff_deleteNote {s : Sudoku} (row col : Fin indexRange) (hNote : s.cells.getCell row col |>.isNotes):
  s.setCellInvalid row col = (s.cells.getCell row col).allCandidates.foldl (fun su n ↦ su.deleteNote row col n) s := by
  have listFoldDeleteNote_sameCell_cells
    (nums : List SudokuInt)
    (s : Sudoku)
    (row col : Fin indexRange) :
    (nums.foldl (fun su n ↦ su.deleteNote row col n) s).cells =
      s.cells.setCell row col
        (nums.foldl (fun cell n ↦ SudokuCell.deleteNote cell n) (s.cells.getCell row col)) := by
    induction nums generalizing s with
    | nil =>
      simp [Board.setCell_getCell_same]
    | cons n rest ih =>
      have hTarget :
          (s.deleteNote row col n).cells.getCell row col = SudokuCell.deleteNote (s.cells.getCell row col) n := by
        unfold Sudoku.deleteNote
        simpa using
          Board.getCell_setCell s.cells row col
            (SudokuCell.deleteNote (s.cells.getCell row col) n)
      calc
        (rest.foldl (fun su n ↦ su.deleteNote row col n) (s.deleteNote row col n)).cells
            = (s.deleteNote row col n).cells.setCell row col
                (rest.foldl (fun cell n ↦ SudokuCell.deleteNote cell n)
                  ((s.deleteNote row col n).cells.getCell row col)) := by
                    simpa using ih (s := s.deleteNote row col n)
        _ = s.cells.setCell row col
              (rest.foldl (fun cell n ↦ SudokuCell.deleteNote cell n)
                (SudokuCell.deleteNote (s.cells.getCell row col) n)) := by
              have hGet :
                  (s.cells.setCell row col (SudokuCell.deleteNote (s.cells.getCell row col) n)).getCell row col
                    = SudokuCell.deleteNote (s.cells.getCell row col) n := by
                simpa using
                  Board.getCell_setCell s.cells row col
                    (SudokuCell.deleteNote (s.cells.getCell row col) n)
              unfold Sudoku.deleteNote
              simp [Board.setCell_overwrite, hGet]

  have mem_foldl_filter_neq_iff
    (nums init : List SudokuInt)
    (x : SudokuInt) :
    x ∈ nums.foldl (fun cs n ↦ cs.filter (fun c ↦ !decide (c = n))) init
      ↔ x ∈ init ∧ ∀ n, n ∈ nums → x ≠ n := by
    induction nums generalizing init with
    | nil =>
      simp
    | cons n rest ih =>
      constructor
      · intro hMem
        have hMemIh :
            x ∈ init.filter (fun c ↦ !decide (c = n)) ∧ ∀ a, a ∈ rest → x ≠ a := by
          exact (ih (init := init.filter (fun c ↦ !decide (c = n)))).1 (by simpa [List.foldl_cons] using hMem)
        have hxInInit : x ∈ init := (List.mem_filter.mp hMemIh.1).1
        have hxNeN : x ≠ n := by
          simpa using (List.mem_filter.mp hMemIh.1).2
        refine ⟨hxInInit, ?_⟩
        intro a ha
        have haCases : a = n ∨ a ∈ rest := by
          simpa using ha
        cases haCases with
        | inl haEq =>
          cases haEq
          exact hxNeN
        | inr haRest =>
          exact hMemIh.2 a haRest
      · intro hInfo
        have hxFilter : x ∈ init.filter (fun c ↦ !decide (c = n)) :=
          List.mem_filter.mpr ⟨hInfo.1, by simpa using hInfo.2 n (by simp)⟩
        have hRest : ∀ a, a ∈ rest → x ≠ a := by
          intro a ha
          exact hInfo.2 a (by simp [ha])
        have hMemIh :
            x ∈ rest.foldl (fun cs n ↦ cs.filter (fun c ↦ !decide (c = n))) (init.filter (fun c ↦ !decide (c = n))) :=
          (ih (init := init.filter (fun c ↦ !decide (c = n)))).2 ⟨hxFilter, hRest⟩
        simpa [List.foldl_cons] using hMemIh

  have foldl_filter_self_eq_nil
    (nums : List SudokuInt) :
    nums.foldl (fun cs n ↦ cs.filter (fun c ↦ !decide (c = n))) nums = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have hxInfo : x ∈ nums ∧ ∀ n, n ∈ nums → x ≠ n :=
      (mem_foldl_filter_neq_iff nums nums x).1 hx
    exact (hxInfo.2 x hxInfo.1) rfl

  have foldl_deleteNote_fromNotes
    (nums init : List SudokuInt) :
    nums.foldl (fun cell n ↦ SudokuCell.deleteNote cell n) (SudokuCell.Notes init)
      = SudokuCell.Notes (nums.foldl (fun cs n ↦ cs.filter (fun c ↦ !decide (c = n))) init) := by
    induction nums generalizing init with
    | nil =>
      simp
    | cons n rest ih =>
      simpa [List.foldl_cons, SudokuCell.deleteNote] using ih (init := init.filter (fun c ↦ !decide (c = n)))

  have foldl_deleteNote_notes_allCandidates_invalid
    (candidates : List SudokuInt) :
    candidates.foldl (fun cell n ↦ SudokuCell.deleteNote cell n) (SudokuCell.Notes candidates) = SudokuCell.invalid := by
    simp [foldl_deleteNote_fromNotes, SudokuCell.invalid, foldl_filter_self_eq_nil]

  cases hCell : s.cells.getCell row col with
  | Fixed n =>
    simp [SudokuCell.isNotes, hCell] at hNote
  | Notes candidates =>
    have hCells :
        ((candidates.foldl (fun su n ↦ su.deleteNote row col n) s).cells)
          = s.cells.setCell row col SudokuCell.invalid := by
      calc
        ((candidates.foldl (fun su n ↦ su.deleteNote row col n) s).cells)
            = s.cells.setCell row col
                (candidates.foldl (fun cell n ↦ SudokuCell.deleteNote cell n) (SudokuCell.Notes candidates)) := by
                  simpa [hCell] using listFoldDeleteNote_sameCell_cells candidates s row col
        _ = s.cells.setCell row col SudokuCell.invalid := by
              simp [foldl_deleteNote_notes_allCandidates_invalid candidates]
    have hCellsEq :
        (s.setCellInvalid row col).cells
          = ((s.cells.getCell row col).allCandidates.foldl (fun su n ↦ su.deleteNote row col n) s).cells := by
      simpa [Sudoku.setCellInvalid, hCell] using hCells.symm
    cases hFold : (s.cells.getCell row col).allCandidates.foldl (fun su n ↦ su.deleteNote row col n) s with
    | mk foldCells =>
      cases hSet : s.setCellInvalid row col with
      | mk setCells =>
        simp [hSet, hFold] at hCellsEq
        cases hCellsEq
        simpa [hCell] using hFold.symm

theorem setCellInvalid_keeps_isFullyValid {s : Sudoku} (h : s.isFullyValid = true) (row col : Fin indexRange) :
  (s.setCellInvalid row col).isFullyValid = true := by
  have listFoldDeleteNote_sameCell_keeps_isFullyValid
    (nums : List SudokuInt)
    {s : Sudoku}
    (hValid : s.isFullyValid = true)
    (row col : Fin indexRange) :
    (nums.foldl (fun su n ↦ su.deleteNote row col n) s).isFullyValid = true := by
    induction nums generalizing s with
    | nil =>
      simpa using hValid
    | cons n rest ih =>
      have hDel : (s.deleteNote row col n).isFullyValid = true :=
        deleteNote_keeps_isFullyValid hValid row col n
      simpa [List.foldl_cons] using ih (s := s.deleteNote row col n) hDel

  have setCellInvalid_keeps_isFullyValid_direct
    {s : Sudoku}
    (hValid : s.isFullyValid = true)
    (row col : Fin indexRange) :
    (s.setCellInvalid row col).isFullyValid = true := by
    let sInv := s.setCellInvalid row col
    have hTarget : sInv.cells.getCell row col = SudokuCell.invalid := by
      unfold sInv Sudoku.setCellInvalid
      simpa using Board.getCell_setCell s.cells row col SudokuCell.invalid
    unfold Sudoku.isFullyValid at hValid ⊢
    apply List.all_eq_true.mpr
    rintro ⟨r, c, fixedNum⟩ hTriple
    have hFixedNew : sInv.cells.getCell r c = SudokuCell.Fixed fixedNum :=
      Board.getCell_fixed_iff_fixedPositions.mp hTriple
    have hFixedOld : s.cells.getCell r c = SudokuCell.Fixed fixedNum := by
      by_cases hr : r = row
      · subst r
        by_cases hc : c = col
        · subst c
          have hFalse : False := by
            simp [hTarget, SudokuCell.invalid] at hFixedNew
          exact False.elim hFalse
        · have hSame : sInv.cells.getCell row c = s.cells.getCell row c := by
            unfold sInv Sudoku.setCellInvalid
            simpa using Board.getCell_setCell_sameRow_of_neCol s.cells row col c SudokuCell.invalid hc
          simpa [hSame] using hFixedNew
      · have hSame : sInv.cells.getCell r c = s.cells.getCell r c := by
          unfold sInv Sudoku.setCellInvalid
          simpa using Board.getCell_setCell_of_neRow s.cells row r col c SudokuCell.invalid hr
        simpa [hSame] using hFixedNew
    have hTripleOld : (r, c, fixedNum) ∈ s.cells.fixedPositions :=
      Board.getCell_fixed_iff_fixedPositions.mpr hFixedOld
    have hPeersOld :
        (Board.peersOf r c).all
          (fun (pr, pc) ↦
            match s.cells.getCell pr pc with
            | .Fixed n => n ≠ fixedNum
            | .Notes candidates => fixedNum ∉ candidates) = true :=
      (List.all_eq_true.mp hValid) (r, c, fixedNum) hTripleOld
    apply List.all_eq_true.mpr
    intro peer hPeer
    rcases peer with ⟨pr, pc⟩
    have hPeerOld :
        (match s.cells.getCell pr pc with
        | .Fixed n => n ≠ fixedNum
        | .Notes candidates => fixedNum ∉ candidates) = true :=
      (List.all_eq_true.mp hPeersOld) (pr, pc) hPeer
    by_cases hpr : pr = row
    · subst pr
      by_cases hpc : pc = col
      · subst pc
        have hAtTarget :
            (match sInv.cells.getCell row col with
            | .Fixed n => n ≠ fixedNum
            | .Notes candidates => fixedNum ∉ candidates) = true := by
          simp [hTarget, SudokuCell.invalid]
        simpa using hAtTarget
      · have hCellEq : sInv.cells.getCell row pc = s.cells.getCell row pc := by
          unfold sInv Sudoku.setCellInvalid
          simpa using Board.getCell_setCell_sameRow_of_neCol s.cells row col pc SudokuCell.invalid hpc
        simpa [sInv, hCellEq] using hPeerOld
    · have hCellEq : sInv.cells.getCell pr pc = s.cells.getCell pr pc := by
        unfold sInv Sudoku.setCellInvalid
        simpa using Board.getCell_setCell_of_neRow s.cells row pr col pc SudokuCell.invalid hpr
      simpa [sInv, hCellEq] using hPeerOld

  by_cases hIsFixed : (s.cells.getCell row col).isFixed = true
  · exact setCellInvalid_keeps_isFullyValid_direct h row col
  · have hNote : (s.cells.getCell row col).isNotes = true := by
      cases hCell : s.cells.getCell row col with
      | Fixed n =>
        simp [SudokuCell.isFixed, hCell] at hIsFixed
      | Notes candidates =>
        simp [SudokuCell.isNotes]
    have hEq := setCellInvalid_iff_deleteNote (s := s) row col hNote
    rw [hEq]
    exact listFoldDeleteNote_sameCell_keeps_isFullyValid
      (nums := (s.cells.getCell row col).allCandidates)
      (s := s)
      h
      row
      col

private theorem listFoldDeleteNote_keeps_isFullyValid
  (coords : List (Fin indexRange × Fin indexRange))
  (num : SudokuInt)
  {s : Sudoku}
  (h : s.isFullyValid = true) :
  (coords.foldl (fun su (r, c) ↦ su.deleteNote r c num) s).isFullyValid = true := by
  induction coords generalizing s with
  | nil =>
    simpa using h
  | cons coord rest ih =>
    rcases coord with ⟨r, c⟩
    have hDel : (s.deleteNote r c num).isFullyValid = true :=
      deleteNote_keeps_isFullyValid h r c num
    simpa [List.foldl_cons] using ih (s := s.deleteNote r c num) hDel

private theorem getCell_deleteNote_of_ne
  (s : Sudoku)
  (row col tr tc : Fin indexRange)
  (num : SudokuInt)
  (hNe : (row, col) ≠ (tr, tc)) :
  (s.deleteNote row col num).cells.getCell tr tc = s.cells.getCell tr tc := by
  by_cases hr : tr = row
  · subst tr
    have htc : tc ≠ col := by
      intro hEq
      apply hNe
      simp [hEq]
    unfold Sudoku.deleteNote
    simpa using
      Board.getCell_setCell_sameRow_of_neCol s.cells row col tc
        (SudokuCell.deleteNote (s.cells.getCell row col) num)
        htc
  · unfold Sudoku.deleteNote
    simpa using
      Board.getCell_setCell_of_neRow s.cells row tr col tc
        (SudokuCell.deleteNote (s.cells.getCell row col) num)
        hr

private theorem getCell_listFoldDeleteNote_of_not_mem
  (coords : List (Fin indexRange × Fin indexRange))
  (num : SudokuInt)
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (hNotMem : (tr, tc) ∉ coords) :
  (coords.foldl (fun su (r, c) ↦ su.deleteNote r c num) s).cells.getCell tr tc = s.cells.getCell tr tc := by
  induction coords generalizing s with
  | nil =>
    simp
  | cons coord rest ih =>
    rcases coord with ⟨r, c⟩
    have hHead : (r, c) ≠ (tr, tc) := by
      intro hEq
      apply hNotMem
      simp [hEq]
    have hTail : (tr, tc) ∉ rest := by
      intro hMem
      apply hNotMem
      simp [hMem]
    calc
      (List.foldl (fun su (r, c) ↦ su.deleteNote r c num) s ((r, c) :: rest)).cells.getCell tr tc
          = (List.foldl (fun su (r, c) ↦ su.deleteNote r c num) (s.deleteNote r c num) rest).cells.getCell tr tc := by
              simp [List.foldl_cons]
      _ = (s.deleteNote r c num).cells.getCell tr tc := ih (s := s.deleteNote r c num) hTail
      _ = s.cells.getCell tr tc := getCell_deleteNote_of_ne s r c tr tc num hHead

private theorem getCell_fillNumber_self
  (s : Sudoku)
  (row col : Fin indexRange)
  (num : SudokuInt) :
  (s.fillNumber row col num).cells.getCell row col = SudokuCell.Fixed num := by
  unfold Sudoku.fillNumber
  simpa using Board.getCell_setCell s.cells row col (SudokuCell.Fixed num)

private theorem getCell_fillNumber_of_ne
  (s : Sudoku)
  (row col tr tc : Fin indexRange)
  (num : SudokuInt)
  (hNe : (row, col) ≠ (tr, tc)) :
  (s.fillNumber row col num).cells.getCell tr tc = s.cells.getCell tr tc := by
  by_cases hr : tr = row
  · subst tr
    have htc : tc ≠ col := by
      intro hEq
      apply hNe
      simp [hEq]
    unfold Sudoku.fillNumber
    simpa using
      Board.getCell_setCell_sameRow_of_neCol s.cells row col tc
        (SudokuCell.Fixed num)
        htc
  · unfold Sudoku.fillNumber
    simpa using
      Board.getCell_setCell_of_neRow s.cells row tr col tc
        (SudokuCell.Fixed num)
        hr

private theorem fixed_of_deleteNote_fixed
  (s : Sudoku)
  (row col tr tc : Fin indexRange)
  (num n : SudokuInt)
  (hFixed : (s.deleteNote row col num).cells.getCell tr tc = SudokuCell.Fixed n) :
  s.cells.getCell tr tc = SudokuCell.Fixed n := by
  by_cases hEq : (row, col) = (tr, tc)
  · cases hEq
    have hTarget :
        (s.deleteNote row col num).cells.getCell row col =
        SudokuCell.deleteNote (s.cells.getCell row col) num := by
      unfold Sudoku.deleteNote
      simpa using
        Board.getCell_setCell s.cells row col
          (SudokuCell.deleteNote (s.cells.getCell row col) num)
    have hDel : SudokuCell.deleteNote (s.cells.getCell row col) num = SudokuCell.Fixed n := by
      simpa [hTarget] using hFixed
    cases hCell : s.cells.getCell row col with
    | Fixed k =>
      simpa [SudokuCell.deleteNote, hCell] using hDel
    | Notes candidates =>
      simp [SudokuCell.deleteNote, hCell] at hDel
  · have hCellEq :
        (s.deleteNote row col num).cells.getCell tr tc = s.cells.getCell tr tc :=
      getCell_deleteNote_of_ne s row col tr tc num hEq
    simpa [hCellEq] using hFixed

private theorem fixed_of_listFoldDeleteNote_fixed
  (coords : List (Fin indexRange × Fin indexRange))
  (num : SudokuInt)
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (n : SudokuInt)
  (hFixed :
    (coords.foldl (fun su (r, c) ↦ su.deleteNote r c num) s).cells.getCell tr tc = SudokuCell.Fixed n) :
  s.cells.getCell tr tc = SudokuCell.Fixed n := by
  induction coords generalizing s with
  | nil =>
    simpa using hFixed
  | cons coord rest ih =>
    rcases coord with ⟨r, c⟩
    have hRest :
        (rest.foldl (fun su (r, c) ↦ su.deleteNote r c num) (s.deleteNote r c num)).cells.getCell tr tc =
          SudokuCell.Fixed n := by
      simpa [List.foldl_cons] using hFixed
    have hStep : (s.deleteNote r c num).cells.getCell tr tc = SudokuCell.Fixed n :=
      ih (s := s.deleteNote r c num) hRest
    exact fixed_of_deleteNote_fixed s r c tr tc num n hStep

private def peerCondAt
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (fixedNum : SudokuInt) : Prop :=
  match s.cells.getCell tr tc with
  | .Fixed n => n ≠ fixedNum
  | .Notes candidates => fixedNum ∉ candidates

private theorem peerCondAt_deleteNote
  (s : Sudoku)
  (row col tr tc : Fin indexRange)
  (num fixedNum : SudokuInt)
  (hCond : peerCondAt s tr tc fixedNum) :
  peerCondAt (s.deleteNote row col num) tr tc fixedNum := by
  by_cases hEq : (row, col) = (tr, tc)
  · cases hEq
    unfold peerCondAt at hCond ⊢
    have hTarget :
        (s.deleteNote row col num).cells.getCell row col =
        SudokuCell.deleteNote (s.cells.getCell row col) num := by
      unfold Sudoku.deleteNote
      simpa using
        Board.getCell_setCell s.cells row col
          (SudokuCell.deleteNote (s.cells.getCell row col) num)
    cases hCell : s.cells.getCell row col with
    | Fixed n =>
      simpa [hTarget, SudokuCell.deleteNote, hCell] using hCond
    | Notes candidates =>
      have hNot : fixedNum ∉ candidates := by
        simpa [hCell] using hCond
      have hNotFiltered : fixedNum ∉ candidates.filter (fun c ↦ c ≠ num) := by
        intro hMem
        have hInCandidates : fixedNum ∈ candidates := by
          have hPair : fixedNum ∈ candidates ∧ fixedNum ≠ num := by
            simpa using hMem
          exact hPair.1
        exact hNot hInCandidates
      simpa [hTarget, SudokuCell.deleteNote, hCell] using hNotFiltered
  · unfold peerCondAt at hCond ⊢
    have hCellEq : (s.deleteNote row col num).cells.getCell tr tc = s.cells.getCell tr tc :=
      getCell_deleteNote_of_ne s row col tr tc num hEq
    simpa [hCellEq] using hCond

private theorem listFoldDeleteNote_preserves_peerCondAt
  (coords : List (Fin indexRange × Fin indexRange))
  (num : SudokuInt)
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (fixedNum : SudokuInt)
  (hCond : peerCondAt s tr tc fixedNum) :
  peerCondAt (coords.foldl (fun su (r, c) ↦ su.deleteNote r c num) s) tr tc fixedNum := by
  induction coords generalizing s hCond with
  | nil =>
    simpa using hCond
  | cons coord rest ih =>
    rcases coord with ⟨r, c⟩
    have hCond' : peerCondAt (s.deleteNote r c num) tr tc fixedNum :=
      peerCondAt_deleteNote s r c tr tc num fixedNum hCond
    simpa [List.foldl_cons] using ih (s := s.deleteNote r c num) (hCond := hCond')

private theorem fixedPeer_ne_num_of_isFullyValid
  {s : Sudoku}
  (h : s.isFullyValid = true)
  (row col : Fin indexRange)
  (num : SudokuInt)
  (hExist :
    match s.cells.getCell row col with
    | .Fixed n => n = num
    | .Notes candidates => num ∈ candidates)
  {pr pc : Fin indexRange}
  {n : SudokuInt}
  (hPeerMem : (pr, pc) ∈ Board.peersOf row col)
  (hPeerFixed : s.cells.getCell pr pc = SudokuCell.Fixed n) :
  n ≠ num := by
  cases hRowCell : s.cells.getCell row col with
  | Fixed k =>
    have hk : k = num := by
      simpa [hRowCell] using hExist
    have hTripleRow : (row, col, k) ∈ s.cells.fixedPositions :=
      Board.getCell_fixed_iff_fixedPositions.mpr (by simp [hRowCell])
    have hPeersRow :
        (Board.peersOf row col).all
          (fun (pr, pc) ↦
            match s.cells.getCell pr pc with
            | .Fixed n => n ≠ k
            | .Notes candidates => k ∉ candidates) = true := by
      unfold Sudoku.isFullyValid at h
      exact (List.all_eq_true.mp h) (row, col, k) hTripleRow
    have hPeerCond :
        (match s.cells.getCell pr pc with
        | .Fixed m => m ≠ k
        | .Notes candidates => k ∉ candidates) = true :=
      (List.all_eq_true.mp hPeersRow) (pr, pc) hPeerMem
    have hnk : n ≠ k := by
      simpa [hPeerFixed] using hPeerCond
    simpa [hk] using hnk
  | Notes candidates =>
    have hNumIn : num ∈ candidates := by
      simpa [hRowCell] using hExist
    have hTriplePeer : (pr, pc, n) ∈ s.cells.fixedPositions :=
      Board.getCell_fixed_iff_fixedPositions.mpr hPeerFixed
    have hPeersPeer :
        (Board.peersOf pr pc).all
          (fun (qr, qc) ↦
            match s.cells.getCell qr qc with
            | .Fixed m => m ≠ n
            | .Notes cs => n ∉ cs) = true := by
      unfold Sudoku.isFullyValid at h
      exact (List.all_eq_true.mp h) (pr, pc, n) hTriplePeer
    have hSymm : (row, col) ∈ Board.peersOf pr pc :=
      Board.mem_peersOf_symm hPeerMem
    have hAtRowCol :
        (match s.cells.getCell row col with
        | .Fixed m => m ≠ n
        | .Notes cs => n ∉ cs) = true :=
      (List.all_eq_true.mp hPeersPeer) (row, col) hSymm
    have hnNotIn : n ∉ candidates := by
      simpa [hRowCell] using hAtRowCol
    intro hEq
    apply hnNotIn
    simpa [hEq] using hNumIn

private def noteCleanAt
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (num : SudokuInt) : Prop :=
  match s.cells.getCell tr tc with
  | .Fixed _ => True
  | .Notes candidates => num ∉ candidates

private theorem noteCleanAt_after_delete_here
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (num : SudokuInt) :
  noteCleanAt (s.deleteNote tr tc num) tr tc num := by
  unfold noteCleanAt
  have hTarget :
      (s.deleteNote tr tc num).cells.getCell tr tc =
      SudokuCell.deleteNote (s.cells.getCell tr tc) num := by
    unfold Sudoku.deleteNote
    simpa using
      Board.getCell_setCell s.cells tr tc
        (SudokuCell.deleteNote (s.cells.getCell tr tc) num)
  cases hCell : s.cells.getCell tr tc with
  | Fixed value =>
    simp [hTarget, SudokuCell.deleteNote, hCell]
  | Notes candidates =>
    simp [hTarget, SudokuCell.deleteNote, hCell]

private theorem noteCleanAt_deleteNote
  (s : Sudoku)
  (row col tr tc : Fin indexRange)
  (num : SudokuInt)
  (hClean : noteCleanAt s tr tc num) :
  noteCleanAt (s.deleteNote row col num) tr tc num := by
  by_cases hEq : (row, col) = (tr, tc)
  · cases hEq
    simpa using noteCleanAt_after_delete_here s row col num
  · unfold noteCleanAt at hClean ⊢
    have hCellEq : (s.deleteNote row col num).cells.getCell tr tc = s.cells.getCell tr tc :=
      getCell_deleteNote_of_ne s row col tr tc num hEq
    simpa [hCellEq] using hClean

private theorem listFoldDeleteNote_preserves_noteCleanAt
  (coords : List (Fin indexRange × Fin indexRange))
  (num : SudokuInt)
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (hClean : noteCleanAt s tr tc num) :
  noteCleanAt (coords.foldl (fun su (r, c) ↦ su.deleteNote r c num) s) tr tc num := by
  induction coords generalizing s hClean with
  | nil =>
    simpa using hClean
  | cons coord rest ih =>
    rcases coord with ⟨r, c⟩
    have hClean' : noteCleanAt (s.deleteNote r c num) tr tc num :=
      noteCleanAt_deleteNote s r c tr tc num hClean
    simpa [List.foldl_cons] using ih (s := s.deleteNote r c num) (hClean := hClean')

private theorem listFoldDeleteNote_noteCleanAt_of_mem
  (coords : List (Fin indexRange × Fin indexRange))
  (num : SudokuInt)
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (hMem : (tr, tc) ∈ coords) :
  noteCleanAt (coords.foldl (fun su (r, c) ↦ su.deleteNote r c num) s) tr tc num := by
  induction coords generalizing s with
  | nil =>
    cases hMem
  | cons coord rest ih =>
    rcases coord with ⟨r, c⟩
    have hMem' : (tr, tc) = (r, c) ∨ (tr, tc) ∈ rest := by
      simpa using hMem
    cases hMem' with
    | inl hHead =>
      have hHere : noteCleanAt (s.deleteNote r c num) tr tc num := by
        cases hHead
        simpa using noteCleanAt_after_delete_here s tr tc num
      have hTail :
          noteCleanAt
            (rest.foldl (fun su (r, c) ↦ su.deleteNote r c num) (s.deleteNote r c num))
            tr
            tc
            num :=
        listFoldDeleteNote_preserves_noteCleanAt rest num (s.deleteNote r c num) tr tc hHere
      simpa [List.foldl_cons] using hTail
    | inr hTailMem =>
      have hTail :
          noteCleanAt
            (rest.foldl (fun su (r, c) ↦ su.deleteNote r c num) (s.deleteNote r c num))
            tr
            tc
            num :=
        ih (s := s.deleteNote r c num) hTailMem
      simpa [List.foldl_cons] using hTail

def fillNumberAndDeleteExistingNotes (s : Sudoku) (row col : Fin indexRange) (num : SudokuInt) : Sudoku :=
  Board.peersOf row col |>.foldl (fun su (r, c) ↦ deleteNote su r c num) <| s.fillNumber row col num

theorem fillNumberAndDeleteExistingNotes_keeps_isFullyValid {s: Sudoku} (h : s.isFullyValid = true) (row col : Fin indexRange) (num : SudokuInt) (hExist : match s.cells.getCell row col with
  | .Fixed n => n = num
  | .Notes candidates => num ∈ candidates):
    (s.fillNumberAndDeleteExistingNotes row col num).isFullyValid = true := by
  let coords := Board.peersOf row col
  let sFill := s.fillNumber row col num
  let sFinal := coords.foldl (fun su (r, c) ↦ su.deleteNote r c num) sFill
  have hFinalEq : s.fillNumberAndDeleteExistingNotes row col num = sFinal := by
    simp [fillNumberAndDeleteExistingNotes, coords, sFill, sFinal]
  have hRowNotMem : (row, col) ∉ coords := by
    simpa [coords] using Board.not_mem_peersOf_self row col
  have hRowCellEq : sFinal.cells.getCell row col = sFill.cells.getCell row col :=
    getCell_listFoldDeleteNote_of_not_mem coords num sFill row col hRowNotMem
  have hRowFixed : sFinal.cells.getCell row col = SudokuCell.Fixed num := by
    simpa [hRowCellEq, sFill] using getCell_fillNumber_self s row col num
  have hFinalValid : sFinal.isFullyValid = true := by
    unfold Sudoku.isFullyValid
    apply List.all_eq_true.mpr
    rintro ⟨r, c, fixedNum⟩ hTriple
    have hFixedFinal : sFinal.cells.getCell r c = SudokuCell.Fixed fixedNum :=
      Board.getCell_fixed_iff_fixedPositions.mp hTriple
    by_cases hRC : (r, c) = (row, col)
    · cases hRC
      have hNumEq : num = fixedNum := by
        simpa [hRowFixed] using hFixedFinal
      have hNumEq' : fixedNum = num := hNumEq.symm
      subst fixedNum
      apply List.all_eq_true.mpr
      intro peer hPeer
      rcases peer with ⟨pr, pc⟩
      cases hPeerCell : sFinal.cells.getCell pr pc with
      | Fixed n =>
        have hFixedInFill : sFill.cells.getCell pr pc = SudokuCell.Fixed n :=
          fixed_of_listFoldDeleteNote_fixed coords num sFill pr pc n (by simpa [sFinal] using hPeerCell)
        have hNePair : (row, col) ≠ (pr, pc) := by
          intro hEq
          apply hRowNotMem
          simpa [coords, hEq] using hPeer
        have hFillEq : sFill.cells.getCell pr pc = s.cells.getCell pr pc :=
          getCell_fillNumber_of_ne s row col pr pc num hNePair
        have hFixedOld : s.cells.getCell pr pc = SudokuCell.Fixed n := by
          simpa [hFillEq] using hFixedInFill
        have hNeNum : n ≠ num :=
          fixedPeer_ne_num_of_isFullyValid h row col num hExist (by simpa [coords] using hPeer) hFixedOld
        simpa [hPeerCell] using hNeNum
      | Notes cs =>
        have hClean : noteCleanAt sFinal pr pc num :=
          listFoldDeleteNote_noteCleanAt_of_mem coords num sFill pr pc (by simpa [coords] using hPeer)
        have hNoNum : num ∉ cs := by
          unfold noteCleanAt at hClean
          simpa [hPeerCell] using hClean
        simpa [hPeerCell] using hNoNum
    · have hFixedInFill : sFill.cells.getCell r c = SudokuCell.Fixed fixedNum :=
        fixed_of_listFoldDeleteNote_fixed coords num sFill r c fixedNum (by simpa [sFinal] using hFixedFinal)
      have hNePair : (row, col) ≠ (r, c) := by
        simpa [eq_comm] using hRC
      have hFillEq : sFill.cells.getCell r c = s.cells.getCell r c :=
        getCell_fillNumber_of_ne s row col r c num hNePair
      have hFixedOld : s.cells.getCell r c = SudokuCell.Fixed fixedNum := by
        simpa [hFillEq] using hFixedInFill
      have hTripleOld : (r, c, fixedNum) ∈ s.cells.fixedPositions :=
        Board.getCell_fixed_iff_fixedPositions.mpr hFixedOld
      have hPeersOld :
          (Board.peersOf r c).all
            (fun (pr, pc) ↦
              match s.cells.getCell pr pc with
              | .Fixed n => n ≠ fixedNum
              | .Notes candidates => fixedNum ∉ candidates) = true := by
        unfold Sudoku.isFullyValid at h
        exact (List.all_eq_true.mp h) (r, c, fixedNum) hTripleOld
      apply List.all_eq_true.mpr
      intro peer hPeer
      rcases peer with ⟨pr, pc⟩
      have hPeerOld :
          (match s.cells.getCell pr pc with
          | .Fixed n => n ≠ fixedNum
          | .Notes candidates => fixedNum ∉ candidates) = true :=
        (List.all_eq_true.mp hPeersOld) (pr, pc) hPeer
      by_cases hTarget : (pr, pc) = (row, col)
      · cases hTarget
        have hNumNeFixed : num ≠ fixedNum := by
          cases hRowCell : s.cells.getCell row col with
          | Fixed n0 =>
            have hn0Eq : n0 = num := by
              simpa [hRowCell] using hExist
            have hn0Ne : n0 ≠ fixedNum := by
              simpa [hRowCell] using hPeerOld
            simpa [hn0Eq] using hn0Ne
          | Notes candidates =>
            have hNumIn : num ∈ candidates := by
              simpa [hRowCell] using hExist
            have hNotIn : fixedNum ∉ candidates := by
              simpa [hRowCell] using hPeerOld
            intro hEq
            apply hNotIn
            simpa [hEq] using hNumIn
        have hAtTarget :
            (match sFinal.cells.getCell row col with
            | .Fixed n => n ≠ fixedNum
            | .Notes candidates => fixedNum ∉ candidates) = true := by
          simpa [hRowFixed] using hNumNeFixed
        simpa using hAtTarget
      · have hNePairPeer : (row, col) ≠ (pr, pc) := by
          intro hEq
          exact hTarget hEq.symm
        have hFillPeerEq : sFill.cells.getCell pr pc = s.cells.getCell pr pc :=
          getCell_fillNumber_of_ne s row col pr pc num hNePairPeer
        have hCondFill : peerCondAt sFill pr pc fixedNum := by
          unfold peerCondAt
          cases hCell : s.cells.getCell pr pc with
          | Fixed n =>
            simpa [hFillPeerEq, hCell] using hPeerOld
          | Notes candidates =>
            simpa [hFillPeerEq, hCell] using hPeerOld
        have hCondFinal : peerCondAt sFinal pr pc fixedNum :=
          listFoldDeleteNote_preserves_peerCondAt coords num sFill pr pc fixedNum hCondFill
        have hAtPeer :
            (match sFinal.cells.getCell pr pc with
            | .Fixed n => n ≠ fixedNum
            | .Notes candidates => fixedNum ∉ candidates) = true := by
          unfold peerCondAt at hCondFinal
          cases hCell : sFinal.cells.getCell pr pc with
          | Fixed n =>
            simpa [hCell] using hCondFinal
          | Notes candidates =>
            simpa [hCell] using hCondFinal
        simpa using hAtPeer
  simpa [hFinalEq] using hFinalValid

def rebuildNotes (s : Sudoku) : Sudoku :=
  s.cells.fixedPositions.foldl (fun su (r, c, num) ↦
    Board.peersOf r c |>.foldl (fun su (pr, pc) ↦ deleteNote su pr pc num) su
  ) <| { cells := Vector.replicate indexRange (Vector.replicate indexRange SudokuCell.empty) }

theorem rebuildNotes_isFullyValid {s : Sudoku} : (rebuildNotes s).isFullyValid = true := by
  let base : Sudoku :=
    { cells := Vector.replicate indexRange (Vector.replicate indexRange SudokuCell.empty) }
  have hBase : base.isFullyValid = true := by decide
  have hFold :
      ∀ (fixeds : List (Fin indexRange × Fin indexRange × SudokuInt)) (start : Sudoku),
        start.isFullyValid = true →
        (fixeds.foldl
          (fun su (r, c, num) ↦
            Board.peersOf r c |>.foldl (fun su (pr, pc) ↦ su.deleteNote pr pc num) su)
          start).isFullyValid = true := by
    intro fixeds
    induction fixeds with
    | nil =>
      intro start hStart
      simpa
    | cons triple rest ih =>
      intro start hStart
      rcases triple with ⟨r, c, num⟩
      have hStep :
          ((Board.peersOf r c).foldl (fun su (pr, pc) ↦ su.deleteNote pr pc num) start).isFullyValid = true :=
        listFoldDeleteNote_keeps_isFullyValid (coords := Board.peersOf r c) (num := num) (s := start) hStart
      have hTail :
          (rest.foldl
            (fun su (r, c, num) ↦
              Board.peersOf r c |>.foldl (fun su (pr, pc) ↦ su.deleteNote pr pc num) su)
            ((Board.peersOf r c).foldl (fun su (pr, pc) ↦ su.deleteNote pr pc num) start)).isFullyValid = true :=
        ih _ hStep
      simpa [List.foldl_cons] using hTail
  simpa [rebuildNotes, base] using hFold s.cells.fixedPositions base hBase

end Sudoku

structure Sukaku where
  cells : Board
  h : Sudoku.isFullyValid (Sudoku.mk cells) = true

namespace Sukaku

def empty : Sukaku := { cells := Vector.replicate indexRange (Vector.replicate indexRange SudokuCell.empty), h := by decide }

def isValid (s : Sukaku) : Bool :=
  let inCellValid := coordPairs.all fun (r, c) ↦
    s.cells.getCell r c ≠ SudokuCell.invalid
  let crossCellValid := Board.iterUnits.all fun unit ↦
    let seen := unit.flatMap fun (r, c) ↦
      match s.cells.getCell r c with
      | .Fixed num => [num]
      | .Notes candidates => candidates
    indices.all fun n ↦ n ∈ seen
  inCellValid && crossCellValid

theorem emptyIsValid : isValid empty = true := by decide

theorem anyCellValid_of_isValid {s : Sukaku} (h : isValid s = true) : ∀ r c, s.cells.getCell r c ≠ SudokuCell.invalid := by
  intro r c
  have hAll :
    ∀ a, a ∈ indices → ∀ b, b ∈ indices → s.cells.getCell a b ≠ SudokuCell.invalid := by
    have hProp :
      (∀ (a : Fin indexRange), a ∈ indices →
        ∀ (b : Fin indexRange), b ∈ indices →
          s.cells.getCell a b ≠ SudokuCell.invalid) ∧
          (∀ (unit : List (Fin indexRange × Fin indexRange)), unit ∈ Board.iterUnits →
            ∀ (n : Fin indexRange), n ∈ indices →
              ∃ pr pc, (pr, pc) ∈ unit ∧
                n ∈
                  match s.cells.getCell pr pc with
                  | .Fixed num => [num]
                  | .Notes candidates => candidates) := by
      simpa [isValid, coordPairs] using h
    exact hProp.1
  have hr : r ∈ indices := by simp [indices]
  have hc : c ∈ indices := by simp [indices]
  exact hAll r hr c hc

def isComplete (s : Sukaku) : Bool :=
  Sudoku.mk s.cells |>.isComplete

def remainingBlanks (s : Sukaku) : Nat :=
  List.product indices indices |>.foldl (fun acc (r, c) ↦
    match s.cells.getCell r c with
    | .Fixed _ => acc
    | .Notes _ => acc + 1
  ) 0

mutual

def fillNumberHelper : Nat → Board → Fin indexRange × Fin indexRange → SudokuInt → Board
  | 0, cells, _, _ =>
    cells
  | .succ rem, cells, (row, col), num =>
    let cells' := Board.peersOf row col |>.foldl (fun cells coord ↦ deleteNoteHelper rem cells coord num) cells
    cells'.setCell row col (SudokuCell.Fixed num)

def deleteNoteHelper : Nat → Board → Fin indexRange × Fin indexRange → SudokuInt → Board
  | remaining, cells, (row, col), num =>
    let cell := cells.getCell row col
    match cell with
    | .Fixed n =>
      if n = num then
        cells.setCell row col SudokuCell.invalid
      else
        cells
    | .Notes _ =>
      let cands' := cell.allCandidates.filter (fun x ↦ x ≠ num)
      let cells' := cells.setCell row col (.Notes cands') -- delete the note first, then propagate, which is the only correct behavior when the note deletion causes a cell to become fixed
      match cands' with
      | [cand'] =>
        fillNumberHelper remaining cells' (row, col) cand'
      | _ =>
        cells'
end

private theorem deleteNoteHelper_noNewNotes_of_fill
  (remaining : Nat)
  (hFill :
    ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
      (_hLegalMove : num ∈ (cells.getCell row col).allCandidates)
      (row' col' : Fin indexRange),
      ((fillNumberHelper remaining cells (row, col) num).getCell row' col').allCandidates
        ⊆ (cells.getCell row' col').allCandidates) :
  ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt) (row' col' : Fin indexRange),
      ((deleteNoteHelper remaining cells (row, col) num).getCell row' col').allCandidates
        ⊆ (cells.getCell row' col').allCandidates := by
  intro cells row col num row' col'
  cases hCell : cells.getCell row col with
  | Fixed n =>
    by_cases hEq : n = num
    · have hEqDel :
        deleteNoteHelper remaining cells (row, col) num = cells.setCell row col SudokuCell.invalid := by
        unfold deleteNoteHelper
        simp [hCell, hEq]
      rw [hEqDel]
      by_cases hr : row' = row
      · cases hr
        by_cases hc : col' = col
        · cases hc
          intro x hx
          have hTarget :
              (cells.setCell row col SudokuCell.invalid).getCell row col = SudokuCell.invalid := by
            simpa using Board.getCell_setCell cells row col SudokuCell.invalid
          have hxInvalid : x ∈ SudokuCell.invalid.allCandidates := by
            simpa [hTarget] using hx
          have hFalse : False := by
            simp [SudokuCell.invalid, SudokuCell.allCandidates] at hxInvalid
          exact False.elim hFalse
        · have hSame :
            (cells.setCell row col SudokuCell.invalid).getCell row col' = cells.getCell row col' := by
            simpa using
              Board.getCell_setCell_sameRow_of_neCol cells row col col' SudokuCell.invalid hc
          intro x hx
          simpa [hSame] using hx
      · have hSame :
          (cells.setCell row col SudokuCell.invalid).getCell row' col' = cells.getCell row' col' := by
          simpa using
            Board.getCell_setCell_of_neRow cells row row' col col' SudokuCell.invalid hr
        intro x hx
        simpa [hSame] using hx
    · intro x hx
      have hEqDel : deleteNoteHelper remaining cells (row, col) num = cells := by
        unfold deleteNoteHelper
        simp [hCell, hEq]
      rw [hEqDel] at hx
      simpa using hx
  | Notes candidates =>
    let filtered : List SudokuInt := candidates.filter (fun x ↦ !decide (x = num))
    have hDel : SudokuCell.deleteNote (SudokuCell.Notes candidates) num = SudokuCell.Notes filtered := by
      simp [filtered, SudokuCell.deleteNote]
    have hSetSubset :
        ((cells.setCell row col (SudokuCell.Notes filtered)).getCell row' col').allCandidates
          ⊆ (cells.getCell row' col').allCandidates := by
      by_cases hr : row' = row
      · cases hr
        by_cases hc : col' = col
        · cases hc
          intro x hx
          have hTarget :
              (cells.setCell row col (SudokuCell.Notes filtered)).getCell row col
                = SudokuCell.Notes filtered := by
            simpa using Board.getCell_setCell cells row col (SudokuCell.Notes filtered)
          have hxInFilter : x ∈ filtered := by
            rw [hTarget] at hx
            simpa [SudokuCell.allCandidates] using hx
          have hxInFilter' : x ∈ candidates.filter (fun x ↦ !decide (x = num)) := by
            simpa [filtered] using hxInFilter
          have hxInCandidates : x ∈ candidates := (List.mem_filter.mp hxInFilter').1
          simpa [hCell, SudokuCell.allCandidates] using hxInCandidates
        · have hSame :
            (cells.setCell row col (SudokuCell.Notes filtered)).getCell row col' = cells.getCell row col' := by
            simpa using
              Board.getCell_setCell_sameRow_of_neCol cells row col col' (SudokuCell.Notes filtered) hc
          intro x hx
          simpa [hSame] using hx
      · have hSame :
          (cells.setCell row col (SudokuCell.Notes filtered)).getCell row' col' = cells.getCell row' col' := by
          simpa using
            Board.getCell_setCell_of_neRow cells row row' col col' (SudokuCell.Notes filtered) hr
        intro x hx
        simpa [hSame] using hx
    cases hFiltered : filtered with
    | nil =>
      have hDelNil : SudokuCell.deleteNote (SudokuCell.Notes candidates) num = SudokuCell.Notes [] := by
        simpa [hFiltered] using hDel
      have hEqDelNil :
          deleteNoteHelper remaining cells (row, col) num =
            cells.setCell row col (SudokuCell.Notes []) := by
        have hFilterEq : candidates.filter (fun x ↦ !decide (x = num)) = [] := by
          simpa [filtered] using hFiltered
        unfold deleteNoteHelper
        simp [hCell, SudokuCell.allCandidates, hFilterEq]
      have hEqDel :
          deleteNoteHelper remaining cells (row, col) num =
            cells.setCell row col (SudokuCell.Notes filtered) := by
        simpa [hFiltered] using hEqDelNil
      rw [hEqDel]
      exact hSetSubset
    | cons candidate' rest =>
      cases rest with
      | nil =>
        have hInFilter : candidate' ∈ filtered := by
          rw [hFiltered]
          simp
        have hInFilter' : candidate' ∈ candidates.filter (fun x ↦ !decide (x = num)) := by
          simpa [filtered] using hInFilter
        have hInCandidates : candidate' ∈ candidates := (List.mem_filter.mp hInFilter').1
        have hLegalMove : candidate' ∈ (cells.getCell row col).allCandidates := by
          simpa [hCell, SudokuCell.allCandidates] using hInCandidates
        have hFillSubset :
            ((fillNumberHelper remaining cells (row, col) candidate').getCell row' col').allCandidates
              ⊆ (cells.getCell row' col').allCandidates := by
          exact hFill cells row col candidate' hLegalMove row' col'
        have hSetSubsetSingle :
            ((cells.setCell row col (SudokuCell.Notes [candidate'])).getCell row' col').allCandidates
              ⊆ (cells.getCell row' col').allCandidates := by
          simpa [hFiltered] using hSetSubset
        have hLegalMoveSet :
            candidate' ∈ ((cells.setCell row col (SudokuCell.Notes [candidate'])).getCell row col).allCandidates := by
          have hTarget :
              (cells.setCell row col (SudokuCell.Notes [candidate'])).getCell row col = SudokuCell.Notes [candidate'] := by
            simpa using Board.getCell_setCell cells row col (SudokuCell.Notes [candidate'])
          simp [hTarget, SudokuCell.allCandidates]
        have hFillSubsetSet :
            ((fillNumberHelper remaining (cells.setCell row col (SudokuCell.Notes [candidate'])) (row, col) candidate').getCell row' col').allCandidates
              ⊆ ((cells.setCell row col (SudokuCell.Notes [candidate'])).getCell row' col').allCandidates := by
          exact hFill (cells.setCell row col (SudokuCell.Notes [candidate'])) row col candidate' hLegalMoveSet row' col'
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              fillNumberHelper remaining (cells.setCell row col (SudokuCell.Notes [candidate'])) (row, col) candidate' := by
          have hFilterEq : candidates.filter (fun x ↦ !decide (x = num)) = [candidate'] := by
            simpa [filtered] using hFiltered
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEq]
        rw [hEqDel]
        intro x hx
        exact hSetSubsetSingle (hFillSubsetSet hx)
      | cons b rest' =>
        have hEqDelMany :
            deleteNoteHelper remaining cells (row, col) num =
              cells.setCell row col (SudokuCell.Notes (candidate' :: b :: rest')) := by
          have hFilterEq : candidates.filter (fun x ↦ !decide (x = num)) = candidate' :: b :: rest' := by
            simpa [filtered] using hFiltered
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEq]
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              cells.setCell row col (SudokuCell.Notes filtered) := by
          simpa [hFiltered] using hEqDelMany
        rw [hEqDel]
        exact hSetSubset

private theorem fill_delete_noNewNotes_aux :
  ∀ remaining,
    (∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
      (_hLegalMove : num ∈ (cells.getCell row col).allCandidates)
      (row' col' : Fin indexRange),
      ((fillNumberHelper remaining cells (row, col) num).getCell row' col').allCandidates
        ⊆ (cells.getCell row' col').allCandidates)
    ∧
    (∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
      (row' col' : Fin indexRange),
      ((deleteNoteHelper remaining cells (row, col) num).getCell row' col').allCandidates
        ⊆ (cells.getCell row' col').allCandidates) := by
  intro remaining
  induction remaining with
  | zero =>
    have hFill0 :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (_hLegalMove : num ∈ (cells.getCell row col).allCandidates)
          (row' col' : Fin indexRange),
          ((fillNumberHelper 0 cells (row, col) num).getCell row' col').allCandidates
            ⊆ (cells.getCell row' col').allCandidates := by
      intro cells row col num _hLegalMove row' col'
      simp [fillNumberHelper]
    have hDelete0 :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (row' col' : Fin indexRange),
          ((deleteNoteHelper 0 cells (row, col) num).getCell row' col').allCandidates
            ⊆ (cells.getCell row' col').allCandidates :=
      deleteNoteHelper_noNewNotes_of_fill 0 hFill0
    exact ⟨hFill0, hDelete0⟩
  | succ rem ih =>
    rcases ih with ⟨ihFill, ihDelete⟩
    have hFillSucc :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (_hLegalMove : num ∈ (cells.getCell row col).allCandidates)
          (row' col' : Fin indexRange),
          ((fillNumberHelper (Nat.succ rem) cells (row, col) num).getCell row' col').allCandidates
            ⊆ (cells.getCell row' col').allCandidates := by
      intro cells row col num hLegalMove row' col'
      let coords := Board.peersOf row col
      let cellsFold := coords.foldl (fun cs coord ↦ deleteNoteHelper rem cs coord num) cells
      have hFold :
          (cellsFold.getCell row' col').allCandidates ⊆ (cells.getCell row' col').allCandidates := by
        have hFoldAux :
            ∀ (cs : List (Fin indexRange × Fin indexRange)) (cells0 : Board),
              ((cs.foldl (fun su coord ↦ deleteNoteHelper rem su coord num) cells0).getCell row' col').allCandidates
                ⊆ (cells0.getCell row' col').allCandidates := by
          intro cs cells0
          induction cs generalizing cells0 with
          | nil =>
            simp
          | cons coord rest ihRest =>
            rcases coord with ⟨r, c⟩
            have hStep :
                ((deleteNoteHelper rem cells0 (r, c) num).getCell row' col').allCandidates
                  ⊆ (cells0.getCell row' col').allCandidates :=
              ihDelete cells0 r c num row' col'
            have hTail :
                ((rest.foldl (fun su coord ↦ deleteNoteHelper rem su coord num) (deleteNoteHelper rem cells0 (r, c) num)).getCell row' col').allCandidates
                  ⊆ ((deleteNoteHelper rem cells0 (r, c) num).getCell row' col').allCandidates :=
              ihRest (cells0 := deleteNoteHelper rem cells0 (r, c) num)
            intro x hx
            exact hStep (hTail (by simpa [List.foldl_cons] using hx))
        exact hFoldAux coords cells
      by_cases hr : row' = row
      · cases hr
        by_cases hc : col' = col
        · cases hc
          intro x hx
          have hCells :
              fillNumberHelper (Nat.succ rem) cells (row, col) num =
                cellsFold.setCell row col (SudokuCell.Fixed num) := by
            simp [fillNumberHelper, coords, cellsFold]
          have hSelf :
              (fillNumberHelper (Nat.succ rem) cells (row, col) num).getCell row col = SudokuCell.Fixed num := by
            calc
              (fillNumberHelper (Nat.succ rem) cells (row, col) num).getCell row col
                  = (cellsFold.setCell row col (SudokuCell.Fixed num)).getCell row col := by
                    simp [hCells]
              _ = SudokuCell.Fixed num := by
                    simpa using Board.getCell_setCell cellsFold row col (SudokuCell.Fixed num)
          have hxNum : x = num := by
            have hxInFixed : x ∈ (SudokuCell.Fixed num).allCandidates := by
              simpa [hSelf] using hx
            simpa [SudokuCell.allCandidates] using hxInFixed
          subst x
          exact hLegalMove
        · have hSame :
            (cellsFold.setCell row col (SudokuCell.Fixed num)).getCell row col' = cellsFold.getCell row col' := by
            simpa using
              Board.getCell_setCell_sameRow_of_neCol cellsFold row col col' (SudokuCell.Fixed num) hc
          simpa [fillNumberHelper, coords, cellsFold, hSame] using hFold
      · have hSame :
          (cellsFold.setCell row col (SudokuCell.Fixed num)).getCell row' col' = cellsFold.getCell row' col' := by
          simpa using
            Board.getCell_setCell_of_neRow cellsFold row row' col col' (SudokuCell.Fixed num) hr
        simpa [fillNumberHelper, coords, cellsFold, hSame] using hFold
    have hDeleteSucc :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (row' col' : Fin indexRange),
          ((deleteNoteHelper (Nat.succ rem) cells (row, col) num).getCell row' col').allCandidates
            ⊆ (cells.getCell row' col').allCandidates :=
      deleteNoteHelper_noNewNotes_of_fill (Nat.succ rem) hFillSucc
    exact ⟨hFillSucc, hDeleteSucc⟩

private theorem fillNumberHelper_noNewNotes (remaining : Nat) {s : Sudoku} (_hValid : s.isFullyValid = true) (row col : Fin indexRange) (num : SudokuInt) (hLegalMove : num ∈ (s.cells.getCell row col).allCandidates) :
  let s' := Sudoku.mk (fillNumberHelper remaining s.cells (row, col) num)
  ∀ r c : Fin indexRange, (s.cells.getCell r c).allCandidates ⊇ (s'.cells.getCell r c).allCandidates := by
  have _ := hLegalMove
  dsimp
  rcases fill_delete_noNewNotes_aux remaining with ⟨hFill, _⟩
  exact hFill s.cells row col num hLegalMove

private theorem deleteNoteHelper_noNewNotes (remaining : Nat) {s : Sudoku} (_hValid : s.isFullyValid = true) (row col : Fin indexRange) (num : SudokuInt) :
  let s' := Sudoku.mk (deleteNoteHelper remaining s.cells (row, col) num)
  ∀ r c : Fin indexRange, (s.cells.getCell r c).allCandidates ⊇ (s'.cells.getCell r c).allCandidates := by
  dsimp
  rcases fill_delete_noNewNotes_aux remaining with ⟨_, hDelete⟩
  exact hDelete s.cells row col num

private theorem deleteNoteHelper_keeps_isFullyValid_of_fill
  (remaining : Nat)
  (hFill :
    ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
      (_hValid : (Sudoku.mk cells).isFullyValid = true)
      (_hLegalMove : num ∈ (cells.getCell row col).allCandidates),
      (Sudoku.mk (fillNumberHelper remaining cells (row, col) num)).isFullyValid = true) :
  ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
    (_hValid : (Sudoku.mk cells).isFullyValid = true),
    (Sudoku.mk (deleteNoteHelper remaining cells (row, col) num)).isFullyValid = true := by
  intro cells row col num hValid
  cases hCell : cells.getCell row col with
  | Fixed n =>
    by_cases hEq : n = num
    · have hEqDel :
        deleteNoteHelper remaining cells (row, col) num = cells.setCell row col SudokuCell.invalid := by
        unfold deleteNoteHelper
        simp [hCell, hEq]
      rw [hEqDel]
      simpa [Sudoku.setCellInvalid] using
        Sudoku.setCellInvalid_keeps_isFullyValid (s := Sudoku.mk cells) hValid row col
    · have hEqDel : deleteNoteHelper remaining cells (row, col) num = cells := by
        unfold deleteNoteHelper
        simp [hCell, hEq]
      simpa [hEqDel] using hValid
  | Notes candidates =>
    let filtered : List SudokuInt := candidates.filter (fun x ↦ !decide (x = num))
    have hDeleteValid :
        (Sudoku.mk (cells.setCell row col (SudokuCell.Notes filtered))).isFullyValid = true := by
      have hDel := Sudoku.deleteNote_keeps_isFullyValid (s := Sudoku.mk cells) hValid row col num
      simpa [Sudoku.deleteNote, hCell, SudokuCell.deleteNote, filtered] using hDel
    cases hFiltered : filtered with
    | nil =>
      have hEqDel :
          deleteNoteHelper remaining cells (row, col) num =
            cells.setCell row col (SudokuCell.Notes []) := by
        have hFilterEq : candidates.filter (fun x ↦ !decide (x = num)) = [] := by
          simpa [filtered] using hFiltered
        unfold deleteNoteHelper
        simp [hCell, SudokuCell.allCandidates, hFilterEq]
      simpa [hEqDel, hFiltered] using hDeleteValid
    | cons cand rest =>
      cases rest with
      | nil =>
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              fillNumberHelper remaining (cells.setCell row col (SudokuCell.Notes [cand])) (row, col) cand := by
          have hFilterEq : candidates.filter (fun x ↦ !decide (x = num)) = [cand] := by
            simpa [filtered] using hFiltered
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEq]
        rw [hEqDel]
        have hLegalMoveSet :
            cand ∈ ((cells.setCell row col (SudokuCell.Notes [cand])).getCell row col).allCandidates := by
          have hTarget :
              (cells.setCell row col (SudokuCell.Notes [cand])).getCell row col = SudokuCell.Notes [cand] := by
            simpa using Board.getCell_setCell cells row col (SudokuCell.Notes [cand])
          simp [hTarget, SudokuCell.allCandidates]
        exact hFill (cells.setCell row col (SudokuCell.Notes [cand])) row col cand
          (by simpa [hFiltered] using hDeleteValid) hLegalMoveSet
      | cons b rest' =>
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              cells.setCell row col (SudokuCell.Notes (cand :: b :: rest')) := by
          have hFilterEq : candidates.filter (fun x ↦ !decide (x = num)) = cand :: b :: rest' := by
            simpa [filtered] using hFiltered
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEq]
        simpa [hEqDel, hFiltered] using hDeleteValid

private def peerCondAtS
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (num : SudokuInt) : Prop :=
  match s.cells.getCell tr tc with
  | .Fixed n => n ≠ num
  | .Notes candidates => num ∉ candidates

private theorem peerCondAtS_of_not_in_allCandidates
  (s : Sudoku)
  (tr tc : Fin indexRange)
  (num : SudokuInt)
  (hNot : num ∉ (s.cells.getCell tr tc).allCandidates) :
  peerCondAtS s tr tc num := by
  unfold peerCondAtS
  cases hCell : s.cells.getCell tr tc with
  | Fixed n =>
    have hNe : n ≠ num := by
      intro hEq
      apply hNot
      simp [SudokuCell.allCandidates, hCell, hEq]
    simpa [hCell] using hNe
  | Notes candidates =>
    have hNotCand : num ∉ candidates := by
      simpa [SudokuCell.allCandidates, hCell] using hNot
    simpa [hCell] using hNotCand

private theorem setCellFixed_keeps_isFullyValid_of_peerClean
  {s : Sudoku}
  (hValid : s.isFullyValid = true)
  (row col : Fin indexRange)
  (num : SudokuInt)
  (hPeersClean :
    ∀ (pr pc : Fin indexRange),
      (pr, pc) ∈ Board.peersOf row col →
      peerCondAtS s pr pc num) :
  (Sudoku.mk (s.cells.setCell row col (SudokuCell.Fixed num))).isFullyValid = true := by
  let s' : Sudoku := Sudoku.mk (s.cells.setCell row col (SudokuCell.Fixed num))
  unfold Sudoku.isFullyValid at hValid ⊢
  apply List.all_eq_true.mpr
  rintro ⟨r, c, fixedNum⟩ hTriple
  have hFixedNew : s'.cells.getCell r c = SudokuCell.Fixed fixedNum :=
    Board.getCell_fixed_iff_fixedPositions.mp hTriple
  by_cases hRC : (r, c) = (row, col)
  · cases hRC
    have hNumEq : fixedNum = num := by
      have hAtRow : s'.cells.getCell row col = SudokuCell.Fixed fixedNum := by
        simpa using hFixedNew
      have hSet : s'.cells.getCell row col = SudokuCell.Fixed num := by
        unfold s'
        simpa using Board.getCell_setCell s.cells row col (SudokuCell.Fixed num)
      have hCellsEq : SudokuCell.Fixed fixedNum = SudokuCell.Fixed num := by
        calc
          SudokuCell.Fixed fixedNum = s'.cells.getCell row col := by simpa using hAtRow.symm
          _ = SudokuCell.Fixed num := hSet
      exact SudokuCell.Fixed.inj hCellsEq
    subst fixedNum
    apply List.all_eq_true.mpr
    intro peer hPeer
    rcases peer with ⟨pr, pc⟩
    have hCondOld : peerCondAtS s pr pc num :=
      hPeersClean pr pc (by simpa using hPeer)
    have hNeTarget : (pr, pc) ≠ (row, col) := by
      intro hEq
      exact (Board.not_mem_peersOf_self row col) (by simpa [hEq] using hPeer)
    have hCellEq : s'.cells.getCell pr pc = s.cells.getCell pr pc := by
      unfold s'
      by_cases hpr : pr = row
      · cases hpr
        have hpc : pc ≠ col := by
          intro hpcEq
          apply hNeTarget
          simp [hpcEq]
        simpa using
          Board.getCell_setCell_sameRow_of_neCol s.cells row col pc (SudokuCell.Fixed num) hpc
      · simpa using
          Board.getCell_setCell_of_neRow s.cells row pr col pc (SudokuCell.Fixed num) hpr
    have hAtNew :
        (match s'.cells.getCell pr pc with
        | .Fixed n => n ≠ num
        | .Notes candidates => num ∉ candidates) = true := by
      unfold peerCondAtS at hCondOld
      cases hCell : s.cells.getCell pr pc with
      | Fixed n =>
        have hNe : n ≠ num := by
          simpa [hCell] using hCondOld
        simpa [hCellEq, hCell] using hNe
      | Notes candidates =>
        have hNot : num ∉ candidates := by
          simpa [hCell] using hCondOld
        simpa [hCellEq, hCell] using hNot
    simpa using hAtNew
  · have hFixedOld : s.cells.getCell r c = SudokuCell.Fixed fixedNum := by
      have hCellEq : s'.cells.getCell r c = s.cells.getCell r c := by
        unfold s'
        by_cases hr : r = row
        · cases hr
          have hc : c ≠ col := by
            intro hcEq
            apply hRC
            simp [hcEq]
          simpa using
            Board.getCell_setCell_sameRow_of_neCol s.cells row col c (SudokuCell.Fixed num) hc
        · simpa using
            Board.getCell_setCell_of_neRow s.cells row r col c (SudokuCell.Fixed num) hr
      simpa [hCellEq] using hFixedNew
    have hTripleOld : (r, c, fixedNum) ∈ s.cells.fixedPositions :=
      Board.getCell_fixed_iff_fixedPositions.mpr hFixedOld
    have hPeersOld :
        (Board.peersOf r c).all
          (fun (pr, pc) ↦
            match s.cells.getCell pr pc with
            | .Fixed n => n ≠ fixedNum
            | .Notes candidates => fixedNum ∉ candidates) = true :=
      (List.all_eq_true.mp hValid) (r, c, fixedNum) hTripleOld
    apply List.all_eq_true.mpr
    intro peer hPeer
    rcases peer with ⟨pr, pc⟩
    by_cases hTargetPeer : (pr, pc) = (row, col)
    · cases hTargetPeer
      have hRowPeer : (row, col) ∈ Board.peersOf r c := by
        simpa using hPeer
      have hSymm : (r, c) ∈ Board.peersOf row col :=
        Board.mem_peersOf_symm hRowPeer
      have hCondAtRC : peerCondAtS s r c num := hPeersClean r c hSymm
      have hNumNe : num ≠ fixedNum := by
        unfold peerCondAtS at hCondAtRC
        have hNe' : fixedNum ≠ num := by
          simpa [hFixedOld] using hCondAtRC
        exact hNe'.symm
      have hSet : s'.cells.getCell row col = SudokuCell.Fixed num := by
        unfold s'
        simpa using Board.getCell_setCell s.cells row col (SudokuCell.Fixed num)
      have hAtNew :
          (match s'.cells.getCell row col with
          | .Fixed n => n ≠ fixedNum
          | .Notes candidates => fixedNum ∉ candidates) = true := by
        simpa [hSet] using hNumNe
      simpa using hAtNew
    · have hPeerOld :
        (match s.cells.getCell pr pc with
        | .Fixed n => n ≠ fixedNum
        | .Notes candidates => fixedNum ∉ candidates) = true :=
        (List.all_eq_true.mp hPeersOld) (pr, pc) hPeer
      have hCellEq : s'.cells.getCell pr pc = s.cells.getCell pr pc := by
        unfold s'
        by_cases hpr : pr = row
        · cases hpr
          have hpc : pc ≠ col := by
            intro hpcEq
            apply hTargetPeer
            simp [hpcEq]
          simpa using
            Board.getCell_setCell_sameRow_of_neCol s.cells row col pc (SudokuCell.Fixed num) hpc
        · simpa using
            Board.getCell_setCell_of_neRow s.cells row pr col pc (SudokuCell.Fixed num) hpr
      simpa [s', hCellEq] using hPeerOld

private theorem deleteNoteHelper_self_num_absent
  (remaining : Nat)
  (cells : Board)
  (row col : Fin indexRange)
  (num : SudokuInt) :
  num ∉ ((deleteNoteHelper remaining cells (row, col) num).getCell row col).allCandidates := by
  cases hCell : cells.getCell row col with
  | Fixed n =>
    by_cases hEq : n = num
    · have hEqDel :
        deleteNoteHelper remaining cells (row, col) num = cells.setCell row col SudokuCell.invalid := by
        unfold deleteNoteHelper
        simp [hCell, hEq]
      rw [hEqDel]
      rw [Board.getCell_setCell cells row col SudokuCell.invalid]
      simp [SudokuCell.invalid, SudokuCell.allCandidates]
    · have hEqDel : deleteNoteHelper remaining cells (row, col) num = cells := by
        unfold deleteNoteHelper
        simp [hCell, hEq]
      rw [hEqDel]
      intro hIn
      have hNumEq : num = n := by
        simpa [hCell, SudokuCell.allCandidates] using hIn
      exact hEq hNumEq.symm
  | Notes candidates =>
    let cands' := candidates.filter (fun x ↦ !decide (x = num))
    have hNotInCands' : num ∉ cands' := by
      intro hIn
      have hInFilter : num ∈ candidates.filter (fun x ↦ !decide (x = num)) := by
        simp [cands'] at hIn
      simp at hInFilter
    cases hCands' : cands' with
    | nil =>
      have hEqDel :
          deleteNoteHelper remaining cells (row, col) num =
            cells.setCell row col (SudokuCell.Notes []) := by
        have hFilterEq :
            (SudokuCell.Notes candidates).allCandidates.filter (fun x ↦ !decide (x = num)) = [] := by
          simpa [SudokuCell.allCandidates, cands'] using hCands'
        unfold deleteNoteHelper
        simp [hCell, hFilterEq]
      rw [hEqDel]
      rw [Board.getCell_setCell cells row col (SudokuCell.Notes [])]
      simp [SudokuCell.allCandidates]
    | cons cand rest =>
      cases rest with
      | nil =>
        have hCandNe : cand ≠ num := by
          have hCandIn : cand ∈ cands' := by
            simp [hCands']
          have hCandInFilter : cand ∈ candidates.filter (fun x ↦ !decide (x = num)) := by
            simpa [cands'] using hCandIn
          simp at hCandInFilter
          exact hCandInFilter.2
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              fillNumberHelper remaining (cells.setCell row col (SudokuCell.Notes [cand])) (row, col) cand := by
          have hFilterEq :
              (SudokuCell.Notes candidates).allCandidates.filter (fun x ↦ !decide (x = num)) = [cand] := by
            simpa [SudokuCell.allCandidates, cands'] using hCands'
          unfold deleteNoteHelper
          simp [hCell, hFilterEq]
        have hLegalMoveSet :
            cand ∈ ((cells.setCell row col (SudokuCell.Notes [cand])).getCell row col).allCandidates := by
          have hTarget :
              (cells.setCell row col (SudokuCell.Notes [cand])).getCell row col = SudokuCell.Notes [cand] := by
            simpa using Board.getCell_setCell cells row col (SudokuCell.Notes [cand])
          simp [hTarget, SudokuCell.allCandidates]
        rcases fill_delete_noNewNotes_aux remaining with ⟨hFill, _⟩
        have hSub :
            ((fillNumberHelper remaining (cells.setCell row col (SudokuCell.Notes [cand])) (row, col) cand).getCell row col).allCandidates
              ⊆ ((cells.setCell row col (SudokuCell.Notes [cand])).getCell row col).allCandidates :=
          hFill (cells.setCell row col (SudokuCell.Notes [cand])) row col cand hLegalMoveSet row col
        have hNotSet : num ∉ ((cells.setCell row col (SudokuCell.Notes [cand])).getCell row col).allCandidates := by
          have hTarget :
              (cells.setCell row col (SudokuCell.Notes [cand])).getCell row col = SudokuCell.Notes [cand] := by
            simpa using Board.getCell_setCell cells row col (SudokuCell.Notes [cand])
          intro hIn
          have hNumEqCand : num = cand := by
            simpa [hTarget, SudokuCell.allCandidates] using hIn
          exact hCandNe hNumEqCand.symm
        rw [hEqDel]
        intro hIn
        exact hNotSet (hSub hIn)
      | cons b rest' =>
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              cells.setCell row col (SudokuCell.Notes (cand :: b :: rest')) := by
          have hFilterEq :
              (SudokuCell.Notes candidates).allCandidates.filter (fun x ↦ !decide (x = num)) = cand :: b :: rest' := by
            simpa [SudokuCell.allCandidates, cands'] using hCands'
          unfold deleteNoteHelper
          simp [hCell, hFilterEq]
        rw [hEqDel]
        have hTarget :
            (cells.setCell row col (SudokuCell.Notes (cand :: b :: rest'))).getCell row col = SudokuCell.Notes (cand :: b :: rest') := by
          simpa using Board.getCell_setCell cells row col (SudokuCell.Notes (cand :: b :: rest'))
        have hNotList : num ∉ (cand :: b :: rest') := by
          simpa [cands', hCands'] using hNotInCands'
        simpa [hTarget, SudokuCell.allCandidates] using hNotList

private theorem deleteNoteHelper_preserves_num_absent_at
  (remaining : Nat)
  (cells : Board)
  (row col tr tc : Fin indexRange)
  (num : SudokuInt)
  (hNot : num ∉ (cells.getCell tr tc).allCandidates) :
  num ∉ ((deleteNoteHelper remaining cells (row, col) num).getCell tr tc).allCandidates := by
  rcases fill_delete_noNewNotes_aux remaining with ⟨_, hDelete⟩
  have hSub := hDelete cells row col num tr tc
  intro hIn
  exact hNot (hSub hIn)

private theorem fold_deleteNoteHelper_preserves_num_absent
  (remaining : Nat)
  (coords : List (Fin indexRange × Fin indexRange))
  (cells : Board)
  (num : SudokuInt)
  (tr tc : Fin indexRange)
  (hNot : num ∉ (cells.getCell tr tc).allCandidates) :
  num ∉ ((coords.foldl (fun cs coord ↦ deleteNoteHelper remaining cs coord num) cells).getCell tr tc).allCandidates := by
  induction coords generalizing cells with
  | nil =>
    simpa using hNot
  | cons coord rest ih =>
    rcases coord with ⟨r, c⟩
    have hNot' :
        num ∉ ((deleteNoteHelper remaining cells (r, c) num).getCell tr tc).allCandidates :=
      deleteNoteHelper_preserves_num_absent_at remaining cells r c tr tc num hNot
    simpa [List.foldl_cons] using
      ih (cells := deleteNoteHelper remaining cells (r, c) num) hNot'

private theorem fold_deleteNoteHelper_num_absent_of_mem
  (remaining : Nat)
  (coords : List (Fin indexRange × Fin indexRange))
  (cells : Board)
  (num : SudokuInt) :
  ∀ (tr tc : Fin indexRange),
    (tr, tc) ∈ coords →
    num ∉ ((coords.foldl (fun cs coord ↦ deleteNoteHelper remaining cs coord num) cells).getCell tr tc).allCandidates := by
  intro tr tc hMem
  induction coords generalizing cells tr tc with
  | nil =>
    cases hMem
  | cons coord rest ih =>
    rcases coord with ⟨r, c⟩
    have hMem' : (tr, tc) = (r, c) ∨ (tr, tc) ∈ rest := by
      simpa using hMem
    cases hMem' with
    | inl hHead =>
      cases hHead
      have hNotHead :
          num ∉ ((deleteNoteHelper remaining cells (tr, tc) num).getCell tr tc).allCandidates :=
        deleteNoteHelper_self_num_absent remaining cells tr tc num
      have hNotFinal :
          num ∉ ((rest.foldl (fun cs coord ↦ deleteNoteHelper remaining cs coord num) (deleteNoteHelper remaining cells (tr, tc) num)).getCell tr tc).allCandidates :=
        fold_deleteNoteHelper_preserves_num_absent
          remaining
          rest
          (deleteNoteHelper remaining cells (tr, tc) num)
          num
          tr
          tc
          hNotHead
      simpa [List.foldl_cons] using hNotFinal
    | inr hTail =>
      have hNotTail :
          num ∉ ((rest.foldl (fun cs coord ↦ deleteNoteHelper remaining cs coord num) (deleteNoteHelper remaining cells (r, c) num)).getCell tr tc).allCandidates :=
        ih
          (cells := deleteNoteHelper remaining cells (r, c) num)
          (tr := tr)
          (tc := tc)
          hTail
      simpa [List.foldl_cons] using hNotTail

private theorem fillNumberHelper_keeps_isFullyValid (remaining : Nat) {s : Sudoku} (_hValid : s.isFullyValid = true) (row col : Fin indexRange) (num : SudokuInt) (_hLegalMove : num ∈ (s.cells.getCell row col).allCandidates) :
  (Sudoku.mk (fillNumberHelper remaining s.cells (row, col) num)).isFullyValid = true := by
  have hMain :
      ∀ remaining,
        ∀ (cells : Board) (r c : Fin indexRange) (n : SudokuInt)
          (hValid : (Sudoku.mk cells).isFullyValid = true)
          (hLegalMove : n ∈ (cells.getCell r c).allCandidates),
          (Sudoku.mk (fillNumberHelper remaining cells (r, c) n)).isFullyValid = true := by
    intro remaining
    induction remaining with
    | zero =>
      intro cells r c n hValid hLegalMove
      have _ := hLegalMove
      simpa [fillNumberHelper]
    | succ rem ih =>
      intro cells r c n hValid hLegalMove
      let coords := Board.peersOf r c
      let cellsFold := coords.foldl (fun cs coord ↦ deleteNoteHelper rem cs coord n) cells
      have hDeleteRem :
          ∀ (cells0 : Board) (r0 c0 : Fin indexRange) (n0 : SudokuInt)
            (hValid0 : (Sudoku.mk cells0).isFullyValid = true),
            (Sudoku.mk (deleteNoteHelper rem cells0 (r0, c0) n0)).isFullyValid = true := by
        intro cells0 r0 c0 n0 hValid0
        exact deleteNoteHelper_keeps_isFullyValid_of_fill rem
          (fun cells1 r1 c1 n1 hValid1 hLegal1 => ih cells1 r1 c1 n1 hValid1 hLegal1)
          cells0 r0 c0 n0 hValid0
      have hFoldValid :
          (Sudoku.mk cellsFold).isFullyValid = true := by
        have hFoldAux :
            ∀ (cs : List (Fin indexRange × Fin indexRange)) (cells0 : Board),
              (Sudoku.mk cells0).isFullyValid = true →
              (Sudoku.mk (cs.foldl (fun su coord ↦ deleteNoteHelper rem su coord n) cells0)).isFullyValid = true := by
          intro cs cells0 hValid0
          induction cs generalizing cells0 with
          | nil =>
            simpa using hValid0
          | cons coord rest ihRest =>
            rcases coord with ⟨rr, cc⟩
            have hStep :
                (Sudoku.mk (deleteNoteHelper rem cells0 (rr, cc) n)).isFullyValid = true :=
              hDeleteRem cells0 rr cc n hValid0
            have hTail :
                (Sudoku.mk (rest.foldl (fun su coord ↦ deleteNoteHelper rem su coord n) (deleteNoteHelper rem cells0 (rr, cc) n))).isFullyValid = true :=
              ihRest (cells0 := deleteNoteHelper rem cells0 (rr, cc) n) hStep
            simpa [List.foldl_cons] using hTail
        exact hFoldAux coords cells hValid
      have hPeersClean :
          ∀ (pr pc : Fin indexRange),
            (pr, pc) ∈ Board.peersOf r c →
            peerCondAtS (Sudoku.mk cellsFold) pr pc n := by
        intro pr pc hMemPeer
        have hNot : n ∉ (cellsFold.getCell pr pc).allCandidates := by
          have hNot' :=
            fold_deleteNoteHelper_num_absent_of_mem rem coords cells n pr pc (by simpa [coords] using hMemPeer)
          simpa [cellsFold] using hNot'
        exact peerCondAtS_of_not_in_allCandidates (Sudoku.mk cellsFold) pr pc n hNot
      have hSetValid :
          (Sudoku.mk (cellsFold.setCell r c (SudokuCell.Fixed n))).isFullyValid = true :=
        setCellFixed_keeps_isFullyValid_of_peerClean
          (s := Sudoku.mk cellsFold)
          hFoldValid
          r
          c
          n
          hPeersClean
      simpa [fillNumberHelper, coords, cellsFold] using hSetValid
  exact hMain remaining s.cells row col num _hValid _hLegalMove

private theorem deleteNoteHelper_keeps_isFullyValid (remaining : Nat) {s : Sudoku} (hValid : s.isFullyValid = true) (row col : Fin indexRange) (num : SudokuInt) :
  (Sudoku.mk (deleteNoteHelper remaining s.cells (row, col) num)).isFullyValid = true := by
  exact deleteNoteHelper_keeps_isFullyValid_of_fill remaining
    (fun cells r c n hValid' hLegalMove' =>
      by
        simpa using
          (fillNumberHelper_keeps_isFullyValid (remaining := remaining)
            (s := Sudoku.mk cells) hValid' r c n hLegalMove'))
    s.cells row col num hValid

def fillNumber (s : Sukaku) (row col : Fin indexRange) (num : SudokuInt) (hLegalMove : num ∈ (s.cells.getCell row col).allCandidates) : Sukaku :=
  ⟨fillNumberHelper (remainingBlanks s) s.cells (row, col) num, fillNumberHelper_keeps_isFullyValid (remainingBlanks s) s.h row col num hLegalMove⟩

def deleteNote (s : Sukaku) (row col : Fin indexRange) (num : SudokuInt) (_ : num ∈ (s.cells.getCell row col).allCandidates): Sukaku :=
  ⟨deleteNoteHelper (remainingBlanks s) s.cells (row, col) num, deleteNoteHelper_keeps_isFullyValid (remainingBlanks s) s.h row col num⟩

theorem fillNumber_noNewNotes (s : Sukaku) (row col : Fin indexRange) (num : SudokuInt) (hLegalMove : num ∈ (s.cells.getCell row col).allCandidates) :
  let s' := s.fillNumber row col num hLegalMove
  ∀ r c : Fin indexRange, (s.cells.getCell r c).allCandidates ⊇ (s'.cells.getCell r c).allCandidates :=
    fillNumberHelper_noNewNotes (remainingBlanks s) s.h row col num hLegalMove

theorem deleteNote_noNewNotes (s : Sukaku) (row col : Fin indexRange) (num : SudokuInt) (hLegalMove : num ∈ (s.cells.getCell row col).allCandidates) :
  let s' := s.deleteNote row col num hLegalMove
  ∀ r c : Fin indexRange, (s.cells.getCell r c).allCandidates ⊇ (s'.cells.getCell r c).allCandidates :=
    deleteNoteHelper_noNewNotes (remainingBlanks s) s.h row col num

def fromFixedNumbers (s : Sudoku) : Sukaku :=
  ⟨s.rebuildNotes.cells, Sudoku.rebuildNotes_isFullyValid⟩

end Sukaku

end leanSudoku
