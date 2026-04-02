import LeanSudoku.Sudoku

namespace LeanSudoku

structure Sukaku where
  cells : Board
  h : Sudoku.isFullyValid (Sudoku.mk cells) = true
deriving Repr, DecidableEq

instance : Inhabited Sukaku := ⟨⟨Vector.replicate indexRange (Vector.replicate indexRange SudokuCell.empty), by native_decide⟩⟩

namespace Sukaku

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

theorem defaultIsValid : isValid default = true := by native_decide

theorem anyCellValid_of_isValid {s : Sukaku} (h : isValid s = true) : ∀ r c, s.cells.getCell r c ≠ SudokuCell.invalid := by
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
  intro r c
  exact hProp.1 r (by simp [indices]) c (by simp [indices])

def isComplete (s : Sukaku) : Bool :=
  Sudoku.mk s.cells |>.isComplete

def remainingBlanks (s : Sukaku) : Nat :=
  List.product indices indices |>.countP fun (r, c) ↦
    match s.cells.getCell r c with
    | .Fixed _ => false
    | .Notes _ => true

private theorem allCellFixed_of_remainingBlanks {s : Sukaku} (h0 : s.remainingBlanks = 0) :
  ∀ row col : Fin indexRange, (s.cells.getCell row col).isFixed = true := by
  intro r c
  cases hCell : s.cells.getCell r c with
  | Fixed n => trivial
  | Notes candidates =>
    have hCountZero :
        List.countP
          (fun (p : Fin indexRange × Fin indexRange) ↦
            match s.cells.getCell p.1 p.2 with
            | .Fixed _ => false
            | .Notes _ => true)
          (List.product indices indices) = 0 := by
      simpa [Sukaku.remainingBlanks] using h0
    have hNotTrue :=
      (List.countP_eq_zero.mp hCountZero)
        (r, c)
        (by simp [indices])
    have hTrueHere :
        (match s.cells.getCell r c with
        | .Fixed _ => false
        | .Notes _ => true) = true := by
      simp [hCell]
    exact False.elim (hNotTrue hTrueHere)

theorem remainingBlanks_of_remainBlank {s : Sukaku} (hRemain : ∃ row col : Fin indexRange, (s.cells.getCell row col).isNotes = true) :
  0 < s.remainingBlanks := by
  apply Nat.zero_lt_of_ne_zero
  intro hZero
  have hCountZero :
      List.countP
        (fun (p : Fin indexRange × Fin indexRange) ↦
          match s.cells.getCell p.1 p.2 with
          | .Fixed _ => false
          | .Notes _ => true)
        (List.product indices indices) = 0 := by
    simpa [Sukaku.remainingBlanks] using hZero
  rcases hRemain with ⟨row, col, hIsNotes⟩
  have hNotTrue :=
    (List.countP_eq_zero.mp hCountZero)
      (row, col)
      (by simp [indices])
  have hTrueHere :
      (match s.cells.getCell row col with
      | .Fixed _ => false
      | .Notes _ => true) = true := by
    simpa [SudokuCell.isNotes] using hIsNotes
  exact hNotTrue hTrueHere

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
    let filtered : List SudokuInt := candidates.filter (fun x ↦ x ≠ num)
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
          have hxInFilter' : x ∈ candidates.filter (fun x ↦ x ≠ num) := by
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
        have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = filtered := by
          simp [filtered]
        unfold deleteNoteHelper
        simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hFiltered]
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
        have hInFilter' : candidate' ∈ candidates.filter (fun x ↦ x ≠ num) := by
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
          have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = filtered := by
            simp [filtered]
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hFiltered]
        rw [hEqDel]
        intro x hx
        exact hSetSubsetSingle (hFillSubsetSet hx)
      | cons b rest' =>
        have hEqDelMany :
            deleteNoteHelper remaining cells (row, col) num =
              cells.setCell row col (SudokuCell.Notes (candidate' :: b :: rest')) := by
          have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = filtered := by
            simp [filtered]
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hFiltered]
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
    let filtered : List SudokuInt := candidates.filter (fun x ↦ x ≠ num)
    have hDeleteValid :
        (Sudoku.mk (cells.setCell row col (SudokuCell.Notes filtered))).isFullyValid = true := by
      have hDel := Sudoku.deleteNote_keeps_isFullyValid (s := Sudoku.mk cells) hValid row col num
      simpa [Sudoku.deleteNote, hCell, SudokuCell.deleteNote, filtered] using hDel
    cases hFiltered : filtered with
    | nil =>
      have hEqDel :
          deleteNoteHelper remaining cells (row, col) num =
            cells.setCell row col (SudokuCell.Notes []) := by
        have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = filtered := by
          simp [filtered]
        unfold deleteNoteHelper
        simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hFiltered]
      simpa [hEqDel, hFiltered] using hDeleteValid
    | cons cand rest =>
      cases rest with
      | nil =>
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              fillNumberHelper remaining (cells.setCell row col (SudokuCell.Notes [cand])) (row, col) cand := by
          have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = filtered := by
            simp [filtered]
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hFiltered]
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
          have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = filtered := by
            simp [filtered]
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hFiltered]
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
    let cands' := candidates.filter (fun x ↦ x ≠ num)
    have hNotInCands' : num ∉ cands' := by
      intro hIn
      have hInFilter : num ∈ candidates.filter (fun x ↦ x ≠ num) := by
        simp [cands'] at hIn
      simp at hInFilter
    cases hCands' : cands' with
    | nil =>
      have hEqDel :
          deleteNoteHelper remaining cells (row, col) num =
            cells.setCell row col (SudokuCell.Notes []) := by
        have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = cands' := by
          simp [cands']
        unfold deleteNoteHelper
        simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hCands']
      rw [hEqDel]
      rw [Board.getCell_setCell cells row col (SudokuCell.Notes [])]
      simp [SudokuCell.allCandidates]
    | cons cand rest =>
      cases rest with
      | nil =>
        have hCandNe : cand ≠ num := by
          have hCandIn : cand ∈ cands' := by
            simp [hCands']
          have hCandInFilter : cand ∈ candidates.filter (fun x ↦ x ≠ num) := by
            simpa [cands'] using hCandIn
          simp at hCandInFilter
          exact hCandInFilter.2
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              fillNumberHelper remaining (cells.setCell row col (SudokuCell.Notes [cand])) (row, col) cand := by
          have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = cands' := by
            simp [cands']
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hCands']
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
          have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = cands' := by
            simp [cands']
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hCands']
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

private theorem isValid_of_noNewNotes
  {s s' : Sukaku}
  (hNoNew : ∀ r c : Fin indexRange,
    (s.cells.getCell r c).allCandidates ⊇ (s'.cells.getCell r c).allCandidates)
  (hValid' : s'.isValid = true) :
  s.isValid = true := by
  have hProp' :
      (∀ (a : Fin indexRange), a ∈ indices →
        ∀ (b : Fin indexRange), b ∈ indices →
          s'.cells.getCell a b ≠ SudokuCell.invalid) ∧
      (∀ (unit : List (Fin indexRange × Fin indexRange)), unit ∈ Board.iterUnits →
        ∀ (n : Fin indexRange), n ∈ indices →
          ∃ pr pc, (pr, pc) ∈ unit ∧
            n ∈
              match s'.cells.getCell pr pc with
              | .Fixed num => [num]
              | .Notes candidates => candidates) := by
    simpa [isValid, coordPairs] using hValid'
  have hInCell :
      ∀ (a : Fin indexRange), a ∈ indices →
        ∀ (b : Fin indexRange), b ∈ indices →
          s.cells.getCell a b ≠ SudokuCell.invalid := by
    intro a ha b hb
    by_contra hOldInvalid
    have hSubset := hNoNew a b
    have hNewNotInvalid := hProp'.1 a ha b hb
    have hNewAllEmpty : (s'.cells.getCell a b).allCandidates = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have hxOld : x ∈ (s.cells.getCell a b).allCandidates := hSubset hx
      simp [hOldInvalid, SudokuCell.invalid, SudokuCell.allCandidates] at hxOld
    have hNewInvalid : s'.cells.getCell a b = SudokuCell.invalid := by
      cases hCellNew : s'.cells.getCell a b with
      | Fixed n =>
        have hImpossible : ([n] : List SudokuInt) = [] := by
          simp [SudokuCell.allCandidates, hCellNew] at hNewAllEmpty
        cases hImpossible
      | Notes candidates =>
        have hCandidatesEmpty : candidates = [] := by
          simpa [SudokuCell.allCandidates, hCellNew] using hNewAllEmpty
        simp [SudokuCell.invalid, hCandidatesEmpty]
    exact hNewNotInvalid hNewInvalid
  have hCross :
      ∀ (unit : List (Fin indexRange × Fin indexRange)), unit ∈ Board.iterUnits →
        ∀ (n : Fin indexRange), n ∈ indices →
          ∃ pr pc, (pr, pc) ∈ unit ∧
            n ∈
              match s.cells.getCell pr pc with
              | .Fixed num => [num]
              | .Notes candidates => candidates := by
    intro unit hUnit n hn
    rcases hProp'.2 unit hUnit n hn with ⟨pr, pc, hMem, hInNew⟩
    refine ⟨pr, pc, hMem, ?_⟩
    have hInNew' : n ∈ (s'.cells.getCell pr pc).allCandidates := by
      simpa [SudokuCell.allCandidates] using hInNew
    have hInOld' : n ∈ (s.cells.getCell pr pc).allCandidates := hNoNew pr pc hInNew'
    simpa [SudokuCell.allCandidates] using hInOld'
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
              | .Notes candidates => candidates) :=
    ⟨hInCell, hCross⟩
  simpa [isValid, coordPairs] using hProp

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

theorem isValid_of_fillNumber_validAfter
  {s : Sukaku}
  {hLegalMove : num ∈ (s.cells.getCell row col).allCandidates}
  (hValid : (s.fillNumber row col num hLegalMove).isValid = true) :
  s.isValid = true := by
  have hNoNew :
      ∀ r c : Fin indexRange,
        (s.cells.getCell r c).allCandidates ⊇
          ((s.fillNumber row col num hLegalMove).cells.getCell r c).allCandidates := by
    simpa using fillNumber_noNewNotes s row col num hLegalMove
  exact isValid_of_noNewNotes
    (s := s)
    (s' := s.fillNumber row col num hLegalMove)
    hNoNew
    hValid

theorem isValid_of_deleteNote_validAfter
  {s : Sukaku}
  {hLegalMove : num ∈ (s.cells.getCell row col).allCandidates}
  (hValid : (s.deleteNote row col num hLegalMove).isValid = true) :
  s.isValid = true := by
  have hNoNew :
      ∀ r c : Fin indexRange,
        (s.cells.getCell r c).allCandidates ⊇
          ((s.deleteNote row col num hLegalMove).cells.getCell r c).allCandidates := by
    simpa using deleteNote_noNewNotes s row col num hLegalMove
  exact isValid_of_noNewNotes
    (s := s)
    (s' := s.deleteNote row col num hLegalMove)
    hNoNew
    hValid

theorem isValid_of_remainingBlanks_eq_zero
  (s : Sukaku)
  (h0 : s.remainingBlanks = 0) :
  s.isValid = true := by
  have hInCell :
      ∀ (a : Fin indexRange), a ∈ indices →
        ∀ (b : Fin indexRange), b ∈ indices →
          s.cells.getCell a b ≠ SudokuCell.invalid := by
    intro a ha b hb
    have hFixed : (s.cells.getCell a b).isFixed = true :=
      allCellFixed_of_remainingBlanks h0 a b
    cases hCell : s.cells.getCell a b with
    | Fixed n => simp [SudokuCell.invalid]
    | Notes candidates =>
      simp [SudokuCell.isFixed, hCell] at hFixed
  have hCross :
      ∀ (unit : List (Fin indexRange × Fin indexRange)), unit ∈ Board.iterUnits →
        ∀ (n : Fin indexRange), n ∈ indices →
          ∃ pr pc, (pr, pc) ∈ unit ∧
            n ∈
              match s.cells.getCell pr pc with
              | .Fixed num => [num]
              | .Notes candidates => candidates := by
    intro unit hUnit n hn
    rcases (by simpa [Board.iterUnits, coordPairs, List.mem_map] using hUnit :
      ∃ r ∈ indices, ∃ c ∈ indices, (r, c) :: Board.peersOf r c = unit) with ⟨r, hr, c0, hc0, hEqUnit⟩
    let f : Fin indexRange → SudokuInt := fun cc ↦
      match s.cells.getCell r cc with
      | .Fixed v => v
      | .Notes _ => n
    have hfEq : ∀ cc : Fin indexRange, s.cells.getCell r cc = SudokuCell.Fixed (f cc) := by
      intro cc
      have hFixed : (s.cells.getCell r cc).isFixed = true :=
        allCellFixed_of_remainingBlanks h0 r cc
      cases hCell : s.cells.getCell r cc with
      | Fixed v => simp [f, hCell]
      | Notes candidates =>
        simp [SudokuCell.isFixed, hCell] at hFixed
    have hfInj : Function.Injective f := by
      intro c1 c2 hEq
      by_contra hNe
      have hPeerMem : (r, c2) ∈ Board.peersOf r c1 :=
        Board.mem_peersOf_sameRow_neCol r c1 c2 (by simpa [eq_comm] using hNe)
      have hFixed1 : s.cells.getCell r c1 = SudokuCell.Fixed (f c1) := hfEq c1
      have hFixed2 : s.cells.getCell r c2 = SudokuCell.Fixed (f c2) := hfEq c2
      have hNeVal : f c2 ≠ f c1 := by
        exact Sudoku.fixedPeer_ne_num_of_isFullyValid
          (s := Sudoku.mk s.cells)
          s.h
          r
          c1
          (f c1)
          (by simp [hFixed1])
          (hPeerMem := hPeerMem)
          (hPeerFixed := hFixed2)
      exact hNeVal (by simpa [eq_comm] using hEq)
    have hfSurj : Function.Surjective f :=
      (Finite.injective_iff_surjective (f := f)).1 hfInj
    rcases hfSurj n with ⟨cn, hcn⟩
    have hMemUnit : (r, cn) ∈ (r, c0) :: Board.peersOf r c0 := by
      by_cases hcn0 : cn = c0
      · simp [hcn0]
      · have hPeer : (r, cn) ∈ Board.peersOf r c0 :=
          Board.mem_peersOf_sameRow_neCol r c0 cn (by simpa [eq_comm] using hcn0)
        simp [hPeer]
    have hCellN : s.cells.getCell r cn = SudokuCell.Fixed n := by
      calc
        s.cells.getCell r cn = SudokuCell.Fixed (f cn) := hfEq cn
        _ = SudokuCell.Fixed n := by simp [hcn]
    refine ⟨r, cn, ?_⟩
    refine ⟨by simpa [hEqUnit] using hMemUnit, ?_⟩
    rw [hCellN]
    exact List.mem_cons_self
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
              | .Notes candidates => candidates) :=
    ⟨hInCell, hCross⟩
  simpa [Sukaku.isValid, coordPairs] using hProp

private def fixedOrInvalid (cell : SudokuCell) : Prop :=
  cell.isFixed = true ∨ cell = SudokuCell.invalid

private theorem deleteNoteHelper_fixedOrInvalid_of_fill
  (remaining : Nat)
  (hFill :
    ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
      (tr tc : Fin indexRange),
      fixedOrInvalid (cells.getCell tr tc) →
      fixedOrInvalid ((fillNumberHelper remaining cells (row, col) num).getCell tr tc)) :
  ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
    (tr tc : Fin indexRange),
    fixedOrInvalid (cells.getCell tr tc) →
    fixedOrInvalid ((deleteNoteHelper remaining cells (row, col) num).getCell tr tc) := by
  intro cells row col num tr tc hStart
  cases hCell : cells.getCell row col with
  | Fixed n =>
    by_cases hEq : n = num
    · have hEqDel :
        deleteNoteHelper remaining cells (row, col) num = cells.setCell row col SudokuCell.invalid := by
        unfold deleteNoteHelper
        simp [hCell, hEq]
      rw [hEqDel]
      by_cases hr : tr = row
      · cases hr
        by_cases hc : tc = col
        · cases hc
          right
          simpa using Board.getCell_setCell cells row col SudokuCell.invalid
        · have hSame :
            (cells.setCell row col SudokuCell.invalid).getCell row tc = cells.getCell row tc := by
            simpa using
              Board.getCell_setCell_sameRow_of_neCol cells row col tc SudokuCell.invalid hc
          simpa [hSame] using hStart
      · have hSame :
          (cells.setCell row col SudokuCell.invalid).getCell tr tc = cells.getCell tr tc := by
          simpa using
            Board.getCell_setCell_of_neRow cells row tr col tc SudokuCell.invalid hr
        simpa [hSame] using hStart
    · have hEqDel : deleteNoteHelper remaining cells (row, col) num = cells := by
        unfold deleteNoteHelper
        simp [hCell, hEq]
      simpa [hEqDel] using hStart
  | Notes candidates =>
    let filtered : List SudokuInt := candidates.filter (fun x ↦ x ≠ num)
    cases hFiltered : filtered with
    | nil =>
      have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = filtered := by
        simp [filtered]
      have hEqDel :
          deleteNoteHelper remaining cells (row, col) num =
            cells.setCell row col (SudokuCell.Notes []) := by
        unfold deleteNoteHelper
        simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hFiltered]
      rw [hEqDel]
      by_cases hr : tr = row
      · cases hr
        by_cases hc : tc = col
        · cases hc
          right
          simpa [SudokuCell.invalid] using Board.getCell_setCell cells row col (SudokuCell.Notes [])
        · have hSame :
            (cells.setCell row col (SudokuCell.Notes [])).getCell row tc = cells.getCell row tc := by
            simpa using
              Board.getCell_setCell_sameRow_of_neCol cells row col tc (SudokuCell.Notes []) hc
          simpa [hSame] using hStart
      · have hSame :
          (cells.setCell row col (SudokuCell.Notes [])).getCell tr tc = cells.getCell tr tc := by
          simpa using
            Board.getCell_setCell_of_neRow cells row tr col tc (SudokuCell.Notes []) hr
        simpa [hSame] using hStart
    | cons cand rest =>
      cases rest with
      | nil =>
        have hNotSelf : (tr, tc) ≠ (row, col) := by
          intro hEqPair
          cases hEqPair
          cases hStart with
          | inl hFixed =>
            simp [SudokuCell.isFixed, hCell] at hFixed
          | inr hInv =>
            have hCandidatesNil : candidates = [] := by
              have hEqCell : SudokuCell.Notes candidates = SudokuCell.invalid := by
                simpa [hCell] using hInv
              simpa [SudokuCell.invalid] using hEqCell
            simp [filtered, hCandidatesNil] at hFiltered
        have hSetEq :
            (cells.setCell row col (SudokuCell.Notes [cand])).getCell tr tc = cells.getCell tr tc := by
          by_cases hr : tr = row
          · cases hr
            have htc : tc ≠ col := by
              intro hEq
              apply hNotSelf
              simp [hEq]
            simpa using
              Board.getCell_setCell_sameRow_of_neCol cells row col tc (SudokuCell.Notes [cand]) htc
          · simpa using
              Board.getCell_setCell_of_neRow cells row tr col tc (SudokuCell.Notes [cand]) hr
        have hStartSet : fixedOrInvalid ((cells.setCell row col (SudokuCell.Notes [cand])).getCell tr tc) := by
          simpa [fixedOrInvalid, hSetEq] using hStart
        have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = filtered := by
          simp [filtered]
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              fillNumberHelper remaining (cells.setCell row col (SudokuCell.Notes [cand])) (row, col) cand := by
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hFiltered]
        rw [hEqDel]
        exact hFill (cells.setCell row col (SudokuCell.Notes [cand])) row col cand tr tc hStartSet
      | cons b rest' =>
        have hNotSelf : (tr, tc) ≠ (row, col) := by
          intro hEqPair
          cases hEqPair
          cases hStart with
          | inl hFixed =>
            simp [SudokuCell.isFixed, hCell] at hFixed
          | inr hInv =>
            have hCandidatesNil : candidates = [] := by
              have hEqCell : SudokuCell.Notes candidates = SudokuCell.invalid := by
                simpa [hCell] using hInv
              simpa [SudokuCell.invalid] using hEqCell
            simp [filtered, hCandidatesNil] at hFiltered
        have hFilterEqNot : List.filter (fun x ↦ !decide (x = num)) candidates = filtered := by
          simp [filtered]
        have hEqDel :
            deleteNoteHelper remaining cells (row, col) num =
              cells.setCell row col (SudokuCell.Notes (cand :: b :: rest')) := by
          unfold deleteNoteHelper
          simp [hCell, SudokuCell.allCandidates, hFilterEqNot, hFiltered]
        rw [hEqDel]
        by_cases hr : tr = row
        · cases hr
          have htc : tc ≠ col := by
            intro hEq
            apply hNotSelf
            simp [hEq]
          have hSame :
              (cells.setCell row col (SudokuCell.Notes (cand :: b :: rest'))).getCell row tc = cells.getCell row tc := by
            simpa using
              Board.getCell_setCell_sameRow_of_neCol cells row col tc (SudokuCell.Notes (cand :: b :: rest')) htc
          simpa [fixedOrInvalid, hSame] using hStart
        · have hSame :
            (cells.setCell row col (SudokuCell.Notes (cand :: b :: rest'))).getCell tr tc = cells.getCell tr tc := by
            simpa using
              Board.getCell_setCell_of_neRow cells row tr col tc (SudokuCell.Notes (cand :: b :: rest')) hr
          simpa [fixedOrInvalid, hSame] using hStart

private theorem fill_delete_fixedOrInvalid_aux :
  ∀ remaining,
    (∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
      (tr tc : Fin indexRange),
      fixedOrInvalid (cells.getCell tr tc) →
      fixedOrInvalid ((fillNumberHelper remaining cells (row, col) num).getCell tr tc))
    ∧
    (∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
      (tr tc : Fin indexRange),
      fixedOrInvalid (cells.getCell tr tc) →
      fixedOrInvalid ((deleteNoteHelper remaining cells (row, col) num).getCell tr tc)) := by
  intro remaining
  induction remaining with
  | zero =>
    have hFill0 :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (tr tc : Fin indexRange),
          fixedOrInvalid (cells.getCell tr tc) →
          fixedOrInvalid ((fillNumberHelper 0 cells (row, col) num).getCell tr tc) := by
      intro cells row col num tr tc hStart
      simpa [fillNumberHelper] using hStart
    have hDelete0 :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (tr tc : Fin indexRange),
          fixedOrInvalid (cells.getCell tr tc) →
          fixedOrInvalid ((deleteNoteHelper 0 cells (row, col) num).getCell tr tc) :=
      deleteNoteHelper_fixedOrInvalid_of_fill 0 hFill0
    exact ⟨hFill0, hDelete0⟩
  | succ rem ih =>
    have hFillRem :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (tr tc : Fin indexRange),
          fixedOrInvalid (cells.getCell tr tc) →
          fixedOrInvalid ((fillNumberHelper rem cells (row, col) num).getCell tr tc) := ih.1
    have hDeleteRem :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (tr tc : Fin indexRange),
          fixedOrInvalid (cells.getCell tr tc) →
          fixedOrInvalid ((deleteNoteHelper rem cells (row, col) num).getCell tr tc) := ih.2
    have hFillSucc :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (tr tc : Fin indexRange),
          fixedOrInvalid (cells.getCell tr tc) →
          fixedOrInvalid ((fillNumberHelper (Nat.succ rem) cells (row, col) num).getCell tr tc) := by
      intro cells row col num tr tc hStart
      let coords := Board.peersOf row col
      let cellsFold := coords.foldl (fun cs coord ↦ deleteNoteHelper rem cs coord num) cells
      have hFold : fixedOrInvalid (cellsFold.getCell tr tc) := by
        have hAux :
            ∀ (cs : List (Fin indexRange × Fin indexRange)) (cells0 : Board),
              fixedOrInvalid (cells0.getCell tr tc) →
              fixedOrInvalid ((cs.foldl (fun su coord ↦ deleteNoteHelper rem su coord num) cells0).getCell tr tc) := by
          intro cs
          induction cs with
          | nil =>
            intro cells0 hStart0
            simpa using hStart0
          | cons coord rest ihRest =>
            intro cells0 hStart0
            rcases coord with ⟨r, c⟩
            have hStep :
                fixedOrInvalid ((deleteNoteHelper rem cells0 (r, c) num).getCell tr tc) :=
              hDeleteRem cells0 r c num tr tc hStart0
            simpa [List.foldl_cons] using
              ihRest (cells0 := deleteNoteHelper rem cells0 (r, c) num) hStep
        exact hAux coords cells hStart
      unfold fillNumberHelper
      by_cases hr : tr = row
      · cases hr
        by_cases hc : tc = col
        · cases hc
          left
          have hTarget :
              ((cellsFold.setCell row col (SudokuCell.Fixed num)).getCell row col).isFixed = true := by
            simpa [SudokuCell.isFixed] using
              congrArg SudokuCell.isFixed (Board.getCell_setCell cellsFold row col (SudokuCell.Fixed num))
          simpa [fillNumberHelper, coords, cellsFold, fixedOrInvalid] using hTarget
        · have hSame :
            (cellsFold.setCell row col (SudokuCell.Fixed num)).getCell row tc = cellsFold.getCell row tc := by
            simpa using
              Board.getCell_setCell_sameRow_of_neCol cellsFold row col tc (SudokuCell.Fixed num) hc
          simpa [fillNumberHelper, coords, cellsFold, fixedOrInvalid, hSame] using hFold
      · have hSame :
          (cellsFold.setCell row col (SudokuCell.Fixed num)).getCell tr tc = cellsFold.getCell tr tc := by
          simpa using
            Board.getCell_setCell_of_neRow cellsFold row tr col tc (SudokuCell.Fixed num) hr
        simpa [fillNumberHelper, coords, cellsFold, fixedOrInvalid, hSame] using hFold
    have hDeleteSucc :
        ∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (tr tc : Fin indexRange),
          fixedOrInvalid (cells.getCell tr tc) →
          fixedOrInvalid ((deleteNoteHelper (Nat.succ rem) cells (row, col) num).getCell tr tc) :=
      deleteNoteHelper_fixedOrInvalid_of_fill (Nat.succ rem) hFillSucc
    have hPairSucc :
        (∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (tr tc : Fin indexRange),
          fixedOrInvalid (cells.getCell tr tc) →
          fixedOrInvalid ((fillNumberHelper (Nat.succ rem) cells (row, col) num).getCell tr tc))
        ∧
        (∀ (cells : Board) (row col : Fin indexRange) (num : SudokuInt)
          (tr tc : Fin indexRange),
          fixedOrInvalid (cells.getCell tr tc) →
          fixedOrInvalid ((deleteNoteHelper (Nat.succ rem) cells (row, col) num).getCell tr tc)) :=
      ⟨hFillSucc, hDeleteSucc⟩
    simpa [Nat.succ_eq_add_one] using hPairSucc

private theorem fillNumber_fixedOrInvalid_of_fixed
  (s : Sukaku)
  (row col : Fin indexRange)
  (num : SudokuInt)
  (hLegalMove : num ∈ (s.cells.getCell row col).allCandidates)
  (tr tc : Fin indexRange)
  (hFixed : (s.cells.getCell tr tc).isFixed = true) :
  fixedOrInvalid ((s.fillNumber row col num hLegalMove).cells.getCell tr tc) := by
  rcases fill_delete_fixedOrInvalid_aux (remainingBlanks s) with ⟨hFill, _⟩
  simpa [Sukaku.fillNumber, fixedOrInvalid] using
    hFill s.cells row col num tr tc (Or.inl hFixed)

private theorem deleteNote_fixedOrInvalid_of_fixed
  (s : Sukaku)
  (row col : Fin indexRange)
  (num : SudokuInt)
  (hLegalMove : num ∈ (s.cells.getCell row col).allCandidates)
  (tr tc : Fin indexRange)
  (hFixed : (s.cells.getCell tr tc).isFixed = true) :
  fixedOrInvalid ((s.deleteNote row col num hLegalMove).cells.getCell tr tc) := by
  rcases fill_delete_fixedOrInvalid_aux (remainingBlanks s) with ⟨_, hDelete⟩
  simpa [Sukaku.deleteNote, fixedOrInvalid] using
    hDelete s.cells row col num tr tc (Or.inl hFixed)

private theorem remainingBlanks_le_of_notesImp
  (s s' : Sukaku)
  (hImp : ∀ r c : Fin indexRange,
    (s'.cells.getCell r c).isNotes = true → (s.cells.getCell r c).isNotes = true) :
  s'.remainingBlanks ≤ s.remainingBlanks := by
  unfold Sukaku.remainingBlanks
  exact List.countP_mono_left (l := List.product indices indices) (p := fun rc ↦ (s'.cells.getCell rc.1 rc.2).isNotes)
    (q := fun rc ↦ (s.cells.getCell rc.1 rc.2).isNotes)
    (by
      intro rc hMem hTrue
      exact hImp rc.1 rc.2 hTrue)

theorem remainingBlanks_le_of_fillNumber_ifValidAfter
  (s : Sukaku)
  (row col : Fin indexRange)
  (num : SudokuInt)
  (hLegalMove : num ∈ (s.cells.getCell row col).allCandidates)
  (hValidAfter : (s.fillNumber row col num hLegalMove).isValid = true) :
  (s.fillNumber row col num hLegalMove).remainingBlanks ≤ s.remainingBlanks := by
  let s' := s.fillNumber row col num hLegalMove
  have hNoInvalid : ∀ r c : Fin indexRange, s'.cells.getCell r c ≠ SudokuCell.invalid :=
    anyCellValid_of_isValid (s := s') hValidAfter
  have hImp : ∀ r c : Fin indexRange,
      (s'.cells.getCell r c).isNotes = true → (s.cells.getCell r c).isNotes = true := by
    intro r c hNewNotes
    by_cases hOldFixed : (s.cells.getCell r c).isFixed = true
    · have hFixedOrInvalid : fixedOrInvalid (s'.cells.getCell r c) :=
        fillNumber_fixedOrInvalid_of_fixed s row col num hLegalMove r c hOldFixed
      cases hFixedOrInvalid with
      | inl hNewFixed =>
          have hFalse : False := by
            cases hCellNew : s'.cells.getCell r c with
            | Fixed v =>
              simp [SudokuCell.isNotes, hCellNew] at hNewNotes
            | Notes candidates =>
              simp [SudokuCell.isFixed, hCellNew] at hNewFixed
          exact False.elim hFalse
      | inr hNewInvalid =>
        exact False.elim ((hNoInvalid r c) hNewInvalid)
    · cases hOldCell : s.cells.getCell r c with
      | Fixed n =>
        simp [SudokuCell.isFixed, hOldCell] at hOldFixed
      | Notes candidates =>
        simp [SudokuCell.isNotes]
  simpa [s'] using remainingBlanks_le_of_notesImp s s' hImp

theorem remainingBlanks_le_of_deleteNote_ifValidAfter
  (s : Sukaku)
  (row col : Fin indexRange)
  (num : SudokuInt)
  (hLegalMove : num ∈ (s.cells.getCell row col).allCandidates)
  (hValidAfter : (s.deleteNote row col num hLegalMove).isValid = true) :
  (s.deleteNote row col num hLegalMove).remainingBlanks ≤ s.remainingBlanks := by
  let s' := s.deleteNote row col num hLegalMove
  have hNoInvalid : ∀ r c : Fin indexRange, s'.cells.getCell r c ≠ SudokuCell.invalid :=
    anyCellValid_of_isValid (s := s') hValidAfter
  have hImp : ∀ r c : Fin indexRange,
      (s'.cells.getCell r c).isNotes = true → (s.cells.getCell r c).isNotes = true := by
    intro r c hNewNotes
    by_cases hOldFixed : (s.cells.getCell r c).isFixed = true
    · have hFixedOrInvalid : fixedOrInvalid (s'.cells.getCell r c) :=
        deleteNote_fixedOrInvalid_of_fixed s row col num hLegalMove r c hOldFixed
      cases hFixedOrInvalid with
      | inl hNewFixed =>
          have hFalse : False := by
            cases hCellNew : s'.cells.getCell r c with
            | Fixed v =>
              simp [SudokuCell.isNotes, hCellNew] at hNewNotes
            | Notes candidates =>
              simp [SudokuCell.isFixed, hCellNew] at hNewFixed
          exact False.elim hFalse
      | inr hNewInvalid =>
        exact False.elim ((hNoInvalid r c) hNewInvalid)
    · cases hOldCell : s.cells.getCell r c with
      | Fixed n =>
        simp [SudokuCell.isFixed, hOldCell] at hOldFixed
      | Notes candidates =>
        simp [SudokuCell.isNotes]
  simpa [s'] using remainingBlanks_le_of_notesImp s s' hImp

theorem remainingBlanks_lt_of_fillNumber_ifValidAfter
  (s : Sukaku)
  (row col : Fin indexRange)
  (num : SudokuInt)
  (hLegalMove : num ∈ (s.cells.getCell row col).allCandidates)
  (hUsableMove : (s.cells.getCell row col).isNotes = true)
  (hValidAfter : (s.fillNumber row col num hLegalMove).isValid = true) :
  (s.fillNumber row col num hLegalMove).remainingBlanks < s.remainingBlanks := by
  let s' := s.fillNumber row col num hLegalMove
  have hLe : s'.remainingBlanks ≤ s.remainingBlanks := by
    simpa [s'] using
      remainingBlanks_le_of_fillNumber_ifValidAfter s row col num hLegalMove hValidAfter
  let l : List (Fin indexRange × Fin indexRange) := List.product indices indices
  let p : (Fin indexRange × Fin indexRange) → Bool := fun rc ↦ (s'.cells.getCell rc.1 rc.2).isNotes
  let q : (Fin indexRange × Fin indexRange) → Bool := fun rc ↦ (s.cells.getCell rc.1 rc.2).isNotes
  let w : Fin indexRange × Fin indexRange := (row, col)
  have hwMem : w ∈ l := by
    simp [l, w, indices]
  have hPerm : l.Perm (w :: l.erase w) := List.perm_cons_erase hwMem
  have hpwFalse : p w = false := by
    have hPos : 0 < s.remainingBlanks :=
      remainingBlanks_of_remainBlank ⟨row, col, hUsableMove⟩
    have hCellFixed : s'.cells.getCell row col = SudokuCell.Fixed num := by
      cases hRem : s.remainingBlanks with
      | zero =>
        have hFalse : False := by
          simp [hRem] at hPos
        exact False.elim hFalse
      | succ rem =>
        have hTarget :
            ((List.foldl (fun cells coord ↦ deleteNoteHelper rem cells coord num) s.cells (Board.peersOf row col)).setCell row col (SudokuCell.Fixed num)).getCell row col
              = SudokuCell.Fixed num := by
          simpa using
            Board.getCell_setCell
              (List.foldl (fun cells coord ↦ deleteNoteHelper rem cells coord num) s.cells (Board.peersOf row col))
              row col (SudokuCell.Fixed num)
        simpa [s', Sukaku.fillNumber, hRem, fillNumberHelper] using hTarget
    simp [p, w, hCellFixed, SudokuCell.isNotes]
  have hqwTrue : q w = true := by
    simpa [q, w, SudokuCell.isNotes] using hUsableMove
  have hImp : ∀ rc ∈ l, p rc = true → q rc = true := by
    intro rc hMem hP
    exact (by
      have hNoInvalid : ∀ r c : Fin indexRange, s'.cells.getCell r c ≠ SudokuCell.invalid :=
        anyCellValid_of_isValid (s := s') hValidAfter
      by_cases hOldFixed : (s.cells.getCell rc.1 rc.2).isFixed = true
      · have hFixedOrInvalid : fixedOrInvalid (s'.cells.getCell rc.1 rc.2) :=
          fillNumber_fixedOrInvalid_of_fixed s row col num hLegalMove rc.1 rc.2 hOldFixed
        cases hFixedOrInvalid with
        | inl hNewFixed =>
          have hFalse : False := by
            cases hCellNew : s'.cells.getCell rc.1 rc.2 with
            | Fixed v =>
              simp [p, SudokuCell.isNotes, hCellNew] at hP
            | Notes candidates =>
              simp [SudokuCell.isFixed, hCellNew] at hNewFixed
          exact False.elim hFalse
        | inr hNewInvalid =>
          exact False.elim ((hNoInvalid rc.1 rc.2) hNewInvalid)
      · cases hOldCell : s.cells.getCell rc.1 rc.2 with
        | Fixed n =>
          simp [SudokuCell.isFixed, hOldCell] at hOldFixed
        | Notes candidates =>
          simp [q, SudokuCell.isNotes, hOldCell])
  have hLeErase : List.countP p (l.erase w) ≤ List.countP q (l.erase w) :=
    List.countP_mono_left (l := l.erase w) (p := p) (q := q)
      (by
        intro rc hMem hP
        exact hImp rc (by simpa using List.mem_of_mem_erase hMem) hP)
  have hStrictCons : List.countP p (w :: l.erase w) < List.countP q (w :: l.erase w) := by
    have hLt : List.countP p (l.erase w) < List.countP q (l.erase w) + 1 := Nat.lt_succ_of_le hLeErase
    simpa [List.countP_cons, hpwFalse, hqwTrue, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hLt
  have hStrictCount : List.countP p l < List.countP q l := by
    calc
      List.countP p l = List.countP p (w :: l.erase w) := (List.Perm.countP_eq p hPerm)
      _ < List.countP q (w :: l.erase w) := hStrictCons
      _ = List.countP q l := (List.Perm.countP_eq q hPerm).symm
  simpa [Sukaku.remainingBlanks, l, p, q, s'] using hStrictCount

def fromFixedNumbers (s : Sudoku) : Sukaku :=
  ⟨s.rebuildNotes.cells, Sudoku.rebuildNotes_isFullyValid⟩

end Sukaku

end LeanSudoku
