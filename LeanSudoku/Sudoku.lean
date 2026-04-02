import LeanSudoku.Board

namespace LeanSudoku

structure Sudoku where
  cells : Board
deriving Repr, DecidableEq

instance : Inhabited Sudoku := ⟨⟨Vector.replicate indexRange (Vector.replicate indexRange SudokuCell.invalid)⟩⟩

namespace Sudoku

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
  have hPeers := (List.all_eq_true.mp h) (r, c, num) hTriple
  apply List.all_eq_true.mpr
  rintro ⟨pr, pc⟩ hPeer
  have hPeer := (List.all_eq_true.mp hPeers) (pr, pc) hPeer
  cases hCell : s.cells.getCell pr pc with
  | Fixed n =>
    simpa [hCell] using hPeer
  | Notes candidates =>
    simp [hCell]

theorem emptyIsFullyValid : isFullyValid default = true := by native_decide

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
    x ∈ nums.foldl (fun cs n ↦ cs.filter (fun c ↦ c ≠ n)) init
      ↔ x ∈ init ∧ ∀ n, n ∈ nums → x ≠ n := by
    induction nums generalizing init with
    | nil =>
      simp
    | cons n rest ih =>
      constructor
      · intro hMem
        have hMemIh :
            x ∈ init.filter (fun c ↦ c ≠ n) ∧ ∀ a, a ∈ rest → x ≠ a := by
          exact (ih (init := init.filter (fun c ↦ c ≠ n))).1 (by simpa [List.foldl_cons] using hMem)
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
        have hxFilter : x ∈ init.filter (fun c ↦ c ≠ n) :=
          List.mem_filter.mpr ⟨hInfo.1, by simpa using hInfo.2 n (by simp)⟩
        have hRest : ∀ a, a ∈ rest → x ≠ a := by
          intro a ha
          exact hInfo.2 a (by simp [ha])
        have hMemIh :
            x ∈ rest.foldl (fun cs n ↦ cs.filter (fun c ↦ c ≠ n)) (init.filter (fun c ↦ c ≠ n)) :=
          (ih (init := init.filter (fun c ↦ c ≠ n))).2 ⟨hxFilter, hRest⟩
        simpa [List.foldl_cons] using hMemIh

  have foldl_filter_self_eq_nil
    (nums : List SudokuInt) :
    nums.foldl (fun cs n ↦ cs.filter (fun c ↦ c ≠ n)) nums = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have hxInfo : x ∈ nums ∧ ∀ n, n ∈ nums → x ≠ n :=
      (mem_foldl_filter_neq_iff nums nums x).1 hx
    exact (hxInfo.2 x hxInfo.1) rfl

  have foldl_deleteNote_fromNotes
    (nums init : List SudokuInt) :
    nums.foldl (fun cell n ↦ SudokuCell.deleteNote cell n) (SudokuCell.Notes init)
      = SudokuCell.Notes (nums.foldl (fun cs n ↦ cs.filter (fun c ↦ c ≠ n)) init) := by
    induction nums generalizing init with
    | nil =>
      simp
    | cons n rest ih =>
      simpa [List.foldl_cons, SudokuCell.deleteNote] using ih (init := init.filter (fun c ↦ c ≠ n))

  have foldl_deleteNote_notes_allCandidates_invalid
    (candidates : List SudokuInt) :
    candidates.foldl (fun cell n ↦ SudokuCell.deleteNote cell n) (SudokuCell.Notes candidates) = SudokuCell.invalid := by
    have hSelf :
        candidates.foldl (fun cs n ↦ cs.filter (fun c ↦ c ≠ n)) candidates = [] :=
      foldl_filter_self_eq_nil candidates
    simpa [foldl_deleteNote_fromNotes, SudokuCell.invalid] using hSelf

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

theorem fixedPeer_ne_num_of_isFullyValid
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
  let base : Sudoku := -- TODO
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

end LeanSudoku
