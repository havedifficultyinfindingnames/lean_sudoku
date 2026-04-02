import LeanSudoku.Sukaku

namespace LeanSudoku

inductive SolverState
  | NoSolution
  | Partial (s : Sukaku)
  | Solved (s : Sukaku)
  | MultiSolution
deriving Repr, DecidableEq

instance : Inhabited SolverState := ⟨.NoSolution⟩

namespace BacktrackingSolver

private def pickNextCell (s : Sukaku) : Option (Fin indexRange × Fin indexRange) :=
  List.product indices indices |>.filterMap (fun (r, c) ↦
    match s.cells.getCell r c with
    | .Fixed _ => none
    | .Notes _ => some (r, c)) |>.minOn? (fun (r, c) ↦
      (s.cells.getCell r c).allCandidates.length)

private theorem remainingBlanks_of_pickNextCell_some {s : Sukaku} (hSome : (pickNextCell s).isSome = true) :
  s.remainingBlanks > 0 := by
  simp [pickNextCell] at hSome
  rcases hSome with ⟨r, hr, c, hc, hCellSome⟩
  apply Nat.zero_lt_of_ne_zero
  simp [Sukaku.remainingBlanks]
  refine ⟨r, hr, c, hc, ?_⟩
  cases hCell : s.cells.getCell r c <;> simp [hCell] at hCellSome ⊢

private theorem isNotes_of_pickNextCell_eq_some
  {s : Sukaku}
  {r c : Fin indexRange}
  (hPick : pickNextCell s = some (r, c)) :
  (s.cells.getCell r c).isNotes = true := by
  unfold pickNextCell at hPick
  have hMem :
      (r, c) ∈
        (List.product indices indices).filterMap
          (fun (r, c) ↦
            match s.cells.getCell r c with
            | .Fixed _ => none
            | .Notes _ => some (r, c)) :=
    List.minOn?_mem hPick
  rcases (List.mem_filterMap.mp hMem) with ⟨a, ha, hEq⟩
  rcases a with ⟨ar, ac⟩
  cases hCell : s.cells.getCell ar ac with
  | Fixed n =>
    simp [hCell] at hEq
  | Notes candidates =>
    have hPair : (ar, ac) = (r, c) := by
      simpa [hCell] using hEq
    cases hPair
    simp [SudokuCell.isNotes, hCell]

private theorem remainingBlanks_of_pickNextCell_eq_none {s : Sukaku} (hNone : pickNextCell s = none) :
  s.remainingBlanks = 0 := by
  by_contra hne
  have hPos : 0 < s.remainingBlanks := Nat.pos_of_ne_zero hne
  let p : (Fin indexRange × Fin indexRange) → Bool :=
    fun (r, c) ↦
      match s.cells.getCell r c with
      | .Fixed _ => false
      | .Notes _ => true
  have hExists :
      ∃ rc, rc ∈ List.product indices indices ∧ p rc = true := by
    by_contra hNo
    have hZeroCount : List.countP p (List.product indices indices) = 0 := by
      apply List.countP_eq_zero.mpr
      intro rc hMem
      have hNot : ¬ (∃ hrc : rc ∈ List.product indices indices, p rc = true) := by
        exact fun hx ↦ hNo ⟨rc, hx.1, hx.2⟩
      intro hp
      exact hNot ⟨hMem, hp⟩
    have hRBZero : s.remainingBlanks = 0 := by
      simpa [Sukaku.remainingBlanks, p] using hZeroCount
    exact (Nat.ne_of_gt hPos) hRBZero
  rcases hExists with ⟨rc, hMem, hP⟩
  rcases rc with ⟨r, c⟩
  have hSome : (pickNextCell s).isSome = true := by
    have hInProd : r ∈ indices ∧ c ∈ indices := by
      simpa [List.mem_product] using hMem
    simp [pickNextCell]
    refine ⟨r, hInProd.1, c, hInProd.2, ?_⟩
    cases hCell : s.cells.getCell r c with
    | Fixed n => simp [p, hCell] at hP
    | Notes candidates => simp
  have hSomeFalse : (pickNextCell s).isSome = false := by
    simp [hNone]
  simp [hSomeFalse] at hSome

mutual

private def solveWithFuel : (fuel : Nat) → (s : Sukaku) → s.remainingBlanks ≤ fuel → SolverState
  | 0, s, hFuel =>
    match hPick : pickNextCell s with
    | none => .Solved s
    | some _ =>
      False.elim <| by
        have hPos : s.remainingBlanks > 0 :=
          remainingBlanks_of_pickNextCell_some (by simp [hPick])
        have hZero : s.remainingBlanks = 0 := Nat.eq_zero_of_le_zero hFuel
        simp [hZero] at hPos
  | Nat.succ fuel, s, hFuel =>
    match hPick : pickNextCell s with
    | none => .Solved s
    | some (r, c) =>
      searchWithFuel fuel s hFuel r c hPick ((s.cells.getCell r c).allCandidates.attach) none

private def searchWithFuel
  (fuel : Nat)
  (s : Sukaku)
  (hFuel : s.remainingBlanks ≤ Nat.succ fuel)
  (r c : Fin indexRange)
  (hPick : pickNextCell s = some (r, c))
  (rest : List {num : SudokuInt // num ∈ (s.cells.getCell r c).allCandidates})
  (found : Option Sukaku) : SolverState :=
  match rest with
  | [] =>
    match found with
    | some sol => .Solved sol
    | none => .NoSolution
  | ⟨num, hLegalMove⟩ :: tail =>
    let s' := s.fillNumber r c num hLegalMove
    have hUsable : (s.cells.getCell r c).isNotes = true :=
      isNotes_of_pickNextCell_eq_some hPick
    if hValidAfter : s'.isValid = true then
      have hDec : s'.remainingBlanks < s.remainingBlanks :=
        Sukaku.remainingBlanks_lt_of_fillNumber_ifValidAfter s r c num hLegalMove hUsable hValidAfter
      have hLtSucc : s'.remainingBlanks < Nat.succ fuel :=
        Nat.lt_of_lt_of_le hDec hFuel
      have hFuel' : s'.remainingBlanks ≤ fuel := Nat.lt_succ_iff.mp hLtSucc
      match solveWithFuel fuel s' hFuel' with
      | .NoSolution =>
        searchWithFuel fuel s hFuel r c hPick tail found
      | .MultiSolution =>
        .MultiSolution
      | .Solved sol =>
        match found with
        | none => searchWithFuel fuel s hFuel r c hPick tail (some sol)
        | some _ => .MultiSolution
      | .Partial _ => unreachable! -- The function never returns .Partial, so it's unreachable. however, it's hard to prove
    else
      searchWithFuel fuel s hFuel r c hPick tail found

end

private theorem isValid_of_searchWithFuel_solved
  (fuel : Nat)
  (ihSolve :
    ∀ (s0 : Sukaku) (hFuel0 : s0.remainingBlanks ≤ fuel),
      (∃ sol, solveWithFuel fuel s0 hFuel0 = .Solved sol) →
      s0.isValid = true)
  (s : Sukaku)
  (hFuel : s.remainingBlanks ≤ Nat.succ fuel)
  (r c : Fin indexRange)
  (hPick : pickNextCell s = some (r, c))
  (rest : List {num : SudokuInt // num ∈ (s.cells.getCell r c).allCandidates})
  (found : Option Sukaku)
  (hFound : ∀ sol0, found = some sol0 → s.isValid = true)
  (hSolved : ∃ sol, searchWithFuel fuel s hFuel r c hPick rest found = .Solved sol) :
  s.isValid = true := by
  induction rest generalizing found with
  | nil =>
    rcases hSolved with ⟨sol, hEq⟩
    cases found with
    | none => simp [searchWithFuel] at hEq
    | some sol0 => exact hFound sol0 rfl
  | cons hd tl ih =>
    rcases hSolved with ⟨sol, hEq⟩
    rcases hd with ⟨num, hLegalMove⟩
    let s' := s.fillNumber r c num hLegalMove
    have hUsable : (s.cells.getCell r c).isNotes = true :=
      isNotes_of_pickNextCell_eq_some hPick
    by_cases hValidAfter : s'.isValid = true
    · have hDec : s'.remainingBlanks < s.remainingBlanks :=
        Sukaku.remainingBlanks_lt_of_fillNumber_ifValidAfter s r c num hLegalMove hUsable hValidAfter
      have hLtSucc : s'.remainingBlanks < Nat.succ fuel :=
        Nat.lt_of_lt_of_le hDec hFuel
      have hFuel' : s'.remainingBlanks ≤ fuel := Nat.lt_succ_iff.mp hLtSucc
      cases hRec : solveWithFuel fuel s' hFuel' with
      | NoSolution =>
        have hTail : ∃ sol, searchWithFuel fuel s hFuel r c hPick tl found = .Solved sol := by
          exact ⟨sol, by simpa [searchWithFuel, hValidAfter, hRec, s'] using hEq⟩
        exact ih found hFound hTail
      | MultiSolution =>
        simp [searchWithFuel, hValidAfter, hRec, s'] at hEq
      | Partial s1 =>
        simp [searchWithFuel, hValidAfter, hRec, s'] at hEq
      | Solved sol1 =>
        cases found with
        | none =>
          have hs'Valid : s'.isValid = true := ihSolve s' hFuel' ⟨sol1, by simp [hRec]⟩
          have hsValid : s.isValid = true :=
            Sukaku.isValid_of_fillNumber_validAfter
              (s := s)
              (row := r)
              (col := c)
              (num := num)
              (hLegalMove := hLegalMove)
              hs'Valid
          have hFound' : ∀ sol0, some sol1 = some sol0 → s.isValid = true := by
            intro sol0 hSomeEq
            exact hsValid
          have hTail : ∃ sol, searchWithFuel fuel s hFuel r c hPick tl (some sol1) = .Solved sol := by
            exact ⟨sol, by simpa [searchWithFuel, hValidAfter, hRec, s'] using hEq⟩
          exact ih (some sol1) hFound' hTail
        | some sol0 =>
          simp [searchWithFuel, hValidAfter, hRec, s'] at hEq
    · have hTail : ∃ sol, searchWithFuel fuel s hFuel r c hPick tl found = .Solved sol := by
        exact ⟨sol, by simpa [searchWithFuel, hValidAfter, s'] using hEq⟩
      exact ih found hFound hTail

def solve (s : Sukaku) : SolverState :=
  solveWithFuel (s.remainingBlanks) s (Nat.le_refl _)

theorem isValid_of_solve_solved {s : Sukaku} (hSolved : ∃ s', (solve s) = .Solved s') :
  s.isValid = true := by
  have hMain :
      ∀ (fuel : Nat) (s0 : Sukaku) (hFuel : s0.remainingBlanks ≤ fuel),
        (∃ sol, solveWithFuel fuel s0 hFuel = .Solved sol) →
        s0.isValid = true := by
    intro fuel
    induction fuel with
    | zero =>
      intro s0 hFuel hSolved0
      rcases hSolved0 with ⟨sol, hEq⟩
      unfold solveWithFuel at hEq
      split at hEq
      · have h0 : s0.remainingBlanks = 0 := remainingBlanks_of_pickNextCell_eq_none ‹pickNextCell s0 = none›
        exact Sukaku.isValid_of_remainingBlanks_eq_zero s0 h0
      · exfalso
        have hPos : s0.remainingBlanks > 0 := remainingBlanks_of_pickNextCell_some (by simp [*])
        have hZero : s0.remainingBlanks = 0 := Nat.eq_zero_of_le_zero hFuel
        simp [hZero] at hPos
    | succ fuel ih =>
      intro s0 hFuel hSolved0
      rcases hSolved0 with ⟨sol, hEq⟩
      unfold solveWithFuel at hEq
      split at hEq
      · have h0 : s0.remainingBlanks = 0 := remainingBlanks_of_pickNextCell_eq_none ‹pickNextCell s0 = none›
        exact Sukaku.isValid_of_remainingBlanks_eq_zero s0 h0
      · rename_i r c hPickSome
        have hSearch :
            ∃ sol, searchWithFuel fuel s0 hFuel r c hPickSome ((s0.cells.getCell r c).allCandidates.attach) none = .Solved sol := by
          exact ⟨sol, by simpa [searchWithFuel] using hEq⟩
        have hFoundInit : ∀ sol0, (none : Option Sukaku) = some sol0 → s0.isValid = true := by
          intro sol0 hNone
          cases hNone
        exact isValid_of_searchWithFuel_solved fuel (fun s1 hFuel1 hSolved1 => ih s1 hFuel1 hSolved1)
          s0 hFuel r c hPickSome ((s0.cells.getCell r c).allCandidates.attach) none hFoundInit hSearch
  rcases hSolved with ⟨sol, hEq⟩
  exact hMain (s.remainingBlanks) s (Nat.le_refl _) ⟨sol, by simpa [solve] using hEq⟩

end BacktrackingSolver

end LeanSudoku
