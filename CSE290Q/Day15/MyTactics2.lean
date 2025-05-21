import Lean
/-!
# Some more basic tactics
-/

open Lean Meta Elab Tactic

/-!
Collecting some of the tactic API
-/

-- Gets the goals from the tactic goal list that have not been assigned.
-- (Sometimes tactics incidentally assign goals that they aren't working on.)
#check getUnsolvedGoals
-- Gets the first unsolved goal, throwing an error if there are no goals.
#check getMainGoal
-- Like `getMainGoal`, but removes it from the goal list.
#check popMainGoal
-- Pushes new goals to the front/end of the goal list.
#check pushGoal
#check pushGoals
#check appendGoals

/-!
Exercise: make `my_swap`, which swaps the first two goals.
-/

elab "my_swap" : tactic => do
  sorry

-- Test
example {p q : Prop} (hp : p) (hq : q) : p ∧ q := by
  constructor
  my_swap
  exact hq
  exact hp

/-!
Exercise: make `defer`, which moves the first goal to the end.
-/

elab "defer" : tactic => do
  sorry

example : ∃ n : Nat, n = n ∧ n ≤ n + 1 := by
  refine ⟨?n, ?_, ?_⟩
  defer
  rfl
  apply Nat.le_add_right
  exact 37

/--
Does all the checks needed to make sure it is safe to do the assignment.
-/
def Lean.MVarId.safeAssign (g : MVarId) (e : Expr) : MetaM Unit := do
  if ← g.isAssigned <||> g.isDelayedAssigned then
    throwError "metavariable is already assigned"
  let gty ← g.getType
  let ety ← inferType e
  unless ← isDefEq (← g.getType) ety do
    throwError "could not assign metavariable, metavariable {← mkHasTypeButIsExpectedMsg gty ety}"
  unless ← g.checkedAssign e do
    throwError "could not assign metavariable, likely due to occurs check failure"

/-!

-/
-- Uses the metavariable's local context as the local context.
#check MVarId.withContext
-- Tactic functions to elaborate terms (as Syntax) into.
-- These make use of a local context, so be sure to use `withContext`.
#check Tactic.elabTerm
#check Tactic.elabTermEnsuringType


/-!
Exercise: make `my_exact`.
-/
elab "my_exact " t:term : tactic => do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let g ← popMainGoal
  g.withContext do
    -- elaborate `e` ensuring it has the type of `g`
    let e : Expr ← sorry
    let mvars ← filterOldMVars (← getMVars e) mvarCounterSaved
    logUnassignedAndAbort mvars
    -- assign `e` to the main goal, safely
    sorry

example : 1 = 1 := by
  my_exact rfl

/-!
Exercise: make `my_refine`
-/
elab "my_refine " t:term : tactic => do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let g ← popMainGoal
  g.withContext do
    -- elaborate `e` ensuring it has the type of `g`
    let e : Expr ← sorry
    let mvars ← filterOldMVars (← getMVars e) mvarCounterSaved
    -- assign `e` to the main goal, safely
    sorry
    -- add the new mvars as new goals
    sorry

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  my_refine ⟨?_, ?_⟩
  exact hp
  exact hq
