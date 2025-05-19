import Lean

namespace CSE290Q

open Lean Elab Tactic

elab "my_exact " t:term : tactic => do
  let g ← popMainGoal
  g.withContext do
    let e ← Tactic.elabTermEnsuringType t (← g.getType)
    if e.hasExprMVar then
      throwError "has metavariables"
    unless ← g.checkedAssign e do
      throwError "occurs check failed"

example : 1 = 1 := by
  my_exact Eq.refl 1

#check Exists.intro

elab "my_constructor" : tactic => do
  let g ← popMainGoal
  g.withContext do
    let ty ← g.getType
    let ty ← instantiateMVars ty
    let ty := ty.consumeMData
    matchConstInduct ty.getAppFn
        (failK := fun _ => throwError "not an inductive type")
        fun ival us => do
      unless ival.ctors.length = 1 do
        throwError "`{.ofConstName ival.name}` is not an inductive type with one constructor"
      let ctor := ival.ctors[0]!
      let ctorConst : Expr := mkConst ctor us
      let (args, _, ty') ← Meta.forallMetaTelescope (← Meta.inferType ctorConst)
      unless ← Meta.isDefEq ty' ty do
        throwError "failed to use constructor to prove goal"
      g.assign <| mkAppN ctorConst args
      let possGoals := args.map (fun arg => arg.mvarId!)
      let goals ← possGoals.filterM (fun goal => not <$> goal.isAssigned)
      for goal in goals do
        goal.setKind .syntheticOpaque
      pushGoals goals.toList

example : ∃ n : Nat, n = n := by
  my_constructor -- applies Exists.intro
  case h =>
    exact rfl
  exact 37

elab "my_intro " id:ident : tactic => do
  let g ← popMainGoal
  g.withContext do
    let h := id.getId
    let ty ← Meta.whnf (← g.getType)
    unless ty.isForall do
      throwError "not a forall or implication"
    Meta.withLocalDeclD h ty.bindingDomain! fun fvar => do
      let bodyTy := ty.bindingBody!.instantiate1 fvar
      let g' ← Meta.mkFreshExprSyntheticOpaqueMVar bodyTy
      g.assign <| ← Meta.mkLambdaFVars #[fvar] g'
      pushGoal g'.mvarId!

example {p : Prop} : p → p := by
  my_intro h
  exact h
