import Lean
/-!
# Implementing a tactic `prop` to prove propositional tautologies
-/

/-!
Spec: handle basic logical connectives (¬, ∧, ∨, →)

Maybe: also handle `∀`/`∃` if the body is true independent of the value of the bound variable.
-/

namespace TacticImpl
open Lean Meta

/--
A value assignment for an atom.
The reader context in `M` has a list of atom value assignments.
-/
structure AtomVal where
  /-- The propositional atom. -/
  a : Expr
  /-- The logical value of the assignment. -/
  val : Bool
  /-- If `val` is true then `pf : a`, otherwise `pf : ¬ a`. -/
  pf : Expr

/--
Returns `True` or `False` depending on `atom.val`.
-/
def AtomVal.expr (atom : AtomVal) : Expr :=
  if atom.val then
    mkConst ``True
  else
    mkConst ``False

/--
Returns a proof of `atom.a ↔ atom.expr`
-/
def AtomVal.iff (atom : AtomVal) : Expr :=
  if atom.val then
    mkApp2 (mkConst ``iff_true_intro) atom.a atom.pf
  else
    mkApp2 (mkConst ``iff_false_intro) atom.a atom.pf

structure Ctx where
  /-- A list of atom value assignments for the `M` monad. -/
  atomVals : List AtomVal := []

abbrev M := ReaderT Ctx MetaM

/--
Find a matching atom in the current atom value assignments.
-/
def findAtomVal? (e : Expr) : M (Option AtomVal) := do
  (← read).atomVals.findM? (fun atom =>
    withReducible <| withNewMCtxDepth <| isDefEq atom.a e)

/--
Adds the atom value to the current list of atom value assignments.

Invariant: `findAtomVal? atom.a` must return `none` from outside `withAtomVal atom _`.
(That is to say, we shouldn't be assigning an atom mutiple times.)
-/
def withAtomVal {α : Type} (atom : AtomVal) (m : M α) : M α :=
  withReader (fun ctx => { ctx with atomVals := atom :: ctx.atomVals })
    m

/--
After reducing `e`, the result is `e'`, with `pf : e ↔ e'`.
If `pf` is `none`, then it is assumed to be `Iff.rfl`.
-/
structure ReduceResult where
  /-- The proposition that was reduced. -/
  e : Expr
  /-- The reduced proposition. -/
  e' : Expr
  /-- The proof of `e ↔ e'` (note: `e` is not represented in this structure).
  If the proof is `none`, then assumed to be `Iff.rfl`. -/
  pf? : Option Expr

/-- Constructor for `ReduceResult`, for "no reduction". -/
def ReduceResult.rfl (e : Expr) : ReduceResult := { e, e' := e, pf? := none }

def ReduceResult.pf (r : ReduceResult) : Expr :=
  match r.pf? with
  | none => mkApp (mkConst ``Iff.refl) r.e'
  | some pf => pf

def ReduceResult.check (r : ReduceResult) (msg? : Option String := none) : MetaM Unit := do
  try
    Meta.check r.e
    Meta.check r.e'
    Meta.check r.pf
    unless ← isDefEq (mkIff r.e r.e') (← inferType r.pf) do
      throwError "result proof has wrong type{indentExpr (← inferType r.pf)}\nexpected{indentExpr (mkIff r.e r.e')}"
  catch ex =>
    if let some m := msg? then logError m!"{m}"
    throw ex

/--
Returns `some b` if the result is `True` or `False`.
-/
def ReduceResult.val? (r : ReduceResult) : Option Bool :=
  if r.e'.isConstOf ``True then some true
  else if r.e'.isConstOf ``False then some false
  else none

/-- Given `hab : a ↔ b` and `hbc : b ↔ c`, returns a proof of `a ↔ c`.
The proofs can be `none`, which means `Iff.refl`. -/
def mkIffTrans? (a b c : Expr) (hab hbc : Option Expr) : Option Expr :=
  match hab, hbc with
  | none, none => none
  | some pf1, none => some pf1
  | none, some pf2 => some pf2
  | some pf1, some pf2 => some <| mkApp5 (mkConst ``Iff.trans) a b c pf1 pf2

/-- Given two reductions, combine them into a single reduction. -/
def ReduceResult.trans (r1 r2 : ReduceResult) : ReduceResult :=
  { e := r1.e, e' := r2.e', pf? := mkIffTrans? r1.e r1.e' r2.e' r1.pf? r2.pf? }

theorem reduce_false_and (q : Prop) : (False ∧ q) ↔ False := by rw [false_and]
theorem reduce_and_false (p : Prop) : (p ∧ False) ↔ False := by rw [and_false]
theorem reduce_true_and (q : Prop) : (True ∧ q) ↔ q := by rw [true_and]
theorem reduce_and_true (p : Prop) : (p ∧ True) ↔ p := by rw [and_true]

theorem reduce_and_congr (p p' q q' : Prop) (hp : p ↔ p') (hq : q ↔ q') : (p ∧ q) ↔ (p' ∧ q') :=
  and_congr hp hq
theorem reduce_and_congr_left (p p' q : Prop) (hp : p ↔ p') : (p ∧ q) ↔ (p' ∧ q) :=
  and_congr_left' hp
theorem reduce_and_congr_right (p q q' : Prop) (hq : q ↔ q') : (p ∧ q) ↔ (p ∧ q') :=
  and_congr_right' hq

theorem reduce_false_or (q : Prop) : (False ∨ q) ↔ q := by rw [false_or]
theorem reduce_or_false (p : Prop) : (p ∨ False) ↔ p := by rw [or_false]
theorem reduce_true_or (q : Prop) : (True ∨ q) ↔ True := by rw [true_or]
theorem reduce_or_true (p : Prop) : (p ∨ True) ↔ True := by rw [or_true]

theorem reduce_or_congr (p p' q q' : Prop) (hp : p ↔ p') (hq : q ↔ q') : (p ∨ q) ↔ (p' ∨ q') :=
  or_congr hp hq
theorem reduce_or_congr_left (p p' q : Prop) (hp : p ↔ p') : (p ∨ q) ↔ (p' ∨ q) :=
  or_congr_left hp
theorem reduce_or_congr_right (p q q' : Prop) (hq : q ↔ q') : (p ∨ q) ↔ (p ∨ q') :=
  or_congr_right hq

theorem reduce_not_false : ¬ False ↔ True := not_false_iff
theorem reduce_not_true : ¬ True ↔ False := not_true

theorem reduce_not_congr (p p' : Prop) (hp : p ↔ p') : ¬ p ↔ ¬ p' := not_congr hp

theorem reduce_imp (p q : Prop) : (p → q) ↔ (¬ p ∨ q) := by
  rw [Classical.or_iff_not_imp_left, Classical.not_not]

/--
Given a unary connective with constructor `mkCon` and the given congruence lemma,
produces a reduction result given reduction result of the argument.
-/
def mkCongr1 (mkCon : Expr → Expr) (congr : Name) (r : ReduceResult) : ReduceResult :=
  let e := mkCon r.e
  let e' := mkCon r.e'
  let pf? :=
    match r.pf? with
    | none => none
    | some pf => mkApp3 (mkConst congr) r.e r.e' pf
  { e, e', pf? }

/--
Given a binary connective with constructor `mkCon` and the given congruence lemmas,
produces a reduction result given reduction results of the left and right.
-/
def mkCongr2 (mkCon : Expr → Expr → Expr) (congrLeft congrRight congrBoth : Name) (rleft rright : ReduceResult) : ReduceResult :=
  let e := mkCon rleft.e rright.e
  let e' := mkCon rleft.e' rright.e'
  let pf? :=
    match rleft.pf?, rright.pf? with
    | none, none => none
    | some pf1, none => mkApp4 (mkConst congrLeft) rleft.e rleft.e' rright.e' pf1
    | none, some pf2 => mkApp4 (mkConst congrRight) rleft.e' rright.e rright.e' pf2
    | some pf1, some pf2 => mkApp6 (mkConst congrBoth) rleft.e rleft.e' rright.e rright.e' pf1 pf2
  { e, e', pf? }

def propVal? (p : Expr) : Option Bool :=
  if p.isConstOf ``True then some true
  else if p.isConstOf ``False then some false
  else none

def reduceAnd (p q : Expr) : ReduceResult :=
  let e := mkAnd p q
  match propVal? p, propVal? q with
  | some false, _ =>
    let pf := mkApp (mkConst ``reduce_false_and) q
    { e, e' := mkConst ``False, pf? := some pf }
  | some true, _ =>
    let pf := mkApp (mkConst ``reduce_true_and) q
    { e, e' := q, pf? := some pf }
  | _, some false =>
    let pf := mkApp (mkConst ``reduce_and_false) p
    { e, e' := mkConst ``False, pf? := some pf }
  | _, some true =>
    let pf := mkApp (mkConst ``reduce_and_true) p
    { e, e' := p, pf? := some pf }
  | _, _ =>
    ReduceResult.rfl e

def reduceOr (p q : Expr) : ReduceResult :=
  let e := mkOr p q
  match propVal? p, propVal? q with
  | some false, _ =>
    let pf := mkApp (mkConst ``reduce_false_or) q
    { e, e' := q, pf? := some pf }
  | some true, _ =>
    let pf := mkApp (mkConst ``reduce_true_or) q
    { e, e' := mkConst ``True, pf? := some pf }
  | _, some false =>
    let pf := mkApp (mkConst ``reduce_or_false) p
    { e, e' := p, pf? := some pf }
  | _, some true =>
    let pf := mkApp (mkConst ``reduce_or_true) p
    { e, e' := mkConst ``True, pf? := some pf }
  | _, _ =>
    ReduceResult.rfl e

def reduceNot (p : Expr) : ReduceResult :=
  let e := mkNot p
  match propVal? p with
  | some false =>
    let pf := mkConst ``reduce_not_false
    { e, e' := mkConst ``True, pf? := some pf }
  | some true =>
    let pf := mkConst ``reduce_not_true
    { e, e' := mkConst ``False, pf? := some pf }
  | _ =>
    ReduceResult.rfl e

/--
Reduces the proposition `e` given the current values of atoms.
-/
partial def reduceProp (e : Expr) : M ReduceResult := do
  -- Apply lambda calculus reductions and unfold reducible definitions.
  let e ← whnfR e
  if let some atom ← findAtomVal? e then
    -- This is an atom that we have chosen a value for.
    -- Reduces to `True`/`False`.
    return { e, e' := atom.expr, pf? := atom.iff }
  if e.isAppOfArity ``And 2 then
    let p ← reduceProp e.appFn!.appArg!
    let q ← reduceProp e.appArg!
    let r := mkCongr2 mkAnd ``reduce_and_congr_left ``reduce_and_congr_right ``reduce_and_congr p q
    r.check "reduceProp and"
    let r' := reduceAnd p.e' q.e'
    return ReduceResult.trans r r'
  else if e.isAppOfArity ``Or 2 then
    let p ← reduceProp e.appFn!.appArg!
    let q ← reduceProp e.appArg!
    let r := mkCongr2 mkOr ``reduce_or_congr_left ``reduce_or_congr_right ``reduce_or_congr p q
    r.check "reduceProp or"
    let r' := reduceOr p.e' q.e'
    return ReduceResult.trans r r'
  else if e.isAppOfArity ``Not 1 then
    let p ← reduceProp e.appArg!
    let r := mkCongr1 mkNot ``reduce_not_congr p
    r.check "reduceProp not"
    let r' := reduceNot p.e'
    return ReduceResult.trans r r'
  else if e.isArrow then
    -- Rather than have special rules for implication, let's do `(p → q) ↔ (¬ p ∨ q)
    let p := e.bindingDomain!
    let q := e.bindingBody!
    let pf := mkApp2 (mkConst ``reduce_imp) p q
    let r := { e, e' := mkOr (mkNot p) q, pf? := some pf }
    let r' ← reduceProp r.e'
    return ReduceResult.trans r r'
  else
    -- Reached an atom. No reductions available.
    return ReduceResult.rfl e

open Elab Term in
elab "#test_reduceProp " t:term : command => Command.runTermElabM fun _ => do
  let e ← withSynthesize <| Term.elabTermEnsuringType t (mkSort levelZero)
  let r ← reduceProp e |>.run {}
  logInfo m!"reduced (has proof = {r.pf?.isSome}):{indentExpr r.e'}"
  r.check "test"
  unless ← isDefEq r.e e do
    throwError "result starts from wrong type"

section
variable (p q : Prop)
#test_reduceProp True ∧ p
#test_reduceProp (True ∧ False) ∧ q
#test_reduceProp p ∧ True
#test_reduceProp False ∧ p
#test_reduceProp p ∧ False
#test_reduceProp (True ∧ p) ∧ (q ∧ True)
#test_reduceProp p → q
#test_reduceProp p → True
#test_reduceProp True → p
#test_reduceProp False → p
end

/--
Finds a "propositional atom" in `e`.
This is a term that we will treat like a propositional variable, like `p x`, when doing case splitting.

Assumes that `reduceProp` was already applied, which means that all the connectives are in whnf already,
and all `→` have been eliminated.
Since `reduceProp` was applied, this will give a *new* propositional atom.
-/
partial def extractAtom (e : Expr) : Expr :=
  if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 then
    -- Can go down the LHS since `e` is reduced.
    extractAtom e.appFn!.appArg!
  else if e.isAppOfArity ``Not 1 then
    extractAtom e.appArg!
  else
    e

/--
Given a propositional atom `p`, prove `q` by checking that it is true no matter the truth value of `p`.
-/
theorem case_split (p q q' : Prop) (htrue : p → (q ↔ q')) (hfalse : ¬ p → (q ↔ q')) : q ↔ q' :=
  Or.elim (Classical.em p) htrue hfalse

/--
Reduces a proposition to `True`, or otherwise throws an error.
Does case analysis on atoms.
-/
partial def reduceAndSplit (e : Expr) : M ReduceResult := do
  let r ← reduceProp e
  -- logInfo m!"reduceAndSplit:{indentExpr r.e'}"
  r.check "reduceAndSplit"
  match propVal? r.e' with
  | some true =>
    -- Reduced to true!
    return r
  | some false =>
    -- Reduced to false. Provably false, assuming the atoms are independent.
    let atoms := (← read).atomVals.map fun atom => indentD m!"{atom.val}: {atom.a}"
    let atomsMsg :=
      if atoms.isEmpty then
        m!""
      else
        m!" with the following assignments" ++ MessageData.joinSep atoms.reverse ""
    throwError "goal is provably false{atomsMsg}"
  | none =>
    -- Find an atom, do a case split, and recurse.
    let atom := extractAtom r.e'
    -- logInfo m!"splitting on atom{indentExpr atom}"
    let htrue ←
      withLocalDeclD `ht atom fun h =>
        withAtomVal { a := atom, val := true, pf := h } do
          let r' ← reduceAndSplit r.e'
          assert! (propVal? r'.e') == true
          mkLambdaFVars #[h] r'.pf
    let hfalse ←
      withLocalDeclD `hf (mkNot atom) fun h =>
        withAtomVal { a := atom, val := false, pf := h } do
          let r' ← reduceAndSplit r.e'
          assert! (propVal? r'.e') == true
          mkLambdaFVars #[h] r'.pf
    let pf := mkApp5 (mkConst ``case_split) atom r.e' (mkConst ``True) htrue hfalse
    return ReduceResult.trans r { e := r.e', e' := mkConst ``True, pf? := some pf }

open Elab Tactic

elab "prop" : tactic => do
  liftMetaFinishingTactic fun g => do
    let e ← g.getType
    let r ← reduceAndSplit e |>.run {}
    assert! r.e' == mkConst ``True
    g.assign <| mkApp4 (mkConst ``Iff.mpr) r.e r.e' r.pf (mkConst ``trivial)

end TacticImpl

example {p q : Prop} : p → (p ∨ q) := by
  prop

example {p q : Prop} : p → (q → p) := by
  prop

example {p q r : Prop} : (p → q) → (p → (q → r)) → (p → r) := by
  prop

/--
error: goal is provably false with the following assignments
  true: p
  false: q
-/
#guard_msgs in
example {p q : Prop} : p → q := by
  prop


/--
info: Try this: (case_split p (p ∨ ¬p) True
      (fun ht =>
        Iff.trans
          (reduce_or_congr p True (¬p) False (iff_true_intro ht)
            (Iff.trans (reduce_not_congr p True (iff_true_intro ht)) reduce_not_true))
          (reduce_true_or False))
      fun hf =>
      Iff.trans
        (reduce_or_congr p False (¬p) True (iff_false_intro hf)
          (Iff.trans (reduce_not_congr p False (iff_false_intro hf)) reduce_not_false))
        (reduce_false_or True)).mpr
  trivial
-/
#guard_msgs in
open TacticImpl in
example {p : Prop} : p ∨ ¬ p := by?
  prop

/--
info: Try this: (Iff.trans
      (Iff.trans (reduce_imp ((p → q) → p) p)
        (reduce_or_congr_left (¬((p → q) → p)) (¬(¬(¬p ∨ q) ∨ p)) p
          (reduce_not_congr ((p → q) → p) (¬(¬p ∨ q) ∨ p)
            (Iff.trans (reduce_imp (p → q) p)
              (reduce_or_congr_left (¬(p → q)) (¬(¬p ∨ q)) p (reduce_not_congr (p → q) (¬p ∨ q) (reduce_imp p q)))))))
      (case_split p (¬(¬(¬p ∨ q) ∨ p) ∨ p) True
        (fun ht =>
          Iff.trans
            (reduce_or_congr (¬(¬(¬p ∨ q) ∨ p)) False p True
              (Iff.trans
                (reduce_not_congr (¬(¬p ∨ q) ∨ p) True
                  (Iff.trans
                    (reduce_or_congr (¬(¬p ∨ q)) (¬q) p True
                      (reduce_not_congr (¬p ∨ q) q
                        (Iff.trans
                          (reduce_or_congr_left (¬p) False q
                            (Iff.trans (reduce_not_congr p True (iff_true_intro ht)) reduce_not_true))
                          (reduce_false_or q)))
                      (iff_true_intro ht))
                    (reduce_or_true ¬q)))
                reduce_not_true)
              (iff_true_intro ht))
            (reduce_false_or True))
        fun hf =>
        Iff.trans
          (reduce_or_congr (¬(¬(¬p ∨ q) ∨ p)) True p False
            (Iff.trans
              (reduce_not_congr (¬(¬p ∨ q) ∨ p) False
                (Iff.trans
                  (reduce_or_congr (¬(¬p ∨ q)) False p False
                    (Iff.trans
                      (reduce_not_congr (¬p ∨ q) True
                        (Iff.trans
                          (reduce_or_congr_left (¬p) True q
                            (Iff.trans (reduce_not_congr p False (iff_false_intro hf)) reduce_not_false))
                          (reduce_true_or q)))
                      reduce_not_true)
                    (iff_false_intro hf))
                  (reduce_false_or False)))
              reduce_not_false)
            (iff_false_intro hf))
          (reduce_true_or False))).mpr
  trivial
-/
#guard_msgs in
open TacticImpl in
-- Peirce's law
example {p q : Prop} : ((p → q) → p) → p := by?
  prop
