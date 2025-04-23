import Mathlib.Tactic.Common
/-!
# Unification & metavariables
-/

/-!

The elaborator uses *metavariables* to represent expressions that
have not been solved for yet.

They are used by the elaborator for many processes:
- the initial value for an implicit argument
- a placeholder when an elaborator postpones itself
- a placeholder for an instance argument,
  until instance synthesis is done
- a placeholder for an unresolved coercion
- a placeholder for an unevaluated tactic script

The Lean kernel does not know about metavariables.
A "fully elaborated expression" is an expression with no metavariables.

Terminology:
- The *metacontext* contains a table of all metavariables
  and and, optionally, their values if they've been assigned.
- *Instantiating* metavariables in an expression means to replace
  each assigned metavariable with its value.
  (Note: assigning a metavariable does not immediately replace the metavariable
  in all expressions. Lean's data structures are *immutable*, so we
  need to manually instantiate.)
- A metavariable can be *natural*, *synthetic*, or *synthetic opaque*.
  These affect unification.
  "Synthetic" metavariables are used for metavariables that the elaborator
  will try to solve for.
  "Synthetic opaque" metavariables are used for metavariables that the *user*
  will try to solve for (via tactics). The elaborator will not solve for these.

-/

/-!
Manually creating metavariables
- `_` is a hole. It elaborates to a natural metavariable.
  You expect Lean to be able to solve for it.
- `?_` and `?A` are placeholders. They create synthetic opaque metavariables.
  In tactic mode, they generally create new goals.
-/

open Lean Meta Elab Command Term

elab tk:"#mycheck " t:term : command => runTermElabM fun _ => do
  let e ← withSynthesize (postpone := .partial) <| elabTerm t none
  unless e.hasSyntheticSorry do
    check e
    let ty ← inferType e
    logInfoAt tk m!"{e} : {ty}"

#mycheck _
#mycheck ?_
#mycheck Type _

#mycheck id true
#mycheck @id _ true
#mycheck @id Bool true

#mycheck (rfl : 1 + _ = _ + 2)
