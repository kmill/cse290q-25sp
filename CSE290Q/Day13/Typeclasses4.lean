import Lean
/-!
# A mini theorem prover using typeclasses
-/

class Provable (p : Prop) : Prop where
  proof : p

class Disprovable (p : Prop) : Prop where
  disproof : ¬ p

export Provable (proof)
export Disprovable (disproof)

variable {p q : Prop} {α : Sort u} {φ ψ : α → Prop}

instance : Provable True where

instance : Disprovable False where

instance [Disprovable p] : Provable (¬ p) where

instance [Provable p] : Disprovable (¬ p) where

instance [Provable p] [Provable q] : Provable (p ∧ q) where

instance [Provable p] : Provable (p ∨ q) where

instance [Provable q] : Provable (p ∨ q) where

instance [Provable q] : Provable (p → q) where

instance [Disprovable p] : Provable (p → q) where

instance [∀ x, Provable (φ x)] : Provable (∀ x, φ x) where

instance [Disprovable (∀ x, ¬ φ x)] : Provable (∃ x, φ x) where

-- Case splitting
instance (priority := low) {φ : Prop → Prop} [Provable (φ True)] [Provable (φ False)] :
    Provable (∀ (p : Prop), φ p) where

instance (priority := low) {φ : Prop → Prop} [Disprovable (φ True)] :
    Disprovable (∀ (p : Prop), φ p) where

instance (priority := low) {φ : Prop → Prop} [Disprovable (φ False)] :
    Disprovable (∀ (p : Prop), φ p) where

/-
## Tactic to get things set up
-/

namespace ProveTactic

open Lean Meta Elab Tactic

/--
The `prove` tactic cleans up the local context, reverts all variables,
and then tries to prove the goal using `Provable.proof`.
-/
elab "prove" : tactic => do
  liftMetaFinishingTactic fun g => do
    let g ← g.cleanup
    let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) (← g.getDecl).lctx.getFVarIds
    let goalType ← g.getType
    let pf ← mkAppOptM ``proof #[goalType, none]
    g.assign pf

end ProveTactic

/-
## Examples
-/

example {p : Prop} : p → p := by
  prove

example {p q : Prop} : p → (q → p) := by
  prove

-- fails
example {p q r : Prop} : (p → q) → (p → (q → r)) → (p → r) := by
  prove
