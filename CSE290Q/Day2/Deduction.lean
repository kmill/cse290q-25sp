import Mathlib.Tactic

/-!
# Natural deduction

First-order logic consists of
- propositional logic (with ¬, ∧, ∨, →, ↔, True, and False),
- quantifiers (∀, ∃), and
- propositional and predicate variables

Let's go through the rules of inference for
[natural deduction](https://en.wikipedia.org/wiki/Natural_deduction)
and see their equivalents in Lean.
Natural deduction is a proof theory for first-order logic that takes
a natural *constructive* interpretation of each logical connective.

In the following, `Γ` stands for a set/list of hypotheses and `p` a proposition

  Γ ⊢ p

It is the *judgement* that `p` is a (syntactic) consequence of `Γ`.
(The `⊨` symbol is used for semantic consequence, not used in Lean.)

This is a horizontal rendering of the Lean Infoview

We will use Gentzen-style notation for the rules:

    Γ₁ ⊢ p₁   Γ₂ ⊢ p₂  ...  Γₙ ⊢ pₙ
  ---------------------------------- rulename
               Γ ⊢ p

This means that, given all the judgements above the line hold,
then so does the judgement below the line.

This is short for

    Γ₁ ⊢ h₁ : p₁   Γ₂ ⊢ h₂ : p₂  ...  Γₙ ⊢ hₙ : pₙ
  ------------------------------------------------- rulename
               Γ ⊢ h : p

where we give names to the evidence that the propositions are true.

-/

variable (p q r : Prop) (α : Type)


/-!
## Assumption

  ------------ hyp
    Γ, h : p ⊢ h : p
-/

example (h : p) : p := h


/-!
## Conjunction introduction

    Γ ⊢ hp : p   Γ ⊢ hq : q
  --------------------------- ∧I
     Γ ⊢ ⟨hp, hq⟩ : p ∧ q
-/

example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩


/-!
## True introduction

----------------- ⊤I
  Γ ⊢ ⟨⟩ : True
-/

example : True := ⟨⟩


/-!
## Disjunction introduction

        Γ ⊢ hp : p
  ---------------------- ∨I₁
    Γ ⊢ inl hp : p ∨ q

        Γ ⊢ hq : q
  ---------------------- ∨I₂
    Γ ⊢ inr hq : p ∨ q
-/

example (hp : p) : p ∨ q := .inl hp
example (hq : q) : p ∨ q := .inr hq


/-!
## Implication introduction
Sometimes the "deduction theorem".

        Γ, hp : p ⊢ hq : q
  --------------------------------- →I
    Γ ⊢ (λ (hp : p) ↦ hq) : p → q
-/

-- This one is harder to illustrate.
example : p → q := fun (hp : p) => sorry
-- At the `sorry`, we see that the local context is
--   hp : p
--   ⊢ q
-- which matches what's above the line for →I

-- More accurate, though weird-looking and seemingly tautological.
-- `hq` represents the dependence on `hp`.
example (hq : p → q) : p → q := fun (hp : p) => hq hp

/-!
## Universal introduction

Let `p` denote a predicate with domain `α`.
We write `p x` instead of `p(x)`.
Similarly, `hp x` represents the dependence of `hp` on `x`.

           Γ, x : α ⊢ hp x : p x
  ------------------------------------- ∀I
    Γ ⊢ (λ (x : α) ↦ hp) : ∀ x : α, p x

We encode predicates as functions `p : α → Prop`.
-/

example (p : α → Prop) (hp : (x : α) → p x) : ∀ x : α, p x := fun (x : α) => hp x
-- At `hp x`, we see that the local context is
--   x : α
--   ⊢ p x
-- which matches what's above the line for →I

/-!
## Existential introduction

Let `p` denote a predicate with domain `α`.

     Γ ⊢ t : α   Γ ⊢ hp : p t
  ------------------------------ ∃I
    Γ ⊢ ⟨t, hp⟩ : ∃ x : α, p x
-/

example (p : α → Prop) (t : α) (hp : p t) : ∃ x : α, p x := ⟨t, hp⟩


/-!
## Conjunction elimination

    Γ ⊢ h : p ∧ q
  ----------------- ∧I₁
     Γ ⊢ h.1 : p

    Γ ⊢ h : p ∧ q
  ----------------- ∧I₂
     Γ ⊢ h.2 : q
-/

example (h : p ∧ q) : p := h.1
example (h : p ∧ q) : q := h.2


/-!
## Disjunction elimination

    Γ ⊢ h : p ∨ q   Γ, hp : p ⊢ hc₁ : r   Γ, hq : q ⊢ hc₂ : r
  ------------------------------------------------------------- ∨E
      Γ ⊢ (match h with | inl hp => hc₁ | inr hq => hc₂) : r
-/

-- Not an exact rendering, since `→I` is automatic in Lean.
example (h : p ∨ q) (hp : p → r) (hq : q → r) : r :=
  Or.elim h hp hq

-- Using the underlying eliminator from the `inductive` command:
example (h : p ∨ q) (hp : p → r) (hq : q → r) : r :=
  Or.recOn h hp hq


/-!
## False elimination (exfalso, "principal of explosion")

        Γ ⊢ h : False
  ------------------------ ⊥E
    Γ ⊢ False.elim h : p
-/

example (h : False) : p := False.elim h


/-!
## Implication elimination (modus ponens)

    Γ ⊢ h : p → q   Γ ⊢ hp : p
  ------------------------------ →E
            Γ ⊢ h hp : q
-/

example (h : p → q) (hp : p) : q := h hp


/-!
## Universal elimination

    Γ ⊢ h : ∀ x : α, p x   Γ ⊢ t : α
  ------------------------------------ ∀E
            Γ ⊢ h t : p t
-/

example (p : α → Prop) (h : ∀ x : α, p x) (t : α) : p t := h t


/-!
## Existential introduction

  Γ ⊢ h : ∃ x, p x   Γ, x : α, hp : p x ⊢ hq : q
-------------------------------------------------- ∃E
          Γ ⊢ (let ⟨x, hp⟩ := h; hq) : q
-/

example (p : α → Prop) (h : ∃ x, p x) (hq : (x : α) → (hp : p x) → q) : q :=
  let ⟨x, hp⟩ := h
  hq x hp
