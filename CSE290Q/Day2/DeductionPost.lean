import Mathlib.Tactic
-- post-lecture
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

  -------------------- hyp
    Γ, h : p ⊢ h : p
-/

example (h : p) : p := h
example (h : p) : p := by exact h
example (h : p) : p := by assumption


/-!
## Conjunction introduction

    Γ ⊢ hp : p   Γ ⊢ hq : q
  --------------------------- ∧I
     Γ ⊢ ⟨hp, hq⟩ : p ∧ q
-/

example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
example (hp : p) (hq : q) : p ∧ q := by
  constructor
  · assumption
  · assumption
example (hp : p) (hq : q) : p ∧ q := by
  refine And.intro ?firstProof ?secondProof
  case secondProof =>
    exact hq
  · assumption

/-!
## True introduction

----------------- ⊤I
  Γ ⊢ ⟨⟩ : True
-/

example : True := ⟨⟩
example : True := True.intro
example : True := by trivial
example : True := by constructor


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
example (hp : p) : p ∨ q := Or.inl hp
example (hq : q) : p ∨ q := Or.inr hq
example (hp : p) : p ∨ q := by
  left
  exact hp
example (hq : q) : p ∨ q := by
  right
  trivial
example (hp : p) : p ∨ q := by
  apply Or.inl
  exact hp
example (hp : p) : p ∨ q := by
  refine Or.inl ?_
  exact hp


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

example : p → q := by
  intro hp
  sorry

example : p → q := by
  refine fun (hp : p) => ?_
  sorry


/-!
## Universal introduction

Let `p` denote a predicate with domain `α`.
We write `p x` instead of `p(x)`.
Similarly, `hp x` represents the dependence of `hp` on `x`.

           Γ, x : α ⊢ hp x : p x
  ----------------------------------------- ∀I
    Γ ⊢ (λ (x : α) ↦ hp x) : ∀ x : α, p x

We encode predicates as functions `p : α → Prop`.
-/

example (p : α → Prop) (hp : (x : α) → p x) : ∀ (x : α), p x := fun (x : α) => hp x
-- At `hp x`, we see that the local context is
--   x : α
--   ⊢ p x
-- which matches what's above the line for →I

example (p : α → Prop) (hp : (x : α) → p x) : ∀ (x : α), p x := by
  intro y
  sorry

example (p : α → Prop) (hp : (x : α) → p x) : ∀ (x : α), p x := by
  refine fun (y : α) => ?_
  sorry


/-!
## Existential introduction

Let `p` denote a predicate with domain `α`.

     Γ ⊢ t : α   Γ ⊢ hp : p t
  ------------------------------ ∃I
    Γ ⊢ ⟨t, hp⟩ : ∃ x : α, p x
-/

example (p : α → Prop) (t : α) (hp : p t) : ∃ x : α, p x := ⟨t, hp⟩
example (p : α → Prop) (t : α) (hp : p t) : ∃ x : α, p x := Exists.intro t hp
example (p : α → Prop) (t : α) (hp : p t) : ∃ x : α, p x := by
  use t
example (p : α → Prop) (t : α) (hp : p t) : ∃ x : α, p x := by
  refine Exists.intro t ?_
  exact hp

section
local macro_rules | `(tactic|trivial) => `(tactic| apply Exists.intro <;> trivial)
example (p : α → Prop) (t : α) (hp : p t) : ∃ x : α, p x := by
  trivial
end

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
example (h : p ∧ q) : p := h.left
example (h : p ∧ q) : q := h.right
example (h : p ∧ q) : p := by
  cases h
  assumption
example (h : p ∧ q) : p := by
  obtain ⟨hp, hq⟩ := h
  exact hp
example (h : p ∧ q) : q := h.right


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

example (h : p ∨ q) (hp : p → r) (hq : q → r) : r := by
  cases h
  · apply hp
    assumption
  · apply hq
    assumption
example (h : p ∨ q) (hp : p → r) (hq : q → r) : r := by
  obtain h1 | h2 := h
  all_goals tauto

/-!
## False elimination (exfalso, "principal of explosion")

        Γ ⊢ h : False
  ------------------------ ⊥E
    Γ ⊢ False.elim h : p
-/

example (h : False) : p := False.elim h
example (h : False) : p := by cases h
example : False → p := nofun


/-!
## Implication elimination (modus ponens)

    Γ ⊢ h : p → q   Γ ⊢ hp : p
  ------------------------------ →E
            Γ ⊢ h hp : q
-/

example (h : p → q) (hp : p) : q := h hp
example (h : p → q) (hp : p) : q := by
  apply h
  exact hp


/-!
## Universal elimination

    Γ ⊢ h : ∀ x : α, p x   Γ ⊢ t : α
  ------------------------------------ ∀E
            Γ ⊢ h t : p t
-/

example (p : α → Prop) (h : ∀ x : α, p x) (t : α) : p t := h t

example (p : α → Prop) (h : ∀ x : α, p x) (t : α) : p t := by
  apply h

/-!
## Existential elimination

  Γ ⊢ h : ∃ x, p x   Γ, x : α, hp : p x ⊢ hq : q
-------------------------------------------------- ∃E
          Γ ⊢ (let ⟨x, hp⟩ := h; hq) : q
-/

example (p : α → Prop) (h : ∃ x, p x) (hq : (x : α) → (hp : p x) → q) : q :=
  let ⟨x, hp⟩ := h
  hq x hp

example (p : α → Prop) (h : ∃ x, p x) (hq : (x : α) → (hp : p x) → q) : q := by
  obtain ⟨x, hp⟩ := h
  exact hq x hp
