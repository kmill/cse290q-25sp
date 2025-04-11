import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!
# Inductive types
-/

/-!
Recall: for `Day3/Types.lean` we saw the basic types that dependent type
theory (DTT) promises.
- type universes (`Prop` and `Type _`; generalized with `Sort _`); and
- pi/function types (`α → β` for non-dependent, `(x : α) → β x` for dependent)

We also saw the basic expressions in DTT.
- expressions for the above types
- applications
- lambda expressions (`fun x => b`)
- let expressions (`let x := v; b`)
- constants (references to declarations in the environment)

Also, we saw the three fundamental judgments:
- that a term is well-typed (is "type-correct").
- that two expressions are definitionally equal.
- that a given term is the inferred type of another. (`x : T`)
These definitions are mutually recursive.

(Terminology note: "term" and "expression" appear to be interchangeable.
We talk about the "terms of a type" rather than "elements of a type",
but it seems people mean "terms of a type" up to definitional equality.)
-/

/-!
One cannot subsist on function types and universes alone.

## How do we introduce new types?

So-called "inductive types" are a large class of types.
The Calculus of Inductive Constructions (CIC) is the type theory used by Lean,
and it controls which inductive types are allowed.

`inductive` is a command that invokes an axiom with:

- Input. Valid inductive type definition.
- Output.
  1. type constructor (e.g. `List : Type u -> Type u`)
  2. constructors (e.g. `List.cons {α : Type u} : α → List α → List α`)
  3. recursor/eliminator (e.g. `List.rec`)

Additionally, there are computation rules for the recursor,
in the form of definitional equalities that hold
(e.g. `List.rec n c List.nil =?= n`
and `List.rec n c (List.cons x xs) =?= c x xs (List.rec n c xs)`).

Recalling `Day2/Deduction.lean`, the constructors correspond to the
introduction rules, and the recursor corresponds to the elimination rule.

Note: There are also a number of auxiliary definitions that the Lean elaborator
generates to support features such as recursive definition elaboration.
-/

/-!
## Syntax
-/

/-!
Basic version:
```
inductive IndType : Type u where
  | ctor₁ (field₁₁ : Ty₁₁) ⋯ (field₁ₖ₁ : Ty₁ₖ₁) : IndType
  | ctor₂ (field₂₁ : Ty₂₁) ⋯ (field₂ₖ₁ : Ty₂ₖ₂) : IndType
  ⋮
```
The "resultant type" `Type u` is optional and can generally be inferred.
In each constructor, the `IndType` is optional and can be inferred.
-/

/-!
*Parameterized* inductive types.
```
inductive IndType (α₁ : Param₁) ⋯ (αₘ : Paramₘ) : Type u where
  | ctor₁ (field₁₁ : Ty₁₁) ⋯ (field₁ₖ₁ : Ty₁ₖ₁) : IndType α₁ ⋯ αₘ
  | ctor₂ (field₂₁ : Ty₂₁) ⋯ (field₂ₖ₁ : Ty₂ₖ₁) : IndType α₁ ⋯ αₘ
  ⋮
```
The *parameters* `α₁`, …, `αₘ` are fixed across all constructors.
Think about this as being a separate inductive type for each assignment
of the parameters.
-/

/-!
*Indexed* inductive types.
```
inductive IndType (α₁ : Param₁) ⋯ (αₘ : Paramₘ) :
    Index₁ → ⋯ → Indexₙ → Type u where
  | ctor₁ (field₁₁ : Ty₁₁) ⋯ (field₁ₖ₁ : Ty₁ₖ₁) : IndType α₁ ⋯ αₘ i₁₁ ⋯ i₁ₙ
  | ctor₂ (field₂₁ : Ty₂₁) ⋯ (field₂ₖ₁ : Ty₂ₖ₁) : IndType α₁ ⋯ αₘ i₂₁ ⋯ i₂ₙ
  ⋮
```
The *indices* can vary across constructors.
This should be thought of as a mutually defined family of inductive types.
(Note: Lean will *promote* indices to parameters if they are constant across
all constructors.)

Let's look at examples.
-/


/-!
An *enumeration* type.
-/
inductive Primary where
  | red
  | green
  | blue

-- The Lean->C compiler doesn't currently support direct use of
-- recursors. This command, defined in Mathlib.Util.CompileInductive,
-- sets up a workaround.
compile_inductive% Primary

#check Primary
#check Primary.red
#check Primary.green
#check Primary.blue
#check Primary.rec

def Primary.isRed (p : Primary) : Bool :=
  match p with
  | .red => true
  | _    => false
  -- p matches .red

#eval Primary.isRed Primary.red
#eval Primary.isRed Primary.blue

/-
Primary.rec.{u}
  {motive : Primary → Sort u}
  (red : motive Primary.red)
  (green : motive Primary.green)
  (blue : motive Primary.blue)
  (t : Primary)
  : motive t
-/

def Primary.isRed' (p : Primary) : Bool :=
  Primary.rec
    (motive := fun _ => Bool)    -- motive
    (red := true)                -- \
    (green := false)             --  | minor premises
    (blue := false)              -- /
    p                            -- major premise

/-!
What is this complexity with the "motive"?
It's to support dependent types. The type of the result can depend on the
major premise.

Think of it as *the return type with a hole*.

Example:
-/
def BoolIfRed (p : Primary) : Type :=
  match p with
  | .red => Bool
  | _    => Unit

#reduce (types := true) BoolIfRed .red
#reduce (types := true) BoolIfRed .green

def Primary.trueIfRed (p : Primary) : BoolIfRed p :=
  Primary.rec
    (motive := fun p' => BoolIfRed p')
    (red := true)
    (green := ())
    (blue := ())
    p

#eval Primary.trueIfRed .red
#eval Primary.trueIfRed .green
#eval Primary.trueIfRed .blue

/-!
A *recursive* type
-/

inductive MyNat : Type where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

compile_inductive% MyNat

def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n' => .succ (add m n')

#check MyNat.rec
/-
MyNat.rec.{u}
  {motive : MyNat → Sort u}
  (zero : motive MyNat.zero)
  (succ : (n : MyNat) → motive n → motive n.succ)
  (t : MyNat)
  : motive t
-/

def MyNat.add' (m n : MyNat) : MyNat :=
  MyNat.rec
    (motive := fun _ => MyNat)
    (zero := m)
    (succ := fun _n' res => .succ res)
    n

#eval MyNat.add' MyNat.zero.succ.succ MyNat.zero.succ.succ

/-!
A *reflexive* type
-/

inductive Tree : Type where
  | leaf : Tree
  | node (f : Bool → Tree) : Tree

compile_inductive% Tree

-- equivalent to
inductive Tree' : Type where
  | leaf : Tree'
  | node (a b : Tree') : Tree'
-- but with a different recursor

#check Tree.rec
/-
Tree.rec.{u}
  {motive : Tree → Sort u}
  (leaf : motive Tree.leaf)
  (node : (f : Bool → Tree) → ((a : Bool) → motive (f a)) → motive (Tree.node f))
  (t : Tree)
  : motive t
-/

def Tree.numLeaves : Tree → Nat
  | .leaf => 1
  | .node f => numLeaves (f false) + numLeaves (f true)

def Tree.numLeaves' (t : Tree) : Nat :=
  Tree.rec
    (motive := fun _ => Nat)
    (leaf := 1)
    (node := fun _f ress => ress false + ress true)
    t

/-!
A parameterized type.
-/

inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons (x : α) (xs : MyList α) : MyList α

#check MyList.rec
/-
MyList.rec.{u_1, u} {α : Type u}
  {motive : MyList α → Sort u_1}
  (nil : motive MyList.nil)
  (cons : (x : α) → (xs : MyList α) → motive xs → motive (MyList.cons x xs))
  (t : MyList α)
  : motive t
-/

/-!
An indexed type.
-/

inductive MyVect (α : Type u) : Nat → Type u where
  | nil : MyVect α 0
  | cons (x : α) {n : ℕ} (xs : MyVect α n) : MyVect α (n + 1)

#check MyVect.cons 100 (MyVect.cons 200 MyVect.nil)

#check MyVect.rec
/-
MyVect.rec.{u_1, u} {α : Type u}
  {motive : (a : ℕ) → MyVect α a → Sort u_1}
  (nil : motive 0 MyVect.nil)
  (cons : (x : α) → {n : ℕ} → (xs : MyVect α n) → motive n xs →
            motive (n + 1) (MyVect.cons x xs))
  {a✝ : ℕ}
  (t : MyVect α a✝)
  : motive a✝ t
-/

/-!
## Positive occurrences

While inductive types can have recursive definitions, there are limitations.
The limitations are conservative.
-/

inductive Bad : Type
  | mk (f : Bad → Empty) : Bad

inductive NotSoBad : Type
  | nil : NotSoBad
  | mk (f : NotSoBad → Empty) : NotSoBad
