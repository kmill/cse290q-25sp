import Lean
/-!
# Basics of dependent type theory
-/

/-!
There are three fundamental judgments:

1. that term `x` is well-typed

2. `x ≟ y`
that **`x` is definitionally equal to `y`**.
This means that `x` and `y` are equivalent modulo the theory's conversion rules.

3. `x : T`
that **term `x` has type `T`**.
There is an algorithm to *infer* the type `T` of `x`.
It's not possible for non-equal types to have the same term.

(What's a **type**? Anything that can appear on the right-hand side of `:`.)

These three notions are mutually recursive.

There is a mathematically ideal definition of these,
but in Lean there are imperfect (conservative) algorithms.
For example, `≟`-the-algorithm is not transitive.
-/

#check (true)
#check (true : Bool)
#check (true : id Bool)
#check (true : Nat)

/-!
*Every* term has a type.

While `true : Bool`,
we have `Bool : Type`.

The type `Type` is known as a **universe**.
(Rule: anything that is the type of the type of a term is a universe.)

Note: in some type theories, one doesn't use `:` for this, but a separate judgment,
(maybe `Bool in universe Type`).
Lean elects to unify the concepts for convenience.

What is the type of `Type`?
-/
#check Type
/-
It's `Type 1`, a higher universe.

There is an infinite chain of higher universes, to make sure that *every* term has a type.
```
Type : Type 1 : Type 2 : Type 3 : …
```
It is tempting to have `Type : Type`, but "type-in-type" leads to Girard's paradox.

Terminology from Automath:

degree 0: universes      Type         Type 1
degree 1: types          Bool         Nat → Type
degree 2: terms          true         Fin
-/
#check (Fin)
#check type_of% Fin

/-!
## "Pi" types (function types)

Given a type `T` and a term `Sₓ` with a free variable `x`,
   `(x : T) → Sₓ`
is a type, provided that `Sₓ` is well-typed and `Sₓ` is a type.

If `T : Type u` and `Sₓ : Type v`, then
   `(x : T) → Sₓ  :  Type (max u v)`


Now, suppose that `φₓ : Sₓ` is a term with a free variable `x`.
Then the **lambda term**
   `fun (x : T) => φₓ`
is a term whose type is `(x : T) → Sₓ`.

Given a term `S` without a free variable, then `T → S`
is short for `(x : T) → S`.
-/

#check (n : Nat) → Fin (n + 1)

#check fun (n : Nat) => n + 2

#check (n : Nat) → (m : Fin n) → Fin (n + 1)
#check @Fin.succ

/-!
While pi types and lambda terms look similar, they have some fundamental differences:

- the type of a pi type is a universe (it's degree 1), but
  the type of a lambda term is a pi type (it's degree 2)
- one can apply lambda terms to arguments, but
  one cannot apply pi types to arguments
-/


/-!
## Application

Given `f : (x : T) → Sₓ` and `t : T`, then `f t : Sₜ`.

If `f` is `fun (x : T) => φₓ`, then
  `f t ≟ φₜ`
This is **beta reduction** (one of the conversion rules).
-/

#reduce (fun a : Bool => fun b : Bool => a) true false

example : ((fun a : Bool => fun b : Bool => a) true false) = true := rfl

/-
Another conversion, **eta reduction**:
  `(fun x => f x) ≟ f`
-/

example (f : α → β) : (fun x => f x) = f := rfl

/-!
## Let expressions

Given `Sₓ` and `φₓ` like before, given `t : T`, then
  `let x : T := t; φₓ`
is a term of type `Sₜ`.

**Zeta reduction** is that
  `let x : T := t; φₓ  ≟  φₜ`

This is similar to `(fun (x : T) => φₓ) t`, but a let expression
is well-typed if `φₜ` is well-typed. The expression `φₓ` need not be well-typed!
-/
#check let x : Nat := 3; x + x
#check let x : Nat := 3; (1 : Fin x)
#check (fun (x : Nat) => (1 : Fin x)) 3


/-!
## Definitions

There is an *environment* of definitions.
Each definition can only refer to definitions previously made.
Creating a definition creates a *constant* that one may refer to.
-/
def myId (α : Type) (x : α) : α := x

/-!
Definition can be *universe polymorphic*
-/
def myId' (α : Type u) (x : α) : α := x
#check myId'
set_option pp.universes true in
#check myId' _ Bool

/-!
Replacing a constant with its definition is **delta reduction**.
(For recursive definitions, Lean has some special support to try to keep delta reduction under control,
so-called "smart unfolding".)
-/


/-!
## Inductive types

This is a whole complicated subject.

The basic form is that if you write
```
inductive I (... parameters ...) : Type u where
  | c₁ (... fields ...) : I (... same parameters ...)
  ...
  | cₙ (... fields ...) : I (... same parameters ...)
```
then `I (... parameters ...)` is a type in `Type u` that is, basically,
the least set that is closed under the constructors.
The fields of constructors can refer to `I` in some restricted ways ("positivity checking")

One gets:
- The type constructor `I`,
- the constructors `I.c₁`, ..., `I.cₙ`, and
- the recursor/eliminator `I.rec`.

Lean also goes ahead and defines a host of supporting auxiliary definitions that make use of these.
-/

inductive MyNat : Type where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

#check MyNat.rec

/-!
# Propositions
-/

#check Prop
-- Prop = Sort 0
-- Type = Type 0 = Sort 1
-- Type u = Sort (u + 1)

#check Type → Nat
#check Type 31 → True -- impredicativity
#check True → Type 31

#check True
#check False
#check 3 = 4

example : (3 = 4) = False := by
  apply propext
  constructor
  · intro h
    cases h
  · intro h
    cases h

set_option pp.proofs true
#check Eq.rec

example (x y : Nat) (h : x = y) (hy : y = 2) :
    x = 2 := by
  refine Eq.rec (motive := fun (a : Nat) _ => a = 2) ?_ h.symm
  dsimp only
  exact hy
