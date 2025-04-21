import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!
# Inductive types part 2
-/

/-!
Last time we were looking at inductive types. The `inductive` command
introduces
- the type constructor (e.g. `List`),
- the constructors (e.g. `List.nil` and `List.cons`), and
- the recursor (e.g. `List.rec`)
-/

--  Type constructor                      resultant universe
--        |       parameter       index       |
--        ~~~~~~  ~~~~~~~~~~     ~~~~~~~    ~~~~~~
inductive MyVect (α : Type u) : (n : Nat) → Type u where
--  constructor
--  ~~~
  | nil : MyVect α 0
--  constructor
--  ~~~~
  | cons (x : α) {n : ℕ} (xs : MyVect α n) : MyVect α (n + 1)
--       ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--                   fields

/-!
In the constructors, the type's parameters always come in order
before the constructor's fields.
Indices are expressed in terms of parameters and fields.
-/
#check MyVect.nil
/-
MyVect.nil.{u} {α : Type u} : MyVect.{u} α 0
-/
#check MyVect.cons
/-
MyVect.cons.{u} {α : Type u} (x : α) {n : ℕ} (xs : MyVect.{u} α n) :
  MyVect.{u} α (n + 1)
-/
-- ex:
#check MyVect.cons (α := Int) 100 (MyVect.cons 200 MyVect.nil)

#check MyVect.rec
/-
MyVect.rec.{v, u} {α : Type u}
  {motive : (a : Nat) → MyVect.{u} α a → Sort v}
  (nil : motive 0 MyVect.nil.{u})
  (cons : (x : α) → {n : Nat} → (xs : MyVect.{u} α n) →
    motive n xs → motive (n + 1) (MyVect.cons.{u} x xs))
  {n : Nat} (t : MyVect.{u} α n) : motive n t
-/

compile_inductive% MyVect

/-!
## Exercises
-/

-- use `match`
def MyVect.isNil {α : Type u} {n : Nat} (v : MyVect α n) : Bool :=
  match v with
  | MyVect.nil => true
  | MyVect.cons _ _ => false

-- use `MyVect.rec`
def MyVect.isNil' {α : Type u} {n : Nat} (v : MyVect α n) : Bool :=
  MyVect.rec
    (motive := fun _ _ => Bool)
    (nil := true)
    (cons := fun _ _ _ _ => false)
    v

-- use `match`
def MyVect.append {α : Type u} {m n : Nat}
    (w : MyVect α m) (v : MyVect α n) : MyVect α (n + m) :=
  match w with
  | .nil => v
  | .cons x xs => .cons x (xs.append v)

-- use `match`
def MyVect.append' {α : Type u} {m n : Nat}
    (w : MyVect α m) (v : MyVect α n) : MyVect α (n + m) :=
  MyVect.rec
    (motive := fun m' _ => MyVect α (n + m'))
    (nil := v)
    (cons := fun x _ _ res => .cons x res)
    w

def MyVect.cast {α : Type u} {m m' : Nat} (v : MyVect α m) (h : m = m') : MyVect α m' :=
  match h with
  | Eq.refl _ => v

-- With flipped addition
def MyVect.append'' {α : Type u} {m n : Nat}
    (w : MyVect α m) (v : MyVect α n) : MyVect α (m + n) :=
  match w with
  | .nil => v.cast (by omega)
  | .cons x xs => (MyVect.cons x (xs.append'' v)).cast (by omega)

def MyVect.append''' {α : Type u} {m n : Nat}
    (w : MyVect α m) (v : MyVect α n) : MyVect α (m + n) :=
  MyVect.recOn w
    (motive := fun m' w' => MyVect α (m' + n))
    (nil := v.cast (by omega))
    (cons := fun x m' xs r => (MyVect.cons x r).cast (by omega))


/-!
## Prop inductives

The inductive command lets us define new propositions as well.
-/

inductive IsEven : Nat → Prop where
  | zero : IsEven 0
  | add_two (n : Nat) : IsEven (n + 2)

theorem IsEven.two : IsEven 2 := by
  sorry

theorem isEven_iff_exists (n : Nat) : IsEven n ↔ ∃ k, n = 2 * k := by
  sorry

#print Exists

/-!
Equality is not built into the system. It's simply an inductive type.
-/
inductive MyEq {α : Sort u} (a : α) : α → Prop where
  | refl : MyEq a a

#check Eq
/-!
Note: `Eq` does have a couple of special properties.
-/
#check propext
#check Quot.lift
#check Quot.sound


/-!
### Large elimination

Generally, inductive propositions have "small elimination".
This means the motive is `Prop`-valued.
-/
#check Exists.rec
/-
Exists.rec.{u} {α : Sort u} {p : α → Prop} {motive : Exists p → Prop} ⋯
-/
#check IsEven.rec
/-
IsEven.rec {motive : (a : ℕ) → IsEven a → Prop} ⋯
-/
/-!
The reason for this is *proof irrelevance*:

  Given two proofs `h h' : p` of a proposition `p`,
  then `h =?= h'` by definition.

This is very convenient.

However, consider the following:
-/
theorem exists1 : ∃ n : ℕ, n > 0 := Exists.intro 1 (by simp)
theorem exists2 : ∃ n : ℕ, n > 0 := Exists.intro 2 (by simp)
/-!
We have two proofs of `∃ n : ℕ, n > 0`. By proof irrelevance,
the proofs are equal:
-/
theorem exists1_eq_exists2 : exists1 = exists2 := rfl
/-!
Let's suppose we had a recursor for `Exists` with large elimination.
-/
axiom Exists.badRec {α : Sort u} {p : α → Prop}
    {motive : Exists p → Sort v} -- <- now `Sort v` instead of `Prop`.
    (intro : ∀ (w : α) (h : p w), motive (Exists.intro w h))
    (t : Exists p) : motive t
-- Recall, recursors have reduction rules for each constructor.
axiom Exists.badRec_intro {α : Sort u} {p : α → Prop}
    {motive : Exists p → Sort v}
    (intro : ∀ (w : α) (h : p w), motive (Exists.intro w h))
    (w : α) (h : p w) :
    Exists.badRec intro (Exists.intro w h) = intro w h
/-!
With these, we can define a function that extracts a witness.
-/
noncomputable def Exists.witness {α : Sort u} {p : α → Prop}
    (he : ∃ x : α, p x) : α :=
  Exists.badRec
    (motive := fun _ => α)
    (intro := fun w _ => w)
    he
theorem Exists.witness_intro {α : Sort u} {p : α → Prop}
    (w : α) (h : p w) :
    Exists.witness (Exists.intro w h : ∃ x : α, p x) = w :=
  Exists.badRec_intro
    (motive := fun _ => α)
    (intro := fun w _ => w)
    w h
/-!
And then we can prove `False`.

This proof is a bit tricky because Lean *really* likes
to take advantage of proof irrelevance!
-/
set_option pp.proofs true in
example : False := by
  have := exists1_eq_exists2
  unfold exists1 exists2 at this
  have := congrArg Exists.witness this
  conv at this =>
    enter [1]
    rw [Exists.witness_intro 1 (by simp)]
  conv at this =>
    enter [2]
    rw [Exists.witness_intro 2 (by simp)]
  simp at this

/-!
Small elimination is reflected in the following error messages:
-/
example (h : ∃ x : ℕ, x > 0) : ℕ :=
  match h with
  | Exists.intro x _ => x

example (h : ∃ x : ℕ, x > 0) : ℕ := by
  cases h

/-!
Despite these issues, some propositions allow large elimination.
Rule: it is allowed if the constructor contains no data.
-/
#check Eq.rec
#check And.rec


/-!
## No confusion

The recursor of an inductive type is enough to prove that constructors
are injective. Both the `cases` and `simp` tactics can be used to prove
impossibilities.

Example:
-/
example (h : [1] = [3,4]) : False := by cases h
example (h : [1] = [3,4]) : False := by simp at h

/-!
It uses a really neat trick.
-/
#check Bool.noConfusionType
#check Bool.noConfusion

def Bool.noConfusionType' (P : Sort u) (v1 v2 : Bool) : Sort u :=
  Bool.recOn v1
    (true := Bool.recOn v2 (true := P → P) (false := P))
    (false := Bool.recOn v2 (true := P) (false := P → P))

#check Eq.recOn

def Bool.noConfusion' {P : Sort u} {v1 v2 : Bool} (h12 : v1 = v2) :
    Bool.noConfusionType' P v1 v2 :=
  Eq.recOn h12
    (motive := fun v2' _ => Bool.noConfusionType' P v1 v2')
    (refl := Bool.recOn v1 (true := id) (false := id))

example (h : true = false) : False :=
  Bool.noConfusion' h
