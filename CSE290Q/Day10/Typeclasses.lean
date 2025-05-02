import Lean
import Mathlib.Logic.Equiv.Defs
/-!
# Introduction to typeclasses and algebraic structures
-/
universe u v w

/-!
Recall that `structure` is a convenient way to define an inductive type
with one constructor.
-/
structure S (α : Type) where
  x : α
  y : α
  ne : x ≠ y
/-!
This is more-or-less the same as doing the following four declarations:
-/
inductive S' (α : Type) where
  | mk (x : α) (y : α) (ne : x ≠ y)

def S'.x {α : Type} (self : S' α) : α :=
  match self with
  | S'.mk x _ _ => x

def S'.y {α : Type} (self : S' α) : α :=
  match self with
  | S'.mk _ y _ => y

def S'.ne {α : Type} (self : S' α) : self.x ≠ self.y :=
  match self with
  | S'.mk _ _ ne => ne

/-!
Structures are a good way to represent algebraic structures.

In textbooks we may see
  "A *semigroup* is a pair `(G, mul)` with a set `G` and an associative
  binary operation `mul : G × G → G`. By abuse of notation, we will write `G`
  for both the semigroup and the set."

"By abuse of notation" is *very* convenient. How do we implement that in Lean?

To motivate this, let's define the structure and see what it's like
to work with structures directly.
-/

structure Semigroup₀ where
  G : Type u
  mul : G → G → G
  mul_assoc : ∀ (x y z : G), mul (mul x y) z = mul x (mul y z)

def Semigroup₀.nat : Semigroup₀ where
  G := Nat
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc

/-!
This `Semigroup₀.{u}` type is good for working with all possible semigroups
in `Type u`. (These are the objects for the category of semigroups in universe `Type u`.)
In practice though, one wants to work with the semigroup structure
for a particular type.
-/

structure Semigroup₁ (G : Type u) where
  mul : G → G → G
  mul_assoc : ∀ (x y z : G), mul (mul x y) z = mul x (mul y z)

def Semigroup₁.nat : Semigroup₁ Nat where
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc

/-!
One can recover `Semigroup₀` as needed using a *sigma type*.
-/
#check (G : Type u) × Semigroup₁ G

def semigroup₀_equiv_semigroup₁ : Semigroup₀ ≃ (G : Type u) × Semigroup₁ G where
  toFun S := ⟨S.G, { S with }⟩
    -- `{ S with }` is equivalent to `{ mul := S.mul, mul_assoc := S.mul_assoc }`
  invFun p := { p.2 with G := p.1 }
  left_inv := by rintro ⟨⟩; rfl
  right_inv := by rintro ⟨⟩; rfl

/-!
Recovering `Semigroup₁` from `Semigroup₀` is less good.
It's possible using a *subtype*, but it involves an equality of types.
(Equality of types is "evil".)
-/
def Semigroup₁' (G : Type u) := { S : Semigroup₀ // S.G = G }

def semigroup₁_equiv_semigroup₁' (G : Type u) :
    Semigroup₁ G ≃ Semigroup₁' G where
  toFun s := ⟨{ s with G }, rfl⟩
    -- `{ s with G }` is short for `{ s with G := G }`
  invFun p := p.2 ▸ { p.1 with }
    -- The `▸` operator is "smart rewrite"; it rewrites the value's type or the expected type.
  left_inv := by rintro ⟨⟩; rfl
  right_inv := by rintro ⟨_, rfl⟩; rfl

/-!
**Side note:** All of the following are kinds of sigma types.
They just have different universe constraints and land in different universes
(and have varying elimination rules).
-/
#check Sigma
#check Subtype
#check Exists
#check PSigma
-- Non-dependent:
#check Prod
#check And
#check PProd
-- Unrelated, but useful to about:
#check PLift
#check ULift

/-!
A *monoid* is a triple `(M,mul,one)` where `one : M`, `M` is a semigroup,
and `one` is a left and right identity of `mul`.

The `extends` clause is a way to include all the fields of a structure.
(The `extends Semigroup₁ M` clause creates a `toSemigroup₁ : Semigroup₁ M`
projection too.)
-/
structure Monoid₁ (M : Type u) extends Semigroup₁ M where
  one : M
  one_mul : ∀ (x : M), mul one x = x
  mul_one : ∀ (x : M), mul x one = x

theorem Monoid₁.one_unique {M : Type u} (s : Monoid₁ M)
    (one' : M) (one_mul' : ∀ x, s.mul x one' = x) :
    one' = s.one := by
  have := s.one_mul one'
  rw [one_mul'] at this
  exact this.symm

def Monoid₁.nat : Monoid₁ Nat where
  toSemigroup₁ := Semigroup₁.nat
  one := 1
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

/-!
With this system, we have to mention the monoid structure directly.
No abuse of notation for us.
-/
example (n : Nat) : Monoid₁.nat.mul (Monoid₁.nat.mul 1 n) 1 = n := by
  have : 1 = Monoid₁.nat.one := rfl
  rw [this, Monoid₁.one_mul, Monoid₁.mul_one]

/-!
There are other reasonable monoid structures on `Nat` too.
With `Monoid₁` there's no harm in defining multiple monoid structures.
-/
def Monoid₁.natAdd : Monoid₁ Nat where
  mul := Nat.add
  one := 0
  mul_assoc := Nat.add_assoc
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero

-- Other types have standard monoid structures too of course.
def Monoid₁.int : Monoid₁ Int where
  mul := Int.mul
  mul_assoc := Int.mul_assoc
  one := 1
  one_mul := Int.one_mul
  mul_one := Int.mul_one

-- Every computer scientist's second favorite monoid, lists!
def Monoid₁.list {α : Type u} : Monoid₁ (List α) where
  mul := List.append
  one := []
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

section NotationSoln
/-!
We will very shortly see how it's actually done in mathlib.
But, one way we might try to work with `Monoid₁` is via notation overloading.
Lean disambiguates using type information.
-/
local infixl:65 " *' " => Monoid₁.nat.mul
local infixl:65 " *' " => Monoid₁.list.mul

variable (m n : Nat)
#check [m *' n] *' [m]

end NotationSoln

namespace UnificationHints

/-!
**Aside: unification hints**. Another solution, used by the Mathematical Components
library in Rocq, is via a tool called a *unification hint*. These direct unification
(the `isDefEq` algorithm) with how to successfully pursue unifying two expressions.

This uses the "bundled" `Semigroup₀` type directly.

Step 1 (optional): define a coercion `Semigroup₀ → Type _`
-/
instance : CoeSort Semigroup₀.{u} (Type u) where
  coe S := S.G
/-!
This lets us use a semigroup structure as if it were the type itself.
-/
def NatSemigroup : Semigroup₀ := { Monoid₁.nat with G := Nat }
#check fun (n : NatSemigroup) => n
/-!
We can't multiply yet though.
-/
#check fun (m n : NatSemigroup) => m * n
/-!
Step 2: add multiplication notation that uses `Semigroup₀.mul`.
We'll override the built-in notation using a macro rule.
-/
local macro_rules | `($x * $y) => `(Semigroup₀.mul _ $x $y)
#check fun (m n : NatSemigroup) => m * n
/-!
The notation works!

However, we want to work with `Nat` itself. This fails:
-/
#check fun (m n : Nat) => m * n
/-!
Step 3: make `Nat` "be" the semigroup using a unification hint.
-/
unif_hint (s : Semigroup₀) where
  s =?= NatSemigroup
  ⊢ s.G =?= Nat
/-!
Abuse of notation successfully implemented:
-/
#check fun (m n : Nat) => m * n
/-!
How does this work?
- `m * n` is `Semigroup₀.mul _ m n`
- the type of `Semigroup₀.mul` is
  `(s : Semigroup₀) → s.G → s.G → s.G`
- hence given `m : Nat`, we need to unify `m` and `s.G` to pass it as an argument,
  the `s` is the unknown `_`
- the unification hint kicks in, causing `_` to be solved for as `NatSemigroup`.
-/
#check Semigroup₀.mul

end UnificationHints

/-!
## Making `Monoid₁` more convenient.

Why should we have to refer to the actual monoid structure all the time?
In practice, there's no more than *one* monoid structure that anyone cares about
on a given type. (Proviso: multiplicative and additive notation might have
different monoid structures!)

Let's go back to "abuse of notation".
How can we get Lean to fill in the algebraic structure for us?
Since we're in type theory, every term has a well-defined type,
and we can make use of this in the *typeclass system*.
-/

/-!
A `class` is a `structure`, but with some small differences.
-/
class Semigroup (G : Type u) where
  mul : G → G → G
  mul_assoc : ∀ (x y z : G), mul (mul x y) z = mul x (mul y z)

/-!
First difference: it registers the structure as being a "class".
Only types that are classes participate in the typeclass system.

Second difference: the types of the projections are modified slightly.
-/
#check Semigroup₁.mul
#check Semigroup.mul
#check Semigroup₁.mul_assoc
#check Semigroup.mul_assoc
/-
Notice the `[Semigroup G]` arguments.
(Language note: when the argument name itself is not relevant for a declaration's type,
`[self : Semigroup G]` can be written as `[Semigroup G]`.)
-/

/-!
A definition can be marked as an *instance*, which lets it be found
via typeclass instance synthesis.
The name of an instance is optional, in which case it is automatically generated.
-/
instance : Semigroup Nat where
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc

#synth Semigroup Nat

/-!
With this instance registered, we can use the fields of `Semigroup`
without specifying the instance argument.
It's filled in using *typeclass inference*.
-/
#check Semigroup.mul 2 3
#check Semigroup.mul_assoc 1 2 3

instance : Semigroup Bool where
  mul := Bool.and
  mul_assoc := Bool.and_assoc

#check Semigroup.mul true false

/-!
Extending classes is similar to extending structures.
-/
class Monoid (M : Type u) extends Semigroup M where
  one : M
  one_mul : ∀ (x : M), mul one x = x
  mul_one : ∀ (x : M), mul x one = x

/-!
Difference: the `toSemigroup` projection is an instance.
This lets a `Monoid` "be" a `Semigroup` without any friction.
-/
#check Monoid.toSemigroup

--set_option trace.Meta.synthInstance true

-- Notice, `mul` works here even though it's only a `Monoid`.
open Semigroup Monoid in
theorem Monoid.one_unique {M : Type u} [Monoid M]
    (one' : M) (one_mul' : ∀ x, mul x one' = x) :
    one' = one := by
  have := one_mul one'
  rw [one_mul'] at this
  exact this.symm

/-!
## Other typeclasses in Lean
-/

-- Not the core definition, but it's equivalent.
class Decidable' (p : Prop) where
  decide : Bool
  pf : bif decide then p else ¬ p

instance : Decidable' True where
  decide := true
  pf := trivial
instance : Decidable' False where
  decide := false
  pf := id

#eval Decidable'.decide True

instance {p q : Prop} [Decidable' p] [Decidable' q] :
    Decidable' (p ∧ q) where
  decide := Decidable'.decide p && Decidable'.decide q
  pf := by
    cases hp : Decidable'.decide p
      <;> cases hq : Decidable'.decide q
    · sorry
    · sorry
    · sorry
    · sorry

/-!
## Homomorphisms

We'll see these in a future installment.
-/
