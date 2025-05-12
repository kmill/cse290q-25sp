import Mathlib.Tactic.Basic
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Basic
/-!
# Implementing subtype polymorphism
-/

/-!
Consider the following:
-/

namespace Ex1

structure A where
  n : Nat

def A.toString (a : A) := s!"A has n = {a.n}"

def myA : A := { n := 2 }
#eval myA.toString

structure B extends A where
  pos : 0 < n

def myB : B := { n := 2, pos := by simp }
#eval myB.toString

/-!
That's not good. How can we fix it?

One option, define a new `toString` for `B`.
-/
def B.toString (b : B) := s!"B has positive n = {b.n}"
#eval myB.toString

/-!
That's basically so-called "static polymorphism".
It works because it resolves to a specific function.
-/

/-!
General solution: create a typeclass for operations.
-/
instance : ToString A where
  toString := A.toString
instance : ToString B where
  toString := B.toString

#eval toString myA
#eval toString myB

end Ex1

namespace Ex2

structure Digraph (V : Type u) where
  adj : V → V → Prop
structure SimpleGraph (V : Type u) extends Digraph V where
  adj_symm : Symmetric adj
  adj_irrefl : Irreflexive adj

def Digraph.union {V : Type u} (G₁ G₂ : Digraph V) : Digraph V where
  adj v w := G₁.adj v w ∨ G₂.adj v w

theorem Digraph.union_comm {V : Type u} {G₁ G₂ : Digraph V} :
    G₁.union G₂ = G₂.union G₁ := by
  sorry

theorem SimpleGraph.sup_comm {V : Type u} {G₁ G₂ : SimpleGraph V} :
    G₁.union G₂ = G₂.union G₁ := by
  sorry

def Digraph.sup {V : Type u} (G₁ G₂ : Digraph V) : Digraph V where
  adj v w := G₁.adj v w ∨ G₂.adj v w
instance {V : Type u} : Max (Digraph V) where max := Digraph.sup

theorem Digraph.sup_comm {V : Type u} {G₁ G₂ : Digraph V} :
    G₁ ⊔ G₂ = G₂ ⊔ G₁ := by
  sorry

theorem SimpleGraph.sup_comm {V : Type u} {G₁ G₂ : SimpleGraph V} :
    G₁ ⊔ G₂ = G₂ ⊔ G₁ := by
  sorry


class Adj (Γ : Type u) (V : outParam <| Type v) where
  adj : Γ → V → V → Prop
export Adj (adj)

instance {V : Type u} : Adj (Digraph V) V where
  adj := Digraph.adj

instance {V : Type u} : Adj (SimpleGraph V) V where
  adj G v w := G.adj v w

def neighbor_set {Γ : Type u} {V : Type v} [Adj Γ V] (G : Γ) (v : V) : Set V :=
  { w : V | adj G v w }

end Ex2
