import Lean
/-!
# Brief introduction to Lean
-/

/-!
## Lean as a functional programming language
-/

set_option pp.fieldNotation false

def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n' + 1 => n * factorial n'

#eval factorial 10

#eval List.range 10 |>.map factorial


/-!
## Lean as a proof assistant
-/

theorem factorial_one_eq : factorial 1 = 1 := by
  unfold factorial
  unfold factorial
  rw [Nat.mul_one]

theorem factorial_one_eq' : factorial 1 = 1 := by trivial

#print factorial

theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih =>
    unfold factorial
    rw [Nat.add_mul, Nat.one_mul]
    apply Nat.lt_add_left
    exact ih

/-!
Propositions as types (Curry–Howard correspondence)
-/

#check Unit
#check True
#check Empty
#check False
#check Prod
#check And
#check Sum
#check Or

set_option pp.proofs true

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  obtain ⟨h1, h2⟩ := h
  exact And.intro h2 h1

example (p : Prop) : p → p := fun h => h
example (p q : Prop) : p → (q → p) := fun h _ => h
example (p q r : Prop) : (p → q) → (p → (q → r)) → (p → r) := by?
  intro h1
  intro h2
  intro h3
  specialize h1 h3
  specialize h2 h3
  specialize h2 h1
  assumption



/-!
## Lean as a metaprogramming environment
-/

macro "solve_imp" : tactic =>
  `(tactic|
    repeat
      first | (intro) | simp only [*] at *
  )

example (p q r : Prop) : (p → q) → (p → (q → r)) → (p → r) := by
  solve_imp


inductive Arith : Type
  | add : Arith → Arith → Arith  -- e + f
  | mul : Arith → Arith → Arith  -- e * f
  | int : Int → Arith  -- constant
  | symbol : String → Arith  -- variable

declare_syntax_cat arith

syntax num : arith  -- int for Arith.int
syntax str : arith  -- strings for Arith.symbol
syntax:60 arith:60 "+" arith:61 : arith  -- Arith.add
syntax:70 arith:70 "*" arith:71 : arith  -- Arith.mul
syntax "(" arith ")" : arith  -- parenthesized expressions

-- auxiliary notation for translating `arith` into `term`
syntax "`[Arith| " arith "]" : term

macro_rules
  | `(`[Arith| $s:str]) => `(Arith.symbol $s)
  | `(`[Arith| $num:num]) => `(Arith.int $num)
  | `(`[Arith| $x + $y]) => `(Arith.add `[Arith| $x] `[Arith| $y])
  | `(`[Arith| $x * $y]) => `(Arith.mul `[Arith| $x] `[Arith| $y])
  | `(`[Arith| ($x)]) => `(`[Arith| $x])

syntax ident : arith

macro_rules
  | `(`[Arith| $x:ident]) => `(Arith.symbol $(Lean.quote (toString x.getId)))

#check `[Arith| x * y]

#check `[Arith| x + y]

#check `[Arith| x + 20]

#check `[Arith| x + y * z]

#check `[Arith| x * y + z]

#check `[Arith| (x + y) * z]

syntax "<[" term "]>" : arith  -- escape for embedding terms into `Arith`

macro_rules
  | `(`[Arith| <[ $e:term ]>]) => pure e

def xPlusY := `[Arith| x + y]
#check `[Arith| <[ xPlusY ]> + z]

def Arith.eval (vars : List (String × Int)) : Arith → Int
  | add x y => x.eval vars + y.eval vars
  | mul x y => x.eval vars * y.eval vars
  | int n => n
  | symbol s => (vars.lookup s).getD 0

#eval
  let vars := [("x", 2), ("y", 3)]
  Arith.eval vars `[Arith| x + 3 * y]
