import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

inductive MyVect (α : Type u) : (n : Nat) → Type u where
  | nil : MyVect α 0
  | cons (x : α) {n : ℕ} (xs : MyVect α n) : MyVect α (n + 1)

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
