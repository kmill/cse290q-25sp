import Mathlib.Tactic.Common

/-
# What is an inductive data type really?
-/

/-
Scott encoding
-/

inductive MyList (α : Type) where
  | nil
  | cons (x : α) (xs : MyList α)

/-
"Definition" of the recursor
-/
def MyList.rec' {α : Type} {motive : MyList α → Sort u}
    (nil : motive MyList.nil)
    (cons : (x : α) → (xs : MyList α) → motive xs → motive (MyList.cons x xs))
    (t : MyList α) :
    motive t :=
  match t with
  | .nil => nil
  | .cons x xs => cons x xs (MyList.rec' nil cons xs)

/-
-/

def MyList_nil {α : Type} :=
  fun n c => n

def MyList_cons {α : Type} (x : α) (xs : MyList α) :=
  fun n c => c x xs

def MyList_rec {motive : MyList α → Sort u}
    (nil : motive MyList.nil)
    (cons : (x : α) → (xs : MyList α) → motive xs → motive (MyList.cons x xs))
    (t : MyList α) :
    motive t :=
  t nil (fun x xs => cons x xs (MyList_rec nil cons xs))

#check List.foldr
/-
List.foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β) : List α → β
-/

--compile_inductive% List

def List.foldr' (f : α → β → β) (init : β) (t : List α) : β :=
  List.rec init (fun x _ r => f x r) t
