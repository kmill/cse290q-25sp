import Mathlib.Tactic.Common

inductive MyList (α : Type u) where
  | nil
  | cons (x : α) (xs : MyList α)

variable {α : Type u}

notation "[]" => MyList.nil
infixr:67 " :: " => MyList.cons

/--
Appends `xs` to the front of `ys`.
-/
def MyList.append (xs ys : MyList α) : MyList α :=
  match xs with
  | [] => ys
  | x :: xs' => x :: (xs'.append ys)

instance : Append (MyList α) where
  append := MyList.append

@[simp]
theorem MyList.nil_append (xs : MyList α) :
    [] ++ xs = xs := by
  sorry

@[simp]
theorem MyList.cons_append (x : α) (xs ys : MyList α) :
    (x :: xs) ++ ys = x :: (xs ++ ys) := by
  sorry

@[simp]
theorem MyList.append_nil (xs : MyList α) :
    xs ++ [] = xs := by
  sorry

theorem MyList.append_assoc (xs ys zs : MyList α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  sorry

theorem MyList.cons_eq_append (x : α) (xs : MyList α) :
    x :: xs = (x :: []) ++ xs := by
  sorry

--set_option trace.compiler.ir.result true
/--
Reverses `xs` and appends it to `ys`.

Tail recursive.
-/
def MyList.reverseAux (xs ys : MyList α) : MyList α :=
  match xs with
  | [] => ys
  | x :: xs' => reverseAux xs' (x :: ys)

/--
Reverses `xs`. Tail recursive.
-/
def MyList.reverse (xs : MyList α) : MyList α :=
  MyList.reverseAux xs []

@[simp]
theorem MyList.reverse_nil :
    MyList.reverse [] = ([] : MyList α) := by
  sorry

theorem MyList.reverseAux_eq (xs ys : MyList α) :
    MyList.reverseAux xs ys = MyList.reverse xs ++ ys := by
  sorry

theorem MyList.reverse_cons_append (x : α) (xs ys : MyList α) :
    (x :: xs).reverse ++ ys = xs.reverse ++ (x :: ys) := by
  sorry

theorem MyList.reverseAux_append (xs ys zs : MyList α) :
    MyList.reverseAux (xs ++ ys) zs = MyList.reverseAux ys (xs.reverse ++ zs) := by
  sorry

theorem MyList.reverse_append (xs ys : MyList α) :
    (xs ++ ys).reverse = ys.reverse ++ xs.reverse := by
  sorry

def MyList.length (xs : MyList α) : ℕ :=
  match xs with
  | [] => 0
  | _ :: xs' => xs'.length + 1 -- Design question: Why +1 and not 1+ ?

@[simp]
theorem MyList.length_nil :
    ([] : MyList α).length = 0 := by
  sorry

@[simp]
theorem MyList.length_cons (x : α) (xs : MyList α) :
    (x :: xs).length = xs.length + 1 := by
  sorry

theorem MyList.length_append (xs ys : MyList α) :
    (xs ++ ys).length = xs.length + ys.length := by
  sorry

theorem MyList.length_reverseAux (xs ys : MyList α) :
    (MyList.reverseAux xs ys).length = xs.length + ys.length := by
  sorry

@[simp]
theorem MyList.length_reverse (xs : MyList α) :
    xs.reverse.length = xs.length := by
  sorry

def MyList.map {β : Type v} (f : α → β) (xs : MyList α) : MyList β :=
  sorry

variable {β : Type v} {f : α → β}

/-!
For the following, you may want to develop more theorems.
-/

theorem MyList.map_append (xs ys : MyList α) :
    (xs ++ ys).map f = xs.map f ++ ys.map f := by
  sorry

theorem MyList.reverse_map (xs : MyList α) :
    (xs.map f).reverse = xs.reverse.map f := by
  sorry

theorem MyList.length_map (xs : MyList α) :
    (xs.map f).length = xs.length := by
  sorry
