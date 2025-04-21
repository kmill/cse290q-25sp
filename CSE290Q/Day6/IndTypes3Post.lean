import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!
## Prop inductives

The inductive command lets us define new propositions as well.
-/

inductive IsEven : Nat → Prop where
  | zero : IsEven 0
  | add_two (n : Nat) (h : IsEven n) : IsEven (n + 2)

theorem IsEven.two : IsEven 2 := by
  apply IsEven.add_two
  exact IsEven.zero

theorem IsEven.not_one : ¬ IsEven 1 := by
  intro h
  cases h

theorem isEven_iff_exists (n : Nat) : IsEven n ↔ ∃ k, n = 2 * k := by
  induction n using Nat.strongRecOn with | _ n ih => ?_
  obtain _ | (_ | n') := n
  · simp only [IsEven.zero, true_iff]
    use 0
  · simp [IsEven.not_one]
    omega
  · constructor
    · intro h
      cases h
      specialize ih n' (by omega)
      simp [*] at ih
      obtain ⟨k, rfl⟩ := ih
      use k + 1
      omega
    · rintro ⟨_ | k, h⟩
      · simp at h
      · simp [Nat.mul_succ] at h
        subst h
        apply IsEven.add_two
        rw [ih]
        · use k
        omega


#print Exists
#print Sigma

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
#### Types can be empty even if there are constructors
-/

inductive NeverTrue : Nat → Prop where
  | add_two (n : Nat) (h : NeverTrue n) : NeverTrue (n + 2)

theorem not_never_true (n : Nat) : ¬ NeverTrue n := by
  intro h
  induction h
  assumption

/-!
#### Types can't be self-inconsistent though
-/

inductive BadProp : Prop where
  | mk (h : ¬ BadProp) : BadProp

-- Let's introduce it against all advice

axiom BadProp : Prop
axiom BadProp.mk (h : ¬ BadProp) : BadProp
axiom BadProp.cases
  {motive : BadProp → Prop}
  (mk : (h : ¬ BadProp) → motive (BadProp.mk h))
  (t : BadProp) : motive t

theorem BadProp_mk' (h : BadProp) : ¬ BadProp :=
  BadProp.cases
    (motive := fun _ => ¬ BadProp)
    (mk := fun h' => h')
    h

example : False := by
  have : BadProp ↔ ¬ BadProp := ⟨BadProp_mk', BadProp.mk⟩
  simp at this

/-!
### Large elimination

Generally, inductive propositions have "small elimination".
This means the motive is `Prop`-valued.
-/
#check Exists.rec

example (p : ∃ n, n > 0) (q : Prop) : q := by
  cases p -- allowed
  sorry
example (p : ∃ n, n > 0) (α : Type) : α := by
  cases p -- not allowed

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

example (h : true = false) : Nat :=
  Bool.noConfusion' h

example (h : [1] = []) : False := List.noConfusion h

example (h : [1] = [1,3]) : False :=
  List.noConfusion (List.noConfusion h fun _ => id)

/- What? How does that work for `List`? -/

def List.noConfusionType' {α : Type _} (P : Sort u) (v1 v2 : List α) : Sort u :=
  List.recOn v1
    (nil :=
      List.recOn v2 (nil := P → P) (cons := fun _ _ _ => P))
    (cons := fun x1 xs1 _ =>
      List.recOn v2 (nil := P)     (cons := fun x2 xs2 _ => (x1 = x2 → xs1 = xs2 → P) → P))

def List.noConfusion' {α : Type _} {P : Sort u} {v1 v2 : List α} (h12 : v1 = v2) :
    List.noConfusionType' P v1 v2 :=
  Eq.recOn h12
    (motive := fun v2' _ => List.noConfusionType' P v1 v2')
    (refl := List.recOn v1 (nil := id) (cons := fun x xs r f => f rfl rfl))

theorem foo {α : Type _} (x1 x2 : α) (xs1 xs2 : List α) (h : x1 :: xs1 = x2 :: xs2) : xs1 = xs2 :=
  Eq.recOn h
    (motive := fun x _ =>
      List.noConfusionType (xs1 = xs2) (x1 :: xs1) x)
    (refl := fun a => a (Eq.refl x1) (Eq.refl xs1))
    (fun _ hxs => hxs)

theorem List.conj_inj_left {α : Type _} (x1 x2 : α) (xs1 xs2 : List α)
    (h : x1 :: xs1 = x2 :: xs2) : x1 = x2 :=
  Eq.recOn h
    (motive := fun xxs _ =>
      List.recOn xxs (motive := fun _ => Prop)
        (nil := False) -- can be anything, unused
        (cons := fun x2' _ _ => x1 = x2'))
    (refl := Eq.refl x1)

theorem List.conj_inj_right {α : Type _} (x1 x2 : α) (xs1 xs2 : List α)
    (h : x1 :: xs1 = x2 :: xs2) : xs1 = xs2 :=
  Eq.recOn h
    (motive := fun xxs _ =>
      List.recOn xxs (motive := fun _ => Prop)
        (nil := False) -- can be anything, unused
        (cons := fun _ xs2' _ => xs1 = xs2'))
    (refl := Eq.refl xs1)

theorem List.nil_ne_cons {α : Type _} (x2 : α) (xs2 : List α) :
    [] ≠ x2 :: xs2 :=
  fun h => Eq.recOn h
    (motive := fun xxs _ =>
      List.recOn xxs (motive := fun _ => Prop)
        (nil := False → False)
        (cons := fun _ _ _ => False))
    (refl := fun a => a)

set_option pp.notation false
set_option pp.explicit true
#reduce (proofs := true) (types := true) @List.nil_ne_cons

example (h : [1] = [1,3]) : False :=
  List.noConfusion' (List.noConfusion' h fun _ hxs => hxs)

-- or, expanded:
example (h : [1] = [1,3]) : False := by
  -- In the cons case, the type of `List.noConfusion' h` is `(x1 = x2 → xs1 = xs2 → P) → P`
  -- so if `P` is `[] = [3]` we can use the function `fun hx hxs => hxs` to extract this proof.
  have : [] = [3] := List.noConfusion' h fun hx hxs => hxs
  exact List.noConfusion' this

example (h : [1] = [1,3]) : False := by?
  cases h
/-
Eq.casesOn (motive := fun a t => [1, 3] = a → HEq h t → False) h
  (fun h_1 => List.noConfusion h_1 fun head_eq tail_eq => List.noConfusion tail_eq)
  (Eq.refl [1, 3]) (HEq.refl h)
-/
