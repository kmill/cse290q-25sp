import Mathlib.Tactic
/-!
# Equivalence of two definitions of the Fibonacci sequence
-/

def fib1 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 1
  | n' + 2 => fib1 n' + fib1 (n' + 1)

-- #eval (List.range 10).map fib1

-- #eval fib1 100
-- #reduce fib1 100

def fib2 (n : ℕ) : ℕ :=
  go n 0 1
where
  go (n : ℕ) (a b : ℕ) : ℕ :=
    match n with
    | 0 => a
    | n' + 1 => go n' b (a + b)

-- #eval (List.range 10).map fib2

-- #eval fib2 100
-- #reduce fib2 100

theorem fib2.go_add (n a b a' b' : ℕ) :
    fib2.go n a b + fib2.go n a' b' = fib2.go n (a + a') (b + b') := by
  induction n generalizing a b a' b' with
  | zero =>
    simp only [fib2.go]
  | succ n ih =>
    simp only [fib2.go]
    rw [ih]
    congr! 1
    abel

theorem fib2_add_two (n : ℕ) : fib2 (n + 2)= fib2 n + fib2 (n + 1) := by
  simp [fib2, fib2.go]
  rw [fib2.go_add]

theorem fib1_eq_fib2 : fib1 = fib2 := by
  ext n
  induction n using Nat.strongRecOn with | _ n ih => ?_
  obtain _ | _ | n' := n
  · rfl
  · rfl
  · rw [fib1, fib2_add_two]
    rw [ih n', ih (n' + 1)]
    all_goals omega

attribute [csimp] fib1_eq_fib2

-- #eval fib1 100
