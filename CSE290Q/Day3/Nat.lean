import Lean
import Batteries
import Mathlib.Util.CompileInductive

/-!
# Implementing the natural numbers from scratch

-/

namespace CSE290Q

/--
Unary encoding of natural numbers: every natural number is either
zero or the successor of a natural number.
-/
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  -- Make it possible print results of `#eval`:
  deriving Lean.ToExpr

-- Inhibit pretty printing `Nat.succ n` as `n.succ`:
attribute [pp_nodot] Nat.succ

/-!
## Definitions
-/

def Nat.add : Nat → Nat → Nat
  | m, zero => m
  | m, succ n => succ (Nat.add m n)

instance : Add Nat where
  add := Nat.add

#eval Nat.succ Nat.zero + Nat.succ (Nat.succ Nat.zero)
-- Nat.succ (Nat.succ (Nat.succ Nat.zero))

-- (This forces the compiler to support `Nat.recOn`)
compile_inductive% Nat

def Nat.add' : Nat → Nat → Nat :=
  fun m n =>
    Nat.recOn n
      m
      (fun _ res => succ res)

#eval Nat.add' (Nat.succ Nat.zero) (Nat.succ (Nat.succ Nat.zero))
-- Nat.succ (Nat.succ (Nat.succ Nat.zero))


def Nat.mul : Nat → Nat → Nat
  | _, zero => zero
  | m, succ n => Nat.mul m n + m

instance : Mul Nat where
  mul := Nat.mul

#eval Nat.succ (Nat.succ Nat.zero) * Nat.succ (Nat.succ Nat.zero)
-- Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

def Nat.pred : Nat → Nat
  | zero => zero
  | succ n => n

def Nat.sub : Nat → Nat → Nat
  | m, zero => m
  | m, succ n => Nat.pred (Nat.sub m n)

instance : Sub Nat where
  sub := Nat.sub

#eval Nat.succ (Nat.succ (Nat.succ Nat.zero)) - Nat.succ Nat.zero
-- Nat.succ (Nat.succ Nat.zero)
#eval Nat.succ Nat.zero - Nat.succ (Nat.succ (Nat.succ Nat.zero))
-- Nat.zero

/-!
## Theorems
-/

theorem Nat.add_zero (n : Nat) : n + zero = n := by
  sorry

theorem Nat.zero_add (n : Nat) : zero + n = n := by
  sorry

theorem Nat.add_succ (m n : Nat) : m + succ n = succ (m + n) := by
  sorry

theorem Nat.succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  sorry

theorem Nat.add_comm (m n : Nat) : m + n = n + m := by
  sorry

theorem Nat.add_assoc (l m n : Nat) : (l + m) + n = l + (m + n) := by
  sorry

theorem Nat.mul_zero (n : Nat) : n * zero = zero := by
  sorry

theorem Nat.zero_mul (n : Nat) : zero * n = zero := by
  sorry

theorem Nat.mul_one (n : Nat) : n * succ zero = n := by
  sorry

theorem Nat.one_mul (n : Nat) : succ zero * n = n := by
  sorry

theorem Nat.mul_comm (m n : Nat) : m * n = n * m := by
  sorry

theorem Nat.mul_assoc (l m n : Nat) : (l * m) * n = l * (m * n) := by
  sorry

theorem Nat.mul_add (l m n : Nat) : l * (m + n) = l * m + l * n := by
  sorry

theorem Nat.add_mul (l m n : Nat) : (l + m) * n = l * n + m * n := by
  sorry

theorem Nat.pred_zero : pred zero = zero := by
  sorry

theorem Nat.pred_succ (n : Nat) : pred (succ n) = n := by
  sorry

theorem Nat.sub_zero (n : Nat) : n - zero = n := by
  sorry

theorem Nat.sub_succ (m n : Nat) : m - succ n = pred (m - n) := by
  sorry

-- Not true:
-- theorem Nat.succ_sub (m n : Nat) : succ m - n = succ (m - n) := by
--   sorry

theorem Nat.succ_sub_succ (m n : Nat) : succ m - succ n = m - n := by
  sorry

theorem Nat.add_sub_add_right (m k n : Nat) : (m + k) - (n + k) = m - n := by
  sorry

theorem Nat.add_sub_add_left (k n m : Nat) : (k + n) - (k + m) = n - m := by
  sorry

end CSE290Q
