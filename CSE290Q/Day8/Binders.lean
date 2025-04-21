import Mathlib.Tactic.Common
/-!
# Binder kinds, and De Bruijn indexing

The anatomy of pi/lambda expressions:

```lean
(x : α) → β x

fun (x : α) => v x
```

Terminology:
- `α` is binder domain
- `x` is binder name
- the `()`s indicate "explicit" binder kind (the default)
- `β x` and `v x` are the bodies

Binder kinds have no theoretical effect.
They control the elaboration of function applications.
- `(x : α)` default/explicit (or `(x)`, for `(x : _)`)
- `{x : α}` implicit (or `{x}`)
- `⦃x : α⦄` strict implicit (or `{{x : α}}`) (or `⦃x⦄`)
- `[x : α]` instance implicit (only when `α` is a class) (or `[α]` for `[inst : α]`)

-/

/-!
High-level overview of the Lean system:

Command parser: source text ----> command `Syntax`
Term parser: source text ----> term `Syntax`
Tactic parser: ...

Command elaborator: reads commands and runs code one at a time.
Examples:
- `#check` elaborator
- `def`/`theorem`/`example` elaborators
- `inductive`/`structure`  elaborators

Term elaborator ("*the* elaborator"): term `Syntax` ----> `Expr`


-/

def f1 (n : Nat) (x : Fin n) : Fin n := x
def f2 {n : Nat} (x : Fin n) : Fin n := x
def f3 ⦃n : Nat⦄ (x : Fin n) : Fin n := x

#check (f1)
#check (f1 2)
#check (f1 2 3)
#check (f2)
#check (f2 (3 : Fin 2))
#check (f3)
#check (f2 (3 : Fin _))

#check (f1 (n := 2))
#check (f2 (n := 2))
#check (f3 (n := 2))
