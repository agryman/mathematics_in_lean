-- example 1 using assume, have-from, show-from
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume h₁ : p,
assume h₂ : q ∧ r,
have h₃ : q, from and.left h₂,
show p ∧ q, from and.intro h₁ h₃

-- example 1 with syntactic sugar expanded
-- have-from introduces a local variable
-- show-from computes a result
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
λ h₁ : p,
λ h₂ : q ∧ r,
(λ h₃ : q, (and.intro h₁ h₃ : p ∧ q)) (and.left h₂)

-- example 2 with notation French quotes ‹p› 
-- translates to (by assumption : p)
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume : p,
assume : q ∧ r,
have q, from and.left this,
show p ∧ q, from and.intro ‹p› this

-- example 2 using labels for hypotheses
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume hp : p,
assume hqr : q ∧ r,
have hq : q, from and.left hqr,
show p ∧ q, from and.intro hp hq

-- example 2 with syntactic sugar expanded
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
λ hp : p,
λ hqr : q ∧ r,
(λ hq: q,
  (and.intro hp hq : p ∧ q)) (and.left hqr)

-- example 3 using suffices-from
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
assume h₁ : p,
assume h₂ : q ∧ r,
suffices h₃ : q, from and.intro h₁ h₃,
show q, from and.left h₂

-- example 3 expanded
example (p q r : Prop) : p → (q ∧ r) → p ∧ q :=
λ h₁ : p,
λ h₂ : q ∧ r,
(λ h₃ : q, and.intro h₁ h₃)
  (and.left h₂ : q)
/-
suffices h : p, from s, t

This means that it suffices to construct a term h
of type p using the expression t because when t is
substituted into s it results in the desired
goal.
-/

/-
My conclusion is that Lean goes to great lengths
to provide many equivalent ways to prove a theorem.
This is flexible and may allow for matching an
informal, published proof to a formal Lean proof.
However, this abundance of equivalent ways to
prove a theorem increases the difficulty of
learning Lean. It also violates the Zen of Python:

"There should be one-- and preferably only one --obvious way to do it.
Although that way may not be obvious at first unless you're Dutch.
"
-/
