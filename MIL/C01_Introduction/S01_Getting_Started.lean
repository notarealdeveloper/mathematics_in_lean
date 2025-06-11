import Mathlib.Tactic         -- For the ℕ syntax
import Mathlib.Data.Nat.Basic -- A more specific way of enabling the ℕ syntax

-- def is a definition
def f (x : ℕ) :=
  x + 3

-- #check will show the type of an expression

#check f

#check f 2

-- #eval will show the value of an expression
#eval f 2

theorem easy : 2 + 2 = 4 :=
  rfl

-- The following expression represents a proof that if n is even then so is m * n for all m.
example : ∀ m n : Nat, Even n → Even (m * n) :=
  fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

-- The proof term can even be compressed to a single line
example : ∀ m n : Nat, Even n → Even (m * n) :=
  fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

-- The following is, instead, a "tactic style" proof of the same theorem
example : ∀ m n : Nat, Even n → Even (m * n) := by

  -- The following lines will amount to us saying:
  -- Suppse `m` and `n` are natural numbers, and assume `n = 2 * k`.
  -- Here's how we do that in Lean:

  -- The goal is currently:
  -- ⊢ ∀ (m n : ℕ), Even n → Even (m * n)
  -- Now we'll add "intro m" to turn the ∀ quantifier into an unbound variable of type Nat.

  intro m
  -- The goal is now:
  -- m : ℕ
  -- ⊢ ∀ (n : ℕ), Even n → Even (m * n)

  -- Now let's introduce a variable for n
  intro n

  -- The goal is now:
  -- m n : ℕ
  -- ⊢ Even n → Even (m * n)
  -- If we now type `intro e` we'll notice that `e` is an instance of type `Even n`
  -- Wtf does that mean?
  intro e

  -- The goal is now:
  -- m n : ℕ
  -- e : Even n
  -- ⊢ Even (m * n)

  -- Now we can destructure the existence proof `e` to get:
  -- 1. a witness `k`, and
  -- 2. a proof `p` that `n = k + k`
  let ⟨k, p⟩ := e

  -- The goal is now:
  -- m n : ℕ
  -- e : Even n
  -- k : ℕ
  -- p : n = k + k
  -- ⊢ Even (m * n)

  -- It now remains to prove that ⊢ Even (m * n)
  -- In other words, we have to prove that m * n = 2 * something
  -- The `use` function lets us use different values for that something
  -- If we type `use 42`, we get `⊢ m * n = 42 + 42`
  -- That's not true, but this is the effect that `use x` has on the goal
  -- Let's type `use m * k` to tell the system to use `m * k` as the number we're seeking

  -- We need to prove `m * n` is twice a natural number. Let's show it's twice `m * k`.
  use m * k

  -- Substitute for `n`
  rw [p]

  -- and now it's obvious,
  -- once we say `ring` to allow the kinds of reduction
  -- and simplification that are allowed in rings. o_O
  ring


-- Let's do that more simply
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intro m n e
  let ⟨k, n_even⟩ := e
  use m * k
  rw [n_even]
  ring

-- We can reduce the tactic proof to a one liner as well
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intro m n ⟨k, hk⟩; use m * k; rw [hk]; ring


-- Most abbreviated version of the proof in tactic mode
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros
  simp [*]


-- Kevin Buzzard's example, rewritten for Lean 4
-- From: https://www.youtube.com/watch?v=POHVMMG7pqE&ab_channel=XenaProject
example (p q r : Prop) : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) := by
  constructor
  . intro h
    constructor
    . intro hp
      apply h
      left
      exact hp
    . intro hq
      apply h
      right
      exact hq
  . intro ⟨hpr, hqr⟩
    intro pq
    cases pq with
    | inl hp => exact hpr hp
    | inr hq => exact hqr hq
