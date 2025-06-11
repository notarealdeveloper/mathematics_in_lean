import MIL.Common
import Mathlib.Data.Real.Basic

-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : (a * b) * c = (a * b) * c := by
  rw [mul_assoc]

-- To prove this super manually on purpose, just to understand the system better
example (a b c : ℝ) : a * b * c = c * b * a := by
  rw [mul_comm a b]
  rw [mul_comm (b * a) c]
  rw [← mul_assoc c b a]

/- Try these -/

-- Problem 1
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_assoc c b a]
  rw [mul_comm c (b * a)]
  rw [mul_assoc b a c]
-- That was fun

-- Problem 2
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

-- Problem 3
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm]
  rw [mul_assoc]
  rw [mul_comm c a]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

#check sub_self

-- This one was provided
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

-- I did this one
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [← mul_assoc, h, h', mul_assoc]

-- Same proof with "section" syntax
section
  variable (a b c d e f : ℝ)
  example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
    rw [h', ← mul_assoc, h, mul_assoc]
end

section

  variable (a b c : ℝ)

  #check a
  #check a + b
  #check (a : ℝ)
  #check mul_comm a b
  #check (mul_comm a b : a * b = b * a)
  #check mul_assoc c a b
  #check mul_comm a
  #check mul_comm

end

section
  variable (a b : ℝ)

  example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
    rw [mul_add, add_mul, add_mul]
    rw [← add_assoc, add_assoc (a * a)]
    rw [mul_comm b a, ← two_mul]

  example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
      (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
        rw [mul_add, add_mul, add_mul]
      _ = a * a + (b * a + a * b) + b * b := by
        rw [← add_assoc, add_assoc (a * a)]
      _ = a * a + 2 * (a * b) + b * b := by
        rw [mul_comm b a, ← two_mul]

  example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
    calc
      (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
        sorry
      _ = a * a + (b * a + a * b) + b * b := by
        sorry
      _ = a * a + 2 * (a * b) + b * b := by
        sorry

end

-- I added this one
section
  variable (a b : ℝ)

  example : (a+b)^2 = a^2 + 2*a*b + b^2 := by
  rw [pow_two]
  rw [add_mul]
  rw [mul_add]
  rw [mul_add]
  rw [mul_comm b a]
  rw [← pow_two a]
  rw [← pow_two b]
  rw [← add_assoc]
  rw [add_assoc (a ^ 2) (a * b) (a * b)]
  rw [← two_mul (a * b)]
  rw [mul_assoc 2 a b]
end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

  example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
    rw [add_mul, mul_add, mul_add, ← add_assoc]

  example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
    rw [add_mul, mul_sub, mul_sub, ← pow_two, mul_comm b a]
    group -- This was super helpful!

  #check pow_two a
  #check mul_sub a b c
  #check add_mul a b c
  #check add_sub a b c
  #check sub_sub a b c
  #check add_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

-- Given example
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

-- Doing it on my own (manually)
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp', mul_comm, ←two_mul, ←mul_assoc]

-- Doing it on my own (with more shortcuts)
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring


-- Alternatives to "ring" as the syntactic tactic for general simplifications
example : c * b * a = b * (a * c) := by
  ring

example : c * b * a = b * (a * c) := by
  linarith

example : c * b * a = b * (a * c) := by
  nlinarith

example : c * b * a = b * (a * c) := by
  group


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
