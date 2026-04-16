/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

-- Here are a few ways to break down a conjunction:

-- You can use `obtain`
example : P ∧ Q → P := by
  intro h
  obtain ⟨left, right⟩ := h
  exact left

-- or `rcases` (which is just `obtain` but with a slightly different syntax)
example : P ∧ Q → P := by
  intro h
  rcases h with ⟨left, right⟩
  exact left

/--
The pattern `intro h` then `rcases h with ...` is so common that it has an abbreviation as
`rintro ...`, so you could also do
-/
example : P ∧ Q → P := by
  rintro ⟨left, right⟩
  exact left

-- or you can get the relevant part out directly using `.left`
example : P ∧ Q → P := by
  intro h
  exact h.left

-- or by using `.1` (the first part)
example : P ∧ Q → P := by
  intro h
  exact h.1

example : P ∧ Q → Q := by
  intro h
  exact h.2

example : P ∧ Q → Q :=
  fun h => h.2

example : (P → Q → R) → P ∧ Q → R := by
  intro h1 h2
  exact (h1 h2.1) h2.2

example : (P → Q → R) → P ∧ Q → R :=
  fun h1 h2 => (h1 h2.1) h2.2

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  -- After the `constructor` tactic, we have *2 goals* for the first time!
  -- We use centre-dots, typed as `\.` to help Lean (and the reader) figure out when we're done
  · assumption
  · assumption

-- If the exact same tactic works to finish both goals, these can be combined:
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  all_goals assumption

-- or alternatively
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor <;> assumption

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro hPyQ
  constructor
  · exact hPyQ.2
  · exact hPyQ.1

example : P ∧ Q → Q ∧ P := by
  intro h <;> constructor <;> first | exact h.2 | exact h.1

example : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨h.2, h.1⟩

example : P ∧ Q → Q ∧ P :=
  fun h => And.intro h.2 h.1

example : P → P ∧ True :=
  fun hP => And.intro hP True.intro

example : False → P ∧ False := by
  intro hF
  constructor
  · exfalso; exact hF
  · exact hF

example : False → P ∧ False :=
  fun hF => False.elim hF

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2
  constructor <;> first | exact h1.1 | exact h2.2

example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro h1 h2; exact ⟨h1.1, h2.2⟩

example : P ∧ Q → Q ∧ R → P ∧ R :=
  fun h1 h2 => And.intro h1.1 h2.2

example : (P ∧ Q → R) → P → Q → R := by
  intro h1 h2 h3
  apply h1
  exact ⟨h2, h3⟩

example : (P ∧ Q → R) → P → Q → R :=
  fun h1 h2 h3 => h1 (And.intro h2 h3)
