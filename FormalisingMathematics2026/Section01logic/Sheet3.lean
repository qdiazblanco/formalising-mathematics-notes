/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  apply h
  trivial

example : ¬True → False :=
  fun h => h True.intro


example : False → ¬True := by
  intro h
  exfalso
  exact h

example : False → ¬True :=
  fun h => False.elim (h)

example : ¬False → True := by
  intro h
  trivial

example : ¬False → True :=
  fun _ => True.intro


example : True → ¬False := by
  intro h hF
  exact hF

example : True → ¬False :=
  fun _ => fun h1 => h1


example : False → ¬P := by
  intro h
  exfalso
  exact h

example : False → ¬P :=
  fun h => False.elim (h)


example : P → ¬P → False := by
  intro hP hnP
  apply hnP
  exact hP

example : P → ¬P → False :=
  fun hP => fun hnP => hnP hP


example : P → ¬¬P := by
  intro hP hnP
  apply hnP
  exact hP

example : P → ¬¬P :=
  fun hP => fun hnP => hnP hP


example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ
  by_contra hP
  apply hPQ at hP
  exact hnQ hP

example : (P → Q) → ¬Q → ¬P :=
  fun hPQ hnQ hP => hnQ (hPQ hP)


example : ¬¬False → False := by
  intro h
  by_contra hnF
  exact h hnF

example : ¬¬False → False :=
  fun hnnF => hnnF (fun hF => hF)

example : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  exact hnnP hnP

example : ¬¬P → P := by
  intro hnnP
  by_contra hnP
  exact hnnP hnP

example : ¬¬P → P :=
  fun hnnP =>
    Or.elim (em P)
      (fun hP => hP)
      (fun hnP => False.elim (hnnP hnP))

example : (¬Q → ¬P) → P → Q := by
  intro h1 hP
  by_contra hnQ
  apply h1 at hnQ
  exact hnQ hP

example : (¬Q → ¬P) → P → Q := by
  intro h1 hP
  by_cases hQ : Q
  · exact hQ
  · apply h1 at hQ
    exfalso
    exact hQ hP

example : (¬Q → ¬P) → P → Q :=
  fun h1 hP =>
    Or.elim (em Q)
      (fun hQ => hQ)
      (fun hnQ => False.elim ((h1 hnQ) hP))
