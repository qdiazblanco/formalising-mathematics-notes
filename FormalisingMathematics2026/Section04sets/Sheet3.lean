/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
  intro hnA hA
  exact hnA hA

example : x ∈ A → x ∉ A → False := by
  intro hA hnA
  exact hnA hA

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hAB hnB hA
  rw [subset_def] at hAB
  specialize hAB x
  exact hnB (hAB hA)

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  intro hx
  exact hx

example : x ∉ (∅ : Set X) := fun x => x

example : x ∈ Aᶜ ↔ x ∉ A := by
  rfl

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor <;> intro h
  · intro h1
    cases' h1 with x hx
    specialize h x
    exact hx h
  · intro x
    by_contra hnA
    apply h
    exact ⟨x,hnA⟩


example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by --mirar lo del PR
  constructor <;> intro h
  · intro h1
    cases' h with x hx
    exact (h1 x) hx
  · by_contra h2
    apply h
    intro x _
    apply h2
    use x
