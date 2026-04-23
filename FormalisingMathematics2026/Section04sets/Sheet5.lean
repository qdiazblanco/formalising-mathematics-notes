/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  constructor <;> intro h
  · cases' h with h h <;> exact h
  · left; exact h

example : A ∩ A = A := by
  ext x ; constructor <;> intro h
  · exact h.1
  · constructor <;> exact h


example : A ∩ ∅ = ∅ := by
  ext x ; constructor <;> intro h
  · exact h.2
  · constructor
    · exfalso
      exact h
    · exact h


example : A ∪ univ = univ := by
  ext x ; constructor <;> intro h
  · trivial
  · right
    trivial


example : A ⊆ B → B ⊆ A → A = B := by
  intro hAB hBA
  ext x
  rw [subset_def] at *
  constructor <;> intro h
  <;> specialize hAB x
  <;> specialize hBA x
  · exact hAB h
  · exact hBA h


example : A ∩ B = B ∩ A := by
  ext x
  constructor
  <;> rintro ⟨h1,h2⟩
  <;> constructor
  <;> assumption


example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  constructor
  · rintro ⟨h1, ⟨h2,h3⟩⟩; exact ⟨⟨h1,h2⟩,h3⟩
  · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨h1, ⟨h2,h3⟩⟩


example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  · rintro (h | (h|h))
    · left; left; exact h
    · left; right; exact h
    · right; exact h
  · rintro ((h|h) | h)
    · left; exact h
    · right; left; exact h
    · right; right; exact h



example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · rintro (h | ⟨h1,h2⟩)
    <;> constructor
    <;> first | left; assumption | right; assumption
  · rintro ⟨(h1|h1),(h2|h2)⟩
    · left; exact h1
    · left; exact h1
    · left; exact h2
    · right; exact ⟨h1,h2⟩

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  exact inter_union_distrib_left A B C
