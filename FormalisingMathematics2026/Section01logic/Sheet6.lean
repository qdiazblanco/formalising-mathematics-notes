/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : P → P ∨ Q :=
  fun hP => Or.intro_left _ hP

example : P → P ∨ Q :=
  fun hP => Or.inl hP


example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases hPoQ with
  | inl h => intro hPR hQR ; exact hPR h
  | inr h => intro hPR hQR ; exact hQR h


example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  obtain h | h := hPoQ
  · intro hPR hQR ; exact hPR h
  · intro hPR hQR ; exact hQR h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (h | h)
  · intro hPR hQR ; exact hPR h
  · intro hPR hQR ; exact hQR h

example : P ∨ Q → (P → R) → (Q → R) → R :=
  fun hPoQ hPR hQR =>
    Or.elim
      (hPoQ)
      (hPR)
      (hQR)


-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  rintro (h | h)
  · right; exact h
  · left; exact h

example : P ∨ Q → Q ∨ P :=
  fun hPoQ => hPoQ.symm

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
  Iff.intro
    (fun h =>
      Or.elim
        (h)
        (fun hPoQ =>
          Or.elim
            (hPoQ)
            (fun hP => Or.inl hP)
            (fun hQ => Or.inr (Or.inl hQ))
            )
        (fun hR => Or.inr (Or.inr hR))
    )
    (fun h =>
      Or.elim
        (h)
        (fun hP => Or.inl (Or.inl hP))
        (fun hQoR =>
          Or.elim
            (hQoR)
            (fun hQ => Or.inl (Or.inr hQ))
            (fun hR => Or.inr hR)
          )
    )


example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · rintro ((h | h) | h)
    · left; exact h
    · right; left; exact h
    · right; right; exact h
  · rintro (h | h | h)
    · left; left; exact h
    · left; right; exact h
    · right; exact h

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  rintro hPR hQS (hP | hQ)
  · left; exact hPR hP
  · right; exact hQS hQ

example : (P → Q) → P ∨ R → Q ∨ R := by
  rintro hPQ (hP | hR)
  · left; exact hPQ hP
  · right; exact hR

example : (P → Q) → P ∨ R → Q ∨ R :=
  fun hPQ hPoR => Or.elim
    (hPoR)
    (fun hP => Or.inl (hPQ hP))
    (fun hR => Or.inr hR)


example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  rintro ⟨hPR, hRP⟩ ⟨hQS, hSQ⟩
  constructor
  · rintro (hP | hQ)
    · left; exact hPR hP
    · right; exact hQS hQ
  · rintro (hR | hS)
    · left; exact hRP hR
    · right; exact hSQ hS

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor <;> intro h
  · constructor
    · intro h1
      apply h
      left
      exact h1
    · intro h1
      apply h
      right
      exact h1
  · rintro (hP | hQ)
    <;> obtain ⟨hnP, hnQ⟩ := h
    · exact hnP hP
    · exact hnQ hQ

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    rcases (em P) with hP | hnP
    · right
      intro hQ
      exact h ⟨hP, hQ⟩
    · left
      exact hnP
  · rintro (hnP | hnQ)
    · intro hPyQ
      exact hnP hPyQ.1
    · intro hPyQ
      exact hnQ hPyQ.2
