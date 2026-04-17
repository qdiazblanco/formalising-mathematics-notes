/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

#check And.intro (fun h : P => h) (fun h : P => h)
#check Iff.intro (fun h : P => h) (fun h : P => h)

#check ⟨fun (h : P) => h, fun (h : P) => h⟩


example : P ↔ P := by
  rfl

example : P ↔ P := by
  constructor
  <;> intro hP
  <;> exact hP

example : P ↔ P := Iff.intro (fun h : P => h) (fun h : P => h)

example : P ↔ P := {
  mp := fun h => h, mpr := fun h => h
}

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  constructor
  · exact h.2
  · exact h.1

lemma example1 : (P ↔ Q) → (Q ↔ P) :=
  fun hPQ => Iff.intro (hPQ.2) (hPQ.1)

example : (P ↔ Q) → (Q ↔ P) :=
  fun hPQ => {mp := hPQ.mpr, mpr := hPQ.mp}


example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;> intro h <;> constructor <;> first | exact h.1 | exact h.2

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;> intro h <;> exact h.symm

example : (P ↔ Q) ↔ (Q ↔ P) := {
  mp := example1 P Q
  mpr := example1 Q P
}

example : (P ↔ Q) ↔ (Q ↔ P) := {
  mp := fun hPQ => {mp := hPQ.mpr, mpr := hPQ.mp}
  mpr := fun hPQ => {mp := hPQ.mpr, mpr := hPQ.mp}
}

example : (P ↔ Q) ↔ (Q ↔ P) :=
  Iff.intro
    (fun hPQ => Iff.intro (hPQ.2) (hPQ.1))
    (fun hPQ => Iff.intro (hPQ.2) (hPQ.1))


example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  constructor <;> intro h
  · exact h2.1 (h1.1 h)
  · exact h1.2 (h2.2 h)

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  fun hPQ hQR => Iff.intro (fun h => hQR.1 (hPQ.1 h)) (fun h => hPQ.2 (hQR.2 h))

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
  fun hPQ hQR => {
    mp := fun h => hQR.1 (hPQ.1 h), mpr := fun h => hPQ.2 (hQR.2 h)
  }

  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩

example : P ∧ Q ↔ Q ∧ P :=
  Iff.intro
    (fun hPyQ => And.intro hPyQ.2 hPyQ.1)
    (fun hQyP => And.intro hQyP.2 hQyP.1)

example : P ∧ Q ↔ Q ∧ P := {
  mp := fun hPyQ => And.intro hPyQ.2 hPyQ.1
  mpr := fun hQyP => And.intro hQyP.2 hQyP.1
}

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor <;> first | intro ⟨⟨h1,h2⟩,h3⟩ | intro ⟨h1,⟨h2,h3⟩⟩
  · exact ⟨h1,⟨h2,h3⟩⟩
  · exact ⟨⟨h1,h2⟩,h3⟩

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R :=
  Iff.intro
  (fun h => And.intro (h.1.1) (And.intro h.1.2 h.2))
  (fun h => And.intro (And.intro h.1 h.2.1) (h.2.2))

example : P ↔ P ∧ True := by
  constructor <;> first | intro ⟨h1,h2⟩ | intro h
  · exact ⟨h, trivial⟩
  · exact h1

example : P ↔ P ∧ True :=
  Iff.intro
  (fun h => And.intro h True.intro)
  (fun h => h.1)


example : False ↔ P ∧ False := by
  constructor <;> first | intro ⟨h1, h2⟩ | intro h
  · exfalso; exact h
  · exact h2

example : False ↔ P ∧ False :=
  Iff.intro
  (fun h => False.elim h)
  (fun h => False.elim h.2)

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ hRS
  constructor <;> intro ⟨h1,h2⟩ <;> constructor
  · exact hPQ.1 h1
  · exact hRS.1 h2
  · exact hPQ.2 h1
  · exact hRS.2 h2

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
  fun hPQ hRS =>
    Iff.intro
      (fun h => And.intro (hPQ.1 h.1) (hRS.1 h.2))
      (fun h => And.intro (hPQ.2 h.1) (hRS.2 h.2))

example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  rcases (em P) with h | h
  · apply h1 at h
    apply h
    apply h2
    exact h
  · apply h
    apply h2
    exact h

example : ¬(P ↔ ¬P) :=
  fun h =>
    Or.elim
      (em P)
      (fun hP => (h.1 hP) hP)
      (fun hnP => hnP (h.2 hnP))
