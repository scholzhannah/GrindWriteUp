import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

-- for the first example
import Mathlib.Algebra.Group.Int.Even

-- for the second example
import Mathlib.Data.Finset.Defs

-- for the third example
import Mathlib.Data.Finset.Card


-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean


open TextbookTemplate

-- for cardinality symbol
open Finset

set_option pp.rawOnError true

#doc (Manual) "Basic usage of `grind`" =>


The `grind` tactic is meant to automatically provide proofs for easy goals.

Here are some examples where `grind` is used to prove simple lemmas in Mathlib:

```lean
lemma two_mul_ediv_two_of_even {n : ℤ} :
    Even n → 2 * (n / 2) = n := by
  grind
```

```lean
@[simp] lemma forall_mem_not_eq {α : Type*}
    {s : Finset α} {a : α} :
    (∀ b ∈ s, ¬ a = b) ↔ a ∉ s := by
  grind
```

The tactic appears very frequently in Mathlib to close simple side goals.

There is also a `grind` interactive mode that is still used very rarely in Mathlib.

Here is one example of its use in Mathlib:

```lean
theorem exists_subset_or_subset_of_two_mul_lt_card
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X)
    finish
```

This proof does not work without the interactive mode:

```lean +error (name := noInter)
theorem exists_subset_or_subset_of_two_mul_lt_card'
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind
```

This is what the ouput looks like when `grind` fails:

```leanOutput noInter
`grind` failed
case grind.2
α : Type u_1
inst : DecidableEq α
X Y : Finset α
n : ℕ
hXY : 2 * n < #(X ∪ Y)
h : ∀ (a : Finset α), #a ≤ n ∨ ¬a ⊆ X ∧ ¬a ⊆ Y
left : ¬X ∪ Y ⊆ X
right : ¬X ∪ Y ⊆ Y
w : α
h_3 : ¬(w ∈ X ∪ Y → w ∈ X)
w_1 : α
h_5 : ¬(w_1 ∈ X ∪ Y → w_1 ∈ Y)
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [cases] Case analyses
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints

[grind] Diagnostics
```

We will come back later to this example to figure out why this doesn't work and how to read the error message.

Similar to `simp`, you can write `grind?` to receive a squeezed `grind` call that limits which lemmas are used and on which terms splits are performed.

In our first example from above we get the suggestions:


```lean (name := grindOnly1)
lemma two_mul_ediv_two_of_even' {n : ℤ} :
    Even n → 2 * (n / 2) = n := by
  grind?
```

```leanOutput grindOnly1
Try these:
  [apply] grind only [= Int.even_iff]
  [apply] grind => instantiate only [= Int.even_iff]
```

You can see that it displays the necessary lemma used here.
We will learn what the `=` means later.

Sometimes the output will be a little more confusing:

```lean (name := grindOnly2)
@[simp] lemma forall_mem_not_eq' {α : Type*} {s : Finset α}
    {a : α} : (∀ b ∈ s, ¬ a = b) ↔ a ∉ s := by
  grind?
```

```leanOutput grindOnly2
Try these:
  [apply] grind only [#d39b]
  [apply] grind only
  [apply] grind => cases #d39b <;> done
```

You can see that this uses a so called "anchor" to refer to parts of the context that `grind` performed a case split on.
Unfortunately these don't show hover information here.
They do however in interactive mode.
We can use `finish?` like this:

```lean
@[simp] lemma forall_mem_not_eq'' {α : Type*}
    {s : Finset α} {a : α} :
    (∀ b ∈ s, ¬ a = b) ↔ a ∉ s := by
  grind =>
    finish?
```

To get a suggestion for a proof which does display the following information for the anchor: `(∀ (b : α), b ∈ s → ¬a = b) = (a ∈ s)`.
So we can see that `grind` performed a split on whether the equivalent propositions are each true or not.
