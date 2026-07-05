import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

-- for the second example
import Mathlib.Data.Finset.Defs

-- for the third example
import Mathlib.Data.Finset.Card

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

-- for cardinality symbol
open Finset

open TextbookTemplate

set_option pp.rawOnError true

#doc (Manual) "Interactive mode" =>

# Example use case

We already saw the interactive mode at the very beginning.
Let's look at the example again to figure out why we needed interactive mode:

```lean
theorem exists_subset_or_subset_of_two_mul_lt_card'
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X)
    finish
```

We should first figure out what lemmas `grind` uses to prove the intermediate step. We can do this for example as follows:

```lean (name := question)
theorem exists_subset_or_subset_of_two_mul_lt_card''
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X) := by grind?
    finish
```

which gives us the following output

```leanOutput question
Try these:
  [apply] grind only [usr card_union_add_card_inter, usr card_sdiff_add_card_inter]
  [apply] grind =>
    instantiate only [usr card_union_add_card_inter]
    instantiate only [usr card_sdiff_add_card_inter]
    instantiate only [usr card_union_add_card_inter]
    ac
```

So we can see that `grind` uses the lemmas `Finset.card_union_add_card_inter` and `Finset.card_union_add_card_inter`

We can now look in Mathlib to see which patterns are specified for a these theorems. Those are:

```lean
grind_pattern card_union_add_card_inter => #(s ∪ t), s ∩ t
grind_pattern card_union_add_card_inter => s ∪ t, #(s ∩ t)
grind_pattern card_union_add_card_inter => #(s ∪ t), #s
grind_pattern card_union_add_card_inter => #(s ∪ t), #t
grind_pattern card_union_add_card_inter => #(s ∩ t), #s
grind_pattern card_union_add_card_inter => #(s ∩ t), #t
```

and

```lean
grind_pattern card_sdiff_add_card_inter =>
  #(s \ t), #(s ∩ t)
grind_pattern card_sdiff_add_card_inter => #(s \ t), #s
```

So we can see that both of these theorems won't be considered if there is neither a union, nor an intersection, nor a difference of sets present.
This means that this example uses interactive mode to guide e-matching.

# interactive mode tactic language

## Query commands

Interactive mode provides a few commands that let you query the state of `grind`.
These will basically output specific parts of the typical error messages.
These commands are: `show_splits`, `show_state`, `show_true`, `show_false`, `show_asserted` and `show_eqcs`.

We could use these in our example from above:

```lean (name := eqclass)
theorem exists_subset_or_subset_of_two_mul_lt_card'''
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X)
    show_eqcs
    finish
```

which shows us the following:

```leanOutput eqclass
[eqc] Equivalence classes
  [eqc] {#(X ∪ Y), #X + #(Y \ X)}
  [eqc] others
```



Write more about how to use the grind interactive mode.

Use the example from the beginning to illustrate why we might need interactive mode.

Show some of the commands you can do there. -> See Examples from talk by Kim Morrison
