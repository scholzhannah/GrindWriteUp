import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

-- for the first example
import Mathlib.Algebra.Group.Int.Even

-- for the second example
import Mathlib.Data.Finset.Defs

-- for the third example
import Mathlib.Data.Finset.Card

-- for the graph example
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

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

So we can see that `grind` uses the lemmas `Finset.card_union_add_card_inter` and `Finset.card_union_add_card_inter`.
The `usr` tells us that is uses patterns manually specified via `grind_pattern`.

We can now look for these patterns in Mathlib. We find:

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

# Interactive mode tactic language

## Usual tactic language

A lot of the features of Lean's tactic language also work in the interactive mode.
For example `all_goals`, `<;>` and `have` can be used a expected (where the latter doesn't usually need a proof as we have seen). You can find more examples in the [Lean 4.25.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.25.0/#The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind)

## `grind`-specific tactics

There are a few tactics that are specific to the interactive mode or behave differently as in the usual Lean tactic language.

Examples here are the satellite solvers which you can manually instruct `grind` to use by writing their name, so `ring`, `linarith` and so on. Again, in the `grind` interactive mode these don't refer to the Mathlib tactic under the same name.
Another tactic that behaves slightly differently is `cases`. In interactive mode, this expects an anchor. You can have the possible anchors displayed with `cases?`.

Here is an example:

```lean (name := casequestion) +error
@[simp] lemma forall_mem_not_eq {α : Type*} {s : Finset α}
    {a : α} : (∀ b ∈ s, ¬ a = b) ↔ a ∉ s := by
  grind =>
    cases?
```

which gives the output:

```leanOutput casequestion
Try these:
  [apply] cases #d39b for
    (∀ b ∈ s, ¬a = b) = (a ∈ s)
```

that shows us the only possible case that we could split on here.

Another tactic that we already saw is `finish`. This basically instructs `grind` to use all the tools at its disposal (you can imagine `grind` to do the same thing as `grind => finish`). In the proof at the beginning of this section we used `have` to provide a hint and then `finish` to tell `grind` to do the rest itself. We also briefly saw `finish?` at the beginning of this document. This provides you with a more detailed proof. Here is an example:

```lean (name := finishquestion)
lemma two_mul_ediv_two_of_even' {n : ℤ} :
    Even n → 2 * (n / 2) = n := by
  grind =>
    finish?
```

which gives the output

```leanOutput finishquestion
Try these:
  [apply] instantiate only [= Int.even_iff]
  [apply] finish only [= Int.even_iff]
```

Here we can see another command: `instantiate` tells `grind` to use e-matching to apply theorems. Additionally one can specify additional theorems to be tried even if they are not tagged with `grind` or have no matching pattern.

In the following example, Mathlib uses the proof `:= by grind [SimpleGraph.adjMatrix_apply]` as we saw in a previous section. But we could also prove it like this:

```lean
theorem isAdjMatrix_adjMatrix''' (α : Type*) {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] [Zero α]
    [One α] : (G.adjMatrix α).IsAdjMatrix where
  zero_or_one := by
    grind =>
      instantiate [SimpleGraph.adjMatrix_apply]
      finish
```

## Query commands

Interactive mode also provides a few commands that let you query the state of `grind`.
These will basically output specific parts of the typical error messages.
These commands are: `show_splits`, `show_state`, `show_true`, `show_false`, `show_asserted` and `show_eqcs`.

We could use these in our example from above:

```lean (name := eqclass)
theorem exists_subset_or_subset_of_two_mul_lt_card''''
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
