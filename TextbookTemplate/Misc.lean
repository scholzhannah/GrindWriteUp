import VersoManual
import TextbookTemplate.Meta.Lean

-- for the first example
import Mathlib.Algebra.Group.Int.Even

-- for the second example
import Mathlib.Data.Finset.Defs

-- for the third example
import Mathlib.Data.Finset.Card

-- for the graph theory examples
import Mathlib.Combinatorics.SimpleGraph.Circulant

-- for compactness example
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

--cannot be in the same file
import TextbookTemplate.AddAttr

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

-- for cardinality symbol
open Finset SimpleGraph

open TextbookTemplate

set_option pp.rawOnError true

#doc (Manual) "Miscellaneous further things" =>

# Local `grind`

As mentioned before, one needs to be careful to not tag too many lemmas. However, sometimes there are lemmas that are too general for a global `grind` lemmas but are convenient to use on a smaller scale. For example, when setting up the basic theory around a definition, one might want to unfold specific definitions or use certain basic lemmas.

For theorems this is facilitated the following way: you can tag a theorem with `@[local grind *]` (where `*` is a pattern modifier) or use `local grind_pattern` to specify a `grind` pattern as usual but allow it to only be used in the file where it is defined. Here is an example from Mathlib (the comments are part of Mathlib as well):

```lean
theorem Finset.card_le_card' {α : Type*} {s t : Finset α} :
    s ⊆ t → #s ≤ #t :=
  Multiset.card_le_card ∘ val_le_iff.mpr

-- This pattern is unreasonable to use generally,
-- but it's convenient in this file.
-- (Note that we turn it on again later in this file.)
local grind_pattern Finset.card_le_card' => #s, #t
```

To use definitions locally you can use the `grind` tactic with `+locals`. This allows `grind` to unfold all definitions from the current file. It is a little hard to include an example here. But you can find one in Mathlib [here](https://github.com/leanprover-community/mathlib4/blob/e2361c1bebbe457b1b699a67f685f675801a6da0/Mathlib/Combinatorics/SimpleGraph/CycleGraph.lean#L152-L156).

# Defining custom `grind` sets

Similarly, you might want to use a certain lemma for `grind` only in a certain situation, for example only when proving things about a specific object. This is possible by defining your own `grind` attribute using `register_grind_attr`.

For example, Mathlib has the following. (Not included as Lean code because to work the attribute has to be defined in a different file to the ones using it.)

```
/-- The `compactness` attribute is a custom grind-set
specialized to prove that sets are compact.
It is called by the `compactness` tactic. -/
register_grind_attr compactness

/-- The `closedness` attribute is a custom grind-set specialized to prove that sets are closed.
It is called by the `closedness` tactic. -/
register_grind_attr closedness
```


But there are currently no usage examples since this a relatively new addition. A [subsequent PR by Floris van Doorn](https://github.com/leanprover-community/mathlib4/pull/39371) does however show what using this could look like:

```lean
attribute [compactness .] isCompact_Icc

@[to_dual self, simp, closedness =]
theorem closure_Icc' {α : Type*} [TopologicalSpace α]
    [Preorder α]  [OrderClosedTopology α] (a b : α) :
    closure (Set.Icc a b) = Set.Icc a b :=
  isClosed_Icc.closure_eq
```

and then it can be used like this:


```lean
example : IsCompact <|
    closure (Set.Icc (1 : ℝ) (3 : ℝ)) := by
  grind only [compactness, closedness]
```

In this case there is also some code on top to be able to use these `grind` sets as there own tactic. So you can do:

```lean
example : IsCompact <| Set.Icc (1 : ℝ) (3 : ℝ) := by
  compactness
```

This is however not provided by `grind` and needs to be added manually.

# Style and Conventions

Since `grind` is a very new tactic, there is no real consensus on style yet. In particular, the style guide doesn't provide any guidelines for `grind`. So take everything presented in this section with a grain of salt. However, ideas are beginning to emerge which we want to discuss some here.
The ideas presented here mainly come from [Chris Henson here](https://github.com/chenson2018/leanprover-community.github.io/blob/grind-style/templates/contribute/grind.md).

## Readability

One big issue with `grind` is readability. Since it can be used to prove so many different things, it can be hard to decipher what it is used to prove in a specific instance. Here are a few rules that follow from this:

* Tactics with names that better describe their purpose are to be preferred over `grind`. For example, if there is an equally short and fast proof using `ring`, `simp` or `linarith`, that proof should be used instead. Similarly, if the goal just follows from a single lemma.
* When providing additional lemmas to `grind` it should ideally be very clear where those are used. For example, if the forward and backward direction of an iff-statement uses different lemmas, it is clearer to have two different `grind` proofs rather than one.
* For the same reason as the above point, proofs of the form `apply foo; grind [bar]` should usually not be golfed into `grind [foo, bar]`.

## Performance

If a proof repeatedly uses `grind` to prove different `have` statements, this means that `grind` will do the same basic setup multiple times. It is usually better to use interactive mode to circumvent this.
Our example from before:

```lean
theorem exists_subset_or_subset_of_two_mul_lt_card5
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X)
    finish
```

could also have been written like this:

```lean
theorem exists_subset_or_subset_of_two_mul_lt_card6
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  have : #(X ∪ Y) = #X + #(Y \ X) := by grind
  grind
```

## Maintainability

Since `grind` is always a finishing tactic it should in general not be squeezed for the same reason that we don't squeeze terminal `simp`s.

There are bugs in `grind` that makes it so that `grind?` sometimes doesn't return a working proof. This is an issue when trying to fix `grind` calls that break during Mathlib updates.
Mathlib tracks these cases in the [Weekly linting log](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Weekly.20linting.20log/) but currently doesn't refactor these `grind` calls. Instead Mathlib is waiting for a bug fix. (See [this PR](https://github.com/leanprover-community/mathlib4/pull/40023) for the discussion on this decision.)
