/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

-- This is a chapter that's included
import TextbookTemplate.Nat

-- for the first example
import Mathlib.Algebra.Group.Int.Even

-- for the second example
import Mathlib.Data.Finset.Defs

-- for the third example
import Mathlib.Data.Finset.Card

-- for a category theory example
import Mathlib.CategoryTheory.Iso

-- for a distribution example
import Mathlib.Analysis.Distribution.Support

-- for a list example
import Mathlib.Data.Bool.Count

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean


open TextbookTemplate

-- for the examples
open Finset CategoryTheory Distribution

set_option pp.rawOnError true

#doc (Manual) "A short introduction to the `grind` tactic" =>

%%%
authors := ["Hannah Scholz"]
%%%

{index}[overview]
This is the writeup for the talk about the `grind` tactic for the Graduate Seminar "Advanced Topics in Formalised Mathematics" taught by Michael Rothgang in Bonn in the summer term 2026. This document is mostly based on the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/), so look there for further reading.

# Basic usage of `grind`

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

--```savedLean
--@[simp] lemma forall_mem_not_eq3 {α : Type*}
--    {s : Finset α} {a : α} :
--    (∀ b ∈ s, ¬ a = b) ↔ a ∉ s := by
--  grind =>
--    cases #d39b <;> done
--```


# Intuition of how `grind` works

All descriptions of `grind` tell you to imagine that `grind` works with a "virtual whiteboard".
First `grind` writes all the hypotheses and the goal on the whiteboard.
All proofs that `grind` produces are by contradiction, so it negates the goal and doesn't further distinguish it from the hypotheses.

Afterwards, `grind` uses several different engines to find a proof, i.e. discover a contradiction.
To ensure that these engines can work together, they all put discovered facts back on the whiteboard, so that another engines may use them.

This document is supposed to be a short introduction on how to use `grind` in your projects. So we will only discuss parts that especially relevant to either a basic understanding of `grind` or to its usage.

# Understanding error messages

We now want to understand how to read the error messages of `grind`.
This is the error message from before:

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

At the top you can see the goal state that `grind` got stuck on.
If there are several open goals, it only displays the first one.
You can see here that we are in a case generated by a case split somewhere.
To see how we got there we can set the option `trace.grind.split` to true to get

```savedLean (name := traceSplit) +error -show
set_option trace.grind.split true in
theorem exists_subset_or_subset_of_two_mul_lt_card''
    [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind
```

```leanOutput traceSplit
[grind.split] #(X ∪ Y) ≤ n ∨ ¬X ∪ Y ⊆ X ∧ ¬X ∪ Y ⊆ Y, generation: 1
```

Here we can see the statement `grind` has split on, which is `h` applied to `X ∪ Y`.

Question: What does the asserted facts section actually do?

The next thing to understand is that `grind` doesn't work by rewriting with terms that it considers to be equal.
Instead, it maintains equivalence classes.
This is also a way to discover contradictions.
If two different constructors of the same type (e.g. `True` and `False` or `some a` and `none`) are put in the same equivalence class, `grind` has found a contradiction and finishes the proof.

The two main equivalence classes are those of true and false propositions which you can see as output in the error message.
It can also show other equivalence classes.
That isn't the case in our example but it is here:

```lean +error (name := missingHyp)
example (n k : ℕ) (h1 : 2 * n = k) : k = 5 := by
  grind
```

Of course this statement is clearly missing a hypothesis for it to be true.
In a more complicated example you might not directly see the missing hypothesis but could maybe figure it out by looking at the error message:

```leanOutput missingHyp
`grind` failed
case grind
n k : ℕ
h1 : 2 * n = k
h : ¬k = 5
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Lean.Grind.Ring.OfSemiring.Q ℕ`
```

You can see that here we have more equivalence classes than just those of true and false propositions.

Next, our error message from the beginning of this section has a section on cases.
Here you can see on which terms case splits were performed.
We will get into case splits in the next section.

Afterwards there is a section called "ematch".
E-matching is how `grind` uses tagged lemmas.
We will discuss this in detail in a later section.

Then both error messages feature sections called `cutsat` and the later error message in this section has a section about `ring`.
These are two examples of satellite solvers that `grind` employs to solve problems of specific types.
They are different from the Mathlib tactics of the same names because `grind` is supposed to work Mathlib-free.
You can however imagine them to work similarly.

# Basic derivations of new facts

First we will consider the basic ways that `grind` uses to derive new facts.
With "basic" I mean that it neither uses any lemmas nor specialized solvers.
We will not go into too much detail here because this part of `grind` doesn't provide too much interactivity for the user.

## Congruence closure

Whenever there is a function `f` in the context, `grind` will equate `f a₁ ... aₙ` and `f b₁ ... bₙ` whenever `a₁ = bₙ`, ..., `aₙ = bₙ`.
It does this always when there is something new to add.

## Constraint Propagation

For all the propositions in the {lean}`True` and {lean}`False` equivalence classes, there are of course basic facts, e.g. about logical combinations of these statements, that can be derived.
This is what constraint propagation does.
Among others, it considers the following:
* Boolean Connectives (e.g. a conjunction is true then both conjuncts are true)
* Inductive Types (e.g. if `some a = some b` then `a = b`)
* Projections (e.g. if `(a₁, a₂) = (b₁, b₂)` then `a₁ = a₂`)

Questions:
* How do coercions work?

## Case Splits

We already saw that `grind` can perform case splits.
It does so mainly on `if`-expressions and `match`-statements.

Excessive case splits can make `grind` very slow.
You can use the option `trace.grind.split` to inspect the splits `grind` performs and determine whether this might be the reason your `grind` call is slow.
If this is the case, you can use `grind -splitIfs` and `grind -splitMatch` to disable certain types of splits or specify the maximal depth of the search tree given by the splits with `grind (splits := n)`. The default value here is 9. You can also use this to increase the depth which you should only do if your proof does really require more splits.

You can also label your own inductive definitions with the `grind cases` attribute to enable case splitting on them. Lean itself does this for example for {lean}`Or` and {lean}`Sum`. Mathlib basically doesn't use this feature, yet. I think this is mainly because people tag lemmas instead to achieve similar effects when needed.

# E-matching

As said before, e-matching is how `grind` uses the lemmas tagged by users.
This of course provides a lot of interactivity, so we will discuss this in detail.

The basic functionality of e-matching is the following: `grind` maintains an index of tagged lemmas an corresponding patterns. If a pattern matches the terms in the context, `grind` tries to apply the theorem to the relevant terms and write the result on the whiteboard.

E-matching can be very powerful if whole libraries are tagged thoroughly but it can of course also be very slow, especially if patterns are chosen to be to general.
This is why `grind` provides a lot of customisability and diagnostic tools here.

## General

An expression is indexable if it starts with a constant that is anything but {lean}`Eq`, {lean}`HEq`, {lean}`Iff`, {lean}`And`, {lean}`Or`, and {lean}`Not`. For example an expression of the form `t = s` where `t` and `s` are some subexpressions cannot be used as a pattern.

In addition to simply looking whether a single pattern can be found in the context, theorem can also have multi-patterns. Here multiple patterns need to be found in the context before the theorem is applied.

Here is an example from Mathlib where a multi-pattern is used:

```lean
theorem card_ne_zero_of_mem {α : Type*} {s : Finset α}
    {a : α} (h : a ∈ s) : #s ≠ 0 :=
  (not_congr card_eq_zero).2 <| ne_empty_of_mem h
```

Here we cannot just use `#s ≠ 0` as a pattern because it doesn't cover `a`. We also probably don't want to try to apply this theorem whenever a statement of the form `a ∈ s` is on the whiteboard So Mathlib specifies the multi-pattern `a ∈ s, #s` here. So the fact that `#s ≠ 0` will be added to the context, whenever there is a statement of the form `a ∈ s` on the whiteboard and somewhere on the whiteboard the cardinality of `s` is mentioned.

It is important to note that a multi-pattern is not the same as specifying multiple patterns.
In a multi-pattern all included patterns need to match.
When multiple patterns are specified, one of them needs to match in order for the theorem to be used.

## Specifying default patterns

There is a list of modifiers to the `grind` attribute that can be used to specify patterns using different algorithms.
Here is an overview of the options with examples from Mathlib.
You can use `grind?` to see which pattern is picked.
Arguments of the lemma are indexed with numbers starting with 0 for the first argument.

Some of these strategies require that a pattern can only be used when it covers all the arguments of the theorem, i.e. if all the arguments are fixed by the pattern. A multi-pattern can then only be used if every argument is covered by at least one of the included patterns. This is so that a theorem isn't applied to eagerly.

### `=`

This instructs `grind` to use the left side of the goal (if it is an equality) as a pattern. It fails if not all arguments are covered in this way.
Here is an example from Mathlib:

```lean (name := question1)
@[grind? =]
lemma even_iff {n : ℤ} : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ ↦ by simp [← Int.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩
```
where `grind?` outputs
```leanOutput question1
even_iff: [@Even `[ℤ] `[Int.instAdd] #0]
```

`#0` refers to the first argument, so `n`.

An equivalence is treated as an equality of proposition, so we can also use modifier here. This theorem is used whenever there is a statement `Even n` on the whiteboard.

### `=_`

This instructs `grind` to use the right side of the goal (if it is an equality) as a pattern. It fails if not all arguments are covered in this way.

I could find an example in Mathlib so here is an example from Lean:

```lean (name := question2)
@[grind? =_]
theorem toList_toArray {α : Type*} {n : ℕ}
    {xs : Vector α n} : xs.toArray.toList = xs.toList :=
  rfl
```

with the `grind?` output

```leanOutput question2
toList_toArray: [@Vector.toList #2 #1 #0]
```

### `_=_`

This modifier adds two patterns corresponding to `=` and `=_`. Thus the theorem can be used if the left or the right side matches something on the whiteboard.

Here is an example from Mathlib:

```lean (name := question3)
@[simp, grind? _=_]
theorem trans_symm {C : Type*} [Category C] {X Y Z : C}
    (α : X ≅ Y) (β : Y ≅ Z) :
    (α ≪≫ β).symm = β.symm ≪≫ α.symm :=
  rfl
```

with the `grind?` output

```leanOutput question3
trans_symm: [@Iso.symm #6 #5 #4 #2 (@Iso.trans _ _ #4 #3 #2 #1 #0)]
```
```leanOutput question3
trans_symm: [@Iso.trans #6 #5 #2 #3 #4 (@Iso.symm _ _ #3 #2 #0) (@Iso.symm _ _ #4 #3 #1)]
```

Here we can see that the modifier produced two patterns. So if either sides of the equality are present somewhere on the whiteboard, `grind` will use this theorem to add the other one to the same equivalence class.

### `→`

With this pattern, `grind` will start with the hypotheses starting with the first.
It will add these hypotheses to a multi-pattern if they cover a previously not covered argument.

Here is an example from Mathlib:

```lean (name := question4)
@[aesop safe forward, grind? →]
lemma EqOn.eq_of_mem {α β : Type*} {s : Set α}
    {f₁ f₂ : α → β} {a : α} (h : s.EqOn f₁ f₂)
    (ha : a ∈ s) : f₁ a = f₂ a :=
  h ha
```

with the `grind?` output

```leanOutput question4
eq_of_mem: [@Set.EqOn #7 #6 #4 #3 #5, @Membership.mem _ _ _ #5 #2]
```

This time, the modifier produced a multi-pattern. You can see that this differs from the example above: multi-patterns are presented as lists with more than one entry, while multiple patterns are presented as different lists. So this theorem will only be used if `grind` finds both an expression `s.EqOn f₁ f₂` and `a ∈ s` on the whiteboard.

### `.`

This is the default strategy. Here `grind` picks expressions for a multi-pattern by first considering the conclusion and then the hypotheses starting with the first one.
(We introduce this last because I could find no easy examples in Mathlib.)

Here is an example from Mathlib:

```lean (name := question0)
@[grind? .]
theorem isClosed_dsupport {α β F V : Type*} [FunLike F α β]
    [TopologicalSpace α] [Zero β] [Zero V] {f : F → V} :
    IsClosed (dsupport f) := by
  grind [dsupport, isClosed_sInter]
```

with the `grind?` output

```leanOutput question0
_root_.isClosed_dsupport: [@IsClosed #8 #3 (@dsupport _ #7 #6 #5 #4 _ #2 #1 #0)]
```

### Further modifiers

There a more modifiers that tell `grind` the order in which it should pick patterns such as `←`, `⇒` and `⇐`. Additionally, there are some modifiers to be used for specific types of theorems such as `ext` for extensionality theorems and `inj` for theorems showing injectivity.

Learn more about these modifiers in the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/E___matching/#e-matching).

### `grind!`

Sometimes you want to pick a subterm or subexpression as a pattern. If you want to be as "aggressive" as possible with this, you can pick minimal indexable subexpression.
An expression is minimal indexable if it has no indexable subexpressions (respecting additionally some priorities).
You can use the `grind!` attribute in the same way as `grind` with the modifiers described above.

Here is an example from the Language Reference that shows why you might prefer `grind!` in some situations. Consider the following setup:

```lean (name := try1)
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind? .]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```

where the selected pattern is

```leanOutput try1
gf: [g (f #0)]
```

Then the following cannot be proven by `grind` because the chosen pattern does not appear:

```lean +error
example {a b c : ℕ} (h₁ : f b = a) (h₂ : f c = a) :
    b = c := by
  grind
```

Clearly, we need to trigger the use of `fg` already when `f x` appears.
If we use `grind!` in the tagging above, this works:

```lean (name := try2)
@[grind!? .]
theorem gf' (x : Nat) : g (f x) = x := by
  simp [f, g]

example {a b c : ℕ} (h₁ : f b = a) (h₂ : f c = a) :
    b = c := by
  grind
```

This works because `g (f x)` isn't minimally indexable and thus the following pattern is chosen

```leanOutput try2
gf': [f #0]
```

Notice that this pattern doesn't cover the argument `g`. Above we discussed that some modifiers such as `=` don't allow this. So if you were to use the modifier `=` instead of `.` in this example, `grind!` wouldn't change anything.

## Custom Patterns

Sometimes the default algorithms from above do not give you the desired pattern.
Then you can use `grind_pattern` to specify a pattern yourself.

Here is a basic example from Mathlib:

```lean
theorem mul_left_iff {M : Type*} [Monoid M] {a b : M}
    (ha : IsUnit a) : IsUnit (a * b) ↔ IsUnit b :=
  show IsUnit (ha.unit * b) ↔ _ by simp [-IsUnit.unit_spec]

grind_pattern mul_left_iff => IsUnit a, IsUnit (a * b)
```

You can see that this is specifying a multi-pattern. This theorem is only used by `grind` if it finds terms of the shape `IsUnit a` and `IsUnit (a * b)` on the whiteboard.

If you want to specify multiple patterns you can do:

```lean -show
open List
```

```lean
@[simp]
theorem count_false_add_count_true' (l : List Bool) : count false l + count true l = length l :=
  count_not_add_count l true

grind_pattern count_false_add_count_true' => count false l
grind_pattern count_false_add_count_true' => count true l

```

So this theorem is used by `grind` if it find either `count false l` or `count true l` on the whiteboard.

## Picking a pattern

So how do you pick a pattern for your theorem?

Firstly, if you just tag it with `@[grind]` without any modifiers, there will be a helpful message suggesting different modifiers and the patterns they would generate.

So for example in the example above we get:

```lean (name := try3)
@[grind]
theorem gf'' (x : Nat) : g (f x) = x := by
  simp [f, g]
```

We get the following suggestions:

```leanOutput try3
Try these:
  [apply] [grind =] for pattern: [g (f #0)]
  [apply] [grind! .] for pattern: [f #0]
```

where we could then directly consider whether we might prefer the second option.

Talk about how to identify bad tagging.

## Further Examples

Show examples where it is non-trivial what pattern to pick

# Satellite Solvers

# Grind Interactive Mode

Write more about how to use the grind interactive mode.

# Random further things

## Style and Conventions

## Difference to other tactics

## Defining new tactics using `grind`

# Further Questions

* Where does grind introduce variable for foralls and exists? Is this in case splitting?

# Lean Code

The tools in this section come from the Verso namespace `Verso.Genre.Manual.InlineLean`.

The {lean}`lean` code block allows Lean code to be included in the text.
It is elaborated in the context of the text's elaboration.

```lean
inductive NatList where
  | nil
  | cons : Nat → NatList → NatList
```

Use the {lean}`leanSection` directive to create a Lean section that delimits scope changes.
The {lean}`lean` role allows Lean terms to be included as inline elements in paragraphs.
Use {lean}`name` to refer to a name that can't be easily elaborated as a term, e.g. due to implicit parameters or type classes.

## Saved Lean Code

The tools in this section come from the Verso namespace `TextbookTemplate` in the module `TextbookTemplate.Meta.Lean`.

The {lean}`savedLean` code block is just like the {lean}`lean` block, except it additionally saves the contents to a file when the book is built.
The code is saved to the output directory, in the subdirectory `example-code` (by default, this is `_out/example-code`), with its filename being that of the file in which it is edited.
Use {lean}`savedImport` to save code for the file header.

```savedComment
Here's some commentary for the file
```
```savedLean
def x : Nat := 15
```

When named, the code block's output is saved.
It can be both checked and included in the document using {lean}`leanOutput`:

```savedLean (name := xVal)
#eval x
```
```leanOutput xVal
15
```

Expected error messages must be indicated explicitly:
```lean +error (name := yVal)
#eval y
```
```leanOutput yVal
Unknown identifier `y`
```

{include 1 TextbookTemplate.Nat}

# Notes

Use {lean}`margin` to create a marginal note.{margin}[Marginal notes should be used like footnotes.]

# Citations

Cite works using {lean}`citet`, {lean}`citep`, or {lean}`citehere`.
They take a name of a citable reference value as a parameter.
References should be defined as values, typically in one module that is imported (similar to the role of a `.bib` file in LaTeX).

Textual citations, as with {citet someThesis}[], look like this.
Parenthetical {citep someArXiv}[] looks like this.
Use {lean}`citehere` to literally include the cite rather than making a margin note, e.g. {citehere somePaper}[].
Literally-included cites are mostly useful when performing citation inside a margin note.

# Section References
%%%
tag := "sec-ref"
%%%

Sections with tags can be cross-referenced.
They additionally gain permalink indicators that can be used to link to them even if the document is reorganized.
Tags are added in section metadata, e.g.
```
%%%
tag := "my-tag"
%%%
```
They can be linked to using {lean}`ref`.
Here's one to {ref "sec-ref"}[this section].



# Viewing the Output

Verso's HTML doesn't presently work correctly when opened directly in a browser, so it should be served via a server.{margin}[This is due to security restrictions on retrieved files: some of the code hovers are deduplicated to a JSON file that's fetched on demand.]
One portable way to do this is documented in the root of this repository.

# Using an Index

{index}[index]
The index should contain an entry for “lorem ipsum”.
{index}[lorem ipsum] foo
{index (subterm := "of lorem")}[ipsum]
{index (subterm := "per se")}[ipsum]
{index}[ipsum]
Lorem ipsum dolor {index}[dolor] sit amet, consectetur adipiscing elit, sed {index}[sed] do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris {index}[laboris] {see "lorem ipsum"}[laboris] {seeAlso "dolor"}[laboris] nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

This is done using the `{index}[term]` syntax. Sub-terms {index (subterm := "sub-term")}[entry] can be added using the `subterm` parameter to `index`.

Multiple index {index}[index] targets for a term also work.

{ref "index"}[Index link]


# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
