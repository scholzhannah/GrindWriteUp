import VersoManual

-- This is a chapter that's included
import TextbookTemplate.Basic
import TextbookTemplate.Error
import TextbookTemplate.EMatching
import TextbookTemplate.Satellite
import TextbookTemplate.Interactive
import TextbookTemplate.Misc

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean


open TextbookTemplate

set_option pp.rawOnError true

#doc (Manual) "A short introduction to the `grind` tactic" =>

%%%
authors := ["Hannah Scholz"]
%%%

{index}[overview]
This is the write-up for the talk about the `grind` tactic for the Graduate Seminar "Advanced Topics in Formalised Mathematics" taught by Michael Rothgang in Bonn in the summer term 2026. This document is mostly based on the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/), so look there for further reading.

{include 1 TextbookTemplate.Basic}

# Intuition of how `grind` works

All descriptions of `grind` tell you to imagine that `grind` works with a "virtual whiteboard".
First `grind` writes all the hypotheses and the goal on the whiteboard.
All proofs that `grind` produces are by contradiction, so it negates the goal and doesn't further distinguish it from the hypotheses.

Afterwards, `grind` uses several different engines to find a proof, i.e. discover a contradiction.
To ensure that these engines can work together, they all put discovered facts back on the whiteboard, so that another engines may use them.

This document is supposed to be a short introduction on how to use `grind` in your projects. So we will only discuss parts that especially relevant to either a basic understanding of `grind` or to its usage.

{include 1 TextbookTemplate.Error}

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

{include 1 TextbookTemplate.EMatching}

{include 1 TextbookTemplate.Satellite}

{include 1 TextbookTemplate.Interactive}

{include 1 TextbookTemplate.Misc}

# Sources and Resources

As mentioned many times, you should read the [relevant section in the Language Reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/) to get a general overview of how `grind` works with a lot more detail than presented here.

For `grind` interactive mode see [this talk by Kim Morrison](https://www.youtube.com/watch?v=sx6lFrsaBJU) (especially to see examples) and the [Lean 4.25.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.25.0/#The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Interactive-mode).

For custom `grind` sets and `local grind` see the [Lean 4.28.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.28.0/#The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--User-Defined-Grind-Attributes).

For style suggestions for `grind` see these [suggestions by Chris Henson](https://github.com/chenson2018/leanprover-community.github.io/blob/grind-style/templates/contribute/grind.md).
