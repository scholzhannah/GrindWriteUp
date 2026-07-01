import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

-- This is a chapter that's included
import TextbookTemplate.Nat
import TextbookTemplate.Basic
import TextbookTemplate.Error
import TextbookTemplate.EMatching

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
This is the writeup for the talk about the `grind` tactic for the Graduate Seminar "Advanced Topics in Formalised Mathematics" taught by Michael Rothgang in Bonn in the summer term 2026. This document is mostly based on the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/), so look there for further reading.

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

# Satellite Solvers

# Grind Interactive Mode

Write more about how to use the grind interactive mode.

Use the example from the beginning to illustrate why we might need interactive mode.

Show some of the commands you can do there. -> See Examples from talk by Kim Morrison

# Random further things

## Style and Conventions

## Difference to other tactics

Aesop? `bv_decide`?

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
