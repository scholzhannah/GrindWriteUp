import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

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

-- for cardinality symbol
open Finset CategoryTheory Distribution

set_option pp.rawOnError true



#doc (Manual) "E-matching" =>

As said before, e-matching is how `grind` uses the lemmas tagged by users. In it's most basic form, you can tag a lemma with `@[grind *]` where `*` is a modifier, of which we discuss examples below.
This of course provides a lot of interactivity, so we will discuss this in detail.

The basic functionality of e-matching is the following: `grind` maintains an index of tagged lemmas and corresponding patterns. If a pattern matches the terms in the context, `grind` tries to apply the theorem to the relevant terms and write the result on the whiteboard.

E-matching can be very powerful if whole libraries are tagged thoroughly but it can of course also be very slow, especially if patterns are chosen to be too general.
This is why `grind` provides a lot of customisability and diagnostic tools here.

# General

An expression is indexable if it starts with a constant that is anything but {lean}`Eq`, {lean}`HEq`, {lean}`Iff`, {lean}`And`, {lean}`Or` and {lean}`Not`. For example, an expression of the form `t = s` where `t` and `s` are some subexpressions cannot be used as a pattern.

In addition to simply looking whether a single pattern can be found in the context, theorems can also have multi-patterns. Here multiple patterns need to be found in the context before the theorem is applied.

Here is an example from Mathlib where a multi-pattern is used:

```lean
theorem card_ne_zero_of_mem {α : Type*} {s : Finset α}
    {a : α} (h : a ∈ s) : #s ≠ 0 :=
  (not_congr card_eq_zero).2 <| ne_empty_of_mem h
```

Let us consider the different patterns we could use here. We cannot use `#s ≠ 0` or `#s = 0` because both of these start with a non-indexable constant.
We could use `#s` as a pattern. However, this doesn't mention `a`, so the theorem would be tried whenever we talk about the cardinality of a finite set even when there is no element in the context. We also probably don't want to try to apply this theorem whenever a statement of the form `a ∈ s` is on the whiteboard because in this case we don't know if we need to consider cardinalities at all.

So Mathlib specifies the multi-pattern `a ∈ s, #s` here. So the fact that `#s ≠ 0` will be added to the context, whenever there is a statement of the form `a ∈ s` on the whiteboard and somewhere on the whiteboard the cardinality of `s` is mentioned.

It is important to note that a multi-pattern is not the same as specifying multiple patterns.
In a multi-pattern all included patterns need to match.
When multiple patterns are specified, one of them needs to match in order for the theorem to be used.

# Specifying default patterns

There is a list of modifiers to the `grind` attribute that can be used to specify patterns using different algorithms.
Here is an overview of the options with examples from Mathlib.
You can use `grind?` to see which pattern is picked.
Arguments of the lemma are indexed with numbers starting with 0 for the first argument.

Some of these strategies require that a pattern can only be used when it covers all the arguments of the theorem, i.e. if all the arguments are fixed by the pattern. A multi-pattern can then only be used if every argument is covered by at least one of the included patterns. This is so that a theorem isn't applied too eagerly.

## `=`: left side of equality

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

An equivalence is treated as an equality of proposition, so we can also use this modifier here. The pattern means that this theorem is used whenever there is a statement `Even n` on the whiteboard.

## `=_`: right side of equality

This instructs `grind` to use the right side of the goal (if it is an equality) as a pattern. It fails if not all arguments are covered in this way.

I could not find an example in Mathlib so here is an example from Lean:

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

##  `_=_`: both sides of equality as two patterns

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

## `→`: starting with hypotheses

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

## `.`: starting with conclusion

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

## Further modifiers

There a more modifiers that tell `grind` the order in which it should pick patterns such as `←`, `⇒` and `⇐`. Additionally, there are some modifiers to be used for specific types of theorems such as `ext` for extensionality theorems and `inj` for theorems showing injectivity.

Learn more about these modifiers in the [Lean Language Reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/E___matching/#e-matching).

## `grind!`

Sometimes you want to pick a subterm or subexpression as a pattern. If you want to be as "aggressive" as possible with this, you can pick minimal indexable subexpression.
An expression is minimally indexable if it has no indexable subexpressions (respecting additionally some priorities).
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

# Custom Patterns

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

If you want to specify multiple patterns you can do that like this:

```lean -show
open List
```

```lean
@[simp]
theorem count_false_add_count_true' (l : List Bool) :
    count false l + count true l = length l :=
  count_not_add_count l true

grind_pattern count_false_add_count_true' => count false l
grind_pattern count_false_add_count_true' => count true l

```

So this theorem is used by `grind` if it find either `count false l` or `count true l` on the whiteboard.

# Picking a pattern

So how do you pick a pattern for your theorem?

Firstly, if you just tag it with `@[grind]` without any modifiers, there will be a helpful message suggesting different modifiers and the patterns they would generate.

If in our example from above we write

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

## Identifying bad tagging

If your `grind` call is slow you might want to check whether it might be due to e-matching by checking what theorems it instantiates. You can do this by setting the option `trace.grind.ematch.instance` to true.

Sometimes a combination of tagged theorems can produce loops. These loops can be identified with `#grind_lint`.

Here is an example from the Language Reference. If we tag {lean}`List.reverse_flatMap` and {lean}`List.flatMap_reverse` like this:

```lean
attribute [grind =] List.reverse_flatMap List.flatMap_reverse
```

Then `#grind_lint inspect` will show us that these theorems now produce a loop:

```lean (name := Lint)
#grind_lint inspect List.reverse_flatMap
```

```leanOutput Lint
instantiating `List.reverse_flatMap` triggers 22 additional `grind` theorem instantiations
```
```leanOutput Lint
Try this to display the actual theorem instances:
  [apply] set_option trace.grind.ematch.instance true in
  #grind_lint inspect List.reverse_flatMap
```

If we do what the the suggestion tells us to do we get:

```lean (name := Lint2)
set_option trace.grind.ematch.instance true in
#grind_lint inspect List.reverse_flatMap
```

with the following (shortened) output:

```
[grind.ematch.instance] reverse_flatMap: (flatMap f l).reverse = flatMap (reverse ∘ f) l.reverse
[grind.ematch.instance] flatMap_reverse: flatMap (reverse ∘ f) l.reverse = (flatMap (reverse ∘ reverse ∘ f) l).reverse
[grind.ematch.instance] flatMap_def: flatMap (reverse ∘ f) l.reverse = (List.map (reverse ∘ f) l.reverse).flatten
[grind.ematch.instance] flatMap_def: flatMap f l = (List.map f l).flatten
[grind.ematch.instance] reverse_flatMap: (flatMap (reverse ∘ reverse ∘ f) l).reverse = flatMap (reverse ∘ reverse ∘ reverse ∘ f) l.reverse
[grind.ematch.instance] flatMap_def: flatMap (reverse ∘ reverse ∘ f) l = (List.map (reverse ∘ reverse ∘ f) l).flatten
[grind.ematch.instance] flatMap_reverse: flatMap (reverse ∘ reverse ∘ reverse ∘ f) l.reverse =
      (flatMap (reverse ∘ reverse ∘ reverse ∘ reverse ∘ f) l).reverse
[grind.ematch.instance] flatMap_def: flatMap (reverse ∘ reverse ∘ reverse ∘ f) l.reverse =
      (List.map (reverse ∘ reverse ∘ reverse ∘ f) l.reverse).flatten
```

where we can actually observe the loop.

If we want to see all theorems that are problematic in this way, we can do this with `#grind_lint check`. We can be more specific and only search in a specific module and require a specific number of additionally instantiated theorems.
(I am not including the following code as Lean code, to not make the build slow.)

```
#grind_lint check (min := 20) in module Mathlib
```

for my current imports this gives

```
instantiating `Set.Icc.convexComb_symm` triggers 24 additional `grind` theorem instantiations
```
```
instantiating `Path.symm_apply` triggers 24 additional `grind` theorem instantiations
```

Mathlib performs this exact test above, the two lemmas we found above are currently the only exceptions.

As you can see the lemmas `reverse_flatMap` and `flatMap_reverse` don't appear here, meaning they don't produce the loop we discovered above in Mathlib. They are still tagged but have additional conditions imposed to prevent the looping:

```lean
grind_pattern reverse_flatMap => (l.flatMap f).reverse where
  f =/= List.reverse ∘ _

grind_pattern flatMap_reverse => l.reverse.flatMap f where
  f =/= List.reverse ∘ _
```

# Restricting e-matching in a `grind` call

If instead of modifying how lemmas are tagged, you want to limit e-matching in your `grind` call, you can for example do this by restricting "generations". Each expression on the whiteboard has a associated generation. The expressions from the original context all have generation 0. When we produce a new expression through e-matching, its generation will be one higher than that of the term with the highest generation that was used for producing the new expression.

You can write `grind (gen := n)` to modify how low the generation number needs to be for e-matching to consider a term. The default is 8.
