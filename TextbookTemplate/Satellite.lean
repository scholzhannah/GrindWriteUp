import VersoManual
import TextbookTemplate.Meta.Lean
import TextbookTemplate.Papers

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

open TextbookTemplate

set_option pp.rawOnError true

#doc (Manual) "Satellite solvers" =>

As mentioned earlier, `grind` employs several satellite solvers to solve problems of a specific nature.
Examples of this are `cutsat` for linear integer arithmetic, `ring` for algebraic expressions in rings and `linarith` for linear arithmetic problems not solved by `cutsat`.

As mentioned before, these might have the same names as Mathlib tactics, they are however implemented independently because they are also supposed to support projects that don't depend on Mathlib. As these are basically tactics in their own right, we won't go into how they work here and instead focus on how you can customize them for your project.

In order for these tactic to work in your projects, you often have to implement certain instances.

For `cutsat` this is for example:

{docstring Lean.Grind.ToInt}

For `ring` there are multiple relevant instances. One example here is:

{docstring Lean.Grind.CommRing}
