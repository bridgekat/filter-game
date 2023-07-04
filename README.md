# The Filter Game

[The Filter Game](https://github.com/Biiiilly/filter) is a Year 2 maths student
group project at Imperial College London, authored by Jiale Miao
([@Biiiilly](https://github.com/Biiiilly/)), Yichen Feng, Lily Frost,
Archie Prime and supervised by Prof. Kevin Buzzard
([@kbuzzard](https://github.com/kbuzzard/)).

This is an adaptation of the filter game to Lean 4.

**Note:** compared to the
[Natural Number Game](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/),
this game requires more advanced Lean knowledge, including lemma-like tactics
(`have` or `suffices`) and the understanding of _definitions_ of new types and
functions (`structure`, `def`). If you are a beginner, you can try this game
after completing NNG!

## Installation

First install Git, Lean 4, Visual Studio Code and the Lean 4 extension by
following [the instructions here](https://leanprover-community.github.io/get_started.html).

Then, open a terminal somewhere and type in the following commands one by one:

```sh
git clone https://github.com/bridgekat/filter-game
cd filter-game
lake exe cache get
```

The last step will download the Mathlib cache, and can take several minutes to
complete. Upon completion, open the `filter-game` folder in VSCode and
double-click the `FilterGame/Filter.lean` file on the left pane; VSCode should
start downloading the required version of Lean automatically. After this
completes, the yellow bars should soon disappear, and you are ready!

## Instruction

There are seven worlds in this game:

- `Filter.lean`: this world contains the basic definition of filters.
- `Basis.lean`: this world introduces filter bases, and discusses some of its
  properties.
- `Order.lean`: given two filters (or filter bases) `f` and `g`, this world
  talks about the definition of `f ≤ g`.
- `Principal.lean`: this world discusses "principal filters", or filters that
  can be generated from a single set.
- `Semilattice.lean`: this world shows that the `f ≤ g` relation can be made
  into a "semilattice", by introducing a notion of "greatest lower bound".
- `Ultrafilter.lean`: this world discusses "ultrafilters", or minimal proper
  filters.
- `Topology.lean`: one of the application areas of filters is topology, and we
  will go through some of the results in this world.

## General Tips

- In Lean 4, you can now hover your mouse cursor over a tactic to see how it can
  be used. Or hover over the name of a lemma to see its statement. If you are
  playing in a real Lean environment, hovering over lemma names in the infoview
  (the panel on the right displaying your goals) also works.
- To **use** what you already have:
  - If you have a function, or anything like `p → ...` or `∀ x, ...`, you
    simply supply arguments to it, or use `specialize`.
  - If you have an equality, use `rw`.
  - In all other cases, use pattern-matching `have` (simple), `cases` (medium)
    or `induction` (powerful) on what you have.
- To **make** something required by the goal:
  - If the goal is in the form `p → ...` or `∀ x, ...`, use `intros`.
  - If you need to prove an equality, use `rw`.
  - In all other cases, use either `exact` (simple), `apply` (medium)
    or `refine` (powerful). If you don't know which lemma to use, try `constructor`.
- To progress **step-by-step**, use `have` or `suffices`.
- To temporarily save an expression, use `let`.
- Special-purpose tactics:
  - Use `conv` if you want to have more control over `rw`.
  - Use `simp_rw` to rewrite _inside function bodies or `∀`_.
    (Plain `rw` does not work in this case.)
  - Use `simp` to carry out chains of `rw`s.
    (Or when some horribly-complicated thing pops up in the infoview.)
  - Use `apply?` to search the Mathlib.
  - Use `ac_rfl`, `ring`, `linarith`, `tauto` (or, finally, `aesop`?) on their
    respective expertise areas.

## Resources

- Guide for writing tactic proofs: see
  [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html)
  (you can also learn writing "term-mode" proofs and creating new types here.)
- A full list of core tactics: see
  [Mathlib 4 Documentation](https://leanprover-community.github.io/mathlib4_docs/Init/Tactics.html)
- A full list of Mathlib tactics will hopefully become available soon.
  (For now, go to https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic.html
  and click on the "source" link on the right.)
