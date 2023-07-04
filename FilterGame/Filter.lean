import Mathlib.Data.Set.Basic

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Filters

In this world, we will define filters and prove some of its basic properties.
-/

/--
Given a type `α`, a filter is a collection of sub**sets** of `α` which:

- contains the whole set (the **univ**ersal set is a **mem**ber of **sets**),
- is upward closed (**superset**s are **mem**bers of **sets**) and
- is closed under intersections (**inter**sections are **mem**bers of **sets**).

We represent it in Lean as a new type, which "packages" the collection of
subsets, along with all the properties it should have.
-/
structure Filter (α : Type _) where
  sets                    : Set (Set α)
  univ_mem_sets           : Set.univ ∈ sets
  superset_mem_sets {s t} : s ∈ sets → s ⊆ t → t ∈ sets
  inter_mem_sets {s t}    : s ∈ sets → t ∈ sets → s ∩ t ∈ sets

/--
If we have a filter `f`, it is more convenient to write `s ∈ f` for
`s ∈ f.sets`. We now define this notation.

## Technical details

A straightforward way is to use the `notation` or `infix` commands. However,
the symbol `∈` is so commonly used in different parts of mathematics, that
doing so naively can lead to parsing ambiguity. The creators of Lean decided to
re-use a mechanism called *typeclasses* for the purpose of operator overloading.
The typeclass providing `∈` is called `Membership`. Creating an instance of
`Membership` allows us to use `∈` for filters.
-/
instance : Membership (Set α) (Filter α) :=
  ⟨fun s f ↦ s ∈ f.sets⟩

/--
The definition of `∈`.

## Technical details

In Lean, things that are *equal by definition* are "more equal than" things
that were *proven to be equal*. You don't need to `rw` for the former!

However, in Lean 3 you actually *cannot* `rw` for the former, which can be
annoying if you just want to unfold a definition. Also, the distinction between
definitional and propositional equality is a source of confusion: why don't we
make everything uniform?

So a common practice is to *manually create propositional equality lemmas*
(like this `mem_def`) for definitional equalities, and then use them all along
-- forget about definitional equalities!
-/
@[simp]
theorem Filter.mem_def (f : Filter α) (s : Set α) : s ∈ f ↔ s ∈ f.sets := by
  exact Iff.rfl

/--
The definition of equality between filters.

## Technical details

In the `Filter` type, we have both tangible objects like `sets` and
conceptual properties like `univ_mem_sets`. When comparing two filters `f` and
`g`, only the tangible parts `f.sets` and `g.sets` are relevant.
So if `f.sets` and `g.sets` are equal, we consider `f` and `g` to be equal, too.
-/
@[simp]
theorem Filter.eq_def (f g : Filter α) : f = g ↔ f.sets = g.sets := by
  apply Iff.intro
  . intro h; rw [h]
  . intro h; cases f; cases g; congr

/--
This is a simple corollary of the above lemmas, `Filter.mem_def` and
`Filter.eq_def`, and set extensionality, `Set.ext`.

## Tips

This lemma's name begins with `Filter.`, so we can refer to other
`Filter.`-prefixed lemmas directly in its proof. For example, we may simply
write `mem_def` for `Filter.mem_def`.
-/
theorem Filter.ext_iff (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  simp only [eq_def, mem_def, Set.ext_iff]

theorem Filter.ext {f g : Filter α} : (∀ s, s ∈ f ↔ s ∈ g) → f = g := by
  exact (ext_iff _ _).mpr

/-!
These lemmas directly follow from the definiton of the filters:
-/
theorem Filter.univ_mem (f : Filter α) : Set.univ ∈ f := by
  exact f.univ_mem_sets

theorem Filter.superset_mem {f : Filter α} {s t : Set α} (hs : s ∈ f) (h : s ⊆ t) : t ∈ f := by
  exact f.superset_mem_sets hs h

theorem Filter.inter_mem {f : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f := by
  exact f.inter_mem_sets hs ht

end FilterGame
