import Mathlib.Data.Set.Basic
import GameServer.Commands

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

Game "Filter"
World "Filter"
Level 1
Title "Introduction"

Introduction
"
# Filters

We define the filters and some basic properties of the filters in this file.

Note: there is no puzzle in this file, and please read the instruction before
starting playing game.

# Main Definitions

`filter` : A filter is a collection of subsets which contains the whole set,
upward closed and closed under intersection.
"

-- First let's define the filters:
structure Filter (α : Type _) where
  sets                            : Set (Set α)
  univ_in_sets                    : Set.univ ∈ sets
  in_sets_of_subset_in_sets {s t} : s ∈ sets → s ⊆ t → t ∈ sets
  inter_in_sets {s t}             : s ∈ sets → t ∈ sets → s ∩ t ∈ sets

DefinitionDoc Filter as "Filter"
"A filter is a collection of subsets which contains the whole set,
upward closed and closed under intersection."
NewDefinition Filter

-- (Technical detail)
-- A filter f is a collection of subsets,
-- so clearly we want to do something like (s : set α) ∈ (f : filter α).
instance : Membership (Set α) (Filter α) :=
  ⟨fun s f ↦ s ∈ f.sets⟩

-- (Technical detail)
-- Make propositional equality from definition, so it can be tagged with `simp`.
@[simp]
theorem Filter.in_iff (f : Filter α) (s : Set α) : s ∈ f ↔ s ∈ f.sets :=
  Iff.rfl

-- (Technical detail)
-- By proof irrelevance, two filters are equal if and only if they contain the same sets.
@[simp]
theorem Filter.eq_iff (f g : Filter α) : f = g ↔ f.sets = g.sets := by
  apply Iff.intro
  . intro h; rw [h]
  . intro h; cases f; cases g; congr

theorem Filter.ext_iff (f g : Filter α) : f = g ↔ (∀ s, s ∈ f ↔ s ∈ g) := by
  simp only [eq_iff, in_iff, Set.ext_iff]

theorem Filter.ext {f g : Filter α} : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
  (ext_iff _ _).2

-- The following three lemmas are directly from the definiton of the filters:
theorem Filter.univ_in (f : Filter α) : Set.univ ∈ f :=
  Filter.univ_in_sets f

theorem Filter.in_of_subset_in {f : Filter α} {s t : Set α} (hs : s ∈ f) (h : s ⊆ t) : t ∈ f :=
  Filter.in_sets_of_subset_in_sets f hs h

theorem Filter.inter_in {f : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f :=
  Filter.inter_in_sets f hs ht

end FilterGame
