import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Lattice
import FilterGame.Solutions.Ultrafilter

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Filters in topology

One of the application areas of filters is topology, and we will go through
some of the results in this world.

First, we review the definition of topological spaces, in Lean...
-/

/--
A topology on type `α`.

Note that it differs from the textbook definition by not requiring
the empty set to be open.
-/
@[class]
structure TopologicalSpace (α : Type _) where
  sets : Set (Set α)
  univ_mem_sets : Set.univ ∈ sets
  inter_mem_sets {s t} : s ∈ sets → t ∈ sets → s ∩ t ∈ sets
  sUnion_mem_sets {c} : (∀ t ∈ c, t ∈ sets) → ⋃₀ c ∈ sets

/--
A constructor of topologies by complementing the specified closed sets,
and showing that their complements satisfy the required conditions.
-/
def TopologicalSpace.of_closed
  (τ : Set (Set α))
  (empty_mem : ∅ ∈ τ)
  (union_mem : ∀ a ∈ τ, ∀ b ∈ τ, a ∪ b ∈ τ)
  (sInter_mem : ∀ s, s ⊆ τ → ⋂₀ s ∈ τ) :
    TopologicalSpace α :=
{ sets := fun a ↦ aᶜ ∈ τ
  univ_mem_sets := by
    change Set.univᶜ ∈ τ
    simp_rw [Set.compl_univ]
    exact empty_mem
  inter_mem_sets := by
    intros s t hs ht
    change (s ∩ t)ᶜ ∈ τ
    rw [Set.compl_inter]
    exact union_mem sᶜ hs tᶜ ht
  sUnion_mem_sets := by
    intros s hs
    change (⋃₀ s)ᶜ ∈ τ
    rw [Set.compl_sUnion]
    refine sInter_mem (compl '' s) ?_
    intros z hz
    have ⟨y, hy, hz⟩ := hz
    rw [← hz]
    exact hs y hy }

--! Now we are coming to the main part of this level.
variable [τ : TopologicalSpace α]

/--
A set is called a "neighborhood" of `a` if it contains an open set around `a`.

The set of all neighborhoods of `a` forms a filter, the neighborhood filter at
`a`, written `𝓝 a` (type `\nhds`).
-/
def TopologicalSpace.nhds (a : α) : Filter α :=
{ sets := {s | ∃ t, t ⊆ s ∧ τ.sets t ∧ a ∈ t},
  univ_mem_sets := by sorry
  superset_mem_sets := by sorry
  inter_mem_sets := by sorry }

notation "𝓝" => TopologicalSpace.nhds

@[simp]
theorem TopologicalSpace.mem_nhds_def (a : α) (s : Set α) :
    s ∈ 𝓝 a ↔ (∃ t, t ⊆ s ∧ τ.sets t ∧ a ∈ t) := by
  exact Iff.rfl

--! Try these exercises below:

/--
To show a filter is coarser than the neighborhood filter at `a`, it suffices to
show that it is coarser than the principal filter of some open set `s`
containing `a`.
-/
theorem TopologicalSpace.nhds_le_of_le {f : Filter α} {a : α} {s : Set α}
    (h : a ∈ s) (ho : τ.sets s) (hsf : 𝓟 s ≤ f) : 𝓝 a ≤ f := by
  sorry

theorem TopologicalSpace.mem_of_mem_nhds {a : α} {s : Set α} (hs : s ∈ 𝓝 a) : a ∈ s := by
  sorry

theorem TopologicalSpace.OpenSets.mem_nhds {a : α} {s : Set α} (hs : τ.sets s) (ha : a ∈ s) :
    s ∈ 𝓝 a := by
  sorry

--! Using results above, we arrive at this:
theorem TopologicalSpace.OpenSets.mem_nhds_iff {a : α} {s : Set α} (hs : τ.sets s) :
    s ∈ 𝓝 a ↔ a ∈ s := by
  sorry

end FilterGame
