import FilterGame.Ultrafilter
import Mathlib.Algebra.Support

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Filters in topology

One of the applications of filters is about topology, and we will go
through some of them in this level.
-/

/- The section below reviews basic knowledge of topological space. This is
basically from mathlib. Notice there is nothing to do in this section -/

/-- A topology on `α`. -/
@[class]
structure TopologicalSpace (α : Type _) where
  is_open             : Set α → Prop
  is_open_univ        : is_open Set.univ
  is_open_inter {s t} : is_open s → is_open t → is_open (s ∩ t)
  is_open_sUnion {s}  : (∀ t ∈ s, is_open t) → is_open (⋃₀ s)

/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def TopologicalSpace.of_closed
  (τ : Set (Set α))
  (empty_mem : ∅ ∈ τ)
  (sInter_mem : ∀ s, s ⊆ τ → ⋂₀ s ∈ τ)
  (union_mem : ∀ a ∈ τ, ∀ b ∈ τ, a ∪ b ∈ τ)
  : TopologicalSpace α :=
{ is_open := fun a ↦ aᶜ ∈ τ
  is_open_univ := by simp_rw [Set.compl_univ, empty_mem]
  is_open_inter := by
    intros s t hs ht
    rw [Set.compl_inter]
    exact union_mem sᶜ hs tᶜ ht
  is_open_sUnion := by
    intros s hs
    rw [Set.compl_sUnion]
    refine sInter_mem (compl '' s) ?_
    intros z hz
    have ⟨y, hy, hz⟩ := hz
    rw [← hz]
    exact hs y hy }

-- Now, coming to the main part of this level:

variable [τ : TopologicalSpace α]

-- Firstly, let's define the neighbourhood filters 𝓝 a:
/-- A set is called a neighborhood of `a` if it contains an open set around `a`. The set of all
neighborhoods of `a` forms a filter, the neighborhood filter at `a`, denoted as 𝓝 a. -/
def TopologicalSpace.nhds (a : α) : Filter α :=
{ sets := {s | ∃ t, t ⊆ s ∧ τ.is_open t ∧ a ∈ t},
  univ_mem_sets := by
    simp only [exists_prop, Set.mem_iff, Set.subset_univ, true_and]
    exact ⟨Set.univ, is_open_univ _, Set.mem_univ _⟩
  superset_mem_sets := by
    intros u v hu huv
    simp only [exists_prop, Set.mem_iff] at hu ⊢
    have ⟨t, ht₁, ht₂, ht₃⟩ := hu
    exact ⟨t, subset_trans ht₁ huv, ht₂, ht₃⟩
  inter_mem_sets := by
    intros u v hu hv
    simp only [exists_prop, Set.mem_iff, Set.subset_inter_iff] at hu hv ⊢
    have ⟨x, hx₁, hx₂, hx₃⟩ := hu
    have ⟨y, hy₁, hy₂, hy₃⟩ := hv
    refine ⟨x ∩ y, ?_, τ.is_open_inter hx₂ hy₂, Set.mem_sep hx₃ hy₃⟩
    apply And.intro
    . apply subset_trans _ hx₁
      exact Set.inter_subset_left x y
    . apply subset_trans _ hy₁
      exact Set.inter_subset_right x y }

notation "𝓝" => TopologicalSpace.nhds

@[simp]
theorem TopologicalSpace.mem_nhds_def (a : α) (s : Set α) : s ∈ 𝓝 a ↔ (∃ t, t ⊆ s ∧ τ.is_open t ∧ a ∈ t) := by
  exact Iff.rfl

-- Try these exercises below:

/-- To show a filter is above the neighborhood filter at `a`, it suffices to show that
it is above the principal filter of some open set `s` containing `a`. -/
theorem TopologicalSpace.nhds_le_of_le {f : Filter α} {a : α} {s : Set α} (h : a ∈ s) (ho : τ.is_open s) (hsf : 𝓟 s ≤ f) : 𝓝 a ≤ f := by
  intros u hu
  rw [mem_nhds_def]
  specialize hsf _ hu
  rw [Filter.mem_principal_def] at hsf
  exact ⟨s, hsf, ho, h⟩

theorem TopologicalSpace.mem_of_mem_nhds {a : α} {s : Set α} (hs : s ∈ 𝓝 a) : a ∈ s := by
  rw [mem_nhds_def] at hs
  have ⟨u, hu₁, hu₂, hu₃⟩ := hs
  exact hu₁ hu₃

theorem TopologicalSpace.IsOpen.mem_nhds {a : α} {s : Set α} (hs : τ.is_open s) (ha : a ∈ s) : s ∈ 𝓝 a := by
  rw [mem_nhds_def]
  exact ⟨s, rfl.subset, hs, ha⟩

-- Using results above, we can get this:
theorem TopologicalSpace.IsOpen.mem_nhds_iff {a : α} {s : Set α} (hs : τ.is_open s) : s ∈ 𝓝 a ↔ a ∈ s := by
  apply Iff.intro
  . exact mem_of_mem_nhds
  . exact mem_nhds hs

end FilterGame
