import FilterGame.Basic

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Filter basis

We define the filter basis in this file.

# Main Definitions

`filter_basis` : A filter basis is a nonempty collection of sets such that the
intersection of two elements of this collection contains
some element of the collection.
-/

-- Let's define the filter basis:
/-- A filter basis is a nonempty collection of sets such that the intersection of
two elements of this collection contains some element of the collection. -/
structure Basis (α : Type _) where
  sets                : Set (Set α)
  sets_nonempty       : ∃ s, s ∈ sets
  inter_in_sets {s t} : s ∈ sets → t ∈ sets → ∃ u ∈ sets, u ⊆ s ∩ t

-- (Technical detail)
-- A filter basis B is a collection of subsets,
-- so clearly we want to do something like U ∈ B.
instance : Membership (Set α) (Basis α) :=
  ⟨fun s b ↦ s ∈ b.sets⟩

-- (Technical detail)
-- Make propositional equality from definition, so it can be tagged with `simp`.
@[simp]
theorem Basis.in_iff (b : Basis α) (s : Set α) : s ∈ b ↔ s ∈ b.sets :=
  Iff.rfl

-- (Technical detail)
-- By proof irrelevance, two filter bases are equal if and only if they contain the same sets.
@[simp]
theorem Basis.eq_iff (b c : Basis α) : b = c ↔ b.sets = c.sets := by
  apply Iff.intro
  . intro h; rw [h]
  . intro h; cases b; cases c; congr

theorem Basis.ext_iff (b c : Basis α) : b = c ↔ (∀ s, s ∈ b ↔ s ∈ c) :=
  by simp_rw [eq_iff, in_iff, Set.ext_iff]

theorem Basis.ext {b c : Basis α} : (∀ s, s ∈ b ↔ s ∈ c) → b = c :=
  (ext_iff _ _).2

-- We can prove that every filter is actually a filter basis.
/-- View a filter as a filter basis. -/
def Filter.as_basis (f : Filter α) : Basis α :=
{ sets := f.sets
  sets_nonempty := by
    exact ⟨Set.univ, Filter.univ_in _⟩,
  inter_in_sets := by
    intro s t hs ht
    exact ⟨s ∩ t, Filter.inter_in hs ht, subset_rfl⟩ }

-- Here are some APIs of filter basis:
theorem Filter.in_as_basis_iff (f : Filter α) (t : Set α) : t ∈ Filter.as_basis f ↔ t ∈ f :=
  Iff.rfl

/- Actually, we can construct filter using filter basis:
The filter f generated by filter base B is te collection of all sets fⱼ such
that Bᵢ ⊆ fⱼ for some Bᵢ ∈ B. -/

-- TODO: not required but helpful
theorem Set.in_set_iff (p : α → Prop) (y : α) : y ∈ {x | p x} ↔ p y :=
  Set.mem_setOf

-- Try to solve these `sorry`s.
/-- The filter associated to a filter basis. -/
def Basis.as_filter (b : Basis α) : Filter α :=
{ sets := {s | ∃ t ∈ b, t ⊆ s}
  univ_in_sets := by
    rw [Set.in_set_iff]
    have ⟨s, hs⟩ := sets_nonempty b
    refine ⟨s, hs, Set.subset_univ _⟩
  in_sets_of_subset_in_sets := by
    intros s t hs h
    rw [Set.in_set_iff] at hs ⊢
    have ⟨u, hu⟩ := hs
    exact ⟨u, hu.1, subset_trans hu.2 h⟩
  inter_in_sets := by
    intros s t hs ht
    rw [Set.in_set_iff] at *
    have ⟨u, hu⟩ := hs
    have ⟨v, hv⟩ := ht
    have ⟨w, hw⟩ := Basis.inter_in_sets b hu.1 hv.1
    have ⟨hwu, hwv⟩ := Set.subset_inter_iff.mp hw.2
    refine ⟨w, hw.1, Set.subset_inter ?_ ?_⟩
    . exact subset_trans hwu hu.2
    . exact subset_trans hwv hv.2 }

-- The following two lemmas are directly from the definition.
theorem Basis.in_as_filter_iff (b : Basis α) (s : Set α) : s ∈ b.as_filter ↔ ∃ t ∈ b, t ⊆ s :=
  Iff.rfl

theorem Basis.in_as_filter_of_in {b : Basis α} {s : Set α} (h : s ∈ b) : s ∈ b.as_filter := by
  rw [Basis.in_as_filter_iff]
  exact ⟨s, h, subset_rfl⟩

-- Next, we can try to prove this lemma:

/-- The filter generated by a filter is actually itself. -/
theorem Filter.as_basis_as_filter_eq (f : Filter α) : f.as_basis.as_filter = f := by
  rw [Filter.eq_iff]
  apply Set.ext; intros x
  simp_rw [← Filter.in_iff, Basis.in_as_filter_iff, Filter.in_as_basis_iff]
  apply Iff.intro
  . intros hx; have ⟨t, ht⟩ := hx; exact Filter.in_of_subset_in ht.1 ht.2
  . intros hx; exact ⟨x, hx, subset_rfl⟩

end FilterGame