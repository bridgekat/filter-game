import FilterGame.Principal

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Challenging Puzzles

This level contains some challenging puzzles. Notice that some of the theorems or theorems
below are used in the previous levels.
-/

/--
The infimum (greatest lower bound) of two filters is the filter consisting of
intersections of elements from the two filters.

Hint: decide which sets to use by drawing Venn diagrams.
-/
instance : Inf (Filter α) := ⟨fun f g ↦
{ sets := { s | ∃ a ∈ f, ∃ b ∈ g, s = a ∩ b }
  univ_mem_sets := by
    rw [Set.mem_iff]
    refine ⟨Set.univ, f.univ_mem, Set.univ, g.univ_mem, ?_⟩
    rw [Set.inter_self]
  superset_mem_sets := by
    intros s t hs hst
    rw [Set.mem_iff] at hs ⊢
    have ⟨a, ha, b, hb, hsab⟩ := hs
    refine ⟨a ∪ t, f.superset_mem ha ?_, b ∪ t, g.superset_mem hb ?_, ?_⟩
    . exact Set.subset_union_left _ _
    . exact Set.subset_union_left _ _
    rw [← Set.inter_union_distrib_right, ← hsab, Set.union_eq_self_of_subset_left hst]
  inter_mem_sets := by
    intros s t hs ht
    rw [Set.mem_iff] at *
    have ⟨sa, hsa, sb, hsb, hsab⟩ := hs
    have ⟨ta, hta, tb, htb, htab⟩ := ht
    refine ⟨sa ∩ ta, f.inter_mem hsa hta, sb ∩ tb, g.inter_mem hsb htb, ?_⟩
    rw [hsab, htab]
    ac_rfl }⟩

theorem Filter.mem_inf_def {f g : Filter α} {s : Set α} : s ∈ f ⊓ g ↔ ∃ a ∈ f, ∃ b ∈ g, s = a ∩ b := by
  exact Iff.rfl

theorem Filter.inter_mem_inf {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) : s ∩ t ∈ f ⊓ g := by
  exact ⟨s, hs, t, ht, rfl⟩

/-
Now we are coming to another challenging puzzle.
Hint for the forward direction: 'mem_inf_def'
Hint for the backward direction: consider 's' as '(t ∪ s) ∩ (tᶜ ∪ s)'
-/
theorem Filter.mem_inf_principal_iff {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ {x | x ∈ t → x ∈ s} ∈ f := by
  apply Iff.intro
  . intros hs
    rw [mem_inf_def] at hs
    have ⟨a, ha, b, hb, hsab⟩ := hs
    clear hs
    rw [hsab]; clear hsab
    rw [mem_principal_def] at hb
    suffices h : a ⊆ {x | x ∈ t → x ∈ a ∩ b}
    . exact superset_mem ha h
    intros x hxa hxt
    exact ⟨hxa, hb hxt⟩
  . intros h
    have heq : {x | x ∈ t → x ∈ s} = tᶜ ∪ s
    . apply Set.ext; intros x
      rw [Set.mem_iff, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
    rw [heq] at h; clear heq
    have heq : s = (tᶜ ∪ s) ∩ (t ∪ s) 
    . rw [← Set.union_distrib_right, Set.compl_inter_self, Set.empty_union]
    rw [heq]; clear heq
    refine inter_mem_inf h ?_
    rw [mem_principal_def]
    exact Set.subset_union_left _ _

-- Hint: 'filter.inter_mem' might be helpful.
theorem Filter.compl_not_mem {f : Filter α} {s : Set α} (hf : f ≠ ⊥) (h : s ∈ f) : sᶜ ∉ f := by
  intros h'
  apply hf
  rw [← empty_mem_iff_eq_bot, ← Set.compl_inter_self s]
  exact inter_mem h' h

instance : SemilatticeInf (Filter α) :=
{ inf := instInfFilter.inf
  inf_le_left := by
    intros f g s hs
    rw [Filter.mem_inf_def]
    refine ⟨s, hs, Set.univ, Filter.univ_mem _, ?_⟩
    rw [Set.inter_univ]
  inf_le_right := by
    intros a b s hs
    rw [Filter.mem_inf_def]
    refine ⟨Set.univ, Filter.univ_mem _, s, hs, ?_⟩
    rw [Set.univ_inter]
  le_inf := by
    intros f g k hfg hfk s hs
    have ⟨a, ha, b, hb, hsab⟩ := hs
    specialize hfg _ ha
    specialize hfk _ hb
    rw [hsab]
    exact Filter.inter_mem hfg hfk }

end FilterGame
