import FilterGame.Order

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Principal filters

We define the principal filters in this file.

# Main Definitions

`principal` : The principal filter of `s` is the collection of all supersets of `s`.
-/

-- First define the principal filters:

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def Filter.principal (s : Set α) : Filter α :=
{ sets                      := {t | s ⊆ t}
  univ_in_sets              := by exact Set.subset_univ s
  in_sets_of_subset_in_sets := by intros x y hx; exact subset_trans hx
  inter_in_sets             := by intros x y; exact Set.subset_inter }

-- We denote the principal filters as '𝓟' for convenience:
notation:max "𝓟" => Filter.principal

@[simp]
theorem Filter.in_principal_iff (s t : Set α) : s ∈ 𝓟 t ↔ t ⊆ s :=
  Iff.rfl

theorem Filter.in_principal_self (s : Set α) : s ∈ 𝓟 s :=
  (in_principal_iff _ _).mpr subset_rfl

/-- A filter f is finer than the principal filter of s if and only if s ∈ f. -/
theorem Filter.le_principal_iff (s : Set α) (f : Filter α) : f ≤ 𝓟 s ↔ s ∈ f := by
  apply Iff.intro
  . intros h
    exact h _ (Filter.in_principal_self s)
  . intros h t ht
    rw [Filter.in_principal_iff] at ht
    exact Filter.in_of_subset_in h ht

/-- The principal filter of s is finer than the principal filter of t
if and only if s ⊆ t. -/
theorem Filter.principal_mono (s t : Set α) : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t := by
  rw [Filter.le_principal_iff, Filter.in_principal_iff]

/-- The principal filter of s is equal to the principal filter of t
if and only if s = t. -/
@[simp]
theorem Filter.principal_eq_iff_eq (s t : Set α) : 𝓟 s = 𝓟 t ↔ s = t := by
  simp only [le_antisymm_iff, Filter.le_principal_iff, Filter.in_principal_iff]; rfl

/--
Next, our goal: Prove '𝓟 (univ : set α) = ⊤' and '𝓟 (∅ : set α) = ⊥'
Before we go to these,
we firstly want to consider how to define the top (⊤) and the bottom (⊥) of filters.
i.e. the largest filter and the smallest filter
Remark:
When we say that a filter f ≤ filter g ,
it means that g ⊆ f. i.e. ∀ s ∈ g → s ∈ f
Idea:
The smallest filter corresponds to the finest one, so it should contain every subset.
Similarly, the largest filter should only contain the whole set.
-/

-- Let's verify these:
instance : OrderTop (Filter α) :=
{ top :=
  { sets                      := {s | ∀ x, x ∈ s}
    univ_in_sets              := by intros s; exact Set.mem_univ s
    in_sets_of_subset_in_sets := by intros s t hs hst x; exact hst (hs x)
    inter_in_sets             := by intros s t hs ht x; exact Set.mem_inter (hs _) (ht _) }
  le_top := by
    intros f s hs
    suffices h : s = Set.univ
    . rw [h]; exact Filter.univ_in _
    rw [Set.eq_univ_iff_forall]
    exact hs }

theorem Filter.in_top_iff_forall (s : Set α) : s ∈ (⊤ : Filter α) ↔ ∀ x, x ∈ s :=
  Iff.rfl

@[simp]
theorem Filter.in_top_iff_eq_univ (s : Set α) : s ∈ (⊤ : Filter α) ↔ s = Set.univ := by
  rw [Filter.in_top_iff_forall, Set.eq_univ_iff_forall]

-- Hint: consider the magic of 'simp'
instance : OrderBot (Filter α) :=
{ bot :=
  { sets                      := Set.univ
    univ_in_sets              := by exact Set.mem_univ _
    in_sets_of_subset_in_sets := by intros _ _ _ _; exact Set.mem_univ _
    inter_in_sets             := by intros _ _ _ _; exact Set.mem_univ _ }
  bot_le := by
    intros _ _ _
    exact Set.mem_univ _ }

@[simp]
theorem Filter.in_bot (s : Set α) : s ∈ (⊥ : Filter α) :=
  True.intro

theorem Filter.empty_in_iff_eq_bot f : ∅ ∈ f ↔ f = (⊥ : Filter α) := by
  apply Iff.intro
  . intros h
    apply Filter.ext
    intros s
    apply Iff.intro
    . intros _; exact True.intro
    . intros _; exact Filter.in_of_subset_in h (Set.empty_subset _)
  . intros h
    rw [h]
    exact Set.mem_univ _

-- Hint: try applying top_unique
@[simp]
theorem Filter.principal_univ : 𝓟 Set.univ = (⊤ : Filter α) := by
  apply top_unique
  rw [le_principal_iff, in_top_iff_forall]
  intros x
  exact True.intro

-- Hint: can you guess this hint using the above hint?
@[simp]
theorem Filter.principal_empty : 𝓟 ∅ = (⊥ : Filter α) := by
  apply bot_unique
  intros s hs
  exact Set.empty_subset s

end FilterGame
