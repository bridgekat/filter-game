import FilterGame.Semilattice

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Ultrafilters

We define the ultrafilters in this file. Notice that some of the lemmas we used are
given in 'game.level_06_challenges'. You can directly use these lemmas for now,
and do them in the level 6.

# Main Definitions

`ultrafilter` : An ultrafilter is a minimal (maximal in the set order) proper filter.
-/

-- Firstly, let's define ultrafilers:
/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
structure Ultrafilter (α : Type _) where
  as_filter    : Filter α
  ne_bot       : as_filter ≠ ⊥
  le_of_le {g} : g ≠ ⊥ → g ≤ as_filter → as_filter ≤ g

-- An ultrafilter is clearly a filter, but they are two distinct types.
-- So we want to convert an ultrafilter `f` into a filter by using notations
-- `↑f` or `f : Filter α`.
instance : Coe (Ultrafilter α) (Filter α) :=
  ⟨Ultrafilter.as_filter⟩

instance : Membership (Set α) (Ultrafilter α) :=
  ⟨fun s f ↦ s ∈ (f : Filter α)⟩

/- If any filter g is finer than the ultrafilter f, then g = f,
since an ultrafilter is a minimal proper filter. -/
theorem Ultrafilter.unique {f : Ultrafilter α} {g : Filter α} (h : g ≤ f) (hg : g ≠ ⊥) : g = f := by
  apply le_antisymm h
  exact f.le_of_le hg h

/-- We provide some basic APIs below.
Notice there is no need to do here. -/

@[simp]
theorem Ultrafilter.mem_coe {f : Ultrafilter α} {s : Set α} : s ∈ (f : Filter α) ↔ s ∈ f := by
  exact Iff.rfl

theorem Ultrafilter.coe_injective : Function.Injective (Coe.coe : Ultrafilter α → Filter α) := by
  intros f g h
  cases f; cases g; congr

theorem Ultrafilter.eq_of_le {f g : Ultrafilter α} (h : (f : Filter α) ≤ g) : f = g := by
  exact coe_injective (g.unique h f.ne_bot)

@[simp]
theorem Ultrafilter.coe_le_coe_iff_eq {f g : Ultrafilter α} : (f : Filter α) ≤ (g : Filter α) ↔ f = g := by
  apply Iff.intro
  . exact eq_of_le
  . intros h; rw [h]

@[simp]
theorem Ultrafilter.coe_inj {f g : Ultrafilter α} : (f : Filter α) = g ↔ f = g := by
  exact coe_injective.eq_iff

theorem Ultrafilter.ext {f g : Ultrafilter α} (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g := by
  exact coe_injective (Filter.ext h)

/--
Now, it's time to do some amazing puzzles!
Our main goal: Prove `f` is an ultrafilter if and only if `∀ s, s ∈ f ↔ sᶜ ∉ f`.
The following theorem 'le_of_inf_ne_bot' might be helpful in the proof of forward direction.

Notice that in that theorem we use the "intersection" of two filters, which is not the usual
intersection of two filters, since the intersection of two filters is not always a filter.
Hence instead, we define "intersection" of two filters as
the filter generated by intersections of elements of the two filters.
This is defined in 'game.level_06_challenges' and you can find some useful lemmas related
it there. Again, you can directly use these lemmas for now, and do them in the level 6.
-/

-- Hint: `le_of_inf_eq` from `SemilatticeInf` may be a good start here.
theorem Ultrafilter.le_of_inf_ne_bot {f : Ultrafilter α} {g : Filter α} (hg : ↑f ⊓ g ≠ ⊥) : ↑f ≤ g := by
  apply le_of_inf_eq
  refine unique ?_ hg
  exact inf_le_left

/-- Now coming to our main goal:
The backward direction is 'filter.compl_not_mem' given in 'game.level_05_challenges'.
(i.e. you can directly use 'filter.compl_not_mem' here for now,
and do it in the next level)
Hints for the forward direction:
'filter.le_principal_iff'
'ultrafilter.le_of_inf_ne_bot'
'filter.empty_mem_iff_bot'
'filter.mem_inf_principal'
Notice that some of the lemmas above are in 'game.level_06_challenges',
you can directly use them for now, and do them in the next level.
-/
@[simp]
theorem Ultrafilter.compl_not_mem_iff {f : Ultrafilter α} {s : Set α} : sᶜ ∉ f ↔ s ∈ f := by
  apply Iff.intro
  . intros hne
    rw [← mem_coe, ← Filter.le_principal_iff]
    apply le_of_inf_ne_bot
    intros h
    rw [← Filter.empty_mem_iff_eq_bot, Filter.mem_inf_principal_iff] at h
    suffices h' : {x | x ∈ s → x ∈ (∅ : Set α)} = sᶜ
    . rw [h'] at h
      exact hne h
    apply Set.ext; intros x
    rw [Set.mem_iff, Set.mem_compl_iff, Set.mem_empty_iff_false]
  . exact Filter.compl_not_mem f.ne_bot

-- This result is directly from previous one.
theorem Ultrafilter.compl_mem_iff {f : Ultrafilter α} {s : Set α} : sᶜ ∈ f ↔ s ∉ f := by
  rw [← compl_not_mem_iff, compl_compl]

-- Hint: 'filter.compl_not_mem' might be helpful.
/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`ultrafilter.compl_not_mem_iff`.  -/
def Ultrafilter.of_compl_not_mem_iff (f : Filter α) (h : ∀ s, sᶜ ∉ f ↔ s ∈ f) : Ultrafilter α :=
{ as_filter := f,
  ne_bot := by
    intros hf
    subst hf
    specialize h Set.univ
    rw [Set.compl_univ] at h
    exact h.mpr (Filter.mem_bot _) (Filter.mem_bot _)
  le_of_le := by
    intros g hg hgf s hs
    apply (h _).mp
    intros hsc
    exact Filter.compl_not_mem hg hs (hgf _ hsc) }

end FilterGame