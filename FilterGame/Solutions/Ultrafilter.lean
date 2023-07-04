import FilterGame.Solutions.Semilattice

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Ultrafilters

The glorious ultrafilter world!
-/

/--
An ultrafilter is a minimal (or, maximal in terms of the size of `sets`)
proper filter.

We represent it in Lean as a new type, which "packages" the filter itself,
along with all the additional properties it should have.
-/
structure Ultrafilter (α : Type _) where
  as_filter    : Filter α
  ne_bot       : as_filter ≠ ⊥
  le_of_le {g} : g ≠ ⊥ → g ≤ as_filter → as_filter ≤ g

/--
The conversion ("coercion") from ultrafilters to filters.

## Technical details

Informally, we consider an ultrafilter as a special kind of filter, but in Lean
they are simply two distinct types.

The way to formalise our intuition in Lean is to define a direct *conversion*
from ultrafilters to filters. Then, to perform such a conversion, we use the
syntax `f : Filter α` or `↑f` (if expected type can be inferred from context).
-/
instance : Coe (Ultrafilter α) (Filter α) :=
  ⟨Ultrafilter.as_filter⟩

/--
If we have an ultrafilter `f`, it is more convenient to write `s ∈ f` for
`s ∈ (f : Filter α)` or `s ∈ (f : Filter α).sets`. We now define this notation.
-/
instance : Membership (Set α) (Ultrafilter α) :=
  ⟨fun s f ↦ s ∈ (f : Filter α)⟩

/--
No proper filter `g` can be strictly finer than the ultrafilter `f`.
So if a proper filter `g` is finer than or equal to `f`, it must be the equality
that holds.
-/
theorem Ultrafilter.unique {f : Ultrafilter α} {g : Filter α} (h : g ≤ f) (hg : g ≠ ⊥) : g = f := by
  apply le_antisymm h
  exact f.le_of_le hg h

/-!
Now we show that the conversion from ultrafilters to filters is "direct enough".
These are mostly technical details...
-/

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

/-!
Now, it's time to do some amazing puzzles!

Our main goal: `f` is an ultrafilter if and only if `∀ s, s ∈ f ↔ sᶜ ∉ f`.
The following lemma might be helpful in the proof of the forward direction.
-/

/-!
Hint: the Mathlib lemmas `le_of_inf_eq`, `inf_le_left` and `inf_le_right`,
applicable on all instances of `SemilatticeInf`, can be useful here.
-/
theorem Ultrafilter.le_of_inf_ne_bot {f : Ultrafilter α} {g : Filter α} (hg : ↑f ⊓ g ≠ ⊥) : ↑f ≤ g := by
  apply le_of_inf_eq
  refine unique ?_ hg
  exact inf_le_left

/-!
Here comes our main goal.

Note that the backward direction is exactly the `Filter.compl_not_mem` which
we have proved earlier.

Hints for the forward direction:

- `Filter.le_principal_iff`
- `Ultrafilter.le_of_inf_ne_bot`
- `Filter.empty_mem_iff_eq_bot`
- `Filter.mem_inf_principal_iff`
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

--! This follows directly:
theorem Ultrafilter.compl_mem_iff {f : Ultrafilter α} {s : Set α} : sᶜ ∈ f ↔ s ∉ f := by
  rw [← compl_not_mem_iff, compl_compl]

/-!
Conversely, if `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter.

Hint: `Filter.compl_not_mem` might be helpful.
-/
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
