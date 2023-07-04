import FilterGame.Principal

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Semilattice

This level contains some challenging puzzles which ultimately lead to the proof
that the `≤` defined on filters, along with a notion of "greatest lower bounds",
make an algebraic structure called "semilattice".

Hint: when confronted by a goal like `∃ s, ...`, you have to come up with a
choice of `s` by yourself. Decide which `s` to use by drawing Venn diagrams.
-/

/--
The "greatest lower bound", or "infimum", of two filters `f` and `g` is defined
as the filter consisting of intersections of elements from `f` and `g`.
-/
instance : Inf (Filter α) := ⟨fun f g ↦
{ sets := { s | ∃ a ∈ f, ∃ b ∈ g, s = a ∩ b }
  univ_mem_sets := by sorry
  superset_mem_sets := by sorry
  inter_mem_sets := by sorry }⟩

/-!
The infimum of `f` and `g` is written as `f ⊓ g`, where `⊓` can be typed into
Lean using `\inf`.
-/

theorem Filter.mem_inf_def {f g : Filter α} {s : Set α} : s ∈ f ⊓ g ↔ ∃ a ∈ f, ∃ b ∈ g, s = a ∩ b := by
  exact Iff.rfl

theorem Filter.inter_mem_inf {f g : Filter α} {s t : Set α} (hs : s ∈ f) (ht : t ∈ g) : s ∩ t ∈ f ⊓ g := by
  sorry

--! Treasure "semilattice" unlocked!
instance : SemilatticeInf (Filter α) :=
{ inf := instInfFilter.inf
  inf_le_left := by sorry
  inf_le_right := by sorry
  le_inf := by sorry }

/-!
However, on our way to the ultrafilter world still resides a hidden boss...

Hint for the forward direction: use `Filter.mem_inf_def`.
Hint for the backward direction: consider `s` as `(t ∪ s) ∩ (tᶜ ∪ s)`.
-/

theorem Filter.mem_inf_principal_iff {f : Filter α} {s t : Set α} : s ∈ f ⊓ 𝓟 t ↔ {x | x ∈ t → x ∈ s} ∈ f := by
  sorry

end FilterGame
