import FilterGame.Solutions.Order

set_option linter.unusedVariables false
set_option autoImplicit false

namespace FilterGame
variable {α : Type _}

/-!
# Principal filters

The partial order defined in the previous world actually makes filters a
"semilattice". But proving this fact can be quite challenging! Before we enter
the semilattice world, let's train and upgrade ourselves by playing with a
special kind of filters.
-/

/--
The so-called "principal filter on a set `s`" is the collection of
all supersets of `s`.
-/
def Filter.principal (s : Set α) : Filter α :=
{ sets              := {t | s ⊆ t}
  univ_mem_sets     := by exact Set.subset_univ s
  superset_mem_sets := by intros x y hx; exact subset_trans hx
  inter_mem_sets    := by intros x y; exact Set.subset_inter }

/-!
For convenience, we denote the principal filter on `s` as `𝓟 s`.

You can type `\MCP` (capitalisation matters) into Lean to produce this symbol.
-/

notation "𝓟" => Filter.principal

@[simp]
theorem Filter.mem_principal_def (s t : Set α) : s ∈ 𝓟 t ↔ t ⊆ s := by
  exact Iff.rfl

theorem Filter.mem_principal_self (s : Set α) : s ∈ 𝓟 s := by
  exact (mem_principal_def _ _).mpr subset_rfl

/--
A filter `f` is finer than the principal filter on `s` if and only if `s` is in
the sets of `f`.
-/
theorem Filter.le_principal_iff (s : Set α) (f : Filter α) : f ≤ 𝓟 s ↔ s ∈ f := by
  apply Iff.intro
  . intros h
    exact h _ (mem_principal_self s)
  . intros h t ht
    rw [mem_principal_def] at ht
    exact superset_mem h ht

/--
The principal filter on `s` is finer than the principal filter on `t`
if and only if `s ⊆ t`.
-/
theorem Filter.principal_mono (s t : Set α) : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t := by
  rw [le_principal_iff, mem_principal_def]

/--
The principal filter on `s` equals to the principal filter on `t`
if and only if `s = t`.
-/
@[simp]
theorem Filter.principal_eq_iff_eq (s t : Set α) : 𝓟 s = 𝓟 t ↔ s = t := by
  simp only [le_antisymm_iff, le_principal_iff, mem_principal_def]; rfl

/-!
Next, we consider the coarsest and finest elements among filters.
The coarsest one, if exists, is called the "top" element or `⊤` (type `\top`
for the symbol). The finest one, if exists, is called the "bottom" element
or `⊥` (type `\bot`).

Our goal is to prove that they both exist: `⊤ = 𝓟 Set.univ` and `⊥ = 𝓟 ∅`.
Note that `⊤` only contains the whole set and `⊥` contains every subset.
(They are the same as the first two examples defined in the initial world!)
-/

instance : OrderTop (Filter α) :=
{ top :=
  { sets              := {s | ∀ x, x ∈ s}
    univ_mem_sets     := by intros s; exact Set.mem_univ s
    superset_mem_sets := by intros s t hs hst x; exact hst (hs x)
    inter_mem_sets    := by intros s t hs ht x; exact Set.mem_inter (hs _) (ht _) }
  le_top := by
    intros f s hs
    suffices h : s = Set.univ
    . rw [h]; exact Filter.univ_mem _
    rw [Set.eq_univ_iff_forall]
    exact hs }

theorem Filter.mem_top_def (s : Set α) : s ∈ (⊤ : Filter α) ↔ ∀ x, x ∈ s := by
  exact Iff.rfl

@[simp]
theorem Filter.mem_top_iff_eq_univ (s : Set α) : s ∈ (⊤ : Filter α) ↔ s = Set.univ := by
  rw [mem_top_def, Set.eq_univ_iff_forall]

instance : OrderBot (Filter α) :=
{ bot :=
  { sets              := Set.univ
    univ_mem_sets     := by exact Set.mem_univ _
    superset_mem_sets := by intros _ _ _ _; exact Set.mem_univ _
    inter_mem_sets    := by intros _ _ _ _; exact Set.mem_univ _ }
  bot_le := by
    intros _ _ _
    exact Set.mem_univ _ }

@[simp]
theorem Filter.mem_bot (s : Set α) : s ∈ (⊥ : Filter α) := by
  exact True.intro

/--
If filter `f` contains the empty set, then it must contains every subset,
and is therefore the finest (bottom) element.
-/
theorem Filter.empty_mem_iff_eq_bot (f : Filter α) : ∅ ∈ f ↔ f = (⊥ : Filter α) := by
  apply Iff.intro
  . intros h
    apply ext
    intros s
    apply Iff.intro
    . intros _; exact True.intro
    . intros _; exact superset_mem h (Set.empty_subset _)
  . intros h
    rw [h]
    exact Set.mem_univ _

--! Hint: try applying `top_unique`.
@[simp]
theorem Filter.principal_univ_eq_top : 𝓟 Set.univ = (⊤ : Filter α) := by
  apply top_unique
  rw [le_principal_iff, mem_top_def]
  intros x
  exact True.intro

--! Hint: can you guess this hint from the above hint?
@[simp]
theorem Filter.principal_empty_eq_bot : 𝓟 ∅ = (⊥ : Filter α) := by
  apply bot_unique
  intros s hs
  exact Set.empty_subset s

--! Bonus level! Hint: `Filter.inter_mem` might be helpful.
theorem Filter.compl_not_mem {f : Filter α} {s : Set α} (hf : f ≠ ⊥) (h : s ∈ f) : sᶜ ∉ f := by
  intros h'
  apply hf
  rw [← empty_mem_iff_eq_bot, ← Set.compl_inter_self s]
  exact inter_mem h' h

end FilterGame
