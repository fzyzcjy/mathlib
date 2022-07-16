import field_theory.adjoin
import linear_algebra.span
import linear_algebra.finsupp
import order.compactly_generated

lemma complete_lattice.is_compact_element.exists_finset_of_le_supr
  (α : Type*) [complete_lattice α] (k : α) (hk : complete_lattice.is_compact_element k)
  {ι : Type*} (f : ι → α) (h : k ≤ ⨆ i, f i) : ∃ s : finset ι, k ≤ ⨆ i ∈ s, f i :=
begin
  classical,
  let g : finset ι → α := λ s, ⨆ i ∈ s, f i,
  have h1 : directed_on (≤) (set.range g),
  { rintros - ⟨s, rfl⟩ - ⟨t, rfl⟩,
    exact ⟨g (s ∪ t), ⟨s ∪ t, rfl⟩, supr_le_supr_of_subset (finset.subset_union_left s t),
      supr_le_supr_of_subset (finset.subset_union_right s t)⟩ },
  have h2 : k ≤ Sup (set.range g),
  { exact h.trans (supr_le (λ i, le_Sup_of_le ⟨{i}, rfl⟩ (le_supr_of_le i (le_supr_of_le
      (finset.mem_singleton_self i) le_rfl)))) },
  obtain ⟨-, ⟨s, rfl⟩, hs⟩ :=
    (complete_lattice.is_compact_element_iff_le_of_directed_Sup_le α k).mp hk
    (set.range g) (set.range_nonempty g) h1 h2,
  exact ⟨s, hs⟩,
end

lemma submodule.exists_finset_of_mem_supr' {R M : Type*} [semiring R]
  [add_comm_monoid M] [module R M]
  {ι : Sort*} (p : ι → submodule R M) {m : M} (hm : m ∈ ⨆ i, p i) :
  ∃ s : finset ι, m ∈ ⨆ i ∈ s, p i :=
begin
  have := complete_lattice.is_compact_element.exists_finset_of_le_supr (submodule R M)
    (submodule.span R {m}) (submodule.singleton_span_is_compact_element m) p,
  simp only [submodule.span_singleton_le_iff_mem] at this,
  exact this hm,
end

variables {K L : Type*} [field K] [field L] [algebra K L]

namespace intermediate_field

open set

lemma adjoin_simple_le_iff {x : L} {F : intermediate_field K L} : K⟮x⟯ ≤ F ↔ x ∈ F :=
adjoin_le_iff.trans set.singleton_subset_iff

/-- Adjoining a finite element is compact in the lattice of intermediate fields. -/
lemma adjoin_simple_is_compact_element (x : L) : complete_lattice.is_compact_element K⟮x⟯ :=
begin
  rw complete_lattice.is_compact_element_iff_le_of_directed_Sup_le,
  rintros s ⟨F₀, hF₀⟩ hs hx,
  simp only [adjoin_simple_le_iff] at hx ⊢,
  let F : intermediate_field K L :=
  { carrier := ⋃ E ∈ s, ↑E,
    add_mem' := by
    { rintros x₁ x₂ ⟨-, ⟨F₁, rfl⟩, ⟨-, ⟨hF₁, rfl⟩, hx₁⟩⟩ ⟨-, ⟨F₂, rfl⟩, ⟨-, ⟨hF₂, rfl⟩, hx₂⟩⟩,
      obtain ⟨F₃, hF₃, h₁₃, h₂₃⟩ := hs F₁ hF₁ F₂ hF₂,
      exact mem_Union_of_mem F₃ (mem_Union_of_mem hF₃ (F₃.add_mem (h₁₃ hx₁) (h₂₃ hx₂))) },
    neg_mem' := by
    { rintros x ⟨-, ⟨E, rfl⟩, ⟨-, ⟨hE, rfl⟩, hx⟩⟩,
      exact mem_Union_of_mem E (mem_Union_of_mem hE (E.neg_mem hx)) },
    mul_mem' := by
    { rintros x₁ x₂ ⟨-, ⟨F₁, rfl⟩, ⟨-, ⟨hF₁, rfl⟩, hx₁⟩⟩ ⟨-, ⟨F₂, rfl⟩, ⟨-, ⟨hF₂, rfl⟩, hx₂⟩⟩,
      obtain ⟨F₃, hF₃, h₁₃, h₂₃⟩ := hs F₁ hF₁ F₂ hF₂,
      exact mem_Union_of_mem F₃ (mem_Union_of_mem hF₃ (F₃.mul_mem (h₁₃ hx₁) (h₂₃ hx₂))) },
    inv_mem' := by
    { rintros x ⟨-, ⟨E, rfl⟩, ⟨-, ⟨hE, rfl⟩, hx⟩⟩,
      exact mem_Union_of_mem E (mem_Union_of_mem hE (E.inv_mem hx)) },
    algebra_map_mem' := λ x, mem_Union_of_mem F₀ (mem_Union_of_mem hF₀ (F₀.algebra_map_mem x)) },
  have key : Sup s ≤ F := Sup_le (λ E hE, set.subset_Union_of_subset E (set.subset_Union _ hE)),
  obtain ⟨-, ⟨E, rfl⟩, -, ⟨hE, rfl⟩, hx⟩ := key hx,
  exact ⟨E, hE, hx⟩,
end

/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
lemma adjoin_finset_is_compact_element (S : finset L) :
  complete_lattice.is_compact_element (adjoin K S : intermediate_field K L) :=
begin
  have key : adjoin K ↑S = ⨆ x ∈ S, K⟮x⟯ :=
  le_antisymm (adjoin_le_iff.mpr (λ x hx, set_like.mem_coe.mpr (adjoin_simple_le_iff.mp
      (le_supr_of_le x (le_supr_of_le hx le_rfl)))))
      (supr_le (λ x, supr_le (λ hx, adjoin_simple_le_iff.mpr (subset_adjoin K S hx)))),
  rw [key, ←finset.sup_eq_supr],
  exact complete_lattice.finset_sup_compact_of_compact S
    (λ x hx, adjoin_simple_is_compact_element x),
end

/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
lemma adjoin_finite_is_compact_element (S : set L) (h : S.finite) :
  complete_lattice.is_compact_element (adjoin K S) :=
finite.coe_to_finset h ▸ (adjoin_finset_is_compact_element h.to_finset)

/-- The lattice of intermediate fields is compactly generated. -/
instance : is_compactly_generated (intermediate_field K L) :=
⟨λ s, ⟨(λ x, K⟮x⟯) '' s, ⟨by rintros t ⟨x, hx, rfl⟩; exact adjoin_simple_is_compact_element x,
  Sup_image.trans (le_antisymm (supr_le (λ i, supr_le (λ hi, adjoin_simple_le_iff.mpr hi)))
    (λ x hx, adjoin_simple_le_iff.mp (le_supr_of_le x (le_supr_of_le hx le_rfl))))⟩⟩⟩

lemma exists_finset_of_mem_supr
  {ι : Type*} {f : ι → intermediate_field K L} {x : L} (hx : x ∈ ⨆ i, f i) :
  ∃ s : finset ι, x ∈ ⨆ i ∈ s, f i :=
begin
  have := complete_lattice.is_compact_element.exists_finset_of_le_supr
    (intermediate_field K L) K⟮x⟯ (adjoin_simple_is_compact_element x) f,
  simp only [adjoin_simple_le_iff] at this,
  exact this hx,
end

end intermediate_field
