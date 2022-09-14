import model_theory.satisfiability
import topology.separation

universes u v w w'

open cardinal topological_space
open_locale cardinal first_order classical

namespace first_order
namespace language
namespace Theory

variables {L : language.{u v}} (T : L.Theory) (α : Type w)

/-- A complete type over a given theory in a certain type of variables is a maximally
  consistent (with the theory) set of formulas in that type. -/
structure complete_type :=
(to_Theory : L[[α]].Theory)
(is_consistent_with : ((L.Lhom_with_constants α).on_Theory T ∪ to_Theory).is_satisfiable)
(is_maximal : to_Theory.is_maximal)

variables {T α}

namespace complete_type

instance : set_like (T.complete_type α) (L.formula α) :=
⟨λ p, formula.equiv_sentence ⁻¹' p.to_Theory, λ p q h, begin
  cases p,
  cases q,
  congr',
  exact (set.preimage_eq_preimage formula.equiv_sentence.surjective).1 h,
end⟩

lemma mem_iff_mem_to_Theory {p : T.complete_type α} {φ : L.formula α} :
  φ ∈ p ↔ formula.equiv_sentence φ ∈ p.to_Theory :=
iff.rfl

lemma mem_or_not_mem (p : T.complete_type α) (φ : L.formula α) : φ ∈ p ∨ φ.not ∈ p :=
p.is_maximal.mem_or_not_mem (formula.equiv_sentence φ)

lemma mem_of_models (p : T.complete_type α) {φ : L.formula α} (h : T ⊨ φ) :
  φ ∈ p :=
begin
  have h1 : (L.Lhom_with_constants α).on_Theory T ⊨ formula.equiv_sentence φ,
  { rw models_sentence_iff,
    intros M,
    rw formula.equiv_sentence,
    simp only [equiv.symm_trans_apply],
    sorry,

  },
  refine (p.mem_or_not_mem φ).resolve_right (λ con, _),
  rw models_iff_not_satisfiable at h1,
  refine h1 (p.is_consistent_with.mono (set.union_subset_union_right _ _)),
  rw [← formula.equiv_sentence_not, set.singleton_subset_iff],
  exact con,
end

instance : topological_space (T.complete_type α) :=
topological_space.generate_from {s | ∃ φ, s = {p : T.complete_type α | φ ∈ p} }

theorem foo :
  is_topological_basis {s : set (T.complete_type α) |
    ∃ φ : L.formula α, s = {p : T.complete_type α | φ ∈ p}} :=
{ exists_subset_inter := begin
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩ p ⟨φp, ψp⟩,
    refine ⟨{ q | φ ∈ q } ∩ { q | ψ ∈ q }, ⟨φ ⊓ ψ, _⟩, ⟨φp, ψp⟩, refl _⟩,
    ext q,
    simp only [set.mem_inter_eq, set.mem_set_of_eq, mem_iff_mem_to_Theory,
      q.is_maximal.mem_iff_models, models_sentence_iff, ← forall_and_distrib, forall_congr,
      formula.equiv_sentence_inf, sentence.realize, formula.realize_inf]
  end,
  sUnion_eq := begin
    ext p,
    simp only [set.mem_sUnion, set.mem_set_of_eq, exists_prop, set.mem_univ, iff_true],
    refine ⟨_, ⟨⊤, rfl⟩, _⟩,
    simp only [set.mem_set_of_eq],
  end,
  eq_generate_from := rfl,

}

theorem closed_embedding :
  closed_embedding (λ (p : T.complete_type α) (φ : L.formula α), (φ ∈ p : bool)) :=
⟨⟨sorry, sorry⟩, begin
  suffices h : is_closed { s : (L.formula α) → Prop | Theory.is_maximal
    ((L.Lhom_with_constants α).on_Theory T ∪ formula.equiv_sentence '' s) },
  { refine (congr rfl (set.ext (λ s, _))).mp h,
    simp only [set.mem_set_of_eq, set.mem_range],
    refine ⟨λ h, ⟨⟨s, h⟩, rfl⟩, _⟩,
    rintro ⟨p, rfl⟩,
    exact p.is_maximal },
  simp_rw [Theory.is_maximal, is_satisfiable_iff_is_finitely_satisfiable, is_finitely_satisfiable,
    set.set_of_and, set.set_of_forall, set.mem_union_eq, set.set_of_or, set.mem_image_equiv],
  refine (is_closed_Inter (λ s, _)).inter
    (is_closed_Inter (λ φ, (is_closed.union _ _).union (is_closed.union _ _))),
  { by_cases hs : is_satisfiable (s : L[[α]].Theory),
    { simp_rw [hs, implies_true_iff, set.set_of_true, is_closed_univ] },
    { simp_rw [hs, imp_false, ← set.compl_set_of, is_closed_compl_iff, set.subset_def,
        set.set_of_forall],
      refine is_open_bInter_finset (λ φ φs, _),
      by_cases φT : φ ∈ (L.Lhom_with_constants α).on_Theory T,
      { simp only [φT, set.mem_union_eq, true_or, set.set_of_true, is_open_univ] },
      { simp only [φT, set.mem_union_eq, false_or, set.mem_image_equiv],
        refine (congr rfl _).mp (is_open_singleton_true.preimage
          (continuous_apply (formula.equiv_sentence.symm φ))),
        ext,
        simp only [set.mem_preimage, set.mem_singleton_iff, eq_iff_iff, iff_true],
        refl } } },
  { by_cases hφ : φ ∈ (L.Lhom_with_constants α).on_Theory T;
    simp [hφ], },
  { refine (congr rfl _).mp (is_closed_singleton.preimage
          (continuous_apply (formula.equiv_sentence.symm φ))),

  }
end⟩

instance : compact_space (T.complete_type α) :=
begin
  refine closed_embedding.compact_space _,
end

end complete_type

end Theory
end language
end first_order
