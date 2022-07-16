import field_theory.normal
import field_theory.is_alg_closed.algebraic_closure
import field_theory.fixed
import field_theory.primitive_element
import field_theory.algebraic_lattice

section intermediate_field_constructions

variables {F L L' : Type*} [field F] [field L] [field L'] [algebra F L] [algebra F L']
  (S T : intermediate_field F L) (f : L' →ₐ[F] L)

def alg_hom.field_range : intermediate_field F L :=
{ .. f.range,
  .. f.to_ring_hom.field_range }

noncomputable def alg_hom.equiv_field_range (f : L' →ₐ[F] L) : L' ≃ₐ[F] f.field_range :=
alg_equiv.of_injective f f.to_ring_hom.injective

def intermediate_field.comap :
  intermediate_field F L' :=
{ inv_mem' := λ x hx, show f x⁻¹ ∈ S, from (f.map_inv x).symm ▸ S.inv_mem hx,
  neg_mem' := λ x hx, (S.to_subalgebra.comap' f).neg_mem hx,
  .. S.to_subalgebra.comap' f }

variables {S T f}

lemma intermediate_field.mem_comap {x : L'} : x ∈ S.comap f ↔ f x ∈ S :=
iff.rfl

lemma intermediate_field.comap_mono (h : S ≤ T) : S.comap f ≤ T.comap f :=
λ x hx, h hx

end intermediate_field_constructions

section technical_lemmas

variables {K L : Type*} [field K] [field L] [algebra K L]

instance intermediate_field.finite_dimensional_supr_of_finite
  {ι : Type*} {t : ι → intermediate_field K L} [h : finite ι] [Π i, finite_dimensional K (t i)] :
  finite_dimensional K (⨆ i, t i : intermediate_field K L) :=
begin
  rw ← supr_univ,
  let P : set ι → Prop := λ s, finite_dimensional K (⨆ i ∈ s, t i : intermediate_field K L),
  change P set.univ,
  apply set.finite.induction_on,
  { exact set.finite_univ },
  all_goals { dsimp only [P] },
  { rw supr_emptyset,
    exact (intermediate_field.bot_equiv K L).symm.to_linear_equiv.finite_dimensional },
  { intros _ s _ _ hs,
    rw supr_insert,
    haveI : finite_dimensional K (⨆ i ∈ s, t i : intermediate_field K L) := hs,
    apply intermediate_field.finite_dimensional_sup },
end

instance intermediate_field.finite_dimensional_supr_of_mem_finset
  {ι : Type*} {f : ι → intermediate_field K L} {s : finset ι}
  [h : Π i ∈ s, finite_dimensional K (f i)] :
  finite_dimensional K (⨆ i ∈ s, f i : intermediate_field K L) :=
begin
  let t : {i // i ∈ s} → intermediate_field K L := λ i, f i,
  haveI : Π i, finite_dimensional K (t i) := λ i, h i i.2,
  have : (⨆ i ∈ s, f i) = ⨆ i, t i :=
  le_antisymm (supr_le (λ i, supr_le (λ h, le_supr t ⟨i, h⟩)))
    (supr_le (λ i, le_supr_of_le i (le_supr_of_le i.2 le_rfl))),
  rw this,
  apply_instance,
end

end technical_lemmas

section the_really_technical_lemmas

variables {K L : Type*} [field K] [field L] [algebra K L]

lemma intermediate_field.algebraic_iff {F : intermediate_field K L} {x : F} :
  is_algebraic K x ↔ is_algebraic K (x : L) :=
begin
  rw [is_algebraic_iff_is_integral, is_algebraic_iff_is_integral],
  exact (is_integral_algebra_map_iff (algebra_map F L).injective).symm,
end

lemma key_lemma {ι : Type*} {f : ι → intermediate_field K L}
  (h : ∀ i, algebra.is_algebraic K (f i)) {x : L} (hx : x ∈ ⨆ i, f i) :
  ∃ s : finset (Σ i, f i), x ∈ ⨆ i ∈ s,
    intermediate_field.adjoin K ((minpoly K (i.2 : L)).root_set L) :=
begin
  refine intermediate_field.exists_finset_of_mem_supr _,
  refine set_like.le_def.mp (supr_le (λ i x hx, _)) hx,
  refine set_like.le_def.mp (le_supr_of_le ⟨i, x, hx⟩ le_rfl) _,
  refine intermediate_field.subset_adjoin K ((minpoly K x).root_set L) _,
  refine (polynomial.mem_root_set_iff (minpoly.ne_zero _) x).mpr (minpoly.aeval K x),
  exact is_algebraic_iff_is_integral.mp (intermediate_field.algebraic_iff.mp (h i ⟨x, hx⟩)),
end

instance key_instance {x : L} [normal K L] : (minpoly K x).is_splitting_field K
  (intermediate_field.adjoin K ((minpoly K x).root_set L)) :=
sorry

end the_really_technical_lemmas

section more_technical_lemmas

variables {K L : Type*} [field K] [field L] [algebra K L]

lemma key_alg_lemma {ι : Type*} {f : ι → intermediate_field K L} {x : L} (hx : x ∈ ⨆ i, f i) :
  ∃ s : finset (Σ i, f i), x ∈ ⨆ i ∈ s, K⟮(i.2 : L)⟯ :=
intermediate_field.exists_finset_of_mem_supr
  (set_like.le_def.mp (supr_le (λ i x h, set_like.le_def.mp (le_supr_of_le ⟨i, x, h⟩ le_rfl)
    (intermediate_field.mem_adjoin_simple_self K x))) hx)

lemma intermediate_field.is_algebraic_supr
  {ι : Type*} {t : ι → intermediate_field K L} (h : ∀ i, algebra.is_algebraic K (t i)) :
  algebra.is_algebraic K (⨆ i, t i : intermediate_field K L) :=
begin
  rintros ⟨x, hx⟩,
  obtain ⟨s, hs⟩ := key_alg_lemma hx,
  haveI : ∀ i : (Σ i, t i), finite_dimensional K K⟮(i.2 : L)⟯,
  { rintros ⟨i, x⟩,
    specialize h i x,
    rw [intermediate_field.algebraic_iff, is_algebraic_iff_is_integral] at h,
    exact intermediate_field.adjoin.finite_dimensional h },
  have := algebra.is_algebraic_of_finite K
    (⨆ i ∈ s, K⟮(i.2 : L)⟯ : intermediate_field K L) ⟨x, hs⟩,
  rwa [intermediate_field.algebraic_iff, subtype.coe_mk] at this ⊢,
end

instance intermediate_field.normal_supr
  {ι : Type*} {t : ι → intermediate_field K L} [Π i, normal K (t i)] :
  normal K (⨆ i, t i : intermediate_field K L) :=
begin
  split,
  { -- wait for the normal refactor
    sorry },
  { intro x,
    obtain ⟨s, hs⟩ := key_lemma _ x.2,
    { -- suffices to show that `minpoly K x` splits in the smaller `intermediate_field`
      -- but the smaller `intermediate_field` is a splitting field, and hence normal
      sorry },
    { -- wait for the normal refactor
      sorry } },
end

end more_technical_lemmas

section normal_closure

variables (F K L : Type*) [field F] [field K] [field L] [algebra F K] [algebra K L] [algebra F L]
  [is_scalar_tower F K L]

/-- The normal closure of `K` in `L`. If `L` is not normal, use `rel_normal_closure` instead. -/
noncomputable! def normal_closure : intermediate_field K L :=
{ algebra_map_mem' := λ r, le_supr (λ f : K →ₐ[F] L, f.field_range)
    (is_scalar_tower.to_alg_hom F K L) ⟨r, rfl⟩,
  .. (⨆ f : K →ₐ[F] L, f.field_range).to_subfield }

example : is_scalar_tower F K (normal_closure F K L) := by apply_instance

namespace normal_closure

instance is_normal [h : normal F L] : normal F (normal_closure F K L) :=
begin
  change normal F (⨆ f : K →ₐ[F] L, f.field_range : intermediate_field F L),
  -- rewrite as a supremum of normal intermediate fields
  -- apply intermediate_field.normal_supr,
  all_goals { sorry },
end

instance is_finite_dimensional [finite_dimensional F K] :
  finite_dimensional F (normal_closure F K L) :=
begin
  haveI : ∀ f : K →ₐ[F] L, finite_dimensional F f.field_range :=
  λ f, f.to_linear_map.finite_dimensional_range,
  apply intermediate_field.finite_dimensional_supr_of_finite,
end

end normal_closure

end normal_closure

namespace intermediate_field

variables {F L : Type*} [field F] [field L] [algebra F L] (K : intermediate_field F L)

/-- The relative normal closure of `K` in `L`. -/
noncomputable def rel_normal_closure (K : intermediate_field F L) : intermediate_field F L :=
((normal_closure F K (algebraic_closure L)).comap (is_scalar_tower.to_alg_hom K L
  (algebraic_closure L))).lift2

lemma le_rel_normal_closure : K ≤ K.rel_normal_closure :=
sorry

lemma rel_normal_closure_idem :
  K.rel_normal_closure.rel_normal_closure = K.rel_normal_closure :=
sorry

end intermediate_field
