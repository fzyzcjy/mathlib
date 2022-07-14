import field_theory.normal
import field_theory.is_alg_closed.algebraic_closure
import field_theory.fixed
import field_theory.primitive_element

section intermediate_field_constructions

variables {F L L' : Type*} [field F] [field L] [field L'] [algebra F L] [algebra F L']
  (S T : intermediate_field F L) (f : L' →ₐ[F] L)

def alg_hom.field_range : intermediate_field F L :=
{ .. f.range,
  .. f.to_ring_hom.field_range }

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

variables {F K L : Type*} [field F] [field K] [field L] [algebra F K] [algebra F L]

instance intermediate_field.finite_dimensional_supr_of_finite
  {ι : Type*} {t : ι → intermediate_field F K} [h : finite ι] [Π i, finite_dimensional F (t i)] :
  finite_dimensional F (⨆ i, t i : intermediate_field F K) :=
begin
  rw ← supr_univ,
  let P : set ι → Prop := λ s, finite_dimensional F (⨆ i ∈ s, t i : intermediate_field F K),
  change P set.univ,
  apply set.finite.induction_on,
  { exact set.finite_univ },
  all_goals { dsimp only [P] },
  { rw supr_emptyset,
    exact (intermediate_field.bot_equiv F K).symm.to_linear_equiv.finite_dimensional },
  { intros _ s _ _ hs,
    rw supr_insert,
    haveI : finite_dimensional F (⨆ i ∈ s, t i : intermediate_field F K) := hs,
    apply intermediate_field.finite_dimensional_sup },
end

end technical_lemmas

section more_technical_lemmas

variables {F K : Type*} [field F] [field K] [algebra F K]

instance intermediate_field.normal_supr
  {ι : Type*} {t : ι → intermediate_field F K} [h : finite ι] [Π i, normal F (t i)] :
  normal F (⨆ i, t i : intermediate_field F K) :=
begin
  sorry
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
  -- change normal F (⨆ f : K →ₐ[F] L, f.field_range : intermediate_field F L),
  sorry,
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

/-namespace intermediate_field

variables {F L : Type*} [field F] [field L] [algebra F L] (K : intermediate_field F L)

/-- The relative normal closure of `K` in `L`. -/
noncomputable def rel_normal_closure : intermediate_field F L :=
(normal_closure F K (algebraic_closure L)).comap
  (is_scalar_tower.to_alg_hom F L (algebraic_closure L))

lemma le_rel_normal_closure : K ≤ K.rel_normal_closure :=
le_trans (by exact λ x hx, ⟨⟨x, hx⟩, rfl⟩) (comap_mono (le_supr alg_hom.field_range
  (is_scalar_tower.to_alg_hom F K (algebraic_closure L))))

lemma rel_normal_closure_rel_normal_closure :
  K.rel_normal_closure.rel_normal_closure = K.rel_normal_closure :=
begin
  refine le_antisymm (comap_mono _) K.rel_normal_closure.le_rel_normal_closure,
  let g := is_scalar_tower.to_alg_hom F L (algebraic_closure L),
  let Kbar := supr (λ f : K →ₐ[F] algebraic_closure L, f.field_range),
  refine Sup_le _,
  rintros - ⟨f : Kbar.comap g →ₐ[F] algebraic_closure L, rfl⟩,
  change f.field_range ≤ Kbar,
  -- basically, Kbar is normal
end

end intermediate_field

namespace intermediate_field

variables {F L : Type*} [field F] [field L] [algebra F L] (K K' : intermediate_field F L)

-- todo: rename to `rel_normal_closure`
noncomputable def normal_closure : intermediate_field F L :=
(supr (λ f : K →ₐ[F] algebraic_closure L, f.field_range)).comap
  (is_scalar_tower.to_alg_hom F L (algebraic_closure L))

lemma le_normal_closure : K ≤ K.normal_closure :=
le_trans (by exact λ x hx, ⟨⟨x, hx⟩, rfl⟩) (comap_mono (le_supr alg_hom.field_range
  (is_scalar_tower.to_alg_hom F K (algebraic_closure L))))

lemma normal_closure_normal_closure : K.normal_closure.normal_closure = K.normal_closure :=
begin
  refine le_antisymm (comap_mono _) K.normal_closure.le_normal_closure,
  let g := is_scalar_tower.to_alg_hom F L (algebraic_closure L),
  let Kbar := supr (λ f : K →ₐ[F] algebraic_closure L, f.field_range),
  refine Sup_le _,
  rintros - ⟨f : Kbar.comap g →ₐ[F] algebraic_closure L, rfl⟩,
  change f.field_range ≤ Kbar,
  -- basically, Kbar is normal
end

end intermediate_field

section normal_closure

variables (F K L : Type*) [field F] [field K] [field L] [algebra F K] [algebra K L] [algebra F L]
  [is_scalar_tower F K L]

noncomputable def normal_closure : intermediate_field K L :=
sorry

end normal_closure-/
