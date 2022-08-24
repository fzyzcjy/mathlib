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

lemma intermediate_field.map_top : f.field_range = (⊤ : intermediate_field F L').map f :=
intermediate_field.ext (λ x, ⟨λ ⟨y, h⟩, ⟨y, trivial, h⟩, λ ⟨y, _, h⟩, ⟨y, h⟩⟩)

-- noncomputable def alg_hom.equiv_field_range (f : L' →ₐ[F] L) : L' ≃ₐ[F] f.field_range :=
-- alg_equiv.of_injective f f.to_ring_hom.injective

def intermediate_field.comap : intermediate_field F L' :=
{ inv_mem' := λ x hx, show f x⁻¹ ∈ S, from (f.map_inv x).symm ▸ S.inv_mem hx,
  neg_mem' := λ x hx, (S.to_subalgebra.comap f).neg_mem hx,
  .. S.to_subalgebra.comap f }

variables {S T f}

lemma intermediate_field.mem_comap {x : L'} : x ∈ S.comap f ↔ f x ∈ S :=
iff.rfl

lemma intermediate_field.comap_mono (h : S ≤ T) : S.comap f ≤ T.comap f :=
λ x hx, h hx

end intermediate_field_constructions

section more_technical_lemmas

variables {K L : Type*} [field K] [field L] [algebra K L]

open_locale big_operators

open polynomial

namespace intermediate_field

-- PRed
lemma is_splitting_field_iff {p : polynomial K} {F : intermediate_field K L} :
  p.is_splitting_field K F ↔ p.splits (algebra_map K F) ∧ F = adjoin K (p.root_set L) :=
begin
  suffices : p.splits (algebra_map K F) →
    ((algebra.adjoin K (p.root_set F) = ⊤ ↔ F = adjoin K (p.root_set L))),
  { exact ⟨λ h, ⟨h.1, (this h.1).mp h.2⟩, λ h, ⟨h.1, (this h.1).mpr h.2⟩⟩ },
  simp_rw [set_like.ext_iff, ←mem_to_subalgebra, ←set_like.ext_iff, ←F.range_val],
  intro hp,
  rw [adjoin_algebraic_to_subalgebra (λ x, is_algebraic_of_mem_root_set), ←image_root_set hp F.val,
      algebra.adjoin_image, ←algebra.map_top, (subalgebra.map_injective _).eq_iff, eq_comm],
  exact (algebra_map F L).injective,
end

end intermediate_field

-- PRed
lemma adjoin_root_set_is_splitting_field {p : polynomial K} (hp : p.splits (algebra_map K L)) :
  p.is_splitting_field K (intermediate_field.adjoin K (p.root_set L)) :=
intermediate_field.is_splitting_field_iff.mpr ⟨intermediate_field.splits_of_splits hp
  (λ x hx, intermediate_field.subset_adjoin K (p.root_set L) hx), rfl⟩

-- PRed
lemma root_set_prod {ι : Type*} {s : finset ι} {p : ι → polynomial K} (h : ∀ i ∈ s, p i ≠ 0) :
  (∏ i in s, p i).root_set L = ⋃ i ∈ s, (p i).root_set L :=
begin
  classical,
  rw [root_set, polynomial.map_prod, roots_prod, finset.bind_to_finset, finset.val_to_finset,
      finset.coe_bUnion],
  { refl },
  { rw finset.prod_ne_zero_iff,
    intros i hi,
    apply map_ne_zero,
    exact h i hi },
end

lemma intermediate_field.splitting_field_supr {ι : Type*} {t : ι → intermediate_field K L}
  {p : ι → polynomial K} {s : finset ι} (h0 : ∀ i ∈ s, p i ≠ 0)
  (h : ∀ i ∈ s, (p i).is_splitting_field K (t i)) :
  (∏ i in s, p i).is_splitting_field K (⨆ i ∈ s, t i : intermediate_field K L) :=
begin
  let F : intermediate_field K L := ⨆ i ∈ s, t i,
  have hF : ∀ i ∈ s, t i ≤ F := λ i hi, le_supr_of_le i (le_supr (λ _, t i) hi),
  simp only [intermediate_field.is_splitting_field_iff] at h ⊢,
  refine ⟨splits_prod (algebra_map K F) (λ i hi, polynomial.splits_comp_of_splits
    (algebra_map K (t i)) (intermediate_field.inclusion (hF i hi)).to_ring_hom (h i hi).1), _⟩,
  simp only [root_set_prod h0, ←set.supr_eq_Union, (@intermediate_field.gc K _ L _ _).l_supr₂],
  exact supr_congr (λ i, supr_congr (λ hi, (h i hi).2)),
end

namespace intermediate_field

lemma exists_finset_of_mem_supr'' {ι : Type*} {f : ι → intermediate_field K L}
  (h : ∀ i, algebra.is_algebraic K (f i)) {x : L} (hx : x ∈ ⨆ i, f i) :
  ∃ s : finset (Σ i, f i), x ∈ ⨆ i ∈ s, adjoin K ((minpoly K (i.2 : f (i.1 : ι))).root_set L) :=
begin
  refine exists_finset_of_mem_supr (set_like.le_def.mp (supr_le (λ i x hx, set_like.le_def.mp
    (le_supr_of_le ⟨i, x, hx⟩ le_rfl) (subset_adjoin K _ _))) hx),
  rw [intermediate_field.minpoly_eq, subtype.coe_mk, polynomial.mem_root_set, minpoly.aeval],
  refine minpoly.ne_zero (is_integral_iff.mp (is_algebraic_iff_is_integral.mp (h i ⟨x, hx⟩))),
end

instance normal_supr
  {ι : Type*} (t : ι → intermediate_field K L) [h : ∀ i, normal K (t i)] :
  normal K (⨆ i, t i : intermediate_field K L) :=
begin
  refine ⟨is_algebraic_supr (λ i, (h i).1), λ x, _⟩,
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr'' (λ i, (h i).1) x.2,
  let F : intermediate_field K L := ⨆ i ∈ s, adjoin K ((minpoly K (i.2 : t (i.1 : ι))).root_set L),
  have hF : normal K F,
  { apply normal.of_is_splitting_field (∏ i in s, minpoly K (i.2 : t (i.1 : ι))),
    refine splitting_field_supr (λ i hi, minpoly.ne_zero ((h i.1).is_integral i.2)) (λ i hi, _),
    apply adjoin_root_set_is_splitting_field,
    exact polynomial.splits_comp_of_splits _ (algebra_map (t i.1) L) ((h i.1).splits i.2) },
  have hFE : F ≤ ⨆ i, t i,
  { refine supr_le (λ i, supr_le (λ hi, le_supr_of_le i.1 _)),
    rw [adjoin_le_iff, ←image_root_set ((h i.1).splits i.2) (t i.1).val],
    exact λ _ ⟨a, _, h⟩, h ▸ a.2 },
  have := hF.splits ⟨x, hx⟩,
  rw [minpoly_eq, subtype.coe_mk, ←minpoly_eq] at this,
  exact polynomial.splits_comp_of_splits _ (inclusion hFE).to_ring_hom this,
end

end intermediate_field

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

lemma restrict_scalars_eq_supr_adjoin [h : normal F L] :
  (normal_closure F K L).restrict_scalars F =
  ⨆ x : K, intermediate_field.adjoin F ((minpoly F x).root_set L) :=
begin
  refine le_antisymm (supr_le _) (supr_le (λ x, _)),
  { rintros f _ ⟨x, rfl⟩,
    refine le_supr (λ x, intermediate_field.adjoin F ((minpoly F x).root_set L)) x
      (intermediate_field.subset_adjoin F ((minpoly F x).root_set L) _),
    rw [polynomial.mem_root_set, alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom,
        polynomial.aeval_alg_hom_apply, minpoly.aeval, map_zero],
    exact minpoly.ne_zero ((is_integral_algebra_map_iff (algebra_map K L).injective).mp
      (h.is_integral (algebra_map K L x))) },
  { have hx := (is_integral_algebra_map_iff
      (algebra_map K L).injective).mp (h.is_integral (algebra_map K L x)),
    rw intermediate_field.adjoin_le_iff,
    intros y hy,
    rw [polynomial.root_set, finset.mem_coe, multiset.mem_to_finset] at hy,
    let g := (intermediate_field.alg_hom_adjoin_integral_equiv F hx).symm ⟨y, hy⟩,
    have hg : g (intermediate_field.adjoin_simple.gen F x) = y :=
    begin
      simp only [g, intermediate_field.alg_hom_adjoin_integral_equiv, equiv.symm_trans_apply,
        power_basis.lift_equiv', power_basis.lift_equiv_symm_apply],
      simp only [equiv.subtype_equiv_symm, equiv.subtype_equiv_apply, equiv.refl_symm,
        equiv.refl_apply, subtype.coe_mk],
      apply power_basis.lift_gen,
    end,
    exact le_supr (λ f : K →ₐ[F] L, f.field_range)
      ((g.lift_normal L).comp (is_scalar_tower.to_alg_hom F K L))
      ⟨x, (g.lift_normal_commutes L (intermediate_field.adjoin_simple.gen F x)).trans hg⟩ },
end

instance normal [h : normal F L] : normal F (normal_closure F K L) :=
begin
  change normal F ((normal_closure F K L).restrict_scalars F),
  rw restrict_scalars_eq_supr_adjoin,
  apply intermediate_field.normal_supr _,
  intro x,
  apply normal.of_is_splitting_field (minpoly F x),
  apply adjoin_root_set_is_splitting_field,
  rw minpoly.eq_of_algebra_map_eq (algebra_map K L).injective ((is_integral_algebra_map_iff
    (algebra_map K L).injective).mp (h.is_integral (algebra_map K L x))) rfl,
  apply h.splits,
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
restrict_scalars F ((normal_closure F K (algebraic_closure L)).comap
  (is_scalar_tower.to_alg_hom K L (algebraic_closure L)))

lemma le_rel_normal_closure : K ≤ K.rel_normal_closure :=
sorry

lemma rel_normal_closure_idem :
  K.rel_normal_closure.rel_normal_closure = K.rel_normal_closure :=
sorry

end intermediate_field
