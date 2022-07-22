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

lemma field_range_eq_map_top : f.field_range = (⊤ : intermediate_field F L').map f :=
sorry

noncomputable def alg_hom.equiv_field_range (f : L' →ₐ[F] L) : L' ≃ₐ[F] f.field_range :=
alg_equiv.of_injective f f.to_ring_hom.injective

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

section technical_lemmas

variables {K L : Type*} [field K] [field L] [algebra K L]

end technical_lemmas

namespace intermediate_field

variables {F E : Type*} [field F] [field E] [algebra F E]

lemma is_algebraic_algebra_map_iff {R A B : Type*} [comm_ring R] [comm_ring A]
  [ring B] [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B] {x : A}
  (hx : function.injective (algebra_map A B)) :
  is_algebraic R (algebra_map A B x) ↔ is_algebraic R x :=
⟨λ ⟨p, hp0, hp⟩, ⟨p, hp0, hx (by rwa [map_zero, ←is_scalar_tower.to_alg_hom_apply R A B,
  ←polynomial.aeval_alg_hom_apply, is_scalar_tower.to_alg_hom_apply R A B])⟩,
  is_algebraic_algebra_map_of_is_algebraic⟩

lemma algebraic_iff {K : intermediate_field F E} {x : K} :
  is_algebraic F x ↔ is_algebraic F (x : E) :=
(is_algebraic_algebra_map_iff (algebra_map K E).injective).symm

lemma key_alg_lemma {ι : Type*} {f : ι → intermediate_field F E} {x : E} (hx : x ∈ ⨆ i, f i) :
  ∃ s : finset (Σ i, f i), x ∈ ⨆ i ∈ s, F⟮(i.2 : E)⟯ :=
intermediate_field.exists_finset_of_mem_supr
  (set_like.le_def.mp (supr_le (λ i x h, set_like.le_def.mp (le_supr_of_le ⟨i, x, h⟩ le_rfl)
    (intermediate_field.mem_adjoin_simple_self F x))) hx)

lemma intermediate_field.is_algebraic_supr
  {ι : Type*} {t : ι → intermediate_field F E} (h : ∀ i, algebra.is_algebraic F (t i)) :
  algebra.is_algebraic F (⨆ i, t i : intermediate_field F E) :=
begin
  rintros ⟨x, hx⟩,
  obtain ⟨s, hs⟩ := key_alg_lemma hx,
  haveI : ∀ i : (Σ i, t i), finite_dimensional F F⟮(i.2 : E)⟯,
  { rintros ⟨i, x⟩,
    specialize h i x,
    rw [intermediate_field.algebraic_iff, is_algebraic_iff_is_integral] at h,
    exact intermediate_field.adjoin.finite_dimensional h },
  have := algebra.is_algebraic_of_finite F
    (⨆ i ∈ s, F⟮(i.2 : E)⟯ : intermediate_field F E) ⟨x, hs⟩,
  rwa [intermediate_field.algebraic_iff, subtype.coe_mk] at this ⊢,
end

end intermediate_field

section more_technical_lemmas

variables {K L : Type*} [field K] [field L] [algebra K L]

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

open_locale big_operators

open polynomial

lemma intermediate_field.splits_of_splits {p : polynomial K} {F : intermediate_field K L}
  (hp : p.splits (algebra_map K L)) (hF : ∀ x ∈ p.root_set L, x ∈ F) :
  p.splits (algebra_map K F) :=
begin
  classical,
  simp_rw [root_set, finset.mem_coe, multiset.mem_to_finset] at hF,
  refine (splits_iff_exists_multiset (algebra_map K F)).mpr
    ⟨(p.map (algebra_map K L)).roots.map (λ x, if hx : x ∈ F then (⟨x, hx⟩ : F) else 0), _⟩,
  apply map_injective (algebra_map F L) (algebra_map F L).injective,
  simp_rw [polynomial.map_mul, polynomial.map_multiset_prod, multiset.map_map, map_C, map_map],
  refine (eq_prod_roots_of_splits hp).trans (congr_arg ((*) (C _))
    (congr_arg multiset.prod (multiset.map_congr rfl (λ x hx, _)))),
  rw [function.comp_app, function.comp_app, dif_pos (hF x hx), polynomial.map_sub, map_X, map_C],
  refl,
end

def intermediate_field.of_is_field {R A : Type*} [field R] [field A] [algebra R A]
  {S : subalgebra R A} (hS : is_field S) : intermediate_field R A :=
S.to_intermediate_field begin
  intros x hx,
  by_cases hx0 : x = 0,
  { rw [hx0, inv_zero],
    exact S.zero_mem },
  letI hS' := hS.to_field,
  suffices : ((⟨x, hx⟩ : S)⁻¹ : A) = ((⟨x, hx⟩⁻¹ : S) : A),
  { rw subtype.coe_mk at this,
    rw this,
    apply set_like.coe_mem },
  apply inv_eq_of_mul_eq_one_right,
  rw [←subalgebra.coe_mul, subalgebra.coe_eq_one],
  apply mul_inv_cancel,
  rwa [ne, subtype.ext_iff, subtype.coe_mk],
end

lemma intermediate_field.adjoin_algebraic_to_subalgebra
  (S : set L) (hS : ∀ x ∈ S, is_algebraic K x) :
  (intermediate_field.adjoin K S).to_subalgebra = algebra.adjoin K S :=
begin
  simp only [is_algebraic_iff_is_integral] at hS,
  have : algebra.is_integral K (algebra.adjoin K S) :=
  by rwa [←le_integral_closure_iff_is_integral, algebra.adjoin_le_iff],
  have := is_field_of_is_integral_of_is_field' this (field.to_is_field K),
  rw ← (intermediate_field.of_is_field this).eq_adjoin_of_eq_algebra_adjoin K S; refl,
end

lemma key_instance' {p : polynomial K} (hp : p.splits (algebra_map K L)) :
  p.is_splitting_field K (intermediate_field.adjoin K (p.root_set L)) :=
begin
  classical,
  by_cases hp0 : p = 0,
  { rw [hp0, polynomial.root_set_zero, intermediate_field.adjoin_empty],
    haveI : subsingleton (subalgebra K (⊥ : intermediate_field K L)) :=
    subsingleton_of_bot_eq_top (subalgebra.bot_eq_top_of_dim_eq_one (intermediate_field.dim_bot)),
    exact ⟨polynomial.splits_zero _, subsingleton.elim _ _⟩ },
  refine ⟨intermediate_field.splits_of_splits hp (intermediate_field.subset_adjoin K (p.root_set L)), _⟩,
  rw [←polynomial.root_set, eq_top_iff],
  let f := is_scalar_tower.to_alg_hom K (intermediate_field.adjoin K (p.root_set L)) L,
  let g := λ S, subalgebra.map S f,
  have h0 : ∀ S T : subalgebra K (intermediate_field.adjoin K (p.root_set L)), S.map f ≤ T.map f → S ≤ T,
  { -- should be a lemma
    intros S T h x hx,
    have key : ↑x ∈ S.map f := ⟨x, hx, rfl⟩,
    obtain ⟨y, hy, heq⟩ := h key,
    rwa ← (algebra_map (intermediate_field.adjoin K (p.root_set L)) L).injective heq },
  refine h0 _ _ _,
  rw algebra.map_top,
  have key0 : f.range = (intermediate_field.adjoin K (p.root_set L)).to_subalgebra,
  { refine subalgebra.ext (λ x, ⟨_, λ h, ⟨⟨x, h⟩, rfl⟩⟩),
    rintros ⟨y, rfl⟩,
    exact y.prop },
  rw key0,
  have key : (intermediate_field.adjoin K (p.root_set L)).to_subalgebra =
    algebra.adjoin K (p.root_set L),
  { -- painful!
    apply intermediate_field.adjoin_algebraic_to_subalgebra,
    intros x hx,
    refine ⟨p, hp0, (mem_root_set hp0).mp hx⟩ },
  rw key,
  rw ← algebra.adjoin_algebra_map,
  apply algebra.adjoin_mono,
  intros x hx,
  refine ⟨⟨x, intermediate_field.subset_adjoin K (p.root_set L) hx⟩, _, rfl⟩,
  rw polynomial.mem_root_set hp0 at hx ⊢,
  apply (algebra_map (intermediate_field.adjoin K (p.root_set L)) L).injective,
  rw map_zero,
  rwa is_scalar_tower.algebra_map_aeval,
end

instance key_instance {x : L} [h : normal K L] : (minpoly K x).is_splitting_field K
  (intermediate_field.adjoin K ((minpoly K x).root_set L)) :=
key_instance' (h.splits x)

instance intermediate_field.normal_supr
  {ι : Type*} {t : ι → intermediate_field K L} [h : Π i, normal K (t i)] :
  normal K (⨆ i, t i : intermediate_field K L) :=
begin
  refine ⟨intermediate_field.intermediate_field.is_algebraic_supr (λ i, (h i).1), λ x, _⟩,
  obtain ⟨s, hx⟩ := key_lemma (λ i, (h i).1) x.2,
  let F : intermediate_field K L := ⨆ i ∈ s,
    intermediate_field.adjoin K ((minpoly K (i.2 : L)).root_set L),
  change x.1 ∈ F at hx,
  let E : intermediate_field K L := ⨆ i, t i,
  change (minpoly K x).splits (algebra_map K E),
  have key1 : F ≤ E,
  { sorry },
  have key2: ∃ p, polynomial.is_splitting_field K F p,
  { -- prove that finite supr of splitting fields is splitting field for product
    sorry },
  have key3 : (minpoly K x).splits (algebra_map K F),
  { obtain ⟨p, hp⟩ := key2,
    have := (@normal.of_is_splitting_field K _ F _ _ p hp).splits ⟨x, hx⟩,
    sorry },
  exact polynomial.splits_comp_of_splits (algebra_map K F)
    (intermediate_field.inclusion key1).to_ring_hom key3,
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
restrict_scalars F ((normal_closure F K (algebraic_closure L)).comap
  (is_scalar_tower.to_alg_hom K L (algebraic_closure L)))

lemma le_rel_normal_closure : K ≤ K.rel_normal_closure :=
sorry

lemma rel_normal_closure_idem :
  K.rel_normal_closure.rel_normal_closure = K.rel_normal_closure :=
sorry

end intermediate_field

section fancy_way

theorem thm1 {F K L : Type*} [field F] [field K] [field L] [algebra F K] [algebra F L] [normal F K]
  (f g : K →ₐ[F] L) : f.field_range = g.field_range :=
begin
  sorry
end

theorem thm2 (F K L : Type*) [field F] [field K] [field L] [algebra F K] [algebra F L]
  [is_alg_closed L] (h : ∀ f g : K →ₐ[F] L, f.field_range ≤ g.field_range) : normal F K :=
begin
  sorry
end

lemma alg_hom.map_supr {F K L : Type*} [field F] [field K] [field L] [algebra F K]
  [algebra F L] {ι : Type*} (t : ι → intermediate_field F K) (f : K →ₐ[F] L) :
  (⨆ i, t i).map f = ⨆ i, (t i).map f :=
sorry

instance intermediate_field.normal_supr'
  {K L : Type*} [field K] [field L] [algebra K L]
  {ι : Type*} {t : ι → intermediate_field K L} [Π i, normal K (t i)] :
  normal K (⨆ i, t i : intermediate_field K L) :=
begin
  refine thm2 K (⨆ i, t i : intermediate_field K L) (algebraic_closure K) (λ f g, _),
  let u : ι → intermediate_field K (⨆ i, t i : intermediate_field K L) :=
  λ i, sorry,
  have key1 : (⊤ : intermediate_field K (⨆ i, t i : intermediate_field K L)) = ⨆ i, u i :=
  sorry,
  have key2 : ∀ i, (u i).map f = (u i).map g := sorry,
  rw [field_range_eq_map_top, key1, alg_hom.map_supr, supr_le_iff],
  intros i,
  rw key2,
  have key := alg_hom.lift_normal,
end

end fancy_way
