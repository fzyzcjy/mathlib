/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.fiber_bundle.trivialization

/-!
# Fiber bundles

Given a "base" topological space `B` and a family `E : B → Type*` for which `bundle.total_space E`
(a type synonym for `Σ b, E b`) carries a topological space structure, a topological fiber bundle
structure for `total_space E` with fiber `F` is a system of local homeomorphisms to `B × F`, each
respecting the fiber structure ("local trivializations" of `total_space E`). We define an object
`fiber_bundle F p` carrying the data of these local trivializations.

-/

variables {ι : Type*} {B : Type*} {F : Type*}

open topological_space filter set bundle
open_locale topological_space classical bundle

noncomputable theory

/-! ### Pretrivializations -/

section general

variables (F) {Z : Type*} [topological_space B] [topological_space F] {proj : Z → B}

variable [topological_space Z]

variables (E : B → Type*)

/-! ### Fiber bundles -/

variables [topological_space (total_space E)] [∀ b, topological_space (E b)]

class fiber_bundle :=
(total_space_mk_inducing [] : ∀ (b : B), inducing (@total_space_mk B E b))
(trivialization_atlas [] : set (trivialization F (π E)))
(trivialization_at [] : B → trivialization F (π E))
(mem_base_set_trivialization_at [] : ∀ b : B, b ∈ (trivialization_at b).base_set)
(trivialization_mem_atlas [] : ∀ b : B, trivialization_at b ∈ trivialization_atlas)

export fiber_bundle

variables {F E} [fiber_bundle F E]

@[mk_iff]
class mem_trivialization_atlas (e : trivialization F (π E)) : Prop :=
(out : e ∈ trivialization_atlas F E)

namespace fiber_bundle

variables (F)
lemma map_proj_nhds (x : total_space E) :
  map (π E) (𝓝 x) = 𝓝 x.proj :=
(trivialization_at F E x.proj).map_proj_nhds $
  (trivialization_at F E x.proj).mem_source.2 $ mem_base_set_trivialization_at F E x.proj

variables (E)
/-- The projection from a topological fiber bundle to its base is continuous. -/
@[continuity] lemma continuous_proj : continuous (π E) :=
continuous_iff_continuous_at.2 $ λ x, (map_proj_nhds F x).le

/-- The projection from a topological fiber bundle to its base is an open map. -/
lemma is_open_map_proj : is_open_map (π E) :=
is_open_map.of_nhds_le $ λ x, (map_proj_nhds F x).ge

/-- The projection from a topological fiber bundle with a nonempty fiber to its base is a surjective
map. -/
lemma surjective_proj [nonempty F] : function.surjective (π E) :=
λ b, let ⟨p, _, hpb⟩ :=
  (trivialization_at F E b).proj_surj_on_base_set (mem_base_set_trivialization_at F E b) in ⟨p, hpb⟩

/-- The projection from a topological fiber bundle with a nonempty fiber to its base is a quotient
map. -/
lemma quotient_map_proj [nonempty F] : quotient_map (π E) :=
(is_open_map_proj F E).to_quotient_map (continuous_proj F E) (surjective_proj F E)

lemma continuous_total_space_mk (x : B) : continuous (@total_space_mk B E x) :=
(total_space_mk_inducing F E x).continuous

end fiber_bundle

/-- Core data defining a locally trivial topological bundle with fiber `F` over a topological
space `B`. Note that "bundle" is used in its mathematical sense. This is the (computer science)
bundled version, i.e., all the relevant data is contained in the following structure. A family of
local trivializations is indexed by a type `ι`, on open subsets `base_set i` for each `i : ι`.
Trivialization changes from `i` to `j` are given by continuous maps `coord_change i j` from
`base_set i ∩ base_set j` to the set of homeomorphisms of `F`, but we express them as maps
`B → F → F` and require continuity on `(base_set i ∩ base_set j) × F` to avoid the topology on the
space of continuous maps on `F`. -/
@[nolint has_nonempty_instance]
structure fiber_bundle_core (ι : Type*) (B : Type*) [topological_space B]
  (F : Type*) [topological_space F] :=
(base_set          : ι → set B)
(is_open_base_set  : ∀ i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀ x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → F → F)
(coord_change_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v)
(continuous_on_coord_change : ∀ i j, continuous_on (λp : B × F, coord_change i j p.1 p.2)
                                               (((base_set i) ∩ (base_set j)) ×ˢ univ))
(coord_change_comp : ∀ i j k, ∀ x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀ v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

namespace fiber_bundle_core

variables [topological_space B] [topological_space F] (C : fiber_bundle_core ι B F)

include C

/-- The index set of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_nonempty_instance]
def index := ι

/-- The base space of a topological fiber bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a topological fiber bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_nonempty_instance]
def fiber (x : B) := F

section fiber_instances
local attribute [reducible] fiber

instance topological_space_fiber (x : B) : topological_space (C.fiber x) := by apply_instance

end fiber_instances

/-- The total space of the topological fiber bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space C.fiber`, a.k.a. `Σ x, C.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def total_space := bundle.total_space C.fiber

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : C.total_space → B := bundle.total_space.proj

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
{ source      := (C.base_set i ∩ C.base_set j) ×ˢ univ,
  target      := (C.base_set i ∩ C.base_set j) ×ˢ univ,
  to_fun      := λp, ⟨p.1, C.coord_change i j p.1 p.2⟩,
  inv_fun     := λp, ⟨p.1, C.coord_change j i p.1 p.2⟩,
  map_source' := λp hp, by simpa using hp,
  map_target' := λp hp, by simpa using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx,
    rw [C.coord_change_comp, C.coord_change_self],
    { exact hx.1 },
    { simp [hx] }
  end,
  right_inv'  := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ] at hx,
    rw [C.coord_change_comp, C.coord_change_self],
    { exact hx.2 },
    { simp [hx] },
  end,
  open_source :=
    (is_open.inter (C.is_open_base_set i) (C.is_open_base_set j)).prod is_open_univ,
  open_target :=
    (is_open.inter (C.is_open_base_set i) (C.is_open_base_set j)).prod is_open_univ,
  continuous_to_fun  :=
    continuous_on.prod continuous_fst.continuous_on (C.continuous_on_coord_change i j),
  continuous_inv_fun := by simpa [inter_comm]
    using continuous_on.prod continuous_fst.continuous_on (C.continuous_on_coord_change j i) }

@[simp, mfld_simps] lemma mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (C.triv_change i j).source ↔ p.1 ∈ C.base_set i ∩ C.base_set j :=
by { erw [mem_prod], simp }

/-- Associate to a trivialization index `i : ι` the corresponding trivialization, i.e., a bijection
between `proj ⁻¹ (base_set i)` and `base_set i × F`. As the fiber above `x` is `F` but read in the
chart with index `index_at x`, the trivialization in the fiber above x is by definition the
coordinate change from i to `index_at x`, so it depends on `x`.
The local trivialization will ultimately be a local homeomorphism. For now, we only introduce the
local equiv version, denoted with a prime. In further developments, avoid this auxiliary version,
and use `C.local_triv` instead.
-/
def local_triv_as_local_equiv (i : ι) : local_equiv C.total_space (B × F) :=
{ source      := C.proj ⁻¹' (C.base_set i),
  target      := C.base_set i ×ˢ univ,
  inv_fun     := λp, ⟨p.1, C.coord_change i (C.index_at p.1) p.1 p.2⟩,
  to_fun      := λp, ⟨p.1, C.coord_change (C.index_at p.1) i p.1 p.2⟩,
  map_source' := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.prod_mk_mem_set_prod_eq] using hp,
  map_target' := λp hp,
    by simpa only [set.mem_preimage, and_true, set.mem_univ, set.mem_prod] using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    change x ∈ C.base_set i at hx,
    dsimp only,
    rw [C.coord_change_comp, C.coord_change_self],
    { exact C.mem_base_set_at _ },
    { simp only [hx, mem_inter_iff, and_self, mem_base_set_at] }
  end,
  right_inv' := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, and_true, mem_univ] at hx,
    rw [C.coord_change_comp, C.coord_change_self],
    { exact hx },
    { simp only [hx, mem_inter_iff, and_self, mem_base_set_at] }
  end }

variable (i : ι)

lemma mem_local_triv_as_local_equiv_source (p : C.total_space) :
  p ∈ (C.local_triv_as_local_equiv i).source ↔ p.1 ∈ C.base_set i :=
iff.rfl

lemma mem_local_triv_as_local_equiv_target (p : B × F) :
  p ∈ (C.local_triv_as_local_equiv i).target ↔ p.1 ∈ C.base_set i :=
by { erw [mem_prod], simp only [and_true, mem_univ] }

lemma local_triv_as_local_equiv_apply (p : C.total_space) :
  (C.local_triv_as_local_equiv i) p = ⟨p.1, C.coord_change (C.index_at p.1) i p.1 p.2⟩ := rfl

/-- The composition of two local trivializations is the trivialization change C.triv_change i j. -/
lemma local_triv_as_local_equiv_trans (i j : ι) :
  (C.local_triv_as_local_equiv i).symm.trans
    (C.local_triv_as_local_equiv j) ≈ (C.triv_change i j).to_local_equiv :=
begin
  split,
  { ext x, simp only [mem_local_triv_as_local_equiv_target] with mfld_simps, refl, },
  { rintros ⟨x, v⟩ hx,
    simp only [triv_change, local_triv_as_local_equiv, local_equiv.symm, true_and, prod.mk.inj_iff,
      prod_mk_mem_set_prod_eq, local_equiv.trans_source, mem_inter_iff, and_true, mem_preimage,
      proj, mem_univ, local_equiv.coe_mk, eq_self_iff_true, local_equiv.coe_trans,
      total_space.proj] at hx ⊢,
    simp only [C.coord_change_comp, hx, mem_inter_iff, and_self, mem_base_set_at], }
end

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space (bundle.total_space C.fiber) :=
topological_space.generate_from $ ⋃ (i : ι) (s : set (B × F)) (s_open : is_open s),
  {(C.local_triv_as_local_equiv i).source ∩ (C.local_triv_as_local_equiv i) ⁻¹' s}

lemma open_source' (i : ι) : is_open (C.local_triv_as_local_equiv i).source :=
begin
  apply topological_space.generate_open.basic,
  simp only [exists_prop, mem_Union, mem_singleton_iff],
  refine ⟨i, C.base_set i ×ˢ univ, (C.is_open_base_set i).prod is_open_univ, _⟩,
  ext p,
  simp only [local_triv_as_local_equiv_apply, prod_mk_mem_set_prod_eq, mem_inter_iff, and_self,
    mem_local_triv_as_local_equiv_source, and_true, mem_univ, mem_preimage],
end

open fiber_bundle

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : trivialization F C.proj :=
{ base_set      := C.base_set i,
  open_base_set := C.is_open_base_set i,
  source_eq     := rfl,
  target_eq     := rfl,
  proj_to_fun   := λ p hp, by { simp only with mfld_simps, refl },
  open_source := C.open_source' i,
  open_target := (C.is_open_base_set i).prod is_open_univ,
  continuous_to_fun := begin
    rw continuous_on_open_iff (C.open_source' i),
    assume s s_open,
    apply topological_space.generate_open.basic,
    simp only [exists_prop, mem_Union, mem_singleton_iff],
    exact ⟨i, s, s_open, rfl⟩
  end,
  continuous_inv_fun := begin
    apply continuous_on_open_of_generate_from ((C.is_open_base_set i).prod is_open_univ),
    assume t ht,
    simp only [exists_prop, mem_Union, mem_singleton_iff] at ht,
    obtain ⟨j, s, s_open, ts⟩ : ∃ j s, is_open s ∧ t =
      (C.local_triv_as_local_equiv j).source ∩ (C.local_triv_as_local_equiv j) ⁻¹' s := ht,
    rw ts,
    simp only [local_equiv.right_inv, preimage_inter, local_equiv.left_inv],
    let e := C.local_triv_as_local_equiv i,
    let e' := C.local_triv_as_local_equiv j,
    let f := e.symm.trans e',
    have : is_open (f.source ∩ f ⁻¹' s),
    { rw [(C.local_triv_as_local_equiv_trans i j).source_inter_preimage_eq],
      exact (continuous_on_open_iff (C.triv_change i j).open_source).1
        ((C.triv_change i j).continuous_on) _ s_open },
    convert this using 1,
    dsimp [local_equiv.trans_source],
    rw [← preimage_comp, inter_assoc],
    refl,
  end,
  to_local_equiv := C.local_triv_as_local_equiv i }

/-- Preferred local trivialization of a fiber bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : trivialization F C.proj :=
C.local_triv (C.index_at b)

@[simp, mfld_simps] lemma local_triv_at_def (b : B) :
  C.local_triv (C.index_at b) = C.local_triv_at b := rfl

/-- If an element of `F` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is continuous. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
lemma continuous_const_section (v : F)
  (h : ∀ i j, ∀ x ∈ (C.base_set i) ∩ (C.base_set j), C.coord_change i j x v = v) :
  continuous (show B → C.total_space, from λ x, ⟨x, v⟩) :=
begin
  apply continuous_iff_continuous_at.2 (λ x, _),
  have A : C.base_set (C.index_at x) ∈ 𝓝 x :=
    is_open.mem_nhds (C.is_open_base_set (C.index_at x)) (C.mem_base_set_at x),
  apply ((C.local_triv_at x).to_local_homeomorph.continuous_at_iff_continuous_at_comp_left _).2,
  { simp only [(∘)] with mfld_simps,
    apply continuous_at_id.prod,
    have : continuous_on (λ (y : B), v) (C.base_set (C.index_at x)) := continuous_on_const,
    apply (this.congr _).continuous_at A,
    assume y hy,
    simp only [h, hy, mem_base_set_at] with mfld_simps },
  { exact A }
end

@[simp, mfld_simps] lemma local_triv_as_local_equiv_coe :
  ⇑(C.local_triv_as_local_equiv i) = C.local_triv i := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_source :
  (C.local_triv_as_local_equiv i).source = (C.local_triv i).source := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_target :
  (C.local_triv_as_local_equiv i).target = (C.local_triv i).target := rfl

@[simp, mfld_simps] lemma local_triv_as_local_equiv_symm :
  (C.local_triv_as_local_equiv i).symm = (C.local_triv i).to_local_equiv.symm := rfl

@[simp, mfld_simps] lemma base_set_at : C.base_set i = (C.local_triv i).base_set := rfl

@[simp, mfld_simps] lemma local_triv_apply (p : C.total_space) :
  (C.local_triv i) p = ⟨p.1, C.coord_change (C.index_at p.1) i p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma local_triv_at_apply (p : C.total_space) :
  ((C.local_triv_at p.1) p) = ⟨p.1, p.2⟩ :=
by { rw [local_triv_at, local_triv_apply, coord_change_self], exact C.mem_base_set_at p.1 }

@[simp, mfld_simps] lemma local_triv_at_apply_mk (b : B) (a : F) :
  ((C.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
C.local_triv_at_apply _

@[simp, mfld_simps] lemma mem_local_triv_source (p : C.total_space) :
  p ∈ (C.local_triv i).source ↔ p.1 ∈ (C.local_triv i).base_set := iff.rfl

@[simp, mfld_simps] lemma mem_local_triv_at_source (p : C.total_space) (b : B) :
  p ∈ (C.local_triv_at b).source ↔ p.1 ∈ (C.local_triv_at b).base_set := iff.rfl

@[simp, mfld_simps] lemma mem_local_triv_target (p : B × F) :
  p ∈ (C.local_triv i).target ↔ p.1 ∈ (C.local_triv i).base_set :=
trivialization.mem_target _

@[simp, mfld_simps] lemma mem_local_triv_at_target (p : B × F) (b : B) :
  p ∈ (C.local_triv_at b).target ↔ p.1 ∈ (C.local_triv_at b).base_set :=
trivialization.mem_target _

@[simp, mfld_simps] lemma local_triv_symm_apply (p : B × F) :
  (C.local_triv i).to_local_homeomorph.symm p =
    ⟨p.1, C.coord_change i (C.index_at p.1) p.1 p.2⟩ := rfl

@[simp, mfld_simps] lemma mem_local_triv_at_base_set (b : B) :
  b ∈ (C.local_triv_at b).base_set :=
by { rw [local_triv_at, ←base_set_at], exact C.mem_base_set_at b, }

/-- The inclusion of a fiber into the total space is a continuous map. -/
@[continuity]
lemma continuous_total_space_mk (b : B) :
  continuous (total_space_mk b : C.fiber b → bundle.total_space C.fiber) :=
begin
  rw [continuous_iff_le_induced, fiber_bundle_core.to_topological_space],
  apply le_induced_generate_from,
  simp only [total_space_mk, mem_Union, mem_singleton_iff, local_triv_as_local_equiv_source,
    local_triv_as_local_equiv_coe],
  rintros s ⟨i, t, ht, rfl⟩,
  rw [←((C.local_triv i).source_inter_preimage_target_inter t), preimage_inter, ←preimage_comp,
    trivialization.source_eq],
  apply is_open.inter,
  { simp only [total_space.proj, proj, ←preimage_comp],
    by_cases (b ∈ (C.local_triv i).base_set),
    { rw preimage_const_of_mem h, exact is_open_univ, },
    { rw preimage_const_of_not_mem h, exact is_open_empty, }},
  { simp only [function.comp, local_triv_apply],
    rw [preimage_inter, preimage_comp],
    by_cases (b ∈ C.base_set i),
    { have hc : continuous (λ (x : C.fiber b), (C.coord_change (C.index_at b) i b) x),
        from (C.continuous_on_coord_change (C.index_at b) i).comp_continuous
          (continuous_const.prod_mk continuous_id) (λ x, ⟨⟨C.mem_base_set_at b, h⟩, mem_univ x⟩),
      exact (((C.local_triv i).open_target.inter ht).preimage (continuous.prod.mk b)).preimage hc },
    { rw [(C.local_triv i).target_eq, ←base_set_at, mk_preimage_prod_right_eq_empty h,
        preimage_empty, empty_inter],
      exact is_open_empty, }}
end

/-- A topological fiber bundle constructed from core is indeed a topological fiber bundle. -/
instance fiber_bundle : fiber_bundle F C.fiber :=
{ total_space_mk_inducing := λ b, ⟨ begin refine le_antisymm _ (λ s h, _),
    { rw ←continuous_iff_le_induced,
      exact continuous_total_space_mk C b, },
    { refine is_open_induced_iff.mpr ⟨(C.local_triv_at b).source ∩ (C.local_triv_at b) ⁻¹'
        ((C.local_triv_at b).base_set ×ˢ s), (continuous_on_open_iff
        (C.local_triv_at b).open_source).mp (C.local_triv_at b).continuous_to_fun _
        ((C.local_triv_at b).open_base_set.prod h), _⟩,
      rw [preimage_inter, ←preimage_comp, function.comp],
      simp only [total_space_mk],
      refine ext_iff.mpr (λ a, ⟨λ ha, _, λ ha, ⟨C.mem_base_set_at b, _⟩⟩),
      { simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk] at ha,
        exact ha.2.2, },
      { simp only [mem_prod, mem_preimage, mem_inter_iff, local_triv_at_apply_mk],
        exact ⟨C.mem_base_set_at b, ha⟩, } } end⟩,
  trivialization_atlas := range C.local_triv,
  trivialization_at := λ x, C.local_triv (C.index_at x),
  mem_base_set_trivialization_at := C.mem_base_set_at,
  trivialization_mem_atlas := λ x, mem_range_self _ }

/-- The projection on the base of a topological bundle created from core is continuous -/
lemma continuous_proj : continuous C.proj :=
by { haveI := C.fiber_bundle, exact continuous_proj F C.fiber }

/-- The projection on the base of a topological bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map C.proj :=
by { haveI := C.fiber_bundle, exact is_open_map_proj F C.fiber }

end fiber_bundle_core

end general

namespace bundle
instance [I : topological_space F] : ∀ x : B, topological_space (trivial B F x) := λ x, I

instance [t₁ : topological_space B] [t₂ : topological_space F] :
  topological_space (total_space (trivial B F)) :=
induced total_space.proj t₁ ⊓ induced (trivial.proj_snd B F) t₂

/-! ### The trivial fiber bundle -/
namespace trivial

variables (B F) [topological_space B] [topological_space F]

/-- Local trivialization for trivial bundle. -/
def trivialization : trivialization F (π (bundle.trivial B F)) :=
{ to_fun := λ x, (x.fst, x.snd),
  inv_fun := λ y, ⟨y.fst, y.snd⟩,
  source := univ,
  target := univ,
  map_source' := λ x h, mem_univ (x.fst, x.snd),
  map_target' := λ y h,  mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_rfl, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_rfl, },
  base_set := univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [univ_prod_univ],
  proj_to_fun := λ y hy, rfl }

@[simp]
lemma trivialization_source : (trivialization B F).source = univ := rfl

@[simp]
lemma trivialization_target : (trivialization B F).target = univ := rfl

instance : fiber_bundle F (bundle.trivial B F) :=
{ trivialization_atlas := {trivialization B F},
  trivialization_at := λ x, trivialization B F,
  mem_base_set_trivialization_at := mem_univ,
  trivialization_mem_atlas := λ x, mem_singleton _,
  total_space_mk_inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp,
      total_space.proj, induced_const, top_inf_eq, trivial.proj_snd, id.def,
      trivial.topological_space, this, induced_id],
  end⟩ }

-- instance : mem_trivialization_atlas (trivialization B F) := ⟨mem_singleton _⟩
variables {B F}
lemma eq_trivialization (e : _root_.trivialization F (π (bundle.trivial B F)))
  [he : mem_trivialization_atlas e] : e = trivialization B F :=
mem_singleton_iff.mp he.1

end trivial

end bundle

/-! ### The fibrewise product of two fibre bundles -/

open trivialization
namespace bundle

variables (E₁ : B → Type*) (E₂ : B → Type*)
variables [topological_space (total_space E₁)] [topological_space (total_space E₂)]

/-- Equip the total space of the fibrewise product of two topological fiber bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `total_space E₁ × total_space E₂`. -/
instance prod.topological_space :
  topological_space (total_space (E₁ ×ᵇ E₂)) :=
topological_space.induced
  (λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)))
  (by apply_instance : topological_space (total_space E₁ × total_space E₂))

/-- The diagonal map from the total space of the fibrewise product of two topological fiber bundles
`E₁`, `E₂` into `total_space E₁ × total_space E₂` is `inducing`. -/
lemma prod.inducing_diag : inducing
  (λ p, (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
    total_space (E₁ ×ᵇ E₂) → total_space E₁ × total_space E₂) :=
⟨rfl⟩

end bundle

open bundle

variables [topological_space B]

variables (F₁ : Type*) [topological_space F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]

variables (F₂ : Type*) [topological_space F₂]
  (E₂ : B → Type*) [topological_space (total_space E₂)]

namespace trivialization
variables (e₁ : trivialization F₁ (π E₁))
variables (e₂ : trivialization F₂ (π E₂))

include e₁ e₂
variables {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def prod.to_fun' : total_space (E₁ ×ᵇ E₂) → B × (F₁ × F₂) :=
λ p, ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩

variables {e₁ e₂}

lemma prod.continuous_to_fun : continuous_on (prod.to_fun' e₁ e₂)
  (π (E₁ ×ᵇ E₂) ⁻¹' (e₁.base_set ∩ e₂.base_set)) :=
begin
  let f₁ : total_space (E₁ ×ᵇ E₂) → total_space E₁ × total_space E₂ :=
    λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)),
  let f₂ : total_space E₁ × total_space E₂ → (B × F₁) × (B × F₂) := λ p, ⟨e₁ p.1, e₂ p.2⟩,
  let f₃ : (B × F₁) × (B × F₂) → B × F₁ × F₂ := λ p, ⟨p.1.1, p.1.2, p.2.2⟩,
  have hf₁ : continuous f₁ := (prod.inducing_diag E₁ E₂).continuous,
  have hf₂ : continuous_on f₂ (e₁.source ×ˢ e₂.source) :=
    e₁.to_local_homeomorph.continuous_on.prod_map e₂.to_local_homeomorph.continuous_on,
  have hf₃ : continuous f₃ :=
    (continuous_fst.comp continuous_fst).prod_mk (continuous_snd.prod_map continuous_snd),
  refine ((hf₃.comp_continuous_on hf₂).comp hf₁.continuous_on _).congr _,
  { rw [e₁.source_eq, e₂.source_eq],
    exact maps_to_preimage _ _ },
  rintros ⟨b, v₁, v₂⟩ ⟨hb₁, hb₂⟩,
  simp only [prod.to_fun', prod.mk.inj_iff, eq_self_iff_true, and_true],
  rw e₁.coe_fst,
  rw [e₁.source_eq, mem_preimage],
  exact hb₁,
end

variables (e₁ e₂) [∀ b, has_zero (E₁ b)] [∀ b, has_zero (E₂ b)]

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def prod.inv_fun' (p : B × (F₁ × F₂)) : total_space (E₁ ×ᵇ E₂) :=
⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩

variables {e₁ e₂}

lemma prod.left_inv {x : total_space (E₁ ×ᵇ E₂)}
  (h : x ∈ π (E₁ ×ᵇ E₂) ⁻¹' (e₁.base_set ∩ e₂.base_set)) :
  prod.inv_fun' e₁ e₂ (prod.to_fun' e₁ e₂ x) = x :=
begin
  obtain ⟨x, v₁, v₂⟩ := x,
  obtain ⟨h₁ : x ∈ e₁.base_set, h₂ : x ∈ e₂.base_set⟩ := h,
  simp only [prod.to_fun', prod.inv_fun', symm_apply_apply_mk, h₁, h₂]
end

lemma prod.right_inv {x : B × F₁ × F₂}
  (h : x ∈ (e₁.base_set ∩ e₂.base_set) ×ˢ (univ : set (F₁ × F₂))) :
  prod.to_fun' e₁ e₂ (prod.inv_fun' e₁ e₂ x) = x :=
begin
  obtain ⟨x, w₁, w₂⟩ := x,
  obtain ⟨⟨h₁ : x ∈ e₁.base_set, h₂ : x ∈ e₂.base_set⟩, -⟩ := h,
  simp only [prod.to_fun', prod.inv_fun', apply_mk_symm, h₁, h₂]
end

lemma prod.continuous_inv_fun :
  continuous_on (prod.inv_fun' e₁ e₂) ((e₁.base_set ∩ e₂.base_set) ×ˢ univ) :=
begin
  rw (prod.inducing_diag E₁ E₂).continuous_on_iff,
  have H₁ : continuous (λ p : B × F₁ × F₂, ((p.1, p.2.1), (p.1, p.2.2))) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd),
  refine (e₁.continuous_on_symm.prod_map e₂.continuous_on_symm).comp H₁.continuous_on _,
  exact λ x h, ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩
end

variables (e₁ e₂)
variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.

Either one of `[∀ b, has_zero (E₁ b)] [∀ b, has_zero (E₂ b)]` would suffice for this, as would either
one of `[fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]`.  We `nolint unused_arguments` to require both for
symmetry.
-/
-- @[nolint unused_arguments]
def prod : trivialization (F₁ × F₂) (π (E₁ ×ᵇ E₂)) :=
{ to_fun := prod.to_fun' e₁ e₂,
  inv_fun := prod.inv_fun' e₁ e₂,
  source := (π (E₁ ×ᵇ E₂)) ⁻¹' (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ set.univ,
  map_source' := λ x h, ⟨h, set.mem_univ _⟩,
  map_target' := λ x h, h.1,
  left_inv' := λ x, prod.left_inv,
  right_inv' := λ x, prod.right_inv,
  open_source := begin
    refine (e₁.open_base_set.inter e₂.open_base_set).preimage _,
    exact (continuous_proj F₁ E₁).comp (prod.inducing_diag E₁ E₂).continuous.fst,
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  continuous_to_fun := prod.continuous_to_fun,
  continuous_inv_fun := prod.continuous_inv_fun,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ x h, rfl }

@[simp] lemma base_set_prod : (prod e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

variables {e₁ e₂}

lemma prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) : (prod e₁ e₂).to_local_equiv.symm (x, w₁, w₂)
  = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ :=
rfl

end trivialization

open trivialization

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂] [Π b, has_zero (E₁ b)] [Π b, has_zero (E₂ b)]

/-- The product of two fiber bundles is a fiber bundle. -/
instance _root_.bundle.prod.fiber_bundle : fiber_bundle (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ total_space_mk_inducing := λ b,
  begin
    rw (prod.inducing_diag E₁ E₂).inducing_iff,
    exact (total_space_mk_inducing F₁ E₁ b).prod_mk (total_space_mk_inducing F₂ E₂ b),
  end,
  trivialization_atlas := (λ (p : trivialization F₁ (π E₁) × trivialization F₂ (π E₂)), p.1.prod p.2) ''
    (trivialization_atlas F₁ E₁ ×ˢ trivialization_atlas F₂ E₂),
  trivialization_at := λ b, (trivialization_at F₁ E₁ b).prod (trivialization_at F₂ E₂ b),
  mem_base_set_trivialization_at :=
    λ b, ⟨mem_base_set_trivialization_at F₁ E₁ b, mem_base_set_trivialization_at F₂ E₂ b⟩,
  trivialization_mem_atlas := λ b,
    ⟨(_, _), ⟨trivialization_mem_atlas F₁ E₁ b, trivialization_mem_atlas F₂ E₂ b⟩, rfl⟩}
