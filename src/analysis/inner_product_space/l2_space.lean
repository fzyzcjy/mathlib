/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.projection
import analysis.normed_space.lp_space
import analysis.inner_product_space.pi_L2

/-!
# Hilbert sum of a family of inner product spaces

Given a family `(G : ι → Type*) [Π i, inner_product_space 𝕜 (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : Π i, G i` for which `∑' i, ∥f i∥ ^ 2`, the sum of the norms-squared, is
summable.  This construction is sometimes called the *Hilbert sum* of the family `G`.  By choosing
`G` to be `ι → 𝕜`, the Hilbert space `ℓ²(ι, 𝕜)` may be seen as a special case of this construction.

We also define a *predicate* `is_hilbert_sum 𝕜 E V`, where `V : Π i, G i →ₗᵢ[𝕜] E`, expressing that
`V` is an `orthogonal_family` and that the associated map `lp G 2 →ₗᵢ[𝕜] E` is surjective.

## Main definitions

* `orthogonal_family.linear_isometry`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with
  mutually-orthogonal images, there is an induced isometric embedding of the Hilbert sum of `G`
  into `E`.

* `is_hilbert_sum`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E`,
  `is_hilbert_sum 𝕜 E V` means that `V` is an `orthogonal_family` and that the above
  linear isometry is surjective.

* `is_hilbert_sum.linear_isometry_equiv`: If a Hilbert space `E` is a Hilbert sum of the
  inner product spaces `G i` with respect to the family `V : Π i, G i →ₗᵢ[𝕜] E`, then the
  corresponding `orthogonal_family.linear_isometry` can be upgraded to a `linear_isometry_equiv`.

* `hilbert_basis`: We define a *Hilbert basis* of a Hilbert space `E` to be a structure whose single
  field `hilbert_basis.repr` is an isometric isomorphism of `E` with `ℓ²(ι, 𝕜)` (i.e., the Hilbert
  sum of `ι` copies of `𝕜`).  This parallels the definition of `basis`, in `linear_algebra.basis`,
  as an isomorphism of an `R`-module with `ι →₀ R`.

* `hilbert_basis.has_coe_to_fun`: More conventionally a Hilbert basis is thought of as a family
  `ι → E` of vectors in `E` satisfying certain properties (orthonormality, completeness).  We obtain
  this interpretation of a Hilbert basis `b` by defining `⇑b`, of type `ι → E`, to be the image
  under `b.repr` of `lp.single 2 i (1:𝕜)`.  This parallels the definition `basis.has_coe_to_fun` in
  `linear_algebra.basis`.

* `hilbert_basis.mk`: Make a Hilbert basis of `E` from an orthonormal family `v : ι → E` of vectors
  in `E` whose span is dense.  This parallels the definition `basis.mk` in `linear_algebra.basis`.

* `hilbert_basis.mk_of_orthogonal_eq_bot`: Make a Hilbert basis of `E` from an orthonormal family
  `v : ι → E` of vectors in `E` whose span has trivial orthogonal complement.

## Main results

* `lp.inner_product_space`: Construction of the inner product space instance on the Hilbert sum
  `lp G 2`.  Note that from the file `analysis.normed_space.lp_space`, the space `lp G 2` already
  held a normed space instance (`lp.normed_space`), and if each `G i` is a Hilbert space (i.e.,
  complete), then `lp G 2` was already known to be complete (`lp.complete_space`).  So the work
  here is to define the inner product and show it is compatible.

* `orthogonal_family.range_linear_isometry`: Given a family `G` of inner product spaces and a family
  `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with mutually-orthogonal
  images, the image of the embedding `orthogonal_family.linear_isometry` of the Hilbert sum of `G`
  into `E` is the closure of the span of the images of the `G i`.

* `hilbert_basis.repr_apply_apply`: Given a Hilbert basis `b` of `E`, the entry `b.repr x i` of
  `x`'s representation in `ℓ²(ι, 𝕜)` is the inner product `⟪b i, x⟫`.

* `hilbert_basis.has_sum_repr`: Given a Hilbert basis `b` of `E`, a vector `x` in `E` can be
  expressed as the "infinite linear combination" `∑' i, b.repr x i • b i` of the basis vectors
  `b i`, with coefficients given by the entries `b.repr x i` of `x`'s representation in `ℓ²(ι, 𝕜)`.

* `exists_hilbert_basis`: A Hilbert space admits a Hilbert basis.

## Keywords

Hilbert space, Hilbert sum, l2, Hilbert basis, unitary equivalence, isometric isomorphism
-/

open is_R_or_C submodule filter
open_locale big_operators nnreal ennreal classical complex_conjugate topological_space

noncomputable theory

variables {ι : Type*}
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E] [cplt : complete_space E]
variables {G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

notation `ℓ²(`ι`, `𝕜`)` := lp (λ i : ι, 𝕜) 2

/-! ### Inner product space structure on `lp G 2` -/

namespace lp

lemma summable_inner (f g : lp G 2) : summable (λ i, ⟪f i, g i⟫) :=
begin
  -- Apply the Direct Comparison Test, comparing with ∑' i, ∥f i∥ * ∥g i∥ (summable by Hölder)
  refine summable_of_norm_bounded (λ i, ∥f i∥ * ∥g i∥) (lp.summable_mul _ f g) _,
  { rw real.is_conjugate_exponent_iff; norm_num },
  intros i,
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm _ _,
end

instance : inner_product_space 𝕜 (lp G 2) :=
{ inner := λ f g, ∑' i, ⟪f i, g i⟫,
  norm_sq_eq_inner := λ f, begin
    calc ∥f∥ ^ 2 = ∥f∥ ^ (2:ℝ≥0∞).to_real : by norm_cast
    ... = ∑' i, ∥f i∥ ^ (2:ℝ≥0∞).to_real : lp.norm_rpow_eq_tsum _ f
    ... = ∑' i, ∥f i∥ ^ 2 : by norm_cast
    ... = ∑' i, re ⟪f i, f i⟫ : by simp only [norm_sq_eq_inner]
    ... = re (∑' i, ⟪f i, f i⟫) : (is_R_or_C.re_clm.map_tsum _).symm
    ... = _ : by congr,
    { norm_num },
    { exact summable_inner f f },
  end,
  conj_sym := λ f g, begin
    calc conj _ = conj ∑' i, ⟪g i, f i⟫ : by congr
    ... = ∑' i, conj ⟪g i, f i⟫ : is_R_or_C.conj_cle.map_tsum
    ... = ∑' i, ⟪f i, g i⟫ : by simp only [inner_conj_sym]
    ... = _ : by congr,
  end,
  add_left := λ f₁ f₂ g, begin
    calc _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ : _
    ... = ∑' i, (⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫) :
          by simp only [inner_add_left, pi.add_apply, coe_fn_add]
    ... = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ : tsum_add _ _
    ... = _ : by congr,
    { congr, },
    { exact summable_inner f₁ g },
    { exact summable_inner f₂ g }
  end,
  smul_left := λ f g c, begin
    calc _ = ∑' i, ⟪c • f i, g i⟫ : _
    ... = ∑' i, conj c * ⟪f i, g i⟫ : by simp only [inner_smul_left]
    ... = conj c * ∑' i, ⟪f i, g i⟫ : tsum_mul_left
    ... = _ : _,
    { simp only [coe_fn_smul, pi.smul_apply] },
    { congr },
  end,
  .. lp.normed_space }

lemma inner_eq_tsum (f g : lp G 2) : ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫ := rfl

lemma has_sum_inner (f g : lp G 2) : has_sum (λ i, ⟪f i, g i⟫) ⟪f, g⟫ :=
(summable_inner f g).has_sum

lemma inner_single_left (i : ι) (a : G i) (f : lp G 2) : ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫ :=
begin
  refine (has_sum_inner (lp.single 2 i a) f).unique _,
  convert has_sum_ite_eq i ⟪a, f i⟫,
  ext j,
  rw lp.single_apply,
  split_ifs,
  { subst h },
  { simp }
end

lemma inner_single_right (i : ι) (a : G i) (f : lp G 2) : ⟪f, lp.single 2 i a⟫ = ⟪f i, a⟫ :=
by simpa [inner_conj_sym] using congr_arg conj (inner_single_left i a f)

end lp

/-! ### Identification of a general Hilbert space `E` with a Hilbert sum -/

namespace orthogonal_family
variables {V : Π i, G i →ₗᵢ[𝕜] E} (hV : orthogonal_family 𝕜 V)

include cplt hV

protected lemma summable_of_lp (f : lp G 2) : summable (λ i, V i (f i)) :=
begin
  rw hV.summable_iff_norm_sq_summable,
  convert (lp.mem_ℓp f).summable _,
  { norm_cast },
  { norm_num }
end

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry from `lp 2` of the
subspaces into `E`. -/
protected def linear_isometry : lp G 2 →ₗᵢ[𝕜] E :=
{ to_fun := λ f, ∑' i, V i (f i),
  map_add' := λ f g, by simp only [tsum_add (hV.summable_of_lp f) (hV.summable_of_lp g),
    lp.coe_fn_add, pi.add_apply, linear_isometry.map_add],
  map_smul' := λ c f, by simpa only [linear_isometry.map_smul, pi.smul_apply, lp.coe_fn_smul]
    using tsum_const_smul (hV.summable_of_lp f),
  norm_map' := λ f, begin
    classical, -- needed for lattice instance on `finset ι`, for `filter.at_top_ne_bot`
    have H : 0 < (2:ℝ≥0∞).to_real := by norm_num,
    suffices : ∥∑' (i : ι), V i (f i)∥ ^ ((2:ℝ≥0∞).to_real) = ∥f∥ ^ ((2:ℝ≥0∞).to_real),
    { exact real.rpow_left_inj_on H.ne' (norm_nonneg _) (norm_nonneg _) this },
    refine tendsto_nhds_unique  _ (lp.has_sum_norm H f),
    convert (hV.summable_of_lp f).has_sum.norm.rpow_const (or.inr H.le),
    ext s,
    exact_mod_cast (hV.norm_sum f s).symm,
  end }

protected lemma linear_isometry_apply (f : lp G 2) :
  hV.linear_isometry f = ∑' i, V i (f i) :=
rfl

protected lemma has_sum_linear_isometry (f : lp G 2) :
  has_sum (λ i, V i (f i)) (hV.linear_isometry f) :=
(hV.summable_of_lp f).has_sum

@[simp] protected lemma linear_isometry_apply_single {i : ι} (x : G i) :
  hV.linear_isometry (lp.single 2 i x) = V i x :=
begin
  rw [hV.linear_isometry_apply, ← tsum_ite_eq i (V i x)],
  congr,
  ext j,
  rw [lp.single_apply],
  split_ifs,
  { subst h },
  { simp }
end

@[simp] protected lemma linear_isometry_apply_dfinsupp_sum_single (W₀ : Π₀ (i : ι), G i) :
  hV.linear_isometry (W₀.sum (lp.single 2)) = W₀.sum (λ i, V i) :=
begin
  have : hV.linear_isometry (∑ i in W₀.support, lp.single 2 i (W₀ i))
    = ∑ i in W₀.support, hV.linear_isometry (lp.single 2 i (W₀ i)),
  { exact hV.linear_isometry.to_linear_map.map_sum },
  simp [dfinsupp.sum, this] {contextual := tt},
end

/-- The canonical linear isometry from the `lp 2` of a mutually orthogonal family of subspaces of
`E` into E, has range the closure of the span of the subspaces. -/
protected lemma range_linear_isometry [Π i, complete_space (G i)] :
  hV.linear_isometry.to_linear_map.range = (⨆ i, (V i).to_linear_map.range).topological_closure :=
begin
  refine le_antisymm _ _,
  { rintros x ⟨f, rfl⟩,
    refine mem_closure_of_tendsto (hV.has_sum_linear_isometry f) (eventually_of_forall _),
    intros s,
    rw set_like.mem_coe,
    refine sum_mem _,
    intros i hi,
    refine mem_supr_of_mem i _,
    exact linear_map.mem_range_self _ (f i) },
  { apply topological_closure_minimal,
    { refine supr_le _,
      rintros i x ⟨x, rfl⟩,
      use lp.single 2 i x,
      exact hV.linear_isometry_apply_single x },
    exact hV.linear_isometry.isometry.uniform_inducing.is_complete_range.is_closed }
end

end orthogonal_family

section is_hilbert_sum

variables (𝕜 E) (V : Π i, G i →ₗᵢ[𝕜] E) (F : ι → submodule 𝕜 E)
include cplt

/-- Given a family of Hilbert spaces `G : ι → Type*`, a Hilbert sum of `G` consists of a Hilbert
space `E` and an orthogonal family `V : Π i, G i →ₗᵢ[𝕜] E` such that the induced isometry
`Φ : lp G 2 → E` is surjective.

Keeping in mind that `lp G 2` is "the" external Hilbert sum of `G : ι → Type*`, this is analogous
to `direct_sum.is_internal`, except that we don't express it in terms of actual submodules. -/
@[protect_proj] structure is_hilbert_sum : Prop := of_surjective ::
(orthogonal_family : orthogonal_family 𝕜 V)
(surjective_isometry : function.surjective (orthogonal_family.linear_isometry))

variables {𝕜 E V}

/-- If `V : Π i, G i →ₗᵢ[𝕜] E` is an orthogonal family such that the supremum of the ranges of
`V i` is dense, then `(E, V)` is a Hilbert sum of `G`. -/
lemma is_hilbert_sum.mk [Π i, complete_space $ G i]
  (hVortho : orthogonal_family 𝕜 V)
  (hVtotal : ⊤ ≤ (⨆ i, (V i).to_linear_map.range).topological_closure) :
  is_hilbert_sum 𝕜 E V :=
{ orthogonal_family := hVortho,
  surjective_isometry :=
  begin
    rw [←linear_isometry.coe_to_linear_map],
    exact linear_map.range_eq_top.mp (eq_top_iff.mpr $
      hVtotal.trans_eq hVortho.range_linear_isometry.symm)
  end }

/-- This is `orthogonal_family.is_hilbert_sum` in the case of actual inclusions from subspaces. -/
lemma is_hilbert_sum.mk_internal [Π i, complete_space $ F i]
  (hFortho : @orthogonal_family 𝕜 E _ _ _ (λ i, F i) _ (λ i, (F i).subtypeₗᵢ))
  (hFtotal : ⊤ ≤ (⨆ i, (F i)).topological_closure) :
  @is_hilbert_sum _ 𝕜 _ E _ _ (λ i, F i) _ (λ i, (F i).subtypeₗᵢ) :=
is_hilbert_sum.mk hFortho (by simpa [subtypeₗᵢ_to_linear_map, range_subtype] using hFtotal)

/-- *A* Hilbert sum `(E, V)` of `G` is canonically isomorphic to *the* Hilbert sum of `G`,
i.e `lp G 2`.

Note that this goes in the opposite direction from `orthogonal_family.linear_isometry`. -/
noncomputable def is_hilbert_sum.linear_isometry_equiv (hV : is_hilbert_sum 𝕜 E V) :
  E ≃ₗᵢ[𝕜] lp G 2 :=
linear_isometry_equiv.symm $
linear_isometry_equiv.of_surjective
hV.orthogonal_family.linear_isometry hV.surjective_isometry

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`. -/
protected lemma is_hilbert_sum.linear_isometry_equiv_symm_apply
  (hV : is_hilbert_sum 𝕜 E V) (w : lp G 2) :
  hV.linear_isometry_equiv.symm w = ∑' i, V i (w i) :=
by simp [is_hilbert_sum.linear_isometry_equiv, orthogonal_family.linear_isometry_apply]

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G` and `lp G 2`,
a vector `w : lp G 2` is the image of the infinite sum of the associated elements in `E`, and this
sum indeed converges. -/
protected lemma is_hilbert_sum.has_sum_linear_isometry_equiv_symm
  (hV : is_hilbert_sum 𝕜 E V) (w : lp G 2) :
  has_sum (λ i, V i (w i)) (hV.linear_isometry_equiv.symm w) :=
by simp [is_hilbert_sum.linear_isometry_equiv, orthogonal_family.has_sum_linear_isometry]

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, an "elementary basis vector" in `lp G 2` supported at `i : ι` is the image of the
associated element in `E`. -/
@[simp] protected lemma is_hilbert_sum.linear_isometry_equiv_symm_apply_single
  (hV : is_hilbert_sum 𝕜 E V) {i : ι} (x : G i) :
  hV.linear_isometry_equiv.symm (lp.single 2 i x) = V i x :=
by simp [is_hilbert_sum.linear_isometry_equiv, orthogonal_family.linear_isometry_apply_single]

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
@[simp] protected lemma is_hilbert_sum.linear_isometry_equiv_symm_apply_dfinsupp_sum_single
  (hV : is_hilbert_sum 𝕜 E V) (W₀ : Π₀ (i : ι), G i) :
  hV.linear_isometry_equiv.symm (W₀.sum (lp.single 2)) = (W₀.sum (λ i, V i)) :=
by simp [is_hilbert_sum.linear_isometry_equiv,
  orthogonal_family.linear_isometry_apply_dfinsupp_sum_single]

/-- In the canonical isometric isomorphism between a Hilbert sum `E` of `G : ι → Type*` and
`lp G 2`, a finitely-supported vector in `lp G 2` is the image of the associated finite sum of
elements of `E`. -/
@[simp] protected lemma is_hilbert_sum.linear_isometry_equiv_apply_dfinsupp_sum_single
  (hV : is_hilbert_sum 𝕜 E V) (W₀ : Π₀ (i : ι), G i) :
  (hV.linear_isometry_equiv (W₀.sum (λ i, V i)) : Π i, G i) = W₀ :=
begin
  rw ← hV.linear_isometry_equiv_symm_apply_dfinsupp_sum_single,
  rw linear_isometry_equiv.apply_symm_apply,
  ext i,
  simp [dfinsupp.sum, lp.single_apply] {contextual := tt},
end

/-- Given a total orthonormal family `v : ι → E`, `E` is a Hilbert sum of `λ i : ι, 𝕜` relative to
the family of linear isometries `λ i, λ k, k • v i`. -/
lemma orthonormal.is_hilbert_sum {v : ι → E} (hv : orthonormal 𝕜 v)
  (hsp : ⊤ ≤ (span 𝕜 (set.range v)).topological_closure) :
  @is_hilbert_sum _ 𝕜 _ _ _ _ (λ i : ι, 𝕜) _
    (λ i, linear_isometry.to_span_singleton 𝕜 E (hv.1 i)) :=
is_hilbert_sum.mk hv.orthogonal_family
begin
  convert hsp,
  simp [← linear_map.span_singleton_eq_range, ← submodule.span_Union],
end

lemma submodule.is_hilbert_sum_orthogonal (K : submodule 𝕜 E) [hK : complete_space K] :
  @is_hilbert_sum _ 𝕜 _ E _ _ (λ b, ((cond b K Kᗮ : submodule 𝕜 E) : Type*)) _
  (λ b, (cond b K Kᗮ).subtypeₗᵢ) :=
begin
  haveI : Π b, complete_space ((cond b K Kᗮ : submodule 𝕜 E) : Type*),
  { intro b,
    cases b;
    exact orthogonal.complete_space K <|> assumption },
  refine is_hilbert_sum.mk_internal _ K.orthogonal_family_self _,
  refine le_trans _ (submodule.submodule_topological_closure _),
  rw [supr_bool_eq, cond, cond],
  refine codisjoint.top_le _,
  exact submodule.is_compl_orthogonal_of_complete_space.codisjoint
end

end is_hilbert_sum

/-! ### Hilbert bases -/

section
variables (ι) (𝕜) (E)

/-- A Hilbert basis on `ι` for an inner product space `E` is an identification of `E` with the `lp`
space `ℓ²(ι, 𝕜)`. -/
structure hilbert_basis := of_repr :: (repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜))

end

namespace hilbert_basis

instance {ι : Type*} : inhabited (hilbert_basis ι 𝕜 ℓ²(ι, 𝕜)) :=
⟨of_repr (linear_isometry_equiv.refl 𝕜 _)⟩

/-- `b i` is the `i`th basis vector. -/
instance : has_coe_to_fun (hilbert_basis ι 𝕜 E) (λ _, ι → E) :=
{ coe := λ b i, b.repr.symm (lp.single 2 i (1:𝕜)) }

@[simp] protected lemma repr_symm_single (b : hilbert_basis ι 𝕜 E) (i : ι) :
  b.repr.symm (lp.single 2 i (1:𝕜)) = b i :=
rfl

@[simp] protected lemma repr_self (b : hilbert_basis ι 𝕜 E) (i : ι) :
  b.repr (b i) = lp.single 2 i (1:𝕜) :=
by rw [← b.repr_symm_single, linear_isometry_equiv.apply_symm_apply]

protected lemma repr_apply_apply (b : hilbert_basis ι 𝕜 E) (v : E) (i : ι) :
  b.repr v i = ⟪b i, v⟫ :=
begin
  rw [← b.repr.inner_map_map (b i) v, b.repr_self, lp.inner_single_left],
  simp,
end

@[simp] protected lemma orthonormal (b : hilbert_basis ι 𝕜 E) : orthonormal 𝕜 b :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self, b.repr_self, lp.inner_single_left,
    lp.single_apply],
  simp,
end

protected lemma has_sum_repr_symm (b : hilbert_basis ι 𝕜 E) (f : ℓ²(ι, 𝕜)) :
  has_sum (λ i, f i • b i) (b.repr.symm f) :=
begin
  suffices H : (λ (i : ι), f i • b i) =
    (λ (b_1 : ι), (b.repr.symm.to_continuous_linear_equiv) ((λ (i : ι), lp.single 2 i (f i)) b_1)),
  { rw H,
    have : has_sum (λ (i : ι), lp.single 2 i (f i)) f := lp.has_sum_single ennreal.two_ne_top f,
    exact (↑(b.repr.symm.to_continuous_linear_equiv) : ℓ²(ι, 𝕜) →L[𝕜] E).has_sum this },
  ext i,
  apply b.repr.injective,
  have : lp.single 2 i (f i * 1) = f i • lp.single 2 i 1 := lp.single_smul 2 i (1:𝕜) (f i),
  rw mul_one at this,
  rw [linear_isometry_equiv.map_smul, b.repr_self, ← this,
    linear_isometry_equiv.coe_to_continuous_linear_equiv],
  exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm,
end

protected lemma has_sum_repr (b : hilbert_basis ι 𝕜 E) (x : E) :
  has_sum (λ i, b.repr x i • b i) x :=
by simpa using b.has_sum_repr_symm (b.repr x)

@[simp] protected lemma dense_span (b : hilbert_basis ι 𝕜 E) :
  (span 𝕜 (set.range b)).topological_closure = ⊤ :=
begin
  classical,
  rw eq_top_iff,
  rintros x -,
  refine mem_closure_of_tendsto (b.has_sum_repr x) (eventually_of_forall _),
  intros s,
  simp only [set_like.mem_coe],
  refine sum_mem _,
  rintros i -,
  refine smul_mem _ _ _,
  exact subset_span ⟨i, rfl⟩
end

protected lemma has_sum_inner_mul_inner (b : hilbert_basis ι 𝕜 E) (x y : E) :
  has_sum (λ i, ⟪x, b i⟫ * ⟪b i, y⟫) ⟪x, y⟫ :=
begin
  convert (b.has_sum_repr y).mapL (innerSL x),
  ext i,
  rw [innerSL_apply, b.repr_apply_apply, inner_smul_right, mul_comm]
end

protected lemma summable_inner_mul_inner (b : hilbert_basis ι 𝕜 E) (x y : E) :
  summable (λ i, ⟪x, b i⟫ * ⟪b i, y⟫) :=
(b.has_sum_inner_mul_inner x y).summable

protected lemma tsum_inner_mul_inner (b : hilbert_basis ι 𝕜 E) (x y : E) :
  ∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ :=
(b.has_sum_inner_mul_inner x y).tsum_eq

-- Note : this should be `b.repr` composed with an identification of `lp (λ i : ι, 𝕜) p` with
-- `pi_Lp p (λ i : ι, 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/-- A finite Hilbert basis is an orthonormal basis. -/
protected def to_orthonormal_basis [fintype ι] (b : hilbert_basis ι 𝕜 E) :
  orthonormal_basis ι 𝕜 E :=
orthonormal_basis.mk b.orthonormal
begin
  refine eq.ge _,
  have := (span 𝕜 (finset.univ.image b : set E)).closed_of_finite_dimensional,
  simpa only [finset.coe_image, finset.coe_univ, set.image_univ, hilbert_basis.dense_span] using
    this.submodule_topological_closure_eq.symm
end

@[simp] lemma coe_to_orthonormal_basis [fintype ι] (b : hilbert_basis ι 𝕜 E) :
  (b.to_orthonormal_basis : ι → E) = b :=
orthonormal_basis.coe_mk _ _

protected lemma has_sum_orthogonal_projection {U : submodule 𝕜 E}
  [complete_space U] (b : hilbert_basis ι 𝕜 U) (x : E) :
  has_sum (λ i, ⟪(b i : E), x⟫ • b i) (orthogonal_projection U x) :=
by simpa only [b.repr_apply_apply, inner_orthogonal_projection_eq_of_mem_left]
  using b.has_sum_repr (orthogonal_projection U x)

lemma finite_spans_dense (b : hilbert_basis ι 𝕜 E) :
  (⨆ J : finset ι, span 𝕜 (J.image b : set E)).topological_closure = ⊤ :=
eq_top_iff.mpr $ b.dense_span.ge.trans
begin
  simp_rw [← submodule.span_Union],
  exact topological_closure_mono (span_mono $ set.range_subset_iff.mpr $
    λ i, set.mem_Union_of_mem {i} $ finset.mem_coe.mpr $ finset.mem_image_of_mem _ $
    finset.mem_singleton_self i)
end

variables {v : ι → E} (hv : orthonormal 𝕜 v)
include hv cplt

/-- An orthonormal family of vectors whose span is dense in the whole module is a Hilbert basis. -/
protected def mk (hsp : ⊤ ≤ (span 𝕜 (set.range v)).topological_closure) :
  hilbert_basis ι 𝕜 E :=
hilbert_basis.of_repr $
(hv.is_hilbert_sum hsp).linear_isometry_equiv

lemma _root_.orthonormal.linear_isometry_equiv_symm_apply_single_one (h i) :
  (hv.is_hilbert_sum h).linear_isometry_equiv.symm (lp.single 2 i 1) = v i :=
by rw [is_hilbert_sum.linear_isometry_equiv_symm_apply_single,
  linear_isometry.to_span_singleton_apply, one_smul]

@[simp] protected lemma coe_mk (hsp : ⊤ ≤ (span 𝕜 (set.range v)).topological_closure) :
  ⇑(hilbert_basis.mk hv hsp) = v :=
by apply (funext $ orthonormal.linear_isometry_equiv_symm_apply_single_one hv hsp)

/-- An orthonormal family of vectors whose span has trivial orthogonal complement is a Hilbert
basis. -/
protected def mk_of_orthogonal_eq_bot (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) : hilbert_basis ι 𝕜 E :=
hilbert_basis.mk hv
(by rw [← orthogonal_orthogonal_eq_closure, ← eq_top_iff, orthogonal_eq_top_iff, hsp])

@[simp] protected lemma coe_of_orthogonal_eq_bot_mk (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) :
  ⇑(hilbert_basis.mk_of_orthogonal_eq_bot hv hsp) = v :=
hilbert_basis.coe_mk hv _

omit hv

-- Note : this should be `b.repr` composed with an identification of `lp (λ i : ι, 𝕜) p` with
-- `pi_Lp p (λ i : ι, 𝕜)` (in this case with `p = 2`), but we don't have this yet (July 2022).
/-- An orthonormal basis is an Hilbert basis. -/
protected def _root_.orthonormal_basis.to_hilbert_basis [fintype ι] (b : orthonormal_basis ι 𝕜 E) :
  hilbert_basis ι 𝕜 E :=
hilbert_basis.mk b.orthonormal $
by simpa only [← orthonormal_basis.coe_to_basis, b.to_basis.span_eq, eq_top_iff]
  using @subset_closure E _ _

@[simp] lemma _root_.orthonormal_basis.coe_to_hilbert_basis [fintype ι]
  (b : orthonormal_basis ι 𝕜 E) : (b.to_hilbert_basis : ι → E) = b :=
hilbert_basis.coe_mk _ _

/-- A Hilbert space admits a Hilbert basis extending a given orthonormal subset. -/
lemma _root_.orthonormal.exists_hilbert_basis_extension
  {s : set E} (hs : orthonormal 𝕜 (coe : s → E)) :
  ∃ (w : set E) (b : hilbert_basis w 𝕜 E), s ⊆ w ∧ ⇑b = (coe : w → E) :=
let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs in
⟨ w,
  hilbert_basis.mk_of_orthogonal_eq_bot hw_ortho
    (by simpa [maximal_orthonormal_iff_orthogonal_complement_eq_bot hw_ortho] using hw_max),
  hws,
  hilbert_basis.coe_of_orthogonal_eq_bot_mk _ _ ⟩

variables (𝕜 E)

/-- A Hilbert space admits a Hilbert basis. -/
lemma _root_.exists_hilbert_basis :
  ∃ (w : set E) (b : hilbert_basis w 𝕜 E), ⇑b = (coe : w → E) :=
let ⟨w, hw, hw', hw''⟩ := (orthonormal_empty 𝕜 E).exists_hilbert_basis_extension in ⟨w, hw, hw''⟩

end hilbert_basis
