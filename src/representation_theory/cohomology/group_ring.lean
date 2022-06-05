/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import representation_theory.Rep
import representation_theory.basic

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains API for the `k[G]`-module `k[Gⁿ]`, where `k` is a commutative ring, `G` is
a group, and we express the module structure as the representation `G →* End(k[Gⁿ])` induced by the
diagonal action of `G` on `Gⁿ.`

In particular, we define morphisms of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) which we will later show
define an isomorphism. From this we will deduce that `k[Gⁿ⁺¹]` is free over `k[G]`.
The freeness of these modules means we can use them to build a projective resolution of the
(trivial) `k[G]`-module `k`, which is useful in group cohomology.

## Main definitions

  * representation.of_mul_action
  * Rep.of_mul_action
  * to_tensor
  * of_tensor

## Implementation notes

We express `k[G]`-module structures on a group `V` as `k`-linear representations of `G` on `V`, as
this simplifies some proofs and also makes it easier to work with different structures on the same
`V`. This is because `module` is a class, and there is only one notation for scalar multiplication,
`•`; representations, meanwhile, give us more flexibility, by avoiding typeclass inference.

We bundle the type `k[Gⁿ]` - or more generally `k[H]` when `H` has `G`-action - and the
representation together as a term of type `Rep k G`, and we call it `Rep.of_mul_action k G H.` This
is so we can talk about morphisms of representations.

-/

noncomputable theory
universes v u
variables (k G : Type u) [comm_ring k]

open monoid_algebra

namespace representation
variables [monoid G] (H : Type u) [mul_action G H]

/-- A `G`-action on `H` induces a representation `G →* End(k[H])` in the natural way. -/
@[simps] def of_mul_action : representation k G (H →₀ k) :=
{ to_fun := λ g, finsupp.lmap_domain k k ((•) g),
  map_one' := by { ext x y, dsimp, simp },
  map_mul' := λ x y, by { ext z w, simp [mul_smul] }}

lemma ermmm (g : G) (h : H) : of_mul_action k G H g (finsupp.single h 1) = finsupp.single (g • h) 1 :=
begin
  show finsupp.map_domain _ _ = _,
  rw finsupp.map_domain_single,
end

end representation
namespace Rep
section
variables [monoid G] (H : Type u) [mul_action G H]

/-- Given a `G`-action on `H`, this is `k[H]` bundled with the natural representation
`G →* End(k[H])` as a term of type `Rep k G.` -/
abbreviation of_mul_action : Rep k G := Rep.of (representation.of_mul_action k G H)

variables {k G} {n : ℕ}

-- No idea what to call these or where to put them; would move them, but then they can't be private.
/-- Sends `(g₁, ..., gₙ) ↦ (1, g₁, g₁g₂, ..., g₁...gₙ)` -/
private def to_prod (f : fin n → G) (i : fin (n + 1)) : G :=
((list.of_fn f).take i).prod

@[simp] private lemma to_prod_zero (f : fin n → G) :
  to_prod f 0 = 1 :=
by simp [to_prod]

private lemma to_prod_succ (f : fin n → G) (j : fin n) :
  to_prod f j.succ = to_prod f j.cast_succ * (f j) :=
by simp [to_prod, list.take_succ, list.of_fn_nth_val, dif_pos j.is_lt, ←option.coe_def]

private lemma to_prod_succ' (f : fin (n + 1) → G) (j : fin (n + 1)) :
  to_prod f j.succ = f 0 * to_prod (fin.tail f) j :=
by simpa [to_prod]

end

variables [group G] (n : ℕ)
open_locale tensor_product

/-- The `k`-linear map from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` sending `(g₀, ..., gₙ)`
to `g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)` -/
def to_tensor_aux :
  of_mul_action k G (fin (n + 1) → G) →ₗ[k] monoid_algebra k G ⊗[k] ((fin n → G) →₀ k) :=
finsupp.lift (monoid_algebra k G ⊗[k] ((fin n → G) →₀ k)) k (fin (n + 1) → G)
  (λ x, finsupp.single (x 0) 1 ⊗ₜ[k] finsupp.single (λ i, (x i)⁻¹ * x i.succ) 1)

variables {k G n}

private lemma to_tensor_aux_single (f : fin (n + 1) → G) (m : k) :
  to_tensor_aux k G n (finsupp.single f m) =
    finsupp.single (f 0) m ⊗ₜ finsupp.single (λ i, (f i)⁻¹ * f i.succ) 1 :=
begin
  erw [finsupp.lift_apply, finsupp.sum_single_index, tensor_product.smul_tmul'],
  { simp },
  { simp },
end

private lemma to_tensor_aux_comm (g : G) (x : fin (n + 1) → G) :
  to_tensor_aux k G n (representation.of_mul_action k G (fin (n + 1) → G) g (finsupp.single x 1))
  = tensor_product.map (representation.of_mul_action k G G g) 1
    (to_tensor_aux k G n (finsupp.single x 1)) :=
begin
  dsimp,
  simp only [to_tensor_aux_single, finsupp.map_domain_single,
    tensor_product.map_tmul, finsupp.lmap_domain_apply],
  congr,
  ext i,
  simp [mul_assoc, inv_mul_cancel_left],
end

variables (k G n)


/-- A hom of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)` -/
def to_tensor : of_mul_action k G (fin (n + 1) → G) ⟶ Rep.of
  ((representation.of_mul_action k G G).tprod (1 : G →* module.End k ((fin n → G) →₀ k))) :=
{ hom := to_tensor_aux k G n,
  comm' := λ g, by ext; exact to_tensor_aux_comm _ _ }

variables {k G n}

@[simp] lemma to_tensor_single (f : fin (n + 1) → G) (m : k) :
  (to_tensor k G n).hom (finsupp.single f m) =
    finsupp.single (f 0) m ⊗ₜ finsupp.single (λ i, (f i)⁻¹ * f i.succ) 1 :=
to_tensor_aux_single _ _

variables (k G n)

/-- The `k`-linear map from `k[G] ⊗ₖ k[Gⁿ]` to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)` -/
def of_tensor_aux :
  monoid_algebra k G ⊗[k] ((fin n → G) →₀ k) →ₗ[k] of_mul_action k G (fin (n + 1) → G) :=
tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, monoid_algebra.of _ (fin (n + 1) → G) (g • to_prod f)))

variables {k G n}

private lemma of_tensor_aux_single (g : G) (m : k) (x : (fin n → G) →₀ k) :
  of_tensor_aux k G n ((finsupp.single g m) ⊗ₜ x) = finsupp.lift (of_mul_action k G
    (fin (n + 1) → G)) k (fin n → G) (λ f, finsupp.single (g • to_prod f) m) x :=
by simp [of_tensor_aux, finsupp.sum_single_index, finsupp.smul_sum, mul_comm m]

private lemma of_tensor_aux_comm (g h : G) (x : fin n → G) :
  of_tensor_aux k G n (tensor_product.map (representation.of_mul_action k G G g)
    (1 : module.End k ((fin n → G) →₀ k)) (finsupp.single h (1 : k) ⊗ₜ finsupp.single x (1 : k)))
  = representation.of_mul_action k G (fin (n + 1) → G) g (of_tensor_aux k G n
    (finsupp.single h 1 ⊗ₜ finsupp.single x 1)) :=
begin
  dsimp,
  simp [of_tensor_aux_single, mul_smul],
end

variables (k G n)

/-- A hom of `k`-linear representations of `G` from `k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts
by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) to `k[Gⁿ⁺¹]` sending `g ⊗ (g₁, ..., gₙ)` to
`(g, gg₁, gg₁g₂, ..., gg₁...gₙ)` -/
def of_tensor :
  Rep.of ((representation.of_mul_action k G G).tprod (1 : G →* module.End k ((fin n → G) →₀ k)))
    ⟶ of_mul_action k G (fin (n + 1) → G) :=
{ hom := of_tensor_aux k G n,
  comm' := λ g, by { ext, congr' 1, exact (of_tensor_aux_comm _ _ _) }}

variables {k G n}

@[simp] lemma of_tensor_single (g : G) (m : k) (x : (fin n → G) →₀ k) :
  (of_tensor k G n).hom ((finsupp.single g m) ⊗ₜ x) = finsupp.lift (of_mul_action k G
    (fin (n + 1) → G)) k (fin n → G) (λ f, finsupp.single (g • to_prod f) m) x :=
of_tensor_aux_single _ _ _

lemma of_tensor_single' (g : monoid_algebra k G) (x : fin n → G) (r : k) :
  (of_tensor k G n).hom (g ⊗ₜ finsupp.single x r) =
    finsupp.lift _ k G (λ a, finsupp.single (a • to_prod x) r) g :=
by simp [of_tensor, of_tensor_aux]


lemma equiv_tensor_left_inv_aux (f : fin (n + 1) → G) :
  f 0 • to_prod (λ i : fin n, (f i)⁻¹ * f i.succ) = f :=
funext $ λ ⟨x, hn⟩,
begin
  revert hn,
  induction x with x hx,
  { simp },
  { intro hn,
    dsimp at hx ⊢,
    rw [←fin.succ_mk _ _ (nat.succ_lt_succ_iff.1 hn), to_prod_succ],
    erw [←mul_assoc, hx (lt_trans (nat.lt_succ_self x) hn)],
    convert mul_inv_cancel_left _ _,
    ext,
    simp [nat.mod_eq_of_lt (lt_trans (nat.lt_succ_self _) hn)] }
end

lemma equiv_tensor_right_inv_aux (g : G) (f : fin n → G) (i : fin n) :
  ((g • to_prod f) i)⁻¹ * (g • to_prod f) i.succ = f i :=
begin
  cases i with i hn,
  revert hn,
  induction i with i hi,
  { intro hn,
    simp [←fin.succ_mk, to_prod_succ] },
  { intro hn,
    specialize hi (lt_trans (nat.lt_succ_self i) hn),
    simp only [mul_inv_rev, fin.coe_eq_cast_succ, fin.succ_mk, fin.cast_succ_mk,
      smul_eq_mul, pi.smul_apply] at hi ⊢,
    rw [←fin.succ_mk _ _ (lt_trans (nat.lt_succ_self _) hn), ←fin.succ_mk],
    simp only [to_prod_succ, mul_inv_rev, fin.cast_succ_mk],
    assoc_rw [hi, inv_mul_cancel_left] }
end

open monoid_algebra (lift) (of)

lemma equiv_tensor_left_inv (x : of_mul_action k G (fin (n + 1) → G)) :
  (of_tensor _ _ _).hom ((to_tensor _ _ _).hom x) = x :=
begin
  refine linear_map.ext_iff.1 (@finsupp.lhom_ext _ _ _ k _ _ _ _ _
    (linear_map.comp (of_tensor _ _ _).hom (to_tensor _ _ _).hom) linear_map.id (λ x y, _)) x,
  dsimp,
  rw [to_tensor_single x y, of_tensor_single,  finsupp.lift_apply, finsupp.sum_single_index,
    one_smul, equiv_tensor_left_inv_aux],
  { rw zero_smul }
end

lemma equiv_tensor_right_inv (x : monoid_algebra k G ⊗[k] of_mul_action k G (fin n → G)) :
  (to_tensor _ _ _).hom ((of_tensor _ _ _).hom x) = x :=
begin
  refine tensor_product.induction_on x (by simp) (λ y z, _) (λ z w hz hw, by simp [hz, hw]),
  erw [←finsupp.sum_single y, tensor_product.sum_tmul],
  simp only [finset.smul_sum, linear_map.map_sum],
  refine finset.sum_congr rfl (λ f hf, _),
  simp only [of_tensor_single, finsupp.lift_apply, finsupp.smul_single', linear_map.map_finsupp_sum,
    equivariant_of_linear_of_comm_apply, to_tensor_single, equiv_tensor_right_inv_aux],
  dsimp,
  simp only [to_prod_zero, mul_one],
  conv_rhs {rw ←finsupp.sum_single z},
  erw tensor_product.tmul_sum,
  exact finset.sum_congr rfl (λ g hg, show _ ⊗ₜ _ = _, by
    rw [←finsupp.smul_single', tensor_product.smul_tmul, finsupp.smul_single_one])
end

variables (k G n)

/-- A `k[G]`-linear isomorphism `k[Gⁿ⁺¹] ≅ k[G] ⊗ₖ k[Gⁿ]` -/
def equiv_tensor : (of_mul_action k G (fin (n + 1) → G)) ≅ Rep.of
  ((representation.of_mul_action k G G).tprod (1 : G →* module.End k ((fin n → G) →₀ k))) :=
Action.mk_iso (linear_equiv.to_Module_iso
{ inv_fun := of_tensor_aux k G n,
  left_inv := equiv_tensor_left_inv,
  right_inv := λ x, by convert equiv_tensor_right_inv x,
  ..to_tensor_aux k G n }) (to_tensor k G n).comm

variables {k G n}

@[simp] lemma equiv_tensor_single (x : fin (n + 1) → G) (m : k) :
  (equiv_tensor k G n).hom.hom (finsupp.single x m) = (finsupp.single (x 0) m) ⊗ₜ
    (finsupp.single (λ i, (x i)⁻¹ * x i.succ) (1 : k)) :=
to_tensor_single _ _

@[simp] lemma equiv_tensor_symm_apply (g : G) (m : k) (x : of_mul_action k G (fin n → G)) :
  (equiv_tensor _ G n).inv.hom ((finsupp.single g m) ⊗ₜ x) =
  finsupp.lift (of_mul_action k G (fin (n + 1) → G)) k (fin n → G)
    (λ f, finsupp.single (g • to_prod f) m) x :=
of_tensor_single _ _ _

end Rep


open_locale tensor_product
open tensor_product

section

variables {R : Type*} {A : Type*} {M : Type*} {N : Type*} {P : Type*} [comm_semiring R]
  [semiring A] [algebra R A] [add_comm_monoid M] [module R M] [module A M]
  [is_scalar_tower R A M] [add_comm_monoid N] [module R N] [add_comm_monoid P] [module R P]
  [module A P] [is_scalar_tower R A P] (n : ℕ)

@[simps] def tensor_product.lift_nc (f : M →ₗ[A] (N →ₗ[R] P)) : (M ⊗[R] N) →ₗ[A] P :=
{ map_smul' := λ c, show ∀ x : M ⊗[R] N, (tensor_product.lift (f.restrict_scalars R)).comp
  (algebra.lsmul R _ c) x = (algebra.lsmul R _ c).comp (tensor_product.lift (f.restrict_scalars R)) x,
    from linear_map.ext_iff.1 $ tensor_product.ext' $ λ x y,
    by simp only [linear_map.comp_apply, algebra.lsmul_coe, tensor_product.smul_tmul',
      tensor_product.lift.tmul, linear_map.coe_restrict_scalars_eq_coe,
      f.map_smul, linear_map.smul_apply],
  .. tensor_product.lift (f.restrict_scalars R) }

@[simp] lemma lift_nc_tmul (f : M →ₗ[A] (N →ₗ[R] P)) (x : M) (y : N) :
  tensor_product.lift_nc f (x ⊗ₜ y) = f x y :=
lift.tmul' x y

end

section

variables {k} (R : Type u) [ring R] [algebra k R] {M : Type u} [add_comm_group M]
  [module k M] {ι : Type*} (b : basis ι k M)

noncomputable def to_basis : (R ⊗[k] M) →ₗ[R] (ι →₀ R) :=
tensor_product.lift_nc (linear_map.to_span_singleton R _ ((finsupp.map_range.linear_map
  (linear_map.to_span_singleton k R 1)).comp b.repr.to_linear_map))

lemma to_basis_apply (r : R) (m : M) :
  to_basis R b (r ⊗ₜ m) = r • finsupp.map_range.linear_map (linear_map.to_span_singleton k R 1)
    (b.repr m) :=
begin
  rw [to_basis, lift_nc_tmul],
  refl,
end

lemma to_basis_apply' (r : R) (m : M) (i : ι) :
  to_basis R b (r ⊗ₜ m) i = r * linear_map.to_span_singleton k R 1 (b.repr m i) :=
begin
  rw to_basis_apply,
  refl,
end

noncomputable def of_basis : (ι →₀ R) →ₗ[R] (R ⊗[k] M) :=
finsupp.lift (R ⊗[k] M) R ι (λ i, 1 ⊗ₜ b.repr.symm (finsupp.single i 1))

lemma of_basis_apply (i : ι) (r : R) :
  of_basis R b (finsupp.single i r) = r ⊗ₜ b.repr.symm (finsupp.single i 1) :=
begin
  simp only [of_basis, basis.repr_symm_apply, finsupp.total_single, one_smul, finsupp.lift_apply,
    finsupp.sum_single_index, zero_smul],
  rw [tensor_product.smul_tmul', smul_eq_mul, mul_one]
end

lemma basis_right_inv_aux (i : ι) (r : R) :
  to_basis R b (of_basis R b (finsupp.single i r)) = finsupp.single i r :=
begin
  simp [of_basis_apply, to_basis_apply, b.repr.apply_symm_apply],
end

lemma basis_left_inv_aux (r : R) (m : M) :
  of_basis R b (to_basis R b (r ⊗ₜ m)) = r ⊗ₜ m :=
begin
  rw [to_basis_apply, linear_map.map_smul, ←finsupp.sum_single (b.repr m),
    linear_map.map_finsupp_sum, linear_map.map_finsupp_sum],
  simp only [finsupp.map_range.linear_map_apply, finsupp.map_range_single, of_basis_apply],
  simp only [linear_map.to_span_singleton_apply, basis.repr_symm_apply, finsupp.total_single, one_smul],
  simp only [tensor_product.smul_tmul],
  unfold finsupp.sum,
  rw [←tmul_sum, smul_tmul', smul_eq_mul, mul_one],
  congr,
  exact b.total_repr _,
end

lemma basis_left_inv (x : R ⊗[k] M) :
  of_basis R b (to_basis R b x) = x :=
begin
  refine x.induction_on _ _ _,
  { simp only [linear_map.map_zero] },
  { intros r m,
    exact basis_left_inv_aux _ _ _ _ },
  { intros x y hx hy,
    simp only [map_add, hx, hy] }
end

lemma basis_right_inv (x : ι →₀ R) :
  to_basis R b (of_basis R b x) = x :=
begin
  rw ←x.sum_single,
  simp only [linear_map.map_finsupp_sum, basis_right_inv_aux],
end

variables (M)

noncomputable def tensor_product_basis : basis ι R (R ⊗[k] M) :=
{ repr :=
  { inv_fun := of_basis R b,
    left_inv := basis_left_inv R b,
    right_inv := basis_right_inv R b, .. to_basis R b } }

end

namespace Rep
open_locale tensor_product
variables (k G) [group G] (n : ℕ)

instance : module (monoid_algebra k G) (representation.as_module
  (of_mul_action k G (fin (n + 1) → G)).ρ) :=
representation.as_module_module (of_mul_action k G (fin (n + 1) → G)).ρ

noncomputable def monoid_algebra_basis :
  basis (fin n → G) (monoid_algebra k G)
    (representation.as_module (of_mul_action k G (fin (n + 1) → G)).ρ) :=
sorry /-@basis.map (fin n → G) (monoid_algebra k G) _ _ _ _ tensor_product.left_module _ _
  ((tensor_product_basis (monoid_algebra k G)
  (representation.as_module (of_mul_action k G (fin n → G)).ρ))
  (⟨linear_equiv.refl k _⟩))-/ --(equiv_tensor k G n).symm.to_Module_iso

instance : module.free (monoid_algebra k G)
  (representation.as_module (of_mul_action k G (fin (n + 1) → G)).ρ) :=
module.free.of_basis (monoid_algebra_basis _ _ _)

end Rep
