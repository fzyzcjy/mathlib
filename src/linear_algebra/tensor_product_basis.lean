/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import linear_algebra.direct_sum.finsupp
import linear_algebra.finsupp_vector_space

/-!
# Bases and dimensionality of tensor products of modules

These can not go into `linear_algebra.tensor_product` since they depend on
`linear_algebra.finsupp_vector_space` which in turn imports `linear_algebra.tensor_product`.

-/
noncomputable theory
open set linear_map submodule

open_locale tensor_product

section comm_ring
variables {R : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
variables [comm_ring R] [add_comm_group M] [module R M] [add_comm_group N] [module R N]

/-- If b : ι → M and c : κ → N are bases then so is λ i, b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N. -/
def basis.tensor_product (b : basis ι R M) (c : basis κ R N) :
  basis (ι × κ) R (tensor_product R M N) :=
finsupp.basis_single_one.map
  ((tensor_product.congr b.repr c.repr).trans $
    (finsupp_tensor_finsupp R _ _ _ _).trans $
    finsupp.lcongr (equiv.refl _) (tensor_product.lid R R)).symm

@[simp]
lemma basis.tensor_product_apply (b : basis ι R M) (c : basis κ R N) (i : ι) (j : κ) :
  basis.tensor_product b c (i, j) = b i ⊗ₜ c j :=
by simp [basis.tensor_product]

lemma basis.tensor_product_apply' (b : basis ι R M) (c : basis κ R N) (i : ι × κ) :
  basis.tensor_product b c i = b i.1 ⊗ₜ c i.2 :=
by simp [basis.tensor_product]

end comm_ring

section field
variables {K : Type*} (V W : Type*)
variables [field K] [add_comm_group V] [module K V] [add_comm_group W] [module K W]

/-- If `V` and `W` are finite dimensional `K` vector spaces, so is `V ⊗ W`. -/
instance finite_dimensional_tensor_product [finite_dimensional K V] [finite_dimensional K W] :
  finite_dimensional K (tensor_product K V W) :=
finite_dimensional.of_fintype_basis
  (basis.tensor_product (basis.of_vector_space K V) (basis.of_vector_space K W))

end field

section finiteness

variables {R : Type*} {M : Type*} {N : Type*}
variables [comm_semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
variables [module.finite R M] [module.finite R N]

instance tensor_product.finite : module.finite R (M ⊗[R] N) :=
{ out := begin
  rcases _inst_6.out with ⟨sM, hM⟩,
  rcases _inst_7.out with ⟨sN, hN⟩,
  let s := { t : M ⊗[R] N | ∃ (m ∈ sM) (n ∈ sN), m ⊗ₜ n = t },
  have h : s = (λ p : M × N, p.1 ⊗ₜ p.2) '' (finset.product sM sN) :=
  by { ext, split,
       { intro hx, rcases hx with ⟨m, hm, n, hn, hx'⟩,
       use ⟨(m, n), finset.mk_mem_product hm hn, by rw [←hx']⟩, },
       { intro hx, rcases hx with ⟨p, hp, hx'⟩,
       use ⟨p.1, (finset.mem_product.1 hp).1, p.2, (finset.mem_product.1 hp).2, by rw [←hx']⟩, }, },
  rw submodule.fg_def,
  use ⟨s, by {rw h, exact finite.image _ (finset.finite_to_set _)},
    tensor_product.span_tmul_set_eq_top hM hN⟩,
end }

end finiteness
