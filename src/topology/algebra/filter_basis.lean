/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import order.filter.bases
import topology.algebra.module.basic
/-!
# Group and ring filter bases

A `group_filter_basis` is a `filter_basis` on a group with some properties relating
the basis to the group structure. The main theorem is that a `group_filter_basis`
on a group gives a topology on the group which makes it into a topological group
with neighborhoods of the neutral element generated by the given basis.

## Main definitions and results

Given a group `G` and a ring `R`:

* `group_filter_basis G`: the type of filter bases that will become neighborhood of `1`
  for a topology on `G` compatible with the group structure
* `group_filter_basis.topology`: the associated topology
* `group_filter_basis.is_topological_group`: the compatibility between the above topology
  and the group structure
* `ring_filter_basis R`: the type of filter bases that will become neighborhood of `0`
  for a topology on `R` compatible with the ring structure
* `ring_filter_basis.topology`: the associated topology
* `ring_filter_basis.is_topological_ring`: the compatibility between the above topology
  and the ring structure

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]
-/

open filter set topological_space function
open_locale topological_space filter pointwise

universe u

/-- A `group_filter_basis` on a group is a `filter_basis` satisfying some additional axioms.
  Example : if `G` is a topological group then the neighbourhoods of the identity are a
  `group_filter_basis`. Conversely given a `group_filter_basis` one can define a topology
  compatible with the group structure on `G`.  -/
class group_filter_basis (G : Type u) [group G] extends filter_basis G :=
(one' : ∀ {U}, U ∈ sets → (1 : G) ∈ U)
(mul' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U)
(inv' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x⁻¹) ⁻¹' U)
(conj' : ∀ x₀, ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x₀*x*x₀⁻¹) ⁻¹' U)

/-- A `add_group_filter_basis` on an additive group is a `filter_basis` satisfying some additional
  axioms. Example : if `G` is a topological group then the neighbourhoods of the identity are a
  `add_group_filter_basis`. Conversely given a `add_group_filter_basis` one can define a topology
  compatible with the group structure on `G`. -/
class add_group_filter_basis (A : Type u) [add_group A] extends filter_basis A :=
(zero' : ∀ {U}, U ∈ sets → (0 : A) ∈ U)
(add' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V + V ⊆ U)
(neg' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, -x) ⁻¹' U)
(conj' : ∀ x₀, ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x₀+x+-x₀) ⁻¹' U)

attribute [to_additive] group_filter_basis
attribute [to_additive] group_filter_basis.one'
attribute [to_additive] group_filter_basis.mul'
attribute [to_additive] group_filter_basis.inv'
attribute [to_additive] group_filter_basis.conj'
attribute [to_additive] group_filter_basis.to_filter_basis

/-- `group_filter_basis` constructor in the commutative group case. -/
@[to_additive "`add_group_filter_basis` constructor in the commutative group case."]
def group_filter_basis_of_comm {G : Type*} [comm_group G]
  (sets                   : set (set G))
  (nonempty               : sets.nonempty)
  (inter_sets  : ∀ (x y), x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y)
  (one : ∀ U ∈ sets, (1 : G) ∈ U)
  (mul : ∀ U ∈ sets, ∃ V ∈ sets, V * V ⊆ U)
  (inv : ∀ U ∈ sets, ∃ V ∈ sets, V ⊆ (λ x, x⁻¹) ⁻¹' U) : group_filter_basis G :=
{ sets := sets,
  nonempty := nonempty,
  inter_sets := inter_sets,
  one' := one,
  mul' := mul,
  inv' := inv,
  conj' := λ x U U_in, ⟨U, U_in, by simp⟩ }


namespace group_filter_basis
variables {G : Type u} [group G] {B : group_filter_basis G}

@[to_additive]
instance : has_mem (set G) (group_filter_basis G) :=
⟨λ s f, s ∈ f.sets⟩

@[to_additive] lemma one {U : set G} : U ∈ B → (1 : G) ∈ U := group_filter_basis.one'

@[to_additive] lemma mul {U : set G} : U ∈ B → ∃ V ∈ B, V*V ⊆ U := group_filter_basis.mul'

@[to_additive] lemma inv {U : set G} : U ∈ B → ∃ V ∈ B, V ⊆ (λ x, x⁻¹) ⁻¹' U :=
group_filter_basis.inv'

@[to_additive]
lemma conj : ∀ x₀, ∀ {U}, U ∈ B → ∃ V ∈ B, V ⊆ (λ x, x₀*x*x₀⁻¹) ⁻¹' U :=
group_filter_basis.conj'

/-- The trivial group filter basis consists of `{1}` only. The associated topology
is discrete. -/
@[to_additive "The trivial additive group filter basis consists of `{0}` only. The associated
topology is discrete."]
instance : inhabited (group_filter_basis G) :=
⟨begin
  refine { sets := {{1}}, nonempty := singleton_nonempty _, .. },
  all_goals { simp only [exists_prop, mem_singleton_iff] },
  { rintros - - rfl rfl,
    use {1},
    simp },
  { simp },
  { rintro - rfl,
    use {1},
    simp },
  { rintro - rfl,
    use {1},
    simp },
  { rintro x₀ - rfl,
    use {1},
    simp }
end⟩

@[to_additive]
lemma prod_subset_self (B : group_filter_basis G) {U : set G} (h : U ∈ B) : U ⊆ U * U :=
λ x x_in, ⟨1, x, one h, x_in, one_mul x⟩

/-- The neighborhood function of a `group_filter_basis` -/
@[to_additive "The neighborhood function of a `add_group_filter_basis`"]
def N (B : group_filter_basis G) : G → filter G :=
λ x, map (λ y, x*y) B.to_filter_basis.filter

@[simp, to_additive]
lemma N_one (B : group_filter_basis G) : B.N 1 = B.to_filter_basis.filter :=
by simp only [N, one_mul, map_id']

@[to_additive]
protected lemma has_basis (B : group_filter_basis G) (x : G) :
  has_basis (B.N x) (λ V : set G, V ∈ B) (λ V, (λ y, x*y) '' V) :=
has_basis.map (λ y, x * y) to_filter_basis.has_basis

/-- The topological space structure coming from a group filter basis. -/
@[to_additive "The topological space structure coming from an additive group filter basis."]
def topology (B : group_filter_basis G) : topological_space G :=
topological_space.mk_of_nhds B.N

@[to_additive]
lemma nhds_eq (B : group_filter_basis G) {x₀ : G} :
  @nhds G (B.topology) x₀ = B.N x₀ :=
begin
  rw [topological_space.nhds_mk_of_nhds],
  { intros x U U_in,
    rw (B.has_basis x).mem_iff at U_in,
    rcases U_in with ⟨V, V_in, H⟩,
    simpa [mem_pure] using H (mem_image_of_mem _ (group_filter_basis.one V_in)), },
  { intros x U U_in,
    rw (B.has_basis x).mem_iff at U_in,
    rcases U_in with ⟨V, V_in, H⟩,
    rcases group_filter_basis.mul V_in with ⟨W, W_in, hW⟩,
    use [(λ y, x*y) '' W, image_mem_map (filter_basis.mem_filter_of_mem _ W_in)],
    split,
    { rw image_subset_iff at H ⊢,
      exact ((B.prod_subset_self W_in).trans hW).trans H },
    { rintros y ⟨t, tW, rfl⟩,
      rw (B.has_basis _).mem_iff,
      use [W, W_in],
      apply subset.trans _ H, clear H,
      rintros z ⟨w, wW, rfl⟩,
      exact ⟨t*w, hW (mul_mem_mul tW wW), by simp [mul_assoc]⟩ } }
end

@[to_additive]
lemma nhds_one_eq (B : group_filter_basis G) :
  @nhds G (B.topology) (1 : G) = B.to_filter_basis.filter :=
by { rw B.nhds_eq, simp only [N, one_mul], exact map_id }

@[to_additive]
lemma nhds_has_basis (B : group_filter_basis G) (x₀ : G) :
has_basis (@nhds G B.topology x₀) (λ V : set G, V ∈ B) (λ V, (λ y, x₀ * y) '' V)  :=
by { rw B.nhds_eq, apply B.has_basis }

@[to_additive]
lemma nhds_one_has_basis (B : group_filter_basis G) :
has_basis (@nhds G B.topology 1) (λ V : set G, V ∈ B) id  :=
by { rw B.nhds_one_eq, exact B.to_filter_basis.has_basis }

@[to_additive]
lemma mem_nhds_one (B : group_filter_basis G) {U : set G} (hU : U ∈ B) : U ∈ @nhds G B.topology 1 :=
begin
  rw B.nhds_one_has_basis.mem_iff,
  exact ⟨U, hU, rfl.subset⟩
end

/-- If a group is endowed with a topological structure coming from
a group filter basis then it's a topological group. -/
@[to_additive, priority 100]
instance is_topological_group (B : group_filter_basis G) :
  @topological_group G B.topology _ :=
begin
  letI := B.topology,
  have basis := B.nhds_one_has_basis,
  have basis' := basis.prod basis,
  refine topological_group.of_nhds_one _ _ _ _,
  { rw basis'.tendsto_iff basis,
    suffices : ∀ U ∈ B, ∃ V W, (V ∈ B ∧ W ∈ B) ∧ ∀ a b, a ∈ V → b ∈ W → a * b ∈ U, by simpa,
    intros U U_in,
    rcases mul U_in with ⟨V, V_in, hV⟩,
    use [V, V, V_in, V_in],
    intros a b a_in b_in,
    exact hV ⟨a, b, a_in, b_in, rfl⟩ },
  { rw basis.tendsto_iff basis,
    intros U U_in,
    simpa using inv U_in },
  { intro x₀,
    rw [nhds_eq, nhds_one_eq],
    refl },
  { intro x₀,
    rw basis.tendsto_iff basis,
    intros U U_in,
    exact conj x₀ U_in }
end

end group_filter_basis

/-- A `ring_filter_basis` on a ring is a `filter_basis` satisfying some additional axioms.
  Example : if `R` is a topological ring then the neighbourhoods of the identity are a
  `ring_filter_basis`. Conversely given a `ring_filter_basis` on a ring `R`, one can define a
  topology on `R` which is compatible with the ring structure.  -/
class ring_filter_basis (R : Type u) [ring R] extends add_group_filter_basis R :=
(mul' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U)
(mul_left' : ∀ (x₀ : R) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x₀*x) ⁻¹' U)
(mul_right' : ∀ (x₀ : R) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x*x₀) ⁻¹' U)

namespace ring_filter_basis

variables {R : Type u} [ring R] (B : ring_filter_basis R)

instance : has_mem (set R) (ring_filter_basis R) :=
⟨λ s B, s ∈ B.sets⟩

lemma mul {U : set R} (hU : U ∈ B) : ∃ V ∈ B, V * V ⊆ U :=
mul' hU

lemma mul_left (x₀ : R) {U : set R} (hU : U ∈ B) :
  ∃ V ∈ B, V ⊆ (λ x, x₀*x) ⁻¹' U :=
mul_left' x₀ hU

lemma mul_right (x₀ : R) {U : set R} (hU : U ∈ B) :
  ∃ V ∈ B, V ⊆ (λ x, x*x₀) ⁻¹' U :=
mul_right' x₀ hU

/-- The topology associated to a ring filter basis.
It has the given basis as a basis of neighborhoods of zero. -/
def topology : topological_space R := B.to_add_group_filter_basis.topology

/-- If a ring is endowed with a topological structure coming from
a ring filter basis then it's a topological ring. -/
@[priority 100]
instance is_topological_ring {R : Type u} [ring R] (B : ring_filter_basis R) :
  @topological_ring R B.topology _ :=
begin
  let B' := B.to_add_group_filter_basis,
  letI := B'.topology,
  have basis := B'.nhds_zero_has_basis,
  have basis' := basis.prod basis,
  haveI := B'.is_topological_add_group,
  apply topological_ring.of_add_group_of_nhds_zero,
  { rw basis'.tendsto_iff basis,
    suffices : ∀ U ∈ B', ∃ V W, (V ∈ B' ∧ W ∈ B') ∧ ∀ a b, a ∈ V → b ∈ W → a * b ∈ U, by simpa,
    intros U U_in,
    rcases B.mul U_in with ⟨V, V_in, hV⟩,
    use [V, V, V_in, V_in],
    intros a b a_in b_in,
    exact hV ⟨a, b, a_in, b_in, rfl⟩ },
  { intro x₀,
    rw basis.tendsto_iff basis,
    intros U,
    simpa using B.mul_left x₀ },
  { intro x₀,
    rw basis.tendsto_iff basis,
    intros U,
    simpa using B.mul_right x₀ },
end

end ring_filter_basis

/-- A `module_filter_basis` on a module is a `filter_basis` satisfying some additional axioms.
  Example : if `M` is a topological module then the neighbourhoods of zero are a
  `module_filter_basis`. Conversely given a `module_filter_basis` one can define a topology
  compatible with the module structure on `M`.  -/
structure module_filter_basis (R M : Type*) [comm_ring R] [topological_space R]
  [add_comm_group M] [module R M] extends add_group_filter_basis M :=
(smul' : ∀ {U}, U ∈ sets → ∃ (V ∈ 𝓝 (0 : R)) (W ∈ sets), V • W ⊆ U)
(smul_left' : ∀ (x₀ : R) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x₀ • x) ⁻¹' U)
(smul_right' : ∀ (m₀ : M) {U}, U ∈ sets → ∀ᶠ x in 𝓝 (0 : R), x • m₀ ∈ U)

namespace module_filter_basis
variables {R M : Type*} [comm_ring R] [topological_space R]
  [add_comm_group M] [module R M] (B : module_filter_basis R M)

instance group_filter_basis.has_mem : has_mem (set M) (module_filter_basis R M) :=
⟨λ s B, s ∈ B.sets⟩

lemma smul  {U : set M} (hU : U ∈ B) : ∃ (V ∈ 𝓝 (0 : R)) (W ∈ B), V • W ⊆ U :=
B.smul' hU

lemma smul_left (x₀ : R) {U : set M} (hU : U ∈ B) : ∃ V ∈ B, V ⊆ (λ x, x₀ • x) ⁻¹' U :=
B.smul_left' x₀ hU

lemma smul_right (m₀ : M) {U : set M} (hU : U ∈ B) : ∀ᶠ x in 𝓝 (0 : R), x • m₀ ∈ U :=
B.smul_right' m₀ hU

/-- If `R` is discrete then the trivial additive group filter basis on any `R`-module is a
module filter basis. -/
instance [discrete_topology R] : inhabited (module_filter_basis R M) :=
⟨{ smul' := begin
     rintro U (h : U ∈ {{(0 : M)}}),
     rw mem_singleton_iff at h,
     use [univ, univ_mem, {0}, rfl],
     rintros a ⟨x, m, -, hm, rfl⟩,
     simp [mem_singleton_iff.1 hm, h]
   end,
   smul_left' := begin
     rintro x₀ U (h : U ∈ {{(0 : M)}}),
     rw mem_singleton_iff at h,
     use [{0}, rfl],
     simp [h]
   end,
   smul_right' := begin
     rintro m₀ U (h : U ∈ (0 : set (set M))),
     rw set.mem_zero at h,
     simp [h, nhds_discrete]
   end,
   ..show add_group_filter_basis M, from default }⟩

/-- The topology associated to a module filter basis on a module over a topological ring.
It has the given basis as a basis of neighborhoods of zero. -/
def topology : topological_space M := B.to_add_group_filter_basis.topology

/-- The topology associated to a module filter basis on a module over a topological ring.
It has the given basis as a basis of neighborhoods of zero. This version gets the ring
topology by unification instead of type class inference. -/
def topology' {R M : Type*} [comm_ring R] {tR : topological_space R}
  [add_comm_group M] [module R M] (B : module_filter_basis R M) : topological_space M :=
  B.to_add_group_filter_basis.topology

/-- A topological add group whith a basis of `𝓝 0` satisfying the axioms of `module_filter_basis`
is a topological module.

This lemma is mathematically useless because one could obtain such a result by applying
`module_filter_basis.has_continuous_smul` and use the fact that group topologies are characterized
by their neighborhoods of 0 to obtain the `has_continuous_smul` on the pre-existing topology.

But it turns out it's just easier to get it as a biproduct of the proof, so this is just a free
quality-of-life improvement. -/
lemma _root_.has_continuous_smul.of_basis_zero {ι : Type*} [topological_ring R]
  [topological_space M] [topological_add_group M] {p : ι → Prop} {b : ι → set M}
  (h : has_basis (𝓝 0) p b) (hsmul : ∀ {i}, p i → ∃ (V ∈ 𝓝 (0 : R)) j (hj : p j), V • (b j) ⊆ b i)
  (hsmul_left : ∀ (x₀ : R) {i}, p i → ∃ j (hj : p j), (b j) ⊆ (λ x, x₀ • x) ⁻¹' (b i))
  (hsmul_right : ∀ (m₀ : M) {i}, p i → ∀ᶠ x in 𝓝 (0 : R), x • m₀ ∈ (b i)) :
  has_continuous_smul R M :=
begin
  apply has_continuous_smul.of_nhds_zero,
  { rw h.tendsto_right_iff,
    intros i hi,
    rcases hsmul hi with ⟨V, V_in, j, hj, hVj⟩,
    apply mem_of_superset (prod_mem_prod V_in $ h.mem_of_mem hj),
    rintros ⟨v, w⟩ ⟨v_in : v ∈ V, w_in : w ∈ (b j)⟩,
    exact hVj (set.smul_mem_smul v_in w_in) },
  { intro m₀,
    rw h.tendsto_right_iff,
    intros i hi,
    exact hsmul_right m₀ hi },
  { intro x₀,
    rw h.tendsto_right_iff,
    intros i hi,
    rcases hsmul_left x₀ hi with ⟨j, hj, hji⟩,
    exact mem_of_superset (h.mem_of_mem hj) hji },
end

/-- If a module is endowed with a topological structure coming from
a module filter basis then it's a topological module. -/
@[priority 100]
instance has_continuous_smul [topological_ring R] :
  @has_continuous_smul R M _ _ B.topology  :=
begin
  let B' := B.to_add_group_filter_basis,
  letI := B'.topology,
  haveI := B'.is_topological_add_group,
  exact has_continuous_smul.of_basis_zero B'.nhds_zero_has_basis (λ _, B.smul) B.smul_left
    B.smul_right,
end

/-- Build a module filter basis from compatible ring and additive group filter bases. -/
def of_bases {R M : Type*} [comm_ring R]
  [add_comm_group M] [module R M] (BR : ring_filter_basis R) (BM : add_group_filter_basis M)
  (smul : ∀ {U}, U ∈ BM → ∃ (V ∈ BR) (W ∈ BM), V • W ⊆ U)
  (smul_left : ∀ (x₀ : R) {U}, U ∈ BM → ∃ V ∈ BM, V ⊆ (λ x, x₀ • x) ⁻¹' U)
  (smul_right : ∀ (m₀ : M) {U}, U ∈ BM → ∃ V ∈ BR, V ⊆ (λ x, x • m₀) ⁻¹' U) :
  @module_filter_basis R M _ BR.topology _ _ :=
{ smul' := begin
    intros U U_in,
    rcases smul U_in with ⟨V, V_in, W, W_in, H⟩,
    exact ⟨V, BR.to_add_group_filter_basis.mem_nhds_zero V_in, W, W_in, H⟩
  end,
  smul_left' := smul_left,
  smul_right' := begin
    intros m₀ U U_in,
    rcases smul_right m₀ U_in with ⟨V, V_in, H⟩,
    exact mem_of_superset (BR.to_add_group_filter_basis.mem_nhds_zero V_in) H
  end,
  ..BM }

end module_filter_basis
