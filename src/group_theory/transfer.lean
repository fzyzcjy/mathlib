/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.zmod.quotient
import group_theory.complement
import group_theory.group_action.basic
import group_theory.index

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
-/

section quotient_action

-- PRed
lemma mk_smul_out' {α β : Type*} [group α] [monoid β] [mul_action β α] (H : subgroup α)
  [mul_action.quotient_action β H] (b : β) (q : α ⧸ H) :
  quotient_group.mk (b • q.out') = b • q :=
by rw [←mul_action.quotient.smul_mk, quotient_group.out_eq']

-- PRed
lemma coe_smul_out' {α β : Type*} [group α] [monoid β] [mul_action β α] (H : subgroup α)
  [mul_action.quotient_action β H] (b : β) (q : α ⧸ H) :
  ↑(b • q.out') = b • q :=
mk_smul_out' H b q

end quotient_action

section equiv_stuff

section lemmaa

open function

-- PRed
@[to_additive] lemma smul_iterate {G S : Type*} [monoid G] [mul_action G S] (x : G) (s : S) (n : ℕ) :
  has_scalar.smul x^[n] s = (x ^ n) • s :=
nat.rec_on n (by rw [iterate_zero, id.def, pow_zero, one_smul])
  (λ n ih, by rw [iterate_succ', comp_app, ih, pow_succ, mul_smul])

-- PRed
lemma iterate_injective_of_lt_minimal_period {α : Type*} {f : α → α} {x : α}
  {m n : ℕ} (hm : m < minimal_period f x) (hn : n < minimal_period f x)
  (hf : (f^[m] x) = (f^[n] x)) :
  m = n :=
begin
  wlog h_le : m ≤ n,
  have : (f^[(minimal_period f x - n) + m] x) = x,
  by rw [iterate_add_apply, hf, ←iterate_add_apply, nat.sub_add_cancel hn.le,
    iterate_eq_mod_minimal_period, nat.mod_self, iterate_zero_apply],
  have key := is_periodic_pt.minimal_period_le (nat.add_pos_left (nat.sub_pos_of_lt hn) m) this,
  rw [←nat.sub_add_comm hn.le, le_tsub_iff_right, add_le_add_iff_left] at key,
  exact le_antisymm h_le key,
  refine hn.le.trans (nat.le_add_right _ _),
end

end lemmaa

-- PRed
@[to_additive] instance subgroup.zpowers.is_commutative {G : Type*} [group G] (g : G) :
  (subgroup.zpowers g).is_commutative :=
⟨⟨λ ⟨a, b, c⟩ ⟨d, e, f⟩, by rw [subtype.ext_iff, subgroup.coe_mul, subgroup.coe_mul,
  subtype.coe_mk, subtype.coe_mk, ←c, ←f, zpow_mul_comm]⟩⟩

@[to_additive add_the_key_lemma]
lemma the_key_lemma {α β : Type*} [group α] {a : α} [mul_action α β] {b : β} {n : ℤ} :
  a ^ n • b = b ↔ (function.minimal_period ((•) a) b : ℤ) ∣ n :=
begin
  have key : ∀ k : ℕ, a ^ k • b = b ↔ function.minimal_period ((•) a) b ∣ k,
  { intro k,
    rw ← smul_iterate,
    exact function.is_periodic_pt_iff_minimal_period_dvd },
  cases n,
  { rw [int.of_nat_eq_coe, zpow_coe_nat, key, int.coe_nat_dvd] },
  { rw [zpow_neg_succ_of_nat, inv_smul_eq_iff, eq_comm, key],
    rw [int.neg_succ_of_nat_eq, dvd_neg, ←int.coe_nat_one, ←int.coe_nat_add, int.coe_nat_dvd] },
end


noncomputable def zmultiples_quotient_stabilizer_equiv
  {α β : Type*} [add_group α] (a : α) [add_action α β] (b : β) :
  add_subgroup.zmultiples a ⧸ add_action.stabilizer (add_subgroup.zmultiples a) b ≃+
  zmod (function.minimal_period ((+ᵥ) a) b) :=
begin
  refine (add_equiv.symm (add_equiv.of_bijective
    (quotient_add_group.map (add_subgroup.zmultiples (function.minimal_period ((+ᵥ) a) b : ℤ))
    (add_action.stabilizer (add_subgroup.zmultiples a) b)
    (zmultiples_hom (add_subgroup.zmultiples a)
    ⟨a, add_subgroup.mem_zmultiples a⟩) _) _)).trans
    (int.quotient_zmultiples_nat_equiv_zmod (function.minimal_period ((+ᵥ) a) b)),
  { -- this rw chain should be a lemma:
    rw [add_subgroup.zmultiples_eq_closure, add_subgroup.closure_le, set.singleton_subset_iff],
    rw [set_like.mem_coe, add_subgroup.mem_comap, add_action.mem_stabilizer_iff,
        zmultiples_hom_apply],
    rw [coe_nat_zsmul, ←vadd_iterate],
    exact function.is_periodic_pt_minimal_period ((+ᵥ) a) b },
  { split,
    { refine (add_monoid_hom.ker_eq_bot_iff _).mp (le_bot_iff.mp _),
      refine λ q, quotient.induction_on' q (λ n hn, _),
      replace hn := (quotient_add_group.eq_zero_iff _).mp hn,
      change n • a +ᵥ b = b at hn,
      refine (quotient_add_group.eq_zero_iff n).mpr _,
      rw [int.mem_zmultiples_iff],
      exact add_the_key_lemma.mp hn },
    { refine λ q, quotient.induction_on' q _,
      rintros ⟨-, n, rfl⟩,
      exact ⟨n, rfl⟩ } },
end

instance party {α β : Type*} [monoid α] [mul_action α β] :
  add_action (additive α) β :=
{ vadd := λ a b, (additive.to_mul a • b),
  zero_vadd := one_smul α,
  add_vadd := mul_smul }

noncomputable def zpowers_quotient_stabilizer_equiv
  {α β : Type*} [group α] (a : α) [mul_action α β] (b : β) :
  subgroup.zpowers a ⧸ mul_action.stabilizer (subgroup.zpowers a) b ≃*
  multiplicative (zmod (function.minimal_period ((•) a) b)) :=
let f := (zmultiples_quotient_stabilizer_equiv (additive.of_mul a) b) in
{ to_fun := f.to_fun,
  inv_fun := f.inv_fun,
  left_inv := f.left_inv,
  right_inv := f.right_inv,
  map_mul' := f.map_add' }

noncomputable def orbit_zpowers_equiv
  {α β : Type*} [group α] (a : α) [mul_action α β] (b : β) :
  mul_action.orbit (subgroup.zpowers a) b ≃ zmod (function.minimal_period ((•) a) b) :=
begin
  refine (mul_action.orbit_equiv_quotient_stabilizer (subgroup.zpowers a) b).trans _,
  exact (zpowers_quotient_stabilizer_equiv a b).to_equiv,
end

lemma orbit_zpowers_equiv_symm_apply {α β : Type*} [group α] (a : α) [mul_action α β] (b : β)
  (k : zmod (function.minimal_period ((•) a) b)) :
  (orbit_zpowers_equiv a b).symm k =
  (⟨a, subgroup.mem_zpowers a⟩ : subgroup.zpowers a) ^ (k : ℤ) • ⟨b, mul_action.mem_orbit_self b⟩ :=
rfl

universe u

noncomputable def key_equiv {G : Type u} [group G] (H : subgroup G) (g : G) :
  G ⧸ H ≃ Σ (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H))),
  zmod (function.minimal_period ((•) g) q.out') :=
(mul_action.self_equiv_sigma_orbits (subgroup.zpowers g) (G ⧸ H)).trans
  (equiv.sigma_congr_right (λ q, orbit_zpowers_equiv g q.out'))

lemma key_equiv_symm_apply {G : Type u} [group G] (H : subgroup G) (g : G)
  (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  (key_equiv H g).symm ⟨q, k⟩ = g ^ (k : ℤ) • q.out' :=
rfl

lemma key_equiv_apply {G : Type u} [group G] (H : subgroup G) (g : G)
  (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : ℤ) :
  key_equiv H g (g ^ k • q.out') = ⟨q, k⟩ :=
begin
  rw [equiv.apply_eq_iff_eq_symm_apply, key_equiv_symm_apply],
  rw [←inv_smul_eq_iff, ←zpow_neg_one, ←zpow_mul, mul_neg_one, ←mul_smul, ←zpow_add, add_comm,
    ←sub_eq_add_neg, the_key_lemma, ←zmod.int_coe_eq_int_coe_iff_dvd_sub],
  rw [zmod.int_cast_cast, zmod.cast_int_cast'],
end

end equiv_stuff

section transversal_stuff

def key_transversal {G : Type*} [group G] (H : subgroup G) (g : G) : subgroup.left_transversals (H : set G) :=
⟨set.range (λ q, g ^ ((key_equiv H g q).2 : ℤ) * (key_equiv H g q).1.out'.out'),
  subgroup.range_mem_left_transversals (λ q, by rw [←smul_eq_mul, coe_smul_out',
    ←key_equiv_symm_apply, sigma.eta, equiv.symm_apply_apply])⟩

lemma key_transversal_apply {G : Type*} [group G] (H : subgroup G) (g : G) (q : G ⧸ H) :
  ↑(subgroup.mem_left_transversals.to_equiv (key_transversal H g).2 q) =
    g ^ ((key_equiv H g q).2 : ℤ) * (key_equiv H g q).1.out'.out' :=
subgroup.mem_left_transversals.range_to_equiv_apply (λ q, by rw [←smul_eq_mul, coe_smul_out',
  ←key_equiv_symm_apply, sigma.eta, equiv.symm_apply_apply]) q

lemma key_transversal_apply' {G : Type*} [group G] (H : subgroup G)
  (g : G) (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  ↑(subgroup.mem_left_transversals.to_equiv (key_transversal H g).2 (g ^ (k : ℤ) • q.out')) =
    g ^ (k : ℤ) * q.out'.out' :=
by rw [key_transversal_apply, ←key_equiv_symm_apply, equiv.apply_symm_apply]


lemma zmod.coe_neg_one {R : Type*} [ring R] (n : ℕ) : ↑(-1 : zmod n) = (n - 1 : R) :=
begin
  cases n,
  { rw [int.cast_neg, int.cast_one, nat.cast_zero, zero_sub] },
  { transitivity ((((n : ℤ) : zmod n.succ).val : ℤ) : R),
    { refine congr_arg zmod.cast _,
      rw [neg_eq_iff_add_eq_zero, add_comm],
      exact zmod.nat_cast_self n.succ },
    { rw [zmod.val_int_cast, int.mod_eq_of_lt, int.cast_coe_nat, nat.cast_succ, add_sub_cancel],
      { exact int.coe_nat_nonneg n },
      { rw [int.coe_nat_succ, lt_add_iff_pos_right],
        exact zero_lt_one } } },
end

lemma key_transversal_apply'' {G : Type*} [group G] (H : subgroup G)
  (g : G) (q : quotient (mul_action.orbit_rel (subgroup.zpowers g) (G ⧸ H)))
  (k : zmod (function.minimal_period ((•) g) q.out')) :
  ↑(subgroup.mem_left_transversals.to_equiv (g • key_transversal H g).2 (g ^ (k : ℤ) • q.out')) =
    if k = 0 then g ^ (function.minimal_period ((•) g) q.out') * q.out'.out'
      else g ^ (k : ℤ) * q.out'.out' :=
begin
  rw [subgroup.smul_apply_eq_smul_apply_inv_smul, key_transversal_apply, ←mul_smul, ←zpow_neg_one,
      ←zpow_add, key_equiv_apply, smul_eq_mul, ←mul_assoc, ←zpow_one_add,
      int.cast_add, int.cast_neg, int.cast_one],
  simp only,
  by_cases hk : k = 0,
  { rw [hk, if_pos rfl, mul_left_inj, zmod.cast_zero, int.cast_zero, add_zero, ←zpow_coe_nat],
    refine congr_arg ((^) g) _,
    rw [zmod.coe_neg_one, int.nat_cast_eq_coe_nat, add_sub_cancel'_right] },
  { rw [if_neg hk, mul_left_inj],
    refine congr_arg ((^) g) _,
    rw [zmod.coe_add_eq_ite, if_pos, zmod.coe_neg_one, add_sub, ←add_assoc, add_sub_cancel'_right],
    simp only [int.nat_cast_eq_coe_nat, zmod.int_cast_cast, zmod.cast_id', id.def, add_tsub_cancel_left],
    rw [zmod.coe_neg_one, sub_add],
    simp only [int.nat_cast_eq_coe_nat, zmod.int_cast_cast, zmod.cast_id', id.def, le_sub_self_iff, sub_nonpos],
    sorry },
end

end transversal_stuff

open_locale big_operators

variables {G : Type*} [group G] {H : subgroup G} {A : Type*} [comm_group A] (ϕ : H →* A)

namespace subgroup

namespace left_transversals

open finset mul_action

open_locale pointwise

variables (R S T : left_transversals (H : set G)) [fintype (G ⧸ H)]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α := mem_left_transversals.to_equiv S.2, β := mem_left_transversals.to_equiv T.2 in
∏ q, ϕ ⟨(α q)⁻¹ * β q, quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive] lemma diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
prod_mul_distrib.symm.trans (prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans (congr_arg ϕ
  (by simp_rw [subtype.ext_iff, coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left]))))

@[to_additive] lemma diff_self : diff ϕ T T = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive] lemma diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
inv_eq_of_mul_eq_one ((diff_mul_diff ϕ S T S).trans (diff_self ϕ S))

@[to_additive] lemma smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
prod_bij' (λ q _, g⁻¹ • q) (λ _ _, mem_univ _) (λ _ _, congr_arg ϕ (by simp_rw [coe_mk,
  smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]))
  (λ q _, g • q) (λ _ _, mem_univ _) (λ q _, smul_inv_smul g q) (λ q _, inv_smul_smul g q)

end left_transversals

end subgroup

namespace monoid_hom

variables [fintype (G ⧸ H)]

open subgroup subgroup.left_transversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`."]
noncomputable def transfer : G →* A :=
let T : left_transversals (H : set G) := inhabited.default in
{ to_fun := λ g, diff ϕ T (g • T),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

variables (T : left_transversals (H : set G))

@[to_additive] lemma transfer_def (g : G) : transfer ϕ g = diff ϕ T (g • T) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

section explicit_computation

variables (H)

open_locale classical

lemma transfer_computation (g : G) : transfer ϕ g =
  ∏ (q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H))),
    ϕ ⟨q.out'.out'⁻¹ * g ^ (function.minimal_period ((•) g) q.out') * q.out'.out', sorry⟩ :=
begin
  haveI : ∀ q : quotient (mul_action.orbit_rel (zpowers g) (G ⧸ H)), fintype
    (zmod (function.minimal_period ((•) g) q.out')) := sorry,
  calc transfer ϕ g = ∏ (q : G ⧸ H), _ : transfer_def ϕ (key_transversal H g) g
  ... = _ : ((key_equiv H g).symm.prod_comp _).symm
  ... = _ : finset.prod_sigma _ _ _
  ... = _ : fintype.prod_congr _ _ (λ q, _),
  simp only [key_equiv_symm_apply, key_transversal_apply', key_transversal_apply''],
  rw fintype.prod_eq_single (0 : zmod (function.minimal_period ((•) g) q.out')),
  { simp only [if_pos, zmod.cast_zero, zpow_zero, one_mul, mul_assoc] },
  { intros k hk,
    simp only [if_neg hk, inv_mul_self],
    exact ϕ.map_one },
end

end explicit_computation

section explicit_computation

lemma _root_.subgroup.pow_index_mem
  {G : Type*} [group G] (H : subgroup G) [H.normal] [fintype (G ⧸ H)] (g : G) :
  g ^ H.index ∈ H :=
begin
  rw [←quotient_group.eq_one_iff, quotient_group.coe_pow, index_eq_card, pow_card_eq_one],
end

lemma _root_.subgroup.pow_index_mem_of_le_center
  {G : Type*} [group G] (H : subgroup G) (hH : H ≤ center G) [fintype (G ⧸ H)] (g : G) :
  g ^ H.index ∈ H :=
begin
  haveI : normal H := sorry,
  exact H.pow_index_mem g,
end


lemma transfer_eq_pow [fintype (G ⧸ H)] (hH : H ≤ center G) [fintype (G ⧸ H)] (g : G) :
  transfer ϕ g = ϕ ⟨g ^ H.index, H.pow_index_mem_of_le_center hH g⟩ :=
begin
  rw transfer_computation,
  sorry,
end

noncomputable def transfer_pow (hH : H ≤ center G) [fintype (G ⧸ H)] : G →* H :=
{ to_fun := λ g, ⟨g ^ H.index, H.pow_index_mem_of_le_center hH g⟩,
  map_one' := subtype.ext (one_pow H.index),
  map_mul' := λ a b, begin
    letI : is_commutative H := ⟨⟨λ a b, subtype.ext (hH b.2 a)⟩⟩,
    simp_rw [←show ∀ g, (_ : H) = ⟨_, _⟩, from transfer_eq_pow (id H) hH, map_mul],
  end }

noncomputable def transfer_pow' (hH : H ≤ center G) (hH₀ : H.index ≠ 0) : G →* H :=
begin
  haveI : fintype (G ⧸ H) := fintype_of_index_ne_zero hH₀,
  exact transfer_pow hH,
end

end explicit_computation

end monoid_hom
