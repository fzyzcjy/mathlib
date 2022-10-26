/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/

import data.finsupp.fintype
import linear_algebra.free_module.ideal_quotient
import linear_algebra.isomorphisms
import ring_theory.dedekind_domain.ideal

/-!

# Ideal norms

This file defines the absolute ideal norm `ideal.abs_norm (I : ideal R) : ℕ` as the cardinality of
the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).

## Main definitions

 * `submodule.card_quot (S : submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
   This maps `⊥` to `0` and `⊤` to `1`.
 * `ideal.abs_norm (I : ideal R)`: the absolute ideal norm, defined as
   the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.
-/

open_locale big_operators

namespace submodule

variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

section

open_locale classical

/-- The cardinality of `(M ⧸ S)`, if `(M ⧸ S)` is finite, and `0` otherwise.
This is used to define the absolute ideal norm `ideal.abs_norm`.
-/
noncomputable def card_quot (S : submodule R M) : ℕ :=
if h : nonempty (fintype (M ⧸ S)) then @fintype.card _ h.some else 0

@[simp] lemma card_quot_apply (S : submodule R M) [h : fintype (M ⧸ S)] :
  card_quot S = fintype.card (M ⧸ S) :=
by convert dif_pos (nonempty.intro h) -- `convert` deals with the different `fintype` instances

@[simp] lemma card_quot_bot [infinite M] : card_quot (⊥ : submodule R M) = 0 :=
dif_neg (by simp; apply_instance)

@[simp] lemma card_quot_top : card_quot (⊤ : submodule R M) = 1 :=
calc card_quot ⊤ = fintype.card (M ⧸ ⊤) : card_quot_apply _
... = fintype.card punit : fintype.card_eq.mpr ⟨equiv_of_subsingleton_of_subsingleton 0 0⟩
... = 1 : fintype.card_punit

@[simp] lemma card_quot_eq_one_iff {P : submodule R M} : card_quot P = 1 ↔ P = ⊤ :=
begin
  unfold card_quot,
  split_ifs,
  { rw [fintype.card_eq_one_iff_nonempty_unique, submodule.unique_quotient_iff_eq_top] },
  { simp only [zero_ne_one, false_iff],
    rintro rfl,
    have : nonempty (fintype (M ⧸ ⊤)) := ⟨@quotient_top.fintype R M _ _ _⟩,
    contradiction }
end

end

end submodule

variables {S : Type*} [comm_ring S] [is_domain S]

open submodule

/-- Multiplicity of the ideal norm, for coprime ideals.
This is essentially just a repackaging of the Chinese Remainder Theorem.
-/
lemma card_quot_mul_of_coprime [is_dedekind_domain S] [module.free ℤ S] [module.finite ℤ S]
  (I J : ideal S) (coprime : I ⊔ J = ⊤) : card_quot (I * J) = card_quot I * card_quot J :=
begin
  let b := module.free.choose_basis ℤ S,
  casesI is_empty_or_nonempty (module.free.choose_basis_index ℤ S),
  { haveI : subsingleton S := function.surjective.subsingleton b.repr.to_equiv.symm.surjective,
    nontriviality S,
    exfalso,
    exact not_nontrivial_iff_subsingleton.mpr ‹subsingleton S› ‹nontrivial S› },
  haveI : infinite S := infinite.of_surjective _ b.repr.to_equiv.surjective,
  by_cases hI : I = ⊥,
  { rw [hI, submodule.bot_mul, card_quot_bot, zero_mul] },
  by_cases hJ : J = ⊥,
  { rw [hJ, submodule.mul_bot, card_quot_bot, mul_zero] },
  have hIJ : I * J ≠ ⊥ := mt ideal.mul_eq_bot.mp (not_or hI hJ),

  letI := classical.dec_eq (module.free.choose_basis_index ℤ S),
  letI := I.fintype_quotient_of_free_of_ne_bot hI,
  letI := J.fintype_quotient_of_free_of_ne_bot hJ,
  letI := (I * J).fintype_quotient_of_free_of_ne_bot hIJ,

  rw [card_quot_apply, card_quot_apply, card_quot_apply,
      fintype.card_eq.mpr ⟨(ideal.quotient_mul_equiv_quotient_prod I J coprime).to_equiv⟩,
      fintype.card_prod]
end

/-- If `a ∈ P^i \ P^(i+1) c ∈ P^i`, then `a * d + e = c` for `e ∈ P^(i+1)`.
`ideal.mul_add_mem_pow_succ_unique` shows the choice of `d` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.exists_mul_add_mem_pow_succ [is_dedekind_domain S]
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  (a c : S) (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1)) (c_mem : c ∈ P ^ i) :
  ∃ (d : S) (e ∈ P ^ (i + 1)), a * d + e = c :=
begin
  suffices eq_b : P ^ i = ideal.span {a} ⊔ P ^ (i + 1),
  { rw eq_b at c_mem,
    simp only [mul_comm a],
    exact ideal.mem_span_singleton_sup.mp c_mem },
  refine (ideal.eq_prime_pow_of_succ_lt_of_le hP
    (lt_of_le_of_ne le_sup_right _)
    (sup_le (ideal.span_le.mpr (set.singleton_subset_iff.mpr a_mem))
      (ideal.pow_succ_lt_pow hP i).le)).symm,
  contrapose! a_not_mem with this,
  rw this,
  exact mem_sup.mpr ⟨a, mem_span_singleton_self a, 0, by simp, by simp⟩
end

lemma prime_pow_succ_dvd_mul {α : Type*} [cancel_comm_monoid_with_zero α]
  {p x y : α} (h : prime p) {i : ℕ} (hxy : p ^ (i + 1) ∣ x * y) :
  p ^ (i + 1) ∣ x ∨ p ∣ y :=
begin
  rw or_iff_not_imp_right,
  intro hy,
  induction i with i ih generalizing x,
  { simp only [zero_add, pow_one] at *,
    exact (h.dvd_or_dvd hxy).resolve_right hy },
  rw pow_succ at hxy ⊢,
  obtain ⟨x', rfl⟩ := (h.dvd_or_dvd (dvd_of_mul_right_dvd hxy)).resolve_right hy,
  rw mul_assoc at hxy,
  exact mul_dvd_mul_left p (ih ((mul_dvd_mul_iff_left h.ne_zero).mp hxy)),
end

lemma ideal.mem_prime_of_mul_mem_pow [is_dedekind_domain S]
  {P : ideal S} [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  {a b : S} (a_not_mem : a ∉ P ^ (i + 1))
  (ab_mem : a * b ∈ P ^ (i + 1)) : b ∈ P :=
begin
  simp only [← ideal.span_singleton_le_iff_mem, ← ideal.dvd_iff_le, pow_succ,
       ← ideal.span_singleton_mul_span_singleton] at a_not_mem ab_mem ⊢,
  exact (prime_pow_succ_dvd_mul (ideal.prime_of_is_prime hP P_prime) ab_mem).resolve_left a_not_mem
end

/-- The choice of `d` in `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`.
Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.mul_add_mem_pow_succ_unique [is_dedekind_domain S]
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ}
  (a d d' e e' : S) (a_not_mem : a ∉ P ^ (i + 1))
  (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
  (h : (a * d + e) - (a * d' + e') ∈ P ^ (i + 1)) : d - d' ∈ P :=
begin
  have : e' - e ∈ P ^ (i + 1) := ideal.sub_mem _ e'_mem e_mem,
  have h' : a * (d - d') ∈ P ^ (i + 1),
  { convert ideal.add_mem _ h (ideal.sub_mem _ e'_mem e_mem),
    ring },
  exact ideal.mem_prime_of_mul_mem_pow hP a_not_mem h'
end

/-- If the `d` from `ideal.exists_mul_add_mem_pow_succ` is unique, up to `P`,
then so are the `c`s, up to `P ^ (i + 1)`.
Inspired by [Neukirch], proposition 6.1 -/
lemma ideal.mul_add_mem_pow_succ_inj
  (P : ideal S) {i : ℕ} (a d d' e e' : S) (a_mem : a ∈ P ^ i)
  (e_mem : e ∈ P ^ (i + 1)) (e'_mem : e' ∈ P ^ (i + 1))
  (h : d - d' ∈ P) : (a * d + e) - (a * d' + e') ∈ P ^ (i + 1) :=
begin
  have : a * d - a * d' ∈ P ^ (i + 1),
  { convert ideal.mul_mem_mul a_mem h; simp [mul_sub, pow_succ, mul_comm] },
  convert ideal.add_mem _ this (ideal.sub_mem _ e_mem e'_mem),
  ring,
end

/-- Multiplicity of the ideal norm, for powers of prime ideals. -/
lemma card_quot_pow_of_prime [is_dedekind_domain S] [module.finite ℤ S] [module.free ℤ S]
  (P : ideal S) [P_prime : P.is_prime] (hP : P ≠ ⊥) {i : ℕ} :
  card_quot (P ^ i) = card_quot P ^ i :=
begin
  let b := module.free.choose_basis ℤ S,
  classical,
  induction i with i ih,
  { simp },
  letI := ideal.fintype_quotient_of_free_of_ne_bot (P ^ i.succ) (pow_ne_zero _ hP),
  letI := ideal.fintype_quotient_of_free_of_ne_bot (P ^ i) (pow_ne_zero _ hP),
  letI := ideal.fintype_quotient_of_free_of_ne_bot P hP,
  have : P ^ (i + 1) < P ^ i := ideal.pow_succ_lt_pow hP i,
  suffices hquot : map (P ^ i.succ).mkq (P ^ i) ≃ S ⧸ P,
  { rw [pow_succ (card_quot P), ← ih, card_quot_apply (P ^ i.succ),
      ← card_quotient_mul_card_quotient (P ^ i) (P ^ i.succ) this.le,
      card_quot_apply (P ^ i), card_quot_apply P],
    congr' 1,
    rw fintype.card_eq,
    exact ⟨hquot⟩ },
  choose a a_mem a_not_mem using set_like.exists_of_lt this,
  -- TODO: can we do this with less repetition?
  refine equiv.of_bijective (λ c', quotient.mk' _) ⟨_, _⟩,
  { cases c' with c' hc',
    choose c hc eq_c' using submodule.mem_map.mp hc',
    exact (ideal.exists_mul_add_mem_pow_succ P hP a c a_mem a_not_mem hc).some },
  { intros c₁' c₂' h,
    cases c₁' with c₁' hc₁',
    cases c₂' with c₂' hc₂',
    rw subtype.mk_eq_mk,
    replace h := (submodule.quotient.eq _).mp h,
    simp only [mkq_apply, ideal.quotient.mk_eq_mk, mem_map] at h,
    obtain ⟨hc₁, eq_c₁'⟩ := classical.some_spec (submodule.mem_map.mp hc₁'),
    obtain ⟨hc₂, eq_c₂'⟩ := classical.some_spec (submodule.mem_map.mp hc₂'),
    intro h,
    rw [← eq_c₁', ← eq_c₂', mkq_apply, mkq_apply, submodule.quotient.eq],
    obtain ⟨he₁, hd₁⟩ :=
      (ideal.exists_mul_add_mem_pow_succ P hP a _ a_mem a_not_mem hc₁).some_spec.some_spec,
    obtain ⟨he₂, hd₂⟩ :=
      (ideal.exists_mul_add_mem_pow_succ P hP a _ a_mem a_not_mem hc₂).some_spec.some_spec,
    rw [← hd₁, ← hd₂],
    exact ideal.mul_add_mem_pow_succ_inj P a _ _ _ _ a_mem he₁ he₂ h },
  { intros d',
    refine quotient.induction_on' d' (λ d, _),
    have hc' := ideal.mul_mem_right d _ a_mem,
    have hd' := mem_map.mpr ⟨a * d, hc', rfl⟩,
    refine ⟨⟨_, hd'⟩, _⟩,
    simp only [submodule.quotient.mk'_eq_mk, ideal.quotient.mk_eq_mk, ideal.quotient.eq],
    obtain ⟨he, hd''⟩ :=
      (ideal.exists_mul_add_mem_pow_succ P hP a _ a_mem a_not_mem hc').some_spec.some_spec,
    refine ideal.mul_add_mem_pow_succ_unique P hP a _ _ 0 _ a_not_mem _ he _,
    { exact (P ^ (i + 1)).zero_mem },
    convert submodule.neg_mem _ (ideal.add_mem _ he he), -- Come on, Lean!
    rw add_zero,
    conv_lhs { congr, skip, congr, rw ← hd'' },
    rw [eq_neg_iff_add_eq_zero, add_assoc, ← sub_sub, sub_add_cancel],
    convert sub_self _,
    -- At some point we used `a * d` as a witness for an existential,
    -- so now we need to show the choice of witness doesn't matter.
    have sub_mem := (submodule.quotient.eq _).mp (classical.some_spec (mem_map.mp hd')).2,
    ext x,
    split; rintro ⟨e, he, eq⟩,
    { refine ⟨_, submodule.add_mem _ he sub_mem, _⟩,
      rw [← add_assoc, eq], ring },
    { refine ⟨_, submodule.sub_mem _ he sub_mem, _⟩,
      rw [← add_sub_assoc, eq], ring } }
end

/-- Multiplicativity of the ideal norm in number rings. -/
theorem card_quot_mul [is_dedekind_domain S] [module.free ℤ S] [module.finite ℤ S] (I J : ideal S) :
  card_quot (I * J) = card_quot I * card_quot J :=
begin
  let b := module.free.choose_basis ℤ S,
  casesI is_empty_or_nonempty (module.free.choose_basis_index ℤ S),
  { haveI : subsingleton S := function.surjective.subsingleton b.repr.to_equiv.symm.surjective,
    nontriviality S,
    exfalso,
    exact not_nontrivial_iff_subsingleton.mpr ‹subsingleton S› ‹nontrivial S›, },
  haveI : infinite S := infinite.of_surjective _ b.repr.to_equiv.surjective,
  exact unique_factorization_monoid.multiplicative_of_coprime card_quot I J
    card_quot_bot
    (λ I J hI, by simp [ideal.is_unit_iff.mp hI, ideal.mul_top])
    (λ I i hI, have ideal.is_prime I := ideal.is_prime_of_prime hI,
              by exactI card_quot_pow_of_prime _ hI.ne_zero)
    (λ I J hIJ, card_quot_mul_of_coprime I J (ideal.is_unit_iff.mp (hIJ _
      (ideal.dvd_iff_le.mpr le_sup_left)
      (ideal.dvd_iff_le.mpr le_sup_right))))
end

/-- The absolute norm of the ideal `I : ideal R` is the cardinality of the quotient `R ⧸ I`. -/
noncomputable def ideal.abs_norm [infinite S] [is_dedekind_domain S]
  [module.free ℤ S] [module.finite ℤ S] :
  ideal S →*₀ ℕ :=
{ to_fun := submodule.card_quot,
  map_mul' := λ I J, by rw card_quot_mul,
  map_one' := by rw [ideal.one_eq_top, card_quot_top],
  map_zero' := by rw [ideal.zero_eq_bot, card_quot_bot] }
