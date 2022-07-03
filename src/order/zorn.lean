/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Eduardo Freire
-/
import order.chain
import tactic
/-!
# Zorn's lemmas

This file proves several formulations of Zorn's Lemma.

## Variants

The primary statement of Zorn's lemma is `exists_maximal_of_chains_bounded`. Then it is specialized
to particular relations:
* `(≤)` with `zorn_partial_order`
* `(⊆)` with `zorn_subset`
* `(⊇)` with `zorn_superset`

Lemma names carry modifiers:
* `₀`: Quantifies over a set, as opposed to over a type.
* `_nonempty`: Doesn't ask to prove that the empty chain is bounded and lets you give an element
  that will be smaller than the maximal element found (the maximal element is no smaller than any
  other element, but it can also be incomparable to some).

## How-to

This file comes across as confusing to those who haven't yet used it, so here is a detailed
walkthrough:
1. Know what relation on which type/set you're looking for. See Variants above. You can discharge
  some conditions to Zorn's lemma directly using a `_nonempty` variant.
2. Write down the definition of your type/set, put a `suffices : ∃ m, ∀ a, m ≺ a → a ≺ m, { ... },`
  (or whatever you actually need) followed by a `apply some_version_of_zorn`.
3. Fill in the details. This is where you start talking about chains.

A typical proof using Zorn could look like this
```lean
lemma zorny_lemma : zorny_statement :=
begin
  let s : set α := {x | whatever x},
  suffices : ∃ x ∈ s, ∀ y ∈ s, y ⊆ x → y = x, -- or with another operator
  { exact proof_post_zorn },
  apply zorn_subset, -- or another variant
  rintro c hcs hc,
  obtain rfl | hcnemp := c.eq_empty_or_nonempty, -- you might need to disjunct on c empty or not
  { exact ⟨edge_case_construction,
      proof_that_edge_case_construction_respects_whatever,
      proof_that_edge_case_construction_contains_all_stuff_in_c⟩ },
  exact ⟨construction,
    proof_that_construction_respects_whatever,
    proof_that_construction_contains_all_stuff_in_c⟩,
end
```

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

open classical set

variables {α β : Type*} {r : α → α → Prop} {c : set α}

local infix ` ≺ `:50  := r

/-- **Zorn's lemma**

If every chain has an upper bound, then there exists a maximal element. -/
lemma exists_maximal_of_chains_bounded (h : ∀ c, is_chain r c → ∃ ub, ∀ a ∈ c, a ≺ ub)
  (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃ m, ∀ a, m ≺ a → a ≺ m :=
have ∃ ub, ∀ a ∈ max_chain r, a ≺ ub,
  from h _ $ max_chain_spec.left,
let ⟨ub, (hub : ∀ a ∈ max_chain r, a ≺ ub)⟩ := this in
⟨ub, λ a ha,
  have is_chain r (insert a $ max_chain r),
    from max_chain_spec.1.insert $ λ b hb _, or.inr $ trans (hub b hb) ha,
  hub a $ by { rw max_chain_spec.right this (subset_insert _ _), exact mem_insert _ _ }⟩

/-- A variant of Zorn's lemma. If every nonempty chain of a nonempty type has an upper bound, then
there is a maximal element.
-/
theorem exists_maximal_of_nonempty_chains_bounded [nonempty α]
  (h : ∀ c, is_chain r c → c.nonempty → ∃ ub, ∀ a ∈ c, a ≺ ub)
  (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃ m, ∀ a, m ≺ a → a ≺ m :=
exists_maximal_of_chains_bounded
  (λ c hc,
    (eq_empty_or_nonempty c).elim
      (λ h, ⟨classical.arbitrary α, λ x hx, (h ▸ hx : x ∈ (∅ : set α)).elim⟩)
      (h c hc))
  (λ a b c, trans)

section preorder
variables [preorder α]

theorem zorn_preorder (h : ∀ c : set α, is_chain (≤) c → bdd_above c) :
  ∃ m : α, ∀ a, m ≤ a → a ≤ m :=
exists_maximal_of_chains_bounded h (λ a b c, le_trans)

theorem zorn_nonempty_preorder [nonempty α]
  (h : ∀ (c : set α), is_chain (≤) c → c.nonempty → bdd_above c) :
  ∃ (m : α), ∀ a, m ≤ a → a ≤ m :=
exists_maximal_of_nonempty_chains_bounded h (λ a b c, le_trans)

theorem zorn_preorder₀ (s : set α)
  (ih : ∀ c ⊆ s, is_chain (≤) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
  ∃ m ∈ s, ∀ z ∈ s, m ≤ z → z ≤ m :=
let ⟨⟨m, hms⟩, h⟩ := @zorn_preorder s _
  (λ c hc,
    let ⟨ub, hubs, hub⟩ := ih (subtype.val '' c) (λ _ ⟨⟨x, hx⟩, _, h⟩, h ▸ hx)
      (by { rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq;
        refine hc hpc hqc (λ t, hpq (subtype.ext_iff.1 t)) })
    in ⟨⟨ub, hubs⟩, λ ⟨y, hy⟩ hc, hub _ ⟨_, hc, rfl⟩⟩)
in ⟨m, hms, λ z hzs hmz, h ⟨z, hzs⟩ hmz⟩

theorem zorn_nonempty_preorder₀ (s : set α)
  (ih : ∀ c ⊆ s, is_chain (≤) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α) (hxs : x ∈ s) :
  ∃ m ∈ s, x ≤ m ∧ ∀ z ∈ s, m ≤ z → z ≤ m :=
begin
  rcases zorn_preorder₀ {y ∈ s | x ≤ y} (λ c hcs hc, _) with ⟨m, ⟨hms, hxm⟩, hm⟩,
  { exact ⟨m, hms, hxm, λ z hzs hmz, hm _ ⟨hzs, (hxm.trans hmz)⟩ hmz⟩ },
  { rcases c.eq_empty_or_nonempty with rfl|⟨y, hy⟩,
    { exact ⟨x, ⟨hxs, le_rfl⟩, λ z, false.elim⟩ },
    { rcases ih c (λ z hz, (hcs hz).1) hc y hy with ⟨z, hzs, hz⟩,
      exact ⟨z, ⟨hzs, (hcs hy).2.trans $ hz _ hy⟩, hz⟩ } }
end

end preorder

section partial_order
variables [partial_order α]

lemma zorn_partial_order (h : ∀ c : set α, is_chain (≤) c → bdd_above c) :
  ∃ m : α, ∀ a, m ≤ a → a = m :=
let ⟨m, hm⟩ := zorn_preorder h in ⟨m, λ a ha, le_antisymm (hm a ha) ha⟩

theorem zorn_nonempty_partial_order [nonempty α]
  (h : ∀ (c : set α), is_chain (≤) c → c.nonempty → bdd_above c) :
  ∃ (m : α), ∀ a, m ≤ a → a = m :=
let ⟨m, hm⟩ := zorn_nonempty_preorder h in ⟨m, λ a ha, le_antisymm (hm a ha) ha⟩

theorem zorn_partial_order₀ (s : set α)
  (ih : ∀ c ⊆ s, is_chain (≤) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
  ∃ m ∈ s, ∀ z ∈ s, m ≤ z → z = m :=
let ⟨m, hms, hm⟩ := zorn_preorder₀ s ih in ⟨m, hms, λ z hzs hmz, (hm z hzs hmz).antisymm hmz⟩

lemma zorn_nonempty_partial_order₀ (s : set α)
  (ih : ∀ c ⊆ s, is_chain (≤) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α) (hxs : x ∈ s) :
  ∃ m ∈ s, x ≤ m ∧ ∀ z ∈ s, m ≤ z → z = m :=
let ⟨m, hms, hxm, hm⟩ := zorn_nonempty_preorder₀ s ih x hxs
in ⟨m, hms, hxm, λ z hzs hmz, (hm z hzs hmz).antisymm hmz⟩

end partial_order

lemma zorn_subset (S : set (set α)) (h : ∀ c ⊆ S, is_chain (⊆) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) :
  ∃ m ∈ S, ∀ a ∈ S, m ⊆ a → a = m :=
zorn_partial_order₀ S h

lemma zorn_subset_nonempty (S : set (set α))
  (H : ∀ c ⊆ S, is_chain (⊆) c → c.nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x) (hx : x ∈ S) :
  ∃ m ∈ S, x ⊆ m ∧ ∀ a ∈ S, m ⊆ a → a = m :=
zorn_nonempty_partial_order₀ _ (λ c cS hc y yc, H _ cS hc ⟨y, yc⟩) _ hx

lemma zorn_superset (S : set (set α))
  (h : ∀ c ⊆ S, is_chain (⊆) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) :
  ∃ m ∈ S, ∀ a ∈ S, a ⊆ m → a = m :=
@zorn_partial_order₀ (set α)ᵒᵈ _ S $ λ c cS hc, h c cS hc.symm

lemma zorn_superset_nonempty (S : set (set α))
  (H : ∀ c ⊆ S, is_chain (⊆) c → c.nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) (x) (hx : x ∈ S) :
  ∃ m ∈ S, m ⊆ x ∧ ∀ a ∈ S, a ⊆ m → a = m :=
@zorn_nonempty_partial_order₀ (set α)ᵒᵈ _ S (λ c cS hc y yc, H _ cS hc.symm ⟨y, yc⟩) _ hx

/-- Every chain is contained in a maximal chain. This generalizes Hausdorff's maximality principle.
-/
lemma is_chain.exists_max_chain (hc : is_chain r c) : ∃ M, @is_max_chain _ r M ∧ c ⊆ M :=
begin
  obtain ⟨M, ⟨_, hM₀⟩, hM₁, hM₂⟩ :=
    zorn_subset_nonempty {s | c ⊆ s ∧ is_chain r s} _ c ⟨subset.rfl, hc⟩,
  { exact ⟨M, ⟨hM₀, λ d hd hMd, (hM₂ _ ⟨hM₁.trans hMd, hd⟩ hMd).symm⟩, hM₁⟩ },
  rintros cs hcs₀ hcs₁ ⟨s, hs⟩,
  refine ⟨⋃₀ cs, ⟨λ _ ha, set.mem_sUnion_of_mem ((hcs₀ hs).left ha) hs, _⟩,
    λ _, set.subset_sUnion_of_mem⟩,
  rintros y ⟨sy, hsy, hysy⟩ z ⟨sz, hsz, hzsz⟩ hyz,
  obtain rfl | hsseq := eq_or_ne sy sz,
  { exact (hcs₀ hsy).right hysy hzsz hyz },
  cases hcs₁ hsy hsz hsseq with h h,
  { exact (hcs₀ hsz).right (h hysy) hzsz hyz },
  { exact (hcs₀ hsy).right hysy (h hzsz) hyz }
end

/-- A finite nonempty chain has a maximal element.
-/
lemma max_of_fin_chain [partial_order α] {c : set α} (hc_fin : c.finite)
 (hc_chain : is_chain (≤) c) (hc_nonempty : c.nonempty) : ∃m ∈ c, ∀{b}, b ∈ c → b ≤ m :=
begin
  rcases finset.exists_maximal (set.finite.to_finset hc_fin)
    ((set.finite.nonempty_to_finset hc_fin).mpr hc_nonempty) with ⟨m, hmc, hm⟩,
  let hmc' := (set.finite.mem_to_finset hc_fin).mp hmc,
  use [m, hmc'],
  intros b hbc,
  by_cases hbm : b = m,
  { exact (eq.symm hbm).ge },
  { cases hc_chain hbc hmc' hbm, exact h, exfalso,
      exact hm b ((set.finite.mem_to_finset hc_fin).mpr hbc) ((ne.symm hbm).lt_of_le h) }
end

/-- A set of sets `F` is of finite character if given any `X`, `X ∈ F` exactly when
all of its finite subsets are in `F`.
-/
def finite_character (F : set (set α)) : Prop :=
  ∀ X, X ∈ F ↔ (∀ {Y : set α}, Y ⊆ X → Y.finite → Y ∈ F)

/-- Tukey's Lemma:
Sets of finite character contain a ⊆-maximal element comparable to a given element.
-/
theorem max_of_fin_character {F : set (set α)} {X : set α} (hX : X ∈ F) (h : finite_character F) :
  ∃M ∈ F, X ⊆ M ∧ ∀{Y}, Y ∈ F → M ⊆ Y → Y = M :=
begin
  apply zorn_subset_nonempty, swap, { exact hX },
  intros c c_ss c_chain c_nonempty,
  use c.sUnion,
  split, swap, { exact λs hs, set.subset_sUnion_of_mem hs },
  by_contra hUcF,
  rw h c.sUnion at hUcF, push_neg at hUcF,
  rcases hUcF with ⟨Y, Y_ss, Y_fin, hYF⟩,
  suffices : ∃b ∈ c, b ∉ F,	{ rcases this with ⟨b, hb1, hb2⟩, exact hb2 (c_ss hb1) },
  have : ∀y ∈ Y, ∃Z ∈ c, y ∈ Z,
  { intros y hy,
      rcases Y_ss hy with ⟨Z, hZc, hyZ⟩,
      exact ⟨Z, hZc, hyZ⟩ },
  choose f hfc hf using this,
  have sub_chain_fin := set.finite.dependent_image Y_fin f,
  set sub_chain := {y : set α | ∃ (x : α) (hx : x ∈ Y), y = f x hx}
  with sub_chain_def,
  have sub_chain_ss : sub_chain ⊆ c,
  { intros Z hZ,
      rw sub_chain_def at hZ,
      simp at hZ,
      rcases hZ with ⟨y, hyY, hyf⟩,
      rw hyf,
      exact hfc y hyY },
  have Y_nonempty : Y.nonempty,
  { rw← set.ne_empty_iff_nonempty,
      intro contra,
      rw contra at hYF,
      apply hYF,
      obtain ⟨X, hX⟩ : F.nonempty := ⟨X, hX⟩,
      exact (h X).mp hX (set.empty_subset X) set.finite_empty },
  have sub_chain_nonempty : sub_chain.nonempty,
  { cases Y_nonempty with y hy,
      exact set.nonempty_of_mem (by { rw sub_chain_def, simp, exact ⟨y, hy, rfl⟩ }) },
  rcases max_of_fin_chain sub_chain_fin (is_chain.mono sub_chain_ss c_chain)
  sub_chain_nonempty with ⟨m, hmsub, hm⟩,
  use [m, sub_chain_ss hmsub],
  suffices : Y ⊆ m, { rw h, push_neg, exact ⟨Y, this, Y_fin, hYF⟩ },
  suffices : ∀y ∈ Y, ∃Z ∈ sub_chain, y ∈ Z,
  { intros y hy,
      rcases this y hy with ⟨Z, Z_sub, hyZ⟩,
      exact hm Z_sub hyZ },
  intros y hy,
  use [f y hy, y, hy, rfl, hf y hy],
end
