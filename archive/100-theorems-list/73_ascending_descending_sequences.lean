/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import tactic.basic
import data.fintype.basic

/-!
# Erdős–Szekeres theorem

This file proves Theorem 73 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/), also
known as the Erdős–Szekeres theorem: given a sequence of more than `r * s` distinct
values, there is an increasing sequence of length longer than `r` or a decreasing sequence of length
longer than `s`.

We use the proof outlined at
https://en.wikipedia.org/wiki/Erdos-Szekeres_theorem#Pigeonhole_principle.

## Tags

sequences, increasing, decreasing, Ramsey, Erdos-Szekeres, Erdős–Szekeres, Erdős-Szekeres
-/

variables {α : Type*} [linear_order α] {β : Type*}

open function finset
open_locale classical

/--
**Erdős–Szekeres Theorem**: Given a sequence of more than `r * s` distinct values, there is an
increasing sequence of length longer than `r` or a decreasing sequence of length longer than `s`.

Proof idea:
We label each value in the sequence with two numbers specifying the longest increasing
subsequence ending there, and the longest decreasing subsequence ending there.
We then show the pair of labels must be unique. Now if there is no increasing sequence longer than
`r` and no decreasing sequence longer than `s`, then there are at most `r * s` possible labels,
which is a contradiction if there are more than `r * s` elements.
-/
theorem erdos_szekeres {r s n : ℕ} {f : fin n → α} (hn : r * s < n) (hf : injective f) :
  (∃ (t : finset (fin n)), r < t.card ∧ strict_mono_on f ↑t) ∨
  (∃ (t : finset (fin n)), s < t.card ∧ strict_anti_on f ↑t) :=
begin
  -- Given an index `i`, produce the set of increasing (resp., decreasing) subsequences which ends
  -- at `i`.
  let inc_sequences_ending_in : fin n → finset (finset (fin n)) :=
    λ i, univ.powerset.filter (λ t, finset.max t = i ∧ strict_mono_on f ↑t),
  let dec_sequences_ending_in : fin n → finset (finset (fin n)) :=
    λ i, univ.powerset.filter (λ t, finset.max t = i ∧ strict_anti_on f ↑t),
  -- The singleton sequence is in both of the above collections.
  -- (This is useful to show that the maximum length subsequence is at least 1, and that the set
  -- of subsequences is nonempty.)
  have inc_i : ∀ i, {i} ∈ inc_sequences_ending_in i := λ i, by simp [strict_mono_on],
  have dec_i : ∀ i, {i} ∈ dec_sequences_ending_in i := λ i, by simp [strict_anti_on],
  -- Define the pair of labels: at index `i`, the pair is the maximum length of an increasing
  -- subsequence ending at `i`, paired with the maximum length of a decreasing subsequence ending
  -- at `i`.
  -- We call these labels `(a_i, b_i)`.
  let ab : fin n → ℕ × ℕ,
  { intro i,
    apply (max' ((inc_sequences_ending_in i).image card) (nonempty.image ⟨{i}, inc_i i⟩ _),
           max' ((dec_sequences_ending_in i).image card) (nonempty.image ⟨{i}, dec_i i⟩ _)) },
  -- It now suffices to show that one of the labels is 'big' somewhere. In particular, if the
  -- first in the pair is more than `r` somewhere, then we have an increasing subsequence in our
  -- set, and if the second is more than `s` somewhere, then we have a decreasing subsequence.
  rsuffices ⟨i, hi⟩ : ∃ i, r < (ab i).1 ∨ s < (ab i).2,
  { apply or.imp _ _ hi,
    work_on_goal 1 { have : (ab i).1 ∈ _ := max'_mem _ _ },
    work_on_goal 2 { have : (ab i).2 ∈ _ := max'_mem _ _ },
    all_goals
    { intro hi,
      rw mem_image at this,
      obtain ⟨t, ht₁, ht₂⟩ := this,
      refine ⟨t, by rwa ht₂, _⟩,
      rw mem_filter at ht₁,
      apply ht₁.2.2 } },
  -- Show first that the pair of labels is unique.
  have : injective ab,
  { apply injective_of_lt_imp_ne,
    intros i j k q,
    injection q with q₁ q₂,
    -- We have two cases: `f i < f j` or `f j < f i`.
    -- In the former we'll show `a_i < a_j`, and in the latter we'll show `b_i < b_j`.
    cases lt_or_gt_of_ne (λ _, ne_of_lt ‹i < j› (hf ‹f i = f j›)),
    work_on_goal 1 { apply ne_of_lt _ q₁, have : (ab i).1 ∈ _ := max'_mem _ _ },
    work_on_goal 2 { apply ne_of_lt _ q₂, have : (ab i).2 ∈ _ := max'_mem _ _ },
    all_goals
    { -- Reduce to showing there is a subsequence of length `a_i + 1` which ends at `j`.
      rw nat.lt_iff_add_one_le,
      apply le_max',
      rw mem_image at this ⊢,
      -- In particular we take the subsequence `t` of length `a_i` which ends at `i`, by definition
      -- of `a_i`
      rcases this with ⟨t, ht₁, ht₂⟩,
      rw mem_filter at ht₁,
      -- Ensure `t` ends at `i`.
      have : t.max = i,
        simp [ht₁.2.1],
      -- Now our new subsequence is given by adding `j` at the end of `t`.
      refine ⟨insert j t, _, _⟩,
      -- First make sure it's valid, i.e., that this subsequence ends at `j` and is increasing
      { rw mem_filter,
        refine ⟨_, _, _⟩,
        { rw mem_powerset, apply subset_univ },
        -- It ends at `j` since `i < j`.
        { convert max_insert,
          rw [ht₁.2.1, max_eq_left],
          apply with_bot.coe_le_coe.mpr (le_of_lt ‹i < j›) },
        -- To show it's increasing (i.e., `f` is monotone increasing on `t.insert j`), we do cases
        -- on what the possibilities could be - either in `t` or equals `j`.
        simp only [strict_mono_on, strict_anti_on, coe_insert, set.mem_insert_iff,
          mem_coe],
        -- Most of the cases are just bashes.
        rintros x ⟨rfl | _⟩ y ⟨rfl | _⟩ _,
        { apply (irrefl _ ‹j < j›).elim },
        { exfalso,
          apply not_le_of_lt (trans ‹i < j› ‹j < y›) (le_max_of_eq ‹y ∈ t› ‹t.max = i›) },
        { apply lt_of_le_of_lt _ ‹f i < f j› <|> apply lt_of_lt_of_le ‹f j < f i› _,
          rcases lt_or_eq_of_le (le_max_of_eq ‹x ∈ t› ‹t.max = i›) with _ | rfl,
          { apply le_of_lt (ht₁.2.2 ‹x ∈ t› (mem_of_max ‹t.max = i›) ‹x < i›) },
          { refl } },
        { apply ht₁.2.2 ‹x ∈ t› ‹y ∈ t› ‹x < y› } },
      -- Finally show that this new subsequence is one longer than the old one.
      { rw [card_insert_of_not_mem, ht₂],
        intro _,
        apply not_le_of_lt ‹i < j› (le_max_of_eq ‹j ∈ t› ‹t.max = i›) } } },
      -- Finished both goals!
  -- Now that we have uniqueness of each label, it remains to do some counting to finish off.
  -- Suppose all the labels are small.
  by_contra q,
  push_neg at q,
  -- Then the labels `(a_i, b_i)` all fit in the following set: `{ (x,y) | 1 ≤ x ≤ r, 1 ≤ y ≤ s }`
  let ran : finset (ℕ × ℕ) := (range r).image nat.succ ×ˢ (range s).image nat.succ,
  -- which we prove here.
  have : image ab univ ⊆ ran,
  -- First some logical shuffling
  { rintro ⟨x₁, x₂⟩,
    simp only [mem_image, exists_prop, mem_range, mem_univ, mem_product, true_and, prod.mk.inj_iff],
    rintros ⟨i, rfl, rfl⟩,
    specialize q i,
    -- Show `1 ≤ a_i` and `1 ≤ b_i`, which is easy from the fact that `{i}` is a increasing and
    -- decreasing subsequence which we did right near the top.
    have z : 1 ≤ (ab i).1 ∧ 1 ≤ (ab i).2,
    { split;
      { apply le_max',
        rw mem_image,
        refine ⟨{i}, by solve_by_elim, card_singleton i⟩ } },
    refine ⟨_, _⟩,
    -- Need to get `a_i ≤ r`, here phrased as: there is some `a < r` with `a+1 = a_i`.
    { refine ⟨(ab i).1 - 1, _, nat.succ_pred_eq_of_pos z.1⟩,
      rw tsub_lt_iff_right z.1,
      apply nat.lt_succ_of_le q.1 },
    { refine ⟨(ab i).2 - 1, _, nat.succ_pred_eq_of_pos z.2⟩,
      rw tsub_lt_iff_right z.2,
      apply nat.lt_succ_of_le q.2 } },
  -- To get our contradiction, it suffices to prove `n ≤ r * s`
  apply not_le_of_lt hn,
  -- Which follows from considering the cardinalities of the subset above, since `ab` is injective.
  simpa [nat.succ_injective, card_image_of_injective, ‹injective ab›] using card_le_of_subset this,
end
