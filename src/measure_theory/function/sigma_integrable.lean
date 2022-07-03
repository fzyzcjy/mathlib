/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.integral.integrable_on

/-!
# σ-integrable functions

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

-/


open filter set function
open_locale measure_theory nnreal ennreal topological_space big_operators


namespace measure_theory

variables {α E F : Type*} {m m₂ m0' m0 : measurable_space α} {μ ν : measure α} {ν' : @measure α m0'}
  [normed_group E] [normed_group F]
  {f g : α → E} {s t : set α}

@[protect_proj, nolint has_inhabited_instance]
structure integrable_spanning_sets_in {m : measurable_space α}
  (f : α → E) (μ : measure α) (C : set (set α)) :=
(set : ℕ → set α)
(set_mem : ∀ i, set i ∈ C)
(integrable_on : ∀ i, integrable_on f (set i) μ)
(spanning : (⋃ i, set i) = univ)

/-- A function is σ-integrable with respect to a measure `μ` and a σ-algebra `m` if the space can be
covered by countably many sets `s ∈ m` such that `f` is integrable on `s`.

Important special case: an integrable function is σ-integrable on any σ-algebra (see
`integrable.sigma_integrable`). -/
def sigma_integrable (m : measurable_space α) {m0 : measurable_space α}
  (f : α → E) (μ : measure α) : Prop :=
nonempty (integrable_spanning_sets_in f μ {s | measurable_set[m] s})

namespace sigma_integrable

def spanning_sets (h : sigma_integrable m f μ) : ℕ → set α := accumulate h.some.set

lemma monotone_spanning_sets (h : sigma_integrable m f μ) :
  monotone h.spanning_sets :=
monotone_accumulate

lemma measurable_spanning_sets (h : sigma_integrable m f μ) (n : ℕ) :
  measurable_set[m] (h.spanning_sets n) :=
measurable_set.Union $ λ j, measurable_set.Union_Prop $ (λ n, h.some.set_mem j)

lemma integrable_on_spanning_sets (h : sigma_integrable m f μ) (n : ℕ) :
  integrable_on f (h.spanning_sets n) μ :=
begin
  simp_rw [spanning_sets, accumulate],
  let s := {i | i ≤ n},
  have hs : s.finite := finite_Iic n,
  have : (⋃ (y : ℕ) (H : y ≤ n), (nonempty.some h).set y) = ⋃ y ∈ s, (nonempty.some h).set y,
  { ext1 x, simp [s], },
  rw [this, integrable_on_finite_Union hs],
  exact λ i his, h.some.integrable_on i,
end

lemma Union_spanning_sets (h : sigma_integrable m f μ) :
  (⋃ i, h.spanning_sets i) = univ :=
by rw [spanning_sets, Union_accumulate, h.some.spanning]

def spanning_sets_disj (hf : sigma_integrable m f μ) : ℕ → set α :=
disjointed hf.spanning_sets

lemma disjoint_spanning_sets_disj (hf : sigma_integrable m f μ) :
  pairwise (disjoint on hf.spanning_sets_disj) :=
disjoint_disjointed _

lemma measurable_spanning_sets_disj (hf : sigma_integrable m f μ) (n : ℕ) :
  measurable_set[m] (hf.spanning_sets_disj n) :=
disjointed_rec (λ t i ht, ht.diff (hf.measurable_spanning_sets i)) (hf.measurable_spanning_sets n)

lemma integrable_on_spanning_sets_disj (hf : sigma_integrable m f μ) (n : ℕ) :
  integrable_on f (hf.spanning_sets_disj n) μ :=
begin
  refine @disjointed_rec _ _ _ (λ s, integrable_on f s μ) _ _ _,
  { exact λ t i ht, integrable_on.mono_set ht (diff_subset _ _), },
  { exact hf.integrable_on_spanning_sets n, },
end

lemma Union_spanning_sets_disj (hf : sigma_integrable m f μ) :
  (⋃ n, hf.spanning_sets_disj n) = univ :=
by rw [spanning_sets_disj, Union_disjointed, hf.Union_spanning_sets]

lemma exists_spanning_sets_disj_mem (hf : sigma_integrable m f μ) (x : α) :
  ∃ n, x ∈ hf.spanning_sets_disj n :=
begin
  have h := hf.Union_spanning_sets_disj,
  rw set.ext_iff at h,
  specialize h x,
  simpa only [mem_Union, mem_univ, iff_true] using h,
end

/-- `n : ℕ` such than `x ∈ hf.spanning_sets_disj n`. -/
def first_spanning_sets_disj_mem (hf : sigma_integrable m f μ) (x : α)
  [decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] : ℕ :=
nat.find (hf.exists_spanning_sets_disj_mem x)

lemma mem_first_spanning_sets_disj_mem (hf : sigma_integrable m f μ) (x : α)
  [decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] :
  x ∈ hf.spanning_sets_disj (hf.first_spanning_sets_disj_mem x) :=
nat.find_spec (hf.exists_spanning_sets_disj_mem x)

lemma first_spanning_sets_disj_mem_eq_iff_mem (hf : sigma_integrable m f μ) (x : α)
  [decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] {n : ℕ} :
  hf.first_spanning_sets_disj_mem x = n ↔ x ∈ hf.spanning_sets_disj n :=
begin
  split; intro h,
  { rw ← h, exact hf.mem_first_spanning_sets_disj_mem x, },
  by_contra h_ne_n,
  have h_mem : x ∈ hf.spanning_sets_disj (hf.first_spanning_sets_disj_mem x),
    from hf.mem_first_spanning_sets_disj_mem x,
  have h_disj : disjoint (hf.spanning_sets_disj n)
      (hf.spanning_sets_disj (hf.first_spanning_sets_disj_mem x)),
    from hf.disjoint_spanning_sets_disj n (hf.first_spanning_sets_disj_mem x) (ne.symm h_ne_n),
  rw disjoint_iff_forall_ne at h_disj,
  exact h_disj x h x h_mem rfl,
end

noncomputable
def mk_strongly_measurable_aux (hf : sigma_integrable m f μ) : ℕ → α → E :=
λ n, (hf.spanning_sets_disj n).indicator ((hf.integrable_on_spanning_sets_disj n).1.mk _)

lemma ae_eq_mk_strongly_measurable_aux (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n : ℕ) :
  f =ᵐ[μ.restrict (hf.spanning_sets_disj n)] hf.mk_strongly_measurable_aux n :=
begin
  have h := (hf.integrable_on_spanning_sets_disj n).1.ae_eq_mk,
  rw [eventually_eq, ae_restrict_iff' (hm _ (hf.measurable_spanning_sets_disj n))] at h ⊢,
  refine h.mono (λ x hx hx_mem, _),
  specialize hx hx_mem,
  rw mk_strongly_measurable_aux,
  dsimp only,
  rw [indicator_of_mem hx_mem],
  exact hx,
end

lemma strongly_measurable_mk_strongly_measurable_aux (hf : sigma_integrable m f μ) (hm : m ≤ m0)
  (n : ℕ) :
  strongly_measurable (hf.mk_strongly_measurable_aux n) :=
strongly_measurable.indicator
  (hf.integrable_on_spanning_sets_disj n).1.strongly_measurable_mk
  (hm _ (hf.measurable_spanning_sets_disj n))

noncomputable
def mk_strongly_measurable (hf : sigma_integrable m f μ)
  [∀ x, decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] :
  α → E :=
λ x, (hf.mk_strongly_measurable_aux (hf.first_spanning_sets_disj_mem x)) x

lemma ae_eq_mk_strongly_measurable (hf : sigma_integrable m f μ) (hm : m ≤ m0)
  [∀ x, decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] :
  f =ᵐ[μ] hf.mk_strongly_measurable :=
begin
  have h_ae_eq' : ∀ n, ∀ᵐ x ∂μ,
    x ∈ (hf.spanning_sets_disj n) → f x = hf.mk_strongly_measurable_aux n x,
  { intro n,
    have h_ae_eq := hf.ae_eq_mk_strongly_measurable_aux hm n,
    rw [eventually_eq, ae_restrict_iff' (hm _ (hf.measurable_spanning_sets_disj n))] at h_ae_eq,
    exact h_ae_eq, },
  rw ← ae_all_iff at h_ae_eq',
  refine h_ae_eq'.mono (λ x hx, _),
  exact hx (hf.first_spanning_sets_disj_mem x) (hf.mem_first_spanning_sets_disj_mem x),
end

lemma exists_approx_in_spanning_sets_disj (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n : ℕ) :
  ∃ (fs : ℕ → simple_func α E),
    (∀ x, tendsto (λ n, fs n x) at_top (𝓝 (hf.mk_strongly_measurable_aux n x)))
    ∧ ∀ x, x ∉ hf.spanning_sets_disj n → ∀ n, fs n x = 0 :=
strongly_measurable.strongly_measurable_in_set
  (hm _ (hf.measurable_spanning_sets_disj n))
  (hf.strongly_measurable_mk_strongly_measurable_aux hm n) (λ x hx, indicator_of_not_mem hx _)

noncomputable
def approx_aux (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n i : ℕ) : simple_func α E :=
(hf.exists_approx_in_spanning_sets_disj hm n).some i

lemma tendsto_approx_aux (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n : ℕ) (x : α) :
  tendsto (λ i, hf.approx_aux hm n i x) at_top (𝓝 (hf.mk_strongly_measurable_aux n x)) :=
(hf.exists_approx_in_spanning_sets_disj hm n).some_spec.1 x

lemma approx_aux_eq_zero (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n : ℕ) (x : α)
  (hx : x ∉ hf.spanning_sets_disj n) (i : ℕ) :
  hf.approx_aux hm n i x = 0 :=
(hf.exists_approx_in_spanning_sets_disj hm n).some_spec.2 x hx i

lemma approx_aux_eq_zero_of_ne (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n : ℕ) (x : α)
  [decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] (hx : hf.first_spanning_sets_disj_mem x ≠ n)
  (i : ℕ) :
  hf.approx_aux hm n i x = 0 :=
begin
  refine approx_aux_eq_zero hf hm n x _ i,
  rwa [ne.def, first_spanning_sets_disj_mem_eq_iff_mem] at hx,
end

lemma approx_aux_apply (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n i : ℕ) (x : α)
  [decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] :
  hf.approx_aux hm n i x = ite (hf.first_spanning_sets_disj_mem x = n)
    (hf.approx_aux hm (hf.first_spanning_sets_disj_mem x) i x) 0 :=
begin
  split_ifs,
  { rw ← h, },
  { rw approx_aux_eq_zero_of_ne hf hm n x h, },
end

noncomputable
def approx₂ (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n j : ℕ) : simple_func α E :=
∑ i in finset.range n, hf.approx_aux hm i j

lemma approx₂_def (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n j : ℕ) :
  hf.approx₂ hm n j = ∑ i in finset.range n, hf.approx_aux hm i j :=
rfl

lemma approx₂_apply (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n j : ℕ) (x : α)
  [decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] :
  hf.approx₂ hm n j x = ite (hf.first_spanning_sets_disj_mem x < n)
        (hf.approx_aux hm (hf.first_spanning_sets_disj_mem x) j x) 0 :=
begin
  induction n with n hn,
  { simp only [approx₂_def hf hm 0, finset.range_zero, finset.sum_empty, simple_func.coe_zero,
      pi.zero_apply, not_lt_zero', if_false], },
  { rw hf.approx₂_def hm at hn ⊢,
    rw [finset.sum_range_succ, simple_func.coe_add, pi.add_apply, hn,
      hf.approx_aux_apply hm n j x],
    split_ifs,
    { exact absurd h_1 h.ne, },
    { exact absurd h_1 h.ne, },
    { rw add_zero, },
    { exact absurd (h.trans (nat.lt_succ_self _)) h_2, },
    { rw zero_add, },
    { rw h_1 at h_2,
      exact absurd (nat.lt_succ_self n) h_2, },
    { refine absurd h_2 _,
      rw [nat.lt_succ_iff_lt_or_eq, auto.not_or_eq],
      exact ⟨h, h_1⟩, },
    { rw zero_add, }, },
end

noncomputable
def approx (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n : ℕ) : simple_func α E :=
hf.approx₂ hm n n

lemma approx_def (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n : ℕ) :
  hf.approx hm n = hf.approx₂ hm n n :=
rfl

lemma approx_apply (hf : sigma_integrable m f μ) (hm : m ≤ m0) (n : ℕ) (x : α)
  [decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] :
  hf.approx hm n x = ite (hf.first_spanning_sets_disj_mem x < n)
        (hf.approx_aux hm (hf.first_spanning_sets_disj_mem x) n x) 0 :=
by rw [approx_def hf hm, approx₂_apply hf hm n n]

lemma strongly_measurable_mk_strongly_measurable (hf : sigma_integrable m f μ) (hm : m ≤ m0)
  [∀ x, decidable_pred (λ n, x ∈ hf.spanning_sets_disj n)] :
  strongly_measurable hf.mk_strongly_measurable :=
begin
  refine ⟨hf.approx hm, λ x, _⟩,
  rw ← tendsto_add_at_top_iff_nat (hf.first_spanning_sets_disj_mem x + 1),
  have h : (λ n, hf.approx hm (n + (hf.first_spanning_sets_disj_mem x + 1)) x)
    = λ n, hf.approx_aux hm (hf.first_spanning_sets_disj_mem x)
      (n + (hf.first_spanning_sets_disj_mem x + 1)) x,
  { ext1 n,
    rw [approx_apply hf hm, if_pos],
    exact (@le_add_left _ _ _ n _ le_rfl).trans_lt (nat.lt_succ_self _), },
  rw [h, @tendsto_add_at_top_iff_nat _
    (λ n, hf.approx_aux hm (hf.first_spanning_sets_disj_mem x) n x) _
    (hf.first_spanning_sets_disj_mem x + 1)],
  exact hf.tendsto_approx_aux hm (hf.first_spanning_sets_disj_mem x) x,
end

protected lemma ae_strongly_measurable (hf : sigma_integrable m f μ) (hm : m ≤ m0) :
  ae_strongly_measurable f μ :=
begin
  classical,
  exact ⟨hf.mk_strongly_measurable, hf.strongly_measurable_mk_strongly_measurable hm,
    hf.ae_eq_mk_strongly_measurable hm⟩,
end

lemma congr_fun (hfg : f =ᵐ[μ] g) (hf : sigma_integrable m f μ) :
  sigma_integrable m g μ :=
⟨⟨hf.spanning_sets,
  hf.measurable_spanning_sets,
  λ n, integrable_on.congr_fun' (hf.integrable_on_spanning_sets n) (ae_restrict_of_ae hfg),
  hf.Union_spanning_sets⟩⟩

lemma mono_measurable_space (hf : sigma_integrable m f μ) (hm : m ≤ m₂) :
  sigma_integrable m₂ f μ :=
⟨⟨hf.spanning_sets,
  λ n, hm _ (hf.measurable_spanning_sets n),
  hf.integrable_on_spanning_sets,
  hf.Union_spanning_sets⟩⟩

lemma mono_measure (hf : sigma_integrable m f μ) (h_le : ν ≤ μ) :
  sigma_integrable m f ν :=
⟨⟨hf.spanning_sets,
  hf.measurable_spanning_sets,
  λ n, (hf.integrable_on_spanning_sets n).mono_measure h_le,
  hf.Union_spanning_sets⟩⟩

end sigma_integrable

lemma sigma_integrable_congr (hfg : f =ᵐ[μ] g) :
  sigma_integrable m f μ ↔ sigma_integrable m g μ :=
⟨λ hf, hf.congr_fun hfg, λ hg, hg.congr_fun hfg.symm⟩

/-- An integrable function is σ-integrable on any σ-algebra. -/
lemma integrable.sigma_integrable (hf : integrable f μ) (m : measurable_space α) :
  sigma_integrable m f μ :=
⟨{ set := λ n, univ,
  set_mem := λ n, measurable_set.univ,
  integrable_on := λ n, @integrable.integrable_on _ _ m0 _ _ _ _ hf,
  spanning := Union_const univ, }⟩

@[simp] lemma sigma_integrable_zero : sigma_integrable m (0 : α → E) μ :=
(integrable_zero _ _ _).sigma_integrable m

lemma sigma_integrable_const (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (c : E) :
  sigma_integrable m (λ _, c) μ :=
begin
  refine ⟨⟨spanning_sets (μ.trim hm), λ n, (measurable_spanning_sets (μ.trim hm) n), λ n, _,
    Union_spanning_sets (μ.trim hm)⟩⟩,
  rw [integrable_on, integrable_const_iff, measure.restrict_apply measurable_set.univ, univ_inter],
  exact or.inr ((le_trim hm).trans_lt (measure_spanning_sets_lt_top (μ.trim hm) n)),
end

lemma sigma_integrable_const_iff (hm : m ≤ m0) (c : E) (hc : c ≠ 0) :
  sigma_integrable m (λ _, c) μ ↔ sigma_finite (μ.trim hm) :=
begin
  split; intro h,
  { refine ⟨⟨{ set := h.spanning_sets,
      set_mem := λ _, mem_univ _,
      finite := λ i, _, -- this remains to be proven
      spanning := h.Union_spanning_sets, }⟩⟩,
    rw trim_measurable_set_eq hm (h.measurable_spanning_sets i),
    have h_int := h.integrable_on_spanning_sets i,
    rw integrable_on_const at h_int,
    cases h_int,
    { exact absurd h_int hc},
    { exact h_int, }, },
  { haveI := h,
    exact sigma_integrable_const hm c, },
end

lemma sigma_integrable_const' [sigma_finite μ] (c : E) : sigma_integrable m0 (λ x : α, c) μ :=
begin
  haveI : sigma_finite (μ.trim le_rfl),
  { rw trim_eq_self, apply_instance, },
  exact sigma_integrable_const le_rfl c,
end

lemma sigma_integrable_of_restrict_of_restrict_compl (hm : m ≤ m0) (hs_meas : measurable_set[m] s)
  (hs : sigma_integrable m f (μ.restrict s)) (hsc : sigma_integrable m f (μ.restrict sᶜ)) :
  sigma_integrable m f μ :=
begin
  let sets := hs.spanning_sets,
  let sets_compl := hsc.spanning_sets,
  refine ⟨⟨λ n, (s ∩ sets n) ∪ (sᶜ ∩ sets_compl n), λ n, _, λ n, _, _⟩⟩,
  { refine (hs_meas.inter _).union (hs_meas.compl.inter _),
    { exact hs.measurable_spanning_sets n, },
    { exact hsc.measurable_spanning_sets n, }, },
  { rw integrable_on_union,
    split,
    { have h_int_s := hs.integrable_on_spanning_sets n,
      rw [integrable_on, measure.restrict_restrict, inter_comm] at h_int_s,
      { exact h_int_s, },
      { exact hm _ (hs.measurable_spanning_sets n), }, },
    { have h_int_sc := hsc.integrable_on_spanning_sets n,
      rw [integrable_on, measure.restrict_restrict, inter_comm] at h_int_sc,
      { exact h_int_sc, },
      { exact hm _ (hsc.measurable_spanning_sets n), }, }, },
  { rw [Union_union_distrib, ← inter_Union, ← inter_Union, hs.Union_spanning_sets,
      hsc.Union_spanning_sets, inter_univ, inter_univ, union_compl_self], },
end

lemma sigma_integrable_of_trim (hm : m ≤ m0) (hf : sigma_integrable m f (μ.trim hm)) :
  sigma_integrable m f μ :=
begin
  refine ⟨⟨hf.spanning_sets, hf.measurable_spanning_sets, λ n, _, hf.Union_spanning_sets⟩⟩,
  refine integrable_of_integrable_trim hm _,
  rw ← restrict_trim hm _ (hf.measurable_spanning_sets n),
  exact hf.integrable_on_spanning_sets n,
end

namespace sigma_integrable

lemma add (hf : sigma_integrable m f μ) (hg : sigma_integrable m g μ) :
  sigma_integrable m (f + g) μ :=
begin
  let sf := hf.spanning_sets,
  let sg := hg.spanning_sets,
  refine ⟨⟨λ n, sf n ∩ sg n, _, _, _⟩⟩,
  { exact λ n, (hf.measurable_spanning_sets n).inter (hg.measurable_spanning_sets n), },
  { refine λ n, integrable.add _ _,
    { exact integrable_on.mono_set (hf.integrable_on_spanning_sets n) (inter_subset_left _ _), },
    { exact integrable_on.mono_set (hg.integrable_on_spanning_sets n) (inter_subset_right _ _), } },
  { have : (⋃ i, sf i ∩ sg i) = (⋃ i, sf i) ∩ (⋃ i, sg i),
    { ext1 x,
      simp only [mem_Union, mem_inter_eq],
      split,
      { rintros ⟨i, hfi, hgi⟩,
        exact ⟨⟨i, hfi⟩, ⟨i, hgi⟩⟩, },
      { rintros ⟨⟨i, hfi⟩, ⟨j, hgj⟩⟩,
        cases le_total i j with hi_le_j hj_le_i,
        { exact ⟨j, hf.monotone_spanning_sets hi_le_j hfi, hgj⟩, },
        { exact ⟨i, hfi, hg.monotone_spanning_sets hj_le_i hgj⟩, }, }, },
    rw [this, hf.Union_spanning_sets, hg.Union_spanning_sets, inter_univ], },
end

lemma neg (hf : sigma_integrable m f μ) : sigma_integrable m (-f) μ :=
⟨⟨hf.spanning_sets,
  hf.measurable_spanning_sets,
  λ n, (hf.integrable_on_spanning_sets n).neg,
  hf.Union_spanning_sets⟩⟩

lemma sub (hf : sigma_integrable m f μ) (hg : sigma_integrable m g μ) :
  sigma_integrable m (f - g) μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg, }

end sigma_integrable

/-- If the measure is σ-finite, a strongly measurable function is σ-integrable on the σ-algebra
on which the measure is defined. -/
lemma strongly_measurable.sigma_integrable [measurable_space E] [borel_space E]
  (hf : strongly_measurable f) [sigma_finite μ] :
  sigma_integrable m0 f μ :=
begin
  let sigma_finite_sets := spanning_sets μ,
  let norm_sets := λ (n : ℕ), {x | ∥f x∥ ≤ n},
  have norm_sets_spanning : (⋃ n, norm_sets n) = univ,
  { ext1 x, simp only [mem_Union, mem_set_of_eq, mem_univ, iff_true],
    exact ⟨⌈∥f x∥⌉₊, nat.le_ceil (∥f x∥)⟩, },
  have h_meas : ∀ n, measurable_set (sigma_finite_sets n ∩ norm_sets n),
  { intros n,
    refine measurable_set.inter _ _,
    { exact measurable_spanning_sets μ n, },
    { exact measurable_set_le hf.measurable.norm measurable_const, }, },
  refine ⟨⟨λ n, sigma_finite_sets n ∩ norm_sets n, h_meas, _, _⟩⟩,
  { intro n,
    have h_int : integrable_on (λ x, (n : ℝ)) (sigma_finite_sets n ∩ norm_sets n) μ,
    { rw integrable_on_const,
      right,
      exact (measure_mono (inter_subset_left _ _)).trans_lt
        (measure_spanning_sets_lt_top μ n), },
    refine integrable.mono' h_int _ _,
    { exact hf.ae_strongly_measurable.restrict, },
    { rw ae_restrict_iff' (h_meas n),
      refine eventually_of_forall (λ x hx, _),
      rw mem_inter_iff at hx,
      exact hx.2, }, },
  { have : (⋃ i, sigma_finite_sets i ∩ norm_sets i)
      = (⋃ i, sigma_finite_sets i) ∩ (⋃ i, norm_sets i),
    { refine Union_inter_of_monotone (monotone_spanning_sets μ) (λ i j hij x, _),
      simp only [norm_sets, mem_set_of_eq],
      refine λ hif, hif.trans _,
      exact_mod_cast hij, },
    rw [this, norm_sets_spanning, Union_spanning_sets μ, univ_inter _], },
end

/-- If the measure is σ-finite, an a.e. strongly measurable function is σ-integrable on the
σ-algebra on which the measure is defined. -/
lemma ae_strongly_measurable.sigma_integrable [measurable_space E] [borel_space E]
  [sigma_finite μ] (hf : ae_strongly_measurable f μ) :
  sigma_integrable m0 f μ :=
sigma_integrable.congr_fun hf.ae_eq_mk.symm hf.strongly_measurable_mk.sigma_integrable

lemma strongly_measurable.sigma_integrable' [measurable_space E] [borel_space E]
  (hm : m ≤ m0) [sigma_finite (μ.trim hm)] (hf : strongly_measurable[m] f) :
  sigma_integrable m f μ :=
sigma_integrable_of_trim hm (@strongly_measurable.sigma_integrable _ _ _ _ _ _ _ _ hf _)

lemma ae_fin_strongly_measurable.ae_strongly_measurable (hf : ae_fin_strongly_measurable f μ) :
  ae_strongly_measurable f μ :=
⟨hf.mk f, hf.fin_strongly_measurable_mk.strongly_measurable, hf.ae_eq_mk⟩

/-- An a.e. finitely strongly measurable function is σ-integrable on the σ-algebra
on which the measure is defined. -/
lemma ae_fin_strongly_measurable.sigma_integrable [measurable_space E] [borel_space E]
  (hf : ae_fin_strongly_measurable f μ) :
  sigma_integrable m0 f μ :=
begin
  let t := hf.sigma_finite_set,
  haveI : sigma_finite (μ.restrict t) := hf.sigma_finite_restrict,
  have : sigma_integrable m0 f (μ.restrict t),
  { exact @ae_strongly_measurable.sigma_integrable _ _ m0 (μ.restrict t)
      _ _ _ _ _ hf.ae_strongly_measurable.restrict, },
  refine sigma_integrable_of_restrict_of_restrict_compl le_rfl hf.measurable_set this _,
  exact sigma_integrable_zero.congr_fun hf.ae_eq_zero_compl.symm,
end

lemma strongly_measurable.is_bounded_bilinear_map {m : measurable_space α} [normed_space ℝ E]
  [normed_space ℝ F] {g : α → F}
  (hf : strongly_measurable f) (hg : strongly_measurable g) (B : E × F → ℝ)
  (hB : is_bounded_bilinear_map ℝ B) :
  strongly_measurable (λ x, B (f x, g x)) :=
begin
  refine ⟨λ n, simple_func.map B ((hf.approx n).pair (hg.approx n)), λ x, _⟩,
  have h_coe : ∀ n, simple_func.map B ((hf.approx n).pair (hg.approx n)) x
    = B (hf.approx n x, hg.approx n x),
  { intro n, rw [simple_func.coe_map, comp_app, simple_func.pair_apply], },
  simp_rw [h_coe],
  exact (hB.continuous.tendsto _).comp ((hf.tendsto_approx x).prod_mk_nhds (hg.tendsto_approx x)),
end

lemma strongly_measurable.continuous_bilinear_map {m : measurable_space α} [normed_space ℝ E]
  [normed_space ℝ F] {g : α → F}
  (hf : strongly_measurable f) (hg : strongly_measurable g) (B : E →L[ℝ] F →L[ℝ] ℝ) :
  strongly_measurable (λ x, B (f x) (g x)) :=
begin
  have h_is_bbm : is_bounded_bilinear_map ℝ (λ (p : E × F), B p.1 p.2),
    from B.is_bounded_bilinear_map,
  exact hf.is_bounded_bilinear_map hg (λ (p : E × F), B p.1 p.2) h_is_bbm,
end

lemma ae_strongly_measurable.is_bounded_bilinear_map [normed_space ℝ E]
  [normed_space ℝ F] {g : α → F}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (B : E × F → ℝ)
  (hB : is_bounded_bilinear_map ℝ B) :
  ae_strongly_measurable (λ x, B (f x, g x)) μ :=
begin
  refine ⟨λ x, B (hf.mk f x, hg.mk g x), _, _⟩,
  { exact hf.strongly_measurable_mk.is_bounded_bilinear_map hg.strongly_measurable_mk B hB, },
  { filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hxf hxg,
    rw [hxf, hxg], },
end

lemma ae_strongly_measurable.continuous_bilinear_map [normed_space ℝ E]
  [normed_space ℝ F] {g : α → F}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) (B : E →L[ℝ] F →L[ℝ] ℝ) :
  ae_strongly_measurable (λ x, B (f x) (g x)) μ :=
begin
  have h_is_bbm : is_bounded_bilinear_map ℝ (λ (p : E × F), B p.1 p.2),
    from B.is_bounded_bilinear_map,
  exact hf.is_bounded_bilinear_map hg (λ (p : E × F), B p.1 p.2) h_is_bbm,
end

lemma sigma_integrable.is_bounded_bilinear_map  [normed_space ℝ E]
  [measurable_space F] [borel_space F] [normed_space ℝ F] {g : α → F}
  (hm : m ≤ m0) (hf : sigma_integrable m f μ) (hg : strongly_measurable[m] g)
  (B : E × F → ℝ) (hB : is_bounded_bilinear_map ℝ B) :
  sigma_integrable m (λ x, B (f x, g x)) μ :=
begin
  let norm_sets := λ (n : ℕ), {x | ∥g x∥ ≤ n},
  have norm_sets_spanning : (⋃ n, norm_sets n) = univ,
  { ext1 x, simp only [mem_Union, mem_set_of_eq, mem_univ, iff_true],
    exact ⟨⌈∥g x∥⌉₊, nat.le_ceil (∥g x∥)⟩, },
  have h_meas : ∀ n, measurable_set[m] (hf.spanning_sets n ∩ norm_sets n),
  { intros n,
    refine measurable_set.inter _ _,
    { exact hf.measurable_spanning_sets n, },
    { refine @measurable_set_le _ _ _ _ _ m _ _ _ _ _ _ measurable_const,
      exact @measurable.norm _ _ _ _ _ m _ hg.measurable, }, },
  refine ⟨⟨λ n, hf.spanning_sets n ∩ norm_sets n, h_meas, λ n, _, _⟩⟩,
  { obtain ⟨C, hC, h_le_norm⟩ : ∃ C (hC : 0 < C),
      ∀ x ∈ hf.spanning_sets n ∩ norm_sets n, ∥B (f x, g x)∥ ≤ C * n * ∥f x∥,
    { obtain ⟨C, hC, h⟩ := hB.bound,
      refine ⟨C, hC, λ x hx, (h (f x) (g x)).trans _⟩,
      rw [mul_comm _ (∥g x∥), mul_comm _ ↑n, mul_assoc],
      exact mul_le_mul hx.2 le_rfl (mul_nonneg hC.lt.le (norm_nonneg _)) (nat.cast_nonneg _), },
    suffices : integrable_on (λ x, C * n * ∥f x∥) (hf.spanning_sets n ∩ norm_sets n) μ,
    { refine integrable.mono' this _ _,
      { exact ((hf.ae_strongly_measurable hm).is_bounded_bilinear_map
          (hg.mono hm).ae_strongly_measurable B hB).restrict },
      { rw ae_restrict_iff' (hm _ (h_meas n)),
        exact eventually_of_forall h_le_norm, }, },
    refine (integrable.norm _).const_mul (C * n),
    exact integrable_on.mono_set (hf.integrable_on_spanning_sets n) (inter_subset_left _ _), },
  { have : (⋃ i, hf.spanning_sets i ∩ norm_sets i)
      = (⋃ i, hf.spanning_sets i) ∩ (⋃ i, norm_sets i),
    { refine Union_inter_of_monotone hf.monotone_spanning_sets (λ i j hij x, _),
      simp only [norm_sets, mem_set_of_eq],
      refine λ hif, hif.trans _,
      exact_mod_cast hij, },
    rw [this, norm_sets_spanning, hf.Union_spanning_sets, univ_inter _], },
end

lemma sigma_integrable.continuous_bilinear_map  [normed_space ℝ E]
  [measurable_space F] [borel_space F] [normed_space ℝ F] {g : α → F}
  (hm : m ≤ m0) (hf : sigma_integrable m f μ) (hg : strongly_measurable[m] g)
  (B : E →L[ℝ] F →L[ℝ] ℝ) :
  sigma_integrable m (λ x, B (f x) (g x)) μ :=
begin
  have h_is_bbm : is_bounded_bilinear_map ℝ (λ (p : E × F), B p.1 p.2),
    from B.is_bounded_bilinear_map,
  exact hf.is_bounded_bilinear_map hm hg (λ (p : E × F), B p.1 p.2) h_is_bbm,
end

lemma integrable.sigma_integrable_is_bounded_bilinear_map [normed_space ℝ E]
  [measurable_space F] [borel_space F] [normed_space ℝ F] {g : α → F}
  (hm : m ≤ m0) (hf : integrable f μ) (hg : strongly_measurable[m] g) (B : E × F → ℝ)
    (hB : is_bounded_bilinear_map ℝ B) :
  sigma_integrable m (λ x, B (f x, g x)) μ :=
(hf.sigma_integrable m).is_bounded_bilinear_map hm hg B hB

lemma integrable.sigma_integrable_continuous_bilinear_map [normed_space ℝ E]
  [measurable_space F] [borel_space F] [normed_space ℝ F] {g : α → F}
  (hm : m ≤ m0) (hf : integrable f μ) (hg : strongly_measurable[m] g) (B : E →L[ℝ] F →L[ℝ] ℝ) :
  sigma_integrable m (λ x, B (f x) (g x)) μ :=
(hf.sigma_integrable m).continuous_bilinear_map hm hg B

lemma integrable.sigma_integrable_inner {E} [inner_product_space ℝ E] {f g : α → E}
  [measurable_space E] [borel_space E]
  (hm : m ≤ m0) (hf : integrable f μ) (hg : strongly_measurable[m] g) :
  sigma_integrable m (λ x, ⟪f x, g x⟫_ℝ) μ :=
begin
  have h_is_bbm : is_bounded_bilinear_map ℝ (λ (p : E × E), ⟪p.1, p.2⟫_ℝ),
    from @is_bounded_bilinear_map_inner ℝ E _ _ _,
  exact hf.sigma_integrable_is_bounded_bilinear_map hm hg _ h_is_bbm,
end

lemma integrable.sigma_integrable_mul {f g : α → ℝ}
  (hm : m ≤ m0) (hf : integrable f μ) (hg : strongly_measurable[m] g) :
  sigma_integrable m (λ x, f x * g x) μ :=
begin
  have h := hf.sigma_integrable_inner hm hg,
  simpa only [is_R_or_C.inner_apply, is_R_or_C.conj_to_real] using h,
end

/-- The space of σ-integrable functions. -/
def L1σ {α} (E : Type*) (m : measurable_space α) {m0 : measurable_space α} [normed_group E]
  (μ : measure α . volume_tac) : add_subgroup (α →ₘ[μ] E) :=
{ carrier := {f | sigma_integrable m f μ},
  zero_mem' := sigma_integrable_zero.congr_fun ae_eq_fun.coe_fn_zero.symm,
  add_mem' := λ f g hf hg, (hf.add hg).congr_fun (ae_eq_fun.coe_fn_add f g).symm,
  neg_mem' := λ f hf, hf.neg.congr_fun (ae_eq_fun.coe_fn_neg f).symm, }

localized "notation α ` →₁σ[`:25 μ `,` m `] ` E := measure_theory.L1σ E m μ" in measure_theory

lemma L1σ.sigma_integrable (f : α →₁σ[μ, m] E) :
  sigma_integrable m f μ :=
f.prop

end measure_theory
