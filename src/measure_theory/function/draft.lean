import measure_theory.function.conditional_expectation
import measure_theory.function.sigma_integrable

open filter set function
open_locale measure_theory nnreal ennreal classical big_operators

namespace measure_theory


variables {α E F : Type*} {m m₂ m0 : measurable_space α} {μ : measure α}
  [normed_group E] [normed_space ℝ E]
  [normed_group F] [normed_space ℝ F] [complete_space F]
  {T T' T'': set α → E →L[ℝ] F} {C C' C'' : ℝ} {f g : α → E} {p : ℝ≥0∞}

noncomputable
def Lp.indicator (f : Lp E p μ) (s : set α) (hs : measurable_set s) : Lp E p μ :=
mem_ℒp.to_Lp (s.indicator f) ((Lp.mem_ℒp f).indicator hs)

noncomputable
def L1.indicator (f : α →₁[μ] E) (s : set α) (hs : measurable_set s) : α →₁[μ] E :=
integrable.to_L1 (s.indicator f) ((L1.integrable_coe_fn f).indicator hs)

variables (μ T)

/-- Extend `T : set α → E →L[ℝ] F` to `(α →₁σ[μ, m] E) → F`. -/
noncomputable
def set_to_L1σ (hT : dominated_fin_meas_additive μ T C) (hm : m ≤ m0) (f : α →₁σ[μ, m] E) : F :=
let hf := L1σ.sigma_integrable f in
∑' n, L1.set_to_L1 hT (integrable.to_L1 ((hf.sets_aux n).indicator f)
  ((hf.integrable_on_sets_aux n).indicator (hm _ (hf.measurable_sets_aux n))))

variables {μ T}

lemma Lp.coe_fn_sum {ι} {s : finset ι} (fs : ι → Lp E p μ) :
  ⇑(∑ i in s, fs i) =ᵐ[μ] ∑ i in s, ⇑(fs i) :=
begin
  refine finset.induction_on s _ _,
  { simp only [finset.sum_empty, finset.sum_apply], exact Lp.coe_fn_zero _ _ _, },
  { intros a t ha_notin_t h,
    rw [finset.sum_insert ha_notin_t, finset.sum_insert ha_notin_t],
    exact (Lp.coe_fn_add _ _).trans (eventually_eq.rfl.add h), },
end

def L1_to_L1σ (f : α →₁[μ] E) (m : measurable_space α) : α →₁σ[μ, m] E :=
⟨f, (L1.integrable_coe_fn f).sigma_integrable m⟩

lemma set_to_L1σ_eq_set_to_L1 (hT : dominated_fin_meas_additive μ T C) (hm : m ≤ m0)
  (f : α →₁[μ] E) :
  set_to_L1σ μ T hT hm (L1_to_L1σ f m) = L1.set_to_L1 hT f :=
begin
  sorry,
end


end measure_theory
