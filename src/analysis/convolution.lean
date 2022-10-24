/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.group.integration
import measure_theory.group.prod
import measure_theory.function.locally_integrable
import analysis.calculus.specific_functions
import analysis.calculus.parametric_integral
import measure_theory.measure.haar_lebesgue

/-!
# Convolution of functions

This file defines the convolution on two functions, i.e. `x ↦ ∫ f(t)g(x - t) ∂t`.
In the general case, these functions can be vector-valued, and have an arbitrary (additive)
group as domain. We use a continuous bilinear operation `L` on these function values as
"multiplication". The domain must be equipped with a Haar measure `μ`
(though many individual results have weaker conditions on `μ`).

For many applications we can take `L = lsmul ℝ ℝ` or `L = mul ℝ ℝ`.

We also define `convolution_exists` and `convolution_exists_at` to state that the convolution is
well-defined (everywhere or at a single point). These conditions are needed for pointwise
computations (e.g. `convolution_exists_at.distrib_add`), but are generally not stong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

# Design Decisions

We use a bilinear map `L` to "multiply" the two functions in the integrand.
This generality has several advantages

* This allows us to compute the total derivative of the convolution, in case the functions are
  multivariate. The total derivative is again a convolution, but where the codomains of the
  functions can be higher-dimensional. See `has_compact_support.has_fderiv_at_convolution_right`.
* This allows us to use `@[to_additive]` everywhere (which would not be possible if we would use
  `mul`/`smul` in the integral, since `@[to_additive]` will incorrectly also try to additivize
  those definitions).
* We need to support the case where at least one of the functions is vector-valued, but if we use
  `smul` to multiply the functions, that would be an asymmetric definition.

# Main Definitions
* `convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ` is the convolution of
  `f` and `g` w.r.t. the continuous bilinear map `L` and measure `μ`.
* `convolution_exists_at f g x L μ` states that the convolution `(f ⋆[L, μ] g) x` is well-defined
  (i.e. the integral exists).
* `convolution_exists f g L μ` states that the convolution `f ⋆[L, μ] g` is well-defined at each
  point.

# Main Results
* `has_compact_support.has_fderiv_at_convolution_right` and
  `has_compact_support.has_fderiv_at_convolution_left`: we can compute the total derivative
  of the convolution as a convolution with the total derivative of the right (left) function.
* `has_compact_support.cont_diff_convolution_right` and
  `has_compact_support.cont_diff_convolution_left`: the convolution is `𝒞ⁿ` if one of the functions
  is `𝒞ⁿ` with compact support and the other function in locally integrable.
* `convolution_tendsto_right`: Given a sequence of nonnegative normalized functions whose support
  tends to a small neighborhood around `0`, the convolution tends to the right argument.
  This is specialized to bump functions in `cont_diff_bump_of_inner.convolution_tendsto_right`.

# Notation
The following notations are localized in the locale `convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

# To do
* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere
-/

open set function filter measure_theory measure_theory.measure topological_space
open continuous_linear_map metric
open_locale pointwise topological_space nnreal filter

variables {𝕜 G E E' E'' F F' F'' : Type*}
variables [normed_add_comm_group E] [normed_add_comm_group E'] [normed_add_comm_group E'']
  [normed_add_comm_group F] {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

section nontrivially_normed_field

variables [nontrivially_normed_field 𝕜]
variables [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E''] [normed_space 𝕜 F]
variables (L : E →L[𝕜] E' →L[𝕜] F)

section no_measurability

variables [add_group G] [topological_space G]

lemma has_compact_support.convolution_integrand_bound_right (hcg : has_compact_support g)
  (hg : continuous g) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥L (f t) (g (x - t))∥ ≤ (- tsupport g + s).indicator (λ t, ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥)) t :=
begin
  refine le_indicator (λ t ht, _) (λ t ht, _) t,
  { refine (L.le_op_norm₂ _ _).trans _,
    exact mul_le_mul_of_nonneg_left
        (le_csupr (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) $ x - t)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) },
  { have : x - t ∉ support g,
    { refine mt (λ hxt, _) ht, refine ⟨_, _, set.neg_mem_neg.mpr (subset_closure hxt), hx, _⟩,
      rw [neg_sub, sub_add_cancel] },
    rw [nmem_support.mp this, (L _).map_zero, norm_zero] }
end

lemma continuous.convolution_integrand_fst [has_continuous_sub G] (hg : continuous g) (t : G) :
  continuous (λ x, L (f t) (g (x - t))) :=
L.continuous₂.comp₂ continuous_const $ hg.comp $ continuous_id.sub continuous_const

lemma has_compact_support.convolution_integrand_bound_left (hcf : has_compact_support f)
  (hf : continuous f) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥L (f (x - t)) (g t)∥ ≤ (- tsupport f + s).indicator (λ t, ∥L∥ * (⨆ i, ∥f i∥) * ∥g t∥) t :=
by { convert hcf.convolution_integrand_bound_right L.flip hf hx,
  simp_rw [L.op_norm_flip, mul_right_comm] }

end no_measurability

section measurability

variables [measurable_space G] {μ : measure G}

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x - t))` is
integrable. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists_at [has_sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
integrable (λ t, L (f t) (g (x - t))) μ

/-- The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x - t))` is integrable
for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists [has_sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
∀ x : G, convolution_exists_at f g x L μ

section convolution_exists

variables {L}
lemma convolution_exists_at.integrable [has_sub G] {x : G} (h : convolution_exists_at f g x L μ) :
  integrable (λ t, L (f t) (g (x - t))) μ :=
h

variables (L)

section group

variables [add_group G]
variables [has_measurable_add₂ G] [has_measurable_neg G]

lemma measure_theory.ae_strongly_measurable.convolution_integrand' [sigma_finite μ]
  (hf : ae_strongly_measurable f μ)
  (hg : ae_strongly_measurable g $ map (λ (p : G × G), p.1 - p.2) (μ.prod μ)) :
  ae_strongly_measurable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
L.ae_strongly_measurable_comp₂ hf.snd $ hg.comp_measurable $ measurable_fst.sub measurable_snd

lemma measure_theory.ae_strongly_measurable.convolution_integrand_snd'
  (hf : ae_strongly_measurable f μ) {x : G}
  (hg : ae_strongly_measurable g $ map (λ t, x - t) μ) :
  ae_strongly_measurable (λ t, L (f t) (g (x - t))) μ :=
L.ae_strongly_measurable_comp₂ hf $ hg.comp_measurable $ measurable_id.const_sub x

lemma measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd'
  {x : G} (hf : ae_strongly_measurable f $ map (λ t, x - t) μ)
  (hg : ae_strongly_measurable g μ) : ae_strongly_measurable (λ t, L (f (x - t)) (g t)) μ :=
L.ae_strongly_measurable_comp₂ (hf.comp_measurable $ measurable_id.const_sub x) hg

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

Note: we could weaken the measurability condition to hold only for `μ.restrict s`. -/
lemma bdd_above.convolution_exists_at' {x₀ : G}
  {s : set G} (hbg : bdd_above ((λ i, ∥g i∥) '' ((λ t, - t + x₀) ⁻¹' s)))
  (hs : measurable_set s) (h2s : support (λ t, L (f t) (g (x₀ - t))) ⊆ s)
  (hf : integrable_on f s μ)
  (hmf : ae_strongly_measurable f μ)
  (hmg : ae_strongly_measurable g $ map (λ t, x₀ - t) μ) :
    convolution_exists_at f g x₀ L μ :=
begin
  set s' := (λ t, - t + x₀) ⁻¹' s,
  have : ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x₀ - t))∥ ≤ s.indicator (λ t, ∥L∥ * ∥f t∥ * ⨆ i : s', ∥g i∥) t,
  { refine eventually_of_forall _,
    refine le_indicator (λ t ht, _) (λ t ht, _),
    { refine (L.le_op_norm₂ _ _).trans _,
      refine mul_le_mul_of_nonneg_left
        (le_csupr_set hbg $ mem_preimage.mpr _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      rwa [neg_sub, sub_add_cancel] },
    { have : t ∉ support (λ t, L (f t) (g (x₀ - t))) := mt (λ h, h2s h) ht,
      rw [nmem_support.mp this, norm_zero] } },
  refine integrable.mono' _ _ this,
  { rw [integrable_indicator_iff hs], exact (hf.norm.const_mul _).mul_const _ },
  { exact hmf.convolution_integrand_snd' L hmg }
end

section left
variables [sigma_finite μ] [is_add_left_invariant μ]

lemma measure_theory.ae_strongly_measurable.convolution_integrand_snd
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
  (x : G) : ae_strongly_measurable (λ t, L (f t) (g (x - t))) μ :=
hf.convolution_integrand_snd' L $ hg.mono' $
  (quasi_measure_preserving_sub_left μ x).absolutely_continuous

lemma measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
  (x : G) : ae_strongly_measurable (λ t, L (f (x - t)) (g t)) μ :=
(hf.mono' (quasi_measure_preserving_sub_left μ x).absolutely_continuous)
  .convolution_integrand_swap_snd' L hg

end left

section right

variables [sigma_finite μ] [is_add_right_invariant μ]

lemma measure_theory.ae_strongly_measurable.convolution_integrand
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
hf.convolution_integrand' L $ hg.mono'
  (quasi_measure_preserving_sub_of_right_invariant μ μ).absolutely_continuous

lemma measure_theory.integrable.convolution_integrand (hf : integrable f μ) (hg : integrable g μ) :
  integrable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
begin
  have h_meas : ae_strongly_measurable (λ (p : G × G), L (f p.2) (g (p.1 - p.2))) (μ.prod μ) :=
    hf.ae_strongly_measurable.convolution_integrand L hg.ae_strongly_measurable,
  have h2_meas : ae_strongly_measurable (λ (y : G), ∫ (x : G), ∥L (f y) (g (x - y))∥ ∂μ) μ :=
    h_meas.prod_swap.norm.integral_prod_right',
  simp_rw [integrable_prod_iff' h_meas],
  refine ⟨eventually_of_forall (λ t, (L (f t)).integrable_comp (hg.comp_sub_right t)), _⟩,
  refine integrable.mono' _ h2_meas (eventually_of_forall $
    λ t, (_ : _ ≤ ∥L∥ * ∥f t∥ * ∫ x, ∥g (x - t)∥ ∂μ)),
  { simp_rw [integral_sub_right_eq_self (λ t, ∥ g t ∥)],
    exact (hf.norm.const_mul _).mul_const _ },
  { simp_rw [← integral_mul_left],
    rw [real.norm_of_nonneg],
    { exact integral_mono_of_nonneg (eventually_of_forall $ λ t, norm_nonneg _)
        ((hg.comp_sub_right t).norm.const_mul _) (eventually_of_forall $ λ t, L.le_op_norm₂ _ _) },
    exact integral_nonneg (λ x, norm_nonneg _) }
end

lemma measure_theory.integrable.ae_convolution_exists (hf : integrable f μ) (hg : integrable g μ) :
  ∀ᵐ x ∂μ, convolution_exists_at f g x L μ :=
((integrable_prod_iff $ hf.ae_strongly_measurable.convolution_integrand L
  hg.ae_strongly_measurable).mp $ hf.convolution_integrand L hg).1

end right

variables [topological_space G] [topological_add_group G] [borel_space G]
  [second_countable_topology G] [sigma_compact_space G]

lemma has_compact_support.convolution_exists_at {x₀ : G}
  (h : has_compact_support (λ t, L (f t) (g (x₀ - t)))) (hf : locally_integrable f μ)
  (hg : continuous g) : convolution_exists_at f g x₀ L μ :=
((((homeomorph.neg G).trans $ homeomorph.add_right x₀).compact_preimage.mpr h).bdd_above_image
  hg.norm.continuous_on).convolution_exists_at' L is_closed_closure.measurable_set subset_closure
  (hf h) hf.ae_strongly_measurable hg.ae_strongly_measurable

lemma has_compact_support.convolution_exists_right
  (hcg : has_compact_support g) (hf : locally_integrable f μ) (hg : continuous g) :
  convolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.convolution_exists_at L _ hf hg,
  refine (hcg.comp_homeomorph (homeomorph.sub_left x₀)).mono _,
  refine λ t, mt (λ ht : g (x₀ - t) = 0, _),
  simp_rw [ht, (L _).map_zero]
end

lemma has_compact_support.convolution_exists_left_of_continuous_right
  (hcf : has_compact_support f) (hf : locally_integrable f μ) (hg : continuous g) :
  convolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.convolution_exists_at L _ hf hg,
  refine hcf.mono _,
  refine λ t, mt (λ ht : f t = 0, _),
  simp_rw [ht, L.map_zero₂]
end

end group

section comm_group

variables [add_comm_group G]

section measurable_group

variables [has_measurable_add₂ G] [has_measurable_neg G] [is_add_left_invariant μ]

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

This is a variant of `bdd_above.convolution_exists_at'` in an abelian group with a left-invariant
measure. This allows us to state the boundedness and measurability of `g` in a more natural way. -/
lemma bdd_above.convolution_exists_at [sigma_finite μ] {x₀ : G}
  {s : set G} (hbg : bdd_above ((λ i, ∥g i∥) '' ((λ t, x₀ - t) ⁻¹' s)))
  (hs : measurable_set s) (h2s : support (λ t, L (f t) (g (x₀ - t))) ⊆ s)
  (hf : integrable_on f s μ)
  (hmf : ae_strongly_measurable f μ)
  (hmg : ae_strongly_measurable g μ) :
    convolution_exists_at f g x₀ L μ :=
begin
  refine bdd_above.convolution_exists_at' L _ hs h2s hf hmf _,
  { simp_rw [← sub_eq_neg_add, hbg] },
  { exact hmg.mono' (quasi_measure_preserving_sub_left μ x₀).absolutely_continuous }
end

variables {L} [is_neg_invariant μ]

lemma convolution_exists_at_flip :
  convolution_exists_at g f x L.flip μ ↔ convolution_exists_at f g x L μ :=
by simp_rw [convolution_exists_at, ← integrable_comp_sub_left (λ t, L (f t) (g (x - t))) x,
  sub_sub_cancel, flip_apply]

lemma convolution_exists_at.integrable_swap (h : convolution_exists_at f g x L μ) :
  integrable (λ t, L (f (x - t)) (g t)) μ :=
by { convert h.comp_sub_left x, simp_rw [sub_sub_self] }

lemma convolution_exists_at_iff_integrable_swap :
  convolution_exists_at f g x L μ ↔ integrable (λ t, L (f (x - t)) (g t)) μ :=
convolution_exists_at_flip.symm

end measurable_group

variables [topological_space G] [topological_add_group G] [borel_space G]
  [second_countable_topology G] [is_add_left_invariant μ] [is_neg_invariant μ]
  [sigma_compact_space G]

lemma has_compact_support.convolution_exists_left
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
  convolution_exists f g L μ :=
λ x₀, convolution_exists_at_flip.mp $ hcf.convolution_exists_right L.flip hg hf x₀

lemma has_compact_support.convolution_exists_right_of_continuous_left
  (hcg : has_compact_support g) (hf : continuous f) (hg : locally_integrable g μ) :
  convolution_exists f g L μ :=
λ x₀, convolution_exists_at_flip.mp $
  hcg.convolution_exists_left_of_continuous_right L.flip hg hf x₀

end comm_group

end convolution_exists

variables [normed_space ℝ F] [complete_space F]

/-- The convolution of two functions `f` and `g` with respect to a continuous bilinear map `L` and
measure `μ`. It is defined to be `(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`. -/
noncomputable def convolution [has_sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : G → F :=
λ x, ∫ t, L (f t) (g (x - t)) ∂μ

localized "notation (name := convolution) f ` ⋆[`:67 L:67 `, ` μ:67 `] `:0 g:66 :=
  convolution f g L μ" in convolution
localized "notation (name := convolution.volume) f ` ⋆[`:67 L:67 `]`:0 g:66 :=
  convolution f g L measure_theory.measure_space.volume" in convolution
localized "notation (name := convolution.lsmul) f ` ⋆ `:67 g:66 :=
  convolution f g (continuous_linear_map.lsmul ℝ ℝ) measure_theory.measure_space.volume"
  in convolution

lemma convolution_def [has_sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ := rfl

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
lemma convolution_lsmul [has_sub G] {f : G → 𝕜} {g : G → F} :
  (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ := rfl

/-- The definition of convolution where the bilinear operator is multiplication. -/
lemma convolution_mul [has_sub G] [normed_space ℝ 𝕜] [complete_space 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
  (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ := rfl

section group

variables {L} [add_group G]

lemma smul_convolution [smul_comm_class ℝ 𝕜 F]
  {y : 𝕜} : (y • f) ⋆[L, μ] g = y • (f ⋆[L, μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂] }

lemma convolution_smul [smul_comm_class ℝ 𝕜 F]
  {y : 𝕜} : f ⋆[L, μ] (y • g) = y • (f ⋆[L, μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul] }

lemma zero_convolution : 0 ⋆[L, μ] g = 0 :=
by { ext, simp_rw [convolution_def, pi.zero_apply, L.map_zero₂, integral_zero] }

lemma convolution_zero : f ⋆[L, μ] 0 = 0 :=
by { ext, simp_rw [convolution_def, pi.zero_apply, (L _).map_zero, integral_zero] }

lemma convolution_exists_at.distrib_add {x : G} (hfg : convolution_exists_at f g x L μ)
  (hfg' : convolution_exists_at f g' x L μ) :
  (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x :=
by simp only [convolution_def, (L _).map_add, pi.add_apply, integral_add hfg hfg']

lemma convolution_exists.distrib_add (hfg : convolution_exists f g L μ)
  (hfg' : convolution_exists f g' L μ) : f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' :=
by { ext, exact (hfg x).distrib_add (hfg' x) }

lemma convolution_exists_at.add_distrib {x : G} (hfg : convolution_exists_at f g x L μ)
  (hfg' : convolution_exists_at f' g x L μ) :
  ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x :=
by simp only [convolution_def, L.map_add₂, pi.add_apply, integral_add hfg hfg']

lemma convolution_exists.add_distrib (hfg : convolution_exists f g L μ)
  (hfg' : convolution_exists f' g L μ) : (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g :=
by { ext, exact (hfg x).add_distrib (hfg' x) }

variables (L)

lemma convolution_congr [has_measurable_add G] [has_measurable_neg G] [is_add_left_invariant μ]
  [is_neg_invariant μ] (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') :
  f ⋆[L, μ] g = f' ⋆[L, μ] g' :=
begin
  ext x,
  apply integral_congr_ae,
  exact (h1.prod_mk $ h2.comp_tendsto (map_sub_left_ae μ x).le).fun_comp ↿(λ x y, L x y)
end

lemma support_convolution_subset_swap : support (f ⋆[L, μ] g) ⊆ support g + support f :=
begin
  intros x h2x,
  by_contra hx,
  apply h2x,
  simp_rw [set.mem_add, not_exists, not_and_distrib, nmem_support] at hx,
  rw [convolution_def],
  convert integral_zero G F,
  ext t,
  rcases hx (x - t) t with h|h|h,
  { rw [h, (L _).map_zero] },
  { rw [h, L.map_zero₂] },
  { exact (h $ sub_add_cancel x t).elim }
end

section
variables [has_measurable_add₂ G] [has_measurable_neg G] [sigma_finite μ] [is_add_right_invariant μ]

lemma measure_theory.integrable.integrable_convolution (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⋆[L, μ] g) μ :=
(hf.convolution_integrand L hg).integral_prod_left

end

variables [topological_space G]
variables [topological_add_group G]

lemma has_compact_support.convolution [t2_space G] (hcf : has_compact_support f)
  (hcg : has_compact_support g) : has_compact_support (f ⋆[L, μ] g) :=
compact_of_is_closed_subset (hcg.is_compact.add hcf) is_closed_closure $ closure_minimal
  ((support_convolution_subset_swap L).trans $ add_subset_add subset_closure subset_closure)
  (hcg.is_compact.add hcf).is_closed

variables [borel_space G] [second_countable_topology G]

/-- The convolution is continuous if one function is locally integrable and the other has compact
support and is continuous. -/
lemma has_compact_support.continuous_convolution_right [locally_compact_space G] [t2_space G]
  (hcg : has_compact_support g) (hf : locally_integrable f μ)
  (hg : continuous g) : continuous (f ⋆[L, μ] g) :=
begin
  refine continuous_iff_continuous_at.mpr (λ x₀, _),
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x₀,
  let K' := - tsupport g + K,
  have hK' : is_compact K' := hcg.neg.add hK,
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x - t))∥ ≤ K'.indicator (λ t, ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥)) t :=
  eventually_of_mem h2K (λ x hx, eventually_of_forall $
    λ t, hcg.convolution_integrand_bound_right L hg hx),
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall
      (λ x, hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable) },
  { rw [integrable_indicator_iff hK'.measurable_set],
    exact ((hf hK').norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t, (L.continuous₂.comp₂ continuous_const $
      hg.comp $ continuous_id.sub $ by apply continuous_const).continuous_at) }
end

/-- The convolution is continuous if one function is integrable and the other is bounded and
continuous. -/
lemma bdd_above.continuous_convolution_right_of_integrable
  (hbg : bdd_above (range (λ x, ∥g x∥))) (hf : integrable f μ) (hg : continuous g) :
    continuous (f ⋆[L, μ] g) :=
begin
  refine continuous_iff_continuous_at.mpr (λ x₀, _),
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x - t))∥ ≤ ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥),
  { refine eventually_of_forall (λ x, eventually_of_forall $ λ t, _),
    refine (L.le_op_norm₂ _ _).trans _,
    exact mul_le_mul_of_nonneg_left (le_csupr hbg $ x - t)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) },
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall
      (λ x, hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable) },
  { exact (hf.norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t, (L.continuous₂.comp₂ continuous_const $
      hg.comp $ continuous_id.sub $ by apply continuous_const).continuous_at) }
end

/-- A version of `has_compact_support.continuous_convolution_right` that works if `G` is
not locally compact but requires that `g` is integrable. -/
lemma has_compact_support.continuous_convolution_right_of_integrable
  (hcg : has_compact_support g) (hf : integrable f μ) (hg : continuous g) :
    continuous (f ⋆[L, μ] g) :=
(hg.norm.bdd_above_range_of_has_compact_support hcg.norm).continuous_convolution_right_of_integrable
  L hf hg

end group

section comm_group

variables [add_comm_group G]

lemma support_convolution_subset : support (f ⋆[L, μ] g) ⊆ support f + support g :=
(support_convolution_subset_swap L).trans (add_comm _ _).subset

variables [is_add_left_invariant μ] [is_neg_invariant μ]

section measurable
variables [has_measurable_neg G]
variables [has_measurable_add G]

variable (L)
/-- Commutativity of convolution -/
lemma convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g :=
begin
  ext1 x,
  simp_rw [convolution_def],
  rw [← integral_sub_left_eq_self _ μ x],
  simp_rw [sub_sub_self, flip_apply]
end

/-- The symmetric definition of convolution. -/
lemma convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ :=
by { rw [← convolution_flip], refl }

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
lemma convolution_lsmul_swap {f : G → 𝕜} {g : G → F}:
  (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x - t) • g t ∂μ :=
convolution_eq_swap _

/-- The symmetric definition of convolution where the bilinear operator is multiplication. -/
lemma convolution_mul_swap [normed_space ℝ 𝕜] [complete_space 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
  (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) * g t ∂μ :=
convolution_eq_swap _

lemma convolution_neg_of_neg_eq (h1 : ∀ᵐ x ∂μ, f (-x) = f x) (h2 : ∀ᵐ x ∂μ, g (-x) = g x) :
  (f ⋆[L, μ] g) (-x) = (f ⋆[L, μ] g) x :=
calc ∫ (t : G), (L (f t)) (g (-x - t)) ∂μ
    = ∫ (t : G), (L (f (-t))) (g (x + t)) ∂μ :
  begin
    apply integral_congr_ae,
    filter_upwards [h1, (eventually_add_left_iff μ x).2 h2] with t ht h't,
    simp_rw [ht, ← h't, neg_add'],
  end
... = ∫ (t : G), (L (f t)) (g (x - t)) ∂μ :
  by { rw ← integral_neg_eq_self, simp only [neg_neg, ← sub_eq_add_neg] }

end measurable

variables [topological_space G]
variables [topological_add_group G]
variables [borel_space G]
variables [second_countable_topology G]

lemma has_compact_support.continuous_convolution_left [locally_compact_space G] [t2_space G]
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
    continuous (f ⋆[L, μ] g) :=
by { rw [← convolution_flip], exact hcf.continuous_convolution_right L.flip hg hf }

lemma bdd_above.continuous_convolution_left_of_integrable
  (hbf : bdd_above (range (λ x, ∥f x∥))) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[L, μ] g) :=
by { rw [← convolution_flip], exact hbf.continuous_convolution_right_of_integrable L.flip hg hf }

/-- A version of `has_compact_support.continuous_convolution_left` that works if `G` is
not locally compact but requires that `g` is integrable. -/
lemma has_compact_support.continuous_convolution_left_of_integrable
  (hcf : has_compact_support f) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[L, μ] g) :=
by { rw [← convolution_flip], exact hcf.continuous_convolution_right_of_integrable L.flip hg hf }

end comm_group

section normed_add_comm_group

variables [seminormed_add_comm_group G]

/-- Compute `(f ⋆ g) x₀` if the support of the `f` is within `metric.ball 0 R`, and `g` is constant
on `metric.ball x₀ R`.

We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)` or more
generally if `L` has a `antilipschitz_with`-condition. -/
lemma convolution_eq_right' {x₀ : G} {R : ℝ}
  (hf : support f ⊆ ball (0 : G) R)
  (hg : ∀ x ∈ ball x₀ R, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ t, L (f t) (g x₀) ∂μ :=
begin
  have h2 : ∀ t, L (f t) (g (x₀ - t)) = L (f t) (g x₀),
  { intro t, by_cases ht : t ∈ support f,
    { have h2t := hf ht,
      rw [mem_ball_zero_iff] at h2t,
      specialize hg (x₀ - t),
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg,
      rw [hg h2t] },
    { rw [nmem_support] at ht,
      simp_rw [ht, L.map_zero₂] } },
  simp_rw [convolution_def, h2],
end

variables [borel_space G] [second_countable_topology G]
variables [is_add_left_invariant μ] [sigma_finite μ]

/-- Approximate `(f ⋆ g) x₀` if the support of the `f` is bounded within a ball, and `g` is near
`g x₀` on a ball with the same radius around `x₀`. See `dist_convolution_le` for a special case.

We can simplify the second argument of `dist` further if we add some extra type-classes on `E`
and `𝕜` or if `L` is scalar multiplication. -/
lemma dist_convolution_le' {x₀ : G} {R ε : ℝ} {z₀ : E'}
  (hε : 0 ≤ ε)
  (hif : integrable f μ)
  (hf : support f ⊆ ball (0 : G) R)
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
  dist ((f ⋆[L, μ] g : G → F) x₀) (∫ t, L (f t) z₀ ∂μ) ≤ ∥L∥ * ∫ x, ∥f x∥ ∂μ * ε :=
begin
  have hfg : convolution_exists_at f g x₀ L μ,
  { refine bdd_above.convolution_exists_at L _ metric.is_open_ball.measurable_set
    (subset_trans _ hf) hif.integrable_on hif.ae_strongly_measurable hmg,
    swap, { refine λ t, mt (λ ht : f t = 0, _), simp_rw [ht, L.map_zero₂] },
    rw [bdd_above_def],
    refine ⟨∥z₀∥ + ε, _⟩,
    rintro _ ⟨x, hx, rfl⟩,
    refine norm_le_norm_add_const_of_dist_le (hg x _),
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff] },
  have h2 : ∀ t, dist (L (f t) (g (x₀ - t))) (L (f t) z₀) ≤ ∥L (f t)∥ * ε,
  { intro t, by_cases ht : t ∈ support f,
    { have h2t := hf ht,
      rw [mem_ball_zero_iff] at h2t,
      specialize hg (x₀ - t),
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg,
      refine ((L (f t)).dist_le_op_norm _ _).trans _,
      exact mul_le_mul_of_nonneg_left (hg h2t) (norm_nonneg _) },
    { rw [nmem_support] at ht,
      simp_rw [ht, L.map_zero₂, L.map_zero, norm_zero, zero_mul, dist_self] } },
  simp_rw [convolution_def],
  simp_rw [dist_eq_norm] at h2 ⊢,
  rw [← integral_sub hfg.integrable], swap, { exact (L.flip z₀).integrable_comp hif },
  refine (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε)
    (eventually_of_forall h2)).trans _,
  rw [integral_mul_right],
  refine mul_le_mul_of_nonneg_right _ hε,
  have h3 : ∀ t, ∥L (f t)∥ ≤ ∥L∥ * ∥f t∥,
  { intros t,
    exact L.le_op_norm (f t) },
  refine (integral_mono (L.integrable_comp hif).norm (hif.norm.const_mul _) h3).trans_eq _,
  rw [integral_mul_left]
end

variables [normed_space ℝ E] [normed_space ℝ E'] [complete_space E']

/-- Approximate `f ⋆ g` if the support of the `f` is bounded within a ball, and `g` is near `g x₀`
on a ball with the same radius around `x₀`.

This is a special case of `dist_convolution_le'` where `L` is `(•)`, `f` has integral 1 and `f` is
nonnegative. -/
lemma dist_convolution_le {f : G → ℝ} {x₀ : G} {R ε : ℝ} {z₀ : E'}
  (hε : 0 ≤ ε)
  (hf : support f ⊆ ball (0 : G) R)
  (hnf : ∀ x, 0 ≤ f x)
  (hintf : ∫ x, f x ∂μ = 1)
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
  dist ((f ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) z₀ ≤ ε :=
begin
  have hif : integrable f μ,
  { by_contra hif, exact zero_ne_one ((integral_undef hif).symm.trans hintf) },
  convert (dist_convolution_le' _ hε hif hf hmg hg).trans _,
  { simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul] },
  { simp_rw [real.norm_of_nonneg (hnf _), hintf, mul_one],
    exact (mul_le_mul_of_nonneg_right op_norm_lsmul_le hε).trans_eq (one_mul ε) }
end

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of nonnegative functions with integral `1` as `i` tends to `l`;
* The support of `φ` tends to small neighborhoods around `(0 : G)` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ᶠ 𝓝 x₀`;
* `k i` tends to `x₀`.

See also `cont_diff_bump_of_inner.convolution_tendsto_right`.
-/
lemma convolution_tendsto_right
  {ι} {g : ι → G → E'} {l : filter ι} {x₀ : G} {z₀ : E'}
  {φ : ι → G → ℝ} {k : ι → G}
  (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x)
  (hiφ : ∀ᶠ i in l, ∫ x, φ i x ∂μ = 1) -- todo: we could weaken this to "the integral tends to 1"
  (hφ : tendsto (λ n, support (φ n)) l (𝓝 0).small_sets)
  (hmg : ∀ᶠ i in l, ae_strongly_measurable (g i) μ)
  (hcg : tendsto (uncurry g) (l ×ᶠ 𝓝 x₀) (𝓝 z₀))
  (hk : tendsto k l (𝓝 x₀)) :
  tendsto (λ i : ι, (φ i ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) :=
begin
  simp_rw [tendsto_small_sets_iff] at hφ,
  rw [metric.tendsto_nhds] at hcg ⊢,
  simp_rw [metric.eventually_prod_nhds_iff] at hcg,
  intros ε hε,
  have h2ε : 0 < ε / 3 := div_pos hε (by norm_num),
  obtain ⟨p, hp, δ, hδ, hgδ⟩ := hcg _ h2ε,
  dsimp only [uncurry] at hgδ,
  have h2k := hk.eventually (ball_mem_nhds x₀ $ half_pos hδ),
  have h2φ := (hφ (ball (0 : G) _) $ ball_mem_nhds _ (half_pos hδ)),
  filter_upwards [hp, h2k, h2φ, hnφ, hiφ, hmg] with i hpi hki hφi hnφi hiφi hmgi,
  have hgi : dist (g i (k i)) z₀ < ε / 3 := hgδ hpi (hki.trans $ half_lt_self hδ),
  have h1 : ∀ x' ∈ ball (k i) (δ / 2), dist (g i x') (g i (k i)) ≤ ε / 3 + ε / 3,
  { intros x' hx',
    refine (dist_triangle_right _ _ _).trans (add_le_add (hgδ hpi _).le hgi.le),
    exact ((dist_triangle _ _ _).trans_lt (add_lt_add hx'.out hki)).trans_eq (add_halves δ) },
  have := dist_convolution_le (add_pos h2ε h2ε).le hφi hnφi hiφi hmgi h1,
  refine ((dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt this hgi)).trans_eq _,
  field_simp, ring_nf
end

end normed_add_comm_group

section

open finite_dimensional

variables {H : Type*} [normed_add_comm_group H] [normed_space ℝ H] [finite_dimensional ℝ H]

lemma support_comp_inv_smul (f : H → ℝ) {R : ℝ} (hR : R ≠ 0) :
  support (λ x, f (R⁻¹ • x)) = R • support f :=
by { ext x, simp only [mem_smul_set_iff_inv_smul_mem₀ hR, mem_support] }

lemma has_compact_mul_support.comp_smul {α : Type*} [has_one α] {f : H → α}
  (h : has_compact_mul_support f) {R : ℝ} (hR : R ≠ 0) :
  has_compact_mul_support (λ x, f (R • x)) :=
h.comp_homeomorph (homeomorph.smul_of_ne_zero R hR)

lemma has_compact_support.comp_smul {α : Type*} [has_zero α] {f : H → α}
  (h : has_compact_support f) {R : ℝ} (hR : R ≠ 0) :
  has_compact_support (λ x, f (R • x)) :=
h.comp_homeomorph (homeomorph.smul_of_ne_zero R hR)


lemma closed_ball_subset_ball' {α : Type*} [metric_space α] {ε₁ ε₂ : ℝ} {x y : α}
  (h : ε₁ + dist x y < ε₂) :
  closed_ball x ε₁ ⊆ ball y ε₂ :=
λ z hz, calc
  dist z y ≤ dist z x + dist x y : dist_triangle _ _ _
  ... ≤ ε₁ + dist x y : add_le_add_right hz _
  ... < ε₂ : h


variable (H)
lemma foo : ∃ g : H → ℝ, cont_diff ℝ ⊤ g ∧
  (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧ (support g = ball 0 1) ∧ (∀ x, g (-x) = g x) ∧
  (has_compact_support g) :=
sorry

set_option profiler true

def e : cont_diff_bump_base H :=
begin
  borelize H,
  let μ : measure H := measure_theory.measure.add_haar,
  choose g g_smooth g_mem g_support g_symm comp_supp_g using foo H,
  have g_cont : continuous g := g_smooth.continuous,
  set φ : H → ℝ := (closed_ball (0 : H) 1).indicator (λ y, 1) with hφ,
  set c := ∫ x, g x ∂μ with hc,
  have cpos : 0 < c,
  { refine (integral_pos_iff_support_of_nonneg (λ x, (g_mem x).1) _).mpr _,
    { exact g_cont.integrable_of_has_compact_support comp_supp_g },
    { rw g_support, exact measure_ball_pos _ _ zero_lt_one } },
  set F : ℝ → H → ℝ := λ R x, (c * R^(finrank ℝ H))⁻¹ • g (R⁻¹ • x) with F_def,
  set g0 : ℝ → H → ℝ := λ R, (F R) ⋆[lsmul ℝ ℝ, μ] φ with g0_def,
  have Hpos : ∀ R x y, 0 < R → 0 ≤ F R y * φ (x - y),
  sorry, /-{ assume R x y Rpos,
    have : 0 ≤ g (R⁻¹ • y), from (g_mem _).1,
    have : 0 ≤ φ (x - y),
      from indicator_nonneg (by simp only [zero_le_one, implies_true_iff]) _,
    rw F_def,
    dsimp,
    positivity }, -/
  have Fsupp : ∀ R, 0 < R → support (F R) = ball (0 : H) R,
  sorry, /- { assume R Rpos,
    have B : R • ball (0 : H) 1 = ball 0 R,
        by rw [smul_unit_ball Rpos.ne', real.norm_of_nonneg Rpos.le],
    have C : R ^ finrank ℝ H ≠ 0, from pow_ne_zero _ Rpos.ne',
    simp only [F_def, algebra.id.smul_eq_mul, support_mul, support_inv, univ_inter,
      support_comp_inv_smul _ Rpos.ne', g_support, B, support_const cpos.ne', support_const C] }, -/
  have : ∀ R x, g0 R (-x) = g0 R x,
  sorry, /-{ assume R x,
    apply convolution_neg_of_neg_eq,
    { apply eventually_of_forall (λ x, _),
      simp only [F_def, g_symm, smul_neg, algebra.id.smul_eq_mul, mul_eq_mul_left_iff,
        eq_self_iff_true, true_or], },
    { apply eventually_of_forall (λ x, _),
      simp only [φ, indicator, mem_closed_ball_zero_iff, norm_neg] } }, -/
  have : ∀ R (x : H), 0 < R → R < 1 → x ∈ closed_ball (0 : H) (1 - R) → g0 R x = 1,
  sorry, /-{ assume R x Rpos Rone hx,
    change ((F R) ⋆[lsmul ℝ ℝ, μ] φ) x = 1,
    have B : ∀ y ∈ ball x R, φ y = 1,
    { have C : ball x R ⊆ ball 0 1,
      { apply ball_subset_ball',
        simp only [mem_closed_ball] at hx,
        linarith only [hx] },
      assume y hy,
      simp only [hφ, indicator, mem_closed_ball, ite_eq_left_iff, not_le, zero_ne_one],
      assume h'y,
      linarith only [mem_ball.1 (C hy), h'y] },
    have Bx : φ x = 1, from B _ (mem_ball_self Rpos),
    have B' : ∀ y ∈ ball x R, φ y = φ x, by { rw Bx, exact B },
    rw convolution_eq_right' _ (le_of_eq (Fsupp R Rpos)) B',
    simp only [continuous_linear_map.map_smul, mul_inv_rev, coe_smul', pi.smul_apply, lsmul_apply,
      algebra.id.smul_eq_mul, integral_mul_left, integral_mul_right],
    rw [integral_comp_inv_smul_of_pos μ _ Rpos, ← hc, Bx, mul_one, smul_eq_mul],
    field_simp [Rpos.ne', cpos.ne'] }, -/
  have : ∀ R (x : H), 0 < R → R < 1 → x ∉ ball (0 : H) (1 + R) → g0 R x = 0,
  sorry, /-{ assume R x Rpos Rone hx,
    change (F R ⋆[lsmul ℝ ℝ, μ] φ) x = 0,
    have B : ∀ y ∈ ball x R, φ y = 0,
    { assume y hy,
      simp only [φ, indicator, mem_closed_ball_zero_iff, ite_eq_right_iff, one_ne_zero],
      assume h'y,
      have C : ball y R ⊆ ball 0 (1+R),
      { apply ball_subset_ball',
        rw ← dist_zero_right at h'y,
        linarith only [h'y] },
      exact hx (C (mem_ball_comm.1 hy)) },
    have Bx : φ x = 0, from B _ (mem_ball_self Rpos),
    have B' : ∀ y ∈ ball x R, φ y = φ x, by { rw Bx, exact B },
    rw convolution_eq_right' _ (le_of_eq (Fsupp R Rpos)) B',
    simp only [lsmul_apply, algebra.id.smul_eq_mul, Bx, mul_zero, integral_const] },-/
  have : ∀ R (x : H), 0 < R → 0 ≤ g0 R x,
    from λ R x Rpos, integral_nonneg (λ y, Hpos R x y Rpos),
  have : ∀ R (x : H), 0 < R → g0 R x ≤ 1,
  sorry, /- { assume R x Rpos,
    have C : (F R ⋆[lsmul ℝ ℝ, μ] φ) x ≤ (F R ⋆[lsmul ℝ ℝ, μ] 1) x,
    { apply integral_mono_of_nonneg (eventually_of_forall (λ y, Hpos R x y Rpos)),
      { refine (has_compact_support.convolution_exists_left _ _ _ _ _).integrable,
        { exact (comp_supp_g.comp_smul (inv_ne_zero Rpos.ne')).mul_left },
        { exact continuous_const.mul (g_smooth.continuous.comp (continuous_id.const_smul _)) },
        { apply locally_integrable_const (1 : ℝ), apply_instance } },
      { apply eventually_of_forall (λ y, _),
        simp only [continuous_linear_map.map_smul, mul_inv_rev, coe_smul', pi.smul_apply,
          lsmul_apply, algebra.id.smul_eq_mul, pi.one_apply, mul_one, F_def],
        refine mul_le_of_le_one_right (mul_nonneg (by positivity) (g_mem _).1) _,
        apply indicator_le_self' (λ x hx, zero_le_one),
        apply_instance } },
    have D : (F R ⋆[lsmul ℝ ℝ, μ] (λ y, (1 : ℝ))) x = 1,
    { simp only [convolution, continuous_linear_map.map_smul, mul_inv_rev, coe_smul', pi.smul_apply,
        lsmul_apply, algebra.id.smul_eq_mul, mul_one, integral_mul_left],
      rw [integral_comp_inv_smul_of_pos μ _ Rpos, ← hc, smul_eq_mul],
      field_simp [Rpos.ne', cpos.ne'] },
    exact C.trans (le_of_eq D) }, -/
  have : ∀ R (x : H), 0 < R → R < 1 → x ∈ ball (0 : H) (1 + R) → 0 < g0 R x,
  sorry, /-{ assume R x Rpos Rone hx,
    simp only [mem_ball_zero_iff] at hx,
    refine (integral_pos_iff_support_of_nonneg (λ y, Hpos R x y Rpos) _).2 _,
    { have F_comp : has_compact_support (F R),
      { rw [has_compact_support_def, Fsupp R Rpos, closure_ball (0 : H) Rpos.ne'],
        exact is_compact_closed_ball _ _ },
      have B : locally_integrable φ μ,
        from (locally_integrable_const _).indicator measurable_set_closed_ball,
      have C : continuous (F R),
        from (continuous.comp g_cont (continuous_id'.const_smul R⁻¹)).const_smul _,
      exact (has_compact_support.convolution_exists_left (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
        F_comp C B x).integrable },
    { set z := (R / (1 + R)) • x with hz,
      have B : 0 < 1 + R, by linarith,
      have C : ball z (R * (1 + R- ∥x∥) / (1 + R)) ⊆ support (λ (y : H), F R y * φ (x - y)),
      { assume y hy,
        simp only [support_mul, Fsupp R Rpos],
        simp only [mem_inter_iff, mem_support, ne.def, indicator_apply_eq_zero,
          mem_closed_ball_zero_iff, one_ne_zero, not_forall, not_false_iff, exists_prop, and_true],
        split,
        { apply ball_subset_ball' _ hy,
          simp only [z, norm_smul, abs_of_nonneg Rpos.le, abs_of_nonneg B.le, dist_zero_right,
            real.norm_eq_abs, abs_div],
          simp only [div_le_iff B] with field_simps,
          ring_nf },
        { have IR : ∥R / (1 + R) - 1∥ = 1 / (1 + R),
          { rw real.norm_of_nonpos,
            { simp only [B.ne', ne.def, not_false_iff, mul_one, neg_sub, add_tsub_cancel_right]
                with field_simps},
            { simp only [B.ne', ne.def, not_false_iff, mul_one] with field_simps,
              apply div_nonpos_of_nonpos_of_nonneg _ B.le,
              linarith only, } },
          rw ← mem_closed_ball_iff_norm',
          apply closed_ball_subset_closed_ball' _ (ball_subset_closed_ball hy),
          rw [← one_smul ℝ x, dist_eq_norm, hz, ← sub_smul, one_smul, norm_smul, IR],
          simp only [-one_div, -mul_eq_zero, B.ne', div_le_iff B] with field_simps,
          simp only [mem_ball_zero_iff] at hx,
          nlinarith only [hx, Rone] } },
      apply lt_of_lt_of_le _ (measure_mono C),
      apply measure_ball_pos,
      exact div_pos (mul_pos Rpos (by linarith only [hx])) B } },-/
  refine
  { to_fun := g0,
    mem_Icc := _,
    symmetric := _,
    smooth := _,
    eq_one := _,
    support := _},
end

instance {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E] :
  nonempty (cont_diff_bump_base E) := sorry



end

#exit

convolution_eq_right' {x₀ : G} {R : ℝ}
  (hf : support f ⊆ ball (0 : G) R)
  (hg : ∀ x ∈ ball x₀ R, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ t, L (f t) (g x₀) ∂μ :=

namespace cont_diff_bump

variables {n : ℕ∞}
variables [normed_space ℝ E']
variables [normed_add_comm_group G] [normed_space ℝ G] [nonempty (cont_diff_bump_base G)]
variables [complete_space E']
variables {a : G} {φ : cont_diff_bump (0 : G)}

/-- If `φ` is a bump function, compute `(φ ⋆ g) x₀` if `g` is constant on `metric.ball x₀ φ.R`. -/
lemma convolution_eq_right {x₀ : G}
  (hg : ∀ x ∈ ball x₀ φ.R, g x = g x₀) : (φ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = integral μ φ • g x₀ :=
by simp_rw [convolution_eq_right' _ φ.support_subset_ball hg, lsmul_apply, integral_smul_const]

variables [borel_space G]
variables [is_locally_finite_measure μ] [is_open_pos_measure μ]
variables [finite_dimensional ℝ G]

/-- If `φ` is a normed bump function, compute `φ ⋆ g` if `g` is constant on `metric.ball x₀ φ.R`. -/
lemma normed_convolution_eq_right {x₀ : G}
  (hg : ∀ x ∈ ball x₀ φ.R, g x = g x₀) : (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ :=
by { simp_rw [convolution_eq_right' _ φ.support_normed_subset_ball hg, lsmul_apply],
  exact integral_normed_smul φ μ (g x₀) }

variables [is_add_left_invariant μ]

/-- If `φ` is a normed bump function, approximate `(φ ⋆ g) x₀` if `g` is near `g x₀` on a ball with
radius `φ.R` around `x₀`. -/
lemma dist_normed_convolution_le {x₀ : G} {ε : ℝ}
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ φ.R, dist (g x) (g x₀) ≤ ε) :
  dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.R_pos)])
  φ.support_normed_subset_ball φ.nonneg_normed φ.integral_normed hmg hg

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of normed bump functions such that `(φ i).R` tends to `0` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ᶠ 𝓝 x₀`;
* `k i` tends to `x₀`. -/
lemma convolution_tendsto_right {ι} {φ : ι → cont_diff_bump (0 : G)}
  {g : ι → G → E'} {k : ι → G} {x₀ : G} {z₀ : E'} {l : filter ι}
  (hφ : tendsto (λ i, (φ i).R) l (𝓝 0))
  (hig : ∀ᶠ i in l, ae_strongly_measurable (g i) μ)
  (hcg : tendsto (uncurry g) (l ×ᶠ 𝓝 x₀) (𝓝 z₀))
  (hk : tendsto k l (𝓝 x₀)) :
  tendsto (λ i, ((λ x, (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) :=
convolution_tendsto_right (eventually_of_forall $ λ i, (φ i).nonneg_normed)
  (eventually_of_forall $ λ i, (φ i).integral_normed)
  (tendsto_support_normed_small_sets hφ) hig hcg hk

/-- Special case of `cont_diff_bump_of_inner.convolution_tendsto_right` where `g` is continuous,
  and the limit is taken only in the first function. -/
lemma convolution_tendsto_right_of_continuous {ι} {φ : ι → cont_diff_bump (0 : G)}
  {l : filter ι} (hφ : tendsto (λ i, (φ i).R) l (𝓝 0))
  (hg : continuous g) (x₀ : G) :
  tendsto (λ i, ((λ x, (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
convolution_tendsto_right hφ (eventually_of_forall $ λ _, hg.ae_strongly_measurable)
  ((hg.tendsto x₀).comp tendsto_snd) tendsto_const_nhds

end cont_diff_bump

end measurability

end nontrivially_normed_field

open_locale convolution


section is_R_or_C

variables [is_R_or_C 𝕜]
variables [normed_space 𝕜 E]
variables [normed_space 𝕜 E']
variables [normed_space 𝕜 E'']
variables [normed_space ℝ F] [normed_space 𝕜 F]
variables {n : ℕ∞}
variables [complete_space F]
variables [measurable_space G] {μ : measure G}
variables (L : E →L[𝕜] E' →L[𝕜] F)

section assoc
variables [normed_add_comm_group F'] [normed_space ℝ F'] [normed_space 𝕜 F'] [complete_space F']
variables [normed_add_comm_group F''] [normed_space ℝ F''] [normed_space 𝕜 F''] [complete_space F'']
variables {k : G → E''}
variables (L₂ : F →L[𝕜] E'' →L[𝕜] F')
variables (L₃ : E →L[𝕜] F'' →L[𝕜] F')
variables (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')
variables [add_group G]
variables [sigma_finite μ]

lemma integral_convolution
  [has_measurable_add₂ G] [has_measurable_neg G] [is_add_right_invariant μ]
  [normed_space ℝ E] [normed_space ℝ E']
  [complete_space E] [complete_space E']
  (hf : integrable f μ) (hg : integrable g μ) :
  ∫ x, (f ⋆[L, μ] g) x ∂μ = L (∫ x, f x ∂μ) (∫ x, g x ∂μ) :=
begin
  refine (integral_integral_swap (by apply hf.convolution_integrand L hg)).trans _,
  simp_rw [integral_comp_comm _ (hg.comp_sub_right _), integral_sub_right_eq_self],
  exact (L.flip (∫ x, g x ∂μ)).integral_comp_comm hf,
end

variables [has_measurable_add G] {ν : measure G} [sigma_finite ν] [is_add_right_invariant ν]


/-- Convolution is associative.
To do: prove that `hi` follows from simpler conditions. -/
lemma convolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z))
  {x₀ : G}
  (h₄ : convolution_exists g k L₄ ν)
  (h₁ : convolution_exists f g L μ)
  (hi : integrable (uncurry (λ x y, (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x))))) (ν.prod μ)) :
  ((f ⋆[L, μ] g) ⋆[L₂, ν] k) x₀ = (f ⋆[L₃, μ] (g ⋆[L₄, ν] k)) x₀ :=
begin
  have h1 := λ t, (L₂.flip (k (x₀ - t))).integral_comp_comm (h₁ t),
  dsimp only [flip_apply] at h1,
  simp_rw [convolution_def, ← (L₃ (f _)).integral_comp_comm (h₄ (x₀ - _)), ← h1, hL],
  rw [integral_integral_swap hi],
  congr', ext t,
  rw [eq_comm, ← integral_sub_right_eq_self _ t],
  { simp_rw [sub_sub_sub_cancel_right] },
  { apply_instance },
end

end assoc

variables [normed_add_comm_group G] [borel_space G]
variables [second_countable_topology G] [sigma_compact_space G]

lemma convolution_precompR_apply {g : G → E'' →L[𝕜] E'}
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : continuous g)
  (x₀ : G) (x : E'') : (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] (λ a, g a x)) x₀  :=
begin
  have := hcg.convolution_exists_right (L.precompR E'') hf hg x₀,
  simp_rw [convolution_def, continuous_linear_map.integral_apply this],
  refl,
end

variables [sigma_finite μ] [is_add_left_invariant μ]
variables [normed_space 𝕜 G] [proper_space G]

/-- Compute the total derivative of `f ⋆ g` if `g` is `C^1` with compact support and `f` is locally
integrable. To write down the total derivative as a convolution, we use
`continuous_linear_map.precompR`. -/
lemma has_compact_support.has_fderiv_at_convolution_right
  (hcg : has_compact_support g) (hf : locally_integrable f μ) (hg : cont_diff 𝕜 1 g) (x₀ : G) :
  has_fderiv_at (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀ :=
begin
  set L' := L.precompR G,
  have h1 : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (λ t, L (f t) (g (x - t))) μ :=
  eventually_of_forall
    (hf.ae_strongly_measurable.convolution_integrand_snd L hg.continuous.ae_strongly_measurable),
  have h2 : ∀ x, ae_strongly_measurable (λ t, L' (f t) (fderiv 𝕜 g (x - t))) μ,
  { exact hf.ae_strongly_measurable.convolution_integrand_snd L'
      (hg.continuous_fderiv le_rfl).ae_strongly_measurable },
  have h3 : ∀ x t, has_fderiv_at (λ x, g (x - t)) (fderiv 𝕜 g (x - t)) x,
  { intros x t,
    simpa using (hg.differentiable le_rfl).differentiable_at.has_fderiv_at.comp x
      ((has_fderiv_at_id x).sub (has_fderiv_at_const t x)) },
  let K' := - tsupport (fderiv 𝕜 g) + closed_ball x₀ 1,
  have hK' : is_compact K' := (hcg.fderiv 𝕜).neg.add (is_compact_closed_ball x₀ 1),
  refine has_fderiv_at_integral_of_dominated_of_fderiv_le
    zero_lt_one h1 _ (h2 x₀) _ _ _,
  { exact K'.indicator (λ t, ∥L'∥ * ∥f t∥ * (⨆ x, ∥fderiv 𝕜 g x∥)) },
  { exact hcg.convolution_exists_right L hf hg.continuous x₀ },
  { refine eventually_of_forall (λ t x hx, _),
    exact (hcg.fderiv 𝕜).convolution_integrand_bound_right L'
      (hg.continuous_fderiv le_rfl) (ball_subset_closed_ball hx) },
  { rw [integrable_indicator_iff hK'.measurable_set],
    exact ((hf hK').norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t x hx, (L _).has_fderiv_at.comp x (h3 x t)) },
end

lemma has_compact_support.has_fderiv_at_convolution_left [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 1 f) (hg : locally_integrable g μ) (x₀ : G) :
  has_fderiv_at (f ⋆[L, μ] g) ((fderiv 𝕜 f ⋆[L.precompL G, μ] g) x₀) x₀ :=
begin
  simp only [← convolution_flip] {single_pass := tt},
  exact hcf.has_fderiv_at_convolution_right L.flip hg hf x₀,
end

lemma has_compact_support.cont_diff_convolution_right [finite_dimensional 𝕜 G]
  (hcg : has_compact_support g) (hf : locally_integrable f μ) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (f ⋆[L, μ] g) :=
begin
  induction n using enat.nat_induction with n ih ih generalizing g,
  { rw [cont_diff_zero] at hg ⊢,
    exact hcg.continuous_convolution_right L hf hg },
  { have h : ∀ x, has_fderiv_at (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x) x :=
      hcg.has_fderiv_at_convolution_right L hf hg.one_of_succ,
    rw cont_diff_succ_iff_fderiv_apply,
    split,
    { exact λ x₀, ⟨_, h x₀⟩ },
    { simp_rw [fderiv_eq h, convolution_precompR_apply L hf (hcg.fderiv 𝕜)
        (hg.one_of_succ.continuous_fderiv le_rfl)],
      intro x,
      refine ih _ _,
      { refine @has_compact_support.comp_left _ _ _ _ _ _ (λ (G : _ →L[𝕜] _), G x) _
          (hcg.fderiv 𝕜) (continuous_linear_map.zero_apply x) },
      { revert x, rw [← cont_diff_clm_apply],
        exact (cont_diff_succ_iff_fderiv.mp hg).2 } } },
  { rw [cont_diff_top] at hg ⊢, exact λ n, ih n hcg (hg n) }
end

lemma has_compact_support.cont_diff_convolution_left [finite_dimensional 𝕜 G] [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 n f) (hg : locally_integrable g μ) :
  cont_diff 𝕜 n (f ⋆[L, μ] g) :=
by { rw [← convolution_flip], exact hcf.cont_diff_convolution_right L.flip hg hf }

end is_R_or_C

section real
/-! The one-variable case -/

variables [is_R_or_C 𝕜]
variables [normed_space 𝕜 E]
variables [normed_space 𝕜 E']
variables [normed_space ℝ F] [normed_space 𝕜 F]
variables {f₀ : 𝕜 → E} {g₀ : 𝕜 → E'}
variables {n : ℕ∞}
variables (L : E →L[𝕜] E' →L[𝕜] F)
variables [complete_space F]
variables {μ : measure 𝕜}
variables [is_add_left_invariant μ] [sigma_finite μ]

lemma has_compact_support.has_deriv_at_convolution_right
  (hf : locally_integrable f₀ μ) (hcg : has_compact_support g₀) (hg : cont_diff 𝕜 1 g₀)
  (x₀ : 𝕜) :
  has_deriv_at (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀ :=
begin
  convert (hcg.has_fderiv_at_convolution_right L hf hg x₀).has_deriv_at,
  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv le_rfl)],
  refl,
end

lemma has_compact_support.has_deriv_at_convolution_left [is_neg_invariant μ]
  (hcf : has_compact_support f₀) (hf : cont_diff 𝕜 1 f₀)
  (hg : locally_integrable g₀ μ) (x₀ : 𝕜) :
  has_deriv_at (f₀ ⋆[L, μ] g₀) ((deriv f₀ ⋆[L, μ] g₀) x₀) x₀ :=
begin
  simp only [← convolution_flip] {single_pass := tt},
  exact hcf.has_deriv_at_convolution_right L.flip hg hf x₀,
end

end real
