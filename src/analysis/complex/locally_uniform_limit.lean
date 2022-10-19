/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import analysis.complex.removable_singularity
import analysis.calculus.uniform_limits_deriv

/-!
# Locally uniform limits of holomorphic functions

## Main results

* `tendsto_locally_uniformly_on.differentiable_on`: A locally uniform limit of holomorphic functions
  is holomorphic.
* `tendsto_locally_uniformly_on.deriv`: Locally uniform convergence implies locally uniform
  convergence of the derivatives to the derivative of the limit.
-/

open set metric measure_theory filter complex interval_integral
open_locale real topological_space

section cderiv

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
  {ι : Type*} {φ : filter ι} {U K : set ℂ} {z : ℂ} {f g : ℂ → E} {F : ι → ℂ → E} {M r δ : ℝ}

noncomputable def cderiv (r : ℝ) (f : ℂ → E) (z : ℂ) : E :=
  (2 * π * I : ℂ)⁻¹ • ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • f w

lemma norm_cderiv_le (hr : 0 < r) (hf : ∀ w ∈ sphere z r, ∥f w∥ ≤ M) :
  ∥cderiv r f z∥ ≤ M / r :=
begin
  have hM : 0 ≤ M,
  { obtain ⟨w, hw⟩ : ∃ w : ℂ, w ∈ sphere z r := normed_space.sphere_nonempty.mpr hr.le,
    exact (norm_nonneg _).trans (hf w hw) },
  have h1 : ∀ w ∈ sphere z r, ∥((w - z) ^ 2)⁻¹ • f w∥ ≤ M / r ^ 2,
  { intros w hw,
    simp only [mem_sphere_iff_norm, norm_eq_abs] at hw,
    simp only [norm_smul, inv_mul_eq_div, hw, norm_eq_abs, map_inv₀, complex.abs_pow],
    exact div_le_div hM (hf w hw) (sq_pos_of_pos hr) le_rfl },
  have h2 := circle_integral.norm_integral_le_of_norm_le_const hr.le h1,
  simp only [cderiv, norm_smul],
  refine (mul_le_mul le_rfl h2 (norm_nonneg _) (norm_nonneg _)).trans (le_of_eq _),
  field_simp [_root_.abs_of_nonneg real.pi_pos.le, real.pi_pos.ne.symm, hr.ne.symm],
  ring
end

lemma cderiv_eq_deriv (hU : is_open U) (hf : differentiable_on ℂ f U) (hr : 0 < r)
  (hzr : closed_ball z r ⊆ U) :
  cderiv r f z = deriv f z :=
two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable hU hzr hf (mem_ball_self hr)

lemma dist_cderiv_le (hr : 0 < r) (hzr : closed_ball z r ⊆ U)
  (hfg : ∀ w ∈ sphere z r, ∥f w - g w∥ < M)
  (hf : continuous_on f U) (hg : continuous_on g U) :
  dist (cderiv r f z) (cderiv r g z) < M / r :=
begin
  obtain ⟨L, hL1, hL2⟩ : ∃ L, L < M ∧ ∀ w ∈ sphere z r, ∥f w - g w∥ ≤ L,
  { have e0 : sphere z r ⊆ U := sphere_subset_closed_ball.trans hzr,
    have e1 : is_compact (sphere z r) := is_compact_sphere z r,
    have e2 : (sphere z r).nonempty := normed_space.sphere_nonempty.mpr hr.le,
    have e3 : continuous_on (λ w, ∥f w - g w∥) (sphere z r),
      from continuous_norm.comp_continuous_on ((hf.mono e0).sub (hg.mono e0)),
    obtain ⟨x, hx, hx'⟩ := is_compact.exists_forall_ge e1 e2 e3,
    refine ⟨∥f x - g x∥, hfg x hx, hx'⟩ },
  have h1 : L / r < M / r := (div_lt_div_right hr).mpr hL1,
  have h2 : continuous_on (λ (w : ℂ), ((w - z) ^ 2)⁻¹) (sphere z r),
  { refine ((continuous_id'.sub continuous_const).pow 2).continuous_on.inv₀ (λ w hw h, hr.ne _),
    simpa [sq_eq_zero_iff.mp h] using mem_sphere_iff_norm.mp hw },
  convert ← (norm_cderiv_le hr hL2).trans_lt h1 using 1,
  simp only [dist_eq_norm, cderiv, ← smul_sub],
  congr' 2,
  simp only [smul_sub],
  refine circle_integral.integral_sub _ _,
  { have e1 := (h2.smul (continuous_on.mono hf ((sphere_subset_closed_ball).trans hzr))),
    exact continuous_on.circle_integrable hr.le e1 },
  { have e1 := (h2.smul (continuous_on.mono hg ((sphere_subset_closed_ball).trans hzr))),
    exact continuous_on.circle_integrable hr.le e1 }
end

lemma tendsto_uniformly_on_cderiv (hU : is_open U) (hf : continuous_on f U) (hK2 : is_compact K)
  (hδ : 0 < δ) (hFn : ∀ n, continuous_on (F n) U) (hK3 : cthickening δ K ⊆ U)
  (hF : tendsto_uniformly_on F f φ (cthickening δ K)) :
  tendsto_uniformly_on (λ n, cderiv δ (F n)) (cderiv δ f) φ K :=
begin
  have hK1 : K ⊆ U := (self_subset_cthickening _).trans hK3,
  rw [tendsto_uniformly_on_iff] at hF ⊢,
  rintro ε hε,
  filter_upwards [hF (ε * δ) (mul_pos hε hδ)] with n h z hz,
  simp_rw [dist_eq_norm] at h,
  have h2 : ∀ w ∈ sphere z δ, ∥f w - F n w∥ < ε * δ,
    from λ w hw1, h w (closed_ball_subset_cthickening hz δ (sphere_subset_closed_ball hw1)),
  convert dist_cderiv_le hδ ((closed_ball_subset_cthickening hz δ).trans hK3) h2 hf (hFn n),
  field_simp [hδ.ne.symm]; ring
end

end cderiv

section deriv_limit

variables {𝕜 β ι : Type*} [is_R_or_C 𝕜] [normed_add_comm_group β] [normed_space 𝕜 β]
  {U : set 𝕜} {x : 𝕜} {F : ι → 𝕜 → β} {f g : 𝕜 → β} {φ : filter ι} [ne_bot φ]

lemma has_deriv_at_of_tendsto_localy_uniformly_on (hU : is_open U) (hx : x ∈ U)
  (hF : ∀ n, differentiable_on 𝕜 (F n) U) (hf : ∀ x ∈ U, tendsto (λ n, F n x) φ (𝓝 (f x)))
  (hg : tendsto_locally_uniformly_on (deriv ∘ F) g φ U) :
  has_deriv_at f (g x) x :=
begin
  have h1 : U ∈ 𝓝 x := hU.mem_nhds hx,
  have h2 : tendsto_uniformly_on_filter (deriv ∘ F) g φ (𝓝[U] x),
    from tendsto_locally_uniformly_on_iff_filter.mp hg x hx,
  rw [is_open.nhds_within_eq hU hx] at h2,
  have h3 : (univ ×ˢ U) ∈ φ.prod (𝓝 x) := by simp only [h1, prod_mem_prod_iff, univ_mem, and_self],
  have h4 : ∀ᶠ (n : ι × 𝕜) in φ.prod (𝓝 x), has_deriv_at (F n.1) (deriv (F n.1) n.2) n.2,
    from eventually_of_mem h3 (λ ⟨n, z⟩ ⟨hn, hz⟩, (hF n).has_deriv_at (hU.mem_nhds hz)),
  exact has_deriv_at_of_tendsto_uniformly_on_filter h2 h4 (eventually_of_mem h1 hf),
end

end deriv_limit

section weierstrass

variables {ι E : Type*} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
  {φ : filter ι} [ne_bot φ] {U K : set ℂ} (hU : is_open U) {F : ι → ℂ → E} {f g : ℂ → E}
  (hF : ∀ n, differentiable_on ℂ (F n) U) (hf : tendsto_locally_uniformly_on F f φ U)
include hU hF hf

lemma tendsto_uniformly_on_deriv_of_cthickening_subset {δ : ℝ} (hδ: 0 < δ) (hK : is_compact K)
  (hKU: cthickening δ K ⊆ U) :
  tendsto_uniformly_on (deriv ∘ F) (cderiv δ f) φ K :=
begin
  have h1 : ∀ n, continuous_on (F n) U := λ n, (hF n).continuous_on,
  have h2 : continuous_on f U := hf.continuous_on (eventually_of_forall h1),
  have h3 : is_compact (cthickening δ K),
    from is_compact_of_is_closed_bounded is_closed_cthickening hK.bounded.cthickening,
  have h4 : tendsto_uniformly_on F f φ (cthickening δ K),
    from (tendsto_locally_uniformly_on_iff_forall_compact hU).mp hf (cthickening δ K) hKU h3,
  have h5 : tendsto_uniformly_on (cderiv δ ∘ F) (cderiv δ f) φ K,
    from tendsto_uniformly_on_cderiv hU h2 hK hδ h1 hKU h4,
  refine h5.congr (eventually_of_forall (λ n z hz, _)),
  exact cderiv_eq_deriv hU (hF n) hδ ((closed_ball_subset_cthickening hz δ).trans hKU)
end

lemma exists_cthickening_tendsto_uniformly_on (hK : is_compact K) (hKU : K ⊆ U) :
  ∃ δ > 0, cthickening δ K ⊆ U ∧ tendsto_uniformly_on (deriv ∘ F) (cderiv δ f) φ K :=
begin
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU,
  exact ⟨δ, hδ, hKδ, tendsto_uniformly_on_deriv_of_cthickening_subset hU hF hf hδ hK hKδ⟩
end

lemma tendsto_locally_uniformly_on.differentiable_on : differentiable_on ℂ f U :=
begin
  rintro x hx,
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx),
  obtain ⟨δ, hδ, -, h1⟩ := exists_cthickening_tendsto_uniformly_on hU hF hf hK hKU,
  have h2 : interior K ⊆ U := interior_subset.trans hKU,
  have h3 : ∀ n, differentiable_on ℂ (F n) (interior K) := λ n, (hF n).mono h2,
  have h4 : tendsto_locally_uniformly_on F f φ (interior K) := hf.mono h2,
  have h5 : tendsto_locally_uniformly_on (deriv ∘ F) (cderiv δ f) φ (interior K),
    from h1.tendsto_locally_uniformly_on.mono interior_subset,
  have h6 : ∀ x ∈ interior K, has_deriv_at f (cderiv δ f x) x,
    from λ x h, has_deriv_at_of_tendsto_localy_uniformly_on is_open_interior h h3 h4.tendsto_at h5,
  have h7 : differentiable_on ℂ f (interior K),
    from λ x hx, (h6 x hx).differentiable_at.differentiable_within_at,
  exact (h7.differentiable_at (interior_mem_nhds.mpr hKx)).differentiable_within_at
end

lemma tendsto_locally_uniformly_on.deriv :
  tendsto_locally_uniformly_on (deriv ∘ F) (deriv f) φ U :=
begin
  refine (tendsto_locally_uniformly_on_iff_forall_compact hU).mpr (λ K hKU hK, _),
  obtain ⟨δ, hδ, hK4, h⟩ := exists_cthickening_tendsto_uniformly_on hU hF hf hK hKU,
  refine h.congr' (λ z hz, _),
  refine cderiv_eq_deriv hU _ hδ ((closed_ball_subset_cthickening hz δ).trans hK4),
  exact hf.differentiable_on hU hF
end

end weierstrass
