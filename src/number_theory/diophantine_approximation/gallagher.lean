/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import analysis.normed.group.add_circle
import measure_theory.covering.density_theorem
import measure_theory.measure.haar
import order.liminf_limsup

/-!
# Gallagher's Theorem on Diophantine Approximation

Explain result and sketch proof in [Approximation by reduced fractions](Gallagher1961).

-/

noncomputable theory

open set filter function metric measure_theory measure_theory.measure_space
open_locale nnreal ennreal topological_space

/- On reflection it might be better not to have unions of balls in this lemma (i.e., for `z` to be
just a sequence of points in `α`) and push the complexity of the unions elsewhere (e.g., into
`volume_well_approximable_eq_zero_or_one`).

TODO Decide and tidy up this mess once sorry-free. (The remaining `sorry`s are all easy.) -/
lemma measure_inf_often_eq
  {α : Type*} [metric_space α] [proper_space α] [measurable_space α] [borel_space α]
  (μ : measure α) [is_locally_finite_measure μ] [is_doubling_measure μ]
  {ρ : ℝ≥0} (hρ : 1 < ρ)
  {r : ℕ → ℝ} (hr₀ : ∀ j, 0 < r j) (hr₁ : tendsto r at_top (𝓝 0))
  (z : ℕ → finset α)
  (p : ℕ → Prop) :
  μ (cofinite.blimsup p $ λ k, ⋃ (w ∈ z k), closed_ball w (r k)) =
  μ (cofinite.blimsup p $ λ k, ⋃ (w ∈ z k), closed_ball w $ ρ * r k) :=
begin
  let U := λ k, ⋃ (w ∈ z k), closed_ball w (r k),
  let I := λ k, ⋃ (w ∈ z k), closed_ball w $ ρ * r k,
  have hUI' : ∀ n, U n ≤ I n,
  { intros n x hx,
    simp only [mem_Union, exists_prop] at hx ⊢,
    obtain ⟨w, hw₁, hw₂⟩ := hx,
    refine ⟨w, hw₁, closed_ball_subset_closed_ball _ hw₂⟩,
    exact le_mul_of_one_le_left (hr₀ n).le hρ.le, },
  let 𝓘 : set α := cofinite.blimsup p I,
  let 𝓤 : ℕ → set α := λ k, ⋃ (l : ℕ) (hl₁ : k ≤ l) (hl₂ : p l), U l,
  let 𝓓 : ℕ → set α := λ k, 𝓘 \ 𝓤 k,
  have h𝓓₀ : ∀ k, 𝓓 k ≤ 𝓘 := λ k, sdiff_le,
  have hUI : cofinite.blimsup p U ≤ 𝓘 := mono_blimsup hUI',
  have h𝓓 : 𝓘 \ cofinite.blimsup p U = ⋃ k, 𝓓 k,
  {
    -- have : (⋃ k, (𝓘 \ 𝓤 k)) ≤ 𝓘 := Union_subset (λ k, @sdiff_le _ 𝓘 (𝓤 k) _),
    -- apply eq_of_sdiff_eq_sdiff sdiff_le this,
    -- rw [sdiff_sdiff_eq_self hUI, sdiff_eq, compl_Union],
    -- simp_rw [sdiff_eq, compl_inf, compl_compl],
    -- change inf_often p U = 𝓘 ∩ ⋂ k, 𝓘ᶜ ∪ 𝓤 k,
    -- rw [← union_Inter, inter_union_distrib_left, inter_compl_self, empty_union],
    -- etc.
    sorry, },
  have h𝓓_mono : monotone 𝓓 :=
    λ k₁ k₂ h, sdiff_le_sdiff_left $ bUnion_mono (λ n, h.trans) (λ n hn x hx, hx),
  have h𝓓₂ : ∀ k l w, k ≤ l → p l → w ∈ z l → disjoint (𝓓 k) (closed_ball w (r l)),
  { sorry, },
  have h𝓓₃ : ∀ k l w, k ≤ l → p l → w ∈ z l →
    μ (𝓓 k ∩ closed_ball w (ρ * r l)) + μ (closed_ball w (r l)) ≤ μ (closed_ball w $ ρ * r l),
  { -- `measure_union` (or `measure_union'`).
    sorry, },
  -- Actually this is closer to what need:
  have h𝓓₃' : ∀ k l w, k ≤ l → p l → w ∈ z l →
    μ (𝓓 k ∩ closed_ball w (ρ * r l)) / μ (closed_ball w $ ρ * r l) +
    μ (closed_ball w (r l)) / μ (closed_ball w $ ρ * r l) ≤ 1,
  { sorry, },
  suffices : ∀ k, μ (𝓓 k) = 0,
  { change μ (cofinite.blimsup p U) = μ 𝓘,
    apply measure_eq_measure_of_null_diff hUI,
    simpa only [h𝓓, measure_Union_eq_supr h𝓓_mono.directed_le, ennreal.supr_eq_zero], },
  intros,
  by_contra contra,
  obtain ⟨x, hx₁, hx₂⟩ := measure.exists_mem_of_measure_ne_zero_of_ae contra
    (is_doubling_measure.ae_tendsto_measure_inter_div μ (𝓓 k) 1 (by norm_num)),
  have hx₀ : x ∈ 𝓘 := h𝓓₀ _ hx₁,
  -- let f₁ : ℕ ↪ {n | p n ∧ x ∈ I n} := hx₀.nat_embedding _,
  -- choose f₂ hf₂ using λ (n : {n | p n ∧ x ∈ I n}), mem_Union.mp n.property.2,
  -- have hx₃ : tendsto
  --   (λ j, μ (𝓓 k ∩ closed_ball ((f₂ ∘ f₁) j) (((ρ • r) ∘ coe ∘ f₁) j)) /
  --         μ (closed_ball ((f₂ ∘ f₁) j) (((ρ • r) ∘ coe ∘ f₁) j))) at_top (𝓝 1),
  -- { refine hx₂ _ _ (λ j, _) _ (λ j, _),
  --   { exact mul_pos (zero_lt_one.trans hρ) (hr₀ (f₁ j)), },
  --   { sorry, },
  --   { simp only [subtype.val_eq_coe, mem_Union, exists_prop] at hf₂,
  --     exact ((hf₂ (f₁ j)).2), }, },
  -- have hρ' : tendsto
  --   (λ j, μ (closed_ball ((f₂ ∘ f₁) j) (((ρ • r) ∘ coe ∘ f₁) j)) /
  --         μ (closed_ball ((f₂ ∘ f₁) j) ((r ∘ coe ∘ f₁) j))) at_top (𝓝 $ ρ^-d),
  -- { sorry, },
  -- have : 1 + (ρ : ℝ≥0∞) ^ -d ≤ 1,
  -- { refine le_of_tendsto (hx₃.add hρ') _,
  --   -- Use h𝓓₃'
  --   sorry, },
  -- replace this : (ρ : ℝ≥0∞) ^ -d ≤ 0 :=
  --   ennreal.add_le_cancellable_iff_ne.mpr ennreal.one_ne_top (by simpa only [add_zero] using this),
  -- simp only [nonpos_iff_eq_zero, ennreal.rpow_eq_zero_iff, ennreal.coe_eq_zero, right.neg_pos_iff,
  --   ennreal.coe_ne_top, false_and, or_false] at this,
  -- rw this.1 at hρ,
  -- exact not_lt_of_gt hρ one_pos,
  sorry,
end

namespace unit_add_circle

instance : measurable_space unit_add_circle := borel unit_add_circle

instance : borel_space unit_add_circle := ⟨rfl⟩

instance : measure_space unit_add_circle := ⟨measure.add_haar_measure ⊤⟩

instance : is_finite_measure (volume : measure unit_add_circle) :=
compact_space.is_finite_measure

@[simp] lemma volume_closed_ball (x : unit_add_circle) (r : ℝ) :
  volume (closed_ball x r) = min 1 (2 * r.to_nnreal) :=
sorry

instance : is_doubling_measure (volume : measure unit_add_circle) :=
sorry

/-- Given a sequence of real numbers: `n ↦ ψ n`, `add_circle.well_approximable ψ` is the set of
points `x` in `ℝ / ℤ` for which there exist infinitely-many rationals `m/n` (in lowest terms) with
`∥x - ↑((m : ℝ) / n)∥ ≤ ψ n`.

Gallagher's theorem `add_circle.volume_well_approximable_eq_zero_or_one` states that
`add_circle.well_approximable ψ` always has measure zero or one. The
Duffin-Koukoulopoulos-Maynard-Schaefer theorem gives a condition for telling which of these two
cases actually occurs for a given `ψ`. -/
def well_approximable (ψ : ℕ → ℝ) : set unit_add_circle :=
cofinite.limsup $ λ n x, ∃ (m : ℕ), m < n ∧ gcd n m = 1 ∧ ∥x - ↑((m : ℝ) / n)∥ ≤ ψ n

-- Needs (easy) asymptotic growth bounds for arithmetic functions.
lemma volume_well_approximable_eq_zero_or_one_aux
  {ψ : ℕ → ℝ} (hψ : ∀ j, 0 < ψ j) (hψ' : ¬ tendsto ψ at_top (𝓝 0)) :
  volume (well_approximable ψ) = 0 ∨ volume (well_approximable ψ) = 1 :=
sorry

local notation a `∤` b := ¬ a ∣ b
local notation a `‖` b := (a ∣ b) ∧ ¬ a^2 ∣ b

/-- Gallagher's theorem.

TODO Eliminate the `hψ` hypothesis? -/
lemma volume_well_approximable_eq_zero_or_one {ψ : ℕ → ℝ} (hψ : ∀ j, 0 < ψ j) :
  volume (well_approximable ψ) = 0 ∨ volume (well_approximable ψ) = 1 :=
begin
  classical,
  by_cases hψ' : tendsto ψ at_top (𝓝 0),
  swap, { exact volume_well_approximable_eq_zero_or_one_aux hψ hψ', },
  let a : ℕ → ℕ → ℕ → set unit_add_circle :=
    λ ν p n x, ∃ (m : ℕ), m < n ∧ gcd n m = 1 ∧ ∥x - ↑((m : ℝ) / n)∥ ≤ p^ν * ψ n,
  let 𝓐 : ℕ → ℕ → set unit_add_circle := λ ν p, cofinite.blimsup (λ n, p ∤ n) (a ν p),
  let z : ℕ → finset unit_add_circle :=
    λ n, ((finset.range n).filter n.coprime).image $ λ m, (↑((m : ℝ) / n) : unit_add_circle),
  have h𝓐z : ∀ ν p, cofinite.blimsup (λ n, p ∤ n) (λ n, ⋃ (w ∈ z n), closed_ball w (p^ν * ψ n)) = 𝓐 ν p,
  { intros,
    simp only [𝓐, finset.mem_image, finset.mem_filter, finset.mem_range, exists_prop, Union_exists,
      bUnion_and', Union_Union_eq_right],
    congr,
    ext n x,
    simpa only [mem_Union, exists_prop, and_assoc], },
  have h𝓐 : ∀ ν p, 1 < p → volume (𝓐 0 p) = volume (𝓐 ν p),
  { intros ν p hp,
    rcases eq_or_ne ν 0 with rfl | hν, { refl, },
    have hρ : 1 < (p : ℝ≥0)^ν := one_lt_pow (nat.one_lt_cast.mpr hp) hν,
    simp_rw ← h𝓐z,
    have h₁ : ∀ (t : ℝ≥0), ∀ᶠ (ε : ℝ≥0) in 𝓝 0, 2 * (t * ε) = t ^ (1 : ℝ) * (2 * ε),
    { refine λ t, eventually_of_forall (λ ε, _),
      simp only [nnreal.rpow_one, ← mul_assoc, mul_comm t], },
    convert measure_inf_often_eq volume hρ hψ hψ' z (λ n, p ∤ n),
    simp, },
  /- Remainder of proof:
   * In view of `h𝓐`, given any `p`, the union of `𝓐 ν p` over all `ν` has the same measure as
     `𝓐 0 p`
   * This union is invariant under the ergodic map `x ↦ p * x` (if `p` is prime) and thus has
     measure 0 or 1. Since it is a subset of `well_approximable ψ` we may as well assume it has
     measure 0 for all `p` (otherwise we're done).
   * Similarly define `𝓑`, just like `𝓐` except using the predicate `p ‖ n` instead of `p | n`.
     Same argument as for `𝓐` except the different divisibility condition means the right ergodic
     map is `x ↦ p * x + 1/p`. Thus again assume the `𝓑` have measure 0.
   * It remains to consider `𝓒` which is defined as for `𝓐` and `𝓑` but using the predicate
     `p^2 | n`. Because we have assumed `𝓐 0 p` and `𝓑 0 p` have measure zero for all primes `p`
     the measure of `𝓒 p` is the same as `well_approximable ψ` but `𝓒 p` is invariant under
     `x ↦ x ± 1/p`. This map is *not* ergodic but because we have this property for all primes,
     another density argument shows that `well_approximable ψ` must have measure 0 or 1.
  -/
  sorry,
end

end unit_add_circle
