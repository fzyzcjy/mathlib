/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import topology.continuous_function.compact
import topology.urysohns_lemma
import data.complex.is_R_or_C

/-!
# Ideals of continuous functions

## Main definitions

* `continuous_map.ideal_of_set`
* `continuous_map.set_of_ideal`

## Main statements

* ``

## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open_locale nnreal

namespace continuous_map
variables {X R : Type*} [topological_space X] [ring R] [topological_space R] [topological_ring R]

variable (R)

/-- Given a topological ring `R` and `s : set X`, construct the ideal in `C(X, R)` of functions
which vanish on the complement of `s`. -/
def ideal_of_set (s : set X) : ideal C(X, R) :=
{ carrier := {f : C(X, R) | ∀ x ∈ sᶜ, f x = 0},
  add_mem' := λ f g hf hg x hx, by simp only [hf x hx, hg x hx, coe_add, pi.add_apply, add_zero],
  zero_mem' := by simp only [set.mem_set_of_eq, coe_zero, pi.zero_apply, eq_self_iff_true, implies_true_iff],
  smul_mem' := λ c f hf x hx, mul_zero (c x) ▸ congr_arg (λ y, c x * y) (hf x hx), }

variable {R}

lemma mem_ideal_of_set {s : set X} {f : C(X, R)} :
  f ∈ ideal_of_set R s ↔ ∀ ⦃x : X⦄, x ∈ sᶜ → f x = 0 := iff.rfl

lemma not_mem_ideal_of_set {s : set X} {f : C(X, R)} :
  f ∉ ideal_of_set R s ↔ ∃ x ∈ sᶜ, f x ≠ 0 :=
by { simp_rw [mem_ideal_of_set, exists_prop], push_neg }

lemma ideal_of_set_closed [locally_compact_space X] [t2_space R] (s : set X) :
  is_closed (ideal_of_set R s : set C(X, R) ) :=
begin
  simp only [ideal_of_set, submodule.coe_set_mk, set.set_of_forall],
  exact is_closed_Inter (λ x, is_closed_Inter $
    λ hx, is_closed_eq (continuous_eval_const' x) continuous_const),
end

/-- Given an ideal `I` of `C(X, R)`, construct the set of points for which every function in the
ideal vanishes on the complement. -/
def set_of_ideal (I : ideal C(X, R)) : set X :=
{x : X | ∀ f ∈ I, (f : C(X, R)) x = 0}ᶜ

lemma not_mem_set_of_ideal {I : ideal C(X, R)} {x : X} :
  x ∉ set_of_ideal I ↔ ∀ ⦃f : C(X, R)⦄, f ∈ I → f x = 0 :=
by rw [←set.mem_compl_iff, set_of_ideal, compl_compl, set.mem_set_of]

lemma mem_set_of_ideal {I : ideal C(X, R)} {x : X} :
  x ∈ set_of_ideal I ↔ ∃ f ∈ I, (f : C(X, R)) x ≠ 0 :=
by { simp_rw [set_of_ideal, set.mem_compl_iff, set.mem_set_of, exists_prop], push_neg }

lemma set_of_ideal_open [t2_space R] (I : ideal C(X, R)) : is_open (set_of_ideal I) :=
begin
  simp only [set_of_ideal, set.set_of_forall, is_open_compl_iff],
  exact is_closed_Inter (λ f, is_closed_Inter $
    λ hf, is_closed_eq (map_continuous f) continuous_const)
end

variables (X R)
lemma gc : galois_connection (set_of_ideal : ideal C(X, R) → set X) (ideal_of_set R) :=
begin
  refine λ I s, ⟨λ h f hf, _, λ h x hx, _⟩,
  { by_contra h',
    rcases not_mem_ideal_of_set.mp h' with ⟨x, hx, hfx⟩,
    exact hfx (not_mem_set_of_ideal.mp (mt (@h x) hx) hf) },
  { obtain ⟨f, hf, hfx⟩ := mem_set_of_ideal.mp hx,
    by_contra hx',
    exact not_mem_ideal_of_set.mpr ⟨x, hx', hfx⟩ (h hf) },
end

theorem nnnorm_lt_iff {α E : Type*} [topological_space α] [compact_space α]
  [normed_add_comm_group E] (f : C(α, E)) {M : ℝ≥0} (M0 : 0 < M) :
∥f∥₊ < M ↔ ∀ (x : α), ∥f x∥₊ < M :=
f.norm_lt_iff M0

end continuous_map

namespace continuous_map

variables {X 𝕜 A : Type*} [is_R_or_C 𝕜] [topological_space X] [normed_ring A] [star_ring A]
variables [cstar_ring A] [normed_algebra 𝕜 A] [h𝕜A : star_module 𝕜 A]
open is_R_or_C

lemma main_lemma_aux (f : C(X, ℝ≥0)) {c : ℝ≥0} (hc : 0 < c) :
  ∃ g : C(X, ℝ≥0), (∀ x : X, (g * f) x ≤ 1) ∧ {x : X | c ≤ f x}.eq_on (g * f) 1 :=
begin
  refine ⟨⟨(f ⊔ (const X c))⁻¹, continuous.inv₀ ((map_continuous f).sup $ map_continuous _)
    (λ x, (hc.trans_le le_sup_right).ne')⟩, λ x, _, _⟩,
  exact (inv_mul_le_iff (hc.trans_le le_sup_right)).mpr ((mul_one (f x ⊔ c)).symm ▸ le_sup_left),
  intros x hx,
  simpa only [coe_const, coe_mk, pi.mul_apply, pi.inv_apply, pi.sup_apply, function.const_apply,
    pi.one_apply, sup_eq_left.mpr (set.mem_set_of.mp hx)]
  using inv_mul_cancel (hc.trans_le hx).ne',
end

lemma ideal_of_set_of_le_closure [compact_space X] (I : ideal C(X, 𝕜)) :
  ideal_of_set 𝕜 (set_of_ideal I) ≤ I.closure :=
begin
  /- given `f ∈ ideal_of_set 𝕜 (set_of_ideal I)` and `(ε : ℝ≥0) > 0` it suffices to show that
  `f` is within `ε` of `I`. Let `t := {x : X | ε / 2 ≤ ∥f x∥₊}}` which is closed and disjoint from
  `set_of_ideal I`. -/
  refine λ f hf, metric.mem_closure_iff.mpr (λ ε hε, _),
  lift ε to ℝ≥0 using hε.lt.le,
  replace hε := (show (0 : ℝ≥0) < ε, from hε),
  simp_rw dist_nndist,
  norm_cast,
  set t := {x : X | ε / 2 ≤ ∥f x∥₊},
  have ht : is_closed t := is_closed_le continuous_const (map_continuous f).nnnorm,
  have htI : disjoint t (set_of_ideal I)ᶜ,
  { refine set.subset_compl_iff_disjoint_left.mp (λ x hx, _),
    simpa only [t, set.mem_set_of, set.mem_compl_iff, not_le]
      using (nnnorm_eq_zero.mpr (mem_ideal_of_set.mp hf hx)).trans_lt (half_pos hε), },
  /- It suffices to produce `g : C(X, ℝ≥0)` which takes values in `[0,1]` and is constantly `1` on
  `t` such that when composed with the natural embedding of `ℝ≥0` into `𝕜` lies in the ideal `I`.
  Indeed, then `∥f - f * ↑g∥ ≤ ∥f * (1 - ↑g)∥ ≤ ⨆ ∥f * (1 - ↑g) x∥`. When `x ∉ t`, `∥f x∥ < ε / 2`
  and `∥(1 - ↑g) x∥ ≤ 1`, and when `x ∈ t`, `(1 - ↑g) x = 0`, and clearly `f * ↑g ∈ I`. -/
  suffices : ∃ g : C(X, ℝ≥0), of_nnreal_cm.comp g ∈ I ∧ (∀ x, g x ≤ 1) ∧ t.eq_on g 1,
  { obtain ⟨g, hgI, hg, hgt⟩ := this,
    refine ⟨f * of_nnreal_cm.comp g, I.mul_mem_left f hgI, _⟩,
    rw nndist_eq_nnnorm,
    refine (nnnorm_lt_iff _ hε).2 (λ x, _),
    simp only [coe_sub, coe_mul, pi.sub_apply, pi.mul_apply],
    by_cases hx : x ∈ t,
    { simpa only [hgt hx, pi.one_apply, mul_one, sub_self, nnnorm_zero, comp_apply,
        of_nnreal_cm_coe, map_one] using hε },
    { refine lt_of_le_of_lt _ (half_lt_self hε),
      have : ∥((1 - of_nnreal_cm.comp g) x : 𝕜)∥₊ ≤ 1,
      { simp only [coe_sub, coe_one, pi.sub_apply, pi.one_apply, comp_apply,
          of_nnreal_cm_coe, ←(map_one of_nnreal_am), of_nnreal_am_coe, coe_coe],
        rw [←is_R_or_C.of_real_one, ←nnreal.coe_one, ←of_real_sub, ←nnreal.coe_sub (hg x)],
        rw [nnnorm_of_nnreal (1 - g x)],
        exact tsub_le_self, },
      calc ∥f x - f x * of_nnreal_cm.comp g x∥₊
          = ∥f x * (1 - of_nnreal_cm.comp g) x∥₊
          : by simp only [mul_sub, coe_sub, coe_one, pi.sub_apply, pi.one_apply, mul_one]
      ... ≤ (ε / 2) * ∥(1 - of_nnreal_cm.comp g) x∥₊
          : (nnnorm_mul_le _ _).trans (mul_le_mul_right'
              (not_le.mp $ show ¬ ε / 2 ≤ ∥f x∥₊, from hx).le _)
      ... ≤ ε / 2 : by simpa only [mul_one] using mul_le_mul_left' this _, } },
  /- There is some `g' : C(X, ℝ≥0)` which is strictly positive on `t` such that the composition
  `↑g` with the natural embedding of `ℝ≥0` into `𝕜` lies in `I`. This follows from compactness of
  `t` and that we can do it in any neighborhood of a point `x ∈ t`. Indeed, since `x ∈ t`, then
  `fₓ x ≠ 0` for some `fₓ ∈ I` and so `λ y, ∥(star fₓ * fₓ) y∥₊` is strictly posiive in a
  neighborhood of `y`. Moreover, `(∥(star fₓ * fₓ) y∥₊ : 𝕜) = (star fₓ * fₓ) y`, so composition of
  this map with the natural embedding is just `star fₓ * fₓ ∈ I`. -/
  have : ∃ g' : C(X, ℝ≥0), of_nnreal_cm.comp g' ∈ I ∧ (∀ x ∈ t, 0 < g' x),
  { refine @is_compact.induction_on _ _ _ ht.is_compact
      (λ s, ∃ g' : C(X, ℝ≥0), of_nnreal_cm.comp g' ∈ I ∧ (∀ x ∈ s, 0 < g' x)) _ _ _ _,
    { refine ⟨0, by { convert I.zero_mem, ext, simp only [comp_apply, coe_zero, pi.zero_apply,
        of_nnreal_cm_coe, map_zero]}, λ x hx, false.elim hx⟩, },
    { rintro s₁ s₂ hs ⟨g, hI, hgt⟩, exact ⟨g, hI, λ x hx, hgt x (hs hx)⟩, },
    { rintro s₁ s₂ ⟨g₁, hI₁, hgt₁⟩ ⟨g₂, hI₂, hgt₂⟩,
      refine ⟨g₁ + g₂, _, λ x hx, _⟩,
      convert I.add_mem hI₁ hI₂,
      ext y,
      simp only [coe_add, pi.add_apply, of_nnreal_cm_coe, map_add, coe_comp, function.comp_app],
      rcases hx with (hx | hx),
      simpa only [zero_add] using add_lt_add_of_lt_of_le (hgt₁ x hx) zero_le',
      simpa only [zero_add] using add_lt_add_of_le_of_lt zero_le' (hgt₂ x hx), },
    { intros x hx,
      replace hx := htI.subset_compl_right hx,
      rw [compl_compl, mem_set_of_ideal] at hx,
      obtain ⟨g, hI, hgx⟩ := hx,
      have := (map_continuous g).continuous_at.eventually_ne hgx,
      refine ⟨{y : X | g y ≠ 0} ∩ t, mem_nhds_within_iff_exists_mem_nhds_inter.mpr
        ⟨_, this, set.subset.rfl⟩, ⟨⟨λ x, ∥g x∥₊ ^ 2, (map_continuous g).nnnorm.pow 2⟩, _,
        λ x hx, pow_pos (norm_pos_iff.mpr hx.1) 2⟩⟩,
      convert I.mul_mem_left (star g) hI,
      ext,
      simp only [comp_apply, coe_mk, of_nnreal_cm_coe, map_pow, coe_mul, coe_star,
        pi.mul_apply, pi.star_apply, star_def],
      simp only [of_nnreal_am_coe, coe_coe, coe_nnnorm, norm_sq_eq_def', conj_mul_eq_norm_sq_left,
        of_real_pow], }, },
  /- Get the function `g'` which is guaranteed to exist above. By the extreme value theorem and
  compactness of `t`, there is some `0 < c` such that `c ≤ g' x` for all `x ∈ t`. Then by
  `main_lemma_aux` there is some `g` for which `g * g'` is the desired function. -/
  obtain ⟨g', hI', hgt'⟩ := this,
  obtain (⟨c, hc, hgc'⟩ : ∃ c (hc : 0 < c), ∀ y : X, y ∈ t → c ≤ g' y) :=
  t.eq_empty_or_nonempty.elim (λ ht', ⟨1, zero_lt_one, λ y hy, false.elim (by rwa ht' at hy)⟩)
    (λ ht', let ⟨x, hx, hx'⟩ := ht.is_compact.exists_forall_le ht' (map_continuous g').continuous_on
      in ⟨g' x, hgt' x hx, hx'⟩),
  obtain ⟨g, hg, hgc⟩ := main_lemma_aux g' hc,
  refine ⟨g * g', _, hg, hgc.mono hgc'⟩,
  convert I.mul_mem_left (of_nnreal_cm.comp g) hI',
  ext,
  simp only [of_nnreal_cm_coe, comp_apply, coe_mul, pi.mul_apply, map_mul],
end

@[simp] lemma ideal_of_set_of_is_closed [compact_space X] {I : ideal C(X, 𝕜)}
  (hI : is_closed (I : set C(X, 𝕜))) : ideal_of_set 𝕜 (set_of_ideal I) = I :=
le_antisymm ((ideal_of_set_of_le_closure I).trans $ closure_subset_iff_is_closed.mpr hI)
  ((gc X 𝕜).le_u_l I)

lemma interior_subset_of_ideal_of_set [compact_space X] [t2_space X] (s : set X) :
  interior s ⊆ set_of_ideal (ideal_of_set 𝕜 s) :=
begin
  /- If `x ∉ closure sᶜ`, we must produce `f : C(X, 𝕜)` which is zero on `sᶜ` and `f x ≠ 0`. -/
  rw [←compl_compl (interior s), ←closure_compl],
  intros x hx,
  simp_rw [mem_set_of_ideal, mem_ideal_of_set],
  haveI : normal_space X := normal_of_compact_t2,
  /- Apply Urysohn's lemma to get `g : C(X, ℝ)` which is zero on `sᶜ` and `g x ≠ 0`, then compose
  with the natural embedding `ℝ ↪ 𝕜` to produce the desired `f`. -/
  obtain ⟨g, hgs, (hgx : set.eq_on g 1 {x}), -⟩ := exists_continuous_zero_one_of_closed
    is_closed_closure is_closed_singleton (set.disjoint_singleton_right.mpr hx),
  exact ⟨⟨λ x, g x, continuous_of_real.comp (map_continuous g)⟩,
    by simpa only [coe_mk, of_real_eq_zero] using λ x hx, hgs (subset_closure hx),
    by simpa only [coe_mk, hgx (set.mem_singleton x), pi.one_apply, is_R_or_C.of_real_one]
      using one_ne_zero⟩,
end

@[simp] lemma set_of_ideal_of_is_open [compact_space X] [t2_space X] {s : set X} (hs : is_open s) :
  set_of_ideal (ideal_of_set 𝕜 s) = s :=
le_antisymm ((gc X 𝕜).l_u_le s)
  (by simpa only [hs.interior_eq] using (interior_subset_of_ideal_of_set s))

end continuous_map
