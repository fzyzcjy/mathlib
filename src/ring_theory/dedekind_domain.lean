/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.discrete_valuation_ring
import ring_theory.fractional_ideal
import ring_theory.ideal.over
import logic.function.basic
import field_theory.minimal_polynomial
import ring_theory.adjoin_root

/-!
# Dedekind domains

This file defines the notion of a Dedekind domain (or Dedekind ring),
giving three equivalent definitions (TODO: and shows that they are equivalent).
We have now shown one side of the equivalence two of these definitions.

## Main definitions

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is not a field,
   Noetherian, integrally closed in its field of fractions and has Krull dimension exactly one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.
 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that is not a field,
   Noetherian, and the localization at every nonzero prime ideal is a discrete valuation ring.
 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain that is not a field,
   and every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags

dedekind domain, dedekind ring
-/

variables (R A K : Type*) [comm_ring R] [integral_domain A] [field K]

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def ring.dimension_le_one : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

namespace ring

lemma dimension_le_one.principal_ideal_ring
  [is_principal_ideal_ring A] : dimension_le_one A :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

lemma dimension_le_one.integral_closure [nontrivial R] [algebra R A]
  (h : dimension_le_one R) : dimension_le_one (integral_closure R A) :=
begin
  intros p ne_bot prime,
  haveI := prime,
  refine integral_closure.is_maximal_of_is_maximal_comap p
    (h _ (integral_closure.comap_ne_bot ne_bot) _),
  apply is_prime.comap
end

end ring

/--
A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension exactly one (`not_is_field` and `dimension_le_one`).

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class is_dedekind_domain : Prop :=
(not_is_field : ¬ is_field A)
(is_noetherian_ring : is_noetherian_ring A)
(dimension_le_one : dimension_le_one A)
(is_integrally_closed : integral_closure A (fraction_ring A) = ⊥)

/-- An integral domain is a Dedekind domain iff and only if it is not a field, is Noetherian, has dimension ≤ 1,
and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
lemma is_dedekind_domain_iff (f : fraction_map A K) :
  is_dedekind_domain A ↔
    (¬ is_field A) ∧ is_noetherian_ring A ∧ dimension_le_one A ∧
    integral_closure A f.codomain = ⊥ :=
⟨λ ⟨hf, hr, hd, hi⟩, ⟨hf, hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f),
         hi, algebra.map_bot]⟩,
 λ ⟨hf, hr, hd, hi⟩, ⟨hf, hr, hd,
  by rw [←integral_closure_map_alg_equiv (fraction_ring.alg_equiv_of_quotient f).symm,
         hi, algebra.map_bot]⟩⟩

/--
A Dedekind domain is an integral domain that is not a field, is Noetherian, and the localization at
every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr : Prop :=
(not_is_field : ¬ is_field A)
(is_noetherian_ring : is_noetherian_ring A)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal A), P.is_prime →
  discrete_valuation_ring (localization.at_prime P))

/--
A Dedekind domain is an integral domain that is not a field such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_inv : Prop :=
(not_is_field : ¬ is_field A)
(mul_inv_cancel : ∀ I ≠ (⊥ : fractional_ideal (fraction_ring.of A)), I * I⁻¹ = 1)

section

open ring.fractional_ideal

lemma is_dedekind_domain_inv_iff (f : fraction_map A K) :
  is_dedekind_domain_inv A ↔
    (¬ is_field A) ∧ (∀ I ≠ (⊥ : fractional_ideal f), I * I⁻¹ = 1) :=
begin
  split; rintros ⟨hf, hi⟩; use hf; intros I hI,
  { have := hi (map (fraction_ring.alg_equiv_of_quotient f).symm.to_alg_hom I) (map_ne_zero _ hI),
    erw [← map_inv, ← fractional_ideal.map_mul] at this,
    convert congr_arg (map (fraction_ring.alg_equiv_of_quotient f).to_alg_hom) this;
      simp only [alg_equiv.to_alg_hom_eq_coe, map_symm_map, map_one] },
  { have := hi (map (fraction_ring.alg_equiv_of_quotient f).to_alg_hom I) (map_ne_zero _ hI),
    erw [← map_inv, ← fractional_ideal.map_mul] at this,
    convert congr_arg (map (fraction_ring.alg_equiv_of_quotient f).symm.to_alg_hom) this;
      simp only [alg_equiv.to_alg_hom_eq_coe, map_map_symm, map_one] }
end

end

section

open ring.fractional_ideal

variables {A}

open_locale classical

variables {B : Type*} [semiring B]
variables {M : Type*} [add_comm_monoid M] [semimodule B M]

open submodule

lemma submodule.mem_span_finite_of_mem_span {S : set M} {x : M} (hx : x ∈ span B S) :
  ∃ T : finset M, ↑T ⊆ S ∧ x ∈ span B (T : set M) :=
begin
  refine span_induction hx (λ x hx, _) _ _ _,
  { refine ⟨{x}, _, _⟩,
    { rwa [finset.coe_singleton, set.singleton_subset_iff] },
    { rw finset.coe_singleton,
      exact submodule.mem_span_singleton_self x } },
  { use ∅, simp },
  { rintros x y ⟨X, hX, hxX⟩ ⟨Y, hY, hyY⟩,
    refine ⟨X ∪ Y, _, _⟩,
    { rw finset.coe_union,
      exact set.union_subset hX hY },
    rw [finset.coe_union, span_union, mem_sup],
    exact ⟨x, hxX, y, hyY, rfl⟩, },
  { rintros a x ⟨T, hT, h2⟩,
    exact ⟨T, hT, smul_mem _ _ h2⟩ }
end

lemma submodule.mem_span_mul_finite_of_mem_span_mul {B M : Type*} [comm_semiring B] [semiring M]
  [algebra B M] {S : set M} {S' : set M} {x : M} (hx : x ∈ span B (S * S')) :
  ∃ (T T' : finset M), ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ x ∈ span B (T * T' : set M) :=
begin
  apply span_induction hx,
  { rintros x hx,
    obtain ⟨y, z, hy, hz, h'⟩ := set.mem_mul.mp hx,
    have hy' := submodule.subset_span hy,
    have hz' := submodule.subset_span hz,
    have h := submodule.mem_span_finite_of_mem_span hy',
    rcases h with ⟨T, hT, fy⟩,
    have h := submodule.mem_span_finite_of_mem_span hz',
    rcases h with ⟨T', hT', fz⟩,
    use [T, T', hT, hT'],
    rw [←h', ←submodule.span_mul_span],
    apply mul_mem_mul fy fz, },
  { use [∅, ∅], simp, },
  { rintros x y ⟨T, T', hT, hT', h1⟩ ⟨U, U', hU, hU', h2⟩,
    use [T ∪ U, T' ∪ U'],
    simp only [finset.coe_union],
    use [set.union_subset hT hU, set.union_subset hT' hU'],
    suffices f : x + y ∈ span B ((T * T') ∪ (U * U') : set M),
    { have f' : ((T * T') ∪ (U * U') : set M) ⊆ ((T ∪ U) * (T' ∪ U') : set M),
      { convert set.subset_union_left (T * T' ∪ U * U' : set M) (T * U' ∪ U * T'),
        simp only [set.mul_union, set.union_mul, set.union_mul],
        ac_refl },
      apply span_mono f' f, },
    rw [span_union, mem_sup],
    exact ⟨x, h1, y, h2, rfl⟩ },
  rintros a x ⟨T, T', hT, hT', h⟩,
  exact ⟨T, T', hT, hT', smul_mem _ _ h⟩,
end


lemma ne_bot_of_is_maximal_of_not_is_field {M : ideal A} (max : M.is_maximal)
  (not_field : ¬ is_field A) : M ≠ ⊥ :=
begin
  rintros h,
  rw h at max,
  cases max with h1 h2,
  obtain ⟨I, hIbot, hItop⟩ := not_is_field_iff_exists_ideal_bot_lt_and_lt_top.mp not_field,
  specialize h2 I hIbot,
  exact ne_of_lt hItop h2
end

variables {K} {f : fraction_map A K}

@[simp, norm_cast]
lemma coe_ideal_le_coe_ideal {I J : ideal A} :
  (I : fractional_ideal f) ≤ (J : fractional_ideal f) ↔ I ≤ J :=
begin
  split,
  { intros h x hI,
    rw le_iff_mem at h,
    specialize h (f.to_map x),
    simp only [exists_prop, mem_coe_ideal, exists_mem_to_map_eq] at h,
    exact h hI },
  { rintros h x hx,
    simp only [val_eq_coe, coe_coe_ideal, localization_map.mem_coe_submodule] at hx ⊢,
    obtain ⟨y, hy, y_eq⟩ := hx,
    exact ⟨y, h hy, y_eq⟩ },
end

lemma mem_coe' {S : submonoid R} {P : Type*} [comm_ring P]
  (f : localization_map S P) (I : fractional_ideal f) (x : f.codomain) :
  x ∈ (I : submodule R f.codomain) ↔ x ∈ I := iff.rfl

lemma fg_of_one_mem_span (s : ideal A) (h2 : (s * (1 / s) : fractional_ideal f) = 1)
  (T T' : finset f.codomain)
  (hT : (T : set f.codomain) ⊆ (s : fractional_ideal f))
  (hT' : (T' : set f.codomain) ⊆ ↑((s : fractional_ideal f)⁻¹))
  (h3 : (1 : f.codomain) ∈ submodule.span A (T * T' : set f.codomain)) :
  s.fg :=
begin
  have g := f.injective,
  apply submodule.fg_of_fg_map f.lin_coe (linear_map.ker_eq_bot.mpr f.injective),
  refine ⟨T, _⟩,
  ext x,
  split,
  { intro gx,
    have f'' : span A (T : set f.codomain) ≤ (s : fractional_ideal f) := submodule.span_le.mpr hT,
    simp only [localization_map.lin_coe_apply, submodule.mem_map],
    have g' := f'' gx,
    simp only [coe_coe_ideal] at g',
    rcases g' with ⟨y, hy, g''⟩,
    use [y, hy, g''], },
  intro gx,
  have g'' : x ∈ submodule.span A {x} := submodule.mem_span_singleton_self x,
  have g' : x * 1 ∈ submodule.span A {x} * submodule.span A (T * T' : set f.codomain) :=
    submodule.mul_mem_mul g'' h3,
  rw [mul_one x, ← submodule.span_mul_span, submodule.mul_comm] at g',
  have g2 : x ∈ submodule.span A (T : set f.codomain) * submodule.span A (T' * {x}),
  { rw [←submodule.span_mul_span A, ←mul_assoc],
    exact g', },
  suffices f2 : submodule.span A (T : set f.codomain) * submodule.span A (T' * {x}) ≤ submodule.span A T,
  apply iff.rfl.1 f2 g2,
  suffices f2 : submodule.span A (T' * {x} : set f.codomain) ≤ 1,
  { have f3 := submodule.mul_le_mul (le_refl (submodule.span A (T : set f.codomain))) f2,
    rwa mul_one (submodule.span A (T : set f.codomain)) at f3, },
  rw submodule.one_eq_span,
  have f2 : ({x} : set f.codomain) ⊆ (s : fractional_ideal f),
  { simp only [submodule.mem_coe, set.singleton_subset_iff],
    simp at gx,
    suffices f1 : x ∈ (s : fractional_ideal f), exact f1, simp,
    rcases gx with ⟨y, hy, g''⟩,
    use [y, hy, g''], },
  have f3 : span A {x} ≤ ↑(s : fractional_ideal f) := submodule.span_le.mpr f2,
  have h1T' : span A (T' : set f.codomain) ≤ ↑((s : fractional_ideal f)⁻¹) := submodule.span_le.mpr hT',
  have f' := submodule.mul_le_mul h1T' f3,
  rw submodule.span_mul_span at f',
  rw ← coe_mul at f',
  suffices hf : (s : fractional_ideal f)⁻¹ * (s : fractional_ideal f) = 1,
  rw hf at f',
  convert f',
  simp, rw [submodule.one_eq_span],
  rw mul_comm _ _,
  assumption,
end

lemma noeth : is_dedekind_domain_inv A -> is_noetherian_ring A :=
begin
  rintros ⟨h1, h2⟩,
  split,
  rintros s,
  specialize h2 s,
  by_cases s = ⊥,
  { rw h, apply submodule.fg_bot, },
  have h := (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr h,
  have h' := h2 h,
  have hf := h2 h,
  rw ← fractional_ideal.ext_iff at h',
  specialize h' 1,
  have h'' := h'.2 one_mem_one,
  set q : submodule A (localization_map.codomain (fraction_ring.of A)) :=
    (s : fractional_ideal (fraction_ring.of A)).val with hq,
  set q' : submodule A (localization_map.codomain (fraction_ring.of A)) :=
    (s : fractional_ideal (fraction_ring.of A))⁻¹.val with hq',
  rw [← mem_coe', coe_mul, ← val_eq_coe, ← val_eq_coe, ←submodule.span_eq (q * q')] at h'',
  simp at h'',
  rw [←submodule.span_eq q, ←submodule.span_eq q', submodule.span_mul_span] at h'',
  obtain ⟨T, T', hT, hT', h⟩ := submodule.mem_span_mul_finite_of_mem_span_mul h'',
  exact fg_of_one_mem_span s hf T T' hT hT' h,
end

lemma fraction_ring_fractional_ideal (x : (fraction_ring A)) (hx : is_integral A x) :
 is_fractional (fraction_ring.of A)
((algebra.adjoin A {x}).to_submodule : submodule A (localization_map.codomain (fraction_ring.of A))) :=
is_fractional_of_fg (fg_adjoin_singleton_of_integral x hx)

lemma mem_adjoin (x : fraction_ring A) :
  x ∈ ((algebra.adjoin A {x}) : subalgebra A (localization_map.codomain (fraction_ring.of A))) :=
by {apply subsemiring.subset_closure, simp}

lemma int_close : is_dedekind_domain_inv A -> integral_closure A (fraction_ring A) = ⊥ :=
begin
  rintros h,
  ext,
  split,
  { rintros hx,
    cases h with h1 h2,
    let S : subalgebra A (localization_map.codomain (fraction_ring.of A)) := algebra.adjoin A {x},
    have f' : is_fractional _ (S.to_submodule),
    { apply fraction_ring_fractional_ideal,
      rcases hx with ⟨p, hp1, hp2⟩,
      split,
      rotate,
      use p,
      split, assumption, assumption, },
    set M : fractional_ideal (fraction_ring.of A) := ⟨S.to_submodule, f'⟩ with h1M,
    by_cases x = 0,
    rw h,
    apply subalgebra.zero_mem ⊥,
    have f : M = 1,
    { specialize h2 M,
      rw ←mul_one M,
      have g : M ≠ ⊥,
      { classical,
        by_contradiction a,
        simp at a,
        rw subtype.ext_iff_val at a,
        simp at a,
        rw submodule.eq_bot_iff S.to_submodule at a,
        specialize a x,
        apply h,
        apply a,
        suffices f : x ∈ (S : submodule A (localization_map.codomain (fraction_ring.of A))), exact f,
        rw subalgebra.mem_to_submodule,
        apply mem_adjoin, },
      have hM := h2 g,
      suffices hM' : M * (M * M⁻¹) = 1,
      rw hM at hM', assumption,
      suffices hM' : M * M = M,
      assoc_rw hM', assumption,
      rw subtype.ext_iff_val,
      simp,
      suffices f : (S : submodule A (localization_map.codomain (fraction_ring.of A))) *
      (S : submodule A (localization_map.codomain (fraction_ring.of A))) =
      (S : submodule A (localization_map.codomain (fraction_ring.of A))), exact f,
      rw subalgebra.mul_self, },
    have fx : x ∈ M,
    suffices f : x ∈ (S : submodule A (localization_map.codomain (fraction_ring.of A))), exact f,
    rw subalgebra.mem_to_submodule,
    apply mem_adjoin,
    suffices h' : x ∈ ((⊥ : subalgebra A (localization_map.codomain (fraction_ring.of A))) :
    submodule A (localization_map.codomain (fraction_ring.of A))),
    rw subalgebra.mem_to_submodule at h', assumption,
    rw algebra.to_submodule_bot,
    rw ← fractional_ideal.ext_iff at f,
    specialize f x,
    have g' := f.1 fx,
    rw ←coe_span_singleton 1,
    rw ring.fractional_ideal.span_singleton_one,
    apply iff.rfl.1 g',  },
  rintros hx,
  rw mem_integral_closure_iff_mem_fg,
  use ⊥,
  split,
  use {1},
  rw algebra.to_submodule_bot,
  simp,
  assumption,
end

lemma dim_le_one : is_dedekind_domain_inv A -> dimension_le_one A :=
begin
  rintros h,
  rcases h with ⟨h1, h2⟩,
  rintros p nz hp,
  have hpinv := h2 p,
  have hpmax := exists_le_maximal p hp.1,
  rcases hpmax with ⟨M, hM1, hM2⟩,
  specialize h2 M,
  have coe_ne_bot : ∀ {I : ideal A}, I ≠ ⊥ → (I : fractional_ideal (fraction_ring.of A)) ≠ 0 :=
    λ I, (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr,
  specialize hpinv (coe_ne_bot nz),
  specialize h2 (coe_ne_bot (ne_bot_of_is_maximal_of_not_is_field hM1 h1)),
  set I := (M : fractional_ideal (fraction_ring.of A))⁻¹ * (p : fractional_ideal (fraction_ring.of A))
  with hI,
  have f' : I ≤ 1,
  { set N := (M : fractional_ideal (fraction_ring.of A))⁻¹ with hN,
    have g'' := submodule.mul_le_mul (coe_ideal_le_coe_ideal.mp hM2) (le_refl N),
    simp only [val_eq_coe, ←coe_mul] at g'',
    norm_cast at g'',
    rw h2 at g'',
    rw mul_comm at g'',
    exact g'', },
  have f : (M : fractional_ideal (fraction_ring.of A)) * I = (p : fractional_ideal (fraction_ring.of A)),
  { rw hI, assoc_rw h2, simp, },
  by_cases p = M,
  { rw h, assumption, },
  exfalso,
  have g : I ≤ (p : fractional_ideal (fraction_ring.of A)),
  { rw le_iff_mem,
    rintros x hxI,
    have hpM : ∃ (y : A) (H : y ∈ M), y ∉ p,
    { apply exists_of_lt,
      apply lt_of_le_of_ne, assumption, assumption, },
    rcases hpM with ⟨z, hz, hpz⟩,
    rw le_iff_mem at f',
    specialize f' x hxI,
    have f'' : x ∈ ((1 : ideal A) : fractional_ideal (fraction_ring.of A)) := f',
    simp at f'',
    rcases f'' with ⟨y, f'⟩,
    rw ←f',
    have f'' : y*z ∈ p,
    { suffices g : x * (localization_map.to_map (fraction_ring.of A) z) ∈ (p : fractional_ideal (fraction_ring.of A)),
      { rw [←f', ←ring_hom.map_mul] at g,
        simp at g,
        rcases g with ⟨x', Hx, g⟩,
        suffices g'' : x' = (y*z),
        rw g'' at Hx,
        assumption,
        apply fraction_map.injective (fraction_ring.of A),
        simp_rw g, simp, },
      rw [←f, mul_comm],
      refine mul_mem_mul _ hxI,
      set z' := (localization_map.to_map (fraction_ring.of A)) z with hz',
      simp, assumption,  },
    have hp' := hp.right f'',
    cases hp',
    { set z' := (localization_map.to_map (fraction_ring.of A)) y with hz',
      simp, assumption, },
    finish,  },
  rw [←subtype.coe_le_coe, hI] at g,
  norm_cast at g,
  have hM := le_refl (M : fractional_ideal (fraction_ring.of A)),
  have g' := submodule.mul_le_mul g hM,
  rw mul_comm at g',
  simp only [val_eq_coe, ←coe_mul] at g',
  norm_cast at g',
  assoc_rw h2 at g',
  rw one_mul at g',
  set q := (p : fractional_ideal (fraction_ring.of A))⁻¹ with hq,
  have g'' := submodule.mul_le_mul g' (le_refl q),
  simp only [val_eq_coe, ←coe_mul] at g'',
  norm_cast at g'',
  rw [hpinv, mul_comm] at g'',
  rw mul_comm at hpinv,
  assoc_rw hpinv at g'',
  rw one_mul at g'',
  have ginv : (M : fractional_ideal (fraction_ring.of A)) ≤ 1,
  { apply submodule.map_mono, simp, },
  have k := (has_le.le.le_iff_eq ginv).1 g'',
  cases hM1 with hM11 hM12,
  apply hM11,
  unfold has_one.one at k,
  simp at k,
  rw ideal.eq_top_iff_one,
  rw ← fractional_ideal.ext_iff at k,
  specialize k 1,
  have k' := k.1 one_mem_one,
  simp at k',
  rcases k' with ⟨x, hx, k'⟩,
  suffices f' : x = 1,
  rw f' at hx,
  assumption,
  apply fraction_map.injective (fraction_ring.of A),
  assumption,
end

theorem tp : is_dedekind_domain_inv A -> is_dedekind_domain A :=
begin
  rintros h,
  split,
  { apply h.1, },
  { apply noeth, assumption, },
  { apply dim_le_one, assumption, },
  { apply int_close, assumption, },
end

end
