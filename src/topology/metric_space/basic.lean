/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/

import data.int.interval
import tactic.positivity
import topology.algebra.order.compact
import topology.metric_space.emetric_space
import topology.bornology.constructions
import topology.uniform_space.complete_separated

/-!
# Metric spaces

This file defines metric spaces. Many definitions and theorems expected
on metric spaces are already introduced on uniform spaces and topological spaces.
For example: open and closed sets, compactness, completeness, continuity and uniform continuity

## Main definitions

* `has_dist α`: Endows a space `α` with a function `dist a b`.
* `pseudo_metric_space α`: A space endowed with a distance function, which can
  be zero even if the two elements are non-equal.
* `metric.ball x ε`: The set of all points `y` with `dist y x < ε`.
* `metric.bounded s`: Whether a subset of a `pseudo_metric_space` is bounded.
* `metric_space α`: A `pseudo_metric_space` with the guarantee `dist x y = 0 → x = y`.

Additional useful definitions:

* `nndist a b`: `dist` as a function to the non-negative reals.
* `metric.closed_ball x ε`: The set of all points `y` with `dist y x ≤ ε`.
* `metric.sphere x ε`: The set of all points `y` with `dist y x = ε`.
* `proper_space α`: A `pseudo_metric_space` where all closed balls are compact.
* `metric.diam s` : The `supr` of the distances of members of `s`.
  Defined in terms of `emetric.diam`, for better handling of the case when it should be infinite.

TODO (anyone): Add "Main results" section.

## Implementation notes

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory of `pseudo_metric_space`, where we don't require `dist x y = 0 → x = y` and we specialize
to `metric_space` at the end.

## Tags

metric, pseudo_metric, dist
-/

open set filter topological_space bornology

open_locale uniformity topological_space big_operators filter nnreal ennreal

universes u v w
variables {α : Type u} {β : Type v} {X ι : Type*}

/-- Construct a uniform structure core from a distance function and metric space axioms.
This is a technical construction that can be immediately used to construct a uniform structure
from a distance function and metric space axioms but is also useful when discussing
metrizable topologies, see `pseudo_metric_space.of_metrizable`. -/
def uniform_space.core_of_dist {α : Type*} (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : uniform_space.core α :=
{ uniformity := (⨅ ε>0, 𝓟 {p:α×α | dist p.1 p.2 < ε}),
  refl       := le_infi $ assume ε, le_infi $
    by simp [set.subset_def, id_rel, dist_self, (>)] {contextual := tt},
  comp       := le_infi $ assume ε, le_infi $ assume h, lift'_le
    (mem_infi_of_mem (ε / 2) $ mem_infi_of_mem (div_pos h zero_lt_two) (subset.refl _)) $
    have ∀ (a b c : α), dist a c < ε / 2 → dist c b < ε / 2 → dist a b < ε,
      from assume a b c hac hcb,
      calc dist a b ≤ dist a c + dist c b : dist_triangle _ _ _
        ... < ε / 2 + ε / 2 : add_lt_add hac hcb
        ... = ε : by rw [div_add_div_same, add_self_div_two],
    by simpa [comp_rel],
  symm       := tendsto_infi.2 $ assume ε, tendsto_infi.2 $ assume h,
    tendsto_infi' ε $ tendsto_infi' h $ tendsto_principal_principal.2 $ by simp [dist_comm] }

/-- Construct a uniform structure from a distance function and metric space axioms -/
def uniform_space_of_dist
  (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : uniform_space α :=
uniform_space.of_core (uniform_space.core_of_dist dist dist_self dist_comm dist_triangle)

/-- This is an internal lemma used to construct a bornology from a metric in `bornology.of_dist`. -/
private lemma bounded_iff_aux {α : Type*} (dist : α → α → ℝ)
  (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
  (s : set α) (a : α) :
  (∃ c, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ c) ↔ (∃ r, ∀ ⦃x⦄, x ∈ s → dist x a ≤ r) :=
begin
  split; rintro ⟨C, hC⟩,
  { rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩,
    { exact ⟨0, by simp⟩ },
    { exact ⟨C + dist x a, λ y hy,
             (dist_triangle y x a).trans (add_le_add_right (hC hy hx) _)⟩ } },
  { exact ⟨C + C, λ x hx y hy,
           (dist_triangle x a y).trans (add_le_add (hC hx) (by {rw dist_comm, exact hC hy}))⟩ }
end

/-- Construct a bornology from a distance function and metric space axioms. -/
def bornology.of_dist {α : Type*} (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) :
  bornology α :=
bornology.of_bounded
  { s : set α | ∃ C, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C }
  ⟨0, λ x hx y, hx.elim⟩
  (λ s ⟨c, hc⟩ t h, ⟨c, λ x hx y hy, hc (h hx) (h hy)⟩)
  (λ s hs t ht,
    begin
      rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩,
      { exact (empty_union t).symm ▸ ht },
      { simp only [λ u, bounded_iff_aux dist dist_comm dist_triangle u z] at hs ht ⊢,
        rcases ⟨hs, ht⟩ with ⟨⟨r₁, hr₁⟩, ⟨r₂, hr₂⟩⟩,
        exact ⟨max r₁ r₂, λ x hx, or.elim hx
          (λ hx', (hr₁ hx').trans (le_max_left _ _))
          (λ hx', (hr₂ hx').trans (le_max_right _ _))⟩ }
    end)
  (λ z, ⟨0, λ x hx y hy,
    by { rw [eq_of_mem_singleton hx, eq_of_mem_singleton hy], exact (dist_self z).le }⟩)

/-- The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`. -/
@[ext] class has_dist (α : Type*) := (dist : α → α → ℝ)

export has_dist (dist)

-- the uniform structure and the emetric space structure are embedded in the metric space structure
-- to avoid instance diamond issues. See Note [forgetful inheritance].

/-- This is an internal lemma used inside the default of `pseudo_metric_space.edist`. -/
private theorem pseudo_metric_space.dist_nonneg' {α} {x y : α} (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z): 0 ≤ dist x y :=
have 2 * dist x y ≥ 0,
  from calc 2 * dist x y = dist x y + dist y x : by rw [dist_comm x y, two_mul]
    ... ≥ 0 : by rw ← dist_self x; apply dist_triangle,
nonneg_of_mul_nonneg_right this zero_lt_two

/-- This tactic is used to populate `pseudo_metric_space.edist_dist` when the default `edist` is
used. -/
protected meta def pseudo_metric_space.edist_dist_tac : tactic unit :=
tactic.intros >> `[exact (ennreal.of_real_eq_coe_nnreal _).symm <|> control_laws_tac]

/-- Pseudo metric and Metric spaces

A pseudo metric space is endowed with a distance for which the requirement `d(x,y)=0 → x = y` might
not hold. A metric space is a pseudo metric space such that `d(x,y)=0 → x = y`.
Each pseudo metric space induces a canonical `uniform_space` and hence a canonical
`topological_space` This is enforced in the type class definition, by extending the `uniform_space`
structure. When instantiating a `pseudo_metric_space` structure, the uniformity fields are not
necessary, they will be filled in by default. In the same way, each (pseudo) metric space induces a
(pseudo) emetric space structure. It is included in the structure, but filled in by default.
-/
class pseudo_metric_space (α : Type u) extends has_dist α : Type u :=
(dist_self : ∀ x : α, dist x x = 0)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
(edist : α → α → ℝ≥0∞ := λ x y,
  @coe (ℝ≥0) _ _ ⟨dist x y, pseudo_metric_space.dist_nonneg' _ ‹_› ‹_› ‹_›⟩)
(edist_dist : ∀ x y : α,
  edist x y = ennreal.of_real (dist x y) . pseudo_metric_space.edist_dist_tac)
(to_uniform_space : uniform_space α := uniform_space_of_dist dist dist_self dist_comm dist_triangle)
(uniformity_dist : 𝓤 α = ⨅ ε>0, 𝓟 {p:α×α | dist p.1 p.2 < ε} . control_laws_tac)
(to_bornology : bornology α := bornology.of_dist dist dist_self dist_comm dist_triangle)
(cobounded_sets : (bornology.cobounded α).sets =
  { s | ∃ C, ∀ ⦃x⦄, x ∈ sᶜ → ∀ ⦃y⦄, y ∈ sᶜ → dist x y ≤ C } . control_laws_tac)

/-- Two pseudo metric space structures with the same distance function coincide. -/
@[ext] lemma pseudo_metric_space.ext {α : Type*} {m m' : pseudo_metric_space α}
  (h : m.to_has_dist = m'.to_has_dist) : m = m' :=
begin
  unfreezingI { rcases m, rcases m' },
  dsimp at h,
  unfreezingI { subst h },
  congr,
  { ext x y : 2,
    dsimp at m_edist_dist m'_edist_dist,
    simp [m_edist_dist, m'_edist_dist] },
  { dsimp at m_uniformity_dist m'_uniformity_dist,
    rw ← m'_uniformity_dist at m_uniformity_dist,
    exact uniform_space_eq m_uniformity_dist },
  { ext1,
    dsimp at m_cobounded_sets m'_cobounded_sets,
    rw ← m'_cobounded_sets at m_cobounded_sets,
    exact filter_eq m_cobounded_sets }
end

variables [pseudo_metric_space α]

attribute [priority 100, instance] pseudo_metric_space.to_uniform_space
attribute [priority 100, instance] pseudo_metric_space.to_bornology

@[priority 200] -- see Note [lower instance priority]
instance pseudo_metric_space.to_has_edist : has_edist α := ⟨pseudo_metric_space.edist⟩

/-- Construct a pseudo-metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def pseudo_metric_space.of_metrizable {α : Type*} [topological_space α] (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
  (H : ∀ s : set α, is_open s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s) :
  pseudo_metric_space α :=
{ dist := dist,
  dist_self := dist_self,
  dist_comm := dist_comm,
  dist_triangle := dist_triangle,
  to_uniform_space := { is_open_uniformity := begin
    dsimp only [uniform_space.core_of_dist],
    intros s,
    change is_open s ↔ _,
    rw H s,
    refine forall₂_congr (λ x x_in, _),
    erw (has_basis_binfi_principal _ nonempty_Ioi).mem_iff,
    { refine exists₂_congr (λ ε ε_pos, _),
      simp only [prod.forall, set_of_subset_set_of],
      split,
      { rintros h _ y H rfl,
        exact h y H },
      { intros h y hxy,
        exact h _ _ hxy rfl } },
    { exact λ r (hr : 0 < r) p (hp : 0 < p), ⟨min r p, lt_min hr hp,
      λ x (hx : dist _ _ < _), lt_of_lt_of_le hx (min_le_left r p),
      λ x (hx : dist _ _ < _), lt_of_lt_of_le hx (min_le_right r p)⟩ },
    { apply_instance }
    end,
    ..uniform_space.core_of_dist dist dist_self dist_comm dist_triangle },
  uniformity_dist := rfl,
  to_bornology := bornology.of_dist dist dist_self dist_comm dist_triangle,
  cobounded_sets := rfl }

@[simp] theorem dist_self (x : α) : dist x x = 0 := pseudo_metric_space.dist_self x

theorem dist_comm (x y : α) : dist x y = dist y x := pseudo_metric_space.dist_comm x y

theorem edist_dist (x y : α) : edist x y = ennreal.of_real (dist x y) :=
pseudo_metric_space.edist_dist x y

theorem dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z :=
pseudo_metric_space.dist_triangle x y z

theorem dist_triangle_left (x y z : α) : dist x y ≤ dist z x + dist z y :=
by rw dist_comm z; apply dist_triangle

theorem dist_triangle_right (x y z : α) : dist x y ≤ dist x z + dist y z :=
by rw dist_comm y; apply dist_triangle

lemma dist_triangle4 (x y z w : α) :
  dist x w ≤ dist x y + dist y z + dist z w :=
calc dist x w ≤ dist x z + dist z w : dist_triangle x z w
          ... ≤ (dist x y + dist y z) + dist z w : add_le_add_right (dist_triangle x y z) _

lemma dist_triangle4_left (x₁ y₁ x₂ y₂ : α) :
  dist x₂ y₂ ≤ dist x₁ y₁ + (dist x₁ x₂ + dist y₁ y₂) :=
by { rw [add_left_comm, dist_comm x₁, ← add_assoc], apply dist_triangle4 }

lemma dist_triangle4_right (x₁ y₁ x₂ y₂ : α) :
  dist x₁ y₁ ≤ dist x₁ x₂ + dist y₁ y₂ + dist x₂ y₂ :=
by { rw [add_right_comm, dist_comm y₁], apply dist_triangle4 }

/-- The triangle (polygon) inequality for sequences of points; `finset.Ico` version. -/
lemma dist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
  dist (f m) (f n) ≤ ∑ i in finset.Ico m n, dist (f i) (f (i + 1)) :=
begin
  revert n,
  apply nat.le_induction,
  { simp only [finset.sum_empty, finset.Ico_self, dist_self] },
  { assume n hn hrec,
    calc dist (f m) (f (n+1)) ≤ dist (f m) (f n) + dist _ _ : dist_triangle _ _ _
      ... ≤ ∑ i in finset.Ico m n, _ + _ : add_le_add hrec le_rfl
      ... = ∑ i in finset.Ico m (n+1), _ :
        by rw [nat.Ico_succ_right_eq_insert_Ico hn, finset.sum_insert, add_comm]; simp }
end

/-- The triangle (polygon) inequality for sequences of points; `finset.range` version. -/
lemma dist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
  dist (f 0) (f n) ≤ ∑ i in finset.range n, dist (f i) (f (i + 1)) :=
nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_dist f (nat.zero_le n)

/-- A version of `dist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
lemma dist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n)
  {d : ℕ → ℝ} (hd : ∀ {k}, m ≤ k → k < n → dist (f k) (f (k + 1)) ≤ d k) :
  dist (f m) (f n) ≤ ∑ i in finset.Ico m n, d i :=
le_trans (dist_le_Ico_sum_dist f hmn) $
finset.sum_le_sum $ λ k hk, hd (finset.mem_Ico.1 hk).1 (finset.mem_Ico.1 hk).2

/-- A version of `dist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
lemma dist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ)
  {d : ℕ → ℝ} (hd : ∀ {k}, k < n → dist (f k) (f (k + 1)) ≤ d k) :
  dist (f 0) (f n) ≤ ∑ i in finset.range n, d i :=
nat.Ico_zero_eq_range ▸ dist_le_Ico_sum_of_dist_le (zero_le n) (λ _ _, hd)

theorem swap_dist : function.swap (@dist α _) = dist :=
by funext x y; exact dist_comm _ _

theorem abs_dist_sub_le (x y z : α) : |dist x z - dist y z| ≤ dist x y :=
abs_sub_le_iff.2
 ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _),
  sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩

theorem dist_nonneg {x y : α} : 0 ≤ dist x y :=
pseudo_metric_space.dist_nonneg' dist dist_self dist_comm dist_triangle

section
open tactic tactic.positivity

/-- Extension for the `positivity` tactic: distances are nonnegative. -/
@[positivity]
meta def _root_.tactic.positivity_dist : expr → tactic strictness
| `(dist %%a %%b) := nonnegative <$> mk_app ``dist_nonneg [a, b]
| _ := failed

end

@[simp] theorem abs_dist {a b : α} : |dist a b| = dist a b :=
abs_of_nonneg dist_nonneg

/-- A version of `has_dist` that takes value in `ℝ≥0`. -/
class has_nndist (α : Type*) := (nndist : α → α → ℝ≥0)

export has_nndist (nndist)

/-- Distance as a nonnegative real number. -/
@[priority 100] -- see Note [lower instance priority]
instance pseudo_metric_space.to_has_nndist : has_nndist α := ⟨λ a b, ⟨dist a b, dist_nonneg⟩⟩

/--Express `nndist` in terms of `edist`-/
lemma nndist_edist (x y : α) : nndist x y = (edist x y).to_nnreal :=
by simp [nndist, edist_dist, real.to_nnreal, max_eq_left dist_nonneg, ennreal.of_real]

/--Express `edist` in terms of `nndist`-/
lemma edist_nndist (x y : α) : edist x y = ↑(nndist x y) :=
by { simpa only [edist_dist, ennreal.of_real_eq_coe_nnreal dist_nonneg] }

@[simp, norm_cast] lemma coe_nnreal_ennreal_nndist (x y : α) : ↑(nndist x y) = edist x y :=
(edist_nndist x y).symm

@[simp, norm_cast] lemma edist_lt_coe {x y : α} {c : ℝ≥0} :
  edist x y < c ↔ nndist x y < c :=
by rw [edist_nndist, ennreal.coe_lt_coe]

@[simp, norm_cast] lemma edist_le_coe {x y : α} {c : ℝ≥0} :
  edist x y ≤ c ↔ nndist x y ≤ c :=
by rw [edist_nndist, ennreal.coe_le_coe]

/--In a pseudometric space, the extended distance is always finite-/
lemma edist_lt_top {α : Type*} [pseudo_metric_space α] (x y : α) : edist x y < ⊤ :=
(edist_dist x y).symm ▸ ennreal.of_real_lt_top

/--In a pseudometric space, the extended distance is always finite-/
lemma edist_ne_top (x y : α) : edist x y ≠ ⊤ := (edist_lt_top x y).ne

/--`nndist x x` vanishes-/
@[simp] lemma nndist_self (a : α) : nndist a a = 0 := (nnreal.coe_eq_zero _).1 (dist_self a)

/--Express `dist` in terms of `nndist`-/
lemma dist_nndist (x y : α) : dist x y = ↑(nndist x y) := rfl

@[simp, norm_cast] lemma coe_nndist (x y : α) : ↑(nndist x y) = dist x y :=
(dist_nndist x y).symm

@[simp, norm_cast] lemma dist_lt_coe {x y : α} {c : ℝ≥0} :
  dist x y < c ↔ nndist x y < c :=
iff.rfl

@[simp, norm_cast] lemma dist_le_coe {x y : α} {c : ℝ≥0} :
  dist x y ≤ c ↔ nndist x y ≤ c :=
iff.rfl

@[simp] lemma edist_lt_of_real {x y : α} {r : ℝ} : edist x y < ennreal.of_real r ↔ dist x y < r :=
by rw [edist_dist, ennreal.of_real_lt_of_real_iff_of_nonneg dist_nonneg]

@[simp] lemma edist_le_of_real {x y : α} {r : ℝ} (hr : 0 ≤ r) :
  edist x y ≤ ennreal.of_real r ↔ dist x y ≤ r :=
by rw [edist_dist, ennreal.of_real_le_of_real_iff hr]

/--Express `nndist` in terms of `dist`-/
lemma nndist_dist (x y : α) : nndist x y = real.to_nnreal (dist x y) :=
by rw [dist_nndist, real.to_nnreal_coe]

theorem nndist_comm (x y : α) : nndist x y = nndist y x :=
by simpa only [dist_nndist, nnreal.coe_eq] using dist_comm x y

/--Triangle inequality for the nonnegative distance-/
theorem nndist_triangle (x y z : α) : nndist x z ≤ nndist x y + nndist y z :=
dist_triangle _ _ _

theorem nndist_triangle_left (x y z : α) : nndist x y ≤ nndist z x + nndist z y :=
dist_triangle_left _ _ _

theorem nndist_triangle_right (x y z : α) : nndist x y ≤ nndist x z + nndist y z :=
dist_triangle_right _ _ _

/--Express `dist` in terms of `edist`-/
lemma dist_edist (x y : α) : dist x y = (edist x y).to_real :=
by rw [edist_dist, ennreal.to_real_of_real (dist_nonneg)]

namespace metric

/- instantiate pseudometric space as a topology -/
variables {x y z : α} {δ ε ε₁ ε₂ : ℝ} {s : set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : α) (ε : ℝ) : set α := {y | dist y x < ε}

@[simp] theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε := iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ dist x y < ε := by rw [dist_comm, mem_ball]

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
dist_nonneg.trans_lt hy

theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε :=
show dist x x < ε, by rw dist_self; assumption

@[simp] lemma nonempty_ball : (ball x ε).nonempty ↔ 0 < ε :=
⟨λ ⟨x, hx⟩, pos_of_mem_ball hx, λ h, ⟨x, mem_ball_self h⟩⟩

@[simp] lemma ball_eq_empty : ball x ε = ∅ ↔ ε ≤ 0 :=
by rw [← not_nonempty_iff_eq_empty, nonempty_ball, not_lt]

@[simp] lemma ball_zero : ball x 0 = ∅ :=
by rw [ball_eq_empty]

/-- If a point belongs to an open ball, then there is a strictly smaller radius whose ball also
contains it.

See also `exists_lt_subset_ball`. -/
lemma exists_lt_mem_ball_of_mem_ball (h : x ∈ ball y ε) : ∃ ε' < ε, x ∈ ball y ε' :=
begin
  simp only [mem_ball] at h ⊢,
  exact ⟨(ε + dist x y) / 2, by linarith, by linarith⟩,
end

lemma ball_eq_ball (ε : ℝ) (x : α) :
  uniform_space.ball x {p | dist p.2 p.1 < ε} = metric.ball x ε := rfl

lemma ball_eq_ball' (ε : ℝ) (x : α) :
  uniform_space.ball x {p | dist p.1 p.2 < ε} = metric.ball x ε :=
by { ext, simp [dist_comm, uniform_space.ball] }

@[simp] lemma Union_ball_nat (x : α) : (⋃ n : ℕ, ball x n) = univ :=
Union_eq_univ_iff.2 $ λ y, exists_nat_gt (dist y x)

@[simp] lemma Union_ball_nat_succ (x : α) : (⋃ n : ℕ, ball x (n + 1)) = univ :=
Union_eq_univ_iff.2 $ λ y, (exists_nat_gt (dist y x)).imp $ λ n hn,
  hn.trans (lt_add_one _)

/-- `closed_ball x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closed_ball (x : α) (ε : ℝ) := {y | dist y x ≤ ε}

@[simp] theorem mem_closed_ball : y ∈ closed_ball x ε ↔ dist y x ≤ ε := iff.rfl

theorem mem_closed_ball' : y ∈ closed_ball x ε ↔ dist x y ≤ ε := by rw [dist_comm, mem_closed_ball]

/-- `sphere x ε` is the set of all points `y` with `dist y x = ε` -/
def sphere (x : α) (ε : ℝ) := {y | dist y x = ε}

@[simp] theorem mem_sphere : y ∈ sphere x ε ↔ dist y x = ε := iff.rfl

theorem mem_sphere' : y ∈ sphere x ε ↔ dist x y = ε := by rw [dist_comm, mem_sphere]

theorem ne_of_mem_sphere (h : y ∈ sphere x ε) (hε : ε ≠ 0) : y ≠ x :=
by { contrapose! hε, symmetry, simpa [hε] using h  }

theorem sphere_eq_empty_of_subsingleton [subsingleton α] (hε : ε ≠ 0) :
  sphere x ε = ∅ :=
set.eq_empty_iff_forall_not_mem.mpr $ λ y hy, ne_of_mem_sphere hy hε (subsingleton.elim _ _)

theorem sphere_is_empty_of_subsingleton [subsingleton α] (hε : ε ≠ 0) :
  is_empty (sphere x ε) :=
by simp only [sphere_eq_empty_of_subsingleton hε, set.has_emptyc.emptyc.is_empty α]

theorem mem_closed_ball_self (h : 0 ≤ ε) : x ∈ closed_ball x ε :=
show dist x x ≤ ε, by rw dist_self; assumption

@[simp] lemma nonempty_closed_ball : (closed_ball x ε).nonempty ↔ 0 ≤ ε :=
⟨λ ⟨x, hx⟩, dist_nonneg.trans hx, λ h, ⟨x, mem_closed_ball_self h⟩⟩

@[simp] lemma closed_ball_eq_empty : closed_ball x ε = ∅ ↔ ε < 0 :=
by rw [← not_nonempty_iff_eq_empty, nonempty_closed_ball, not_le]

theorem ball_subset_closed_ball : ball x ε ⊆ closed_ball x ε :=
assume y (hy : _ < _), le_of_lt hy

theorem sphere_subset_closed_ball : sphere x ε ⊆ closed_ball x ε :=
λ y, le_of_eq

lemma closed_ball_disjoint_ball (h : δ + ε ≤ dist x y) : disjoint (closed_ball x δ) (ball y ε) :=
set.disjoint_left.mpr $
  λ a ha1 ha2, (h.trans $ dist_triangle_left _ _ _).not_lt $ add_lt_add_of_le_of_lt ha1 ha2

lemma ball_disjoint_closed_ball (h : δ + ε ≤ dist x y) : disjoint (ball x δ) (closed_ball y ε) :=
(closed_ball_disjoint_ball $ by rwa [add_comm, dist_comm]).symm

lemma ball_disjoint_ball (h : δ + ε ≤ dist x y) : disjoint (ball x δ) (ball y ε) :=
(closed_ball_disjoint_ball h).mono_left ball_subset_closed_ball

lemma closed_ball_disjoint_closed_ball (h : δ + ε < dist x y) :
  disjoint (closed_ball x δ) (closed_ball y ε) :=
set.disjoint_left.mpr $
  λ a ha1 ha2, h.not_le $ (dist_triangle_left _ _ _).trans $ add_le_add ha1 ha2

theorem sphere_disjoint_ball : disjoint (sphere x ε) (ball x ε) :=
set.disjoint_left.mpr $ λ y hy₁ hy₂, absurd hy₁ $ ne_of_lt hy₂

@[simp] theorem ball_union_sphere : ball x ε ∪ sphere x ε = closed_ball x ε :=
set.ext $ λ y, (@le_iff_lt_or_eq ℝ _ _ _).symm

@[simp] theorem sphere_union_ball : sphere x ε ∪ ball x ε = closed_ball x ε :=
by rw [union_comm, ball_union_sphere]

@[simp] theorem closed_ball_diff_sphere : closed_ball x ε \ sphere x ε = ball x ε :=
by rw [← ball_union_sphere, set.union_diff_cancel_right sphere_disjoint_ball.symm.le_bot]

@[simp] theorem closed_ball_diff_ball : closed_ball x ε \ ball x ε = sphere x ε :=
by rw [← ball_union_sphere, set.union_diff_cancel_left sphere_disjoint_ball.symm.le_bot]

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε :=
by rw [mem_ball', mem_ball]

theorem mem_closed_ball_comm : x ∈ closed_ball y ε ↔ y ∈ closed_ball x ε :=
by rw [mem_closed_ball', mem_closed_ball]

theorem mem_sphere_comm : x ∈ sphere y ε ↔ y ∈ sphere x ε :=
by rw [mem_sphere', mem_sphere]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
λ y (yx : _ < ε₁), lt_of_lt_of_le yx h

lemma closed_ball_eq_bInter_ball : closed_ball x ε = ⋂ δ > ε, ball x δ :=
by ext y; rw [mem_closed_ball, ← forall_lt_iff_le', mem_Inter₂]; refl

lemma ball_subset_ball' (h : ε₁ + dist x y ≤ ε₂) : ball x ε₁ ⊆ ball y ε₂ :=
λ z hz, calc
  dist z y ≤ dist z x + dist x y : dist_triangle _ _ _
  ... < ε₁ + dist x y : add_lt_add_right hz _
  ... ≤ ε₂ : h

theorem closed_ball_subset_closed_ball (h : ε₁ ≤ ε₂) :
  closed_ball x ε₁ ⊆ closed_ball x ε₂ :=
λ y (yx : _ ≤ ε₁), le_trans yx h

lemma closed_ball_subset_closed_ball' (h : ε₁ + dist x y ≤ ε₂) :
  closed_ball x ε₁ ⊆ closed_ball y ε₂ :=
λ z hz, calc
  dist z y ≤ dist z x + dist x y : dist_triangle _ _ _
  ... ≤ ε₁ + dist x y : add_le_add_right hz _
  ... ≤ ε₂ : h

theorem closed_ball_subset_ball (h : ε₁ < ε₂) :
  closed_ball x ε₁ ⊆ ball x ε₂ :=
λ y (yh : dist y x ≤ ε₁), lt_of_le_of_lt yh h

lemma closed_ball_subset_ball' (h : ε₁ + dist x y < ε₂) :
  closed_ball x ε₁ ⊆ ball y ε₂ :=
λ z hz, calc
  dist z y ≤ dist z x + dist x y : dist_triangle _ _ _
  ... ≤ ε₁ + dist x y : add_le_add_right hz _
  ... < ε₂ : h

lemma dist_le_add_of_nonempty_closed_ball_inter_closed_ball
  (h : (closed_ball x ε₁ ∩ closed_ball y ε₂).nonempty) :
  dist x y ≤ ε₁ + ε₂ :=
let ⟨z, hz⟩ := h in calc
  dist x y ≤ dist z x + dist z y : dist_triangle_left _ _ _
  ... ≤ ε₁ + ε₂ : add_le_add hz.1 hz.2

lemma dist_lt_add_of_nonempty_closed_ball_inter_ball (h : (closed_ball x ε₁ ∩ ball y ε₂).nonempty) :
  dist x y < ε₁ + ε₂ :=
let ⟨z, hz⟩ := h in calc
  dist x y ≤ dist z x + dist z y : dist_triangle_left _ _ _
  ... < ε₁ + ε₂ : add_lt_add_of_le_of_lt hz.1 hz.2

lemma dist_lt_add_of_nonempty_ball_inter_closed_ball (h : (ball x ε₁ ∩ closed_ball y ε₂).nonempty) :
  dist x y < ε₁ + ε₂ :=
begin
  rw inter_comm at h,
  rw [add_comm, dist_comm],
  exact dist_lt_add_of_nonempty_closed_ball_inter_ball h
end

lemma dist_lt_add_of_nonempty_ball_inter_ball (h : (ball x ε₁ ∩ ball y ε₂).nonempty) :
  dist x y < ε₁ + ε₂ :=
dist_lt_add_of_nonempty_closed_ball_inter_ball $
  h.mono (inter_subset_inter ball_subset_closed_ball subset.rfl)

@[simp] lemma Union_closed_ball_nat (x : α) : (⋃ n : ℕ, closed_ball x n) = univ :=
Union_eq_univ_iff.2 $ λ y, exists_nat_ge (dist y x)

lemma Union_inter_closed_ball_nat (s : set α) (x : α) :
  (⋃ (n : ℕ), s ∩ closed_ball x n) = s :=
by rw [← inter_Union, Union_closed_ball_nat, inter_univ]

theorem ball_subset (h : dist x y ≤ ε₂ - ε₁) : ball x ε₁ ⊆ ball y ε₂ :=
λ z zx, by rw ← add_sub_cancel'_right ε₁ ε₂; exact
lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)

theorem ball_half_subset (y) (h : y ∈ ball x (ε / 2)) : ball y (ε / 2) ⊆ ball x ε :=
ball_subset $ by rw sub_self_div_two; exact le_of_lt h

theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
⟨_, sub_pos.2 h, ball_subset $ by rw sub_sub_self⟩

/-- If a property holds for all points in closed balls of arbitrarily large radii, then it holds for
all points. -/
lemma forall_of_forall_mem_closed_ball (p : α → Prop) (x : α)
  (H : ∃ᶠ (R : ℝ) in at_top, ∀ y ∈ closed_ball x R, p y) (y : α) :
  p y :=
begin
  obtain ⟨R, hR, h⟩ : ∃ (R : ℝ) (H : dist y x ≤ R), ∀ (z : α), z ∈ closed_ball x R → p z :=
    frequently_iff.1 H (Ici_mem_at_top (dist y x)),
  exact h _ hR
end

/-- If a property holds for all points in balls of arbitrarily large radii, then it holds for all
points. -/
lemma forall_of_forall_mem_ball (p : α → Prop) (x : α)
  (H : ∃ᶠ (R : ℝ) in at_top, ∀ y ∈ ball x R, p y) (y : α) :
  p y :=
begin
  obtain ⟨R, hR, h⟩ : ∃ (R : ℝ) (H : dist y x < R), ∀ (z : α), z ∈ ball x R → p z :=
    frequently_iff.1 H (Ioi_mem_at_top (dist y x)),
  exact h _ hR
end

theorem is_bounded_iff {s : set α} :
  is_bounded s ↔ ∃ C : ℝ, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C :=
by rw [is_bounded_def, ← filter.mem_sets, (@pseudo_metric_space.cobounded_sets α _).out,
  mem_set_of_eq, compl_compl]

theorem is_bounded_iff_eventually {s : set α} :
  is_bounded s ↔ ∀ᶠ C in at_top, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C :=
is_bounded_iff.trans ⟨λ ⟨C, h⟩, eventually_at_top.2 ⟨C, λ C' hC' x hx y hy, (h hx hy).trans hC'⟩,
  eventually.exists⟩

theorem is_bounded_iff_exists_ge {s : set α} (c : ℝ) :
  is_bounded s ↔ ∃ C, c ≤ C ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → dist x y ≤ C :=
⟨λ h, ((eventually_ge_at_top c).and (is_bounded_iff_eventually.1 h)).exists,
  λ h, is_bounded_iff.2 $ h.imp $ λ _, and.right⟩

theorem is_bounded_iff_nndist {s : set α} :
  is_bounded s ↔ ∃ C : ℝ≥0, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → nndist x y ≤ C :=
by simp only [is_bounded_iff_exists_ge 0, nnreal.exists, ← nnreal.coe_le_coe, ← dist_nndist,
  nnreal.coe_mk, exists_prop]

theorem uniformity_basis_dist :
  (𝓤 α).has_basis (λ ε : ℝ, 0 < ε) (λ ε, {p:α×α | dist p.1 p.2 < ε}) :=
begin
  rw ← pseudo_metric_space.uniformity_dist.symm,
  refine has_basis_binfi_principal _ nonempty_Ioi,
  exact λ r (hr : 0 < r) p (hp : 0 < p), ⟨min r p, lt_min hr hp,
     λ x (hx : dist _ _ < _), lt_of_lt_of_le hx (min_le_left r p),
     λ x (hx : dist _ _ < _), lt_of_lt_of_le hx (min_le_right r p)⟩
end

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then `f i`-neighborhoods of the diagonal form a basis of `𝓤 α`.

For specific bases see `uniformity_basis_dist`, `uniformity_basis_dist_inv_nat_succ`,
and `uniformity_basis_dist_inv_nat_pos`. -/
protected theorem mk_uniformity_basis {β : Type*} {p : β → Prop} {f : β → ℝ}
  (hf₀ : ∀ i, p i → 0 < f i) (hf : ∀ ⦃ε⦄, 0 < ε → ∃ i (hi : p i), f i ≤ ε) :
  (𝓤 α).has_basis p (λ i, {p:α×α | dist p.1 p.2 < f i}) :=
begin
  refine ⟨λ s, uniformity_basis_dist.mem_iff.trans _⟩,
  split,
  { rintros ⟨ε, ε₀, hε⟩,
    obtain ⟨i, hi, H⟩ : ∃ i (hi : p i), f i ≤ ε, from hf ε₀,
    exact ⟨i, hi, λ x (hx : _ < _), hε $ lt_of_lt_of_le hx H⟩ },
  { exact λ ⟨i, hi, H⟩, ⟨f i, hf₀ i hi, H⟩ }
end

theorem uniformity_basis_dist_inv_nat_succ :
  (𝓤 α).has_basis (λ _, true) (λ n:ℕ, {p:α×α | dist p.1 p.2 < 1 / (↑n+1) }) :=
metric.mk_uniformity_basis (λ n _, div_pos zero_lt_one $ nat.cast_add_one_pos n)
  (λ ε ε0, (exists_nat_one_div_lt ε0).imp $ λ n hn, ⟨trivial, le_of_lt hn⟩)

theorem uniformity_basis_dist_inv_nat_pos :
  (𝓤 α).has_basis (λ n:ℕ, 0<n) (λ n:ℕ, {p:α×α | dist p.1 p.2 < 1 / ↑n }) :=
metric.mk_uniformity_basis (λ n hn, div_pos zero_lt_one $ nat.cast_pos.2 hn)
  (λ ε ε0, let ⟨n, hn⟩ := exists_nat_one_div_lt ε0 in ⟨n+1, nat.succ_pos n,
    by exact_mod_cast hn.le⟩)

theorem uniformity_basis_dist_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
  (𝓤 α).has_basis (λ n:ℕ, true) (λ n:ℕ, {p:α×α | dist p.1 p.2 < r ^ n }) :=
metric.mk_uniformity_basis (λ n hn, pow_pos h0 _)
  (λ ε ε0, let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1 in ⟨n, trivial, hn.le⟩)

theorem uniformity_basis_dist_lt {R : ℝ} (hR : 0 < R) :
  (𝓤 α).has_basis (λ r : ℝ, 0 < r ∧ r < R) (λ r, {p : α × α | dist p.1 p.2 < r}) :=
metric.mk_uniformity_basis (λ r, and.left) $ λ r hr,
  ⟨min r (R / 2), ⟨lt_min hr (half_pos hR), min_lt_iff.2 $ or.inr (half_lt_self hR)⟩,
    min_le_left _ _⟩

/-- Given `f : β → ℝ`, if `f` sends `{i | p i}` to a set of positive numbers
accumulating to zero, then closed neighborhoods of the diagonal of sizes `{f i | p i}`
form a basis of `𝓤 α`.

Currently we have only one specific basis `uniformity_basis_dist_le` based on this constructor.
More can be easily added if needed in the future. -/
protected theorem mk_uniformity_basis_le {β : Type*} {p : β → Prop} {f : β → ℝ}
  (hf₀ : ∀ x, p x → 0 < f x) (hf : ∀ ε, 0 < ε → ∃ x (hx : p x), f x ≤ ε) :
  (𝓤 α).has_basis p (λ x, {p:α×α | dist p.1 p.2 ≤ f x}) :=
begin
  refine ⟨λ s, uniformity_basis_dist.mem_iff.trans _⟩,
  split,
  { rintros ⟨ε, ε₀, hε⟩,
    rcases exists_between ε₀ with ⟨ε', hε'⟩,
    rcases hf ε' hε'.1 with ⟨i, hi, H⟩,
    exact ⟨i, hi, λ x (hx : _ ≤ _), hε $ lt_of_le_of_lt (le_trans hx H) hε'.2⟩ },
  { exact λ ⟨i, hi, H⟩, ⟨f i, hf₀ i hi, λ x (hx : _ < _), H (le_of_lt hx)⟩ }
end

/-- Contant size closed neighborhoods of the diagonal form a basis
of the uniformity filter. -/
theorem uniformity_basis_dist_le :
  (𝓤 α).has_basis (λ ε : ℝ, 0 < ε) (λ ε, {p:α×α | dist p.1 p.2 ≤ ε}) :=
metric.mk_uniformity_basis_le (λ _, id) (λ ε ε₀, ⟨ε, ε₀, le_refl ε⟩)

theorem uniformity_basis_dist_le_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
  (𝓤 α).has_basis (λ n:ℕ, true) (λ n:ℕ, {p:α×α | dist p.1 p.2 ≤ r ^ n }) :=
metric.mk_uniformity_basis_le (λ n hn, pow_pos h0 _)
  (λ ε ε0, let ⟨n, hn⟩ := exists_pow_lt_of_lt_one ε0 h1 in ⟨n, trivial, hn.le⟩)

theorem mem_uniformity_dist {s : set (α×α)} :
  s ∈ 𝓤 α ↔ (∃ε>0, ∀{a b:α}, dist a b < ε → (a, b) ∈ s) :=
uniformity_basis_dist.mem_uniformity_iff

/-- A constant size neighborhood of the diagonal is an entourage. -/
theorem dist_mem_uniformity {ε:ℝ} (ε0 : 0 < ε) :
  {p:α×α | dist p.1 p.2 < ε} ∈ 𝓤 α :=
mem_uniformity_dist.2 ⟨ε, ε0, λ a b, id⟩

theorem uniform_continuous_iff [pseudo_metric_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0,
    ∀{a b:α}, dist a b < δ → dist (f a) (f b) < ε :=
uniformity_basis_dist.uniform_continuous_iff uniformity_basis_dist

lemma uniform_continuous_on_iff [pseudo_metric_space β] {f : α → β} {s : set α} :
  uniform_continuous_on f s ↔ ∀ ε > 0, ∃ δ > 0, ∀ x y ∈ s, dist x y < δ → dist (f x) (f y) < ε :=
metric.uniformity_basis_dist.uniform_continuous_on_iff metric.uniformity_basis_dist

lemma uniform_continuous_on_iff_le [pseudo_metric_space β] {f : α → β} {s : set α} :
  uniform_continuous_on f s ↔ ∀ ε > 0, ∃ δ > 0, ∀ x y ∈ s, dist x y ≤ δ → dist (f x) (f y) ≤ ε :=
metric.uniformity_basis_dist_le.uniform_continuous_on_iff metric.uniformity_basis_dist_le

theorem uniform_embedding_iff [pseudo_metric_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ uniform_continuous f ∧
    ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
uniform_embedding_def'.trans $ and_congr iff.rfl $ and_congr iff.rfl
⟨λ H δ δ0, let ⟨t, tu, ht⟩ := H _ (dist_mem_uniformity δ0),
               ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 tu in
  ⟨ε, ε0, λ a b h, ht _ _ (hε h)⟩,
 λ H s su, let ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 su, ⟨ε, ε0, hε⟩ := H _ δ0 in
  ⟨_, dist_mem_uniformity ε0, λ a b h, hδ (hε h)⟩⟩

/-- If a map between pseudometric spaces is a uniform embedding then the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_uniform_embedding [pseudo_metric_space β] {f : α → β} :
  uniform_embedding f →
  (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
  (∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ) :=
begin
  assume h,
  exact ⟨uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1, (uniform_embedding_iff.1 h).2.2⟩
end

theorem totally_bounded_iff {s : set α} :
  totally_bounded s ↔ ∀ ε > 0, ∃t : set α, t.finite ∧ s ⊆ ⋃y∈t, ball y ε :=
⟨λ H ε ε0, H _ (dist_mem_uniformity ε0),
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru,
               ⟨t, ft, h⟩ := H ε ε0 in
  ⟨t, ft, h.trans $ Union₂_mono $ λ y yt z, hε⟩⟩

/-- A pseudometric space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data. -/
lemma totally_bounded_of_finite_discretization {s : set α}
  (H : ∀ε > (0 : ℝ), ∃ (β : Type u) (_ : fintype β) (F : s → β),
    ∀x y, F x = F y → dist (x:α) y < ε) :
  totally_bounded s :=
begin
  cases s.eq_empty_or_nonempty with hs hs,
  { rw hs, exact totally_bounded_empty },
  rcases hs with ⟨x0, hx0⟩,
  haveI : inhabited s := ⟨⟨x0, hx0⟩⟩,
  refine totally_bounded_iff.2 (λ ε ε0, _),
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩,
  resetI,
  let Finv := function.inv_fun F,
  refine ⟨range (subtype.val ∘ Finv), finite_range _, λ x xs, _⟩,
  let x' := Finv (F ⟨x, xs⟩),
  have : F x' = F ⟨x, xs⟩ := function.inv_fun_eq ⟨⟨x, xs⟩, rfl⟩,
  simp only [set.mem_Union, set.mem_range],
  exact ⟨_, ⟨F ⟨x, xs⟩, rfl⟩, hF _ _ this.symm⟩
end

theorem finite_approx_of_totally_bounded {s : set α} (hs : totally_bounded s) :
  ∀ ε > 0, ∃ t ⊆ s, set.finite t ∧ s ⊆ ⋃y∈t, ball y ε :=
begin
  intros ε ε_pos,
  rw totally_bounded_iff_subset at hs,
  exact hs _ (dist_mem_uniformity ε_pos),
end

/-- Expressing uniform convergence using `dist` -/
lemma tendsto_uniformly_on_filter_iff {ι : Type*}
  {F : ι → β → α} {f : β → α} {p : filter ι} {p' : filter β} :
  tendsto_uniformly_on_filter F f p p' ↔
  ∀ ε > 0, ∀ᶠ (n : ι × β) in (p ×ᶠ p'), dist (f n.snd) (F n.fst n.snd) < ε :=
begin
  refine ⟨λ H ε hε, H _ (dist_mem_uniformity hε), λ H u hu, _⟩,
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩,
  refine (H ε εpos).mono (λ n hn, hε hn),
end

/-- Expressing locally uniform convergence on a set using `dist`. -/
lemma tendsto_locally_uniformly_on_iff {ι : Type*} [topological_space β]
  {F : ι → β → α} {f : β → α} {p : filter ι} {s : set β} :
  tendsto_locally_uniformly_on F f p s ↔
  ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε :=
begin
  refine ⟨λ H ε hε, H _ (dist_mem_uniformity hε), λ H u hu x hx, _⟩,
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩,
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩,
  exact ⟨t, ht, Ht.mono (λ n hs x hx, hε (hs x hx))⟩
end

/-- Expressing uniform convergence on a set using `dist`. -/
lemma tendsto_uniformly_on_iff {ι : Type*}
  {F : ι → β → α} {f : β → α} {p : filter ι} {s : set β} :
  tendsto_uniformly_on F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, dist (f x) (F n x) < ε :=
begin
  refine ⟨λ H ε hε, H _ (dist_mem_uniformity hε), λ H u hu, _⟩,
  rcases mem_uniformity_dist.1 hu with ⟨ε, εpos, hε⟩,
  exact (H ε εpos).mono (λ n hs x hx, hε (hs x hx))
end

/-- Expressing locally uniform convergence using `dist`. -/
lemma tendsto_locally_uniformly_iff {ι : Type*} [topological_space β]
  {F : ι → β → α} {f : β → α} {p : filter ι} :
  tendsto_locally_uniformly F f p ↔
  ∀ ε > 0, ∀ (x : β), ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, dist (f y) (F n y) < ε :=
by simp only [← tendsto_locally_uniformly_on_univ, tendsto_locally_uniformly_on_iff,
  nhds_within_univ, mem_univ, forall_const, exists_prop]

/-- Expressing uniform convergence using `dist`. -/
lemma tendsto_uniformly_iff {ι : Type*}
  {F : ι → β → α} {f : β → α} {p : filter ι} :
  tendsto_uniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, dist (f x) (F n x) < ε :=
by { rw [← tendsto_uniformly_on_univ, tendsto_uniformly_on_iff], simp }

protected lemma cauchy_iff {f : filter α} :
  cauchy f ↔ ne_bot f ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x y ∈ t, dist x y < ε :=
uniformity_basis_dist.cauchy_iff

theorem nhds_basis_ball : (𝓝 x).has_basis (λ ε:ℝ, 0 < ε) (ball x) :=
nhds_basis_uniformity uniformity_basis_dist

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ε>0, ball x ε ⊆ s :=
nhds_basis_ball.mem_iff

theorem eventually_nhds_iff {p : α → Prop} :
  (∀ᶠ y in 𝓝 x, p y) ↔ ∃ε>0, ∀ ⦃y⦄, dist y x < ε → p y :=
mem_nhds_iff

lemma eventually_nhds_iff_ball {p : α → Prop} :
  (∀ᶠ y in 𝓝 x, p y) ↔ ∃ ε>0, ∀ y ∈ ball x ε, p y :=
mem_nhds_iff

/-- A version of `filter.eventually_prod_iff` where the second filter consists of neighborhoods
in a pseudo-metric space.-/
lemma eventually_prod_nhds_iff {f : filter ι} {x₀ : α} {p : ι × α → Prop}:
  (∀ᶠ x in f ×ᶠ 𝓝 x₀, p x) ↔ ∃ (pa : ι → Prop) (ha : ∀ᶠ i in f, pa i) (ε > 0),
    ∀ {i}, pa i → ∀ {x}, dist x x₀ < ε → p (i, x) :=
begin
  simp_rw [eventually_prod_iff, metric.eventually_nhds_iff],
  refine exists_congr (λ q, exists_congr $ λ hq, _),
  split,
  { rintro ⟨r, ⟨ε, hε, hεr⟩, hp⟩, exact ⟨ε, hε, λ i hi x hx, hp hi $ hεr hx⟩ },
  { rintro ⟨ε, hε, hp⟩, exact ⟨λ x, dist x x₀ < ε, ⟨ε, hε, λ y, id⟩, @hp⟩ }
end

/-- A version of `filter.eventually_prod_iff` where the first filter consists of neighborhoods
in a pseudo-metric space.-/
lemma eventually_nhds_prod_iff {ι α} [pseudo_metric_space α] {f : filter ι} {x₀ : α}
  {p : α × ι → Prop}:
  (∀ᶠ x in 𝓝 x₀ ×ᶠ f, p x) ↔ ∃ (ε > (0 : ℝ)) (pa : ι → Prop) (ha : ∀ᶠ i in f, pa i) ,
    ∀ {x}, dist x x₀ < ε → ∀ {i}, pa i → p (x, i) :=
begin
  rw [eventually_swap_iff, metric.eventually_prod_nhds_iff],
  split; { rintro ⟨a1, a2, a3, a4, a5⟩, refine ⟨a3, a4, a1, a2, λ b1 b2 b3 b4, a5 b4 b2⟩ }
end

theorem nhds_basis_closed_ball : (𝓝 x).has_basis (λ ε:ℝ, 0 < ε) (closed_ball x) :=
nhds_basis_uniformity uniformity_basis_dist_le

theorem nhds_basis_ball_inv_nat_succ :
  (𝓝 x).has_basis (λ _, true) (λ n:ℕ, ball x (1 / (↑n+1))) :=
nhds_basis_uniformity uniformity_basis_dist_inv_nat_succ

theorem nhds_basis_ball_inv_nat_pos :
  (𝓝 x).has_basis (λ n, 0<n) (λ n:ℕ, ball x (1 / ↑n)) :=
nhds_basis_uniformity uniformity_basis_dist_inv_nat_pos

theorem nhds_basis_ball_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
  (𝓝 x).has_basis (λ n, true) (λ n:ℕ, ball x (r ^ n)) :=
nhds_basis_uniformity (uniformity_basis_dist_pow h0 h1)

theorem nhds_basis_closed_ball_pow {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
  (𝓝 x).has_basis (λ n, true) (λ n:ℕ, closed_ball x (r ^ n)) :=
nhds_basis_uniformity (uniformity_basis_dist_le_pow h0 h1)

theorem is_open_iff : is_open s ↔ ∀x∈s, ∃ε>0, ball x ε ⊆ s :=
by simp only [is_open_iff_mem_nhds, mem_nhds_iff]

theorem is_open_ball : is_open (ball x ε) :=
is_open_iff.2 $ λ y, exists_ball_subset_ball

theorem ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : ball x ε ∈ 𝓝 x :=
is_open_ball.mem_nhds (mem_ball_self ε0)

theorem closed_ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : closed_ball x ε ∈ 𝓝 x :=
mem_of_superset (ball_mem_nhds x ε0) ball_subset_closed_ball

theorem closed_ball_mem_nhds_of_mem {x c : α} {ε : ℝ} (h : x ∈ ball c ε) :
  closed_ball c ε ∈ 𝓝 x :=
mem_of_superset (is_open_ball.mem_nhds h) ball_subset_closed_ball

theorem nhds_within_basis_ball {s : set α} :
  (𝓝[s] x).has_basis (λ ε:ℝ, 0 < ε) (λ ε, ball x ε ∩ s) :=
nhds_within_has_basis nhds_basis_ball s

theorem mem_nhds_within_iff {t : set α} : s ∈ 𝓝[t] x ↔ ∃ε>0, ball x ε ∩ t ⊆ s :=
nhds_within_basis_ball.mem_iff

theorem tendsto_nhds_within_nhds_within [pseudo_metric_space β] {t : set β} {f : α → β} {a b} :
  tendsto f (𝓝[s] a) (𝓝[t] b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀{x:α}, x ∈ s → dist x a < δ → f x ∈ t ∧ dist (f x) b < ε :=
(nhds_within_basis_ball.tendsto_iff nhds_within_basis_ball).trans $
  forall₂_congr $ λ ε hε, exists₂_congr $ λ δ hδ,
  forall_congr $ λ x, by simp; itauto

theorem tendsto_nhds_within_nhds [pseudo_metric_space β] {f : α → β} {a b} :
  tendsto f (𝓝[s] a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀{x:α}, x ∈ s → dist x a < δ → dist (f x) b < ε :=
by { rw [← nhds_within_univ b, tendsto_nhds_within_nhds_within],
  simp only [mem_univ, true_and] }

theorem tendsto_nhds_nhds [pseudo_metric_space β] {f : α → β} {a b} :
  tendsto f (𝓝 a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀{x:α}, dist x a < δ → dist (f x) b < ε :=
nhds_basis_ball.tendsto_iff nhds_basis_ball

theorem continuous_at_iff [pseudo_metric_space β] {f : α → β} {a : α} :
  continuous_at f a ↔
    ∀ ε > 0, ∃ δ > 0, ∀{x:α}, dist x a < δ → dist (f x) (f a) < ε :=
by rw [continuous_at, tendsto_nhds_nhds]

theorem continuous_within_at_iff [pseudo_metric_space β] {f : α → β} {a : α} {s : set α} :
  continuous_within_at f s a ↔
  ∀ ε > 0, ∃ δ > 0, ∀{x:α}, x ∈ s → dist x a < δ → dist (f x) (f a) < ε :=
by rw [continuous_within_at, tendsto_nhds_within_nhds]

theorem continuous_on_iff [pseudo_metric_space β] {f : α → β} {s : set α} :
  continuous_on f s ↔
  ∀ (b ∈ s) (ε > 0), ∃ δ > 0, ∀a ∈ s, dist a b < δ → dist (f a) (f b) < ε :=
by simp [continuous_on, continuous_within_at_iff]

theorem continuous_iff [pseudo_metric_space β] {f : α → β} :
  continuous f ↔
  ∀b (ε > 0), ∃ δ > 0, ∀a, dist a b < δ → dist (f a) (f b) < ε :=
continuous_iff_continuous_at.trans $ forall_congr $ λ b, tendsto_nhds_nhds

theorem tendsto_nhds {f : filter β} {u : β → α} {a : α} :
  tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, dist (u x) a < ε :=
nhds_basis_ball.tendsto_right_iff

theorem continuous_at_iff' [topological_space β] {f : β → α} {b : β} :
  continuous_at f b ↔
  ∀ ε > 0, ∀ᶠ x in 𝓝 b, dist (f x) (f b) < ε :=
by rw [continuous_at, tendsto_nhds]

theorem continuous_within_at_iff' [topological_space β] {f : β → α} {b : β} {s : set β} :
  continuous_within_at f s b ↔
  ∀ ε > 0, ∀ᶠ x in 𝓝[s] b, dist (f x) (f b) < ε :=
by rw [continuous_within_at, tendsto_nhds]

theorem continuous_on_iff' [topological_space β] {f : β → α} {s : set β} :
  continuous_on f s ↔
  ∀ (b ∈ s) (ε > 0), ∀ᶠ x in 𝓝[s] b, dist (f x) (f b) < ε  :=
by simp [continuous_on, continuous_within_at_iff']

theorem continuous_iff' [topological_space β] {f : β → α} :
  continuous f ↔ ∀a (ε > 0), ∀ᶠ x in 𝓝 a, dist (f x) (f a) < ε :=
continuous_iff_continuous_at.trans $ forall_congr $ λ b, tendsto_nhds

theorem tendsto_at_top [nonempty β] [semilattice_sup β] {u : β → α} {a : α} :
  tendsto u at_top (𝓝 a) ↔ ∀ε>0, ∃N, ∀n≥N, dist (u n) a < ε :=
(at_top_basis.tendsto_iff nhds_basis_ball).trans $
  by { simp only [exists_prop, true_and], refl }

/--
A variant of `tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
theorem tendsto_at_top' [nonempty β] [semilattice_sup β] [no_max_order β] {u : β → α} {a : α} :
  tendsto u at_top (𝓝 a) ↔ ∀ε>0, ∃N, ∀n>N, dist (u n) a < ε :=
(at_top_basis_Ioi.tendsto_iff nhds_basis_ball).trans $
  by { simp only [exists_prop, true_and], refl }

lemma is_open_singleton_iff {α : Type*} [pseudo_metric_space α] {x : α} :
  is_open ({x} : set α) ↔ ∃ ε > 0, ∀ y, dist y x < ε → y = x :=
by simp [is_open_iff, subset_singleton_iff, mem_ball]

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is an open ball
centered at `x` and intersecting `s` only at `x`. -/
lemma exists_ball_inter_eq_singleton_of_mem_discrete [discrete_topology s] {x : α} (hx : x ∈ s) :
  ∃ ε > 0, metric.ball x ε ∩ s = {x} :=
nhds_basis_ball.exists_inter_eq_singleton_of_mem_discrete hx

/-- Given a point `x` in a discrete subset `s` of a pseudometric space, there is a closed ball
of positive radius centered at `x` and intersecting `s` only at `x`. -/
lemma exists_closed_ball_inter_eq_singleton_of_discrete [discrete_topology s] {x : α} (hx : x ∈ s) :
  ∃ ε > 0, metric.closed_ball x ε ∩ s = {x} :=
nhds_basis_closed_ball.exists_inter_eq_singleton_of_mem_discrete hx

lemma _root_.dense.exists_dist_lt {s : set α} (hs : dense s) (x : α) {ε : ℝ} (hε : 0 < ε) :
  ∃ y ∈ s, dist x y < ε :=
begin
  have : (ball x ε).nonempty, by simp [hε],
  simpa only [mem_ball'] using hs.exists_mem_open is_open_ball this
end

lemma _root_.dense_range.exists_dist_lt {β : Type*} {f : β → α} (hf : dense_range f)
  (x : α) {ε : ℝ} (hε : 0 < ε) :
  ∃ y, dist x (f y) < ε :=
exists_range_iff.1 (hf.exists_dist_lt x hε)

end metric

open metric

/-Instantiate a pseudometric space as a pseudoemetric space. Before we can state the instance,
we need to show that the uniform structure coming from the edistance and the
distance coincide. -/

/-- Expressing the uniformity in terms of `edist` -/
protected lemma pseudo_metric.uniformity_basis_edist :
  (𝓤 α).has_basis (λ ε:ℝ≥0∞, 0 < ε) (λ ε, {p | edist p.1 p.2 < ε}) :=
⟨begin
  intro t,
  refine mem_uniformity_dist.trans ⟨_, _⟩; rintro ⟨ε, ε0, Hε⟩,
  { use [ennreal.of_real ε, ennreal.of_real_pos.2 ε0],
    rintros ⟨a, b⟩,
    simp only [edist_dist, ennreal.of_real_lt_of_real_iff ε0],
    exact Hε },
  { rcases ennreal.lt_iff_exists_real_btwn.1 ε0 with ⟨ε', _, ε0', hε⟩,
    rw [ennreal.of_real_pos] at ε0',
    refine ⟨ε', ε0', λ a b h, Hε (lt_trans _ hε)⟩,
    rwa [edist_dist, ennreal.of_real_lt_of_real_iff ε0'] }
end⟩

theorem metric.uniformity_edist : 𝓤 α = (⨅ ε>0, 𝓟 {p:α×α | edist p.1 p.2 < ε}) :=
pseudo_metric.uniformity_basis_edist.eq_binfi

/-- A pseudometric space induces a pseudoemetric space -/
@[priority 100] -- see Note [lower instance priority]
instance pseudo_metric_space.to_pseudo_emetric_space : pseudo_emetric_space α :=
{ edist               := edist,
  edist_self          := by simp [edist_dist],
  edist_comm          := by simp only [edist_dist, dist_comm]; simp,
  edist_triangle      := assume x y z, begin
    simp only [edist_dist, ← ennreal.of_real_add, dist_nonneg],
    rw ennreal.of_real_le_of_real_iff _,
    { exact dist_triangle _ _ _ },
    { simpa using add_le_add (dist_nonneg : 0 ≤ dist x y) dist_nonneg }
  end,
  uniformity_edist    := metric.uniformity_edist,
  ..‹pseudo_metric_space α› }

/-- In a pseudometric space, an open ball of infinite radius is the whole space -/
lemma metric.eball_top_eq_univ (x : α) :
  emetric.ball x ∞ = set.univ :=
set.eq_univ_iff_forall.mpr (λ y, edist_lt_top y x)

/-- Balls defined using the distance or the edistance coincide -/
@[simp] lemma metric.emetric_ball {x : α} {ε : ℝ} : emetric.ball x (ennreal.of_real ε) = ball x ε :=
begin
  ext y,
  simp only [emetric.mem_ball, mem_ball, edist_dist],
  exact ennreal.of_real_lt_of_real_iff_of_nonneg dist_nonneg
end

/-- Balls defined using the distance or the edistance coincide -/
@[simp] lemma metric.emetric_ball_nnreal {x : α} {ε : ℝ≥0} : emetric.ball x ε = ball x ε :=
by { convert metric.emetric_ball, simp }

/-- Closed balls defined using the distance or the edistance coincide -/
lemma metric.emetric_closed_ball {x : α} {ε : ℝ} (h : 0 ≤ ε) :
  emetric.closed_ball x (ennreal.of_real ε) = closed_ball x ε :=
by ext y; simp [edist_dist]; rw ennreal.of_real_le_of_real_iff h

/-- Closed balls defined using the distance or the edistance coincide -/
@[simp] lemma metric.emetric_closed_ball_nnreal {x : α} {ε : ℝ≥0} :
  emetric.closed_ball x ε = closed_ball x ε :=
by { convert metric.emetric_closed_ball ε.2, simp }

@[simp] lemma metric.emetric_ball_top (x : α) : emetric.ball x ⊤ = univ :=
eq_univ_of_forall $ λ y, edist_lt_top _ _

lemma metric.inseparable_iff {x y : α} : inseparable x y ↔ dist x y = 0 :=
by rw [emetric.inseparable_iff, edist_nndist, dist_nndist, ennreal.coe_eq_zero,
  nnreal.coe_eq_zero]

/-- Build a new pseudometric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
def pseudo_metric_space.replace_uniformity {α} [U : uniform_space α] (m : pseudo_metric_space α)
  (H : @uniformity _ U = @uniformity _ pseudo_emetric_space.to_uniform_space) :
  pseudo_metric_space α :=
{ dist               := @dist _ m.to_has_dist,
  dist_self          := dist_self,
  dist_comm          := dist_comm,
  dist_triangle      := dist_triangle,
  edist              := edist,
  edist_dist         := edist_dist,
  to_uniform_space   := U,
  uniformity_dist    := H.trans pseudo_metric_space.uniformity_dist }

lemma pseudo_metric_space.replace_uniformity_eq {α} [U : uniform_space α]
  (m : pseudo_metric_space α)
  (H : @uniformity _ U = @uniformity _ pseudo_emetric_space.to_uniform_space) :
  m.replace_uniformity H = m :=
by { ext, refl }

/-- Build a new pseudo metric space from an old one where the bundled topological structure is
provably (but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
-/
@[reducible] def pseudo_metric_space.replace_topology {γ} [U : topological_space γ]
  (m : pseudo_metric_space γ) (H : U = m.to_uniform_space.to_topological_space) :
  pseudo_metric_space γ :=
@pseudo_metric_space.replace_uniformity γ (m.to_uniform_space.replace_topology H) m rfl

lemma pseudo_metric_space.replace_topology_eq {γ} [U : topological_space γ]
  (m : pseudo_metric_space γ) (H : U = m.to_uniform_space.to_topological_space) :
  m.replace_topology H = m :=
by { ext, refl }

/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the pseudoemetric space. In this definition, the
distance is given separately, to be able to prescribe some expression which is not defeq to the
push-forward of the edistance to reals. -/
def pseudo_emetric_space.to_pseudo_metric_space_of_dist {α : Type u} [e : pseudo_emetric_space α]
  (dist : α → α → ℝ)
  (edist_ne_top : ∀x y: α, edist x y ≠ ⊤)
  (h : ∀x y, dist x y = ennreal.to_real (edist x y)) :
  pseudo_metric_space α :=
let m : pseudo_metric_space α :=
{ dist := dist,
  dist_self          := λx, by simp [h],
  dist_comm          := λx y, by simp [h, pseudo_emetric_space.edist_comm],
  dist_triangle      := λx y z, begin
    simp only [h],
    rw [← ennreal.to_real_add (edist_ne_top _ _) (edist_ne_top _ _),
        ennreal.to_real_le_to_real (edist_ne_top _ _)],
    { exact edist_triangle _ _ _ },
    { simp [ennreal.add_eq_top, edist_ne_top] }
  end,
  edist := edist,
  edist_dist := λ x y, by simp [h, ennreal.of_real_to_real, edist_ne_top] } in
m.replace_uniformity $ by { rw [uniformity_pseudoedist, metric.uniformity_edist], refl }

/-- One gets a pseudometric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the pseudometric space and the emetric space. -/
def pseudo_emetric_space.to_pseudo_metric_space {α : Type u} [e : pseudo_emetric_space α]
  (h : ∀x y: α, edist x y ≠ ⊤) : pseudo_metric_space α :=
pseudo_emetric_space.to_pseudo_metric_space_of_dist
  (λx y, ennreal.to_real (edist x y)) h (λx y, rfl)

/-- Build a new pseudometric space from an old one where the bundled bornology structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
-/
def pseudo_metric_space.replace_bornology {α} [B : bornology α] (m : pseudo_metric_space α)
  (H : ∀ s, @is_bounded _ B s ↔ @is_bounded _ pseudo_metric_space.to_bornology s) :
  pseudo_metric_space α :=
{ to_bornology := B,
  cobounded_sets := set.ext $ compl_surjective.forall.2 $ λ s, (H s).trans $
    by rw [is_bounded_iff, mem_set_of_eq, compl_compl],
  .. m }

lemma pseudo_metric_space.replace_bornology_eq {α} [m : pseudo_metric_space α] [B : bornology α]
  (H : ∀ s, @is_bounded _ B s ↔ @is_bounded _ pseudo_metric_space.to_bornology s) :
  pseudo_metric_space.replace_bornology _ H = m :=
by { ext, refl }

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `dist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem metric.complete_of_convergent_controlled_sequences (B : ℕ → real) (hB : ∀n, 0 < B n)
  (H : ∀u : ℕ → α, (∀N n m : ℕ, N ≤ n → N ≤ m → dist (u n) (u m) < B N) →
    ∃x, tendsto u at_top (𝓝 x)) :
  complete_space α :=
uniform_space.complete_of_convergent_controlled_sequences
  (λ n, {p:α×α | dist p.1 p.2 < B n}) (λ n, dist_mem_uniformity $ hB n) H

theorem metric.complete_of_cauchy_seq_tendsto :
  (∀ u : ℕ → α, cauchy_seq u → ∃a, tendsto u at_top (𝓝 a)) → complete_space α :=
emetric.complete_of_cauchy_seq_tendsto

section real

/-- Instantiate the reals as a pseudometric space. -/
instance real.pseudo_metric_space : pseudo_metric_space ℝ :=
{ dist               := λx y, |x - y|,
  dist_self          := by simp [abs_zero],
  dist_comm          := assume x y, abs_sub_comm _ _,
  dist_triangle      := assume x y z, abs_sub_le _ _ _ }

theorem real.dist_eq (x y : ℝ) : dist x y = |x - y| := rfl

theorem real.nndist_eq (x y : ℝ) : nndist x y = real.nnabs (x - y) := rfl

theorem real.nndist_eq' (x y : ℝ) : nndist x y = real.nnabs (y - x) := nndist_comm _ _

theorem real.dist_0_eq_abs (x : ℝ) : dist x 0 = |x| :=
by simp [real.dist_eq]

theorem real.dist_left_le_of_mem_interval {x y z : ℝ} (h : y ∈ interval x z) :
  dist x y ≤ dist x z :=
by simpa only [dist_comm x] using abs_sub_left_of_mem_interval h

theorem real.dist_right_le_of_mem_interval {x y z : ℝ} (h : y ∈ interval x z) :
  dist y z ≤ dist x z :=
by simpa only [dist_comm _ z] using abs_sub_right_of_mem_interval h

theorem real.dist_le_of_mem_interval {x y x' y' : ℝ} (hx : x ∈ interval x' y')
  (hy : y ∈ interval x' y') : dist x y ≤ dist x' y' :=
abs_sub_le_of_subinterval $ interval_subset_interval (by rwa interval_swap) (by rwa interval_swap)

theorem real.dist_le_of_mem_Icc {x y x' y' : ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') :
  dist x y ≤ y' - x' :=
by simpa only [real.dist_eq, abs_of_nonpos (sub_nonpos.2 $ hx.1.trans hx.2), neg_sub]
  using real.dist_le_of_mem_interval (Icc_subset_interval hx) (Icc_subset_interval hy)

theorem real.dist_le_of_mem_Icc_01 {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
  dist x y ≤ 1 :=
by simpa only [sub_zero] using real.dist_le_of_mem_Icc hx hy

instance : order_topology ℝ :=
order_topology_of_nhds_abs $ λ x,
  by simp only [nhds_basis_ball.eq_binfi, ball, real.dist_eq, abs_sub_comm]

lemma real.ball_eq_Ioo (x r : ℝ) : ball x r = Ioo (x - r) (x + r) :=
set.ext $ λ y, by rw [mem_ball, dist_comm, real.dist_eq,
  abs_sub_lt_iff, mem_Ioo, ← sub_lt_iff_lt_add', sub_lt_comm]

lemma real.closed_ball_eq_Icc {x r : ℝ} : closed_ball x r = Icc (x - r) (x + r) :=
by ext y; rw [mem_closed_ball, dist_comm, real.dist_eq,
  abs_sub_le_iff, mem_Icc, ← sub_le_iff_le_add', sub_le_comm]

theorem real.Ioo_eq_ball (x y : ℝ) : Ioo x y = ball ((x + y) / 2) ((y - x) / 2) :=
by rw [real.ball_eq_Ioo, ← sub_div, add_comm, ← sub_add,
  add_sub_cancel', add_self_div_two, ← add_div,
  add_assoc, add_sub_cancel'_right, add_self_div_two]

theorem real.Icc_eq_closed_ball (x y : ℝ) : Icc x y = closed_ball ((x + y) / 2) ((y - x) / 2) :=
by rw [real.closed_ball_eq_Icc, ← sub_div, add_comm, ← sub_add,
  add_sub_cancel', add_self_div_two, ← add_div,
  add_assoc, add_sub_cancel'_right, add_self_div_two]

section metric_ordered

variables [preorder α] [compact_Icc_space α]

lemma totally_bounded_Icc (a b : α) : totally_bounded (Icc a b) :=
is_compact_Icc.totally_bounded

lemma totally_bounded_Ico (a b : α) : totally_bounded (Ico a b) :=
totally_bounded_subset Ico_subset_Icc_self (totally_bounded_Icc a b)

lemma totally_bounded_Ioc (a b : α) : totally_bounded (Ioc a b) :=
totally_bounded_subset Ioc_subset_Icc_self (totally_bounded_Icc a b)

lemma totally_bounded_Ioo (a b : α) : totally_bounded (Ioo a b) :=
totally_bounded_subset Ioo_subset_Icc_self (totally_bounded_Icc a b)

end metric_ordered

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the
general case. -/
lemma squeeze_zero' {α} {f g : α → ℝ} {t₀ : filter α} (hf : ∀ᶠ t in t₀, 0 ≤ f t)
  (hft : ∀ᶠ t in t₀, f t ≤ g t) (g0 : tendsto g t₀ (nhds 0)) : tendsto f t₀ (𝓝 0) :=
tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft

/-- Special case of the sandwich theorem; see `tendsto_of_tendsto_of_tendsto_of_le_of_le`
and  `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case. -/
lemma squeeze_zero {α} {f g : α → ℝ} {t₀ : filter α} (hf : ∀t, 0 ≤ f t) (hft : ∀t, f t ≤ g t)
  (g0 : tendsto g t₀ (𝓝 0)) : tendsto f t₀ (𝓝 0) :=
squeeze_zero' (eventually_of_forall hf) (eventually_of_forall hft) g0

theorem metric.uniformity_eq_comap_nhds_zero :
  𝓤 α = comap (λp:α×α, dist p.1 p.2) (𝓝 (0 : ℝ)) :=
by { ext s,
  simp [mem_uniformity_dist, (nhds_basis_ball.comap _).mem_iff, subset_def, real.dist_0_eq_abs] }

lemma cauchy_seq_iff_tendsto_dist_at_top_0 [nonempty β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ tendsto (λ (n : β × β), dist (u n.1) (u n.2)) at_top (𝓝 0) :=
by rw [cauchy_seq_iff_tendsto, metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff,
  prod.map_def]

lemma tendsto_uniformity_iff_dist_tendsto_zero {ι : Type*} {f : ι → α × α} {p : filter ι} :
  tendsto f p (𝓤 α) ↔ tendsto (λ x, dist (f x).1 (f x).2) p (𝓝 0) :=
by rw [metric.uniformity_eq_comap_nhds_zero, tendsto_comap_iff]

lemma filter.tendsto.congr_dist {ι : Type*} {f₁ f₂ : ι → α} {p : filter ι} {a : α}
  (h₁ : tendsto f₁ p (𝓝 a)) (h : tendsto (λ x, dist (f₁ x) (f₂ x)) p (𝓝 0)) :
  tendsto f₂ p (𝓝 a) :=
h₁.congr_uniformity $ tendsto_uniformity_iff_dist_tendsto_zero.2 h

alias filter.tendsto.congr_dist ← tendsto_of_tendsto_of_dist

lemma tendsto_iff_of_dist {ι : Type*} {f₁ f₂ : ι → α} {p : filter ι} {a : α}
  (h : tendsto (λ x, dist (f₁ x) (f₂ x)) p (𝓝 0)) :
  tendsto f₁ p (𝓝 a) ↔ tendsto f₂ p (𝓝 a) :=
uniform.tendsto_congr $ tendsto_uniformity_iff_dist_tendsto_zero.2 h

/-- If `u` is a neighborhood of `x`, then for small enough `r`, the closed ball
`closed_ball x r` is contained in `u`. -/
lemma eventually_closed_ball_subset {x : α} {u : set α} (hu : u ∈ 𝓝 x) :
  ∀ᶠ r in 𝓝 (0 : ℝ), closed_ball x r ⊆ u :=
begin
  obtain ⟨ε, εpos, hε⟩ : ∃ ε (hε : 0 < ε), closed_ball x ε ⊆ u :=
    nhds_basis_closed_ball.mem_iff.1 hu,
  have : Iic ε ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds εpos,
  filter_upwards [this] with _ hr using subset.trans (closed_ball_subset_closed_ball hr) hε,
end

end real

section cauchy_seq
variables [nonempty β] [semilattice_sup β]

/-- In a pseudometric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem metric.cauchy_seq_iff {u : β → α} :
  cauchy_seq u ↔ ∀ε>0, ∃N, ∀m n≥N, dist (u m) (u n) < ε :=
uniformity_basis_dist.cauchy_seq_iff

/-- A variation around the pseudometric characterization of Cauchy sequences -/
theorem metric.cauchy_seq_iff' {u : β → α} :
  cauchy_seq u ↔ ∀ε>0, ∃N, ∀n≥N, dist (u n) (u N) < ε :=
uniformity_basis_dist.cauchy_seq_iff'

/-- In a pseudometric space, unifom Cauchy sequences are characterized by the fact that, eventually,
the distance between all its elements is uniformly, arbitrarily small -/
@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem metric.uniform_cauchy_seq_on_iff {γ : Type*}
  {F : β → γ → α} {s : set γ} :
  uniform_cauchy_seq_on F at_top s ↔
    ∀ ε : ℝ, ε > 0 → ∃ (N : β), ∀ m : β, m ≥ N → ∀ n : β, n ≥ N → ∀ x : γ, x ∈ s →
    dist (F m x) (F n x) < ε :=
begin
  split,
  { intros h ε hε,
    let u := { a : α × α | dist a.fst a.snd < ε },
    have hu : u ∈ 𝓤 α := metric.mem_uniformity_dist.mpr ⟨ε, hε, (λ a b, by simp)⟩,
    rw ←@filter.eventually_at_top_prod_self' _ _ _
      (λ m, ∀ x : γ, x ∈ s → dist (F m.fst x) (F m.snd x) < ε),
    specialize h u hu,
    rw prod_at_top_at_top_eq at h,
    exact h.mono (λ n h x hx, set.mem_set_of_eq.mp (h x hx)), },
  { intros h u hu,
    rcases (metric.mem_uniformity_dist.mp hu) with ⟨ε, hε, hab⟩,
    rcases h ε hε with ⟨N, hN⟩,
    rw [prod_at_top_at_top_eq, eventually_at_top],
    use (N, N),
    intros b hb x hx,
    rcases hb with ⟨hbl, hbr⟩,
    exact hab (hN b.fst hbl.ge b.snd hbr.ge x hx), },
end

/-- If the distance between `s n` and `s m`, `n ≤ m` is bounded above by `b n`
and `b` converges to zero, then `s` is a Cauchy sequence.  -/
lemma cauchy_seq_of_le_tendsto_0' {s : β → α} (b : β → ℝ)
  (h : ∀ n m : β, n ≤ m → dist (s n) (s m) ≤ b n) (h₀ : tendsto b at_top (𝓝 0)) :
  cauchy_seq s :=
metric.cauchy_seq_iff'.2 $ λ ε ε0,
  (h₀.eventually (gt_mem_nhds ε0)).exists.imp $ λ N hN n hn,
  calc dist (s n) (s N) = dist (s N) (s n) : dist_comm _ _
                    ... ≤ b N              : h _ _ hn
                    ... < ε                : hN

/-- If the distance between `s n` and `s m`, `n, m ≥ N` is bounded above by `b N`
and `b` converges to zero, then `s` is a Cauchy sequence.  -/
lemma cauchy_seq_of_le_tendsto_0 {s : β → α} (b : β → ℝ)
  (h : ∀ n m N : β, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) (h₀ : tendsto b at_top (𝓝 0)) :
  cauchy_seq s :=
cauchy_seq_of_le_tendsto_0' b (λ n m hnm, h _ _ _ le_rfl hnm) h₀

/-- A Cauchy sequence on the natural numbers is bounded. -/
theorem cauchy_seq_bdd {u : ℕ → α} (hu : cauchy_seq u) :
  ∃ R > 0, ∀ m n, dist (u m) (u n) < R :=
begin
  rcases metric.cauchy_seq_iff'.1 hu 1 zero_lt_one with ⟨N, hN⟩,
  rsuffices ⟨R, R0, H⟩ : ∃ R > 0, ∀ n, dist (u n) (u N) < R,
  { exact ⟨_, add_pos R0 R0, λ m n,
      lt_of_le_of_lt (dist_triangle_right _ _ _) (add_lt_add (H m) (H n))⟩ },
  let R := finset.sup (finset.range N) (λ n, nndist (u n) (u N)),
  refine ⟨↑R + 1, add_pos_of_nonneg_of_pos R.2 zero_lt_one, λ n, _⟩,
  cases le_or_lt N n,
  { exact lt_of_lt_of_le (hN _ h) (le_add_of_nonneg_left R.2) },
  { have : _ ≤ R := finset.le_sup (finset.mem_range.2 h),
    exact lt_of_le_of_lt this (lt_add_of_pos_right _ zero_lt_one) }
end

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
lemma cauchy_seq_iff_le_tendsto_0 {s : ℕ → α} : cauchy_seq s ↔ ∃ b : ℕ → ℝ,
  (∀ n, 0 ≤ b n) ∧
  (∀ n m N : ℕ, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) ∧
  tendsto b at_top (𝓝 0) :=
⟨λ hs, begin
  /- `s` is a Cauchy sequence. The sequence `b` will be constructed by taking
  the supremum of the distances between `s n` and `s m` for `n m ≥ N`.
  First, we prove that all these distances are bounded, as otherwise the Sup
  would not make sense. -/
  let S := λ N, (λ(p : ℕ × ℕ), dist (s p.1) (s p.2)) '' {p | p.1 ≥ N ∧ p.2 ≥ N},
  have hS : ∀ N, ∃ x, ∀ y ∈ S N, y ≤ x,
  { rcases cauchy_seq_bdd hs with ⟨R, R0, hR⟩,
    refine λ N, ⟨R, _⟩, rintro _ ⟨⟨m, n⟩, _, rfl⟩,
    exact le_of_lt (hR m n) },
  have bdd : bdd_above (range (λ(p : ℕ × ℕ), dist (s p.1) (s p.2))),
  { rcases cauchy_seq_bdd hs with ⟨R, R0, hR⟩,
    use R, rintro _ ⟨⟨m, n⟩, rfl⟩, exact le_of_lt (hR m n) },
  -- Prove that it bounds the distances of points in the Cauchy sequence
  have ub : ∀ m n N, N ≤ m → N ≤ n → dist (s m) (s n) ≤ Sup (S N) :=
    λ m n N hm hn, le_cSup (hS N) ⟨⟨_, _⟩, ⟨hm, hn⟩, rfl⟩,
  have S0m : ∀ n, (0:ℝ) ∈ S n := λ n, ⟨⟨n, n⟩, ⟨le_rfl, le_rfl⟩, dist_self _⟩,
  have S0 := λ n, le_cSup (hS n) (S0m n),
  -- Prove that it tends to `0`, by using the Cauchy property of `s`
  refine ⟨λ N, Sup (S N), S0, ub, metric.tendsto_at_top.2 (λ ε ε0, _)⟩,
  refine (metric.cauchy_seq_iff.1 hs (ε/2) (half_pos ε0)).imp (λ N hN n hn, _),
  rw [real.dist_0_eq_abs, abs_of_nonneg (S0 n)],
  refine lt_of_le_of_lt (cSup_le ⟨_, S0m _⟩ _) (half_lt_self ε0),
  rintro _ ⟨⟨m', n'⟩, ⟨hm', hn'⟩, rfl⟩,
  exact le_of_lt (hN _ (le_trans hn hm') _ (le_trans hn hn'))
  end,
λ ⟨b, _, b_bound, b_lim⟩, cauchy_seq_of_le_tendsto_0 b b_bound b_lim⟩

end cauchy_seq

/-- Pseudometric space structure pulled back by a function. -/
def pseudo_metric_space.induced {α β} (f : α → β)
  (m : pseudo_metric_space β) : pseudo_metric_space α :=
{ dist               := λ x y, dist (f x) (f y),
  dist_self          := λ x, dist_self _,
  dist_comm          := λ x y, dist_comm _ _,
  dist_triangle      := λ x y z, dist_triangle _ _ _,
  edist              := λ x y, edist (f x) (f y),
  edist_dist         := λ x y, edist_dist _ _,
  to_uniform_space   := uniform_space.comap f m.to_uniform_space,
  uniformity_dist    := begin
    apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ (λ x y, dist (f x) (f y)),
    refine compl_surjective.forall.2 (λ s, compl_mem_comap.trans $ mem_uniformity_dist.trans _),
    simp only [mem_compl_iff, @imp_not_comm _ (_ ∈ _), ← prod.forall', prod.mk.eta, ball_image_iff]
  end,
  to_bornology       := bornology.induced f,
  cobounded_sets     := set.ext $ compl_surjective.forall.2 $ λ s,
    by simp only [compl_mem_comap, filter.mem_sets, ← is_bounded_def, mem_set_of_eq, compl_compl,
      is_bounded_iff, ball_image_iff] }

/-- Pull back a pseudometric space structure by an inducing map. This is a version of
`pseudo_metric_space.induced` useful in case if the domain already has a `topological_space`
structure. -/
def inducing.comap_pseudo_metric_space {α β} [topological_space α] [pseudo_metric_space β]
  {f : α → β} (hf : inducing f) : pseudo_metric_space α :=
(pseudo_metric_space.induced f ‹_›).replace_topology hf.induced

/-- Pull back a pseudometric space structure by a uniform inducing map. This is a version of
`pseudo_metric_space.induced` useful in case if the domain already has a `uniform_space`
structure. -/
def uniform_inducing.comap_pseudo_metric_space {α β} [uniform_space α] [pseudo_metric_space β]
  (f : α → β) (h : uniform_inducing f) : pseudo_metric_space α :=
(pseudo_metric_space.induced f ‹_›).replace_uniformity h.comap_uniformity.symm

instance subtype.pseudo_metric_space {p : α → Prop} : pseudo_metric_space (subtype p) :=
pseudo_metric_space.induced coe ‹_›

theorem subtype.dist_eq {p : α → Prop} (x y : subtype p) : dist x y = dist (x : α) y := rfl
theorem subtype.nndist_eq {p : α → Prop} (x y : subtype p) : nndist x y = nndist (x : α) y := rfl

namespace mul_opposite

@[to_additive]
instance : pseudo_metric_space (αᵐᵒᵖ) := pseudo_metric_space.induced mul_opposite.unop ‹_›

@[simp, to_additive] theorem dist_unop (x y : αᵐᵒᵖ) : dist (unop x) (unop y) = dist x y := rfl
@[simp, to_additive] theorem dist_op (x y : α) : dist (op x) (op y) = dist x y := rfl
@[simp, to_additive] theorem nndist_unop (x y : αᵐᵒᵖ) : nndist (unop x) (unop y) = nndist x y := rfl
@[simp, to_additive] theorem nndist_op (x y : α) : nndist (op x) (op y) = nndist x y := rfl

end mul_opposite

section nnreal

instance : pseudo_metric_space ℝ≥0 := subtype.pseudo_metric_space

lemma nnreal.dist_eq (a b : ℝ≥0) : dist a b = |(a:ℝ) - b| := rfl

lemma nnreal.nndist_eq (a b : ℝ≥0) :
  nndist a b = max (a - b) (b - a) :=
begin
  /- WLOG, `b ≤ a`. `wlog h : b ≤ a` works too but it is much slower because Lean tries to prove one
  case from the other and fails; `tactic.skip` tells Lean not to try. -/
  wlog h : b ≤ a := le_total b a using [a b, b a] tactic.skip,
  { rw [← nnreal.coe_eq, ← dist_nndist, nnreal.dist_eq, tsub_eq_zero_iff_le.2 h,
      max_eq_left (zero_le $ a - b), ← nnreal.coe_sub h, abs_of_nonneg (a - b).coe_nonneg] },
  { rwa [nndist_comm, max_comm] }
end

@[simp] lemma nnreal.nndist_zero_eq_val (z : ℝ≥0) : nndist 0 z = z :=
by simp only [nnreal.nndist_eq, max_eq_right, tsub_zero, zero_tsub, zero_le']

@[simp] lemma nnreal.nndist_zero_eq_val' (z : ℝ≥0) : nndist z 0 = z :=
by { rw nndist_comm, exact nnreal.nndist_zero_eq_val z, }

lemma nnreal.le_add_nndist (a b : ℝ≥0) : a ≤ b + nndist a b :=
begin
  suffices : (a : ℝ) ≤ (b : ℝ) + (dist a b),
  { exact nnreal.coe_le_coe.mp this, },
  linarith [le_of_abs_le (by refl : abs (a-b : ℝ) ≤ (dist a b))],
end

end nnreal

section ulift
variables [pseudo_metric_space β]

instance : pseudo_metric_space (ulift β) :=
pseudo_metric_space.induced ulift.down ‹_›

lemma ulift.dist_eq (x y : ulift β) : dist x y = dist x.down y.down := rfl
lemma ulift.nndist_eq (x y : ulift β) : nndist x y = nndist x.down y.down := rfl

@[simp] lemma ulift.dist_up_up (x y : β) : dist (ulift.up x) (ulift.up y) = dist x y := rfl
@[simp] lemma ulift.nndist_up_up (x y : β) : nndist (ulift.up x) (ulift.up y) = nndist x y := rfl

end ulift

section prod
variables [pseudo_metric_space β]

instance prod.pseudo_metric_space_max :
  pseudo_metric_space (α × β) :=
(pseudo_emetric_space.to_pseudo_metric_space_of_dist
  (λ x y : α × β, dist x.1 y.1 ⊔ dist x.2 y.2)
  (λ x y, (max_lt (edist_lt_top _ _) (edist_lt_top _ _)).ne)
  (λ x y, by simp only [sup_eq_max, dist_edist,
    ← ennreal.to_real_max (edist_ne_top _ _) (edist_ne_top _ _), prod.edist_eq]))
    .replace_bornology $
  λ s, by { simp only [← is_bounded_image_fst_and_snd, is_bounded_iff_eventually, ball_image_iff,
    ← eventually_and, ← forall_and_distrib, ← max_le_iff], refl }

lemma prod.dist_eq {x y : α × β} :
  dist x y = max (dist x.1 y.1) (dist x.2 y.2) := rfl

@[simp]
lemma dist_prod_same_left {x : α} {y₁ y₂ : β} : dist (x, y₁) (x, y₂) = dist y₁ y₂ :=
by simp [prod.dist_eq, dist_nonneg]

@[simp]
lemma dist_prod_same_right {x₁ x₂ : α} {y : β} : dist (x₁, y) (x₂, y) = dist x₁ x₂ :=
by simp [prod.dist_eq, dist_nonneg]

theorem ball_prod_same (x : α) (y : β) (r : ℝ) :
  ball x r ×ˢ ball y r = ball (x, y) r :=
ext $ λ z, by simp [prod.dist_eq]

theorem closed_ball_prod_same (x : α) (y : β) (r : ℝ) :
  closed_ball x r ×ˢ closed_ball y r = closed_ball (x, y) r :=
ext $ λ z, by simp [prod.dist_eq]

end prod

theorem uniform_continuous_dist : uniform_continuous (λp:α×α, dist p.1 p.2) :=
metric.uniform_continuous_iff.2 (λ ε ε0, ⟨ε/2, half_pos ε0,
begin
  suffices,
  { intros p q h, cases p with p₁ p₂, cases q with q₁ q₂,
    cases max_lt_iff.1 h with h₁ h₂, clear h,
    dsimp at h₁ h₂ ⊢,
    rw real.dist_eq,
    refine abs_sub_lt_iff.2 ⟨_, _⟩,
    { revert p₁ p₂ q₁ q₂ h₁ h₂, exact this },
    { apply this; rwa dist_comm } },
  intros p₁ p₂ q₁ q₂ h₁ h₂,
  have := add_lt_add
    (abs_sub_lt_iff.1 (lt_of_le_of_lt (abs_dist_sub_le p₁ q₁ p₂) h₁)).1
    (abs_sub_lt_iff.1 (lt_of_le_of_lt (abs_dist_sub_le p₂ q₂ q₁) h₂)).1,
  rwa [add_halves, dist_comm p₂, sub_add_sub_cancel, dist_comm q₂] at this
end⟩)

theorem uniform_continuous.dist [uniform_space β] {f g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  uniform_continuous (λb, dist (f b) (g b)) :=
uniform_continuous_dist.comp (hf.prod_mk hg)

@[continuity]
theorem continuous_dist : continuous (λp:α×α, dist p.1 p.2) :=
uniform_continuous_dist.continuous

@[continuity]
theorem continuous.dist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, dist (f b) (g b)) :=
continuous_dist.comp (hf.prod_mk hg : _)

theorem filter.tendsto.dist {f g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, dist (f x) (g x)) x (𝓝 (dist a b)) :=
(continuous_dist.tendsto (a, b)).comp (hf.prod_mk_nhds hg)

lemma nhds_comap_dist (a : α) : (𝓝 (0 : ℝ)).comap (λa', dist a' a) = 𝓝 a :=
by simp only [@nhds_eq_comap_uniformity α, metric.uniformity_eq_comap_nhds_zero,
  comap_comap, (∘), dist_comm]

lemma tendsto_iff_dist_tendsto_zero {f : β → α} {x : filter β} {a : α} :
  (tendsto f x (𝓝 a)) ↔ (tendsto (λb, dist (f b) a) x (𝓝 0)) :=
by rw [← nhds_comap_dist a, tendsto_comap_iff]

lemma continuous_iff_continuous_dist [topological_space β] {f : β → α} :
  continuous f ↔ continuous (λ x : β × β, dist (f x.1) (f x.2)) :=
⟨λ h, (h.comp continuous_fst).dist (h.comp continuous_snd), λ h, continuous_iff_continuous_at.2 $
  λ x, tendsto_iff_dist_tendsto_zero.2 $
    (h.comp (continuous_id.prod_mk continuous_const)).tendsto' _ _ $ dist_self _⟩

lemma uniform_continuous_nndist : uniform_continuous (λp:α×α, nndist p.1 p.2) :=
uniform_continuous_dist.subtype_mk _

lemma uniform_continuous.nndist [uniform_space β] {f g : β → α} (hf : uniform_continuous f)
  (hg : uniform_continuous g) :
  uniform_continuous (λ b, nndist (f b) (g b)) :=
uniform_continuous_nndist.comp (hf.prod_mk hg)

lemma continuous_nndist : continuous (λp:α×α, nndist p.1 p.2) :=
uniform_continuous_nndist.continuous

lemma continuous.nndist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, nndist (f b) (g b)) :=
continuous_nndist.comp (hf.prod_mk hg : _)

theorem filter.tendsto.nndist {f g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, nndist (f x) (g x)) x (𝓝 (nndist a b)) :=
(continuous_nndist.tendsto (a, b)).comp (hf.prod_mk_nhds hg)

namespace metric
variables {x y z : α} {ε ε₁ ε₂ : ℝ} {s : set α}

theorem is_closed_ball : is_closed (closed_ball x ε) :=
is_closed_le (continuous_id.dist continuous_const) continuous_const

lemma is_closed_sphere : is_closed (sphere x ε) :=
is_closed_eq (continuous_id.dist continuous_const) continuous_const

@[simp] theorem closure_closed_ball : closure (closed_ball x ε) = closed_ball x ε :=
is_closed_ball.closure_eq

theorem closure_ball_subset_closed_ball : closure (ball x ε) ⊆ closed_ball x ε :=
closure_minimal ball_subset_closed_ball is_closed_ball

theorem frontier_ball_subset_sphere : frontier (ball x ε) ⊆ sphere x ε :=
frontier_lt_subset_eq (continuous_id.dist continuous_const) continuous_const

theorem frontier_closed_ball_subset_sphere : frontier (closed_ball x ε) ⊆ sphere x ε :=
frontier_le_subset_eq (continuous_id.dist continuous_const) continuous_const

theorem ball_subset_interior_closed_ball : ball x ε ⊆ interior (closed_ball x ε) :=
interior_maximal ball_subset_closed_ball is_open_ball

/-- ε-characterization of the closure in pseudometric spaces-/
theorem mem_closure_iff {s : set α} {a : α} :
  a ∈ closure s ↔ ∀ε>0, ∃b ∈ s, dist a b < ε :=
(mem_closure_iff_nhds_basis nhds_basis_ball).trans $
  by simp only [mem_ball, dist_comm]

lemma mem_closure_range_iff {e : β → α} {a : α} :
  a ∈ closure (range e) ↔ ∀ε>0, ∃ k : β, dist a (e k) < ε :=
by simp only [mem_closure_iff, exists_range_iff]

lemma mem_closure_range_iff_nat {e : β → α} {a : α} :
  a ∈ closure (range e) ↔ ∀n : ℕ, ∃ k : β, dist a (e k) < 1 / ((n : ℝ) + 1) :=
(mem_closure_iff_nhds_basis nhds_basis_ball_inv_nat_succ).trans $
  by simp only [mem_ball, dist_comm, exists_range_iff, forall_const]

theorem mem_of_closed' {s : set α} (hs : is_closed s) {a : α} :
  a ∈ s ↔ ∀ε>0, ∃b ∈ s, dist a b < ε :=
by simpa only [hs.closure_eq] using @mem_closure_iff _ _ s a

lemma closed_ball_zero' (x : α) : closed_ball x 0 = closure {x} :=
subset.antisymm
  (λ y hy, mem_closure_iff.2 $ λ ε ε0, ⟨x, mem_singleton x, (mem_closed_ball.1 hy).trans_lt ε0⟩)
  (closure_minimal (singleton_subset_iff.2 (dist_self x).le) is_closed_ball)

lemma dense_iff {s : set α} :
  dense s ↔ ∀ x, ∀ r > 0, (ball x r ∩ s).nonempty :=
forall_congr $ λ x, by simp only [mem_closure_iff, set.nonempty, exists_prop, mem_inter_iff,
  mem_ball', and_comm]

lemma dense_range_iff {f : β → α} :
  dense_range f ↔ ∀ x, ∀ r > 0, ∃ y, dist x (f y) < r :=
forall_congr $ λ x, by simp only [mem_closure_iff, exists_range_iff]

/-- If a set `s` is separable, then the corresponding subtype is separable in a metric space.
This is not obvious, as the countable set whose closure covers `s` does not need in general to
be contained in `s`. -/
lemma _root_.topological_space.is_separable.separable_space {s : set α} (hs : is_separable s) :
  separable_space s :=
begin
  classical,
  rcases eq_empty_or_nonempty s with rfl|⟨⟨x₀, x₀s⟩⟩,
  { apply_instance },
  rcases hs with ⟨c, hc, h'c⟩,
  haveI : encodable c := hc.to_encodable,
  obtain ⟨u, -, u_pos, u_lim⟩ : ∃ (u : ℕ → ℝ), strict_anti u ∧ (∀ (n : ℕ), 0 < u n) ∧
    tendsto u at_top (𝓝 0) := exists_seq_strict_anti_tendsto (0 : ℝ),
  let f : c × ℕ → α := λ p, if h : (metric.ball (p.1 : α) (u p.2) ∩ s).nonempty then h.some else x₀,
  have fs : ∀ p, f p ∈ s,
  { rintros ⟨y, n⟩,
    by_cases h : (ball (y : α) (u n) ∩ s).nonempty,
    { simpa only [f, h, dif_pos] using h.some_spec.2 },
    { simpa only [f, h, not_false_iff, dif_neg] } },
  let g : c × ℕ → s := λ p, ⟨f p, fs p⟩,
  apply separable_space_of_dense_range g,
  apply metric.dense_range_iff.2,
  rintros ⟨x, xs⟩ r (rpos : 0 < r),
  obtain ⟨n, hn⟩ : ∃ n, u n < r / 2 := ((tendsto_order.1 u_lim).2 _ (half_pos rpos)).exists,
  obtain ⟨z, zc, hz⟩ : ∃ z ∈ c, dist x z < u n :=
    metric.mem_closure_iff.1 (h'c xs) _ (u_pos n),
  refine ⟨(⟨z, zc⟩, n), _⟩,
  change dist x (f (⟨z, zc⟩, n)) < r,
  have A : (metric.ball z (u n) ∩ s).nonempty := ⟨x, hz, xs⟩,
  dsimp [f],
  simp only [A, dif_pos],
  calc dist x A.some
      ≤ dist x z + dist z A.some : dist_triangle _ _ _
  ... < r/2 + r/2 : add_lt_add (hz.trans hn) ((metric.mem_ball'.1 A.some_spec.1).trans hn)
  ... = r : add_halves _
end

/-- The preimage of a separable set by an inducing map is separable. -/
protected lemma _root_.inducing.is_separable_preimage {f : β → α} [topological_space β]
  (hf : inducing f) {s : set α} (hs : is_separable s) :
  is_separable (f ⁻¹' s) :=
begin
  haveI : second_countable_topology s,
  { haveI : separable_space s := hs.separable_space,
    exact uniform_space.second_countable_of_separable _ },
  let g : f ⁻¹' s → s := cod_restrict (f ∘ coe) s (λ x, x.2),
  have : inducing g := (hf.comp inducing_coe).cod_restrict _,
  haveI : second_countable_topology (f ⁻¹' s) := this.second_countable_topology,
  rw show f ⁻¹' s = coe '' (univ : set (f ⁻¹' s)),
     by simpa only [image_univ, subtype.range_coe_subtype],
  exact (is_separable_of_separable_space _).image continuous_subtype_coe
end

protected lemma _root_.embedding.is_separable_preimage {f : β → α} [topological_space β]
  (hf : embedding f) {s : set α} (hs : is_separable s) :
  is_separable (f ⁻¹' s) :=
hf.to_inducing.is_separable_preimage hs

/-- If a map is continuous on a separable set `s`, then the image of `s` is also separable. -/
lemma _root_.continuous_on.is_separable_image [topological_space β] {f : α → β} {s : set α}
  (hf : continuous_on f s) (hs : is_separable s) :
  is_separable (f '' s) :=
begin
  rw show f '' s = s.restrict f '' univ, by ext ; simp,
  exact (is_separable_univ_iff.2 hs.separable_space).image
    (continuous_on_iff_continuous_restrict.1 hf),
end

end metric

section pi
open finset
variables {π : β → Type*} [fintype β] [∀b, pseudo_metric_space (π b)]

/-- A finite product of pseudometric spaces is a pseudometric space, with the sup distance. -/
instance pseudo_metric_space_pi : pseudo_metric_space (Πb, π b) :=
begin
  /- we construct the instance from the pseudoemetric space instance to avoid checking again that
  the uniformity is the same as the product uniformity, but we register nevertheless a nice formula
  for the distance -/
  refine (pseudo_emetric_space.to_pseudo_metric_space_of_dist
    (λf g : Π b, π b, ((sup univ (λb, nndist (f b) (g b)) : ℝ≥0) : ℝ))
    (λ f g, _) (λ f g, _)).replace_bornology (λ s, _),
  show edist f g ≠ ⊤,
    from ne_of_lt ((finset.sup_lt_iff bot_lt_top).2 $ λ b hb, edist_lt_top _ _),
  show ↑(sup univ (λ b, nndist (f b) (g b))) = (sup univ (λ b, edist (f b) (g b))).to_real,
    by simp only [edist_nndist, ← ennreal.coe_finset_sup, ennreal.coe_to_real],
  show (@is_bounded _ pi.bornology s ↔ @is_bounded _ pseudo_metric_space.to_bornology _),
  { simp only [← is_bounded_def, is_bounded_iff_eventually, ← forall_is_bounded_image_eval_iff,
      ball_image_iff, ← eventually_all, function.eval_apply, @dist_nndist (π _)],
    refine eventually_congr ((eventually_ge_at_top 0).mono $ λ C hC, _),
    lift C to ℝ≥0 using hC,
    refine ⟨λ H x hx y hy, nnreal.coe_le_coe.2 $ finset.sup_le $ λ b hb, H b x hx y hy,
      λ H b x hx y hy, nnreal.coe_le_coe.2 _⟩,
    simpa only using finset.sup_le_iff.1 (nnreal.coe_le_coe.1 $ H hx hy) b (finset.mem_univ b) }
end

lemma nndist_pi_def (f g : Πb, π b) : nndist f g = sup univ (λb, nndist (f b) (g b)) :=
nnreal.eq rfl

lemma dist_pi_def (f g : Πb, π b) :
  dist f g = (sup univ (λb, nndist (f b) (g b)) : ℝ≥0) := rfl

lemma nndist_pi_le_iff {f g : Πb, π b} {r : ℝ≥0} :
  nndist f g ≤ r ↔ ∀b, nndist (f b) (g b) ≤ r :=
by simp [nndist_pi_def]

lemma dist_pi_lt_iff {f g : Πb, π b} {r : ℝ} (hr : 0 < r) :
  dist f g < r ↔ ∀b, dist (f b) (g b) < r :=
begin
  lift r to ℝ≥0 using hr.le,
  simp [dist_pi_def, finset.sup_lt_iff (show ⊥ < r, from hr)],
end

lemma dist_pi_le_iff {f g : Πb, π b} {r : ℝ} (hr : 0 ≤ r) :
  dist f g ≤ r ↔ ∀b, dist (f b) (g b) ≤ r :=
begin
  lift r to ℝ≥0 using hr,
  exact nndist_pi_le_iff
end

lemma dist_pi_le_iff' [nonempty β] {f g : Π b, π b} {r : ℝ} :
  dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r :=
begin
  by_cases hr : 0 ≤ r,
  { exact dist_pi_le_iff hr },
  { exact iff_of_false (λ h, hr $ dist_nonneg.trans h)
      (λ h, hr $ dist_nonneg.trans $ h $ classical.arbitrary _) }
end

lemma dist_pi_const_le (a b : α) : dist (λ _ : β, a) (λ _, b) ≤ dist a b :=
(dist_pi_le_iff dist_nonneg).2 $ λ _, le_rfl

lemma nndist_pi_const_le (a b : α) : nndist (λ _ : β, a) (λ _, b) ≤ nndist a b :=
nndist_pi_le_iff.2 $ λ _, le_rfl

@[simp] lemma dist_pi_const [nonempty β] (a b : α) : dist (λ x : β, a) (λ _, b) = dist a b :=
by simpa only [dist_edist] using congr_arg ennreal.to_real (edist_pi_const a b)

@[simp] lemma nndist_pi_const [nonempty β] (a b : α) :
  nndist (λ x : β, a) (λ _, b) = nndist a b := nnreal.eq $ dist_pi_const a b

lemma nndist_le_pi_nndist (f g : Πb, π b) (b : β) : nndist (f b) (g b) ≤ nndist f g :=
by { rw [nndist_pi_def], exact finset.le_sup (finset.mem_univ b) }

lemma dist_le_pi_dist (f g : Πb, π b) (b : β) : dist (f b) (g b) ≤ dist f g :=
by simp only [dist_nndist, nnreal.coe_le_coe, nndist_le_pi_nndist f g b]

/-- An open ball in a product space is a product of open balls. See also `metric.ball_pi'`
for a version assuming `nonempty β` instead of `0 < r`. -/
lemma ball_pi (x : Πb, π b) {r : ℝ} (hr : 0 < r) :
  ball x r = set.pi univ (λ b, ball (x b) r) :=
by { ext p, simp [dist_pi_lt_iff hr] }

/-- An open ball in a product space is a product of open balls. See also `metric.ball_pi`
for a version assuming `0 < r` instead of `nonempty β`. -/
lemma ball_pi' [nonempty β] (x : Π b, π b) (r : ℝ) :
  ball x r = set.pi univ (λ b, ball (x b) r) :=
(lt_or_le 0 r).elim (ball_pi x) $ λ hr, by simp [ball_eq_empty.2 hr]

/-- A closed ball in a product space is a product of closed balls. See also `metric.closed_ball_pi'`
for a version assuming `nonempty β` instead of `0 ≤ r`. -/
lemma closed_ball_pi (x : Πb, π b) {r : ℝ} (hr : 0 ≤ r) :
  closed_ball x r = set.pi univ (λ b, closed_ball (x b) r) :=
by { ext p, simp [dist_pi_le_iff hr] }

/-- A closed ball in a product space is a product of closed balls. See also `metric.closed_ball_pi`
for a version assuming `0 ≤ r` instead of `nonempty β`. -/
lemma closed_ball_pi' [nonempty β] (x : Π b, π b) (r : ℝ) :
  closed_ball x r = set.pi univ (λ b, closed_ball (x b) r) :=
(le_or_lt 0 r).elim (closed_ball_pi x) $ λ hr, by simp [closed_ball_eq_empty.2 hr]

@[simp] lemma fin.nndist_insert_nth_insert_nth {n : ℕ} {α : fin (n + 1) → Type*}
  [Π i, pseudo_metric_space (α i)] (i : fin (n + 1)) (x y : α i) (f g : Π j, α (i.succ_above j)) :
  nndist (i.insert_nth x f) (i.insert_nth y g) = max (nndist x y) (nndist f g) :=
eq_of_forall_ge_iff $ λ c, by simp [nndist_pi_le_iff, i.forall_iff_succ_above]

@[simp] lemma fin.dist_insert_nth_insert_nth {n : ℕ} {α : fin (n + 1) → Type*}
  [Π i, pseudo_metric_space (α i)] (i : fin (n + 1)) (x y : α i) (f g : Π j, α (i.succ_above j)) :
  dist (i.insert_nth x f) (i.insert_nth y g) = max (dist x y) (dist f g) :=
by simp only [dist_nndist, fin.nndist_insert_nth_insert_nth, nnreal.coe_max]

lemma real.dist_le_of_mem_pi_Icc {x y x' y' : β → ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') :
  dist x y ≤ dist x' y' :=
begin
  refine (dist_pi_le_iff dist_nonneg).2 (λ b, (real.dist_le_of_mem_interval _ _).trans
    (dist_le_pi_dist _ _ b)); refine Icc_subset_interval _,
  exacts [⟨hx.1 _, hx.2 _⟩, ⟨hy.1 _, hy.2 _⟩]
end

end pi

section compact

/-- Any compact set in a pseudometric space can be covered by finitely many balls of a given
positive radius -/
lemma finite_cover_balls_of_compact {α : Type u} [pseudo_metric_space α] {s : set α}
  (hs : is_compact s) {e : ℝ} (he : 0 < e) :
  ∃t ⊆ s, set.finite t ∧ s ⊆ ⋃x∈t, ball x e :=
begin
  apply hs.elim_finite_subcover_image,
  { simp [is_open_ball] },
  { intros x xs,
    simp,
    exact ⟨x, ⟨xs, by simpa⟩⟩ }
end

alias finite_cover_balls_of_compact ← is_compact.finite_cover_balls

end compact

section proper_space
open metric

/-- A pseudometric space is proper if all closed balls are compact. -/
class proper_space (α : Type u) [pseudo_metric_space α] : Prop :=
(is_compact_closed_ball : ∀x:α, ∀r, is_compact (closed_ball x r))

export proper_space (is_compact_closed_ball)

/-- In a proper pseudometric space, all spheres are compact. -/
lemma is_compact_sphere {α : Type*} [pseudo_metric_space α] [proper_space α] (x : α) (r : ℝ) :
  is_compact (sphere x r) :=
is_compact_of_is_closed_subset (is_compact_closed_ball x r) is_closed_sphere
sphere_subset_closed_ball

/-- In a proper pseudometric space, any sphere is a `compact_space` when considered as a subtype. -/
instance {α : Type*} [pseudo_metric_space α] [proper_space α] (x : α) (r : ℝ) :
  compact_space (sphere x r) :=
is_compact_iff_compact_space.mp (is_compact_sphere _ _)

/-- A proper pseudo metric space is sigma compact, and therefore second countable. -/
@[priority 100] -- see Note [lower instance priority]
instance second_countable_of_proper [proper_space α] :
  second_countable_topology α :=
begin
  -- We already have `sigma_compact_space_of_locally_compact_second_countable`, so we don't
  -- add an instance for `sigma_compact_space`.
  suffices : sigma_compact_space α, by exactI emetric.second_countable_of_sigma_compact α,
  rcases em (nonempty α) with ⟨⟨x⟩⟩|hn,
  { exact ⟨⟨λ n, closed_ball x n, λ n, is_compact_closed_ball _ _, Union_closed_ball_nat _⟩⟩ },
  { exact ⟨⟨λ n, ∅, λ n, is_compact_empty, Union_eq_univ_iff.2 $ λ x, (hn ⟨x⟩).elim⟩⟩ }
end

lemma tendsto_dist_right_cocompact_at_top [proper_space α] (x : α) :
  tendsto (λ y, dist y x) (cocompact α) at_top :=
(has_basis_cocompact.tendsto_iff at_top_basis).2 $ λ r hr,
  ⟨closed_ball x r, is_compact_closed_ball x r, λ y hy, (not_le.1 $ mt mem_closed_ball.2 hy).le⟩

lemma tendsto_dist_left_cocompact_at_top [proper_space α] (x : α) :
  tendsto (dist x) (cocompact α) at_top :=
by simpa only [dist_comm] using tendsto_dist_right_cocompact_at_top x

/-- If all closed balls of large enough radius are compact, then the space is proper. Especially
useful when the lower bound for the radius is 0. -/
lemma proper_space_of_compact_closed_ball_of_le
  (R : ℝ) (h : ∀x:α, ∀r, R ≤ r → is_compact (closed_ball x r)) :
  proper_space α :=
⟨begin
  assume x r,
  by_cases hr : R ≤ r,
  { exact h x r hr },
  { have : closed_ball x r = closed_ball x R ∩ closed_ball x r,
    { symmetry,
      apply inter_eq_self_of_subset_right,
      exact closed_ball_subset_closed_ball (le_of_lt (not_le.1 hr)) },
    rw this,
    exact (h x R le_rfl).inter_right is_closed_ball }
end⟩

/- A compact pseudometric space is proper -/
@[priority 100] -- see Note [lower instance priority]
instance proper_of_compact [compact_space α] : proper_space α :=
⟨assume x r, is_closed_ball.is_compact⟩

/-- A proper space is locally compact -/
@[priority 100] -- see Note [lower instance priority]
instance locally_compact_of_proper [proper_space α] :
  locally_compact_space α :=
locally_compact_space_of_has_basis (λ x, nhds_basis_closed_ball) $
  λ x ε ε0, is_compact_closed_ball _ _

/-- A proper space is complete -/
@[priority 100] -- see Note [lower instance priority]
instance complete_of_proper [proper_space α] : complete_space α :=
⟨begin
  intros f hf,
  /- We want to show that the Cauchy filter `f` is converging. It suffices to find a closed
  ball (therefore compact by properness) where it is nontrivial. -/
  obtain ⟨t, t_fset, ht⟩ : ∃ t ∈ f, ∀ x y ∈ t, dist x y < 1 :=
    (metric.cauchy_iff.1 hf).2 1 zero_lt_one,
  rcases hf.1.nonempty_of_mem t_fset with ⟨x, xt⟩,
  have : closed_ball x 1 ∈ f := mem_of_superset t_fset (λ y yt, (ht y yt x xt).le),
  rcases (is_compact_iff_totally_bounded_is_complete.1 (is_compact_closed_ball x 1)).2 f hf
    (le_principal_iff.2 this) with ⟨y, -, hy⟩,
  exact ⟨y, hy⟩
end⟩

/-- A finite product of proper spaces is proper. -/
instance pi_proper_space {π : β → Type*} [fintype β] [∀b, pseudo_metric_space (π b)]
  [h : ∀b, proper_space (π b)] : proper_space (Πb, π b) :=
begin
  refine proper_space_of_compact_closed_ball_of_le 0 (λx r hr, _),
  rw closed_ball_pi _ hr,
  apply is_compact_univ_pi (λb, _),
  apply (h b).is_compact_closed_ball
end

variables [proper_space α] {x : α} {r : ℝ} {s : set α}

/-- If a nonempty ball in a proper space includes a closed set `s`, then there exists a nonempty
ball with the same center and a strictly smaller radius that includes `s`. -/
lemma exists_pos_lt_subset_ball (hr : 0 < r) (hs : is_closed s) (h : s ⊆ ball x r) :
  ∃ r' ∈ Ioo 0 r, s ⊆ ball x r' :=
begin
  unfreezingI { rcases eq_empty_or_nonempty s with rfl|hne },
  { exact ⟨r / 2, ⟨half_pos hr, half_lt_self hr⟩, empty_subset _⟩ },
  have : is_compact s,
    from is_compact_of_is_closed_subset (is_compact_closed_ball x r) hs
      (subset.trans h ball_subset_closed_ball),
  obtain ⟨y, hys, hy⟩ : ∃ y ∈ s, s ⊆ closed_ball x (dist y x),
    from this.exists_forall_ge hne (continuous_id.dist continuous_const).continuous_on,
  have hyr : dist y x < r, from h hys,
  rcases exists_between hyr with ⟨r', hyr', hrr'⟩,
  exact ⟨r', ⟨dist_nonneg.trans_lt hyr', hrr'⟩, subset.trans hy $ closed_ball_subset_ball hyr'⟩
end

/-- If a ball in a proper space includes a closed set `s`, then there exists a ball with the same
center and a strictly smaller radius that includes `s`. -/
lemma exists_lt_subset_ball (hs : is_closed s) (h : s ⊆ ball x r) :
  ∃ r' < r, s ⊆ ball x r' :=
begin
  cases le_or_lt r 0 with hr hr,
  { rw [ball_eq_empty.2 hr, subset_empty_iff] at h, unfreezingI { subst s },
    exact (exists_lt r).imp (λ r' hr', ⟨hr', empty_subset _⟩) },
  { exact (exists_pos_lt_subset_ball hr hs h).imp (λ r' hr', ⟨hr'.fst.2, hr'.snd⟩) }
end

end proper_space

lemma is_compact.is_separable {s : set α} (hs : is_compact s) :
  is_separable s :=
begin
  haveI : compact_space s := is_compact_iff_compact_space.mp hs,
  exact is_separable_of_separable_space_subtype s,
end

namespace metric
section second_countable
open topological_space

/-- A pseudometric space is second countable if, for every `ε > 0`, there is a countable set which
is `ε`-dense. -/
lemma second_countable_of_almost_dense_set
  (H : ∀ε > (0 : ℝ), ∃ s : set α, s.countable ∧ (∀x, ∃y ∈ s, dist x y ≤ ε)) :
  second_countable_topology α :=
begin
  refine emetric.second_countable_of_almost_dense_set (λ ε ε0, _),
  rcases ennreal.lt_iff_exists_nnreal_btwn.1 ε0 with ⟨ε', ε'0, ε'ε⟩,
  choose s hsc y hys hyx using H ε' (by exact_mod_cast ε'0),
  refine ⟨s, hsc, Union₂_eq_univ_iff.2 (λ x, ⟨y x, hys _, le_trans _ ε'ε.le⟩)⟩,
  exact_mod_cast hyx x
end

end second_countable
end metric

lemma lebesgue_number_lemma_of_metric
  {s : set α} {ι} {c : ι → set α} (hs : is_compact s)
  (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
  ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i :=
let ⟨n, en, hn⟩ := lebesgue_number_lemma hs hc₁ hc₂,
    ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 en in
⟨δ, δ0, assume x hx, let ⟨i, hi⟩ := hn x hx in
 ⟨i, assume y hy, hi (hδ (mem_ball'.mp hy))⟩⟩

lemma lebesgue_number_lemma_of_metric_sUnion
  {s : set α} {c : set (set α)} (hs : is_compact s)
  (hc₁ : ∀ t ∈ c, is_open t) (hc₂ : s ⊆ ⋃₀ c) :
  ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, ball x δ ⊆ t :=
by rw sUnion_eq_Union at hc₂;
   simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂

namespace metric

/-- Boundedness of a subset of a pseudometric space. We formulate the definition to work
even in the empty space. -/
def bounded (s : set α) : Prop :=
∃C, ∀x y ∈ s, dist x y ≤ C

section bounded
variables {x : α} {s t : set α} {r : ℝ}

lemma bounded_iff_is_bounded (s : set α) : bounded s ↔ is_bounded s :=
begin
  change bounded s ↔ sᶜ ∈ (cobounded α).sets,
  simp [pseudo_metric_space.cobounded_sets, metric.bounded],
end

@[simp] lemma bounded_empty : bounded (∅ : set α) :=
⟨0, by simp⟩

lemma bounded_iff_mem_bounded : bounded s ↔ ∀ x ∈ s, bounded s :=
⟨λ h _ _, h, λ H,
  s.eq_empty_or_nonempty.elim
  (λ hs, hs.symm ▸ bounded_empty)
  (λ ⟨x, hx⟩, H x hx)⟩

/-- Subsets of a bounded set are also bounded -/
lemma bounded.mono (incl : s ⊆ t) : bounded t → bounded s :=
Exists.imp $ λ C hC x hx y hy, hC x (incl hx) y (incl hy)

/-- Closed balls are bounded -/
lemma bounded_closed_ball : bounded (closed_ball x r) :=
⟨r + r, λ y hy z hz, begin
  simp only [mem_closed_ball] at *,
  calc dist y z ≤ dist y x + dist z x : dist_triangle_right _ _ _
            ... ≤ r + r : add_le_add hy hz
end⟩

/-- Open balls are bounded -/
lemma bounded_ball : bounded (ball x r) :=
bounded_closed_ball.mono ball_subset_closed_ball

/-- Spheres are bounded -/
lemma bounded_sphere : bounded (sphere x r) :=
bounded_closed_ball.mono sphere_subset_closed_ball

/-- Given a point, a bounded subset is included in some ball around this point -/
lemma bounded_iff_subset_ball (c : α) : bounded s ↔ ∃r, s ⊆ closed_ball c r :=
begin
  split; rintro ⟨C, hC⟩,
  { cases s.eq_empty_or_nonempty with h h,
    { subst s, exact ⟨0, by simp⟩ },
    { rcases h with ⟨x, hx⟩,
      exact ⟨C + dist x c, λ y hy, calc
        dist y c ≤ dist y x + dist x c : dist_triangle _ _ _
            ... ≤ C + dist x c : add_le_add_right (hC y hy x hx) _⟩ } },
  { exact bounded_closed_ball.mono hC }
end

lemma bounded.subset_ball (h : bounded s) (c : α) : ∃ r, s ⊆ closed_ball c r :=
(bounded_iff_subset_ball c).1 h

lemma bounded.subset_ball_lt (h : bounded s) (a : ℝ) (c : α) : ∃ r, a < r ∧ s ⊆ closed_ball c r :=
begin
  rcases h.subset_ball c with ⟨r, hr⟩,
  refine ⟨max r (a+1), lt_of_lt_of_le (by linarith) (le_max_right _ _), _⟩,
  exact subset.trans hr (closed_ball_subset_closed_ball (le_max_left _ _))
end

lemma bounded_closure_of_bounded (h : bounded s) : bounded (closure s) :=
let ⟨C, h⟩ := h in
⟨C, λ a ha b hb, (is_closed_le' C).closure_subset $ map_mem_closure₂ continuous_dist ha hb h⟩

alias bounded_closure_of_bounded ← bounded.closure

@[simp] lemma bounded_closure_iff : bounded (closure s) ↔ bounded s :=
⟨λ h, h.mono subset_closure, λ h, h.closure⟩

/-- The union of two bounded sets is bounded. -/
lemma bounded.union (hs : bounded s) (ht : bounded t) : bounded (s ∪ t) :=
begin
  refine bounded_iff_mem_bounded.2 (λ x _, _),
  rw bounded_iff_subset_ball x at hs ht ⊢,
  rcases hs with ⟨Cs, hCs⟩, rcases ht with ⟨Ct, hCt⟩,
  exact ⟨max Cs Ct, union_subset
    (subset.trans hCs $ closed_ball_subset_closed_ball $ le_max_left _ _)
    (subset.trans hCt $ closed_ball_subset_closed_ball $ le_max_right _ _)⟩,
end

/-- The union of two sets is bounded iff each of the sets is bounded. -/
@[simp] lemma bounded_union : bounded (s ∪ t) ↔ bounded s ∧ bounded t :=
⟨λ h, ⟨h.mono (by simp), h.mono (by simp)⟩, λ h, h.1.union h.2⟩

/-- A finite union of bounded sets is bounded -/
lemma bounded_bUnion {I : set β} {s : β → set α} (H : I.finite) :
  bounded (⋃i∈I, s i) ↔ ∀i ∈ I, bounded (s i) :=
finite.induction_on H (by simp) $ λ x I _ _ IH,
by simp [or_imp_distrib, forall_and_distrib, IH]

protected lemma bounded.prod [pseudo_metric_space β] {s : set α} {t : set β}
  (hs : bounded s) (ht : bounded t) : bounded (s ×ˢ t) :=
begin
  refine bounded_iff_mem_bounded.mpr (λ x hx, _),
  rcases hs.subset_ball x.1 with ⟨rs, hrs⟩,
  rcases ht.subset_ball x.2 with ⟨rt, hrt⟩,
  suffices : s ×ˢ t ⊆ closed_ball x (max rs rt),
    from bounded_closed_ball.mono this,
  rw [← @prod.mk.eta _ _ x, ← closed_ball_prod_same],
  exact prod_mono (hrs.trans $ closed_ball_subset_closed_ball $ le_max_left _ _)
    (hrt.trans $ closed_ball_subset_closed_ball $ le_max_right _ _)
end

/-- A totally bounded set is bounded -/
lemma _root_.totally_bounded.bounded {s : set α} (h : totally_bounded s) : bounded s :=
-- We cover the totally bounded set by finitely many balls of radius 1,
-- and then argue that a finite union of bounded sets is bounded
let ⟨t, fint, subs⟩ := (totally_bounded_iff.mp h) 1 zero_lt_one in
bounded.mono subs $ (bounded_bUnion fint).2 $ λ i hi, bounded_ball

/-- A compact set is bounded -/
lemma _root_.is_compact.bounded {s : set α} (h : is_compact s) : bounded s :=
-- A compact set is totally bounded, thus bounded
h.totally_bounded.bounded

/-- A finite set is bounded -/
lemma bounded_of_finite {s : set α} (h : s.finite) : bounded s :=
h.is_compact.bounded

alias bounded_of_finite ← _root_.set.finite.bounded

/-- A singleton is bounded -/
lemma bounded_singleton {x : α} : bounded ({x} : set α) :=
bounded_of_finite $ finite_singleton _

/-- Characterization of the boundedness of the range of a function -/
lemma bounded_range_iff {f : β → α} : bounded (range f) ↔ ∃C, ∀x y, dist (f x) (f y) ≤ C :=
exists_congr $ λ C, ⟨
  λ H x y, H _ ⟨x, rfl⟩ _ ⟨y, rfl⟩,
  by rintro H _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact H x y⟩

lemma bounded_range_of_tendsto_cofinite_uniformity {f : β → α}
  (hf : tendsto (prod.map f f) (cofinite ×ᶠ cofinite) (𝓤 α)) :
  bounded (range f) :=
begin
  rcases (has_basis_cofinite.prod_self.tendsto_iff uniformity_basis_dist).1 hf 1 zero_lt_one
    with ⟨s, hsf, hs1⟩,
  rw [← image_univ, ← union_compl_self s, image_union, bounded_union],
  use [(hsf.image f).bounded, 1],
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
  exact le_of_lt (hs1 (x, y) ⟨hx, hy⟩)
end

lemma bounded_range_of_cauchy_map_cofinite {f : β → α} (hf : cauchy (map f cofinite)) :
  bounded (range f) :=
bounded_range_of_tendsto_cofinite_uniformity $ (cauchy_map_iff.1 hf).2

lemma _root_.cauchy_seq.bounded_range {f : ℕ → α} (hf : cauchy_seq f) : bounded (range f) :=
bounded_range_of_cauchy_map_cofinite $ by rwa nat.cofinite_eq_at_top

lemma bounded_range_of_tendsto_cofinite {f : β → α} {a : α} (hf : tendsto f cofinite (𝓝 a)) :
  bounded (range f) :=
bounded_range_of_tendsto_cofinite_uniformity $
  (hf.prod_map hf).mono_right $ nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)

/-- In a compact space, all sets are bounded -/
lemma bounded_of_compact_space [compact_space α] : bounded s :=
is_compact_univ.bounded.mono (subset_univ _)

lemma bounded_range_of_tendsto (u : ℕ → α) {x : α} (hu : tendsto u at_top (𝓝 x)) :
  bounded (range u) :=
hu.cauchy_seq.bounded_range

/-- If a function is continuous at every point of a compact set `k`, then it is bounded on
some open neighborhood of `k`. -/
lemma exists_is_open_bounded_image_of_is_compact_of_forall_continuous_at
  [topological_space β] {k : set β} {f : β → α}
  (hk : is_compact k) (hf : ∀ x ∈ k, continuous_at f x) :
  ∃ t, k ⊆ t ∧ is_open t ∧ bounded (f '' t) :=
begin
  apply hk.induction_on,
  { refine ⟨∅, subset.refl _, is_open_empty, by simp only [image_empty, bounded_empty]⟩ },
  { rintros s s' hss' ⟨t, s't, t_open, t_bounded⟩,
    exact ⟨t, hss'.trans s't, t_open, t_bounded⟩ },
  { rintros s s' ⟨t, st, t_open, t_bounded⟩ ⟨t', s't', t'_open, t'_bounded⟩,
    refine ⟨t ∪ t', union_subset_union st s't', t_open.union t'_open, _⟩,
    rw image_union,
    exact t_bounded.union t'_bounded },
  { assume x hx,
    have A : ball (f x) 1 ∈ 𝓝 (f x), from ball_mem_nhds _ zero_lt_one,
    have B : f ⁻¹' (ball (f x) 1) ∈ 𝓝 x, from hf x hx A,
    obtain ⟨u, uf, u_open, xu⟩ : ∃ (u : set β) (H : u ⊆ f ⁻¹' ball (f x) 1), is_open u ∧ x ∈ u,
      from _root_.mem_nhds_iff.1 B,
    refine ⟨u, _, u, subset.refl _, u_open, _⟩,
    { apply nhds_within_le_nhds,
      exact u_open.mem_nhds xu },
    { apply bounded.mono (image_subset _ uf),
      exact bounded_ball.mono (image_preimage_subset _ _) } }
end

/-- If a function is continuous on a neighborhood of a compact set `k`, then it is bounded on
some open neighborhood of `k`. -/
lemma exists_is_open_bounded_image_of_is_compact_of_continuous_on
  [topological_space β] {k s : set β} {f : β → α}
  (hk : is_compact k) (hs : is_open s) (hks : k ⊆ s) (hf : continuous_on f s) :
  ∃ t, k ⊆ t ∧ is_open t ∧ bounded (f '' t) :=
begin
  apply exists_is_open_bounded_image_of_is_compact_of_forall_continuous_at hk
  (λ x hx, hf.continuous_at (hs.mem_nhds (hks hx))),
end

/-- The **Heine–Borel theorem**: In a proper space, a closed bounded set is compact. -/
lemma is_compact_of_is_closed_bounded [proper_space α] (hc : is_closed s) (hb : bounded s) :
  is_compact s :=
begin
  unfreezingI { rcases eq_empty_or_nonempty s with (rfl|⟨x, hx⟩) },
  { exact is_compact_empty },
  { rcases hb.subset_ball x with ⟨r, hr⟩,
    exact is_compact_of_is_closed_subset (is_compact_closed_ball x r) hc hr }
end

/-- The **Heine–Borel theorem**: In a proper space, the closure of a bounded set is compact. -/
lemma bounded.is_compact_closure [proper_space α] (h : bounded s) :
  is_compact (closure s) :=
is_compact_of_is_closed_bounded is_closed_closure h.closure

/-- The **Heine–Borel theorem**:
In a proper Hausdorff space, a set is compact if and only if it is closed and bounded. -/
lemma is_compact_iff_is_closed_bounded [t2_space α] [proper_space α] :
  is_compact s ↔ is_closed s ∧ bounded s :=
⟨λ h, ⟨h.is_closed, h.bounded⟩, λ h, is_compact_of_is_closed_bounded h.1 h.2⟩

lemma compact_space_iff_bounded_univ [proper_space α] : compact_space α ↔ bounded (univ : set α) :=
⟨@bounded_of_compact_space α _ _, λ hb, ⟨is_compact_of_is_closed_bounded is_closed_univ hb⟩⟩

section conditionally_complete_linear_order

variables [preorder α] [compact_Icc_space α]

lemma bounded_Icc (a b : α) : bounded (Icc a b) :=
(totally_bounded_Icc a b).bounded

lemma bounded_Ico (a b : α) : bounded (Ico a b) :=
(totally_bounded_Ico a b).bounded

lemma bounded_Ioc (a b : α) : bounded (Ioc a b) :=
(totally_bounded_Ioc a b).bounded

lemma bounded_Ioo (a b : α) : bounded (Ioo a b) :=
(totally_bounded_Ioo a b).bounded

/-- In a pseudo metric space with a conditionally complete linear order such that the order and the
    metric structure give the same topology, any order-bounded set is metric-bounded. -/
lemma bounded_of_bdd_above_of_bdd_below {s : set α} (h₁ : bdd_above s) (h₂ : bdd_below s) :
  bounded s :=
let ⟨u, hu⟩ := h₁, ⟨l, hl⟩ := h₂ in
bounded.mono (λ x hx, mem_Icc.mpr ⟨hl hx, hu hx⟩) (bounded_Icc l u)

end conditionally_complete_linear_order

end bounded

section diam
variables {s : set α} {x y z : α}

/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the emetric.diameter -/
noncomputable def diam (s : set α) : ℝ := ennreal.to_real (emetric.diam s)

/-- The diameter of a set is always nonnegative -/
lemma diam_nonneg : 0 ≤ diam s := ennreal.to_real_nonneg

lemma diam_subsingleton (hs : s.subsingleton) : diam s = 0 :=
by simp only [diam, emetric.diam_subsingleton hs, ennreal.zero_to_real]

/-- The empty set has zero diameter -/
@[simp] lemma diam_empty : diam (∅ : set α) = 0 :=
diam_subsingleton subsingleton_empty

/-- A singleton has zero diameter -/
@[simp] lemma diam_singleton : diam ({x} : set α) = 0 :=
diam_subsingleton subsingleton_singleton

-- Does not work as a simp-lemma, since {x, y} reduces to (insert y {x})
lemma diam_pair : diam ({x, y} : set α) = dist x y :=
by simp only [diam, emetric.diam_pair, dist_edist]

-- Does not work as a simp-lemma, since {x, y, z} reduces to (insert z (insert y {x}))
lemma diam_triple :
  metric.diam ({x, y, z} : set α) = max (max (dist x y) (dist x z)) (dist y z) :=
begin
  simp only [metric.diam, emetric.diam_triple, dist_edist],
  rw [ennreal.to_real_max, ennreal.to_real_max];
    apply_rules [ne_of_lt, edist_lt_top, max_lt]
end

/-- If the distance between any two points in a set is bounded by some constant `C`,
then `ennreal.of_real C`  bounds the emetric diameter of this set. -/
lemma ediam_le_of_forall_dist_le {C : ℝ} (h : ∀ (x ∈ s) (y ∈ s), dist x y ≤ C) :
  emetric.diam s ≤ ennreal.of_real C :=
emetric.diam_le $
λ x hx y hy, (edist_dist x y).symm ▸ ennreal.of_real_le_of_real (h x hx y hy)

/-- If the distance between any two points in a set is bounded by some non-negative constant,
this constant bounds the diameter. -/
lemma diam_le_of_forall_dist_le {C : ℝ} (h₀ : 0 ≤ C) (h : ∀ (x ∈ s) (y ∈ s), dist x y ≤ C) :
  diam s ≤ C :=
ennreal.to_real_le_of_le_of_real h₀ (ediam_le_of_forall_dist_le h)

/-- If the distance between any two points in a nonempty set is bounded by some constant,
this constant bounds the diameter. -/
lemma diam_le_of_forall_dist_le_of_nonempty (hs : s.nonempty) {C : ℝ}
  (h : ∀ (x ∈ s) (y ∈ s), dist x y ≤ C) : diam s ≤ C :=
have h₀ : 0 ≤ C, from let ⟨x, hx⟩ := hs in le_trans dist_nonneg (h x hx x hx),
diam_le_of_forall_dist_le h₀ h

/-- The distance between two points in a set is controlled by the diameter of the set. -/
lemma dist_le_diam_of_mem' (h : emetric.diam s ≠ ⊤) (hx : x ∈ s) (hy : y ∈ s) :
  dist x y ≤ diam s :=
begin
  rw [diam, dist_edist],
  rw ennreal.to_real_le_to_real (edist_ne_top _ _) h,
  exact emetric.edist_le_diam_of_mem hx hy
end

/-- Characterize the boundedness of a set in terms of the finiteness of its emetric.diameter. -/
lemma bounded_iff_ediam_ne_top : bounded s ↔ emetric.diam s ≠ ⊤ :=
iff.intro
  (λ ⟨C, hC⟩, ne_top_of_le_ne_top ennreal.of_real_ne_top $ ediam_le_of_forall_dist_le hC)
  (λ h, ⟨diam s, λ x hx y hy, dist_le_diam_of_mem' h hx hy⟩)

lemma bounded.ediam_ne_top (h : bounded s) : emetric.diam s ≠ ⊤ :=
bounded_iff_ediam_ne_top.1 h

lemma ediam_univ_eq_top_iff_noncompact [proper_space α] :
  emetric.diam (univ : set α) = ∞ ↔ noncompact_space α :=
by rw [← not_compact_space_iff, compact_space_iff_bounded_univ, bounded_iff_ediam_ne_top, not_not]

@[simp] lemma ediam_univ_of_noncompact [proper_space α] [noncompact_space α] :
  emetric.diam (univ : set α) = ∞ :=
ediam_univ_eq_top_iff_noncompact.mpr ‹_›

@[simp] lemma diam_univ_of_noncompact [proper_space α] [noncompact_space α] :
  diam (univ : set α) = 0 :=
by simp [diam]

/-- The distance between two points in a set is controlled by the diameter of the set. -/
lemma dist_le_diam_of_mem (h : bounded s) (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ diam s :=
dist_le_diam_of_mem' h.ediam_ne_top hx hy

lemma ediam_of_unbounded (h : ¬(bounded s)) : emetric.diam s = ∞ :=
by rwa [bounded_iff_ediam_ne_top, not_not] at h

/-- An unbounded set has zero diameter. If you would prefer to get the value ∞, use `emetric.diam`.
This lemma makes it possible to avoid side conditions in some situations -/
lemma diam_eq_zero_of_unbounded (h : ¬(bounded s)) : diam s = 0 :=
by rw [diam, ediam_of_unbounded h, ennreal.top_to_real]

/-- If `s ⊆ t`, then the diameter of `s` is bounded by that of `t`, provided `t` is bounded. -/
lemma diam_mono {s t : set α} (h : s ⊆ t) (ht : bounded t) : diam s ≤ diam t :=
begin
  unfold diam,
  rw ennreal.to_real_le_to_real (bounded.mono h ht).ediam_ne_top ht.ediam_ne_top,
  exact emetric.diam_mono h
end

/-- The diameter of a union is controlled by the sum of the diameters, and the distance between
any two points in each of the sets. This lemma is true without any side condition, since it is
obviously true if `s ∪ t` is unbounded. -/
lemma diam_union {t : set α} (xs : x ∈ s) (yt : y ∈ t) :
  diam (s ∪ t) ≤ diam s + dist x y + diam t :=
begin
  by_cases H : bounded (s ∪ t),
  { have hs : bounded s, from H.mono (subset_union_left _ _),
    have ht : bounded t, from H.mono (subset_union_right _ _),
    rw [bounded_iff_ediam_ne_top] at H hs ht,
    rw [dist_edist, diam, diam, diam, ← ennreal.to_real_add, ← ennreal.to_real_add,
      ennreal.to_real_le_to_real];
      repeat { apply ennreal.add_ne_top.2; split }; try { assumption };
      try { apply edist_ne_top },
    exact emetric.diam_union xs yt },
  { rw [diam_eq_zero_of_unbounded H],
    apply_rules [add_nonneg, diam_nonneg, dist_nonneg] }
end

/-- If two sets intersect, the diameter of the union is bounded by the sum of the diameters. -/
lemma diam_union' {t : set α} (h : (s ∩ t).nonempty) : diam (s ∪ t) ≤ diam s + diam t :=
begin
  rcases h with ⟨x, ⟨xs, xt⟩⟩,
  simpa using diam_union xs xt
end

lemma diam_le_of_subset_closed_ball {r : ℝ} (hr : 0 ≤ r) (h : s ⊆ closed_ball x r) :
  diam s ≤ 2 * r :=
diam_le_of_forall_dist_le (mul_nonneg zero_le_two hr) $ λa ha b hb, calc
  dist a b ≤ dist a x + dist b x : dist_triangle_right _ _ _
  ... ≤ r + r : add_le_add (h ha) (h hb)
  ... = 2 * r : by simp [mul_two, mul_comm]

/-- The diameter of a closed ball of radius `r` is at most `2 r`. -/
lemma diam_closed_ball {r : ℝ} (h : 0 ≤ r) : diam (closed_ball x r) ≤ 2 * r :=
diam_le_of_subset_closed_ball h subset.rfl

/-- The diameter of a ball of radius `r` is at most `2 r`. -/
lemma diam_ball {r : ℝ} (h : 0 ≤ r) : diam (ball x r) ≤ 2 * r :=
diam_le_of_subset_closed_ball h ball_subset_closed_ball

/-- If a family of complete sets with diameter tending to `0` is such that each finite intersection
is nonempty, then the total intersection is also nonempty. -/
lemma _root_.is_complete.nonempty_Inter_of_nonempty_bInter {s : ℕ → set α} (h0 : is_complete (s 0))
  (hs : ∀ n, is_closed (s n)) (h's : ∀ n, bounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).nonempty)
  (h' : tendsto (λ n, diam (s n)) at_top (𝓝 0)) :
  (⋂ n, s n).nonempty :=
begin
  let u := λ N, (h N).some,
  have I : ∀ n N, n ≤ N → u N ∈ s n,
  { assume n N hn,
    apply mem_of_subset_of_mem _ ((h N).some_spec),
    assume x hx,
    simp only [mem_Inter] at hx,
    exact hx n hn },
  have : ∀ n, u n ∈ s 0 := λ n, I 0 n (zero_le _),
  have : cauchy_seq u,
  { apply cauchy_seq_of_le_tendsto_0 _ _ h',
    assume m n N hm hn,
    exact dist_le_diam_of_mem (h's N) (I _ _ hm) (I _ _ hn) },
  obtain ⟨x, hx, xlim⟩ : ∃ (x : α) (H : x ∈ s 0), tendsto (λ (n : ℕ), u n) at_top (𝓝 x) :=
    cauchy_seq_tendsto_of_is_complete h0 (λ n, I 0 n (zero_le _)) this,
  refine ⟨x, mem_Inter.2 (λ n, _)⟩,
  apply (hs n).mem_of_tendsto xlim,
  filter_upwards [Ici_mem_at_top n] with p hp,
  exact I n p hp,
end

/-- In a complete space, if a family of closed sets with diameter tending to `0` is such that each
finite intersection is nonempty, then the total intersection is also nonempty. -/
lemma nonempty_Inter_of_nonempty_bInter [complete_space α] {s : ℕ → set α}
  (hs : ∀ n, is_closed (s n)) (h's : ∀ n, bounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).nonempty)
  (h' : tendsto (λ n, diam (s n)) at_top (𝓝 0)) :
  (⋂ n, s n).nonempty :=
(hs 0).is_complete.nonempty_Inter_of_nonempty_bInter hs h's h h'

end diam

lemma exists_local_min_mem_ball [proper_space α] [topological_space β]
  [conditionally_complete_linear_order β] [order_topology β]
  {f : α → β} {a z : α} {r : ℝ} (hf : continuous_on f (closed_ball a r))
  (hz : z ∈ closed_ball a r) (hf1 : ∀ z' ∈ sphere a r, f z < f z') :
  ∃ z ∈ ball a r, is_local_min f z :=
begin
  simp_rw [← closed_ball_diff_ball] at hf1,
  exact (is_compact_closed_ball a r).exists_local_min_mem_open ball_subset_closed_ball hf hz hf1
    is_open_ball,
end

end metric

namespace tactic
open positivity

/-- Extension for the `positivity` tactic: the diameter of a set is always nonnegative. -/
@[positivity]
meta def positivity_diam : expr → tactic strictness
| `(metric.diam %%s) := nonnegative <$> mk_app ``metric.diam_nonneg [s]
| e := pp e >>= fail ∘ format.bracket "The expression " " is not of the form `metric.diam s`"

end tactic

lemma comap_dist_right_at_top_le_cocompact (x : α) : comap (λ y, dist y x) at_top ≤ cocompact α :=
begin
  refine filter.has_basis_cocompact.ge_iff.2 (λ s hs, mem_comap.2 _),
  rcases hs.bounded.subset_ball x with ⟨r, hr⟩,
  exact ⟨Ioi r, Ioi_mem_at_top r, λ y hy hys, (mem_closed_ball.1 $ hr hys).not_lt hy⟩
end

lemma comap_dist_left_at_top_le_cocompact (x : α) : comap (dist x) at_top ≤ cocompact α :=
by simpa only [dist_comm _ x] using comap_dist_right_at_top_le_cocompact x

lemma comap_dist_right_at_top_eq_cocompact [proper_space α] (x : α) :
  comap (λ y, dist y x) at_top = cocompact α :=
(comap_dist_right_at_top_le_cocompact x).antisymm $ (tendsto_dist_right_cocompact_at_top x).le_comap

lemma comap_dist_left_at_top_eq_cocompact [proper_space α] (x : α) :
  comap (dist x) at_top = cocompact α :=
(comap_dist_left_at_top_le_cocompact x).antisymm $ (tendsto_dist_left_cocompact_at_top x).le_comap

lemma tendsto_cocompact_of_tendsto_dist_comp_at_top {f : β → α} {l : filter β} (x : α)
  (h : tendsto (λ y, dist (f y) x) l at_top) : tendsto f l (cocompact α) :=
by { refine tendsto.mono_right _ (comap_dist_right_at_top_le_cocompact x), rwa tendsto_comap_iff }

/-- We now define `metric_space`, extending `pseudo_metric_space`. -/
class metric_space (α : Type u) extends pseudo_metric_space α : Type u :=
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)

/-- Two metric space structures with the same distance coincide. -/
@[ext] lemma metric_space.ext {α : Type*} {m m' : metric_space α}
  (h : m.to_has_dist = m'.to_has_dist) : m = m' :=
begin
  have h' : m.to_pseudo_metric_space = m'.to_pseudo_metric_space := pseudo_metric_space.ext h,
  unfreezingI { rcases m, rcases m' },
  dsimp at h',
  unfreezingI { subst h' },
end

/-- Construct a metric space structure whose underlying topological space structure
(definitionally) agrees which a pre-existing topology which is compatible with a given distance
function. -/
def metric_space.of_metrizable {α : Type*} [topological_space α] (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
  (H : ∀ s : set α, is_open s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s)
  (eq_of_dist_eq_zero : ∀ x y : α, dist x y = 0 → x = y) : metric_space α :=
{ eq_of_dist_eq_zero := eq_of_dist_eq_zero,
  ..pseudo_metric_space.of_metrizable dist dist_self dist_comm dist_triangle H }

variables {γ : Type w} [metric_space γ]

theorem eq_of_dist_eq_zero {x y : γ} : dist x y = 0 → x = y :=
metric_space.eq_of_dist_eq_zero

@[simp] theorem dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y :=
iff.intro eq_of_dist_eq_zero (assume : x = y, this ▸ dist_self _)

@[simp] theorem zero_eq_dist {x y : γ} : 0 = dist x y ↔ x = y :=
by rw [eq_comm, dist_eq_zero]

theorem dist_ne_zero {x y : γ} : dist x y ≠ 0 ↔ x ≠ y :=
by simpa only [not_iff_not] using dist_eq_zero

@[simp] theorem dist_le_zero {x y : γ} : dist x y ≤ 0 ↔ x = y :=
by simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp] theorem dist_pos {x y : γ} : 0 < dist x y ↔ x ≠ y :=
by simpa only [not_le] using not_congr dist_le_zero

theorem eq_of_forall_dist_le {x y : γ} (h : ∀ ε > 0, dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

/--Deduce the equality of points with the vanishing of the nonnegative distance-/
theorem eq_of_nndist_eq_zero {x y : γ} : nndist x y = 0 → x = y :=
by simp only [← nnreal.eq_iff, ← dist_nndist, imp_self, nnreal.coe_zero, dist_eq_zero]

/--Characterize the equality of points with the vanishing of the nonnegative distance-/
@[simp] theorem nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y :=
by simp only [← nnreal.eq_iff, ← dist_nndist, imp_self, nnreal.coe_zero, dist_eq_zero]

@[simp] theorem zero_eq_nndist {x y : γ} : 0 = nndist x y ↔ x = y :=
by simp only [← nnreal.eq_iff, ← dist_nndist, imp_self, nnreal.coe_zero, zero_eq_dist]

namespace metric

variables {x : γ} {s : set γ}

@[simp] lemma closed_ball_zero : closed_ball x 0 = {x} :=
set.ext $ λ y, dist_le_zero

@[simp] lemma sphere_zero : sphere x 0 = {x} :=
set.ext $ λ y, dist_eq_zero

lemma subsingleton_closed_ball (x : γ) {r : ℝ} (hr : r ≤ 0) : (closed_ball x r).subsingleton :=
begin
  rcases hr.lt_or_eq with hr|rfl,
  { rw closed_ball_eq_empty.2 hr, exact subsingleton_empty },
  { rw closed_ball_zero, exact subsingleton_singleton }
end

lemma subsingleton_sphere (x : γ) {r : ℝ} (hr : r ≤ 0) : (sphere x r).subsingleton :=
(subsingleton_closed_ball x hr).anti sphere_subset_closed_ball

/-- A map between metric spaces is a uniform embedding if and only if the distance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem uniform_embedding_iff' [metric_space β] {f : γ → β} :
  uniform_embedding f ↔
  (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, dist a b < δ → dist (f a) (f b) < ε) ∧
  (∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, dist (f a) (f b) < ε → dist a b < δ) :=
begin
  split,
  { assume h,
    exact ⟨uniform_continuous_iff.1 (uniform_embedding_iff.1 h).2.1,
          (uniform_embedding_iff.1 h).2.2⟩ },
  { rintros ⟨h₁, h₂⟩,
    refine uniform_embedding_iff.2 ⟨_, uniform_continuous_iff.2 h₁, h₂⟩,
    assume x y hxy,
    have : dist x y ≤ 0,
    { refine le_of_forall_lt' (λδ δpos, _),
      rcases h₂ δ δpos with ⟨ε, εpos, hε⟩,
      have : dist (f x) (f y) < ε, by simpa [hxy],
      exact hε this },
    simpa using this }
end

@[priority 100] -- see Note [lower instance priority]
instance _root_.metric_space.to_separated : separated_space γ :=
separated_def.2 $ λ x y h, eq_of_forall_dist_le $
  λ ε ε0, le_of_lt (h _ (dist_mem_uniformity ε0))

/-- If a `pseudo_metric_space` is a T₀ space, then it is a `metric_space`. -/
def of_t0_pseudo_metric_space (α : Type*) [pseudo_metric_space α] [t0_space α] :
  metric_space α :=
{ eq_of_dist_eq_zero := λ x y hdist, inseparable.eq $ metric.inseparable_iff.2 hdist,
  ..‹pseudo_metric_space α› }

/-- A metric space induces an emetric space -/
@[priority 100] -- see Note [lower instance priority]
instance metric_space.to_emetric_space : emetric_space γ :=
emetric.of_t0_pseudo_emetric_space γ

lemma is_closed_of_pairwise_le_dist {s : set γ} {ε : ℝ} (hε : 0 < ε)
  (hs : s.pairwise (λ x y, ε ≤ dist x y)) : is_closed s :=
is_closed_of_spaced_out (dist_mem_uniformity hε) $ by simpa using hs

lemma closed_embedding_of_pairwise_le_dist {α : Type*} [topological_space α] [discrete_topology α]
  {ε : ℝ} (hε : 0 < ε) {f : α → γ} (hf : pairwise (λ x y, ε ≤ dist (f x) (f y))) :
  closed_embedding f :=
closed_embedding_of_spaced_out (dist_mem_uniformity hε) $ by simpa using hf

/-- If `f : β → α` sends any two distinct points to points at distance at least `ε > 0`, then
`f` is a uniform embedding with respect to the discrete uniformity on `β`. -/
lemma uniform_embedding_bot_of_pairwise_le_dist {β : Type*} {ε : ℝ} (hε : 0 < ε) {f : β → α}
  (hf : pairwise (λ x y, ε ≤ dist (f x) (f y))) : @uniform_embedding _ _ ⊥ (by apply_instance) f :=
uniform_embedding_of_spaced_out (dist_mem_uniformity hε) $ by simpa using hf

end metric

/-- Build a new metric space from an old one where the bundled uniform structure is provably
(but typically non-definitionaly) equal to some given uniform structure.
See Note [forgetful inheritance].
-/
def metric_space.replace_uniformity {γ} [U : uniform_space γ] (m : metric_space γ)
  (H : @uniformity _ U = @uniformity _ pseudo_emetric_space.to_uniform_space) :
  metric_space γ :=
{ eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _,
  ..pseudo_metric_space.replace_uniformity m.to_pseudo_metric_space H, }

lemma metric_space.replace_uniformity_eq {γ} [U : uniform_space γ] (m : metric_space γ)
  (H : @uniformity _ U = @uniformity _ pseudo_emetric_space.to_uniform_space) :
  m.replace_uniformity H = m :=
by { ext, refl }

/-- Build a new metric space from an old one where the bundled topological structure is provably
(but typically non-definitionaly) equal to some given topological structure.
See Note [forgetful inheritance].
-/
@[reducible] def metric_space.replace_topology {γ} [U : topological_space γ] (m : metric_space γ)
  (H : U = m.to_pseudo_metric_space.to_uniform_space.to_topological_space) :
  metric_space γ :=
@metric_space.replace_uniformity γ (m.to_uniform_space.replace_topology H) m rfl

lemma metric_space.replace_topology_eq {γ} [U : topological_space γ] (m : metric_space γ)
  (H : U = m.to_pseudo_metric_space.to_uniform_space.to_topological_space) :
  m.replace_topology H = m :=
by { ext, refl }

  /-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. In this definition, the distance
is given separately, to be able to prescribe some expression which is not defeq to the push-forward
of the edistance to reals. -/
def emetric_space.to_metric_space_of_dist {α : Type u} [e : emetric_space α]
  (dist : α → α → ℝ)
  (edist_ne_top : ∀x y: α, edist x y ≠ ⊤)
  (h : ∀x y, dist x y = ennreal.to_real (edist x y)) :
  metric_space α :=
{ dist := dist,
  eq_of_dist_eq_zero := λx y hxy,
    by simpa [h, ennreal.to_real_eq_zero_iff, edist_ne_top x y] using hxy,
  ..pseudo_emetric_space.to_pseudo_metric_space_of_dist dist edist_ne_top h, }

/-- One gets a metric space from an emetric space if the edistance
is everywhere finite, by pushing the edistance to reals. We set it up so that the edist and the
uniformity are defeq in the metric space and the emetric space. -/
def emetric_space.to_metric_space {α : Type u} [e : emetric_space α] (h : ∀x y: α, edist x y ≠ ⊤) :
  metric_space α :=
emetric_space.to_metric_space_of_dist (λx y, ennreal.to_real (edist x y)) h (λx y, rfl)

/-- Build a new metric space from an old one where the bundled bornology structure is provably
(but typically non-definitionaly) equal to some given bornology structure.
See Note [forgetful inheritance].
-/
def metric_space.replace_bornology {α} [B : bornology α] (m : metric_space α)
  (H : ∀ s, @is_bounded _ B s ↔ @is_bounded _ pseudo_metric_space.to_bornology s) :
  metric_space α :=
{ to_bornology := B,
  .. pseudo_metric_space.replace_bornology _ H,
  .. m }

lemma metric_space.replace_bornology_eq {α} [m : metric_space α] [B : bornology α]
  (H : ∀ s, @is_bounded _ B s ↔ @is_bounded _ pseudo_metric_space.to_bornology s) :
  metric_space.replace_bornology _ H = m :=
by { ext, refl }

/-- Metric space structure pulled back by an injective function. Injectivity is necessary to
ensure that `dist x y = 0` only if `x = y`. -/
def metric_space.induced {γ β} (f : γ → β) (hf : function.injective f)
  (m : metric_space β) : metric_space γ :=
{ eq_of_dist_eq_zero := λ x y h, hf (dist_eq_zero.1 h),
  ..pseudo_metric_space.induced f m.to_pseudo_metric_space }

/-- Pull back a metric space structure by a uniform embedding. This is a version of
`metric_space.induced` useful in case if the domain already has a `uniform_space` structure. -/
@[reducible] def uniform_embedding.comap_metric_space
  {α β} [uniform_space α] [metric_space β] (f : α → β) (h : uniform_embedding f) :
  metric_space α :=
(metric_space.induced f h.inj ‹_›).replace_uniformity h.comap_uniformity.symm

/-- Pull back a metric space structure by an embedding. This is a version of
`metric_space.induced` useful in case if the domain already has a `topological_space` structure. -/
@[reducible] def embedding.comap_metric_space
  {α β} [topological_space α] [metric_space β] (f : α → β) (h : embedding f) :
  metric_space α :=
begin
  letI : uniform_space α := embedding.comap_uniform_space f h,
  exact uniform_embedding.comap_metric_space f (h.to_uniform_embedding f),
end

instance subtype.metric_space {α : Type*} {p : α → Prop} [metric_space α] :
  metric_space (subtype p) :=
metric_space.induced coe subtype.coe_injective ‹_›

@[to_additive] instance {α : Type*} [metric_space α] : metric_space (αᵐᵒᵖ) :=
metric_space.induced mul_opposite.unop mul_opposite.unop_injective ‹_›

instance : metric_space empty :=
{ dist := λ _ _, 0,
  dist_self := λ _, rfl,
  dist_comm := λ _ _, rfl,
  eq_of_dist_eq_zero := λ _ _ _, subsingleton.elim _ _,
  dist_triangle := λ _ _ _, show (0:ℝ) ≤ 0 + 0, by rw add_zero,
  to_uniform_space := empty.uniform_space,
  uniformity_dist := subsingleton.elim _ _ }

instance : metric_space punit.{u + 1} :=
{ dist := λ _ _, 0,
  dist_self := λ _, rfl,
  dist_comm := λ _ _, rfl,
  eq_of_dist_eq_zero := λ _ _ _, subsingleton.elim _ _,
  dist_triangle := λ _ _ _, show (0:ℝ) ≤ 0 + 0, by rw add_zero,
  to_uniform_space := punit.uniform_space,
  uniformity_dist :=
    begin
      simp only,
      haveI : ne_bot (⨅ ε > (0 : ℝ), 𝓟 {p : punit.{u + 1} × punit.{u + 1} | 0 < ε}),
      { exact @uniformity.ne_bot _ (uniform_space_of_dist (λ _ _, 0) (λ _, rfl) (λ _ _, rfl)
          (λ _ _ _, by rw zero_add)) _ },
      refine (eq_top_of_ne_bot _).trans (eq_top_of_ne_bot _).symm,
    end}

section real

/-- Instantiate the reals as a metric space. -/
instance real.metric_space : metric_space ℝ :=
{ eq_of_dist_eq_zero := λ x y h, by simpa [dist, sub_eq_zero] using h,
  ..real.pseudo_metric_space }

end real

section nnreal

instance : metric_space ℝ≥0 := subtype.metric_space

end nnreal

instance [metric_space β] : metric_space (ulift β) :=
metric_space.induced ulift.down ulift.down_injective ‹_›

section prod

instance prod.metric_space_max [metric_space β] : metric_space (γ × β) :=
{ eq_of_dist_eq_zero := λ x y h, begin
    cases max_le_iff.1 (le_of_eq h) with h₁ h₂,
    exact prod.ext_iff.2 ⟨dist_le_zero.1 h₁, dist_le_zero.1 h₂⟩
  end,
  ..prod.pseudo_metric_space_max, }

end prod

section pi
open finset
variables {π : β → Type*} [fintype β] [∀b, metric_space (π b)]

/-- A finite product of metric spaces is a metric space, with the sup distance. -/
instance metric_space_pi : metric_space (Πb, π b) :=
  /- we construct the instance from the emetric space instance to avoid checking again that the
  uniformity is the same as the product uniformity, but we register nevertheless a nice formula
  for the distance -/
{ eq_of_dist_eq_zero := assume f g eq0,
  begin
    have eq1 : edist f g = 0 := by simp only [edist_dist, eq0, ennreal.of_real_zero],
    have eq2 : sup univ (λ (b : β), edist (f b) (g b)) ≤ 0 := le_of_eq eq1,
    simp only [finset.sup_le_iff] at eq2,
    exact (funext $ assume b, edist_le_zero.1 $ eq2 b $ mem_univ b)
  end,
  ..pseudo_metric_space_pi }

end pi

namespace metric
section second_countable
open topological_space

/-- A metric space is second countable if one can reconstruct up to any `ε>0` any element of the
space from countably many data. -/
lemma second_countable_of_countable_discretization {α : Type u} [metric_space α]
  (H : ∀ε > (0 : ℝ), ∃ (β : Type*) (_ : encodable β) (F : α → β), ∀x y, F x = F y → dist x y ≤ ε) :
  second_countable_topology α :=
begin
  cases (univ : set α).eq_empty_or_nonempty with hs hs,
  { haveI : compact_space α := ⟨by rw hs; exact is_compact_empty⟩, by apply_instance },
  rcases hs with ⟨x0, hx0⟩,
  letI : inhabited α := ⟨x0⟩,
  refine second_countable_of_almost_dense_set (λε ε0, _),
  rcases H ε ε0 with ⟨β, fβ, F, hF⟩,
  resetI,
  let Finv := function.inv_fun F,
  refine ⟨range Finv, ⟨countable_range _, λx, _⟩⟩,
  let x' := Finv (F x),
  have : F x' = F x := function.inv_fun_eq ⟨x, rfl⟩,
  exact ⟨x', mem_range_self _, hF _ _ this.symm⟩
end

end second_countable
end metric

section eq_rel

/-- The canonical equivalence relation on a pseudometric space. -/
def pseudo_metric.dist_setoid (α : Type u) [pseudo_metric_space α] : setoid α :=
setoid.mk (λx y, dist x y = 0)
begin
  unfold equivalence,
  repeat { split },
  { exact pseudo_metric_space.dist_self },
  { assume x y h, rwa pseudo_metric_space.dist_comm },
  { assume x y z hxy hyz,
    refine le_antisymm _ dist_nonneg,
    calc dist x z ≤ dist x y + dist y z : pseudo_metric_space.dist_triangle _ _ _
         ... = 0 + 0 : by rw [hxy, hyz]
         ... = 0 : by simp }
end

local attribute [instance] pseudo_metric.dist_setoid

/-- The canonical quotient of a pseudometric space, identifying points at distance `0`. -/
@[reducible] definition pseudo_metric_quot (α : Type u) [pseudo_metric_space α] : Type* :=
quotient (pseudo_metric.dist_setoid α)

instance has_dist_metric_quot {α : Type u} [pseudo_metric_space α] :
  has_dist (pseudo_metric_quot α) :=
{ dist := quotient.lift₂ (λp q : α, dist p q)
begin
  assume x y x' y' hxx' hyy',
  have Hxx' : dist x x' = 0 := hxx',
  have Hyy' : dist y y' = 0 := hyy',
  have A : dist x y ≤ dist x' y' := calc
    dist x y ≤ dist x x' + dist x' y : pseudo_metric_space.dist_triangle _ _ _
    ... = dist x' y : by simp [Hxx']
    ... ≤ dist x' y' + dist y' y : pseudo_metric_space.dist_triangle _ _ _
    ... = dist x' y' : by simp [pseudo_metric_space.dist_comm, Hyy'],
  have B : dist x' y' ≤ dist x y := calc
    dist x' y' ≤ dist x' x + dist x y' : pseudo_metric_space.dist_triangle _ _ _
    ... = dist x y' : by simp [pseudo_metric_space.dist_comm, Hxx']
    ... ≤ dist x y + dist y y' : pseudo_metric_space.dist_triangle _ _ _
    ... = dist x y : by simp [Hyy'],
  exact le_antisymm A B
end }

lemma pseudo_metric_quot_dist_eq {α : Type u} [pseudo_metric_space α] (p q : α) :
  dist ⟦p⟧ ⟦q⟧ = dist p q := rfl

instance metric_space_quot {α : Type u} [pseudo_metric_space α] :
  metric_space (pseudo_metric_quot α) :=
{ dist_self := begin
    refine quotient.ind (λy, _),
    exact pseudo_metric_space.dist_self _
  end,
  eq_of_dist_eq_zero := λxc yc, by exact quotient.induction_on₂ xc yc (λx y H, quotient.sound H),
  dist_comm :=
    λxc yc, quotient.induction_on₂ xc yc (λx y, pseudo_metric_space.dist_comm _ _),
  dist_triangle :=
    λxc yc zc, quotient.induction_on₃ xc yc zc (λx y z, pseudo_metric_space.dist_triangle _ _ _) }

end eq_rel

/-!
### `additive`, `multiplicative`

The distance on those type synonyms is inherited without change.
-/

open additive multiplicative

section
variables [has_dist X]

instance : has_dist (additive X) := ‹has_dist X›
instance : has_dist (multiplicative X) := ‹has_dist X›

@[simp] lemma dist_of_mul (a b : X) : dist (of_mul a) (of_mul b) = dist a b := rfl
@[simp] lemma dist_of_add (a b : X) : dist (of_add a) (of_add b) = dist a b := rfl
@[simp] lemma dist_to_mul (a b : additive X) : dist (to_mul a) (to_mul b) = dist a b := rfl
@[simp] lemma dist_to_add (a b : multiplicative X) : dist (to_add a) (to_add b) = dist a b := rfl

end

section
variables [pseudo_metric_space X]

instance : pseudo_metric_space (additive X) := ‹pseudo_metric_space X›
instance : pseudo_metric_space (multiplicative X) := ‹pseudo_metric_space X›

@[simp] lemma nndist_of_mul (a b : X) : nndist (of_mul a) (of_mul b) = nndist a b := rfl
@[simp] lemma nndist_of_add (a b : X) : nndist (of_add a) (of_add b) = nndist a b := rfl
@[simp] lemma nndist_to_mul (a b : additive X) : nndist (to_mul a) (to_mul b) = nndist a b := rfl
@[simp] lemma nndist_to_add (a b : multiplicative X) : nndist (to_add a) (to_add b) = nndist a b :=
rfl

end

instance [metric_space X] : metric_space (additive X) := ‹metric_space X›
instance [metric_space X] : metric_space (multiplicative X) := ‹metric_space X›
instance [pseudo_metric_space X] [proper_space X] : proper_space (additive X) := ‹proper_space X›
instance [pseudo_metric_space X] [proper_space X] : proper_space (multiplicative X) :=
‹proper_space X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/

open order_dual

section
variables [has_dist X]

instance : has_dist Xᵒᵈ := ‹has_dist X›

@[simp] lemma dist_to_dual (a b : X) : dist (to_dual a) (to_dual b) = dist a b := rfl
@[simp] lemma dist_of_dual (a b : Xᵒᵈ) : dist (of_dual a) (of_dual b) = dist a b := rfl

end

section
variables [pseudo_metric_space X]

instance : pseudo_metric_space Xᵒᵈ := ‹pseudo_metric_space X›

@[simp] lemma nndist_to_dual (a b : X) : nndist (to_dual a) (to_dual b) = nndist a b := rfl
@[simp] lemma nndist_of_dual (a b : Xᵒᵈ) : nndist (of_dual a) (of_dual b) = nndist a b := rfl

end

instance [metric_space X] : metric_space Xᵒᵈ := ‹metric_space X›
instance [pseudo_metric_space X] [proper_space X] : proper_space Xᵒᵈ := ‹proper_space X›
