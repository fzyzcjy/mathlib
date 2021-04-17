import data.finset.sort
import data.matrix.notation
import linear_algebra.basis
import linear_algebra.affine_space.basic
import linear_algebra.affine_space.combination
import linear_algebra.affine_space.independent
import analysis.convex.basic
import combinatorics.simplicial_complex.to_move

open_locale affine big_operators classical
open finset

universes u₁ u₂
variables {E : Type u₁} [add_comm_group E] [vector_space ℝ E]
variables {ι : Type u₂}

def convex_independent (p : ι → E) : Prop :=
∀ (s : finset ι) (x : ι), p x ∈ convex_hull (p '' s) → x ∈ s

lemma convex_independent_set_iff (A : set E) :
  convex_independent (λ p, p : A → E) ↔ ∀ s : finset E, ↑s ⊆ A → A ∩ convex_hull ↑s ⊆ ↑s :=
begin
  split,
  { rintro h s hs x ⟨hx₁, hx₂⟩,
    simpa using h (s.attach.image (λ x, ⟨x.1, hs x.2⟩)) ⟨_, hx₁⟩ _,
    convert hx₂,
    ext y,
    simpa [←and_assoc] using @hs y },
  { intros h s x hs,
    simpa using h (s.image coe) (by simp) ⟨x.2, by simpa using hs⟩ }
end

lemma nontrivial_sum_of_affine_independent' {p : ι → E} {X : finset ι}
  (hX : affine_independent ℝ p) (w : ι → ℝ)
  (hw₀ : ∑ i in X, w i = 0) (hw₁ : ∑ i in X, w i • p i = 0) :
∀ i ∈ X, w i = 0 :=
begin
  specialize hX _ _ hw₀ _,
  { rw finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ _ _ hw₀ (0 : E),
    rw finset.weighted_vsub_of_point_apply,
    simpa only [vsub_eq_sub, sub_zero, coe_sum X (λ i, w i • p i)] },
  intros i hi,
  apply hX _ hi
end

lemma unique_combination' {p : ι → E} (X : finset ι)
  (hX : affine_independent ℝ p)
  (w₁ w₂ : ι → ℝ) (hw₁ : ∑ i in X, w₁ i = 1) (hw₂ : ∑ i in X, w₂ i = 1)
  (same : ∑ i in X, w₁ i • p i = ∑ i in X, w₂ i • p i) :
  ∀ i ∈ X, w₁ i = w₂ i :=
begin
  let w := w₁ - w₂,
  suffices : ∀ i ∈ X, w i = 0,
  { intros i hi,
    apply eq_of_sub_eq_zero (this i hi) },
  apply nontrivial_sum_of_affine_independent' hX,
  { change ∑ i in X, (w₁ i - w₂ i) = _,
    rw [finset.sum_sub_distrib, hw₁, hw₂, sub_self] },
  { change ∑ i in X, (w₁ i - w₂ i) • p i = _,
    simp_rw [sub_smul, finset.sum_sub_distrib, same, sub_self] }
end

lemma convex_independent_of_affine_independent {p : ι → E} (hp : affine_independent ℝ p) :
  convex_independent p :=
begin
  intros s x hx,
  by_contra,
  rw [←finset.coe_image, finset.convex_hull_eq] at hx,
  rcases hx with ⟨w, hw₀, hw₁, x_eq⟩,
  have : set.inj_on p s := λ x hx y hy h, injective_of_affine_independent hp h,
  rw finset.center_mass_eq_of_sum_1 _ _ hw₁ at x_eq,
  rw finset.sum_image ‹set.inj_on p s› at hw₁,
  rw finset.sum_image ‹set.inj_on p s› at x_eq,
  dsimp at hw₁ x_eq,
  simp only [and_imp, finset.mem_image, forall_apply_eq_imp_iff₂, exists_imp_distrib] at hw₀,
  let w₀ : ι → ℝ := λ i, if i ∈ s then w (p i) else 0,
  let w₁ : ι → ℝ := λ i, if x = i then 1 else 0,
  have thing : _ = _ := unique_combination' (insert x s) hp w₀ w₁ _ _ _ _ (mem_insert_self _ _),
  { change ite _ _ _ = ite _ _ _ at thing,
    simpa [h] using thing },
  { rwa [sum_insert_of_eq_zero_if_not_mem, sum_extend_by_zero s],
    simp [h] },
  { simp [sum_ite_eq] },
  { simpa [sum_insert_of_eq_zero_if_not_mem, h, ite_smul, sum_extend_by_zero s] }
end
