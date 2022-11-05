/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes
-/
import data.finite.card
import group_theory.commutator
import group_theory.finiteness

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `algebra/category/Group/adjunctions`.

## Main definitions

* `commutator`: defines the commutator of a group `G` as a subgroup of `G`.
* `abelianization`: defines the abelianization of a group `G` as the quotient of a group by its
  commutator subgroup.
* `abelianization.map`: lifts a group homomorphism to a homomorphism between the abelianizations
* `mul_equiv.abelianization_congr`: Equivalent groups have equivalent abelianizations

-/

universes u v w

-- Let G be a group.
variables (G : Type u) [group G]

/-- The commutator subgroup of a group G is the normal subgroup
  generated by the commutators [p,q]=`p*q*p⁻¹*q⁻¹`. -/
@[derive subgroup.normal]
def commutator : subgroup G :=
⁅(⊤ : subgroup G), ⊤⁆

lemma commutator_def : commutator G = ⁅(⊤ : subgroup G), ⊤⁆ := rfl

lemma commutator_eq_closure : commutator G = subgroup.closure (commutator_set G) :=
by simp [commutator, subgroup.commutator_def, commutator_set]

lemma commutator_eq_normal_closure :
  commutator G = subgroup.normal_closure (commutator_set G) :=
by simp [commutator, subgroup.commutator_def', commutator_set]

instance commutator_characteristic : (commutator G).characteristic :=
subgroup.commutator_characteristic ⊤ ⊤

instance [finite (commutator_set G)] : group.fg (commutator G) :=
begin
  rw commutator_eq_closure,
  apply group.closure_finite_fg,
end

lemma rank_commutator_le_card [finite (commutator_set G)] :
  group.rank (commutator G) ≤ nat.card (commutator_set G) :=
begin
  rw subgroup.rank_congr (commutator_eq_closure G),
  apply subgroup.rank_closure_finite_le_nat_card,
end

lemma commutator_centralizer_commutator_le_center :
  ⁅(commutator G).centralizer, (commutator G).centralizer⁆ ≤ subgroup.center G :=
begin
  rw [←subgroup.centralizer_top, ←subgroup.commutator_eq_bot_iff_le_centralizer],
  suffices : ⁅⁅⊤, (commutator G).centralizer⁆, (commutator G).centralizer⁆ = ⊥,
  { refine subgroup.commutator_commutator_eq_bot_of_rotate _ this,
    rwa subgroup.commutator_comm (commutator G).centralizer },
  rw [subgroup.commutator_comm, subgroup.commutator_eq_bot_iff_le_centralizer],
  exact set.centralizer_subset (subgroup.commutator_mono le_top le_top),
end

/-- The abelianization of G is the quotient of G by its commutator subgroup. -/
def abelianization : Type u :=
G ⧸ (commutator G)

namespace abelianization

local attribute [instance] quotient_group.left_rel

instance : comm_group (abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂' x y $ λ a b, quotient.sound' $
    quotient_group.left_rel_apply.mpr $
    subgroup.subset_closure ⟨b⁻¹, subgroup.mem_top b⁻¹, a⁻¹, subgroup.mem_top a⁻¹, by group⟩,
.. quotient_group.quotient.group _ }

instance : inhabited (abelianization G) := ⟨1⟩

instance [fintype G] [decidable_pred (∈ commutator G)] :
  fintype (abelianization G) :=
quotient_group.fintype (commutator G)

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
def of : G →* abelianization G :=
{ to_fun := quotient_group.mk,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

@[simp] lemma mk_eq_of (a : G) : quot.mk _ a = of a := rfl

section lift
-- So far we have built Gᵃᵇ and proved it's an abelian group.
-- Furthremore we defined the canonical projection `of : G → Gᵃᵇ`

-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
variables {A : Type v} [comm_group A] (f : G →* A)

lemma commutator_subset_ker : commutator G ≤ f.ker :=
begin
  rw [commutator_eq_closure, subgroup.closure_le],
  rintros x ⟨p, q, rfl⟩,
  simp [monoid_hom.mem_ker, mul_right_comm (f p) (f q), commutator_element_def],
end

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map from
  the abelianization of a `G` to `A` that factors through `f`. -/
def lift : (G →* A) ≃ (abelianization G →* A) :=
{ to_fun := λ f, quotient_group.lift _ f (λ x h, f.mem_ker.2 $ commutator_subset_ker _ h),
  inv_fun := λ F, F.comp of,
  left_inv := λ f, monoid_hom.ext $ λ x, rfl,
  right_inv := λ F, monoid_hom.ext $ λ x, quotient_group.induction_on x $ λ z, rfl }

@[simp] lemma lift.of (x : G) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (φ : abelianization G →* A)
  -- hφ : φ agrees with f on the image of G in Gᵃᵇ
  (hφ : ∀ (x : G), φ (of x) = f x)
  {x : abelianization G} :
  φ x = lift f x :=
quotient_group.induction_on x hφ

@[simp] lemma lift_of : lift of = monoid_hom.id (abelianization G) :=
lift.apply_symm_apply $ monoid_hom.id _

end lift

variables {A : Type v} [monoid A]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext (φ ψ : abelianization G →* A)
  (h : φ.comp of = ψ.comp of) : φ = ψ :=
monoid_hom.ext $ λ x, quotient_group.induction_on x $ monoid_hom.congr_fun h

section map

variables {H : Type v} [group H] (f : G →* H)

/-- The map operation of the `abelianization` functor -/
def map : abelianization G →* abelianization H := lift (of.comp f)

@[simp]
lemma map_of (x : G) : map f (of x) = of (f x) := rfl

@[simp]
lemma map_id : map (monoid_hom.id G) = monoid_hom.id (abelianization G) := hom_ext _ _ rfl

@[simp]
lemma map_comp {I : Type w} [group I] (g : H →* I) :
  (map g).comp (map f) = map (g.comp f) := hom_ext _ _ rfl

@[simp]
lemma map_map_apply {I : Type w} [group I] {g : H →* I} {x : abelianization G}:
  map g (map f x) = map (g.comp f) x := monoid_hom.congr_fun (map_comp _ _) x

end map

end abelianization

section abelianization_congr

variables {G} {H : Type v} [group H] (e : G ≃* H)

/-- Equivalent groups have equivalent abelianizations -/
def mul_equiv.abelianization_congr : abelianization G ≃* abelianization H :=
{ to_fun := abelianization.map e.to_monoid_hom,
  inv_fun := abelianization.map e.symm.to_monoid_hom,
  left_inv := by { rintros ⟨a⟩, simp },
  right_inv := by { rintros ⟨a⟩, simp },
  map_mul' := monoid_hom.map_mul _ }

@[simp]
lemma abelianization_congr_of (x : G) :
  (e.abelianization_congr) (abelianization.of x) = abelianization.of (e x) := rfl

@[simp]
lemma abelianization_congr_refl :
  (mul_equiv.refl G).abelianization_congr = mul_equiv.refl (abelianization G) :=
mul_equiv.to_monoid_hom_injective abelianization.lift_of

@[simp]
lemma abelianization_congr_symm  :
  e.abelianization_congr.symm = e.symm.abelianization_congr := rfl

@[simp]
lemma abelianization_congr_trans {I : Type v} [group I] (e₂ : H ≃* I) :
  e.abelianization_congr.trans e₂.abelianization_congr = (e.trans e₂).abelianization_congr :=
mul_equiv.to_monoid_hom_injective (abelianization.hom_ext _ _ rfl)

end abelianization_congr

/-- An Abelian group is equivalent to its own abelianization. -/
@[simps] def abelianization.equiv_of_comm {H : Type*} [comm_group H] :
  H ≃* abelianization H :=
{ to_fun    := abelianization.of,
  inv_fun   := abelianization.lift (monoid_hom.id H),
  left_inv  := λ a, rfl,
  right_inv := by { rintros ⟨a⟩, refl, },
  .. abelianization.of }

section commutator_representatives

open subgroup

/-- Representatives `(g₁, g₂) : G × G` of commutator_set `⁅g₁, g₂⁆ ∈ G`. -/
def commutator_representatives : set (G × G) :=
set.range (λ g : commutator_set G, (g.2.some, g.2.some_spec.some))

instance [finite (commutator_set G)] : finite (commutator_representatives G) :=
set.finite_coe_iff.mpr (set.finite_range _)

/-- Subgroup generated by representatives `g₁ g₂ : G` of commutators `⁅g₁, g₂⁆ ∈ G`. -/
def closure_commutator_representatives : subgroup G :=
closure (prod.fst '' commutator_representatives G ∪ prod.snd '' commutator_representatives G)

instance closure_commutator_representatives_fg [finite (commutator_set G)] :
  group.fg (closure_commutator_representatives G) :=
group.closure_finite_fg _

lemma rank_closure_commutator_representations_le [finite (commutator_set G)] :
  group.rank (closure_commutator_representatives G) ≤ 2 * nat.card (commutator_set G) :=
begin
  rw two_mul,
  exact (subgroup.rank_closure_finite_le_nat_card _).trans ((set.card_union_le _ _).trans
    (add_le_add ((finite.card_image_le _).trans (finite.card_range_le _))
    ((finite.card_image_le _).trans (finite.card_range_le _ )))),
end

lemma image_commutator_set_closure_commutator_representatives :
  (closure_commutator_representatives G).subtype ''
    (commutator_set (closure_commutator_representatives G)) = commutator_set G :=
begin
  apply set.subset.antisymm,
  { rintros - ⟨-, ⟨g₁, g₂, rfl⟩, rfl⟩,
    exact ⟨g₁, g₂, rfl⟩ },
  { exact λ g hg, ⟨_,
      ⟨⟨_, subset_closure (or.inl ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩)⟩,
       ⟨_, subset_closure (or.inr ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩)⟩,
       rfl⟩,
      hg.some_spec.some_spec⟩ },
end

lemma card_commutator_set_closure_commutator_representatives :
  nat.card (commutator_set (closure_commutator_representatives G)) = nat.card (commutator_set G) :=
begin
  rw ← image_commutator_set_closure_commutator_representatives G,
  exact nat.card_congr (equiv.set.image _ _ (subtype_injective _)),
end

lemma card_commutator_closure_commutator_representatives :
  nat.card (commutator (closure_commutator_representatives G)) = nat.card (commutator G) :=
begin
  rw [commutator_eq_closure G, ←image_commutator_set_closure_commutator_representatives,
      ←monoid_hom.map_closure, ←commutator_eq_closure],
  exact nat.card_congr (equiv.set.image _ _ (subtype_injective _)),
end

instance [finite (commutator_set G)] :
  finite (commutator_set (closure_commutator_representatives G)) :=
begin
  apply nat.finite_of_card_ne_zero,
  rw card_commutator_set_closure_commutator_representatives,
  exact finite.card_pos.ne',
end

end commutator_representatives
