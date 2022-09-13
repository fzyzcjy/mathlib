/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin
-/
import data.mv_polynomial.equiv
import data.mv_polynomial.comm_ring
import logic.equiv.functor
import ring_theory.free_ring

/-!
# Free commutative rings

The theory of the free commutative ring generated by a type `α`.
It is isomorphic to the polynomial ring over ℤ with variables
in `α`

## Main definitions

* `free_comm_ring α`     : the free commutative ring on a type α
* `lift (f : α → R)` : the ring hom `free_comm_ring α →+* R` induced by functoriality from `f`.
* `map (f : α → β)`      : the ring hom `free_comm_ring α →*+ free_comm_ring β` induced by
                           functoriality from f.

## Main results

`free_comm_ring` has functorial properties (it is an adjoint to the forgetful functor).
In this file we have:

* `of : α → free_comm_ring α`
* `lift (f : α → R) : free_comm_ring α →+* R`
* `map (f : α → β) : free_comm_ring α →+* free_comm_ring β`

* `free_comm_ring_equiv_mv_polynomial_int : free_comm_ring α ≃+* mv_polynomial α ℤ` :
    `free_comm_ring α` is isomorphic to a polynomial ring.



## Implementation notes

`free_comm_ring α` is implemented not using `mv_polynomial` but
directly as the free abelian group on `multiset α`, the type
of monomials in this free commutative ring.

## Tags

free commutative ring, free ring
-/

noncomputable theory
open_locale classical polynomial

universes u v

variables (α : Type u)

/-- `free_comm_ring α` is the free commutative ring on the type `α`. -/
@[derive [comm_ring, inhabited]]
def free_comm_ring (α : Type u) : Type u :=
free_abelian_group $ multiplicative $ multiset α

namespace free_comm_ring

variables {α}

/-- The canonical map from `α` to the free commutative ring on `α`. -/
def of (x : α) : free_comm_ring α :=
free_abelian_group.of $ multiplicative.of_add ({x} : multiset α)

lemma of_injective : function.injective (of : α → free_comm_ring α) :=
free_abelian_group.of_injective.comp (λ x y,
  (multiset.coe_eq_coe.trans list.singleton_perm_singleton).mp)

@[elab_as_eliminator] protected lemma induction_on
  {C : free_comm_ring α → Prop} (z : free_comm_ring α)
  (hn1 : C (-1)) (hb : ∀ b, C (of b))
  (ha : ∀ x y, C x → C y → C (x + y))
  (hm : ∀ x y, C x → C y → C (x * y)) : C z :=
have hn : ∀ x, C x → C (-x), from λ x ih, neg_one_mul x ▸ hm _ _ hn1 ih,
have h1 : C 1, from neg_neg (1 : free_comm_ring α) ▸ hn _ hn1,
free_abelian_group.induction_on z
  (add_left_neg (1 : free_comm_ring α) ▸ ha _ _ hn1 h1)
  (λ m, multiset.induction_on m h1 $ λ a m ih, hm _ _ (hb a) ih)
  (λ m ih, hn _ ih)
  ha
section lift

variables {R : Type v} [comm_ring R] (f : α → R)

/-- A helper to implement `lift`. This is essentially `free_comm_monoid.lift`, but this does not
currently exist. -/
private def lift_to_multiset : (α → R) ≃ (multiplicative (multiset α) →* R) :=
{ to_fun := λ f,
  { to_fun := λ s, (s.to_add.map f).prod,
    map_mul' := λ x y, calc _ = multiset.prod ((multiset.map f x) + (multiset.map f y)) :
                                    by {congr' 1, exact multiset.map_add _ _ _}
                          ... = _ : multiset.prod_add _ _,
    map_one' := rfl},
  inv_fun := λ F x, F (multiplicative.of_add ({x} : multiset α)),
  left_inv := λ f, funext $ λ x, show (multiset.map f {x}).prod = _, by simp,
  right_inv := λ F, monoid_hom.ext $ λ x,
    let F' := F.to_additive'', x' := x.to_add in show (multiset.map (λ a, F' {a}) x').sum = F' x',
    begin
      rw [←multiset.map_map, ←add_monoid_hom.map_multiset_sum],
      exact F.congr_arg (multiset.sum_map_singleton x'),
    end }

/-- Lift a map `α → R` to a additive group homomorphism `free_comm_ring α → R`.
For a version producing a bundled homomorphism, see `lift_hom`. -/
def lift : (α → R) ≃ (free_comm_ring α →+* R) :=
equiv.trans lift_to_multiset free_abelian_group.lift_monoid

@[simp] lemma lift_of (x : α) : lift f (of x) = f x :=
(free_abelian_group.lift.of _ _).trans $ mul_one _

@[simp] lemma lift_comp_of (f : free_comm_ring α →+* R) : lift (f ∘ of) = f :=
ring_hom.ext $ λ x, free_comm_ring.induction_on x
  (by rw [ring_hom.map_neg, ring_hom.map_one, f.map_neg, f.map_one])
  (lift_of _)
  (λ x y ihx ihy, by rw [ring_hom.map_add, f.map_add, ihx, ihy])
  (λ x y ihx ihy, by rw [ring_hom.map_mul, f.map_mul, ihx, ihy])

@[ext]
lemma hom_ext ⦃f g : free_comm_ring α →+* R⦄ (h : ∀ x, f (of x) = g (of x)) :
  f = g :=
lift.symm.injective (funext h)

end lift

variables {β : Type v} (f : α → β)

/-- A map `f : α → β` produces a ring homomorphism `free_comm_ring α →+* free_comm_ring β`. -/
def map : free_comm_ring α →+* free_comm_ring β :=
lift $ of ∘ f

@[simp]
lemma map_of (x : α) : map f (of x) = of (f x) := lift_of _ _

/-- `is_supported x s` means that all monomials showing up in `x` have variables in `s`. -/
def is_supported (x : free_comm_ring α) (s : set α) : Prop :=
x ∈ subring.closure (of '' s)

section is_supported
variables {x y : free_comm_ring α} {s t : set α}

theorem is_supported_upwards (hs : is_supported x s) (hst : s ⊆ t) :
  is_supported x t :=
subring.closure_mono (set.monotone_image hst) hs

theorem is_supported_add (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x + y) s :=
subring.add_mem _ hxs hys

theorem is_supported_neg (hxs : is_supported x s) :
  is_supported (-x) s :=
subring.neg_mem _ hxs

theorem is_supported_sub (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x - y) s :=
subring.sub_mem _ hxs hys

theorem is_supported_mul (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x * y) s :=
subring.mul_mem _ hxs hys

theorem is_supported_zero : is_supported 0 s :=
subring.zero_mem _

theorem is_supported_one : is_supported 1 s :=
subring.one_mem _

theorem is_supported_int {i : ℤ} {s : set α} : is_supported ↑i s :=
int.induction_on i is_supported_zero
  (λ i hi, by rw [int.cast_add, int.cast_one]; exact is_supported_add hi is_supported_one)
  (λ i hi, by rw [int.cast_sub, int.cast_one]; exact is_supported_sub hi is_supported_one)

end is_supported

/-- The restriction map from `free_comm_ring α` to `free_comm_ring s` where `s : set α`, defined
  by sending all variables not in `s` to zero. -/
def restriction (s : set α) [decidable_pred (∈ s)] : free_comm_ring α →+* free_comm_ring s :=
lift (λ p, if H : p ∈ s then of (⟨p, H⟩ : s) else 0)

section restriction
variables (s : set α) [decidable_pred (∈ s)] (x y : free_comm_ring α)
@[simp] lemma restriction_of (p) :
  restriction s (of p) = if H : p ∈ s then of ⟨p, H⟩ else 0 := lift_of _ _

end restriction

theorem is_supported_of {p} {s : set α} : is_supported (of p) s ↔ p ∈ s :=
suffices is_supported (of p) s → p ∈ s, from ⟨this, λ hps, subring.subset_closure ⟨p, hps, rfl⟩⟩,
assume hps : is_supported (of p) s, begin
  haveI := classical.dec_pred s,
  have : ∀ x, is_supported x s →
    ∃ (n : ℤ), lift (λ a, if a ∈ s then (0 : ℤ[X]) else polynomial.X) x = n,
  { intros x hx, refine subring.in_closure.rec_on hx _ _ _ _,
    { use 1, rw [ring_hom.map_one], norm_cast },
    { use -1, rw [ring_hom.map_neg, ring_hom.map_one, int.cast_neg, int.cast_one] },
    { rintros _ ⟨z, hzs, rfl⟩ _ _, use 0, rw [ring_hom.map_mul, lift_of, if_pos hzs, zero_mul],
      norm_cast },
    { rintros x y ⟨q, hq⟩ ⟨r, hr⟩, refine ⟨q+r, _⟩, rw [ring_hom.map_add, hq, hr], norm_cast } },
  specialize this (of p) hps, rw [lift_of] at this, split_ifs at this, { exact h },
  exfalso, apply ne.symm int.zero_ne_one,
  rcases this with ⟨w, H⟩, rw ←polynomial.C_eq_int_cast at H,
  have : polynomial.X.coeff 1 = (polynomial.C ↑w).coeff 1, by rw H,
  rwa [polynomial.coeff_C, if_neg (one_ne_zero : 1 ≠ 0), polynomial.coeff_X, if_pos rfl] at this
end

theorem map_subtype_val_restriction {x} (s : set α) [decidable_pred (∈ s)]
  (hxs : is_supported x s) :
  map (subtype.val : s → α) (restriction s x) = x :=
begin
  refine subring.in_closure.rec_on hxs _ _ _ _,
  { rw ring_hom.map_one, refl },
  { rw [ring_hom.map_neg, ring_hom.map_neg, ring_hom.map_one], refl },
  { rintros _ ⟨p, hps, rfl⟩ n ih,
    rw [ring_hom.map_mul, restriction_of, dif_pos hps, ring_hom.map_mul, map_of, ih] },
  { intros x y ihx ihy, rw [ring_hom.map_add, ring_hom.map_add, ihx, ihy] }
end

theorem exists_finite_support (x : free_comm_ring α) :
  ∃ s : set α, set.finite s ∧ is_supported x s :=
free_comm_ring.induction_on x
  ⟨∅, set.finite_empty, is_supported_neg is_supported_one⟩
  (λ p, ⟨{p}, set.finite_singleton p, is_supported_of.2 $ set.mem_singleton _⟩)
  (λ x y ⟨s, hfs, hxs⟩ ⟨t, hft, hxt⟩, ⟨s ∪ t, hfs.union hft, is_supported_add
    (is_supported_upwards hxs $ set.subset_union_left s t)
    (is_supported_upwards hxt $ set.subset_union_right s t)⟩)
  (λ x y ⟨s, hfs, hxs⟩ ⟨t, hft, hxt⟩, ⟨s ∪ t, hfs.union hft, is_supported_mul
    (is_supported_upwards hxs $ set.subset_union_left s t)
    (is_supported_upwards hxt $ set.subset_union_right s t)⟩)

theorem exists_finset_support (x : free_comm_ring α) : ∃ s : finset α, is_supported x ↑s :=
let ⟨s, hfs, hxs⟩ := exists_finite_support x in ⟨hfs.to_finset, by rwa set.finite.coe_to_finset⟩

end free_comm_ring


namespace free_ring
open function
variable (α)

/-- The canonical ring homomorphism from the free ring generated by `α` to the free commutative ring
    generated by `α`. -/
def to_free_comm_ring {α} : free_ring α →+* free_comm_ring α :=
free_ring.lift free_comm_ring.of

instance : has_coe (free_ring α) (free_comm_ring α) := ⟨to_free_comm_ring⟩

/-- The natural map `free_ring α → free_comm_ring α`, as a `ring_hom`. -/
def coe_ring_hom : free_ring α →+* free_comm_ring α := to_free_comm_ring

@[simp, norm_cast] protected lemma coe_zero : ↑(0 : free_ring α) = (0 : free_comm_ring α) := rfl
@[simp, norm_cast] protected lemma coe_one : ↑(1 : free_ring α) = (1 : free_comm_ring α) := rfl

variable {α}

@[simp] protected lemma coe_of (a : α) : ↑(free_ring.of a) = free_comm_ring.of a :=
free_ring.lift_of _ _
@[simp, norm_cast] protected lemma coe_neg (x : free_ring α) : ↑(-x) = -(x : free_comm_ring α) :=
(free_ring.lift _).map_neg _
@[simp, norm_cast] protected lemma coe_add (x y : free_ring α) :
  ↑(x + y) = (x : free_comm_ring α) + y :=
(free_ring.lift _).map_add _ _
@[simp, norm_cast] protected lemma coe_sub (x y : free_ring α) :
  ↑(x - y) = (x : free_comm_ring α) - y :=
(free_ring.lift _).map_sub _ _
@[simp, norm_cast] protected lemma coe_mul (x y : free_ring α) :
  ↑(x * y) = (x : free_comm_ring α) * y :=
(free_ring.lift _).map_mul _ _

variable (α)

protected lemma coe_surjective : surjective (coe : free_ring α → free_comm_ring α) :=
λ x,
begin
  apply free_comm_ring.induction_on x,
  { use -1, refl },
  { intro x, use free_ring.of x, refl },
  { rintros _ _ ⟨x, rfl⟩ ⟨y, rfl⟩, use x + y, exact (free_ring.lift _).map_add _ _ },
  { rintros _ _ ⟨x, rfl⟩ ⟨y, rfl⟩, use x * y, exact (free_ring.lift _).map_mul _ _ }
end

lemma coe_eq :
  (coe : free_ring α → free_comm_ring α) =
  @functor.map free_abelian_group _ _ _ (λ (l : list α), (l : multiset α)) :=
funext $ λ x, free_abelian_group.lift.unique _ _ $ λ L,
by { simp_rw [free_abelian_group.lift.of, (∘)], exact free_monoid.rec_on L rfl
(λ hd tl ih, by { rw [(free_monoid.lift _).map_mul, free_monoid.lift_eval_of, ih], refl }) }

/-- If α has size at most 1 then the natural map from the free ring on `α` to the
    free commutative ring on `α` is an isomorphism of rings. -/
def subsingleton_equiv_free_comm_ring [subsingleton α] :
  free_ring α ≃+* free_comm_ring α :=
ring_equiv.of_bijective (coe_ring_hom _)
  begin
    have : (coe_ring_hom _ : free_ring α → free_comm_ring α) =
      (functor.map_equiv free_abelian_group (multiset.subsingleton_equiv α)) := coe_eq α,
    rw this,
    apply equiv.bijective,
  end

instance [subsingleton α] : comm_ring (free_ring α) :=
{ mul_comm := λ x y,
  by { rw [← (subsingleton_equiv_free_comm_ring α).symm_apply_apply (y * x),
        ((subsingleton_equiv_free_comm_ring α)).map_mul,
        mul_comm,
        ← ((subsingleton_equiv_free_comm_ring α)).map_mul,
        (subsingleton_equiv_free_comm_ring α).symm_apply_apply], },
  .. free_ring.ring α }

end free_ring

/-- The free commutative ring on `α` is isomorphic to the polynomial ring over ℤ with
    variables in `α` -/
def free_comm_ring_equiv_mv_polynomial_int :
  free_comm_ring α ≃+* mv_polynomial α ℤ :=
ring_equiv.of_hom_inv
  (free_comm_ring.lift $ (λ a, mv_polynomial.X a : α → mv_polynomial α ℤ))
  (mv_polynomial.eval₂_hom (int.cast_ring_hom (free_comm_ring α)) free_comm_ring.of)
  (by { ext, simp })
  (by ext; simp)

/-- The free commutative ring on the empty type is isomorphic to `ℤ`. -/
def free_comm_ring_pempty_equiv_int : free_comm_ring pempty.{u+1} ≃+* ℤ :=
ring_equiv.trans (free_comm_ring_equiv_mv_polynomial_int _)
  (mv_polynomial.is_empty_ring_equiv _ pempty)

/-- The free commutative ring on a type with one term is isomorphic to `ℤ[X]`. -/
def free_comm_ring_punit_equiv_polynomial_int : free_comm_ring punit.{u+1} ≃+* polynomial ℤ :=
(free_comm_ring_equiv_mv_polynomial_int _).trans (mv_polynomial.punit_alg_equiv ℤ).to_ring_equiv

open free_ring

/-- The free ring on the empty type is isomorphic to `ℤ`. -/
def free_ring_pempty_equiv_int : free_ring pempty.{u+1} ≃+* ℤ :=
ring_equiv.trans (subsingleton_equiv_free_comm_ring _) free_comm_ring_pempty_equiv_int

/-- The free ring on a type with one term is isomorphic to `ℤ[X]`. -/
def free_ring_punit_equiv_polynomial_int : free_ring punit.{u+1} ≃+* polynomial ℤ :=
ring_equiv.trans (subsingleton_equiv_free_comm_ring _) free_comm_ring_punit_equiv_polynomial_int
