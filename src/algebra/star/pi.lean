/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.star.basic
import algebra.ring.pi
import algebra.module.pi

/-!
# `star` on pi types

We put a `has_star` structure on pi types that operates elementwise, such that it describes the
complex conjugation of vectors.
-/

universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances

namespace pi

instance [Π i, has_star (f i)] : has_star (Π i, f i) :=
{ star := λ x i, star (x i) }

@[simp] lemma star_apply [Π i, has_star (f i)] (x : Π i, f i) (i : I) : star x i = star (x i) := rfl

lemma star_def [Π i, has_star (f i)] (x : Π i, f i) : star x = λ i, star (x i) := rfl

instance [Π i, has_involutive_star (f i)] : has_involutive_star (Π i, f i) :=
{ star_involutive := λ _, funext $ λ _, star_star _ }

instance [Π i, semigroup (f i)] [Π i, star_semigroup (f i)] : star_semigroup (Π i, f i) :=
{ star_mul := λ _ _, funext $ λ _, star_mul _ _ }

instance [Π i, add_monoid (f i)] [Π i, star_add_monoid (f i)] : star_add_monoid (Π i, f i) :=
{ star_add := λ _ _, funext $ λ _, star_add _ _ }

instance [Π i, non_unital_semiring (f i)] [Π i, star_ring (f i)] : star_ring (Π i, f i) :=
{ ..pi.star_add_monoid, ..(pi.star_semigroup : star_semigroup (Π i, f i)) }

instance {R : Type w}
  [Π i, has_smul R (f i)] [has_star R] [Π i, has_star (f i)] [Π i, star_module R (f i)] :
  star_module R (Π i, f i) :=
{ star_smul := λ r x, funext $ λ i, star_smul r (x i) }

lemma single_star [Π i, add_monoid (f i)] [Π i, star_add_monoid (f i)] [decidable_eq I]
  (i : I) (a : f i) :
  pi.single i (star a) = star (pi.single i a) :=
single_op (λ i, @star (f i) _) (λ i, star_zero _) i a

end pi

namespace function

lemma update_star [Π i, has_star (f i)] [decidable_eq I]
  (h : Π (i : I), f i) (i : I) (a : f i) :
  function.update (star h) i (star a) = star (function.update h i a) :=
funext $ λ j, (apply_update (λ i, star) h i a j).symm

lemma star_sum_elim {I J α : Type*} (x : I → α) (y : J → α) [has_star α] :
  star (sum.elim x y) = sum.elim (star x) (star y) :=
by { ext x, cases x; simp }

end function
