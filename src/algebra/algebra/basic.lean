/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.module.basic
import algebra.module.ulift
import algebra.ne_zero
import algebra.ring.aut
import algebra.ring.ulift
import linear_algebra.span
import tactic.abel

/-!
# Algebras over commutative semirings

In this file we define associative unital `algebra`s over commutative (semi)rings, algebra
homomorphisms `alg_hom`, and algebra equivalences `alg_equiv`.

`subalgebra`s are defined in `algebra.algebra.subalgebra`.

For the category of `R`-algebras, denoted `Algebra R`, see the file
`algebra/category/Algebra/basic.lean`.

See the implementation notes for remarks about non-associative and non-unital algebras.

## Main definitions:

* `algebra R A`: the algebra typeclass.
* `alg_hom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `alg_equiv R A B`: the type of `R`-algebra isomorphisms between `A` to `B`.
* `algebra_map R A : R →+* A`: the canonical map from `R` to `A`, as a `ring_hom`. This is the
  preferred spelling of this map.
* `algebra.linear_map R A : R →ₗ[R] A`: the canonical map from `R` to `A`, as a `linear_map`.
* `algebra.of_id R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as n `alg_hom`.
* Instances of `algebra` in this file:
  * `algebra.id`
  * `pi.algebra`
  * `prod.algebra`
  * `algebra_nat`
  * `algebra_int`
  * `algebra_rat`
  * `mul_opposite.algebra`
  * `module.End.algebra`

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.

## Implementation notes

Given a commutative (semi)ring `R`, there are two ways to define an `R`-algebra structure on a
(possibly noncommutative) (semi)ring `A`:
* By endowing `A` with a morphism of rings `R →+* A` denoted `algebra_map R A` which lands in the
  center of `A`.
* By requiring `A` be an `R`-module such that the action associates and commutes with multiplication
  as `r • (a₁ * a₂) = (r • a₁) * a₂ = a₁ * (r • a₂)`.

We define `algebra R A` in a way that subsumes both definitions, by extending `has_smul R A` and
requiring that this scalar action `r • x` must agree with left multiplication by the image of the
structure morphism `algebra_map R A r * x`.

As a result, there are two ways to talk about an `R`-algebra `A` when `A` is a semiring:
1. ```lean
   variables [comm_semiring R] [semiring A]
   variables [algebra R A]
   ```
2. ```lean
   variables [comm_semiring R] [semiring A]
   variables [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]
   ```

The first approach implies the second via typeclass search; so any lemma stated with the second set
of arguments will automatically apply to the first set. Typeclass search does not know that the
second approach implies the first, but this can be shown with:
```lean
example {R A : Type*} [comm_semiring R] [semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A] : algebra R A :=
algebra.of_module smul_mul_assoc mul_smul_comm
```

The advantage of the first approach is that `algebra_map R A` is available, and `alg_hom R A B` and
`subalgebra R A` can be used. For concrete `R` and `A`, `algebra_map R A` is often definitionally
convenient.

The advantage of the second approach is that `comm_semiring R`, `semiring A`, and `module R A` can
all be relaxed independently; for instance, this allows us to:
* Replace `semiring A` with `non_unital_non_assoc_semiring A` in order to describe non-unital and/or
  non-associative algebras.
* Replace `comm_semiring R` and `module R A` with `comm_group R'` and `distrib_mul_action R' A`,
  which when `R' = Rˣ` lets us talk about the "algebra-like" action of `Rˣ` on an
  `R`-algebra `A`.

While `alg_hom R A B` cannot be used in the second approach, `non_unital_alg_hom R A B` still can.

You should always use the first approach when working with associative unital algebras, and mimic
the second approach only when you need to weaken a condition on either `R` or `A`.

-/

universes u v w u₁ v₁

open_locale big_operators

section prio
-- We set this priority to 0 later in this file
set_option extends_priority 200 /- control priority of
`instance [algebra R A] : has_smul R A` -/

/--
An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.

See the implementation notes in this file for discussion of the details of this definition.
-/
@[nolint has_nonempty_instance]
class algebra (R : Type u) (A : Type v) [comm_semiring R] [semiring A]
  extends has_smul R A, R →+* A :=
(commutes' : ∀ r x, to_fun r * x = x * to_fun r)
(smul_def' : ∀ r x, r • x = to_fun r * x)
end prio

/-- Embedding `R →+* A` given by `algebra` structure. -/
def algebra_map (R : Type u) (A : Type v) [comm_semiring R] [semiring A] [algebra R A] : R →+* A :=
algebra.to_ring_hom

namespace algebra_map

def has_lift_t (R A : Type*) [comm_semiring R] [semiring A] [algebra R A] :
  has_lift_t R A := ⟨λ r, algebra_map R A r⟩

attribute [instance, priority 900] algebra_map.has_lift_t

section comm_semiring_semiring

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

@[simp, norm_cast] lemma coe_zero : (↑(0 : R) : A) = 0 := map_zero (algebra_map R A)
@[simp, norm_cast] lemma coe_one : (↑(1 : R) : A) = 1 := map_one (algebra_map R A)
@[norm_cast] lemma coe_add (a b : R) : (↑(a + b : R) : A) = ↑a + ↑b :=
map_add (algebra_map R A) a b
@[norm_cast] lemma coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b :=
map_mul (algebra_map R A) a b
@[norm_cast] lemma coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = ↑a ^ n :=
map_pow (algebra_map R A) _ _

end comm_semiring_semiring

section comm_ring_ring

variables {R A : Type*} [comm_ring R] [ring A] [algebra R A]

@[norm_cast] lemma coe_neg (x : R) : (↑(-x : R) : A) = -↑x :=
map_neg (algebra_map R A) x

end comm_ring_ring

section comm_semiring_comm_semiring

variables {R A : Type*} [comm_semiring R] [comm_semiring A] [algebra R A]

open_locale big_operators

-- direct to_additive fails because of some mix-up with polynomials
@[norm_cast] lemma coe_prod {ι : Type*} {s : finset ι} (a : ι → R) :
  (↑( ∏ (i : ι) in s, a i : R) : A) = ∏ (i : ι) in s, (↑(a i) : A) :=
map_prod (algebra_map R A) a s

-- to_additive fails for some reason
@[norm_cast] lemma coe_sum {ι : Type*} {s : finset ι} (a : ι → R) :
  ↑(( ∑ (i : ι) in s, a i)) = ∑ (i : ι) in s, (↑(a i) : A) :=
map_sum (algebra_map R A) a s

attribute [to_additive] coe_prod

end comm_semiring_comm_semiring

section field_nontrivial

variables {R A : Type*} [field R] [comm_semiring A] [nontrivial A] [algebra R A]

@[norm_cast, simp] lemma coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
⟨λ h, (algebra_map R A).injective h, by rintro rfl; refl⟩

@[norm_cast, simp] lemma lift_map_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 :=
begin
  rw (show (0 : A) = ↑(0 : R), from (map_zero (algebra_map R A)).symm),
  norm_cast,
end

end field_nontrivial

end algebra_map

/-- Creating an algebra from a morphism to the center of a semiring. -/
def ring_hom.to_algebra' {R S} [comm_semiring R] [semiring S] (i : R →+* S)
  (h : ∀ c x, i c * x = x * i c) :
  algebra R S :=
{ smul := λ c x, i c * x,
  commutes' := h,
  smul_def' := λ c x, rfl,
  to_ring_hom := i}

/-- Creating an algebra from a morphism to a commutative semiring. -/
def ring_hom.to_algebra {R S} [comm_semiring R] [comm_semiring S] (i : R →+* S) :
  algebra R S :=
i.to_algebra' $ λ _, mul_comm _

lemma ring_hom.algebra_map_to_algebra {R S} [comm_semiring R] [comm_semiring S]
  (i : R →+* S) :
  @algebra_map R S _ _ i.to_algebra = i :=
rfl

namespace algebra

variables {R : Type u} {S : Type v} {A : Type w} {B : Type*}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `algebra`
over `R`.

See note [reducible non-instances]. -/
@[reducible]
def of_module' [comm_semiring R] [semiring A] [module R A]
  (h₁ : ∀ (r : R) (x : A), (r • 1) * x = r • x)
  (h₂ : ∀ (r : R) (x : A), x * (r • 1) = r • x) : algebra R A :=
{ to_fun := λ r, r • 1,
  map_one' := one_smul _ _,
  map_mul' := λ r₁ r₂, by rw [h₁, mul_smul],
  map_zero' := zero_smul _ _,
  map_add' := λ r₁ r₂, add_smul r₁ r₂ 1,
  commutes' := λ r x, by simp only [h₁, h₂],
  smul_def' := λ r x, by simp only [h₁] }

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `algebra` over `R`.

See note [reducible non-instances]. -/
@[reducible]
def of_module [comm_semiring R] [semiring A] [module R A]
  (h₁ : ∀ (r : R) (x y : A), (r • x) * y = r • (x * y))
  (h₂ : ∀ (r : R) (x y : A), x * (r • y) = r • (x * y)) : algebra R A :=
of_module' (λ r x, by rw [h₁, one_mul]) (λ r x, by rw [h₂, mul_one])

section semiring

variables [comm_semiring R] [comm_semiring S]
variables [semiring A] [algebra R A] [semiring B] [algebra R B]

/-- We keep this lemma private because it picks up the `algebra.to_has_smul` instance
which we set to priority 0 shortly. See `smul_def` below for the public version. -/
private lemma smul_def'' (r : R) (x : A) : r • x = algebra_map R A r * x :=
algebra.smul_def' r x

/--
To prove two algebra structures on a fixed `[comm_semiring R] [semiring A]` agree,
it suffices to check the `algebra_map`s agree.
-/
-- We'll later use this to show `algebra ℤ M` is a subsingleton.
@[ext]
lemma algebra_ext {R : Type*} [comm_semiring R] {A : Type*} [semiring A] (P Q : algebra R A)
  (w : ∀ (r : R), by { haveI := P, exact algebra_map R A r } =
    by { haveI := Q, exact algebra_map R A r }) :
  P = Q :=
begin
  unfreezingI { rcases P with @⟨⟨P⟩⟩, rcases Q with @⟨⟨Q⟩⟩ },
  congr,
  { funext r a,
    replace w := congr_arg (λ s, s * a) (w r),
    simp only [←smul_def''] at w,
    apply w, },
  { ext r,
    exact w r, },
  { apply proof_irrel_heq, },
  { apply proof_irrel_heq, },
end

@[priority 200] -- see Note [lower instance priority]
instance to_module : module R A :=
{ one_smul := by simp [smul_def''],
  mul_smul := by simp [smul_def'', mul_assoc],
  smul_add := by simp [smul_def'', mul_add],
  smul_zero := by simp [smul_def''],
  add_smul := by simp [smul_def'', add_mul],
  zero_smul := by simp [smul_def''] }

-- From now on, we don't want to use the following instance anymore.
-- Unfortunately, leaving it in place causes deterministic timeouts later in mathlib.
attribute [instance, priority 0] algebra.to_has_smul

lemma smul_def (r : R) (x : A) : r • x = algebra_map R A r * x :=
algebra.smul_def' r x

lemma algebra_map_eq_smul_one (r : R) : algebra_map R A r = r • 1 :=
calc algebra_map R A r = algebra_map R A r * 1 : (mul_one _).symm
                   ... = r • 1                 : (algebra.smul_def r 1).symm

lemma algebra_map_eq_smul_one' : ⇑(algebra_map R A) = λ r, r • (1 : A) :=
funext algebra_map_eq_smul_one

/-- `mul_comm` for `algebra`s when one element is from the base ring. -/
theorem commutes (r : R) (x : A) : algebra_map R A r * x = x * algebra_map R A r :=
algebra.commutes' r x

/-- `mul_left_comm` for `algebra`s when one element is from the base ring. -/
theorem left_comm (x : A) (r : R) (y : A) :
  x * (algebra_map R A r * y) = algebra_map R A r * (x * y) :=
by rw [← mul_assoc, ← commutes, mul_assoc]

/-- `mul_right_comm` for `algebra`s when one element is from the base ring. -/
theorem right_comm (x : A) (r : R) (y : A) :
  (x * algebra_map R A r) * y = (x * y) * algebra_map R A r :=
by rw [mul_assoc, commutes, ←mul_assoc]

instance _root_.is_scalar_tower.right : is_scalar_tower R A A :=
⟨λ x y z, by rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp] protected lemma mul_smul_comm (s : R) (x y : A) :
  x * (s • y) = s • (x * y) :=
-- TODO: set up `is_scalar_tower.smul_comm_class` earlier so that we can actually prove this using
-- `mul_smul_comm s x y`.
by rw [smul_def, smul_def, left_comm]

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp] protected lemma smul_mul_assoc (r : R) (x y : A) :
  (r • x) * y = r • (x * y) :=
smul_mul_assoc r x y

@[simp]
lemma _root_.smul_algebra_map {α : Type*} [monoid α] [mul_distrib_mul_action α A]
  [smul_comm_class α R A] (a : α) (r : R) : a • algebra_map R A r = algebra_map R A r :=
by rw [algebra_map_eq_smul_one, smul_comm a r (1 : A), smul_one]

section
variables {r : R} {a : A}

@[simp] lemma bit0_smul_one : bit0 r • (1 : A) = bit0 (r • (1 : A)) :=
by simp [bit0, add_smul]
lemma bit0_smul_one' : bit0 r • (1 : A) = r • 2 :=
by simp [bit0, add_smul, smul_add]
@[simp] lemma bit0_smul_bit0 : bit0 r • bit0 a = r • (bit0 (bit0 a)) :=
by simp [bit0, add_smul, smul_add]
@[simp] lemma bit0_smul_bit1 : bit0 r • bit1 a = r • (bit0 (bit1 a)) :=
by simp [bit0, add_smul, smul_add]
@[simp] lemma bit1_smul_one : bit1 r • (1 : A) = bit1 (r • (1 : A)) :=
by simp [bit1, add_smul]
lemma bit1_smul_one' : bit1 r • (1 : A) = r • 2 + 1 :=
by simp [bit1, bit0, add_smul, smul_add]
@[simp] lemma bit1_smul_bit0 : bit1 r • bit0 a = r • (bit0 (bit0 a)) + bit0 a :=
by simp [bit1, add_smul, smul_add]
@[simp] lemma bit1_smul_bit1 : bit1 r • bit1 a = r • (bit0 (bit1 a)) + bit1 a :=
by { simp only [bit0, bit1, add_smul, smul_add, one_smul], abel }

end

variables (R A)

/--
The canonical ring homomorphism `algebra_map R A : R →* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
protected def linear_map : R →ₗ[R] A :=
{ map_smul' := λ x y, by simp [algebra.smul_def],
  ..algebra_map R A }

@[simp]
lemma linear_map_apply (r : R) : algebra.linear_map R A r = algebra_map R A r := rfl

lemma coe_linear_map : ⇑(algebra.linear_map R A) = algebra_map R A := rfl

instance id : algebra R R := (ring_hom.id R).to_algebra

variables {R A}

namespace id

@[simp] lemma map_eq_id : algebra_map R R = ring_hom.id _ := rfl

lemma map_eq_self (x : R) : algebra_map R R x = x := rfl

@[simp] lemma smul_eq_mul (x y : R) : x • y = x * y := rfl

end id

section punit

instance _root_.punit.algebra : algebra R punit :=
{ to_fun := λ x, punit.star,
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  commutes' := λ _ _, rfl,
  smul_def' := λ _ _, rfl }

@[simp] lemma algebra_map_punit (r : R) : algebra_map R punit r = punit.star := rfl

end punit

section ulift

instance _root_.ulift.algebra : algebra R (ulift A) :=
{ to_fun := λ r, ulift.up (algebra_map R A r),
  commutes' := λ r x, ulift.down_injective $ algebra.commutes r x.down,
  smul_def' := λ r x, ulift.down_injective $ algebra.smul_def' r x.down,
  .. ulift.module',
  .. (ulift.ring_equiv : ulift A ≃+* A).symm.to_ring_hom.comp (algebra_map R A) }

lemma _root_.ulift.algebra_map_eq (r : R) :
  algebra_map R (ulift A) r = ulift.up (algebra_map R A r) := rfl

@[simp] lemma _root_.ulift.down_algebra_map (r : R) :
  (algebra_map R (ulift A) r).down = algebra_map R A r := rfl

end ulift

section prod
variables (R A B)

instance _root_.prod.algebra : algebra R (A × B) :=
{ commutes' := by { rintro r ⟨a, b⟩, dsimp, rw [commutes r a, commutes r b] },
  smul_def' := by { rintro r ⟨a, b⟩, dsimp, rw [smul_def r a, smul_def r b] },
  .. prod.module,
  .. ring_hom.prod (algebra_map R A) (algebra_map R B) }

variables {R A B}

@[simp] lemma algebra_map_prod_apply (r : R) :
  algebra_map R (A × B) r = (algebra_map R A r, algebra_map R B r) := rfl

end prod

/-- Algebra over a subsemiring. This builds upon `subsemiring.module`. -/
instance of_subsemiring (S : subsemiring R) : algebra S A :=
{ smul := (•),
  commutes' := λ r x, algebra.commutes r x,
  smul_def' := λ r x, algebra.smul_def r x,
  .. (algebra_map R A).comp S.subtype }

lemma algebra_map_of_subsemiring (S : subsemiring R) :
  (algebra_map S R : S →+* R) = subsemiring.subtype S := rfl

lemma coe_algebra_map_of_subsemiring (S : subsemiring R) :
  (algebra_map S R : S → R) = subtype.val := rfl

lemma algebra_map_of_subsemiring_apply (S : subsemiring R) (x : S) :
  algebra_map S R x = x := rfl

/-- Algebra over a subring. This builds upon `subring.module`. -/
instance of_subring {R A : Type*} [comm_ring R] [ring A] [algebra R A]
  (S : subring R) : algebra S A :=
{ smul := (•),
  .. algebra.of_subsemiring S.to_subsemiring,
  .. (algebra_map R A).comp S.subtype }

lemma algebra_map_of_subring {R : Type*} [comm_ring R] (S : subring R) :
  (algebra_map S R : S →+* R) = subring.subtype S := rfl

lemma coe_algebra_map_of_subring {R : Type*} [comm_ring R] (S : subring R) :
  (algebra_map S R : S → R) = subtype.val := rfl

lemma algebra_map_of_subring_apply {R : Type*} [comm_ring R] (S : subring R) (x : S) :
  algebra_map S R x = x := rfl

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebra_map_submonoid (S : Type*) [semiring S] [algebra R S]
  (M : submonoid R) : submonoid S :=
M.map (algebra_map R S)

lemma mem_algebra_map_submonoid_of_mem {S : Type*} [semiring S] [algebra R S] {M : submonoid R}
  (x : M) : (algebra_map R S x) ∈ algebra_map_submonoid S M :=
set.mem_image_of_mem (algebra_map R S) x.2

end semiring

section comm_semiring

variables [comm_semiring R]

lemma mul_sub_algebra_map_commutes [ring A] [algebra R A] (x : A) (r : R) :
  x * (x - algebra_map R A r) = (x - algebra_map R A r) * x :=
by rw [mul_sub, ←commutes, sub_mul]

lemma mul_sub_algebra_map_pow_commutes [ring A] [algebra R A] (x : A) (r : R) (n : ℕ) :
  x * (x - algebra_map R A r) ^ n = (x - algebra_map R A r) ^ n * x :=
begin
  induction n with n ih,
  { simp },
  { rw [pow_succ, ←mul_assoc, mul_sub_algebra_map_commutes, mul_assoc, ih, ←mul_assoc] }
end

end comm_semiring

section ring
variables [comm_ring R]

variables (R)

/-- A `semiring` that is an `algebra` over a commutative ring carries a natural `ring` structure.
See note [reducible non-instances]. -/
@[reducible]
def semiring_to_ring [semiring A] [algebra R A] : ring A :=
{ ..module.add_comm_monoid_to_add_comm_group R,
  ..(infer_instance : semiring A) }

end ring

end algebra

namespace mul_opposite

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

instance : algebra R Aᵐᵒᵖ :=
{ to_ring_hom := (algebra_map R A).to_opposite $ λ x y, algebra.commutes _ _,
  smul_def' := λ c x, unop_injective $
    by { dsimp, simp only [op_mul, algebra.smul_def, algebra.commutes, op_unop] },
  commutes' := λ r, mul_opposite.rec $ λ x, by dsimp; simp only [← op_mul, algebra.commutes],
  .. mul_opposite.has_smul A R }

@[simp] lemma algebra_map_apply (c : R) : algebra_map R Aᵐᵒᵖ c = op (algebra_map R A c) := rfl

end mul_opposite

namespace module
variables (R : Type u) (M : Type v) [comm_semiring R] [add_comm_monoid M] [module R M]

instance : algebra R (module.End R M) :=
algebra.of_module smul_mul_assoc (λ r f g, (smul_comm r f g).symm)

lemma algebra_map_End_eq_smul_id (a : R) :
  (algebra_map R (End R M)) a = a • linear_map.id := rfl

@[simp] lemma algebra_map_End_apply (a : R) (m : M) :
  (algebra_map R (End R M)) a m = a • m := rfl

@[simp] lemma ker_algebra_map_End (K : Type u) (V : Type v)
  [field K] [add_comm_group V] [module K V] (a : K) (ha : a ≠ 0) :
  ((algebra_map K (End K V)) a).ker = ⊥ :=
linear_map.ker_smul _ _ ha

section

variables {R M}

lemma End_is_unit_apply_inv_apply_of_is_unit {f : module.End R M} (h : is_unit f) (x : M) :
  f (h.unit.inv x) = x :=
show (f * h.unit.inv) x = x, by simp

lemma End_is_unit_inv_apply_apply_of_is_unit {f : module.End R M} (h : is_unit f) (x : M) :
  h.unit.inv (f x) = x :=
(by simp : (h.unit.inv * f) x = x)

lemma End_is_unit_iff (f : module.End R M) :
  is_unit f ↔ function.bijective f :=
⟨λ h, function.bijective_iff_has_inverse.mpr $
  ⟨h.unit.inv, ⟨End_is_unit_inv_apply_apply_of_is_unit h,
    End_is_unit_apply_inv_apply_of_is_unit h⟩⟩,
 λ H, let e : M ≃ₗ[R] M := { ..f, ..(equiv.of_bijective f H)} in
  ⟨⟨_, e.symm, linear_map.ext e.right_inv, linear_map.ext e.left_inv⟩, rfl⟩⟩

lemma End_algebra_map_is_unit_inv_apply_eq_iff
  {x : R} (h : is_unit (algebra_map R (module.End R M) x)) (m m' : M) :
  h.unit⁻¹ m = m' ↔ m = x • m' :=
{ mp := λ H, ((congr_arg h.unit H).symm.trans (End_is_unit_apply_inv_apply_of_is_unit h _)).symm,
  mpr := λ H, H.symm ▸
  begin
    apply_fun h.unit using ((module.End_is_unit_iff _).mp h).injective,
    erw [End_is_unit_apply_inv_apply_of_is_unit],
    refl,
  end }

lemma End_algebra_map_is_unit_inv_apply_eq_iff'
  {x : R} (h : is_unit (algebra_map R (module.End R M) x)) (m m' : M) :
  m' = h.unit⁻¹ m ↔ m = x • m' :=
{ mp := λ H, ((congr_arg h.unit H).trans (End_is_unit_apply_inv_apply_of_is_unit h _)).symm,
  mpr := λ H, H.symm ▸
  begin
    apply_fun h.unit using ((module.End_is_unit_iff _).mp h).injective,
    erw [End_is_unit_apply_inv_apply_of_is_unit],
    refl,
  end }

end

end module

namespace linear_map

variables {R : Type*} {A : Type*} {B : Type*} [comm_semiring R] [semiring A] [semiring B]
  [algebra R A] [algebra R B]

/-- An alternate statement of `linear_map.map_smul` for when `algebra_map` is more convenient to
work with than `•`. -/
lemma map_algebra_map_mul (f : A →ₗ[R] B) (a : A) (r : R) :
  f (algebra_map R A r * a) = algebra_map R B r * f a :=
by rw [←algebra.smul_def, ←algebra.smul_def, map_smul]

lemma map_mul_algebra_map (f : A →ₗ[R] B) (a : A) (r : R) :
  f (a * algebra_map R A r) = f a * algebra_map R B r :=
by rw [←algebra.commutes, ←algebra.commutes, map_algebra_map_mul]

end linear_map

set_option old_structure_cmd true
/-- Defining the homomorphism in the category R-Alg. -/
@[nolint has_nonempty_instance]
structure alg_hom (R : Type u) (A : Type v) (B : Type w)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B] extends ring_hom A B :=
(commutes' : ∀ r : R, to_fun (algebra_map R A r) = algebra_map R B r)

run_cmd tactic.add_doc_string `alg_hom.to_ring_hom "Reinterpret an `alg_hom` as a `ring_hom`"

infixr ` →ₐ `:25 := alg_hom _
notation A ` →ₐ[`:25 R `] ` B := alg_hom R A B

/-- `alg_hom_class F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class alg_hom_class (F : Type*) (R : out_param Type*) (A : out_param Type*) (B : out_param Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  extends ring_hom_class F A B :=
(commutes : ∀ (f : F) (r : R), f (algebra_map R A r) = algebra_map R B r)

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] alg_hom_class.to_ring_hom_class

attribute [simp] alg_hom_class.commutes

namespace alg_hom_class

variables {R : Type*} {A : Type*} {B : Type*} [comm_semiring R] [semiring A] [semiring B]
  [algebra R A] [algebra R B]

@[priority 100] -- see Note [lower instance priority]
instance {F : Type*} [alg_hom_class F R A B] : linear_map_class F R A B :=
{ map_smulₛₗ := λ f r x, by simp only [algebra.smul_def, map_mul, commutes, ring_hom.id_apply],
  ..‹alg_hom_class F R A B› }

instance {F : Type*} [alg_hom_class F R A B] : has_coe_t F (A →ₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
    commutes' := alg_hom_class.commutes f,
    .. (f : A →+* B) } }

end alg_hom_class

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section semiring

variables [comm_semiring R] [semiring A] [semiring B] [semiring C] [semiring D]
variables [algebra R A] [algebra R B] [algebra R C] [algebra R D]

instance : has_coe_to_fun (A →ₐ[R] B) (λ _, A → B) := ⟨alg_hom.to_fun⟩

initialize_simps_projections alg_hom (to_fun → apply)

@[simp, protected] lemma coe_coe {F : Type*} [alg_hom_class F R A B] (f : F) :
  ⇑(f : A →ₐ[R] B) = f := rfl

@[simp] lemma to_fun_eq_coe (f : A →ₐ[R] B) : f.to_fun = f := rfl

instance : alg_hom_class (A →ₐ[R] B) R A B :=
{ coe := to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  map_add := map_add',
  map_zero := map_zero',
  map_mul := map_mul',
  map_one := map_one',
  commutes := λ f, f.commutes' }

instance coe_ring_hom : has_coe (A →ₐ[R] B) (A →+* B) := ⟨alg_hom.to_ring_hom⟩

instance coe_monoid_hom : has_coe (A →ₐ[R] B) (A →* B) := ⟨λ f, ↑(f : A →+* B)⟩

instance coe_add_monoid_hom : has_coe (A →ₐ[R] B) (A →+ B) := ⟨λ f, ↑(f : A →+* B)⟩

@[simp, norm_cast] lemma coe_mk {f : A → B} (h₁ h₂ h₃ h₄ h₅) :
  ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f := rfl

-- make the coercion the simp-normal form
@[simp] lemma to_ring_hom_eq_coe (f : A →ₐ[R] B) : f.to_ring_hom = f := rfl

@[simp, norm_cast] lemma coe_to_ring_hom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f := rfl

@[simp, norm_cast] lemma coe_to_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f := rfl

@[simp, norm_cast] lemma coe_to_add_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f := rfl

variables (φ : A →ₐ[R] B)

theorem coe_fn_injective : @function.injective (A →ₐ[R] B) (A → B) coe_fn := fun_like.coe_injective

theorem coe_fn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ := fun_like.coe_fn_eq

theorem coe_ring_hom_injective : function.injective (coe : (A →ₐ[R] B) → (A →+* B)) :=
λ φ₁ φ₂ H, coe_fn_injective $ show ((φ₁ : (A →+* B)) : A → B) = ((φ₂ : (A →+* B)) : A → B),
  from congr_arg _ H

theorem coe_monoid_hom_injective : function.injective (coe : (A →ₐ[R] B)  → (A →* B)) :=
ring_hom.coe_monoid_hom_injective.comp coe_ring_hom_injective

theorem coe_add_monoid_hom_injective : function.injective (coe : (A →ₐ[R] B)  → (A →+ B)) :=
ring_hom.coe_add_monoid_hom_injective.comp coe_ring_hom_injective

protected lemma congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
fun_like.congr_fun H x
protected lemma congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
fun_like.congr_arg φ h

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ := fun_like.ext _ _ H

theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x := fun_like.ext_iff

@[simp] theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) :
  (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f := ext $ λ _, rfl

@[simp]
theorem commutes (r : R) : φ (algebra_map R A r) = algebra_map R B r := φ.commutes' r

theorem comp_algebra_map : (φ : A →+* B).comp (algebra_map R A) = algebra_map R B :=
ring_hom.ext $ φ.commutes

protected lemma map_add (r s : A) : φ (r + s) = φ r + φ s := map_add _ _ _
protected lemma map_zero : φ 0 = 0 := map_zero _
protected lemma map_mul (x y) : φ (x * y) = φ x * φ y := map_mul _ _ _
protected lemma map_one : φ 1 = 1 := map_one _
protected lemma map_pow (x : A) (n : ℕ) : φ (x ^ n) = (φ x) ^ n := map_pow _ _ _

@[simp] protected lemma map_smul (r : R) (x : A) : φ (r • x) = r • φ x := map_smul _ _ _

protected lemma map_sum {ι : Type*} (f : ι → A) (s : finset ι) :
  φ (∑ x in s, f x) = ∑ x in s, φ (f x) := map_sum _ _ _

protected lemma map_finsupp_sum {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
  φ (f.sum g) = f.sum (λ i a, φ (g i a)) := map_finsupp_sum _ _ _

protected lemma map_bit0 (x) : φ (bit0 x) = bit0 (φ x) := map_bit0 _ _
protected lemma map_bit1 (x) : φ (bit1 x) = bit1 (φ x) := map_bit1 _ _

/-- If a `ring_hom` is `R`-linear, then it is an `alg_hom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R) x, f (c • x) = c • f x) : A →ₐ[R] B :=
{ to_fun := f,
  commutes' := λ c, by simp only [algebra.algebra_map_eq_smul_one, h, f.map_one],
  .. f }

@[simp] lemma coe_mk' (f : A →+* B) (h : ∀ (c : R) x, f (c • x) = c • f x) : ⇑(mk' f h) = f := rfl

section

variables (R A)
/-- Identity map as an `alg_hom`. -/
protected def id : A →ₐ[R] A :=
{ commutes' := λ _, rfl,
  ..ring_hom.id A }

@[simp] lemma coe_id : ⇑(alg_hom.id R A) = id := rfl

@[simp] lemma id_to_ring_hom : (alg_hom.id R A : A →+* A) = ring_hom.id _ := rfl

end

lemma id_apply (p : A) : alg_hom.id R A p = p := rfl

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
{ commutes' := λ r : R, by rw [← φ₁.commutes, ← φ₂.commutes]; refl,
  .. φ₁.to_ring_hom.comp ↑φ₂ }

@[simp] lemma coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ := rfl

lemma comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) := rfl

lemma comp_to_ring_hom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
  (φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ := rfl

@[simp] theorem comp_id : φ.comp (alg_hom.id R A) = φ :=
ext $ λ x, rfl

@[simp] theorem id_comp : (alg_hom.id R B).comp φ = φ :=
ext $ λ x, rfl

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
  (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
ext $ λ x, rfl

/-- R-Alg ⥤ R-Mod -/
def to_linear_map : A →ₗ[R] B :=
{ to_fun := φ,
  map_add' := map_add _,
  map_smul' := map_smul _ }

@[simp] lemma to_linear_map_apply (p : A) : φ.to_linear_map p = φ p := rfl

theorem to_linear_map_injective : function.injective (to_linear_map : _ → (A →ₗ[R] B)) :=
λ φ₁ φ₂ h, ext $ linear_map.congr_fun h

@[simp] lemma comp_to_linear_map (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  (g.comp f).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

@[simp] lemma to_linear_map_id : to_linear_map (alg_hom.id R A) = linear_map.id :=
linear_map.ext $ λ _, rfl

/-- Promote a `linear_map` to an `alg_hom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def of_linear_map (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
  A →ₐ[R] B :=
{ to_fun := f,
  map_one' := map_one,
  map_mul' := map_mul,
  commutes' := λ c, by simp only [algebra.algebra_map_eq_smul_one, f.map_smul, map_one],
  .. f.to_add_monoid_hom }

@[simp] lemma of_linear_map_to_linear_map (map_one) (map_mul) :
  of_linear_map φ.to_linear_map map_one map_mul = φ :=
by { ext, refl }

@[simp] lemma to_linear_map_of_linear_map (f : A →ₗ[R] B) (map_one) (map_mul) :
  to_linear_map (of_linear_map f map_one map_mul) = f :=
by { ext, refl }

@[simp] lemma of_linear_map_id (map_one) (map_mul) :
  of_linear_map linear_map.id map_one map_mul = alg_hom.id R A :=
ext $ λ _, rfl

lemma map_smul_of_tower {R'} [has_smul R' A] [has_smul R' B]
  [linear_map.compatible_smul A B R' R] (r : R') (x : A) : φ (r • x) = r • φ x :=
φ.to_linear_map.map_smul_of_tower r x

lemma map_list_prod (s : list A) :
  φ s.prod = (s.map φ).prod :=
φ.to_ring_hom.map_list_prod s

@[simps mul one {attrs := []}] instance End : monoid (A →ₐ[R] A) :=
{ mul := comp,
  mul_assoc := λ ϕ ψ χ, rfl,
  one := alg_hom.id R A,
  one_mul := λ ϕ, ext $ λ x, rfl,
  mul_one := λ ϕ, ext $ λ x, rfl }

@[simp] lemma one_apply (x : A) : (1 : A →ₐ[R] A) x = x := rfl

@[simp] lemma mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) := rfl

section prod

variables (R A B)

/-- First projection as `alg_hom`. -/
def fst : A × B →ₐ[R] A :=
{ commutes' := λ r, rfl, .. ring_hom.fst A B}

/-- Second projection as `alg_hom`. -/
def snd : A × B →ₐ[R] B :=
{ commutes' := λ r, rfl, .. ring_hom.snd A B}

variables {R A B}

/-- The `pi.prod` of two morphisms is a morphism. -/
@[simps] def prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (A →ₐ[R] B × C) :=
{ commutes' := λ r, by simp only [to_ring_hom_eq_coe, ring_hom.to_fun_eq_coe, ring_hom.prod_apply,
    coe_to_ring_hom, commutes, algebra.algebra_map_prod_apply],
  .. (f.to_ring_hom.prod g.to_ring_hom) }

lemma coe_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : ⇑(f.prod g) = pi.prod f g := rfl

@[simp] theorem fst_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) :
  (fst R B C).comp (prod f g) = f := by ext; refl

@[simp] theorem snd_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) :
  (snd R B C).comp (prod f g) = g := by ext; refl

@[simp] theorem prod_fst_snd : prod (fst R A B) (snd R A B) = 1 :=
fun_like.coe_injective pi.prod_fst_snd

/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps] def prod_equiv : ((A →ₐ[R] B) × (A →ₐ[R] C)) ≃ (A →ₐ[R] B × C) :=
{ to_fun := λ f, f.1.prod f.2,
  inv_fun := λ f, ((fst _ _ _).comp f, (snd _ _ _).comp f),
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl }

end prod

lemma algebra_map_eq_apply (f : A →ₐ[R] B) {y : R} {x : A} (h : algebra_map R A y = x) :
  algebra_map R B y = f x :=
h ▸ (f.commutes _).symm

end semiring

section comm_semiring

variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra R B] (φ : A →ₐ[R] B)

protected lemma map_multiset_prod (s : multiset A) :
  φ s.prod = (s.map φ).prod := map_multiset_prod _ _

protected lemma map_prod {ι : Type*} (f : ι → A) (s : finset ι) :
  φ (∏ x in s, f x) = ∏ x in s, φ (f x) := map_prod _ _ _

protected lemma map_finsupp_prod {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A) :
  φ (f.prod g) = f.prod (λ i a, φ (g i a)) := map_finsupp_prod _ _ _

end comm_semiring

section ring

variables [comm_semiring R] [ring A] [ring B]
variables [algebra R A] [algebra R B] (φ : A →ₐ[R] B)

protected lemma map_neg (x) : φ (-x) = -φ x := map_neg _ _
protected lemma map_sub (x y) : φ (x - y) = φ x - φ y := map_sub _ _ _

end ring

end alg_hom

@[simp] lemma rat.smul_one_eq_coe {A : Type*} [division_ring A] [algebra ℚ A] (m : ℚ) :
  @@has_smul.smul algebra.to_has_smul m (1 : A) = ↑m :=
by rw [algebra.smul_def, mul_one, eq_rat_cast]

set_option old_structure_cmd true
/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure alg_equiv (R : Type u) (A : Type v) (B : Type w)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B :=
(commutes' : ∀ r : R, to_fun (algebra_map R A r) = algebra_map R B r)

attribute [nolint doc_blame] alg_equiv.to_ring_equiv
attribute [nolint doc_blame] alg_equiv.to_equiv
attribute [nolint doc_blame] alg_equiv.to_add_equiv
attribute [nolint doc_blame] alg_equiv.to_mul_equiv

notation A ` ≃ₐ[`:50 R `] ` A' := alg_equiv R A A'

/-- `alg_equiv_class F R A B` states that `F` is a type of algebra structure preserving
  equivalences. You should extend this class when you extend `alg_equiv`. -/
class alg_equiv_class (F : Type*) (R A B : out_param Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  extends ring_equiv_class F A B :=
(commutes : ∀ (f : F) (r : R), f (algebra_map R A r) = algebra_map R B r)

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] alg_equiv_class.to_ring_equiv_class

namespace alg_equiv_class

@[priority 100] -- See note [lower instance priority]
instance to_alg_hom_class (F R A B : Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  [h : alg_equiv_class F R A B] : alg_hom_class F R A B :=
{ coe := coe_fn,
  coe_injective' := fun_like.coe_injective,
  map_zero := map_zero,
  map_one := map_one,
  .. h }

@[priority 100]
instance to_linear_equiv_class (F R A B : Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  [h : alg_equiv_class F R A B] : linear_equiv_class F R A B :=
{ map_smulₛₗ := λ f, map_smulₛₗ f,
  ..h }

instance (F R A B : Type*) [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]
  [h : alg_equiv_class F R A B] : has_coe_t F (A ≃ₐ[R] B) :=
{ coe := λ f,
  { to_fun := f,
  inv_fun := equiv_like.inv f,
  commutes' := alg_hom_class.commutes f,
  .. (f : A ≃+* B) } }

end alg_equiv_class

namespace alg_equiv

variables {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁}

section semiring

variables [comm_semiring R] [semiring A₁] [semiring A₂] [semiring A₃]
variables [algebra R A₁] [algebra R A₂] [algebra R A₃]
variables (e : A₁ ≃ₐ[R] A₂)

instance : alg_equiv_class (A₁ ≃ₐ[R] A₂) R A₁ A₂ :=
{ coe := to_fun,
  inv := inv_fun,
  coe_injective' := λ f g h₁ h₂, by { cases f, cases g, congr' },
  map_add := map_add',
  map_mul := map_mul',
  commutes := commutes',
  left_inv := left_inv,
  right_inv := right_inv }

/--  Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (A₁ ≃ₐ[R] A₂) (λ _, A₁ → A₂) := ⟨alg_equiv.to_fun⟩

@[simp, protected] lemma coe_coe {F : Type*} [alg_equiv_class F R A₁ A₂] (f : F) :
  ⇑(f : A₁ ≃ₐ[R] A₂) = f := rfl

@[ext]
lemma ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

protected lemma congr_arg {f : A₁ ≃ₐ[R] A₂} {x x' : A₁} : x = x' → f x = f x' :=
fun_like.congr_arg f

protected lemma congr_fun {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x :=
fun_like.congr_fun h x

protected lemma ext_iff {f g : A₁ ≃ₐ[R] A₂} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

lemma coe_fun_injective : @function.injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) (λ e, (e : A₁ → A₂)) :=
fun_like.coe_injective

instance has_coe_to_ring_equiv : has_coe (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) := ⟨alg_equiv.to_ring_equiv⟩

@[simp] lemma coe_mk {to_fun inv_fun left_inv right_inv map_mul map_add commutes} :
  ⇑(⟨to_fun, inv_fun, left_inv, right_inv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = to_fun :=
rfl

@[simp] theorem mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) :
  (⟨e, e', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e := ext $ λ _, rfl

@[simp] lemma to_fun_eq_coe (e : A₁ ≃ₐ[R] A₂) : e.to_fun = e := rfl

@[simp] lemma to_equiv_eq_coe : e.to_equiv = e := rfl

@[simp] lemma to_ring_equiv_eq_coe : e.to_ring_equiv = e := rfl

@[simp, norm_cast] lemma coe_ring_equiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e := rfl

lemma coe_ring_equiv' : (e.to_ring_equiv : A₁ → A₂) = e := rfl

lemma coe_ring_equiv_injective : function.injective (coe : (A₁ ≃ₐ[R] A₂) → (A₁ ≃+* A₂)) :=
λ e₁ e₂ h, ext $ ring_equiv.congr_fun h

protected lemma map_add : ∀ x y, e (x + y) = e x + e y := map_add e
protected lemma map_zero : e 0 = 0 := map_zero e
protected lemma map_mul : ∀ x y, e (x * y) = (e x) * (e y) := map_mul e
protected lemma map_one : e 1 = 1 := map_one e

@[simp] lemma commutes : ∀ (r : R), e (algebra_map R A₁ r) = algebra_map R A₂ r :=
  e.commutes'

@[simp] lemma map_smul (r : R) (x : A₁) : e (r • x) = r • e x :=
by simp only [algebra.smul_def, map_mul, commutes]

lemma map_sum {ι : Type*} (f : ι → A₁) (s : finset ι) :
  e (∑ x in s, f x) = ∑ x in s, e (f x) :=
e.to_add_equiv.map_sum f s

lemma map_finsupp_sum {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A₁) :
  e (f.sum g) = f.sum (λ i b, e (g i b)) :=
e.map_sum _ _

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to_*_hom` projections.
The `simp` normal form is to use the coercion of the `alg_hom_class.has_coe_t` instance. -/
def to_alg_hom : A₁ →ₐ[R] A₂ :=
{ map_one' := e.map_one, map_zero' := e.map_zero, ..e }

@[simp] lemma to_alg_hom_eq_coe : e.to_alg_hom = e := rfl

@[simp, norm_cast] lemma coe_alg_hom : ((e : A₁ →ₐ[R] A₂) : A₁ → A₂) = e :=
rfl

lemma coe_alg_hom_injective : function.injective (coe : (A₁ ≃ₐ[R] A₂) → (A₁ →ₐ[R] A₂)) :=
λ e₁ e₂ h, ext $ alg_hom.congr_fun h

/-- The two paths coercion can take to a `ring_hom` are equivalent -/
lemma coe_ring_hom_commutes : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = ((e : A₁ ≃+* A₂) : A₁ →+* A₂) :=
rfl

protected lemma map_pow : ∀ (x : A₁) (n : ℕ), e (x ^ n) = (e x) ^ n := map_pow _
protected lemma injective : function.injective e := equiv_like.injective e
protected lemma surjective : function.surjective e := equiv_like.surjective e
protected lemma bijective : function.bijective e := equiv_like.bijective e

/-- Algebra equivalences are reflexive. -/
@[refl] def refl : A₁ ≃ₐ[R] A₁ := {commutes' := λ r, rfl, ..(1 : A₁ ≃+* A₁)}

instance : inhabited (A₁ ≃ₐ[R] A₁) := ⟨refl⟩

@[simp] lemma refl_to_alg_hom : ↑(refl : A₁ ≃ₐ[R] A₁) = alg_hom.id R A₁ := rfl

@[simp] lemma coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id := rfl

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
{ commutes' := λ r, by { rw ←e.to_ring_equiv.symm_apply_apply (algebra_map R A₁ r), congr,
                         change _ = e _, rw e.commutes, },
  ..e.to_ring_equiv.symm, }

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ := e.symm

initialize_simps_projections alg_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp] lemma coe_apply_coe_coe_symm_apply {F : Type*} [alg_equiv_class F R A₁ A₂]
  (f : F) (x : A₂) : f ((f : A₁ ≃ₐ[R] A₂).symm x) = x := equiv_like.right_inv f x

@[simp] lemma coe_coe_symm_apply_coe_apply {F : Type*} [alg_equiv_class F R A₁ A₂]
  (f : F) (x : A₁) : (f : A₁ ≃ₐ[R] A₂).symm (f x) = x := equiv_like.left_inv f x

@[simp] lemma inv_fun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.inv_fun = e.symm := rfl

@[simp] lemma symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e :=
by { ext, refl, }

lemma symm_bijective : function.bijective (symm : (A₁ ≃ₐ[R] A₂) → (A₂ ≃ₐ[R] A₁)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) :
  (⟨f, e, h₁, h₂, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[simp] theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
  (⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm =
  { to_fun := f', inv_fun := f,
    ..(⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm } := rfl

@[simp] theorem refl_symm : (alg_equiv.refl : A₁ ≃ₐ[R] A₁).symm = alg_equiv.refl := rfl

--this should be a simp lemma but causes a lint timeout
lemma to_ring_equiv_symm (f : A₁ ≃ₐ[R] A₁) : (f : A₁ ≃+* A₁).symm = f.symm := rfl

@[simp] lemma symm_to_ring_equiv : (e.symm : A₂ ≃+* A₁) = (e : A₁ ≃+* A₂).symm := rfl

/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
{ commutes' := λ r, show e₂.to_fun (e₁.to_fun _) = _, by rw [e₁.commutes', e₂.commutes'],
  ..(e₁.to_ring_equiv.trans e₂.to_ring_equiv), }

@[simp] lemma apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.to_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.to_equiv.symm_apply_apply

@[simp] lemma symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) :
  (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

@[simp] lemma coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[simp] lemma trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma comp_symm (e : A₁ ≃ₐ[R] A₂) :
  alg_hom.comp (e : A₁ →ₐ[R] A₂) ↑e.symm = alg_hom.id R A₂ :=
by { ext, simp }

@[simp] lemma symm_comp (e : A₁ ≃ₐ[R] A₂) :
  alg_hom.comp ↑e.symm (e : A₁ →ₐ[R] A₂) = alg_hom.id R A₁ :=
by { ext, simp }

theorem left_inverse_symm (e : A₁ ≃ₐ[R] A₂) : function.left_inverse e.symm e := e.left_inv

theorem right_inverse_symm (e : A₁ ≃ₐ[R] A₂) : function.right_inverse e.symm e := e.right_inv

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
def arrow_congr {A₁' A₂' : Type*} [semiring A₁'] [semiring A₂'] [algebra R A₁'] [algebra R A₂']
  (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂') :=
{ to_fun := λ f, (e₂.to_alg_hom.comp f).comp e₁.symm.to_alg_hom,
  inv_fun := λ f, (e₂.symm.to_alg_hom.comp f).comp e₁.to_alg_hom,
  left_inv := λ f, by { simp only [alg_hom.comp_assoc, to_alg_hom_eq_coe, symm_comp],
    simp only [←alg_hom.comp_assoc, symm_comp, alg_hom.id_comp, alg_hom.comp_id] },
  right_inv := λ f, by { simp only [alg_hom.comp_assoc, to_alg_hom_eq_coe, comp_symm],
    simp only [←alg_hom.comp_assoc, comp_symm, alg_hom.id_comp, alg_hom.comp_id] } }

lemma arrow_congr_comp {A₁' A₂' A₃' : Type*} [semiring A₁'] [semiring A₂'] [semiring A₃']
  [algebra R A₁'] [algebra R A₂'] [algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂')
  (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₃) :
  arrow_congr e₁ e₃ (g.comp f) = (arrow_congr e₂ e₃ g).comp (arrow_congr e₁ e₂ f) :=
by { ext, simp only [arrow_congr, equiv.coe_fn_mk, alg_hom.comp_apply],
  congr, exact (e₂.symm_apply_apply _).symm }

@[simp] lemma arrow_congr_refl :
  arrow_congr alg_equiv.refl alg_equiv.refl = equiv.refl (A₁ →ₐ[R] A₂) :=
by { ext, refl }

@[simp] lemma arrow_congr_trans {A₁' A₂' A₃' : Type*} [semiring A₁'] [semiring A₂'] [semiring A₃']
  [algebra R A₁'] [algebra R A₂'] [algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂')
  (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
  arrow_congr (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr e₁ e₁').trans (arrow_congr e₂ e₂') :=
by { ext, refl }

@[simp] lemma arrow_congr_symm {A₁' A₂' : Type*} [semiring A₁'] [semiring A₂']
  [algebra R A₁'] [algebra R A₂'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') :
  (arrow_congr e₁ e₂).symm = arrow_congr e₁.symm e₂.symm :=
by { ext, refl }

/-- If an algebra morphism has an inverse, it is a algebra isomorphism. -/
def of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = alg_hom.id R A₂)
  (h₂ : g.comp f = alg_hom.id R A₁) : A₁ ≃ₐ[R] A₂ :=
{ to_fun    := f,
  inv_fun   := g,
  left_inv  := alg_hom.ext_iff.1 h₂,
  right_inv := alg_hom.ext_iff.1 h₁,
  ..f }

lemma coe_alg_hom_of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
  ↑(of_alg_hom f g h₁ h₂) = f := alg_hom.ext $ λ _, rfl

@[simp]
lemma of_alg_hom_coe_alg_hom (f : A₁ ≃ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
  of_alg_hom ↑f g h₁ h₂ = f := ext $ λ _, rfl

lemma of_alg_hom_symm (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) :
  (of_alg_hom f g h₁ h₂).symm = of_alg_hom g f h₂ h₁ := rfl

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def of_bijective (f : A₁ →ₐ[R] A₂) (hf : function.bijective f) : A₁ ≃ₐ[R] A₂ :=
{ .. ring_equiv.of_bijective (f : A₁ →+* A₂) hf, .. f }

@[simp] lemma coe_of_bijective {f : A₁ →ₐ[R] A₂} {hf : function.bijective f} :
  (alg_equiv.of_bijective f hf : A₁ → A₂) = f := rfl

lemma of_bijective_apply {f : A₁ →ₐ[R] A₂} {hf : function.bijective f} (a : A₁) :
  (alg_equiv.of_bijective f hf) a = f a := rfl

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply] def to_linear_equiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ :=
{ to_fun    := e,
  map_smul' := e.map_smul,
  inv_fun   := e.symm,
  .. e }

@[simp] lemma to_linear_equiv_refl :
  (alg_equiv.refl : A₁ ≃ₐ[R] A₁).to_linear_equiv = linear_equiv.refl R A₁ := rfl

@[simp] lemma to_linear_equiv_symm (e : A₁ ≃ₐ[R] A₂) :
  e.to_linear_equiv.symm = e.symm.to_linear_equiv := rfl

@[simp] lemma to_linear_equiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
  (e₁.trans e₂).to_linear_equiv = e₁.to_linear_equiv.trans e₂.to_linear_equiv := rfl

theorem to_linear_equiv_injective : function.injective (to_linear_equiv : _ → (A₁ ≃ₗ[R] A₂)) :=
λ e₁ e₂ h, ext $ linear_equiv.congr_fun h

/-- Interpret an algebra equivalence as a linear map. -/
def to_linear_map : A₁ →ₗ[R] A₂ :=
e.to_alg_hom.to_linear_map

@[simp] lemma to_alg_hom_to_linear_map :
  (e : A₁ →ₐ[R] A₂).to_linear_map = e.to_linear_map := rfl

@[simp] lemma to_linear_equiv_to_linear_map :
  e.to_linear_equiv.to_linear_map = e.to_linear_map := rfl

@[simp] lemma to_linear_map_apply (x : A₁) : e.to_linear_map x = e x := rfl

theorem to_linear_map_injective : function.injective (to_linear_map : _ → (A₁ →ₗ[R] A₂)) :=
λ e₁ e₂ h, ext $ linear_map.congr_fun h

@[simp] lemma trans_to_linear_map (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
  (f.trans g).to_linear_map = g.to_linear_map.comp f.to_linear_map := rfl

section of_linear_equiv

variables (l : A₁ ≃ₗ[R] A₂)
  (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)
  (commutes : ∀ r : R, l (algebra_map R A₁ r) = algebra_map R A₂ r)

/--
Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and action of scalars.
-/
@[simps apply]
def of_linear_equiv : A₁ ≃ₐ[R] A₂ :=
{ to_fun := l,
  inv_fun := l.symm,
  map_mul' := map_mul,
  commutes' := commutes,
  ..l }

@[simp]
lemma of_linear_equiv_symm :
  (of_linear_equiv l map_mul commutes).symm = of_linear_equiv l.symm
    ((of_linear_equiv l map_mul commutes).symm.map_mul)
    ((of_linear_equiv l map_mul commutes).symm.commutes) :=
rfl

@[simp] lemma of_linear_equiv_to_linear_equiv (map_mul) (commutes) :
  of_linear_equiv e.to_linear_equiv map_mul commutes = e :=
by { ext, refl }

@[simp] lemma to_linear_equiv_of_linear_equiv :
  to_linear_equiv (of_linear_equiv l map_mul commutes) = l :=
by { ext, refl }

end of_linear_equiv

section of_ring_equiv

/-- Promotes a linear ring_equiv to an alg_equiv. -/
@[simps]
def of_ring_equiv {f : A₁ ≃+* A₂}
  (hf : ∀ x, f (algebra_map R A₁ x) = algebra_map R A₂ x) : A₁ ≃ₐ[R] A₂ :=
{ to_fun := f,
  inv_fun := f.symm,
  commutes' := hf,
  .. f }

end of_ring_equiv

@[simps mul one {attrs := []}] instance aut : group (A₁ ≃ₐ[R] A₁) :=
{ mul := λ ϕ ψ, ψ.trans ϕ,
  mul_assoc := λ ϕ ψ χ, rfl,
  one := refl,
  one_mul := λ ϕ, ext $ λ x, rfl,
  mul_one := λ ϕ, ext $ λ x, rfl,
  inv := symm,
  mul_left_inv := λ ϕ, ext $ symm_apply_apply ϕ }

@[simp] lemma one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x := rfl

@[simp] lemma mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

/-- An algebra isomorphism induces a group isomorphism between automorphism groups -/
@[simps apply]
def aut_congr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* (A₂ ≃ₐ[R] A₂) :=
{ to_fun := λ ψ, ϕ.symm.trans (ψ.trans ϕ),
  inv_fun := λ ψ, ϕ.trans (ψ.trans ϕ.symm),
  left_inv := λ ψ, by { ext, simp_rw [trans_apply, symm_apply_apply] },
  right_inv := λ ψ, by { ext, simp_rw [trans_apply, apply_symm_apply] },
  map_mul' := λ ψ χ, by { ext, simp only [mul_apply, trans_apply, symm_apply_apply] } }

@[simp] lemma aut_congr_refl : aut_congr (alg_equiv.refl) = mul_equiv.refl (A₁ ≃ₐ[R] A₁) :=
by { ext, refl }

@[simp] lemma aut_congr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (aut_congr ϕ).symm = aut_congr ϕ.symm := rfl

@[simp] lemma aut_congr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) :
  (aut_congr ϕ).trans (aut_congr ψ) = aut_congr (ϕ.trans ψ) := rfl

/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_mul_semiring_action : mul_semiring_action (A₁ ≃ₐ[R] A₁) A₁ :=
{ smul := ($),
  smul_zero := alg_equiv.map_zero,
  smul_add := alg_equiv.map_add,
  smul_one := alg_equiv.map_one,
  smul_mul := alg_equiv.map_mul,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] protected lemma smul_def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a := rfl

instance apply_has_faithful_smul : has_faithful_smul (A₁ ≃ₐ[R] A₁) A₁ :=
⟨λ _ _, alg_equiv.ext⟩

instance apply_smul_comm_class : smul_comm_class R (A₁ ≃ₐ[R] A₁) A₁ :=
{ smul_comm := λ r e a, (e.map_smul r a).symm }

instance apply_smul_comm_class' : smul_comm_class (A₁ ≃ₐ[R] A₁) R A₁ :=
{ smul_comm := λ e r a, (e.map_smul r a) }

@[simp] lemma algebra_map_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} :
  (algebra_map R A₂ y = e x) ↔ (algebra_map R A₁ y = x) :=
⟨λ h, by simpa using e.symm.to_alg_hom.algebra_map_eq_apply h,
 λ h, e.to_alg_hom.algebra_map_eq_apply h⟩

end semiring

section comm_semiring

variables [comm_semiring R] [comm_semiring A₁] [comm_semiring A₂]
variables [algebra R A₁] [algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

lemma map_prod {ι : Type*} (f : ι → A₁) (s : finset ι) :
  e (∏ x in s, f x) = ∏ x in s, e (f x) :=
map_prod _ f s

lemma map_finsupp_prod {α : Type*} [has_zero α] {ι : Type*} (f : ι →₀ α) (g : ι → α → A₁) :
  e (f.prod g) = f.prod (λ i a, e (g i a)) :=
map_finsupp_prod _ f g

end comm_semiring

section ring

variables [comm_semiring R] [ring A₁] [ring A₂]
variables [algebra R A₁] [algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

protected lemma map_neg (x) : e (-x) = -e x := map_neg e x
protected lemma map_sub (x y) : e (x - y) = e x - e y := map_sub e x y

end ring

end alg_equiv

namespace mul_semiring_action

variables {M G : Type*} (R A : Type*) [comm_semiring R] [semiring A] [algebra R A]

section
variables [monoid M] [mul_semiring_action M A] [smul_comm_class M R A]

/-- Each element of the monoid defines a algebra homomorphism.

This is a stronger version of `mul_semiring_action.to_ring_hom` and
`distrib_mul_action.to_linear_map`. -/
@[simps]
def to_alg_hom (m : M) : A →ₐ[R] A :=
{ to_fun := λ a, m • a,
  commutes' := smul_algebra_map _,
  ..mul_semiring_action.to_ring_hom _ _ m }

theorem to_alg_hom_injective [has_faithful_smul M A] :
  function.injective (mul_semiring_action.to_alg_hom R A : M → A →ₐ[R] A) :=
λ m₁ m₂ h, eq_of_smul_eq_smul $ λ r, alg_hom.ext_iff.1 h r

end

section
variables [group G] [mul_semiring_action G A] [smul_comm_class G R A]

/-- Each element of the group defines a algebra equivalence.

This is a stronger version of `mul_semiring_action.to_ring_equiv` and
`distrib_mul_action.to_linear_equiv`. -/
@[simps]
def to_alg_equiv (g : G) : A ≃ₐ[R] A :=
{ .. mul_semiring_action.to_ring_equiv _ _ g,
  .. mul_semiring_action.to_alg_hom R A g }

theorem to_alg_equiv_injective [has_faithful_smul G A] :
  function.injective (mul_semiring_action.to_alg_equiv R A : G → A ≃ₐ[R] A) :=
λ m₁ m₂ h, eq_of_smul_eq_smul $ λ r, alg_equiv.ext_iff.1 h r

end

end mul_semiring_action

section nat

variables {R : Type*} [semiring R]

-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℕ`-algebras. This is only an issue since `algebra.id` and `algebra_nat` are not yet defeq.
-- TODO: fix this by adding an `of_nat` field to semirings.
/-- Semiring ⥤ ℕ-Alg -/
@[priority 99] instance algebra_nat : algebra ℕ R :=
{ commutes' := nat.cast_commute,
  smul_def' := λ _ _, nsmul_eq_mul _ _,
  to_ring_hom := nat.cast_ring_hom R }

instance nat_algebra_subsingleton : subsingleton (algebra ℕ R) :=
⟨λ P Q, by { ext, simp, }⟩

end nat

namespace ring_hom

variables {R S : Type*}

/-- Reinterpret a `ring_hom` as an `ℕ`-algebra homomorphism. -/
def to_nat_alg_hom [semiring R] [semiring S] (f : R →+* S) :
  R →ₐ[ℕ] S :=
{ to_fun := f, commutes' := λ n, by simp, .. f }

/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def to_int_alg_hom [ring R] [ring S] [algebra ℤ R] [algebra ℤ S] (f : R →+* S) :
  R →ₐ[ℤ] S :=
{ commutes' := λ n, by simp, .. f }

-- note that `R`, `S` could be `semiring`s but this is useless mathematically speaking -
-- a ℚ-algebra is a ring. furthermore, this change probably slows down elaboration.
@[simp] lemma map_rat_algebra_map [ring R] [ring S] [algebra ℚ R] [algebra ℚ S]
  (f : R →+* S) (r : ℚ) : f (algebra_map ℚ R r) = algebra_map ℚ S r :=
ring_hom.ext_iff.1 (subsingleton.elim (f.comp (algebra_map ℚ R)) (algebra_map ℚ S)) r

/-- Reinterpret a `ring_hom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `ring_hom.equiv_rat_alg_hom`. -/
def to_rat_alg_hom [ring R] [ring S] [algebra ℚ R] [algebra ℚ S] (f : R →+* S) :
  R →ₐ[ℚ] S :=
{ commutes' := f.map_rat_algebra_map, .. f }

@[simp]
lemma to_rat_alg_hom_to_ring_hom [ring R] [ring S] [algebra ℚ R] [algebra ℚ S]
  (f : R →+* S) : ↑f.to_rat_alg_hom = f :=
ring_hom.ext $ λ x, rfl

end ring_hom

section

variables {R S : Type*}

@[simp]
lemma alg_hom.to_ring_hom_to_rat_alg_hom [ring R] [ring S] [algebra ℚ R] [algebra ℚ S]
  (f : R →ₐ[ℚ] S) : (f : R →+* S).to_rat_alg_hom = f :=
alg_hom.ext $ λ x, rfl

/-- The equivalence between `ring_hom` and `ℚ`-algebra homomorphisms. -/
@[simps]
def ring_hom.equiv_rat_alg_hom [ring R] [ring S] [algebra ℚ R] [algebra ℚ S] :
  (R →+* S) ≃ (R →ₐ[ℚ] S) :=
{ to_fun := ring_hom.to_rat_alg_hom,
  inv_fun := alg_hom.to_ring_hom,
  left_inv := ring_hom.to_rat_alg_hom_to_ring_hom,
  right_inv := alg_hom.to_ring_hom_to_rat_alg_hom, }

end

section rat

instance algebra_rat {α} [division_ring α] [char_zero α] : algebra ℚ α :=
{ smul := (•),
  smul_def' := division_ring.qsmul_eq_mul',
  to_ring_hom := rat.cast_hom α,
  commutes' := rat.cast_commute }

/-- The two `algebra ℚ ℚ` instances should coincide. -/
example : algebra_rat = algebra.id ℚ := rfl

@[simp] theorem algebra_map_rat_rat : algebra_map ℚ ℚ = ring_hom.id ℚ :=
subsingleton.elim _ _

instance algebra_rat_subsingleton {α} [semiring α] :
  subsingleton (algebra ℚ α) :=
⟨λ x y, algebra.algebra_ext x y $ ring_hom.congr_fun $ subsingleton.elim _ _⟩

end rat

namespace algebra
open module

variables (R : Type u) (A : Type v)

variables [comm_semiring R] [semiring A] [algebra R A]

/-- `algebra_map` as an `alg_hom`. -/
def of_id : R →ₐ[R] A :=
{ commutes' := λ _, rfl, .. algebra_map R A }
variables {R}

theorem of_id_apply (r) : of_id R A r = algebra_map R A r := rfl

end algebra

section int

variables (R : Type*) [ring R]

-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℤ`-algebras. This is only an issue since `algebra.id ℤ` and `algebra_int ℤ` are not yet defeq.
-- TODO: fix this by adding an `of_int` field to rings.
/-- Ring ⥤ ℤ-Alg -/
@[priority 99] instance algebra_int : algebra ℤ R :=
{ commutes' := int.cast_commute,
  smul_def' := λ _ _, zsmul_eq_mul _ _,
  to_ring_hom := int.cast_ring_hom R }

/-- A special case of `eq_int_cast'` that happens to be true definitionally -/
@[simp] lemma algebra_map_int_eq : algebra_map ℤ R = int.cast_ring_hom R := rfl

variables {R}

instance int_algebra_subsingleton : subsingleton (algebra ℤ R) :=
⟨λ P Q, by { ext, simp, }⟩

end int

namespace no_zero_smul_divisors

variables {R A : Type*}

open algebra

/-- If `algebra_map R A` is injective and `A` has no zero divisors,
`R`-multiples in `A` are zero only if one of the factors is zero.

Cannot be an instance because there is no `injective (algebra_map R A)` typeclass.
-/
lemma of_algebra_map_injective
  [comm_semiring R] [semiring A] [algebra R A] [no_zero_divisors A]
  (h : function.injective (algebra_map R A)) : no_zero_smul_divisors R A :=
⟨λ c x hcx, (mul_eq_zero.mp ((smul_def c x).symm.trans hcx)).imp_left
  (map_eq_zero_iff (algebra_map R A) h).mp⟩

variables (R A)
lemma algebra_map_injective [comm_ring R] [ring A] [nontrivial A]
  [algebra R A] [no_zero_smul_divisors R A] :
  function.injective (algebra_map R A) :=
suffices function.injective (λ (c : R), c • (1 : A)),
by { convert this, ext, rw [algebra.smul_def, mul_one] },
smul_left_injective R one_ne_zero

lemma _root_.ne_zero.of_no_zero_smul_divisors (n : ℕ) [comm_ring R] [ne_zero (n : R)] [ring A]
  [nontrivial A] [algebra R A] [no_zero_smul_divisors R A] : ne_zero (n : A) :=
ne_zero.nat_of_injective $ no_zero_smul_divisors.algebra_map_injective R A

variables {R A}
lemma iff_algebra_map_injective [comm_ring R] [ring A] [is_domain A] [algebra R A] :
  no_zero_smul_divisors R A ↔ function.injective (algebra_map R A) :=
⟨@@no_zero_smul_divisors.algebra_map_injective R A _ _ _ _,
 no_zero_smul_divisors.of_algebra_map_injective⟩

@[priority 100] -- see note [lower instance priority]
instance char_zero.no_zero_smul_divisors_nat [semiring R] [no_zero_divisors R] [char_zero R] :
  no_zero_smul_divisors ℕ R :=
no_zero_smul_divisors.of_algebra_map_injective $ (algebra_map ℕ R).injective_nat

@[priority 100] -- see note [lower instance priority]
instance char_zero.no_zero_smul_divisors_int [ring R] [no_zero_divisors R] [char_zero R] :
  no_zero_smul_divisors ℤ R :=
no_zero_smul_divisors.of_algebra_map_injective $ (algebra_map ℤ R).injective_int

section field

variables [field R] [semiring A] [algebra R A]

@[priority 100] -- see note [lower instance priority]
instance algebra.no_zero_smul_divisors [nontrivial A] [no_zero_divisors A] :
  no_zero_smul_divisors R A :=
no_zero_smul_divisors.of_algebra_map_injective (algebra_map R A).injective

end field

end no_zero_smul_divisors

/-!
The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

We couldn't set this up back in `algebra.pi_instances` because this file imports it.
-/
namespace pi

variable {I : Type u}     -- The indexing type
variable {R : Type*}      -- The scalar type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)
variables (I f)

instance algebra {r : comm_semiring R}
  [s : ∀ i, semiring (f i)] [∀ i, algebra R (f i)] :
  algebra R (Π i : I, f i) :=
{ commutes' := λ a f, begin ext, simp [algebra.commutes], end,
  smul_def' := λ a f, begin ext, simp [algebra.smul_def], end,
  ..(pi.ring_hom (λ i, algebra_map R (f i)) : R →+* Π i : I, f i) }

lemma algebra_map_def {r : comm_semiring R}
  [s : ∀ i, semiring (f i)] [∀ i, algebra R (f i)] (a : R) :
  algebra_map R (Π i, f i) a = (λ i, algebra_map R (f i) a) := rfl

@[simp] lemma algebra_map_apply {r : comm_semiring R}
  [s : ∀ i, semiring (f i)] [∀ i, algebra R (f i)] (a : R) (i : I) :
  algebra_map R (Π i, f i) a i = algebra_map R (f i) a := rfl

-- One could also build a `Π i, R i`-algebra structure on `Π i, A i`,
-- when each `A i` is an `R i`-algebra, although I'm not sure that it's useful.

variables {I} (R) (f)

/-- `function.eval` as an `alg_hom`. The name matches `pi.eval_ring_hom`, `pi.eval_monoid_hom`,
etc. -/
@[simps]
def eval_alg_hom {r : comm_semiring R} [Π i, semiring (f i)] [Π i, algebra R (f i)] (i : I) :
  (Π i, f i) →ₐ[R] f i :=
{ to_fun := λ f, f i, commutes' := λ r, rfl, .. pi.eval_ring_hom f i}

variables (A B : Type*) [comm_semiring R] [semiring B] [algebra R B]

/-- `function.const` as an `alg_hom`. The name matches `pi.const_ring_hom`, `pi.const_monoid_hom`,
etc. -/
@[simps]
def const_alg_hom : B →ₐ[R] (A → B) :=
{ to_fun := function.const _,
  commutes' := λ r, rfl,
  .. pi.const_ring_hom A B}

/-- When `R` is commutative and permits an `algebra_map`, `pi.const_ring_hom` is equal to that
map. -/
@[simp] lemma const_ring_hom_eq_algebra_map : const_ring_hom A R = algebra_map R (A → R) :=
rfl

@[simp] lemma const_alg_hom_eq_algebra_of_id : const_alg_hom R A R = algebra.of_id R (A → R) :=
rfl

end pi

/-- A special case of `pi.algebra` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this, -/
instance function.algebra {R : Type*} (I : Type*)  (A : Type*) [comm_semiring R]
  [semiring A] [algebra R A] : algebra R (I → A) :=
pi.algebra _ _

namespace alg_equiv

/-- A family of algebra equivalences `Π j, (A₁ j ≃ₐ A₂ j)` generates a
multiplicative equivalence between `Π j, A₁ j` and `Π j, A₂ j`.

This is the `alg_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`alg_equiv.arrow_congr`.
-/
@[simps apply]
def Pi_congr_right {R ι : Type*} {A₁ A₂ : ι → Type*} [comm_semiring R]
  [Π i, semiring (A₁ i)] [Π i, semiring (A₂ i)] [Π i, algebra R (A₁ i)] [Π i, algebra R (A₂ i)]
  (e : Π i, A₁ i ≃ₐ[R] A₂ i) : (Π i, A₁ i) ≃ₐ[R] Π i, A₂ i :=
{ to_fun := λ x j, e j (x j),
  inv_fun := λ x j, (e j).symm (x j),
  commutes' := λ r, by { ext i, simp },
  .. @ring_equiv.Pi_congr_right ι A₁ A₂ _ _ (λ i, (e i).to_ring_equiv) }

@[simp]
lemma Pi_congr_right_refl {R ι : Type*} {A : ι → Type*} [comm_semiring R]
  [Π i, semiring (A i)] [Π i, algebra R (A i)] :
  Pi_congr_right (λ i, (alg_equiv.refl : A i ≃ₐ[R] A i)) = alg_equiv.refl := rfl

@[simp]
lemma Pi_congr_right_symm {R ι : Type*} {A₁ A₂ : ι → Type*} [comm_semiring R]
  [Π i, semiring (A₁ i)] [Π i, semiring (A₂ i)] [Π i, algebra R (A₁ i)] [Π i, algebra R (A₂ i)]
  (e : Π i, A₁ i ≃ₐ[R] A₂ i) : (Pi_congr_right e).symm = (Pi_congr_right $ λ i, (e i).symm) := rfl

@[simp]
lemma Pi_congr_right_trans {R ι : Type*} {A₁ A₂ A₃ : ι → Type*} [comm_semiring R]
  [Π i, semiring (A₁ i)] [Π i, semiring (A₂ i)] [Π i, semiring (A₃ i)]
  [Π i, algebra R (A₁ i)] [Π i, algebra R (A₂ i)] [Π i, algebra R (A₃ i)]
  (e₁ : Π i, A₁ i ≃ₐ[R] A₂ i) (e₂ : Π i, A₂ i ≃ₐ[R] A₃ i) :
  (Pi_congr_right e₁).trans (Pi_congr_right e₂) = (Pi_congr_right $ λ i, (e₁ i).trans (e₂ i)) :=
rfl

end alg_equiv

section is_scalar_tower

variables {R : Type*} [comm_semiring R]
variables (A : Type*) [semiring A] [algebra R A]
variables {M : Type*} [add_comm_monoid M] [module A M] [module R M] [is_scalar_tower R A M]
variables {N : Type*} [add_comm_monoid N] [module A N] [module R N] [is_scalar_tower R A N]

lemma algebra_compatible_smul (r : R) (m : M) : r • m = ((algebra_map R A) r) • m :=
by rw [←(one_smul A m), ←smul_assoc, algebra.smul_def, mul_one, one_smul]

@[simp] lemma algebra_map_smul (r : R) (m : M) : ((algebra_map R A) r) • m = r • m :=
(algebra_compatible_smul A r m).symm

lemma int_cast_smul {k V : Type*} [comm_ring k] [add_comm_group V] [module k V] (r : ℤ) (x : V) :
  (r : k) • x = r • x :=
algebra_map_smul k r x

lemma no_zero_smul_divisors.trans (R A M : Type*) [comm_ring R] [ring A] [is_domain A] [algebra R A]
  [add_comm_group M] [module R M] [module A M] [is_scalar_tower R A M] [no_zero_smul_divisors R A]
  [no_zero_smul_divisors A M] : no_zero_smul_divisors R M :=
begin
  refine ⟨λ r m h, _⟩,
  rw [algebra_compatible_smul A r m] at h,
  cases smul_eq_zero.1 h with H H,
  { have : function.injective (algebra_map R A) :=
      no_zero_smul_divisors.iff_algebra_map_injective.1 infer_instance,
    left,
    exact (injective_iff_map_eq_zero _).1 this _ H },
  { right,
    exact H }
end

variable {A}

@[priority 100] -- see Note [lower instance priority]
instance is_scalar_tower.to_smul_comm_class : smul_comm_class R A M :=
⟨λ r a m, by rw [algebra_compatible_smul A r (a • m), smul_smul, algebra.commutes, mul_smul,
  ←algebra_compatible_smul]⟩

@[priority 100] -- see Note [lower instance priority]
instance is_scalar_tower.to_smul_comm_class' : smul_comm_class A R M :=
smul_comm_class.symm _ _ _

lemma smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
smul_comm _ _ _

namespace linear_map

instance coe_is_scalar_tower : has_coe (M →ₗ[A] N) (M →ₗ[R] N) :=
⟨restrict_scalars R⟩

variables (R) {A M N}

@[simp, norm_cast squash] lemma coe_restrict_scalars_eq_coe (f : M →ₗ[A] N) :
  (f.restrict_scalars R : M → N) = f := rfl

@[simp, norm_cast squash] lemma coe_coe_is_scalar_tower (f : M →ₗ[A] N) :
  ((f : M →ₗ[R] N) : M → N) = f := rfl

/-- `A`-linearly coerce a `R`-linear map from `M` to `A` to a function, given an algebra `A` over
a commutative semiring `R` and `M` a module over `R`. -/
def lto_fun (R : Type u) (M : Type v) (A : Type w)
  [comm_semiring R] [add_comm_monoid M] [module R M] [comm_ring A] [algebra R A] :
  (M →ₗ[R] A) →ₗ[A] (M → A) :=
{ to_fun := linear_map.to_fun,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl }

end linear_map

end is_scalar_tower

/-! TODO: The following lemmas no longer involve `algebra` at all, and could be moved closer
to `algebra/module/submodule.lean`. Currently this is tricky because `ker`, `range`, `⊤`, and `⊥`
are all defined in `linear_algebra/basic.lean`. -/
section module
open module

variables (R S M N : Type*) [semiring R] [semiring S] [has_smul R S]
variables [add_comm_monoid M] [module R M] [module S M] [is_scalar_tower R S M]
variables [add_comm_monoid N] [module R N] [module S N] [is_scalar_tower R S N]

variables {S M N}

@[simp]
lemma linear_map.ker_restrict_scalars (f : M →ₗ[S] N) :
  (f.restrict_scalars R).ker = f.ker.restrict_scalars R :=
rfl

end module

namespace submodule

variables (R A M : Type*)
variables [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid M]
variables [module R M] [module A M] [is_scalar_tower R A M]

/-- If `A` is an `R`-algebra such that the induced morhpsim `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
lemma span_eq_restrict_scalars (X : set M) (hsur : function.surjective (algebra_map R A)) :
  span R X = restrict_scalars R (span A X) :=
begin
  apply (span_le_restrict_scalars R A X).antisymm (λ m hm, _),
  refine span_induction hm subset_span (zero_mem _) (λ _ _, add_mem) (λ a m hm, _),
  obtain ⟨r, rfl⟩ := hsur a,
  simpa [algebra_map_smul] using smul_mem _ r hm
end

end submodule

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w} {I : Type*}

variables [comm_semiring R] [semiring A] [semiring B]
variables [algebra R A] [algebra R B]

/-- `R`-algebra homomorphism between the function spaces `I → A` and `I → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps] protected def comp_left (f : A →ₐ[R] B) (I : Type*) : (I → A) →ₐ[R] (I → B) :=
{ to_fun := λ h, f ∘ h,
  commutes' := λ c, by { ext, exact f.commutes' c },
  .. f.to_ring_hom.comp_left I }

end alg_hom

example {R A} [comm_semiring R] [semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A] : algebra R A :=
algebra.of_module smul_mul_assoc mul_smul_comm
