/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.associated
import algebra.module.basic
import algebra.order.absolute_value
import data.int.cast
import group_theory.group_action.units

/-!
# Absolute values and the integers

This file contains some results on absolute values applied to integers.

## Main results

 * `absolute_value.map_units_int`: an absolute value sends all units of `ℤ` to `1`
 * `int.nat_abs_hom`: `int.nat_abs` bundled as a `monoid_with_zero_hom`
-/

variables {R S : Type*} [ring R] [linear_ordered_comm_ring S]

@[simp]
lemma absolute_value.map_units_int (abv : absolute_value ℤ S) (x : ℤˣ) :
  abv x = 1 :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp

@[simp]
lemma absolute_value.map_units_int_cast [nontrivial R] (abv : absolute_value R S) (x : ℤˣ) :
  abv ((x : ℤ) : R) = 1 :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp

@[simp]
lemma absolute_value.map_units_int_smul (abv : absolute_value R S) (x : ℤˣ) (y : R) :
  abv (x • y) = abv y :=
by rcases int.units_eq_one_or x with (rfl | rfl); simp

lemma int.nat_abs_eq_iff_associated {a b : ℤ} :
  a.nat_abs = b.nat_abs ↔ associated a b :=
begin
  refine int.nat_abs_eq_nat_abs_iff.trans _,
  split,
  { rintro (rfl | rfl),
    { refl },
    { exact ⟨-1, by simp⟩ } },
  { rintro ⟨u, rfl⟩,
    obtain (rfl | rfl) := int.units_eq_one_or u,
    { exact or.inl (by simp) },
    { exact or.inr (by simp) } }
end

/-- `int.nat_abs` as a bundled monoid with zero hom. -/
@[simps]
def int.nat_abs_hom : ℤ →*₀ ℕ :=
{ to_fun := int.nat_abs,
  map_mul' := int.nat_abs_mul,
  map_one' := int.nat_abs_one,
  map_zero' := int.nat_abs_zero }
