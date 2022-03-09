import algebra.ring.basic
import algebra.group.hom

structure centroid (A : Type*) [non_unital_non_assoc_semiring A] extends A →+ A :=
(lmul_comm: ∀ (a b : A), to_add_monoid_hom (a*b) = a * (to_add_monoid_hom b))
(rmul_comm: ∀ (a b : A), to_add_monoid_hom (a*b) = (to_add_monoid_hom a) * b)

class centroid_class (F A : Type*) [non_unital_non_assoc_semiring A]  extends add_monoid_hom_class F A A

instance centroid.has_coe_to_add_monoid_hom (A : Type*) [non_unital_non_assoc_semiring A] : has_coe (centroid A) (A →+ A) := ⟨centroid.to_add_monoid_hom⟩

instance centroid.centroid_class (A : Type*) [non_unital_non_assoc_semiring A] :
  centroid_class (centroid A) A :=
{ coe := sorry, --centroid.to_fun,
  coe_injective' := sorry, --λ f g h, by cases f; cases g; congr',
  map_add := begin
    rintro T a b,

    rw add_monoid_hom.map_add,
  end,
  map_zero := add_monoid_hom.map_zero }

variables (A : Type*) [non_unital_non_assoc_semiring A]

instance : has_add (centroid A) := {
  add := λ T S, {
    lmul_comm := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.add_apply, centroid.lmul_comm, left_distrib],

    rmul_comm := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.add_apply, centroid.rmul_comm, right_distrib],
    ..T.to_add_monoid_hom  + S.to_add_monoid_hom,
  }
}

instance : has_zero (centroid A) := {
  zero := {
    lmul_comm := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.zero_apply, mul_zero],
    rmul_comm := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.zero_apply, zero_mul],
    ..(0 : A →+ A)
  }
}

instance : has_one (centroid A) := {
  one := {
    lmul_comm := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.id_apply],
    rmul_comm := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.id_apply],
    ..add_monoid_hom.id A,
  }
}

instance : has_mul (centroid A) := {
  mul := λ T S, {
    lmul_comm := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.coe_comp, add_monoid_hom.coe_mk,
        function.comp_app, centroid.lmul_comm],
    rmul_comm := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.coe_comp, add_monoid_hom.coe_mk,
        function.comp_app, centroid.rmul_comm],
    ..add_monoid_hom.comp T.to_add_monoid_hom S.to_add_monoid_hom,
  }
}



namespace centroid

instance : has_coe_to_fun (centroid A) (λ _, A → A) := fun_like.has_coe_to_fun
--⟨λ T, T.to_fun⟩

end centroid

--instance : has_coe_to_fun (centroid A) (λ _, A → A) :=
--⟨centroid.to_fun⟩

@[ext]
lemma centroid.ext ⦃T S : centroid A⦄ (h : ∀ (a : A), T a = S a) : T = S :=
fun_like.ext _ _ h



--fun_like.ext _ _ h

-- This is essentially the same as algebra.group.
instance : semiring (centroid A) := {
  add := (+),
  --add_assoc := by intros; ext; apply add_assoc,
  --zero_add := by intros; ext; apply zero_add,
  --add_zero := by intros; ext; apply add_zero,
  zero := (0),
  one := (1),
  mul := (*),
  ..add_monoid_hom.add_comm_monoid,
}

/-
instance : has_neg (centroid A) := {
  neg := λ T, {
    lmul_comm := sorry,
    rmul_comm := sorry,
    ..(-T.to_add_monoid_hom)
  }
}
-/
