import algebra.ring.basic
import algebra.group.hom

variable {A : Type*}
variable {F : Type*}

variable [non_unital_non_assoc_semiring A]

@[ancestor add_monoid_hom]
structure centroid (A : Type*) [non_unital_non_assoc_semiring A] extends A →+ A :=
(lmul_comm': ∀ a b, to_add_monoid_hom (a*b) = a * (to_add_monoid_hom b))
(rmul_comm': ∀ a b, to_add_monoid_hom (a*b) = (to_add_monoid_hom a) * b)


attribute [nolint doc_blame] centroid.to_add_monoid_hom

@[ancestor add_monoid_hom_class]
class centroid_class (F : Type*) (A : out_param $ Type*) [non_unital_non_assoc_semiring A]
  extends add_monoid_hom_class F A A :=
(lmul_comm: ∀ (f : F) (a b : A), f (a*b) = a * (f b))
(rmul_comm: ∀ (f : F) (a b : A), f (a*b) = (f a) * b)

instance centroid.add_monoid_hom_class : add_monoid_hom_class (centroid A) A A :=
{ coe := λ c a, c.to_add_monoid_hom a,
  coe_injective' := λ f g h,
  begin
    cases f,
    cases g,
    congr',
    exact fun_like.ext f__to_add_monoid_hom g__to_add_monoid_hom (congr_fun h),
  end,
  map_add := λ f _ _, f.to_add_monoid_hom.map_add _ _,
  map_zero := λ f, f.to_add_monoid_hom.map_zero, }

-- c.f. https://github.com/leanprover-community/mathlib/blob/5d405e2a7028f87e962e7cc2133dc0cfc9c55f7d/src/algebra/group/hom.lean#L276
instance centroid.centroid_class : centroid_class (centroid A) A :=
{ lmul_comm := λ f a b, by apply f.lmul_comm',
  rmul_comm := λ f a b, by apply f.rmul_comm', }

instance centroid.has_coe_to_add_monoid_hom  : has_coe (centroid A) (A →+ A) := ⟨centroid.to_add_monoid_hom⟩

instance : has_add (centroid A) := {
  add := λ T S, {
    lmul_comm' := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.add_apply, centroid.lmul_comm', left_distrib],

    rmul_comm' := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.add_apply, centroid.rmul_comm', right_distrib],
    ..T.to_add_monoid_hom  + S.to_add_monoid_hom,
  }
}

instance : has_zero (centroid A) := {
  zero := {
    lmul_comm' := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.zero_apply, mul_zero],
    rmul_comm' := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.zero_apply, zero_mul],
    ..(0 : A →+ A)
  }
}

instance : has_one (centroid A) := {
  one := {
    lmul_comm' := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.id_apply],
    rmul_comm' := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.mk_coe,
      add_monoid_hom.id_apply],
    ..add_monoid_hom.id A,
  }
}

instance : has_mul (centroid A) := {
  mul := λ T S, {
    lmul_comm' := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.coe_comp, add_monoid_hom.coe_mk,
        function.comp_app, centroid.lmul_comm'],
    rmul_comm' := λ _ _, by simp only [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.coe_comp, add_monoid_hom.coe_mk,
        function.comp_app, centroid.rmul_comm'],
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

@[simp] lemma centroid.comp_id (f : centroid A) : f * 1 = f := centroid.ext $ λ x, rfl

@[simp] lemma centroid.id_comp (f : centroid A) : 1 * f = f := centroid.ext $ λ x, rfl

lemma centroid.comp_assoc
  (f : centroid A) (g : centroid A) (h : centroid A) :
  (h*g)* f = h * (g * f) := rfl

-- This is essentially the same as algebra.group.hom_instances

instance : semiring (centroid A) := {
  add := (+),
  add_assoc := by intros; ext; apply add_assoc,
  zero_add := by intros; ext; apply zero_add,
  add_zero := by intros; ext; apply add_zero,
  add_comm := by intros; ext; apply add_comm,
  left_distrib :=  λ x y z, centroid.ext $ λ i, add_monoid_hom.map_add _ _ _,
  right_distrib := λ x y z, centroid.ext $ λ i, rfl,
  zero := (0),
  one := (1),
  mul := (*),
  zero_mul := λ x, centroid.ext $ λ i, rfl,
  mul_zero := λ x, centroid.ext $ λ i, add_monoid_hom.map_zero _,
  one_mul := centroid.comp_id,
  mul_one := centroid.id_comp,
  mul_assoc :=  λ _ _ _, centroid.comp_assoc _ _ _,
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
