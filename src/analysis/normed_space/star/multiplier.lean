import analysis.normed_space.star.basic
import analysis.normed_space.operator_norm
import data.real.sqrt
import data.real.nnreal
import analysis.special_functions.pow

/-!
# Multiplier Algebra of a C⋆-algebra

Define the multiplier algebra of a C⋆-algebra as the algebra (over `𝕜`) of double centralizers,
for which we provide the localized notation `𝓜(𝕜, A)`.  A double centralizer is a pair of
continuous linear maps `L R : A →L[𝕜] A` satisfying the intertwining condition `R x * y = x * L y`.

There is a natural embedding `A → 𝓜(𝕜, A)` which sends `a : A` to the continuous linear maps
`L R : A →L[𝕜] A` given by left and right multiplication by `a`, and we provide this map as a
coercion.

The multiplier algebra corresponds to a non-commutative Stone–Čech compactification in the sense
that when the algebra `A` is commutative, it can be identified with `C₀(X, ℂ)` for some locally
compact Hausdorff space `X`, and in that case `𝓜(𝕜, A)` can be identified with `C(β X, ℂ)`.

## Implementation notes

## TODO

+ show that `𝓜(𝕜, A)` is a C⋆-ring
+ define a type synonym for `𝓜(𝕜, A)` which is equipped with the strict topology
+ after ⋆-algebra morphisms are implemented in mathlib, bundle the coercion `A → 𝓜(𝕜, A)`
+ show that the image of `A` in `𝓜(𝕜, A)` is an essential ideal
+ prove the universal property of `𝓜(𝕜, A)`
* Construct a double centralizer from a pair of maps `L : A → A`, `R : A → A` satisfying the
  centrality condition `∀ x y, R x * y = x * L y`.
-/

noncomputable theory

open_locale nnreal ennreal
open nnreal continuous_linear_map

universes u v

variables (𝕜 : Type u) (A : Type v)
  [nontrivially_normed_field 𝕜]
  [non_unital_normed_ring A]
  [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A]

section prereqs

-- this should go in `analysis.normed_space.star_basic`
lemma _root_.cstar_ring.nnnorm_self_mul_star {E : Type*} [non_unital_normed_ring E] [star_ring E]
  [cstar_ring E] {x : E} : ∥x * star x∥₊ = ∥x∥₊ * ∥x∥₊ :=
by simpa using @cstar_ring.nnnorm_star_mul_self _ _ _ _ (star x)

end prereqs

/-- The type of *double centralizers*, also known as the *multiplier algebra* and denoted by
`𝓜(𝕜, A)`, of a non-unital normed algebra. -/
@[ext]
structure double_centralizer : Type v :=
(left : A →L[𝕜] A)
(right : A →L[𝕜] A)
(central : ∀ x y : A, right x * y = x * left y)

localized "notation `𝓜(` 𝕜 `, ` A `)` := double_centralizer 𝕜 A" in multiplier_algebra

instance : inhabited 𝓜(𝕜, A) :=
{ default := ⟨1, 1, by simp only [one_apply, eq_self_iff_true, forall_const]⟩ }

/-!
### Normed space structure

Because the multiplier algebra is defined as the algebra of double centralizers, there is a natural
map `double_centralizer.prod_mk := λ a, (a.left, a.right) : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)`.
We use this map to pull back the normed space structure from `(A →L[𝕜] A) × (A →L[𝕜] A)` to
`𝓜(𝕜, A)`, which provides a definitional isometric embedding. Consequently, completeness of
`𝓜(𝕜, A)` is obtained by proving that the range of this map is closed.
-/

namespace double_centralizer

/-- the canonical map of `𝓜(𝕜, A)` into `(A →L[𝕜] A) × (A →L[𝕜] A)`. -/
@[simp] def prod_mk (a : 𝓜(𝕜, A)) : (A →L[𝕜] A) × (A →L[𝕜] A) := (a.left, a.right)

variables {𝕜 A}

lemma injective_prod_mk : function.injective (prod_mk 𝕜 A) :=
λ a b h, ext a b (prod.ext_iff.mp h).1 (prod.ext_iff.mp h).2

lemma range_prod_mk : set.range (prod_mk 𝕜 A) = {lr | ∀ x y, lr.2 x * y = x * lr.1 y} :=
set.ext $ λ x, ⟨by {rintro ⟨a, rfl⟩, exact a.central}, λ hx, ⟨⟨x.1, x.2, hx⟩, by simp⟩⟩

instance : has_add 𝓜(𝕜, A) :=
{ add := λ a b,
  { left := a.left + b.left,
    right := a.right + b.right,
    central := λ x y, by simp only [continuous_linear_map.add_apply, add_mul, mul_add, central] } }

instance : has_zero 𝓜(𝕜, A) :=
{ zero :=
  { left := 0,
    right := 0,
    central := λ x y, by simp only [continuous_linear_map.zero_apply, zero_mul, mul_zero] } }

instance : has_neg 𝓜(𝕜, A) :=
{ neg := λ a,
  { left := -(a.left),
    right := -(a.right),
    central := λ x y, by simp only [continuous_linear_map.neg_apply, neg_mul,
                      mul_neg, neg_inj, central]}}

instance : has_sub 𝓜(𝕜, A) :=
{ sub := λ a b,
  { left := a.left - b.left,
    right := a.right - b.right,
    central := λ x y, by simp only [continuous_linear_map.coe_sub', pi.sub_apply, sub_mul,
      mul_sub, central] } }

section scalars

variables {S : Type*} [monoid S] [distrib_mul_action S A] [smul_comm_class 𝕜 S A]
  [has_continuous_const_smul S A] [is_scalar_tower S A A] [smul_comm_class S A A]

instance : has_smul S 𝓜(𝕜, A) :=
{ smul := λ s a,
  { left := s • a.left,
    right := s • a.right,
    central := λ x y, by simp only [continuous_linear_map.coe_smul', pi.smul_apply, mul_smul_comm,
      smul_mul_assoc, central] } }

@[simp] lemma smul_left (k : 𝕜) (a : 𝓜(𝕜, A)) : (k • a).left = k • a.left := rfl
@[simp] lemma smul_right (k : 𝕜) (a : 𝓜(𝕜, A)) : (k • a).right = k • a.right := rfl

end scalars

@[simp] lemma add_left (a b : 𝓜(𝕜, A)) : (a + b).left = a.left + b.left := rfl
@[simp] lemma add_right (a b : 𝓜(𝕜, A)) : (a + b).right = a.right + b.right := rfl
@[simp] lemma zero_left : (0 : 𝓜(𝕜, A)).left = 0 := rfl
@[simp] lemma zero_right : (0 : 𝓜(𝕜, A)).right = 0 := rfl
@[simp] lemma neg_left (a : 𝓜(𝕜, A)) : (-a).left = -a.left := rfl
@[simp] lemma neg_right (a : 𝓜(𝕜, A)) : (-a).right = -a.right := rfl
@[simp] lemma sub_left (a b : 𝓜(𝕜, A)) : (a - b).left = a.left - b.left := rfl
@[simp] lemma sub_right (a b : 𝓜(𝕜, A)) : (a - b).right = a.right - b.right := rfl

/-- The module structure is inherited as the pullback under the injective map
`double_centralizer.prod_mk : 𝓜(𝕜, A) → (A →L[𝕜] A) × (A →L[𝕜] A)` -/
instance : add_comm_group 𝓜(𝕜, A) :=
function.injective.add_comm_group (prod_mk 𝕜 A) injective_prod_mk rfl (λ x y, rfl) (λ x, rfl)
  (λ x y, rfl) (λ x n, rfl) (λ x n, rfl)

/-- The canonical map `double_centralizer.prod_mk` as an additive group homomorphism. -/
def add_group_hom_prod_mk : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A) :=
{ to_fun := prod_mk 𝕜 A,
  map_zero' := rfl,
  map_add' := λ x y, rfl }

/-- The module structure is inherited as the pullback under the additive group monomoprhism
`double_centralizer.prod_mk : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)` -/
instance : module 𝕜 𝓜(𝕜, A) :=
function.injective.module 𝕜 add_group_hom_prod_mk injective_prod_mk (λ x y, rfl)

/-- The normed group structure is inherited as the pullback under the additive group monomoprhism
`double_centralizer.prod_mk : 𝓜(𝕜, A) →+ (A →L[𝕜] A) × (A →L[𝕜] A)` -/
instance : normed_add_comm_group 𝓜(𝕜, A) :=
normed_add_comm_group.induced add_group_hom_prod_mk injective_prod_mk

@[simp] lemma norm_eq (a : 𝓜(𝕜, A)) : ∥a∥ = max (∥a.left∥) (∥a.right∥) := rfl

instance : normed_space 𝕜 𝓜(𝕜, A) :=
{ norm_smul_le := λ k a, show max (∥k • a.left∥) (∥k • a.right∥) ≤ ∥k∥ * max (∥a.left∥) (∥a.right∥),
    by simp only [mul_max_of_nonneg _ _ (norm_nonneg k), norm_smul],
  .. double_centralizer.module }

lemma uniform_embedding_prod_mk : uniform_embedding (prod_mk 𝕜 A) :=
uniform_embedding_comap injective_prod_mk

instance [complete_space A] : complete_space 𝓜(𝕜, A) :=
begin
  rw complete_space_iff_is_complete_range uniform_embedding_prod_mk.to_uniform_inducing,
  apply is_closed.is_complete,
  simp only [range_prod_mk, set.set_of_forall],
  refine is_closed_Inter (λ x, is_closed_Inter $ λ y, is_closed_eq _ _),
  { exact ((continuous_mul_right y).comp (continuous_linear_map.apply 𝕜 A x).continuous).comp
      continuous_snd },
  { exact ((continuous_mul_left x).comp (continuous_linear_map.apply 𝕜 A y).continuous).comp
      continuous_fst }
end

/-!
### Multiplicative structure
-/

instance : ring 𝓜(𝕜, A) :=
{ one := ⟨1, 1, λ x y, rfl⟩,
  mul := λ x y,
  { left := x.left.comp y.left,
    right := y.right.comp x.right,
    central := λ x y, by simp only [continuous_linear_map.coe_comp', function.comp_app, central] },
  mul_assoc := λ a b c, ext _ _ (mul_assoc _ _ _) (mul_assoc _ _ _),
  one_mul := λ a, ext _ _ (one_mul _) (one_mul _),
  mul_one := λ a, ext _ _ (mul_one _) (mul_one _),
  left_distrib := λ a b c, ext _ _ (mul_add _ _ _) (add_mul _ _ _),
  right_distrib := λ a b c, ext _ _ (add_mul _ _ _) (mul_add _ _ _),
  nat_cast := λ n, ⟨n, n, λ x y,
    by simp only [←nat.smul_one_eq_coe, smul_apply n 1, one_apply, mul_smul_comm, smul_mul_assoc]⟩,
  int_cast := λ n, ⟨n, n, λ x y,
    by simp only [←int.smul_one_eq_coe, smul_apply n 1, one_apply, mul_smul_comm, smul_mul_assoc]⟩,
  npow := λ n a, ⟨a.left ^ n, a.right ^ n, λ x y,
  begin
    induction n with k hk generalizing x y,
    refl,
    rw [pow_succ, mul_apply, a.central, hk, pow_succ', mul_apply],
  end⟩,
  npow_succ' := λ n a, nat.rec_on n (ext _ _ rfl rfl) (λ k hk, ext _ _
    (by { change _ = a.left * _, simp only [congr_arg left hk, pow_succ] })
    (by { change _ = _ * a.right, simp only [congr_arg right hk, pow_succ'] })),
  .. double_centralizer.add_comm_group }

@[simp] lemma one_left : (1 : 𝓜(𝕜, A)).left = 1 := rfl
@[simp] lemma one_right : (1 : 𝓜(𝕜, A)).right = 1 := rfl
@[simp] lemma mul_left (a b : 𝓜(𝕜, A)) : (a * b).left = a.left * b.left := rfl
@[simp] lemma mul_right (a b : 𝓜(𝕜, A)) : (a * b).right = b.right * a.right := rfl
@[simp] lemma nat_cast_left (n : ℕ) : (n : 𝓜(𝕜 , A)).left = n := rfl
@[simp] lemma nat_cast_right (n : ℕ) : (n : 𝓜(𝕜 , A)).right = n := rfl
@[simp] lemma int_cast_left (n : ℤ) : (n : 𝓜(𝕜 , A)).left = n := rfl
@[simp] lemma int_cast_right (n : ℤ) : (n : 𝓜(𝕜 , A)).right = n := rfl
@[simp] lemma pow_left (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).left = a.left ^ n := rfl
@[simp] lemma pow_right (n : ℕ) (a : 𝓜(𝕜, A)) : (a ^ n).right = a.right ^ n := rfl

/-!
### Coercion from an algebra into its multiplier algebra
-/

noncomputable instance : has_coe_t A 𝓜(𝕜, A) :=
{ coe := λ a,
  { left := continuous_linear_map.lmul 𝕜 A a,
    right := continuous_linear_map.lmul_right 𝕜 A a,
    central := λ x y, mul_assoc _ _ _ } }

@[simp, norm_cast]
lemma coe_left (a : A) : (a : 𝓜(𝕜, A)).left = continuous_linear_map.lmul 𝕜 A a := rfl
@[simp, norm_cast]
lemma coe_right (a : A) : (a : 𝓜(𝕜, A)).right = continuous_linear_map.lmul_right 𝕜 A a := rfl

-- TODO: make this into a `non_unital_star_alg_hom` once we have those
/-- The coercion of an algebra into its multiplier algebra as a non-unital algebra homomorphism. -/
def non_unital_algebra_hom_coe : A →ₙₐ[𝕜] 𝓜(𝕜, A) :=
{ to_fun := λ a, a,
  map_smul' := λ k a, by {ext1; simp only [coe_left, coe_right, continuous_linear_map.map_smul,
    smul_left, smul_right]},
  map_zero' := by {ext1; simp only [coe_left, coe_right, map_zero, zero_left, zero_right]},
  map_add' := λ a b, by {ext1; simp only [coe_left, coe_right, map_add, add_left, add_right]},
  map_mul' := λ a b, by {ext; simp only [coe_left, coe_right, continuous_linear_map.lmul_apply,
    continuous_linear_map.lmul_right_apply, mul_left, mul_right, coe_mul, function.comp_app,
    mul_assoc]} }

/-!
### Star structure
-/

section star

variables [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A]

instance : has_star 𝓜(𝕜, A) :=
{ star := λ a,
  { left := (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.right).comp
      ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A),
    right := (((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp a.left).comp
      ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A),
    central := λ x y, by simpa only [star_mul, star_star]
      using (congr_arg star (a.central (star y) (star x))).symm } }

@[simp] lemma star_left (a : 𝓜(𝕜, A)) (b : A) : (star a).left b = star (a.right (star b)) := rfl
@[simp] lemma star_right (a : 𝓜(𝕜, A)) (b : A) : (star a).right b = star (a.left (star b)) := rfl

instance : star_add_monoid 𝓜(𝕜, A) :=
{ star_involutive := λ x, by {ext; simp only [star_left, star_right, star_star]},
  star_add := λ x y, by {ext; simp only [star_left, star_right, add_left, add_right,
    continuous_linear_map.add_apply, star_add]},
  .. double_centralizer.has_star }

instance : star_ring 𝓜(𝕜, A) :=
{ star_mul := λ a b, by {ext; simp only [star_left, star_right, mul_left, mul_right, star_star,
    continuous_linear_map.coe_mul, function.comp_app]},
  .. double_centralizer.star_add_monoid }

instance : star_module 𝕜 𝓜(𝕜, A) :=
{ star_smul := λ k a, by {ext; exact star_smul _ _},
  .. double_centralizer.star_add_monoid }

end star

/-!
### Norm structures
-/

noncomputable instance : normed_ring 𝓜(𝕜, A) :=
{ norm_mul := λ a b,
    begin
      refine max_le ((norm_mul_le _ _).trans _) ((norm_mul_le _ _).trans _),
      exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (norm_nonneg _)
        ((norm_nonneg _).trans $ le_max_left _ _),
      exact mul_comm (∥a.right∥) (∥b.right∥) ▸ mul_le_mul (le_max_right _ _) (le_max_right _ _)
        (norm_nonneg _) ((norm_nonneg _).trans $ le_max_right _ _),
    end,
  .. double_centralizer.ring,
  .. double_centralizer.normed_add_comm_group }

variables [star_ring A] [cstar_ring A]

/-- For `a : 𝓜(𝕜, A)`, the norms of `a.left` and `a.right` coincide, and hence these
also coincide with `∥a∥` which is `max (∥a.left∥) (∥a.right∥)`. -/
lemma norm_left_eq_right (a : 𝓜(𝕜, A)) : ∥a.left∥ = ∥a.right∥ :=
begin
  -- a handy lemma for this proof
  have h0 : ∀ f : A →L[𝕜] A, ∀ C : ℝ≥0, (∀ b : A, ∥f b∥₊ ^ 2 ≤ C * ∥f b∥₊ * ∥b∥₊) → ∥f∥₊ ≤ C,
  { intros f C h,
    have h1 : ∀ b, C * ∥f b∥₊ * ∥b∥₊ ≤ C * ∥f∥₊ * ∥b∥₊ ^ 2,
    { intros b,
      convert mul_le_mul_right' (mul_le_mul_left' (f.le_op_nnnorm b) C) (∥b∥₊) using 1,
      ring, },
    have := div_le_of_le_mul (f.op_nnnorm_le_bound _ (by simpa only [sqrt_sq, sqrt_mul]
      using (λ b, sqrt_le_sqrt_iff.mpr ((h b).trans (h1 b))))),
    convert rpow_le_rpow this (by exact_mod_cast zero_le (2 : ℕ) : 0 ≤ (2 : ℝ)),
    { simp only [rpow_two, div_pow, sq_sqrt], simp only [sq, mul_self_div_self] },
    { simp only [rpow_two, sq_sqrt] } },
  have h1 : ∀ b, ∥ a.left b ∥₊ ^ 2 ≤  ∥ a.right ∥₊ * ∥ a.left b ∥₊ * ∥ b ∥₊,
  { intros b,
    calc ∥ a.left b ∥₊ ^ 2
        = ∥ star (a.left b) * (a.left b) ∥₊
        : by simpa only [←sq] using (cstar_ring.nnnorm_star_mul_self).symm
    ... ≤ ∥ a.right (star (a.left b))∥₊ * ∥ b ∥₊ : a.central (star (a.left b)) b ▸ nnnorm_mul_le _ _
    ... ≤ ∥ a.right ∥₊ * ∥ a.left b ∥₊ * ∥ b ∥₊
        : nnnorm_star (a.left b) ▸ mul_le_mul_right' (a.right.le_op_nnnorm _) _},
  have h2 : ∀ b, ∥ a.right b ∥₊ ^ 2 ≤  ∥ a.left ∥₊ * ∥ a.right b ∥₊ * ∥ b ∥₊,
  { intros b,
    calc ∥ a.right b ∥₊ ^ 2
        = ∥ a.right b * star (a.right b) ∥₊
        : by simpa only [←sq] using (cstar_ring.nnnorm_self_mul_star).symm
    ... ≤ ∥ b ∥₊ * ∥ a.left (star (a.right b))∥₊
        : (a.central b (star (a.right b))).symm ▸ nnnorm_mul_le _ _
    ... = ∥ a.left (star (a.right b))∥₊ * ∥b∥₊ : mul_comm _ _
    ... ≤ ∥ a.left ∥₊ * ∥ a.right b ∥₊ * ∥ b ∥₊
        : nnnorm_star (a.right b) ▸ mul_le_mul_right' (a.left.le_op_nnnorm _) _  },
  exact le_antisymm (h0 _ _ h1) (h0 _ _ h2),
end

lemma norm_left (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.left∥ :=
by simp only [norm_eq, norm_left_eq_right, max_eq_right, eq_self_iff_true]
lemma norm_right (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.right∥ := by rw [norm_left, norm_left_eq_right]

-- it would be nice if maybe we could get this for `ℝ≥0` instead, but we go to `ℝ≥0∞` because it
-- is a complete lattice and therefore `supr` is well-behaved.
lemma key_lemma {𝕜 E : Type*} [densely_normed_field 𝕜] [non_unital_normed_ring E] [star_ring E]
  [cstar_ring E] [normed_space 𝕜 E] [is_scalar_tower 𝕜 E E] (a : E) :
  (∥a∥₊ : ℝ≥0∞) = ⨆ b (hb : ∥b∥₊ ≤ 1), ∥b * a∥₊ :=
begin
  refine le_antisymm _ (supr₂_le (λ b hb, _)),
  { by_cases h : ∥a∥₊ = 0,
    { rw h, exact_mod_cast zero_le _ },
    { refine ennreal.le_of_forall_pos_le_add (λ ε hε h_lt, _),
      rw ennreal.bsupr_add' (⟨0, by simp only [nnnorm_zero, zero_le']⟩ : ∃ x : E, ∥x∥₊ ≤ 1),
      /- choose some `k : 𝕜` such that `(1 + ε * ∥a∥₊⁻¹) * ∥a∥₊⁻¹ < ∥k'∥₊ < ∥a∥₊⁻¹`. -/
      have : (1 - ε * ∥a∥₊⁻¹) * ∥a∥₊⁻¹ < ∥a∥₊⁻¹,
      { have a_pos := nnreal.inv_pos.mpr (zero_lt_iff.mpr h),
        simpa only [one_mul] using (mul_lt_mul_right a_pos).mpr
          (tsub_lt_self_iff.mpr ⟨zero_lt_one, mul_pos hε a_pos⟩) },
      obtain ⟨k, hk₁, hk₂⟩ := normed_field.exists_lt_nnnorm_lt 𝕜 this,
      refine le_trans _ (le_supr₂ (k • (star a)) _),
      { norm_cast,
        simp only [smul_mul_assoc, nnnorm_smul, cstar_ring.nnnorm_star_mul_self],
        convert mul_le_mul_right'
          (le_tsub_add.trans (add_le_add_right ((mul_inv_le_iff₀ h).mp hk₁.le) _)) (∥a∥₊),
        exact (one_mul _).symm,
        rw [add_mul, inv_mul_cancel_right₀ h _, mul_assoc] },
      { simpa only [nnnorm_smul, nnnorm_star] using ((nnreal.lt_inv_iff_mul_lt h).mp hk₂).le, } } },
  { calc (∥b * a∥₊ : ℝ≥0∞) ≤ ∥b∥₊ * ∥a∥₊ : by exact_mod_cast norm_mul_le _ _
    ...                    ≤ ∥a∥₊ : by simpa using (ennreal.coe_mono $ mul_le_mul_right' hb _) }
end

instance [star_ring 𝕜] [star_module 𝕜 A] [normed_star_group A] : cstar_ring 𝓜(𝕜, A) :=
{ norm_star_mul_self := sorry }

end double_centralizer

lemma op_norm_eq_sup_unit_ball {𝕜 E F: Type*} [normed_add_comm_group E]
  [normed_add_comm_group F] [densely_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]
  (f : E →L[𝕜] F) :  ∥f∥₊ = Sup {(∥f x∥₊) | (x : E) (hx : ∥ x ∥₊ ≤ 1)} :=
begin
have hf : ∥f∥₊ ∈ upper_bounds {(∥f x∥₊) | (x : E) (hx : ∥ x ∥₊ ≤ 1)},
{ rintro _ ⟨x, hx, rfl⟩,
  exact mul_one (∥f∥₊) ▸ (f.le_op_nnnorm x).trans (mul_le_mul_left' hx (∥f∥₊)) },
rw← cInf_upper_bounds_eq_cSup _ _,
{ refine le_antisymm _ (cInf_le (order_bot.bdd_below _) hf),
 { refine le_cInf ⟨∥f∥₊, hf⟩ (λ u hu, _),
   have P := λ (y : E) (δ : ℝ) (hδ : 0 < δ), normed_field.exists_lt_norm_lt 𝕜
   (nnreal.coe_nonneg ∥ y ∥₊) (lt_add_of_pos_right (∥ y ∥₊ : ℝ) (hδ)),
   by_contra, push_neg at h,
   rw upper_bounds at *,
   simp only [coe_nnnorm, set.mem_set_of_eq, forall_exists_index, forall_apply_eq_imp_iff₂] at *,
   unfold nnnorm at *,
   simp only [subtype.mk_le_mk] at *,
   have Q : ∀ (x : E)(δ : ℝ≥0), (0 < δ) → ∥ f x ∥₊ ≤ ∥ x ∥₊ * u + δ * u,
        begin
        intros x δ hδ,
        cases P x δ (nnreal.coe_pos.mp hδ),
        have Q1 : ∥w⁻¹ • x∥ ≤ 1,
          { by_cases w=0, rw h, simp only [zero_smul, zero_le_one, inv_zero, norm_zero],
            rw [norm_smul, norm_inv, ←mul_le_mul_left (norm_pos_iff.mpr h), mul_one, ←mul_assoc],
            simp only [h, mul_inv_cancel, ne.def, norm_eq_zero, not_false_iff, one_mul,
            le_of_lt (h_1.left)]},
        have Q2 : ∥ f x ∥ ≤ ∥ w ∥ * u,
          { have A := h_1.left,
            by_cases w=0, rw h at A, rw norm_zero at A, linarith [norm_nonneg x],
            have R : ∥f (w⁻¹ • x)∥ ≤ (u : ℝ), by exact_mod_cast (hu (w⁻¹ • x) Q1),
            simp only [norm_smul, continuous_linear_map.map_smul, norm_inv] at R,
            rw [←mul_le_mul_left (norm_pos_iff.mpr h), ←mul_assoc] at R,
            simp only [mul_inv_cancel (norm_ne_zero_iff.mpr h), one_mul] at R,
            exact R},
        by_cases u=0, simp only [h, mul_zero, add_zero, le_zero_iff, nnnorm_eq_zero],
        simp only [h, nonneg.coe_zero, mul_zero, norm_le_zero_iff] at Q2, exact Q2,
        have B:= (mul_le_mul_of_nonneg_right (le_of_lt (h_1.right))
        (le_of_lt (pos_iff_ne_zero.mpr h))),
        rw ←add_mul,
        exact_mod_cast (le_trans Q2 B),
        end,
   have H : ∀ (x : E), ∥f x∥ ≤ ∥x∥ * u,
        begin
        intro x,
        apply le_iff_forall_pos_le_add.mpr,
        intros ε hε,
        have C := Q x ((real.to_nnreal ε) * u⁻¹),--need zero case removed.
        rw [mul_assoc, inv_mul_cancel, mul_one] at C,
        have G : 0 < ε.to_nnreal * u⁻¹, by sorry,
        have := C G,
        unfold nnnorm at *,
        unfold real.to_nnreal at *,
        unfold max at this,
        rw real.to_nnreal_of_nonneg (∥ f x ∥) (norm_nonneg (f x)),
        end,
   },},
{ exact ⟨∥f∥₊, hf⟩,},
{ exact ⟨0, 0, nnnorm_zero.trans_le zero_le_one, (map_zero f).symm ▸ nnnorm_zero⟩, },
end
