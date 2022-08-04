import analysis.convex.cone

noncomputable theory

structure proper_cone (E : Type*) [inner_product_space ℝ E] [complete_space E]:=
(carrier : convex_cone ℝ E)
(nonempty' : (carrier : set E).nonempty)
(is_closed' : is_closed (carrier : set E))

namespace proper_cone

variables {E : Type*} [inner_product_space ℝ E] [complete_space E]

instance : has_coe (proper_cone E) (convex_cone ℝ E) := ⟨proper_cone.carrier⟩

instance : has_coe (proper_cone E) (set E) := ⟨λ K, K.carrier⟩

instance : has_mem E (proper_cone E) := ⟨λ m S, m ∈ S.carrier⟩

lemma mem_cone (K : proper_cone E) {x : E} : x ∈ K ↔ x ∈ K.carrier := sorry

@[simp, norm_cast] lemma mem_coe (K : proper_cone E) {x : E} : x ∈ (K : set E) ↔ x ∈ K := iff.rfl

lemma nonempty (K : proper_cone E) : (K.carrier : set E).nonempty := K.nonempty'

lemma is_closed (K : proper_cone E) : is_closed (K.carrier : set E) := K.is_closed'

@[ext] theorem ext {S T : proper_cone E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := sorry

instance : has_star (proper_cone E) := ⟨ λ K,
  ⟨ (K.carrier : set E).inner_dual_cone,
    set.nonempty_of_mem (pointed_inner_dual_cone (K.carrier : set E)),
    inner_dual_cone_closed (K.carrier : set E) ⟩ ⟩

@[simp] lemma mem_star (x : E) (K : proper_cone E) : x ∈ star K ↔ x ∈ (K.carrier : set E).inner_dual_cone := by sorry

lemma star_coe (K : proper_cone E) : (star K).carrier = (K.carrier : set E).inner_dual_cone := sorry

instance : has_involutive_star (proper_cone E) :=
{ star := has_star.star,
  star_involutive := λ K, proper_cone.ext $ λ x,
    by rw [mem_star, star_coe, dual_of_dual_eq_self K.nonempty K.is_closed, mem_cone] }

end proper_cone

-- def convex_cone.cone_le (K : convex_cone ℝ E) (x y : E) := ∃ k : K, x + k = y

-- def cone_preorder (K : closed_convex_cone E) : preorder E :=
-- { le := λ x y, ∃ k : K.carrier, x + k = y,
--   lt := λ x y, x ≠ y ∧ ∃ k : K.carrier, x + k = y ,
--   le_refl := λ x,
--   begin
--   have := pointed_of_nonempty_closed K.ne K.cl,
--   unfold convex_cone.pointed at this,
--   end,
--   le_trans := _,
--   lt_iff_le_not_le := _ }


namespace dual_conic_program
/-- A dual conic program for decision variables `x` is a system of inequalities
`constraints_i x ≤K bounds_i` for all `i ∈ I` where `x ≤K y` means there exists a `k ∈ K` such that
` x + k = y`. -/
structure dual_conic_program (H H' : Type*) [inner_product_space ℝ H] [inner_product_space ℝ H'] [complete_space H] [complete_space H']:=
(K : proper_cone H')
(obj : H →L[ℝ] ℝ)
(I : Type*)
(constraints: I → H →L[ℝ] H')
(bounds: I → H')

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] [complete_space E] [complete_space F]

def is_feasible (p : dual_conic_program E F) := { x : E | ∀ i, ∃ k : p.K.carrier, p.constraints i x + k = p.bounds i }

def obj_value (p : dual_conic_program E F) (x : E) := p.obj x

def is_optimal (p : dual_conic_program E F) (x : E) := is_feasible p x ∧ ∀ y, is_feasible p y → obj_value p y ≤ obj_value p x

end dual_conic_program
