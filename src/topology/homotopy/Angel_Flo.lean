import analysis.complex.circle
import topology.metric_space.basic
import topology.homotopy.path
import data.real.basic
import topology.algebra.polynomial
import topology.continuous_function.algebra
import topology.continuous_function.compact
import analysis.inner_product_space.pi_L2

universe u

noncomputable theory

open_locale unit_interval

namespace H_space

class H_space (G : Type u) [topological_space G] :=
--(m : G → G → G)
(m : G × G → G)
(e : G)
--(m_e_e : m e e = e)
(m_e_e : m(e,e) = e)
-- m is continuous
(cont_m : continuous m) -- this is a term of type continuous m
(m_e_dot_homotopic_to_id :
  continuous_map.homotopy_rel
  ⟨(λ g : G, m (e, g)), (continuous.comp cont_m (continuous.prod_mk continuous_const continuous_id'))⟩
  --⟨(λ g : G, g), continuous_id'⟩
  ⟨id, continuous_id'⟩
  {e})
(m_dot_e_homotopic_to_id :
  continuous_map.homotopy_rel
  ⟨(λ g : G, m(g, e)), (continuous.comp cont_m (continuous.prod_mk continuous_id' continuous_const))⟩
  ⟨id, continuous_id'⟩
  {e})

instance top_group_is_H_space (G : Type u) [topological_space G][group G] [topological_group G]
  : H_space G :=
{
  m := function.uncurry (*) ,
  e := 1,
  m_e_e := by {simp only [function.uncurry_apply_pair, mul_one]},
  cont_m := has_continuous_mul.continuous_mul,
  m_e_dot_homotopic_to_id := by {
    simp only [function.uncurry_apply_pair, one_mul],
    exact continuous_map.homotopy_rel.refl ⟨id, continuous_id'⟩  {1},
  },
  m_dot_e_homotopic_to_id := by {simp only [function.uncurry_apply_pair, mul_one],
    exact continuous_map.homotopy_rel.refl _ _}
}

example : H_space circle := infer_instance

/-
Next, give an example of an H-space (ℝ,z,m) where m(x,y)=(x+y)/2 and z is arbitrary in ℝ. The point is to show that, in the definition of an H-space, the neutral element up to homotopy e is not unique in general.

lemma [Given m as above] ∀ z : (ℝ,z,m) is an H-space.

Proof:

m(z,z) = (z+z)/2 = (2*z)/2 = z

(ℝ,+) is a topological group, from which we should obtain that m(x,y)=(x+y)/2 is continuous.

m(x,z) = (x+z)/2 = (z+x)/2 = m(z,x) and this map is homotopic to id_X via
H(t,x) = (1-t) * (x+z)/2 + t * x
-/


def H (z : ℝ) : I × ℝ → ℝ := λ p, (1 - p.1) * (p.2 + z)/2 + p.1 * p.2
lemma cont_H (z : ℝ) : continuous (H z) :=
begin
  dsimp [H],

  -- Handy trick continuity?,
  exact ((continuous_const.sub (continuous_induced_dom.comp continuous_fst)).mul
   (continuous_snd.add continuous_const)).div_const.add
  ((continuous_induced_dom.comp continuous_fst).mul continuous_snd),
end

def H' (z: ℝ) : C(I × ℝ, ℝ) := ⟨H(z), cont_H(z)⟩

def H_space_R_with_z (z : ℝ) : H_space ℝ :=
{ m := λ x, (x.1 + x.2)/2 ,
  e := z,
  m_e_e := by simp only [half_add_self],
  cont_m := continuous_add.div_const,
  m_e_dot_homotopic_to_id := begin
  use H' z,
  {
    intro x,
    dsimp [H', H],
    ring_nf,
  },
  {
   intro x,
    dsimp [H', H],
    ring_nf,
  },
  { simp only [set.mem_Icc, set.mem_singleton_iff, continuous_map.coe_mk, id.def, set_coe.forall, forall_eq, half_add_self, and_self],
    intros x _,
    dsimp [H', H],
    ring,
  },
  end,
  m_dot_e_homotopic_to_id := begin
  use H' z,
  {
    intro x,
    dsimp [H', H],
    ring_nf,
  },
  {
   intro x,
    dsimp [H', H],
    ring_nf,
  },
  { simp only [set.mem_Icc, set.mem_singleton_iff, continuous_map.coe_mk, id.def, set_coe.forall, forall_eq, half_add_self, and_self],
    intros x _,
    dsimp [H', H],
    ring,
  },
  end
}

class Ω (X : Type u) [topological_space X] (x : X):=
    (loop : ℝ → X)
    (boundary_0 : loop 0 = x)
    (boundary_1 : loop 1 = x)

def my_loop : Ω ℝ 0 :=
{
  loop := λ t, t*(1-t),
  boundary_0 := by ring,
  boundary_1 := by ring
}

def juxt_loop (X : Type u) [topological_space X] (x : X) (α β : Ω X x) : Ω X x:=
{
  loop :=  λ t, if t < 1/2 then (α.loop : ℝ → X) (2*t) else (β.loop : ℝ → X) (2*t-1),
  boundary_0 :=
  begin
    simp only [one_div, inv_pos, zero_lt_bit0, zero_lt_one, mul_zero, if_true],
    exact α.boundary_0,
  end,
  boundary_1 := begin
    simp only [one_div, mul_one],
    split_ifs,
    {
      have eq : ¬ (1 < (2 : ℝ)⁻¹) := begin
        have eq_aux : ¬ ((1:ℝ) < 1/2) := begin
          simp only [not_lt],
          nlinarith,
        end,
        simp only [not_lt],
        rw inv_eq_one_div (2:ℝ),
        apply not_lt.1,
        exact eq_aux,
      end,
      contradiction
    },
    {
      ring_nf,
      exact β.boundary_1,
    },
  end,
}


-- instance loop_space_is_H_space (X : Type u) [topological_space X] (x : X)
--   : H_space (Ω X x) :=
-- {
--   m := sorry,
--   e := sorry,
--   m_e_e := sorry,
--   cont_m := sorry,
--   m_e_dot_homotopic_to_id  := sorry,
--   m_dot_e_homotopic_to_id := sorry,
-- }

/-
  Next, show that the sphere S^3 has a canonical H-space structure.

  We will think of S^3 as the quaternions of norm 1.

  The "usual" quaternions are denoted H[ℝ] in Lean. They form an ℝ-algebra, equipped with a conjugation x → quaternion.conj x and a norm |x|^2 = x * quaternion.conj x.

  This norm is multiplicative, so the elements of norm 1 form a group norm_1_quaternions. The quaternion algebra H[ℝ] should have a topology, and the induced topology on norm_1_quaternions makes it a topological group.

  In particular, the norm 1 quaternions form an H-space.

  There is a theorem in Lean saying that |x|^2 = x_1^2 + x_2^2 + x_3^2 + x_4^2 (coordinates in the canonical basis of H[ℝ]), so the norm one quaternions are identified with S^3.

  If SU(2) is already defined in Lean, it would be nice to also identify S^3 with SU(2), via u + v J → matrix (u & - complex.conj v \\ v & complex.conj u).

  Obs: a similar strategy will apply for S^7 (octonions of norm 1), except that the octonions of norm 1 do not form a group (no associativity).
-/


--def R4 := euclidean_space ℝ (fin 4)

--#check metric.sphere R4 1

--example : H_space S^3 :=

end H_space
