import analysis.normed_space.dual
import analysis.normed_space.star.basic
import analysis.complex.basic
import analysis.inner_product_space.adjoint

/-!
# Von Neumann algebras

We give the "abstract" and "concrete" definitions of a von Neumann algebra.
We still have a major project ahead of us to show the equivalence between these definitions!

An abstract von Neumann algebra `wstar_algebra M` is a C^* algebra with a Banach space predual,
per Sakai (1971).

A concrete von Neumann algebra `von_neumann_algebra H` (where `H` is a Hilbert space)
is a *-closed subalgebra of bounded operators on `H` which is equal to its double commutant.

We'll also need to prove the von Neumann double commutant theorem,
that the concrete definition is equivalent to a *-closed subalgebra which is weakly closed.
-/

universes u v

/--
Sakai's definition of a von Neumann algebra as a C^* algebra with a Banach space predual.

So that we can unambiguously talk about these "abstract" von Neumann algebras
in parallel with the "concrete" ones (weakly closed *-subalgebras of B(H)),
we name this definition `wstar_algebra`.
-/
class wstar_algebra (M : Type u) [normed_ring M] [star_ring M] [cstar_ring M]
  [module ℂ M] [normed_algebra ℂ M] [star_module ℂ M] :=
(exists_predual : ∃ (X : Type u) [normed_group X] [normed_space ℂ X] [complete_space X],
  nonempty (normed_space.dual ℂ X ≃ₗᵢ⋆[ℂ] M))

open_locale inner_product

/-- The commutant of a subsemiring. -/
def subsemiring.commutant {A : Type u} [semiring A] (B : subsemiring A) : subsemiring A :=
{ carrier := { x : A | ∀ y ∈ B, x * y = y * x },
  zero_mem' := by tidy,
  one_mem' := by tidy,
  mul_mem' := λ a b ha hb c mc, by rw [mul_assoc, hb _ mc, ←mul_assoc, ha _ mc, mul_assoc],
  add_mem' := λ a b ha hb c mc, by rw [add_mul, mul_add, ha _ mc, hb _ mc], }

/-- The commutant of a subalgebra. -/
def subalgebra.commutant {𝕜 : Type v} [comm_semiring 𝕜] {A : Type u} [semiring A] [algebra 𝕜 A]
  (B : subalgebra 𝕜 A) : subalgebra 𝕜 A :=
{ algebra_map_mem' := λ r x mx, by rw [algebra.commutes],
  .. B.to_subsemiring.commutant, }

/-- A *-subalgebra is a subalgebra of *-algebra which is closed under *. -/
structure star_subalgebra (R : Type u) (A : Type v) [comm_semiring R] [star_ring R]
  [semiring A] [star_ring A] [algebra R A] [star_module R A] extends subalgebra R A : Type v :=
(star_mem' {a} : a ∈ carrier → star a ∈ carrier)

/-- The commutant of a *-subalgebra. -/
def star_subalgebra.commutant {R : Type u} {A : Type v} [comm_semiring R] [star_ring R]
  [semiring A] [star_ring A] [algebra R A] [star_module R A] (B : star_subalgebra R A) :
  star_subalgebra R A :=
{ star_mem' := λ x xm y hy, by simpa using congr_arg star (xm _ (B.star_mem' hy)).symm,
  ..B.to_subalgebra.commutant, }

/--
The double commutant definition of a von Neumann algebra,
as a *-closed subalgebra of bounded operators on a Hilbert space,
which is equal to its double commutant.

Note that this definition is parameterised by the Hilbert space
on which the algebra faithfully acts.
-/
structure von_neumann_algebra (H : Type u) [inner_product_space ℂ H] [complete_space H] extends
  M : star_subalgebra ℂ (H →L[ℂ] H) :=
(double_commutant : M.commutant.commutant = M)
