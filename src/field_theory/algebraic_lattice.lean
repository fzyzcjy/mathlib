import field_theory.adjoin
import linear_algebra.span
import linear_algebra.finsupp
import order.compactly_generated

variables {K L : Type*} [field K] [field L] [algebra K L]

namespace intermediate_field

open set

lemma exists_finset_of_mem_supr
  {ι : Type*} {f : ι → intermediate_field K L} {x : L} (hx : x ∈ ⨆ i, f i) :
  ∃ s : finset ι, x ∈ ⨆ i ∈ s, f i :=
begin
  have := complete_lattice.is_compact_element.exists_finset_of_le_supr
    (intermediate_field K L) (adjoin_simple_is_compact_element x) f,
  simp only [adjoin_simple_le_iff] at this,
  exact this hx,
end

end intermediate_field
