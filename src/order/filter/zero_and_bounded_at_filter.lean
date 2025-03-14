/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import order.filter
import algebra.module.submodule.basic
import topology.algebra.monoid
import analysis.asymptotics.asymptotics

/-!
# Zero and Bounded at filter

Given a filter `l` we define the notion of a function being `zero_at_filter` as well as being
`bounded_at_filter`. Alongside this we construct the `submodule`, `add_submonoid` of functions
that are `zero_at_filter`. Similarly, we construct the `submodule` and `subalgebra` of functions
that are `bounded_at_filter`.

-/

namespace filter

variables {α β : Type*}

open_locale topological_space

/-- If `l` is a filter on `α`, then a function `f : α → β` is `zero_at_filter l`
  if it tends to zero along `l`. -/
def zero_at_filter [has_zero β] [topological_space β] (l : filter α) (f : α → β) : Prop :=
filter.tendsto f l (𝓝 0)

lemma zero_is_zero_at_filter [has_zero β] [topological_space β] (l : filter α) : zero_at_filter l
  (0 : α → β) := tendsto_const_nhds

/-- `zero_at_filter_submodule l` is the submodule of `f : α → β` which
tend to zero along `l`. -/
def zero_at_filter_submodule [topological_space β] [semiring β]
  [has_continuous_add β] [has_continuous_mul β] (l : filter α) : submodule β (α → β) :=
{ carrier := zero_at_filter l,
  zero_mem' := zero_is_zero_at_filter l,
  add_mem' := by { intros a b ha hb, simpa using ha.add hb, },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul c }, }

/-- `zero_at_filter_add_submonoid l` is the additive submonoid of `f : α → β`
which tend to zero along `l`. -/
def zero_at_filter_add_submonoid [topological_space β]
  [add_zero_class β] [has_continuous_add β] (l : filter α) : add_submonoid (α → β) :=
{ carrier := zero_at_filter l,
  add_mem' := by { intros a b ha hb, simpa using ha.add hb },
  zero_mem' := zero_is_zero_at_filter l, }

/-- If `l` is a filter on `α`, then a function `f: α → β` is `bounded_at_filter l`
if `f =O[l] 1`. -/
def bounded_at_filter [has_norm β] [has_one (α → β)] (l : filter α) (f : α → β) : Prop :=
asymptotics.is_O l f (1 : α → β)

lemma zero_at_filter_is_bounded_at_filter [normed_field β] (l : filter α) (f : α → β)
  (hf : zero_at_filter l f) : bounded_at_filter l f :=
asymptotics.is_O_of_div_tendsto_nhds (by simp) _ (by { convert hf, ext1, simp, })

lemma zero_is_bounded_at_filter [normed_field β] (l : filter α) :
  bounded_at_filter l (0 : α → β) :=
(zero_at_filter_is_bounded_at_filter l _) (zero_is_zero_at_filter l)

/-- The submodule of functions that are bounded along a filter `l`. -/
def bounded_filter_submodule [normed_field β] (l : filter α) : submodule β (α → β) :=
{ carrier := bounded_at_filter l,
  zero_mem' := zero_is_bounded_at_filter l,
  add_mem' := by { intros f g hf hg, simpa using hf.add hg, },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul_left c }, }

/-- The subalgebra of functions that are bounded along a filter `l`. -/
def bounded_filter_subalgebra [normed_field β] (l : filter α) :
  subalgebra β (α → β) :=
begin
  refine submodule.to_subalgebra (bounded_filter_submodule l) _ (λ f g hf hg, _),
  { simpa using asymptotics.is_O_const_mul_self (1 : β) (1 : α → β) l },
  { simpa only [pi.one_apply, mul_one, norm_mul] using hf.mul hg, },
end

end filter
