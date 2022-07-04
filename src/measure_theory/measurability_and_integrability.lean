/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.draft
import measure_theory.function.uniform_integrable

/-!
# Measurability And Integrability in mathlib

There are several notions of measurability and of integrability in mathlib. The purpose of this file
is to summarize how they relate to each other.

## Measurability

* `measurable f` (in measure_theory.measurable_space_def.lean):
* `strongly_measurable f` (in measure_theory.function.strongly_measurable.lean):
* `fin_strongly_measurable f μ` (in measure_theory.function.strongly_measurable.lean):

Additionally, we define the following three notions:
* `ae_measurable f μ` (in measure_theory.measure.measure_space_def.lean)
* `ae_strongly_measurable f μ` (in measure_theory.function.strongly_measurable.lean)
* `ae_fin_strongly_measurable f μ` (in measure_theory.function.strongly_measurable.lean)

All three `ae_*` definitions follow the same principle: a function is
`ae_measurable` (resp. `ae_strongly_measurable`, `ae_fin_strongly_measurable`) if it is `μ`-almost-
everywhere equal to a `measurable` (resp. `strongly_measurable`, `fin_strongly_measurable`)
function.

## Integrability

* `mem_ℒp f p μ`
* `integrable f μ`
* `sigma_integrable m f μ`
* `unif_integrable f p μ`
* `uniform_integrable f p μ`

-/

open measure_theory topological_space
open_locale ennreal

variables {ι α β : Type*} {m m₀ : measurable_space α} {μ : measure α} {f : α → β} {p : ℝ≥0∞}

include m₀

/-! ### Measurability -/

/-- A strongly measurable function is a.e. strongly measurable. -/
example [topological_space β] :
  strongly_measurable f → ae_strongly_measurable f μ :=
strongly_measurable.ae_strongly_measurable

/-- A measurable function is a.e. measurable. -/
example [measurable_space β] :
  measurable f → ae_measurable f μ :=
measurable.ae_measurable

/-- A finitely strongly measurable function is a.e. finitely strongly measurable. -/
example [topological_space β] [has_zero β] :
  fin_strongly_measurable f μ → ae_fin_strongly_measurable f μ :=
fin_strongly_measurable.ae_fin_strongly_measurable

/-- In a pseudo-metrizable borel space, a strongly measurable function is measurable. -/
example [topological_space β] [measurable_space β] [pseudo_metrizable_space β] [borel_space β] :
  strongly_measurable f → measurable f :=
strongly_measurable.measurable

example [topological_space β] [has_zero β] :
  fin_strongly_measurable f μ → strongly_measurable f :=
fin_strongly_measurable.strongly_measurable

/-- If the measure is σ-finite, finitely strongly measurable and strongly measurable are
equivalent. -/
example [topological_space β] [has_zero β] [sigma_finite μ] :
  fin_strongly_measurable f μ ↔ strongly_measurable f :=
⟨fin_strongly_measurable.strongly_measurable,
  λ h, strongly_measurable.fin_strongly_measurable h μ⟩

/-- In a metrizable, second-countable borel space, strongly measurable and measurable are
equivalent. -/
example [topological_space β] [measurable_space β] [metrizable_space β] [borel_space β]
  [second_countable_topology β] :
  strongly_measurable f ↔ measurable f :=
strongly_measurable_iff_measurable

/-! ### Integrability -/

example [normed_group β] :
  integrable f μ → ae_strongly_measurable f μ :=
integrable.ae_strongly_measurable

example [normed_group β] :
  integrable f μ → sigma_integrable m f μ :=
λ h, integrable.sigma_integrable h m

example [normed_group β] :
  integrable f μ ↔ mem_ℒp f 1 μ :=
mem_ℒp_one_iff_integrable.symm

example [normed_group β] (hm : m ≤ m₀) :
  sigma_integrable m f μ → ae_strongly_measurable f μ :=
λ h, sigma_integrable.ae_strongly_measurable h hm

/-- In a borel_space, if the measure is σ-finite then σ-integrable with respect to the ambiant
σ-algebra and a.e. strongly measurable are equivalent. -/
example [normed_group β] [measurable_space β] [borel_space β] [sigma_finite μ] :
  sigma_integrable m₀ f μ ↔ ae_strongly_measurable f μ :=
⟨λ h, sigma_integrable.ae_strongly_measurable h le_rfl, ae_strongly_measurable.sigma_integrable⟩

example [normed_group β] {f : ι → α → β} :
  uniform_integrable f p μ → unif_integrable f p μ :=
uniform_integrable.unif_integrable

example [normed_group β] {f : ι → α → β} :
  uniform_integrable f p μ → ∀ i, strongly_measurable (f i) :=
uniform_integrable.strongly_measurable

example [normed_group β] {f : ι → α → β} :
  uniform_integrable f p μ → ∀ i, mem_ℒp (f i) p μ :=
uniform_integrable.mem_ℒp
