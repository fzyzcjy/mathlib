/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import measure_theory.function.special_functions.basic
import analysis.special_functions.trigonometric.arctan

/-!
# Measurability of arctan

-/

namespace real

@[measurability] lemma measurable_arctan : measurable arctan := continuous_arctan.measurable

end real

section real_composition
open real
variables {α : Type*} {m : measurable_space α} {f : α → ℝ} (hf : measurable f)

@[measurability] lemma measurable.arctan : measurable (λ x, arctan (f x)) :=
measurable_arctan.comp hf

end real_composition
