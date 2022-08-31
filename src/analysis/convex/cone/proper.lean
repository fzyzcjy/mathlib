
/-
Copyright (c) 2020 Apurva Nakade All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import analysis.inner_product_space.adjoint

/-!

We define the closure of the convex cone over a real inner product space as a convex cone.

-/

-- TODO: add proper cones and farkas' lemma


open continuous_linear_map filter

namespace convex_cone

variables {E : Type*} [inner_product_space ℝ E]

/-- The closure of a convex cone inside a real inner product space is a convex cone. This
construction is mainly used for defining maps between proper cones. -/
def closure (K : convex_cone ℝ E) : convex_cone ℝ E :=
{ carrier := closure ↑K,
  smul_mem' :=
  begin
    rw ← seq_closure_eq_closure,
    rintros c hc x ⟨seq, mem, tends⟩,
    exact ⟨λ n, c • seq n, ⟨λ n, K.smul_mem hc (mem n), tendsto.const_smul tends c⟩⟩,
  end,
  add_mem' :=
  begin
    rw ← seq_closure_eq_closure,
    rintros x ⟨xseq, xmem, xtends⟩ y ⟨yseq, ymem, ytends⟩,
    exact ⟨λ n, xseq n + yseq n, ⟨λ n, K.add_mem (xmem n) (ymem n), tendsto.add xtends ytends⟩⟩,
  end }

@[simp] lemma coe_closure {K : convex_cone ℝ E} : (K.closure : set E) = _root_.closure K := rfl

lemma mem_closure_iff_seq_limit {K : convex_cone ℝ E} {a : E} :
  a ∈ K.closure ↔ ∃ x : ℕ → E, (∀ n : ℕ, x n ∈ K) ∧ tendsto x at_top (nhds a) :=
by simp_rw [← set_like.mem_coe, coe_closure, mem_closure_iff_seq_limit]

end convex_cone
