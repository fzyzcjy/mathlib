/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import analysis.convex.between
import geometry.euclidean.angle.unoriented.basic

/-!
# Angles between points

This file defines unoriented angles in Euclidean affine spaces.

## Main definitions

* `euclidean_geometry.angle`, with notation `∠`, is the undirected angle determined by three
  points.

-/

noncomputable theory
open_locale big_operators
open_locale real
open_locale real_inner_product_space

namespace euclidean_geometry

open inner_product_geometry

variables {V : Type*} {P : Type*} [inner_product_space ℝ V] [metric_space P]
    [normed_add_torsor V P]
include V

/-- The undirected angle at `p2` between the line segments to `p1` and
`p3`. If either of those points equals `p2`, this is π/2. Use
`open_locale euclidean_geometry` to access the `∠ p1 p2 p3`
notation. -/
def angle (p1 p2 p3 : P) : ℝ := angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2)

localized "notation (name := angle) `∠` := euclidean_geometry.angle" in euclidean_geometry

lemma continuous_at_angle {x : P × P × P} (hx12 : x.1 ≠ x.2.1) (hx32 : x.2.2 ≠ x.2.1) :
  continuous_at (λ y : P × P × P, ∠ y.1 y.2.1 y.2.2) x :=
begin
  let f : P × P × P → V × V := λ y, (y.1 -ᵥ y.2.1, y.2.2 -ᵥ y.2.1),
  have hf1 : (f x).1 ≠ 0, by simp [hx12],
  have hf2 : (f x).2 ≠ 0, by simp [hx32],
  exact (inner_product_geometry.continuous_at_angle hf1 hf2).comp
    ((continuous_fst.vsub continuous_snd.fst).prod_mk
      (continuous_snd.snd.vsub continuous_snd.fst)).continuous_at
end

@[simp] lemma _root_.affine_isometry.angle_map {V₂ P₂ : Type*} [inner_product_space ℝ V₂]
  [metric_space P₂] [normed_add_torsor V₂ P₂] (f : P →ᵃⁱ[ℝ] P₂) (p₁ p₂ p₃ : P) :
  ∠ (f p₁) (f p₂) (f p₃) = ∠ p₁ p₂ p₃ :=
by simp_rw [angle, ←affine_isometry.map_vsub, linear_isometry.angle_map]

@[simp, norm_cast] lemma _root_.affine_subspace.angle_coe {s : affine_subspace ℝ P}
  (p₁ p₂ p₃ : s) :
  by haveI : nonempty s := ⟨p₁⟩; exact ∠ (p₁ : P) (p₂ : P) (p₃ : P) = ∠ p₁ p₂ p₃ :=
by haveI : nonempty s := ⟨p₁⟩; exact s.subtypeₐᵢ.angle_map p₁ p₂ p₃

/-- The angle at a point does not depend on the order of the other two
points. -/
lemma angle_comm (p1 p2 p3 : P) : ∠ p1 p2 p3 = ∠ p3 p2 p1 :=
angle_comm _ _

/-- The angle at a point is nonnegative. -/
lemma angle_nonneg (p1 p2 p3 : P) : 0 ≤ ∠ p1 p2 p3 :=
angle_nonneg _ _

/-- The angle at a point is at most π. -/
lemma angle_le_pi (p1 p2 p3 : P) : ∠ p1 p2 p3 ≤ π :=
angle_le_pi _ _

/-- The angle ∠AAB at a point. -/
lemma angle_eq_left (p1 p2 : P) : ∠ p1 p1 p2 = π / 2 :=
begin
  unfold angle,
  rw vsub_self,
  exact angle_zero_left _
end

/-- The angle ∠ABB at a point. -/
lemma angle_eq_right (p1 p2 : P) : ∠ p1 p2 p2 = π / 2 :=
by rw [angle_comm, angle_eq_left]

/-- The angle ∠ABA at a point. -/
lemma angle_eq_of_ne {p1 p2 : P} (h : p1 ≠ p2) : ∠ p1 p2 p1 = 0 :=
angle_self (λ he, h (vsub_eq_zero_iff_eq.1 he))

/-- If the angle ∠ABC at a point is π, the angle ∠BAC is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_left {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
  ∠ p2 p1 p3 = 0 :=
begin
  unfold angle at h,
  rw angle_eq_pi_iff at h,
  rcases h with ⟨hp1p2, ⟨r, ⟨hr, hpr⟩⟩⟩,
  unfold angle,
  rw angle_eq_zero_iff,
  rw [←neg_vsub_eq_vsub_rev, neg_ne_zero] at hp1p2,
  use [hp1p2, -r + 1, add_pos (neg_pos_of_neg hr) zero_lt_one],
  rw [add_smul, ←neg_vsub_eq_vsub_rev p1 p2, smul_neg],
  simp [←hpr]
end

/-- If the angle ∠ABC at a point is π, the angle ∠BCA is 0. -/
lemma angle_eq_zero_of_angle_eq_pi_right {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
  ∠ p2 p3 p1 = 0 :=
begin
  rw angle_comm at h,
  exact angle_eq_zero_of_angle_eq_pi_left h
end

/-- If ∠BCD = π, then ∠ABC = ∠ABD. -/
lemma angle_eq_angle_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
  ∠ p1 p2 p3 = ∠ p1 p2 p4 :=
begin
  unfold angle at *,
  rcases angle_eq_pi_iff.1 h with ⟨hp2p3, ⟨r, ⟨hr, hpr⟩⟩⟩,
  rw [eq_comm],
  convert angle_smul_right_of_pos (p1 -ᵥ p2) (p3 -ᵥ p2) (add_pos (neg_pos_of_neg hr) zero_lt_one),
  rw [add_smul, ← neg_vsub_eq_vsub_rev p2 p3, smul_neg, neg_smul, ← hpr],
  simp
end

/-- If ∠BCD = π, then ∠ACB + ∠ACD = π. -/
lemma angle_add_angle_eq_pi_of_angle_eq_pi (p1 : P) {p2 p3 p4 : P} (h : ∠ p2 p3 p4 = π) :
  ∠ p1 p3 p2 + ∠ p1 p3 p4 = π :=
begin
  unfold angle at h,
  rw [angle_comm p1 p3 p2, angle_comm p1 p3 p4],
  unfold angle,
  exact angle_add_angle_eq_pi_of_angle_eq_pi _ h
end

/-- Vertical Angles Theorem: angles opposite each other, formed by two intersecting straight
lines, are equal. -/
lemma angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi {p1 p2 p3 p4 p5 : P}
  (hapc : ∠ p1 p5 p3 = π) (hbpd : ∠ p2 p5 p4 = π) : ∠ p1 p5 p2 = ∠ p3 p5 p4 :=
by linarith [angle_add_angle_eq_pi_of_angle_eq_pi p1 hbpd, angle_comm p4 p5 p1,
             angle_add_angle_eq_pi_of_angle_eq_pi p4 hapc, angle_comm p4 p5 p3]

/-- If ∠ABC = π then dist A B ≠ 0. -/
lemma left_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p1 p2 ≠ 0 :=
begin
  by_contra heq,
  rw [dist_eq_zero] at heq,
  rw [heq, angle_eq_left] at h,
  exact real.pi_ne_zero (by linarith),
end

/-- If ∠ABC = π then dist C B ≠ 0. -/
lemma right_dist_ne_zero_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) : dist p3 p2 ≠ 0 :=
left_dist_ne_zero_of_angle_eq_pi $ (angle_comm _ _ _).trans h

/-- If ∠ABC = π, then (dist A C) = (dist A B) + (dist B C). -/
lemma dist_eq_add_dist_of_angle_eq_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = π) :
  dist p1 p3 = dist p1 p2 + dist p3 p2 :=
begin
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right],
  exact norm_sub_eq_add_norm_of_angle_eq_pi h,
end

/-- If A ≠ B and C ≠ B then ∠ABC = π if and only if (dist A C) = (dist A B) + (dist B C). -/
lemma dist_eq_add_dist_iff_angle_eq_pi {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
  dist p1 p3 = dist p1 p2 + dist p3 p2 ↔ ∠ p1 p2 p3 = π :=
begin
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right],
  exact norm_sub_eq_add_norm_iff_angle_eq_pi
    ((λ he, hp1p2 (vsub_eq_zero_iff_eq.1 he))) (λ he, hp3p2 (vsub_eq_zero_iff_eq.1 he)),
end

/-- If ∠ABC = 0, then (dist A C) = abs ((dist A B) - (dist B C)). -/
lemma dist_eq_abs_sub_dist_of_angle_eq_zero {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = 0) :
  (dist p1 p3) = |(dist p1 p2) - (dist p3 p2)| :=
begin
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right],
  exact norm_sub_eq_abs_sub_norm_of_angle_eq_zero h,
end

/-- If A ≠ B and C ≠ B then ∠ABC = 0 if and only if (dist A C) = abs ((dist A B) - (dist B C)). -/
lemma dist_eq_abs_sub_dist_iff_angle_eq_zero {p1 p2 p3 : P} (hp1p2 : p1 ≠ p2) (hp3p2 : p3 ≠ p2) :
  (dist p1 p3) = |(dist p1 p2) - (dist p3 p2)| ↔ ∠ p1 p2 p3 = 0 :=
begin
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right],
  exact norm_sub_eq_abs_sub_norm_iff_angle_eq_zero
    ((λ he, hp1p2 (vsub_eq_zero_iff_eq.1 he))) (λ he, hp3p2 (vsub_eq_zero_iff_eq.1 he)),
end

/-- If M is the midpoint of the segment AB, then ∠AMB = π. -/
lemma angle_midpoint_eq_pi (p1 p2 : P) (hp1p2 : p1 ≠ p2) : ∠ p1 (midpoint ℝ p1 p2) p2 = π :=
have p2 -ᵥ midpoint ℝ p1 p2 = -(p1 -ᵥ midpoint ℝ p1 p2), by { rw neg_vsub_eq_vsub_rev, simp },
by simp [angle, this, hp1p2, -zero_lt_one]

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMA = π / 2. -/
lemma angle_left_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
  ∠ p3 (midpoint ℝ p1 p2) p1 = π / 2 :=
begin
  let m : P := midpoint ℝ p1 p2,
  have h1 : p3 -ᵥ p1 = (p3 -ᵥ m) - (p1 -ᵥ m) := (vsub_sub_vsub_cancel_right p3 p1 m).symm,
  have h2 : p3 -ᵥ p2 = (p3 -ᵥ m) + (p1 -ᵥ m),
  { rw [left_vsub_midpoint, ← midpoint_vsub_right, vsub_add_vsub_cancel] },
  rw [dist_eq_norm_vsub V p3 p1, dist_eq_norm_vsub V p3 p2, h1, h2] at h,
  exact (norm_add_eq_norm_sub_iff_angle_eq_pi_div_two (p3 -ᵥ m) (p1 -ᵥ m)).mp h.symm,
end

/-- If M is the midpoint of the segment AB and C is the same distance from A as it is from B
then ∠CMB = π / 2. -/
lemma angle_right_midpoint_eq_pi_div_two_of_dist_eq {p1 p2 p3 : P} (h : dist p3 p1 = dist p3 p2) :
  ∠ p3 (midpoint ℝ p1 p2) p2 = π / 2 :=
by rw [midpoint_comm p1 p2, angle_left_midpoint_eq_pi_div_two_of_dist_eq h.symm]

/-- If the second of three points is strictly between the other two, the angle at that point
is π. -/
lemma _root_.sbtw.angle₁₂₃_eq_pi {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₂ p₃ = π :=
begin
  rw [angle, angle_eq_pi_iff],
  rcases h with ⟨⟨r, ⟨hr0, hr1⟩, hp₂⟩, hp₂p₁, hp₂p₃⟩,
  refine ⟨vsub_ne_zero.2 hp₂p₁.symm, -(1 - r) / r, _⟩,
  have hr0' : r ≠ 0,
  { rintro rfl,
    rw ←hp₂ at hp₂p₁,
    simpa using hp₂p₁ },
  have hr1' : r ≠ 1,
  { rintro rfl,
    rw ←hp₂ at hp₂p₃,
    simpa using hp₂p₃ },
  replace hr0 := hr0.lt_of_ne hr0'.symm,
  replace hr1 := hr1.lt_of_ne hr1',
  refine ⟨div_neg_of_neg_of_pos (left.neg_neg_iff.2 (sub_pos.2 hr1)) hr0, _⟩,
  rw [←hp₂, affine_map.line_map_apply, vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub, vsub_self,
      zero_sub, smul_neg, smul_smul, div_mul_cancel _ hr0', neg_smul, neg_neg, sub_eq_iff_eq_add,
      ←add_smul, sub_add_cancel, one_smul]
end

/-- If the second of three points is strictly between the other two, the angle at that point
(reversed) is π. -/
lemma _root_.sbtw.angle₃₂₁_eq_pi {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₂ p₁ = π :=
by rw [←h.angle₁₂₃_eq_pi, angle_comm]

/-- The angle between three points is π if and only if the second point is strictly between the
other two. -/
lemma angle_eq_pi_iff_sbtw {p₁ p₂ p₃ : P} : ∠ p₁ p₂ p₃ = π ↔ sbtw ℝ p₁ p₂ p₃ :=
begin
  refine ⟨_, λ h, h.angle₁₂₃_eq_pi⟩,
  rw [angle, angle_eq_pi_iff],
  rintro ⟨hp₁p₂, r, hr, hp₃p₂⟩,
  refine ⟨⟨1 / (1 - r),
           ⟨div_nonneg zero_le_one (sub_nonneg.2 (hr.le.trans zero_le_one)),
            (div_le_one (sub_pos.2 (hr.trans zero_lt_one))).2 ((le_sub_self_iff 1).2 hr.le)⟩, _⟩,
          (vsub_ne_zero.1 hp₁p₂).symm, _⟩,
  { rw ←eq_vadd_iff_vsub_eq at hp₃p₂,
    rw [affine_map.line_map_apply, hp₃p₂, vadd_vsub_assoc, ←neg_vsub_eq_vsub_rev p₂ p₁,
        smul_neg, ←neg_smul, smul_add, smul_smul, ←add_smul, eq_comm, eq_vadd_iff_vsub_eq],
    convert (one_smul ℝ (p₂ -ᵥ p₁)).symm,
    field_simp [(sub_pos.2 (hr.trans zero_lt_one)).ne.symm],
    abel },
  { rw [ne_comm, ←@vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff],
    exact ⟨hr.ne, hp₁p₂⟩ }
end

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point is zero. -/
lemma _root_.wbtw.angle₂₁₃_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
  ∠ p₂ p₁ p₃ = 0 :=
begin
  rw [angle, angle_eq_zero_iff],
  rcases h with ⟨r, ⟨hr0, hr1⟩, rfl⟩,
  have hr0' : r ≠ 0, { rintro rfl, simpa using hp₂p₁ },
  replace hr0 := hr0.lt_of_ne hr0'.symm,
  refine ⟨vsub_ne_zero.2 hp₂p₁, r⁻¹, inv_pos.2 hr0, _⟩,
  rw [affine_map.line_map_apply, vadd_vsub_assoc, vsub_self, add_zero, smul_smul,
      inv_mul_cancel hr0', one_smul]
end

/-- If the second of three points is strictly between the other two, the angle at the first point
is zero. -/
lemma _root_.sbtw.angle₂₁₃_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₁ p₃ = 0 :=
h.wbtw.angle₂₁₃_eq_zero_of_ne h.ne_left

/-- If the second of three points is weakly between the other two, and not equal to the first,
the angle at the first point (reversed) is zero. -/
lemma _root_.wbtw.angle₃₁₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) (hp₂p₁ : p₂ ≠ p₁) :
  ∠ p₃ p₁ p₂ = 0 :=
by rw [←h.angle₂₁₃_eq_zero_of_ne hp₂p₁, angle_comm]

/-- If the second of three points is strictly between the other two, the angle at the first point
(reversed) is zero. -/
lemma _root_.sbtw.angle₃₁₂_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₃ p₁ p₂ = 0 :=
h.wbtw.angle₃₁₂_eq_zero_of_ne h.ne_left

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point is zero. -/
lemma _root_.wbtw.angle₂₃₁_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
  ∠ p₂ p₃ p₁ = 0 :=
h.symm.angle₂₁₃_eq_zero_of_ne hp₂p₃

/-- If the second of three points is strictly between the other two, the angle at the third point
is zero. -/
lemma _root_.sbtw.angle₂₃₁_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₂ p₃ p₁ = 0 :=
h.wbtw.angle₂₃₁_eq_zero_of_ne h.ne_right

/-- If the second of three points is weakly between the other two, and not equal to the third,
the angle at the third point (reversed) is zero. -/
lemma _root_.wbtw.angle₁₃₂_eq_zero_of_ne {p₁ p₂ p₃ : P} (h : wbtw ℝ p₁ p₂ p₃) (hp₂p₃ : p₂ ≠ p₃) :
  ∠ p₁ p₃ p₂ = 0 :=
h.symm.angle₃₁₂_eq_zero_of_ne hp₂p₃

/-- If the second of three points is strictly between the other two, the angle at the third point
(reversed) is zero. -/
lemma _root_.sbtw.angle₁₃₂_eq_zero {p₁ p₂ p₃ : P} (h : sbtw ℝ p₁ p₂ p₃) : ∠ p₁ p₃ p₂ = 0 :=
h.wbtw.angle₁₃₂_eq_zero_of_ne h.ne_right

/-- The angle between three points is zero if and only if one of the first and third points is
weakly between the other two, and not equal to the second. -/
lemma angle_eq_zero_iff_ne_and_wbtw {p₁ p₂ p₃ : P} :
  ∠ p₁ p₂ p₃ = 0 ↔ (p₁ ≠ p₂ ∧ wbtw ℝ p₂ p₁ p₃) ∨ (p₃ ≠ p₂ ∧ wbtw ℝ p₂ p₃ p₁) :=
begin
  split,
  { rw [angle, angle_eq_zero_iff],
    rintro ⟨hp₁p₂, r, hr0, hp₃p₂⟩,
    rcases le_or_lt 1 r with hr1 | hr1,
    { refine or.inl ⟨vsub_ne_zero.1 hp₁p₂, r⁻¹, ⟨(inv_pos.2 hr0).le, inv_le_one hr1⟩, _⟩,
      rw [affine_map.line_map_apply, hp₃p₂, smul_smul, inv_mul_cancel hr0.ne.symm, one_smul,
          vsub_vadd] },
    { refine or.inr ⟨_, r, ⟨hr0.le, hr1.le⟩, _⟩,
      { rw [←@vsub_ne_zero V, hp₃p₂, smul_ne_zero_iff],
        exact ⟨hr0.ne.symm, hp₁p₂⟩ },
      { rw [affine_map.line_map_apply, ←hp₃p₂, vsub_vadd] } } },
  { rintro (⟨hp₁p₂, h⟩ | ⟨hp₃p₂, h⟩),
    { exact h.angle₂₁₃_eq_zero_of_ne hp₁p₂ },
    { exact h.angle₃₁₂_eq_zero_of_ne hp₃p₂ } }
end

/-- The angle between three points is zero if and only if one of the first and third points is
strictly between the other two, or those two points are equal but not equal to the second. -/
lemma angle_eq_zero_iff_eq_and_ne_or_sbtw {p₁ p₂ p₃ : P} :
  ∠ p₁ p₂ p₃ = 0 ↔ (p₁ = p₃ ∧ p₁ ≠ p₂) ∨ sbtw ℝ p₂ p₁ p₃ ∨ sbtw ℝ p₂ p₃ p₁ :=
begin
  rw angle_eq_zero_iff_ne_and_wbtw,
  by_cases hp₁p₂ : p₁ = p₂, { simp [hp₁p₂] },
  by_cases hp₁p₃ : p₁ = p₃, { simp [hp₁p₃] },
  by_cases hp₃p₂ : p₃ = p₂, { simp [hp₃p₂] },
  simp [hp₁p₂, hp₁p₃, ne.symm hp₁p₃, sbtw, hp₃p₂]
end

end euclidean_geometry
