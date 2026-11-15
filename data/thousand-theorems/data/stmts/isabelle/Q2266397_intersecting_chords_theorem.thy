(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2266397 (thousand-theorems__isabelle__Q2266397), "Intersecting chords
  theorem": four cospherical points on two straight-angle chords through a
  point have equal products of distances to that point. This file contains no
  proof.
*)

theory Q2266397_intersecting_chords_theorem
  imports "HOL-Analysis.Inner_Product"
begin

locale q2266397_euclidean_affine_space =
  fixes q2266397_vadd :: "'v::real_inner \<Rightarrow> 'p \<Rightarrow> 'p"
    and q2266397_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q2266397_zero_vadd:
      "q2266397_vadd 0 p = p"
    and q2266397_add_vadd:
      "q2266397_vadd (u + v) p =
        q2266397_vadd u (q2266397_vadd v p)"
    and q2266397_vadd_vsub:
      "q2266397_vadd (q2266397_vsub p q) q = p"
    and q2266397_vsub_vadd:
      "q2266397_vsub (q2266397_vadd v p) p = v"
begin

definition q2266397_dist :: "'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q2266397_dist p q = norm (q2266397_vsub p q)"

definition q2266397_angle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q2266397_angle a p b =
    arccos (inner (q2266397_vsub a p) (q2266397_vsub b p) /
      (norm (q2266397_vsub a p) * norm (q2266397_vsub b p)))"

definition q2266397_cospherical :: "'p set \<Rightarrow> bool" where
  "q2266397_cospherical S \<longleftrightarrow>
    (\<exists>center radius.
      \<forall>x \<in> S. q2266397_dist x center = radius)"

theorem intersecting_chords_theorem:
  fixes a b c d p :: 'p
  assumes cospherical:
      "q2266397_cospherical {a, b, c, d}"
    and first_straight_angle:
      "q2266397_angle a p b = pi"
    and second_straight_angle:
      "q2266397_angle c p d = pi"
  shows
      "q2266397_dist a p * q2266397_dist b p =
        q2266397_dist c p * q2266397_dist d p"
  sorry

end

end
