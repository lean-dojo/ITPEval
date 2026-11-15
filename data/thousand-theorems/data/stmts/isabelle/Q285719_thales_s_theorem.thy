(*
  Statement-only formalization of thousand-theorems corpus artifact Q285719,
  "Thales's theorem": in a real inner-product affine space, if two points are
  endpoints of a sphere diameter, then the angle at a third point is a right
  angle exactly when that point lies on the sphere. This file contains no proof.
*)

theory Q285719_thales_s_theorem
  imports "HOL-Analysis.Inner_Product"
begin

record 'p q285719_sphere =
  q285719_center :: 'p
  q285719_radius :: real

locale q285719_euclidean_affine_space =
  fixes q285719_vadd :: "'v::real_inner \<Rightarrow> 'p \<Rightarrow> 'p"
    and q285719_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q285719_zero_vadd:
      "q285719_vadd 0 p = p"
    and q285719_add_vadd:
      "q285719_vadd (u + v) p = q285719_vadd u (q285719_vadd v p)"
    and q285719_vadd_vsub:
      "q285719_vadd (q285719_vsub p q) q = p"
    and q285719_vsub_vadd:
      "q285719_vsub (q285719_vadd v p) p = v"
begin

definition q285719_dist :: "'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q285719_dist p q = norm (q285719_vsub p q)"

definition q285719_midpoint :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
  "q285719_midpoint p q =
    q285719_vadd ((1 / 2) *\<^sub>R q285719_vsub p q) q"

definition q285719_angle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q285719_angle p1 p2 p3 =
    arccos (inner (q285719_vsub p1 p2) (q285719_vsub p3 p2) /
      (norm (q285719_vsub p1 p2) * norm (q285719_vsub p3 p2)))"

definition q285719_sphere_mem :: "'p \<Rightarrow> 'p q285719_sphere \<Rightarrow> bool" where
  "q285719_sphere_mem p s \<longleftrightarrow>
    q285719_dist p (q285719_center s) = q285719_radius s"

definition q285719_is_diameter ::
    "'p q285719_sphere \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "q285719_is_diameter s p1 p3 \<longleftrightarrow>
    q285719_sphere_mem p1 s \<and>
    q285719_midpoint p1 p3 = q285719_center s"

theorem thales_theorem:
  fixes p1 p2 p3 :: 'p
    and s :: "'p q285719_sphere"
  assumes "q285719_is_diameter s p1 p3"
  shows
    "q285719_angle p1 p2 p3 = pi / 2 \<longleftrightarrow>
      q285719_sphere_mem p2 s"
  sorry

end

end
