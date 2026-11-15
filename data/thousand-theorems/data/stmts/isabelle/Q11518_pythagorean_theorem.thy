(*
  Statement-only formalization of thousand-theorems corpus artifact Q11518,
  "Pythagorean theorem": for three points in a real inner-product affine
  space, the squared-distance identity holds exactly when the angle at the
  middle point is pi divided by two. This file contains no proof.
*)

theory Q11518_pythagorean_theorem
  imports "HOL-Analysis.Inner_Product"
begin

locale q11518_euclidean_affine_space =
  fixes q11518_vadd :: "'v::real_inner \<Rightarrow> 'p \<Rightarrow> 'p"
    and q11518_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q11518_zero_vadd:
      "q11518_vadd 0 p = p"
    and q11518_add_vadd:
      "q11518_vadd (u + v) p = q11518_vadd u (q11518_vadd v p)"
    and q11518_vadd_vsub:
      "q11518_vadd (q11518_vsub p q) q = p"
    and q11518_vsub_vadd:
      "q11518_vsub (q11518_vadd v p) p = v"
begin

definition q11518_dist :: "'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q11518_dist p q = norm (q11518_vsub p q)"

definition q11518_angle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q11518_angle p1 p2 p3 =
    arccos (inner (q11518_vsub p1 p2) (q11518_vsub p3 p2) /
      (norm (q11518_vsub p1 p2) * norm (q11518_vsub p3 p2)))"

theorem pythagorean_theorem:
  fixes p1 p2 p3 :: 'p
  shows
    "q11518_dist p1 p3 * q11518_dist p1 p3 =
        q11518_dist p1 p2 * q11518_dist p1 p2 +
          q11518_dist p3 p2 * q11518_dist p3 p2
      \<longleftrightarrow> q11518_angle p1 p2 p3 = pi / 2"
  sorry

end

end
