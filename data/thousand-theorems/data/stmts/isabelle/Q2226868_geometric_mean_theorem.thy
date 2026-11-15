(*
  Statement-only formalization of thousand-theorems corpus artifact Q2226868,
  "Geometric mean theorem": in a real inner-product affine space, the squared
  altitude of a right triangle equals the product of the two hypotenuse
  segments cut off by its strictly interior foot. This file contains no proof.
*)

theory Q2226868_geometric_mean_theorem
  imports "HOL-Analysis.Inner_Product"
begin

locale q2226868_euclidean_affine_space =
  fixes q2226868_vadd :: "'v::real_inner \<Rightarrow> 'p \<Rightarrow> 'p"
    and q2226868_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q2226868_zero_vadd:
      "q2226868_vadd 0 p = p"
    and q2226868_add_vadd:
      "q2226868_vadd (u + v) p =
        q2226868_vadd u (q2226868_vadd v p)"
    and q2226868_vadd_vsub:
      "q2226868_vadd (q2226868_vsub p q) q = p"
    and q2226868_vsub_vadd:
      "q2226868_vsub (q2226868_vadd v p) p = v"
begin

definition q2226868_dist :: "'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q2226868_dist p q = norm (q2226868_vsub p q)"

definition q2226868_angle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q2226868_angle p1 p2 p3 =
    arccos (inner (q2226868_vsub p1 p2) (q2226868_vsub p3 p2) /
      (norm (q2226868_vsub p1 p2) * norm (q2226868_vsub p3 p2)))"

definition q2226868_strictly_between ::
    "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "q2226868_strictly_between p1 p4 p3 \<longleftrightarrow>
    p1 \<noteq> p3 \<and>
    (\<exists>r::real.
      0 < r \<and> r < 1 \<and>
      p4 = q2226868_vadd (r *\<^sub>R q2226868_vsub p3 p1) p1)"

theorem geometric_mean_theorem:
  fixes p1 p2 p3 p4 :: 'p
  assumes foot_between:
      "q2226868_strictly_between p1 p4 p3"
    and altitude_right_angle:
      "q2226868_angle p1 p4 p2 = pi / 2"
    and triangle_right_angle:
      "q2226868_angle p1 p2 p3 = pi / 2"
  shows
      "q2226868_dist p2 p4 ^ 2 =
        q2226868_dist p1 p4 * q2226868_dist p3 p4"
  sorry

end

end
