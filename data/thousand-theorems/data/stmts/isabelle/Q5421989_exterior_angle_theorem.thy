(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q5421989 (thousand-theorems__isabelle__Q5421989), "Exterior angle theorem":
  in a real inner-product affine space, when one vertex lies strictly between
  an exterior point and a second vertex, the exterior angle equals the sum of
  the two remote interior angles. This file contains no proof.
*)

theory Q5421989_exterior_angle_theorem
  imports "HOL-Analysis.Inner_Product"
begin

locale q5421989_euclidean_affine_space =
  fixes q5421989_vadd :: "'v::real_inner \<Rightarrow> 'p::metric_space \<Rightarrow> 'p"
    and q5421989_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q5421989_zero_vadd:
      "q5421989_vadd 0 p = p"
    and q5421989_add_vadd:
      "q5421989_vadd (u + v) p =
        q5421989_vadd u (q5421989_vadd v p)"
    and q5421989_vadd_vsub:
      "q5421989_vadd (q5421989_vsub p q) q = p"
    and q5421989_vsub_vadd:
      "q5421989_vsub (q5421989_vadd v p) p = v"
    and q5421989_dist_eq_norm_vsub:
      "dist p q = norm (q5421989_vsub p q)"
begin

definition q5421989_angle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q5421989_angle p1 p2 p3 =
    arccos (inner (q5421989_vsub p1 p2) (q5421989_vsub p3 p2) /
      (norm (q5421989_vsub p1 p2) * norm (q5421989_vsub p3 p2)))"

definition q5421989_weakly_between ::
    "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "q5421989_weakly_between left middle right \<longleftrightarrow>
    (\<exists>r::real.
      0 \<le> r \<and> r \<le> 1 \<and>
      middle =
        q5421989_vadd (r *\<^sub>R q5421989_vsub right left) left)"

definition q5421989_strictly_between ::
    "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "q5421989_strictly_between left middle right \<longleftrightarrow>
    q5421989_weakly_between left middle right \<and>
    middle \<noteq> left \<and>
    middle \<noteq> right"

theorem exterior_angle_theorem:
  fixes p p1 p2 p3 :: 'p
  assumes p1_strictly_between_p_and_p2:
      "q5421989_strictly_between p p1 p2"
  shows
      "q5421989_angle p3 p1 p =
        q5421989_angle p1 p3 p2 + q5421989_angle p3 p2 p1"
  sorry

end

end
