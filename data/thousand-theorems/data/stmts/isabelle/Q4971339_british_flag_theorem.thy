(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q4971339 (thousand-theorems__isabelle__Q4971339), "British flag theorem":
  in a real inner-product affine space, a parallelogram with a right angle has
  equal sums of squared distances from any point to opposite vertex pairs.
  This file contains no proof.
*)

theory Q4971339_british_flag_theorem
  imports "HOL-Analysis.Inner_Product"
begin

locale q4971339_euclidean_affine_space =
  fixes q4971339_vadd :: "'v::real_inner \<Rightarrow> 'p \<Rightarrow> 'p"
    and q4971339_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q4971339_zero_vadd:
      "q4971339_vadd 0 p = p"
    and q4971339_add_vadd:
      "q4971339_vadd (u + v) p =
        q4971339_vadd u (q4971339_vadd v p)"
    and q4971339_vadd_vsub:
      "q4971339_vadd (q4971339_vsub p q) q = p"
    and q4971339_vsub_vadd:
      "q4971339_vsub (q4971339_vadd v p) p = v"
begin

definition q4971339_dist :: "'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q4971339_dist p q = norm (q4971339_vsub p q)"

definition q4971339_midpoint :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
  "q4971339_midpoint p q =
    q4971339_vadd ((1 / 2) *\<^sub>R q4971339_vsub p q) q"

definition q4971339_angle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q4971339_angle p1 p2 p3 =
    arccos (inner (q4971339_vsub p1 p2) (q4971339_vsub p3 p2) /
      (norm (q4971339_vsub p1 p2) * norm (q4971339_vsub p3 p2)))"

theorem british_flag_theorem:
  fixes a b c d p :: 'p
  assumes parallelogram:
      "q4971339_midpoint a c = q4971339_midpoint b d"
    and right_angle:
      "q4971339_angle b a d = pi / 2"
  shows
      "q4971339_dist p a ^ 2 + q4971339_dist p c ^ 2 =
        q4971339_dist p b ^ 2 + q4971339_dist p d ^ 2"
  sorry

end

end
