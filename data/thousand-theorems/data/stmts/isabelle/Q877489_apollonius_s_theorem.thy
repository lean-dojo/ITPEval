(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q877489 (thousand-theorems__isabelle__Q877489), "Apollonius's theorem":
  in a real inner-product affine metric space, the sum of the squared
  distances from a point to two endpoints equals twice the sum of the squared
  distance to their midpoint and the squared half-distance between them.
  This file contains no proof.
*)

theory Q877489_apollonius_s_theorem
  imports "HOL-Analysis.Inner_Product"
begin

locale q877489_euclidean_affine_space =
  fixes q877489_vadd :: "'v::real_inner \<Rightarrow> 'p::metric_space \<Rightarrow> 'p"
    and q877489_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q877489_zero_vadd:
      "q877489_vadd 0 p = p"
    and q877489_add_vadd:
      "q877489_vadd (u + v) p =
        q877489_vadd u (q877489_vadd v p)"
    and q877489_vadd_vsub:
      "q877489_vadd (q877489_vsub p q) q = p"
    and q877489_vsub_vadd:
      "q877489_vsub (q877489_vadd v p) p = v"
    and q877489_dist_eq_norm_vsub:
      "dist p q = norm (q877489_vsub p q)"
begin

definition q877489_midpoint :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
  "q877489_midpoint p q =
    q877489_vadd ((1 / 2) *\<^sub>R q877489_vsub p q) q"

theorem apollonius_s_theorem:
  fixes a b c :: 'p
  shows
    "dist a b ^ 2 + dist a c ^ 2 =
      2 * (dist a (q877489_midpoint b c) ^ 2 + (dist b c / 2) ^ 2)"
  sorry

end

end
