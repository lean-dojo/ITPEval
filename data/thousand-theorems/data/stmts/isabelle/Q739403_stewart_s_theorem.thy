(*
  Statement-only formalization of thousand-theorems corpus artifact Q739403
  (thousand-theorems__isabelle__Q739403), "Stewart's theorem": in a real
  inner-product affine metric space, a point forming a straight angle with two
  endpoints satisfies Stewart's weighted squared-distance identity. This file
  contains no proof.
*)

theory Q739403_stewart_s_theorem
  imports "HOL-Analysis.Inner_Product"
begin

locale q739403_euclidean_affine_space =
  fixes q739403_vadd :: "'v::real_inner \<Rightarrow> 'p::metric_space \<Rightarrow> 'p"
    and q739403_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q739403_zero_vadd:
      "q739403_vadd 0 p = p"
    and q739403_add_vadd:
      "q739403_vadd (u + v) p =
        q739403_vadd u (q739403_vadd v p)"
    and q739403_vadd_vsub:
      "q739403_vadd (q739403_vsub p q) q = p"
    and q739403_vsub_vadd:
      "q739403_vsub (q739403_vadd v p) p = v"
    and q739403_dist_eq_norm_vsub:
      "dist p q = norm (q739403_vsub p q)"
begin

definition q739403_angle :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q739403_angle a p c =
    arccos (inner (q739403_vsub a p) (q739403_vsub c p) /
      (norm (q739403_vsub a p) * norm (q739403_vsub c p)))"

theorem stewart_s_theorem:
  fixes a b c p :: 'p
  assumes straight_angle:
      "q739403_angle b p c = pi"
  shows
      "dist a b ^ 2 * dist c p + dist a c ^ 2 * dist b p =
        dist b c * (dist a p ^ 2 + dist b p * dist c p)"
  sorry

end

end
