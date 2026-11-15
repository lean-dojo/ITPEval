(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2267175 (thousand-theorems__isabelle__Q2267175), "Tangent-secant theorem":
  in a real inner-product affine space, the squared distance along a tangent
  line equals the product of the distances from the same point to two sphere
  intersections on a secant line. This file contains no proof.
*)

theory Q2267175_tangent_secant_theorem
  imports "HOL-Analysis.Inner_Product"
begin

record 'p q2267175_sphere =
  q2267175_center :: 'p
  q2267175_radius :: real

locale q2267175_euclidean_affine_space =
  fixes q2267175_vadd :: "'v::real_inner \<Rightarrow> 'p \<Rightarrow> 'p"
    and q2267175_vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes q2267175_zero_vadd:
      "q2267175_vadd 0 p = p"
    and q2267175_add_vadd:
      "q2267175_vadd (u + v) p =
        q2267175_vadd u (q2267175_vadd v p)"
    and q2267175_vadd_vsub:
      "q2267175_vadd (q2267175_vsub p q) q = p"
    and q2267175_vsub_vadd:
      "q2267175_vsub (q2267175_vadd v p) p = v"
begin

definition q2267175_dist :: "'p \<Rightarrow> 'p \<Rightarrow> real" where
  "q2267175_dist p q = norm (q2267175_vsub p q)"

definition q2267175_sphere_mem ::
    "'p \<Rightarrow> 'p q2267175_sphere \<Rightarrow> bool" where
  "q2267175_sphere_mem x s \<longleftrightarrow>
    q2267175_dist x (q2267175_center s) = q2267175_radius s"

definition q2267175_line_mem ::
    "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "q2267175_line_mem x a b \<longleftrightarrow>
    (\<exists>r::real.
      x = q2267175_vadd (r *\<^sub>R q2267175_vsub a b) b)"

definition q2267175_is_tangent_at_line ::
    "'p q2267175_sphere \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "q2267175_is_tangent_at_line s t p \<longleftrightarrow>
    q2267175_sphere_mem t s \<and>
    q2267175_line_mem t p t \<and>
    (\<forall>x. q2267175_line_mem x p t \<longrightarrow>
      inner (q2267175_vsub x t)
        (q2267175_vsub t (q2267175_center s)) = 0)"

theorem tangent_secant_theorem:
  fixes a b t p :: 'p
    and s :: "'p q2267175_sphere"
  assumes first_secant_intersection:
      "q2267175_sphere_mem a s"
    and second_secant_intersection:
      "q2267175_sphere_mem b s"
    and point_on_secant:
      "q2267175_line_mem p a b"
    and tangent_at_t:
      "q2267175_is_tangent_at_line s t p"
  shows
      "q2267175_dist p t ^ 2 =
        q2267175_dist p a * q2267175_dist p b"
  sorry

end

end
