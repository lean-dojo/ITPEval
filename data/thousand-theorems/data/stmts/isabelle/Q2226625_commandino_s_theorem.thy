(*
  Statement-only formalization of thousand-theorems corpus artifact Q2226625
  (thousand-theorems__isabelle__Q2226625), "Commandino's theorem": for an
  n-simplex in an affine space over a characteristic-zero division ring, the
  vector from a vertex to the centroid is n times the vector from the centroid
  to the centroid of the opposite face. This file contains no proof.
*)

theory Q2226625_commandino_s_theorem
  imports Main
begin

locale q2226625_affine_space =
  fixes scale :: "'k::{division_ring,ring_char_0} \<Rightarrow> 'v::ab_group_add \<Rightarrow> 'v"
    and vadd :: "'v \<Rightarrow> 'p \<Rightarrow> 'p"
    and vsub :: "'p \<Rightarrow> 'p \<Rightarrow> 'v"
  assumes scale_right_distrib:
      "scale a (u + v) = scale a u + scale a v"
    and scale_left_distrib:
      "scale (a + b) v = scale a v + scale b v"
    and scale_assoc:
      "scale a (scale b v) = scale (a * b) v"
    and scale_one:
      "scale 1 v = v"
    and vadd_zero:
      "vadd 0 p = p"
    and vadd_add:
      "vadd (u + v) p = vadd u (vadd v p)"
    and vsub_vadd:
      "vsub (vadd v p) p = v"
    and vadd_vsub:
      "vadd (vsub p q) q = p"
begin

definition q2226625_affine_independent ::
    "nat \<Rightarrow> (nat \<Rightarrow> 'p) \<Rightarrow> bool"
  where
    "q2226625_affine_independent n points \<longleftrightarrow>
      (\<forall>c :: nat \<Rightarrow> 'k.
        (\<Sum>j\<in>{..n}. c j) = 0 \<and>
        (\<Sum>j\<in>{..n}. scale (c j) (vsub (points j) (points 0))) = 0
        \<longrightarrow> (\<forall>j\<le>n. c j = 0))"

definition q2226625_centroid ::
    "nat \<Rightarrow> (nat \<Rightarrow> 'p) \<Rightarrow> 'p"
  where
    "q2226625_centroid n points =
      vadd
        (scale (inverse (of_nat (Suc n)))
          (\<Sum>j\<in>{..n}. vsub (points j) (points 0)))
        (points 0)"

definition q2226625_face_opposite_centroid ::
    "nat \<Rightarrow> (nat \<Rightarrow> 'p) \<Rightarrow> nat \<Rightarrow> 'p"
  where
    "q2226625_face_opposite_centroid n points i =
      vadd
        (scale (inverse (of_nat n))
          (\<Sum>j\<in>{..n} - {i}. vsub (points j) (points 0)))
        (points 0)"

theorem q2226625_commandino:
  fixes n :: nat
    and points :: "nat \<Rightarrow> 'p"
    and i :: nat
  assumes n_nonzero: "n \<noteq> 0"
    and simplex: "q2226625_affine_independent n points"
    and vertex: "i \<le> n"
  shows
    "vsub (points i) (q2226625_centroid n points) =
      scale (of_nat n)
        (vsub (q2226625_centroid n points)
          (q2226625_face_opposite_centroid n points i))"
  sorry

end

end
