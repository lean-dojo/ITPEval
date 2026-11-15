(*
  Statement-only formalization of "Pascal's Hexagon Theorem" from Hundred Theorems item 028.
  In the real affine plane, it states that six points on an arbitrary nonzero quadratic
  conic determine three collinear opposite-side intersection points, under the stated
  mixed-triple noncollinearity conditions. This file contains no proof.
*)

theory Pascal_Hexagon_Theorem
  imports Complex_Main
begin

type_synonym affine_point = "real \<times> real"

definition affine_conic :: "affine_point set \<Rightarrow> bool" where
  "affine_conic con \<longleftrightarrow>
    (\<exists>a b c d e f :: real.
      \<not> (a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0 \<and> e = 0 \<and> f = 0) \<and>
      con = {x.
        a * (fst x) ^ 2 + b * (snd x) ^ 2 + c * fst x * snd x +
        d * fst x + e * snd x + f = 0})"

definition collinear_points :: "affine_point \<Rightarrow> affine_point \<Rightarrow> affine_point \<Rightarrow> bool" where
  "collinear_points a b c \<longleftrightarrow>
    (fst b - fst a) * (snd c - snd a) =
    (snd b - snd a) * (fst c - fst a)"

theorem pascal_affine:
  fixes con :: "affine_point set"
    and x1 x2 x3 x4 x5 x6 x7 x8 x9 :: affine_point
  assumes mixed_triples_noncollinear:
      "\<not> collinear_points x1 x2 x4"
      "\<not> collinear_points x1 x2 x5"
      "\<not> collinear_points x1 x2 x6"
      "\<not> collinear_points x1 x3 x4"
      "\<not> collinear_points x1 x3 x5"
      "\<not> collinear_points x1 x3 x6"
      "\<not> collinear_points x2 x3 x4"
      "\<not> collinear_points x2 x3 x5"
      "\<not> collinear_points x2 x3 x6"
      "\<not> collinear_points x4 x5 x1"
      "\<not> collinear_points x4 x5 x2"
      "\<not> collinear_points x4 x5 x3"
      "\<not> collinear_points x4 x6 x1"
      "\<not> collinear_points x4 x6 x2"
      "\<not> collinear_points x4 x6 x3"
      "\<not> collinear_points x5 x6 x1"
      "\<not> collinear_points x5 x6 x2"
      "\<not> collinear_points x5 x6 x3"
    and conic_configuration:
      "affine_conic con"
      "x1 \<in> con"
      "x2 \<in> con"
      "x3 \<in> con"
      "x4 \<in> con"
      "x5 \<in> con"
      "x6 \<in> con"
    and opposite_side_intersections:
      "collinear_points x1 x9 x5"
      "collinear_points x1 x8 x6"
      "collinear_points x2 x9 x4"
      "collinear_points x2 x7 x6"
      "collinear_points x3 x8 x4"
      "collinear_points x3 x7 x5"
  shows "collinear_points x7 x8 x9"
  sorry

end
