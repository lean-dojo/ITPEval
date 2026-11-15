(*
  Statement-only formalization of Desargues's theorem from Hundred Theorems
  item 087. Points use homogeneous coordinates, and collinearity is the
  vanishing of the corresponding 3-by-3 determinant. The nondegeneracy and
  incidence hypotheses match the HOL Light benchmark. This file contains no
  proof.
*)

theory Desargues_Theorem
  imports Complex_Main
begin

datatype projective_point = Projective_Point real real real

fun bracket ::
    "projective_point \<Rightarrow> projective_point \<Rightarrow>
      projective_point \<Rightarrow> real"
  where
    "bracket (Projective_Point x1 x2 x3)
        (Projective_Point y1 y2 y3)
        (Projective_Point z1 z2 z3) =
      x1 * (y2 * z3 - y3 * z2)
        - x2 * (y1 * z3 - y3 * z1)
        + x3 * (y1 * z2 - y2 * z1)"

definition collinear ::
    "projective_point \<Rightarrow> projective_point \<Rightarrow>
      projective_point \<Rightarrow> bool"
  where
    "collinear A B C \<longleftrightarrow> bracket A B C = 0"

theorem desargues_direct:
  fixes A A' B B' C C' P Q R S :: projective_point
  assumes "\<not> collinear A' B S"
    and "\<not> collinear A P C"
    and "\<not> collinear A P R"
    and "\<not> collinear A C B"
    and "\<not> collinear A B R"
    and "\<not> collinear C' P A'"
    and "\<not> collinear C' P B"
    and "\<not> collinear C' P B'"
    and "\<not> collinear C' A' S"
    and "\<not> collinear C' A' B'"
    and "\<not> collinear P C A'"
    and "\<not> collinear P C B"
    and "\<not> collinear P A' R"
    and "\<not> collinear P B Q"
    and "\<not> collinear P Q B'"
    and "\<not> collinear C B S"
    and "\<not> collinear A' Q B'"
    and "collinear P A' A"
    and "collinear P B B'"
    and "collinear P C' C"
    and "collinear B C Q"
    and "collinear B' C' Q"
    and "collinear A R C"
    and "collinear A' C' R"
    and "collinear B S A"
    and "collinear A' S B'"
  shows "collinear Q S R"
  sorry

end
