(*
  Statement-only formalization of "Feuerbach's Theorem" from Hundred Theorems item 029.
  Using real coordinate pairs for the Euclidean plane, it states that for a nondegenerate
  triangle the circle through the side midpoints is tangent to a circle tangent to all
  three side-lines. This file contains no proof.
*)

theory Feuerbach_Theorem
  imports Complex_Main
begin

type_synonym plane_point = "real \<times> real"

definition euclidean_distance :: "plane_point \<Rightarrow> plane_point \<Rightarrow> real" where
  "euclidean_distance p q =
    sqrt ((fst p - fst q) ^ 2 + (snd p - snd q) ^ 2)"

definition plane_midpoint :: "plane_point \<Rightarrow> plane_point \<Rightarrow> plane_point" where
  "plane_midpoint p q =
    ((fst p + fst q) / 2, (snd p + snd q) / 2)"

definition collinear_points :: "plane_point \<Rightarrow> plane_point \<Rightarrow> plane_point \<Rightarrow> bool" where
  "collinear_points p q r \<longleftrightarrow>
    (fst q - fst p) * (snd r - snd p) =
    (snd q - snd p) * (fst r - fst p)"

definition perpendicular_at ::
    "plane_point \<Rightarrow> plane_point \<Rightarrow> plane_point \<Rightarrow> plane_point \<Rightarrow> bool" where
  "perpendicular_at p q center foot \<longleftrightarrow>
    (fst p - fst q) * (fst center - fst foot) +
    (snd p - snd q) * (snd center - snd foot) = 0"

theorem feuerbach:
  fixes a b c mbc mac mab pbc pac pab ncenter icenter :: plane_point
    and nradius iradius :: real
  assumes nondegenerate: "\<not> collinear_points a b c"
    and midpoint_ab: "plane_midpoint a b = mab"
    and midpoint_bc: "plane_midpoint b c = mbc"
    and midpoint_ca: "plane_midpoint c a = mac"
    and nine_point_radius_bc: "euclidean_distance ncenter mbc = nradius"
    and nine_point_radius_ca: "euclidean_distance ncenter mac = nradius"
    and nine_point_radius_ab: "euclidean_distance ncenter mab = nradius"
    and tangent_radius_bc: "euclidean_distance icenter pbc = iradius"
    and tangent_radius_ca: "euclidean_distance icenter pac = iradius"
    and tangent_radius_ab: "euclidean_distance icenter pab = iradius"
    and contact_ab: "collinear_points a b pab"
    and perpendicular_ab: "perpendicular_at a b icenter pab"
    and contact_bc: "collinear_points b c pbc"
    and perpendicular_bc: "perpendicular_at b c icenter pbc"
    and contact_ac: "collinear_points a c pac"
    and perpendicular_ac: "perpendicular_at a c icenter pac"
  shows "(ncenter = icenter \<and> nradius = iradius) \<or>
    (\<exists>!x :: plane_point.
      euclidean_distance ncenter x = nradius \<and>
      euclidean_distance icenter x = iradius)"
  sorry

end
