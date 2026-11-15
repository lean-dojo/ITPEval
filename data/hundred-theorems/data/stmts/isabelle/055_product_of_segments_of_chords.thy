(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Intersecting Chord Theorem\<close>

theory Chord_Segments
imports Triangle.Triangle
begin

subsection \<open>Preliminaries\<close>

lemma betweenE_if_dist_leq:
  fixes A B X :: "'a::euclidean_space"
  assumes "between (A, B) X"
  assumes "dist A X \<le> dist B X"
  obtains u where "1 / 2 \<le> u" "u \<le> 1" and "X = u *\<^sub>R A + (1 - u) *\<^sub>R B"
  by sorry

lemma dist_geq_iff_midpoint_in_between:
  fixes A B X :: "'a::euclidean_space"
  assumes "between (A, B) X"
  shows "dist A X \<le> dist B X \<longleftrightarrow> between (X, B) (midpoint A B)"
  by sorry

subsection \<open>Properties of Chord Segments\<close>

lemma chord_property:
  fixes S C :: "'a :: euclidean_space"
  assumes "dist C S = dist C T"
  assumes "between (S, T) X"
  shows "dist S X * dist X T = (dist C S) ^ 2 - (dist C X) ^ 2"
  by sorry

theorem product_of_chord_segments:
  fixes S\<^sub>1 T\<^sub>1 S\<^sub>2 T\<^sub>2 X C :: "'a :: euclidean_space"
  assumes "between (S\<^sub>1, T\<^sub>1) X" "between (S\<^sub>2, T\<^sub>2) X"
  assumes "dist C S\<^sub>1 = r" "dist C T\<^sub>1 = r"
  assumes "dist C S\<^sub>2 = r" "dist C T\<^sub>2 = r"
  shows "dist S\<^sub>1 X * dist X T\<^sub>1 = dist S\<^sub>2 X * dist X T\<^sub>2"
  by sorry

end
