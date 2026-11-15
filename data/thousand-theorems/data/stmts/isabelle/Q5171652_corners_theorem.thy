(*
  Statement-only formalization of thousand-theorems corpus artifact Q5171652
  (thousand-theorems__isabelle__Q5171652), "Corners theorem": every sufficiently
  dense finite subset of an initial natural-number square contains a nontrivial
  additive corner once the side length meets the explicit bound. This file
  contains no proof.
*)

theory Q5171652_corners_theorem
  imports Complex_Main
begin

definition q5171652_nat_floor :: "real \<Rightarrow> nat" where
  "q5171652_nat_floor x = nat (floor x)"

definition q5171652_nat_ceiling :: "real \<Rightarrow> nat" where
  "q5171652_nat_ceiling x = nat (ceiling x)"

definition q5171652_step_bound :: "nat \<Rightarrow> nat" where
  "q5171652_step_bound m = m * 4 ^ m"

definition q5171652_initial_bound :: "real \<Rightarrow> nat \<Rightarrow> nat" where
  "q5171652_initial_bound delta l =
    max 7 (max l
      (q5171652_nat_floor (ln (100 / delta ^ 5) / ln 4) + 1))"

definition q5171652_regularity_bound :: "real \<Rightarrow> nat \<Rightarrow> nat" where
  "q5171652_regularity_bound delta l =
    (let m =
      (q5171652_step_bound ^^ q5171652_nat_floor (4 / delta ^ 5))
        (q5171652_initial_bound delta l)
     in m * 16 ^ m)"

definition q5171652_triangle_removal_bound :: "real \<Rightarrow> real" where
  "q5171652_triangle_removal_bound delta =
    (let c = q5171652_nat_ceiling (4 / delta)
     in min
       (inverse (2 * (real c) ^ 3))
       ((1 - min 1 delta / 4) *
        (delta / (16 * real (q5171652_regularity_bound (delta / 8) c))) ^ 3))"

definition q5171652_corners_bound :: "real \<Rightarrow> nat" where
  "q5171652_corners_bound delta =
    q5171652_nat_floor
      (inverse (q5171652_triangle_removal_bound (delta / 9) * 27)) + 1"

definition q5171652_corner_free :: "(nat \<times> nat) set \<Rightarrow> bool" where
  "q5171652_corner_free A \<longleftrightarrow>
    (\<forall>x1 y1 x2 y2.
      (x1, y1) \<in> A \<and>
      (x1, y2) \<in> A \<and>
      (x2, y1) \<in> A \<and>
      x1 + y2 = x2 + y1
      \<longrightarrow> x1 = x2)"

theorem corners_theorem_nat:
  fixes epsilon :: real
    and n :: nat
    and A :: "(nat \<times> nat) set"
  assumes epsilon_pos: "0 < epsilon"
    and bound: "q5171652_corners_bound (epsilon / 9) \<le> n"
    and contained: "A \<subseteq> {..<n} \<times> {..<n}"
    and dense: "epsilon * (real n) ^ 2 \<le> real (card A)"
  shows "\<not> q5171652_corner_free A"
  sorry

end
