(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a5
  (putnambench__isabelle__putnam_2024_a5): the center displacement r in
  [0,8] minimizing the probability that a random chord of the radius-9 circle
  meets the radius-1 disk centered at (r,0) is exactly r = 0. This file
  contains no proof.
*)

theory putnam_2024_a5
  imports Complex_Main
begin

type_synonym putnam_2024_a5_point = "real \<times> real"

definition putnam_2024_a5_circle_point ::
    "real \<Rightarrow> putnam_2024_a5_point" where
  "putnam_2024_a5_circle_point s =
    (9 * cos (2 * pi * s), 9 * sin (2 * pi * s))"

definition putnam_2024_a5_line ::
    "putnam_2024_a5_point \<Rightarrow> putnam_2024_a5_point \<Rightarrow>
      putnam_2024_a5_point set" where
  "putnam_2024_a5_line P Q =
    {X. \<exists>u :: real.
      X =
        (fst P + u * (fst Q - fst P),
          snd P + u * (snd Q - snd P))}"

definition putnam_2024_a5_is_intersecting ::
    "real \<Rightarrow> putnam_2024_a5_point \<Rightarrow>
      putnam_2024_a5_point \<Rightarrow> bool" where
  "putnam_2024_a5_is_intersecting r P Q \<longleftrightarrow>
    putnam_2024_a5_line P Q \<inter>
      {X. (fst X - r) ^ 2 + (snd X) ^ 2 = 1} \<noteq> {}"

definition putnam_2024_a5_lebesgue_outer ::
    "putnam_2024_a5_point set \<Rightarrow> real" where
  "putnam_2024_a5_lebesgue_outer A =
    Inf
      {suminf (\<lambda>n. max 0 (b n - a n) * max 0 (d n - c n)) |
        a b c d.
          summable
            (\<lambda>n. max 0 (b n - a n) * max 0 (d n - c n)) \<and>
          A \<subseteq>
            (\<Union>n :: nat.
              {(x, y).
                a n < x \<and> x < b n \<and>
                c n < y \<and> y < d n})}"

definition putnam_2024_a5_prob_intersect :: "real \<Rightarrow> real" where
  "putnam_2024_a5_prob_intersect r =
    putnam_2024_a5_lebesgue_outer
      {p :: real \<times> real.
        fst p \<in> {0..1} \<and>
        snd p \<in> {0..1} \<and>
        putnam_2024_a5_is_intersecting r
          (putnam_2024_a5_circle_point (fst p))
          (putnam_2024_a5_circle_point (snd p))}"

definition putnam_2024_a5_solution :: "real set" where
  "putnam_2024_a5_solution = {0}"

theorem putnam_2024_a5:
  shows
    "{r :: real.
      r \<in> {0..8} \<and>
      putnam_2024_a5_prob_intersect r =
        (INF x\<in>{0..8}. putnam_2024_a5_prob_intersect x)}
      = putnam_2024_a5_solution"
  sorry

end
