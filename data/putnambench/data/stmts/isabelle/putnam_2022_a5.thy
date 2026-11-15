(*
  Statement-only formalization of PutnamBench artifact putnam_2022_a5,
  concerning the greatest number of uncovered squares Alice can guarantee in
  a domino-placement game on a row of 2022 squares. This file contains no proof.
*)

theory putnam_2022_a5
  imports Main
begin

definition putnam_2022_a5_board :: "nat set" where
  "putnam_2022_a5_board = {..<2022}"

definition putnam_2022_a5_valid_move ::
    "nat set \<Rightarrow> nat set \<Rightarrow> bool" where
  "putnam_2022_a5_valid_move x y \<longleftrightarrow>
    x \<subseteq> putnam_2022_a5_board \<and>
    y \<subseteq> putnam_2022_a5_board \<and>
    ((x = y \<and>
      (\<forall>i<2021. i \<notin> x \<longrightarrow> Suc i \<in> x)) \<or>
     (\<exists>i<2021.
      i \<notin> x \<and> Suc i \<notin> x \<and>
      y = x \<union> {i, Suc i}))"

definition putnam_2022_a5_valid_game :: "nat set list \<Rightarrow> bool" where
  "putnam_2022_a5_valid_game g \<longleftrightarrow>
    g \<noteq> [] \<and>
    hd g = {} \<and>
    (\<forall>i. Suc i < length g \<longrightarrow>
      putnam_2022_a5_valid_move (g ! i) (g ! Suc i))"

definition putnam_2022_a5_conforms_to_strategy ::
    "nat set list \<Rightarrow> (nat set \<Rightarrow> nat set) \<Rightarrow> bool" where
  "putnam_2022_a5_conforms_to_strategy g s \<longleftrightarrow>
    (\<forall>i. Suc i < length g \<longrightarrow> even i \<longrightarrow>
      g ! Suc i = s (g ! i))"

definition putnam_2022_a5_guaranteed :: "nat set" where
  "putnam_2022_a5_guaranteed =
    {n. \<exists>s :: nat set \<Rightarrow> nat set.
      (\<forall>x. x \<subseteq> putnam_2022_a5_board \<longrightarrow>
        putnam_2022_a5_valid_move x (s x)) \<and>
      (\<forall>g.
        putnam_2022_a5_valid_game g \<longrightarrow>
        putnam_2022_a5_conforms_to_strategy g s \<longrightarrow>
        (\<exists>gh x.
          g = gh @ [x] \<and>
          n \<le> card (putnam_2022_a5_board - x)))}"

definition putnam_2022_a5_solution :: nat where
  "putnam_2022_a5_solution = 290"

theorem putnam_2022_a5:
  shows "putnam_2022_a5_solution \<in> putnam_2022_a5_guaranteed \<and>
    (\<forall>n\<in>putnam_2022_a5_guaranteed.
      n \<le> putnam_2022_a5_solution)"
  sorry

end
