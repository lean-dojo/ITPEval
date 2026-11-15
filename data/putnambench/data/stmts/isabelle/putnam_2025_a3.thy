(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a3
  (putnambench__isabelle__putnam_2025_a3): in the no-repetition game on
  length-n strings over {0, 1, 2}, where a move changes one digit by 1, Bob
  has a winning strategy for every positive n. This file contains no proof.
*)

theory putnam_2025_a3
  imports Main
begin

type_synonym game_string = "nat list"

definition valid_game_string :: "nat \<Rightarrow> game_string \<Rightarrow> bool" where
  "valid_game_string n s \<longleftrightarrow>
    length s = n \<and> set s \<subseteq> {..<3}"

definition initial_state :: "nat \<Rightarrow> game_string" where
  "initial_state n = replicate n 0"

definition is_valid_move ::
    "nat \<Rightarrow> game_string \<Rightarrow> game_string \<Rightarrow> bool" where
  "is_valid_move n s1 s2 \<longleftrightarrow>
    valid_game_string n s1 \<and>
    valid_game_string n s2 \<and>
    (\<exists>!i. i < n \<and> s1 ! i \<noteq> s2 ! i) \<and>
    (\<forall>i<n. s1 ! i \<noteq> s2 ! i \<longrightarrow>
      s1 ! i + 1 = s2 ! i \<or> s2 ! i + 1 = s1 ! i)"

primrec move_chain ::
    "nat \<Rightarrow> game_string \<Rightarrow> game_string list \<Rightarrow> bool" where
  "move_chain n s [] = True"
| "move_chain n s (t # ts) =
    (is_valid_move n s t \<and> move_chain n t ts)"

definition is_valid_game_play :: "nat \<Rightarrow> game_string list \<Rightarrow> bool" where
  "is_valid_game_play n play \<longleftrightarrow>
    move_chain n (initial_state n) play \<and>
    distinct (initial_state n # play)"

inductive has_winning_strategy :: "nat \<Rightarrow> game_string list \<Rightarrow> bool" where
  win:
    "is_valid_game_play n (play @ [s]) \<Longrightarrow>
     (\<And>s'. is_valid_game_play n (play @ [s, s']) \<Longrightarrow>
       has_winning_strategy n (play @ [s, s'])) \<Longrightarrow>
     has_winning_strategy n play"

definition alice_has_winning_strategy :: "nat \<Rightarrow> bool" where
  "alice_has_winning_strategy n \<longleftrightarrow>
    has_winning_strategy n []"

definition putnam_2025_a3_solution :: "nat \<Rightarrow> bool" where
  "putnam_2025_a3_solution n \<longleftrightarrow> False"

theorem putnam_2025_a3:
  fixes n :: nat
  assumes "1 \<le> n"
  shows
    "putnam_2025_a3_solution n \<longleftrightarrow>
      alice_has_winning_strategy n"
  sorry

end
