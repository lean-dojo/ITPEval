theory putnam_2015_b5 imports Complex_Main
"HOL-Combinatorics.Permutations"
begin

definition putnam_2015_b5_solution :: int where
  "putnam_2015_b5_solution \<equiv> 4"
(* 4 *)
theorem putnam_2015_b5:
  fixes P :: "nat \<Rightarrow> nat"
  defines "P \<equiv> \<lambda>n. card {pi :: nat \<Rightarrow> nat.
    pi permutes {1..n} \<and>
    (\<forall>i\<in>{1..n}. \<forall>j\<in>{1..n}.
      abs (int i - int j) = 1 \<longrightarrow>
      abs (int (pi i) - int (pi j)) \<le> 2)}"
  shows "\<forall>n::nat \<ge> 2.
    int (P (n + 5)) - int (P (n + 4)) - int (P (n + 3)) + int (P n)
      = putnam_2015_b5_solution"
  sorry

end
