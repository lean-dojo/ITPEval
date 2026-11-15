(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a4
  (putnambench__isabelle__putnam_2024_a4): the primes greater than 5 admitting
  an integer geometric-power sequence whose terms can be reordered so that
  consecutive differences are constant modulo the prime. The solution set is
  {7}. This file contains no proof.
*)

theory putnam_2024_a4
  imports Complex_Main
begin

definition putnam_2024_a4_solution :: "nat set" where
  "putnam_2024_a4_solution = {7}"

theorem putnam_2024_a4:
  shows
    "{p :: nat.
      prime p \<and>
      5 < p \<and>
      (\<exists>a r :: int.
        1 \<le> r \<and>
        r \<le> int (p - 1) \<and>
        (\<exists>e :: nat \<Rightarrow> nat.
          bij_betw e {0..p - 5} {0..p - 5} \<and>
          (\<forall>n :: nat.
            1 \<le> n \<and> n \<le> p - 5 \<longrightarrow>
              int p dvd a ^ (e n) - a ^ (e (n - 1)) - r)))}
      = putnam_2024_a4_solution"
  sorry

end
