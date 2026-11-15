theory putnam_2023_b6 imports Complex_Main
"HOL-Analysis.Determinants"
begin

(* uses (nat \<Rightarrow> 'n) instead of (Fin n \<Rightarrow> 'n) *)
definition putnam_2023_b6_solution :: "int \<Rightarrow> int" where
  "putnam_2023_b6_solution =
    (\<lambda>n. let h = (n + 1) div 2 in (-1) ^ nat (h + 1) * 2 * h)"
theorem putnam_2023_b6:
  fixes n :: int
  and S :: "int^'n^'n"
  assumes npos: "n > 0"
  and pncard: "CARD('n) = (nat n)"
  and hS: "\<exists>pnind::int\<Rightarrow>'n. (pnind ` {0..(n-1)} = UNIV \<and>
    (\<forall>i::int\<in>{0..(n-1)}. \<forall>j::int\<in>{0..(n-1)}.
      S$(pnind i)$(pnind j) =
        int (card {(a::nat,b::nat). int a * (i+1) + int b * (j+1) = n})))"
  shows "det S = putnam_2023_b6_solution n"
  sorry

end
