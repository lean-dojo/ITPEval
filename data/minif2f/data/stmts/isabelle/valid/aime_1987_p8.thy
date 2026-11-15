(*
  Authors: Albert Qiaochu Jiang
*)

theory aime_1987_p8 imports
  Complex_Main
begin

theorem aime_1987_p8:
  shows "(0 < (112::nat) \<and>
      (\<exists>! k::nat. (8::real) / 15 <
        of_nat 112 / of_nat (112 + k) \<and>
        of_nat 112 / of_nat (112 + k) < 7 / 13))
    \<and> (\<forall> n::nat. (0 < n \<and>
      (\<exists>! k::nat. (8::real) / 15 <
        of_nat n / of_nat (n + k) \<and>
        of_nat n / of_nat (n + k) < 7 / 13))
      \<longrightarrow> n \<le> 112)"
  by sorry

end
