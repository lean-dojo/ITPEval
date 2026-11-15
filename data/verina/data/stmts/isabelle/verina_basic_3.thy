(*
  Statement-only formalization of VERINA corpus artifact verina_basic_3
  (verina__isabelle__verina_basic_3), catalog title "isDivisibleBy11": an
  executable integer program tests whether its input is divisible by 11,
  together with its trivial precondition, Boolean postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_3
  imports Main
begin

definition isDivisibleBy11_precond :: "int \<Rightarrow> bool" where
  "isDivisibleBy11_precond n \<longleftrightarrow> True"

definition isDivisibleBy11 :: "int \<Rightarrow> bool" where
  "isDivisibleBy11 n = (n mod 11 = 0)"

definition isDivisibleBy11_postcond ::
    "int \<Rightarrow> bool \<Rightarrow> bool" where
  "isDivisibleBy11_postcond n result \<longleftrightarrow>
    ((result \<longrightarrow> (\<exists>k::int. n = 11 * k)) \<and>
     (\<not> result \<longrightarrow> (\<forall>k::int. n \<noteq> 11 * k)))"

theorem isDivisibleBy11_spec_satisfied:
  assumes "isDivisibleBy11_precond n"
  shows "isDivisibleBy11_postcond n (isDivisibleBy11 n)"
  sorry

end
