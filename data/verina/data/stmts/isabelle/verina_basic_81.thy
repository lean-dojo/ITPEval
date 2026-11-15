(*
  Statement-only formalization of VERINA corpus artifact verina_basic_81
  (verina__isabelle__verina_basic_81), catalog title "DivisionFunction": an
  executable natural-number division program returns an integer remainder and
  quotient, with a safe zero-divisor branch and the corresponding Euclidean
  division correctness contract. This file contains no proof.
*)

theory verina_basic_81
  imports Main
begin

definition DivisionFunction_precond :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "DivisionFunction_precond x y \<longleftrightarrow> True"

definition divMod :: "nat \<Rightarrow> nat \<Rightarrow> int \<times> int" where
  "divMod x y = (int (x mod y), int (x div y))"

definition DivisionFunction :: "nat \<Rightarrow> nat \<Rightarrow> int \<times> int" where
  "DivisionFunction x y =
    (if y = 0 then (int x, 0) else divMod x y)"

definition DivisionFunction_postcond ::
    "nat \<Rightarrow> nat \<Rightarrow> (int \<times> int) \<Rightarrow> bool" where
  "DivisionFunction_postcond x y result \<longleftrightarrow>
    (let r = fst result;
         q = snd result
     in (y = 0 \<longrightarrow> r = int x \<and> q = 0) \<and>
        (y \<noteq> 0 \<longrightarrow>
          q * int y + r = int x \<and>
          (0 \<le> r \<and> r < int y) \<and>
          0 \<le> q))"

theorem DivisionFunction_spec_satisfied:
  assumes "DivisionFunction_precond x y"
  shows
    "DivisionFunction_postcond x y
      (DivisionFunction x y)"
  sorry

end
