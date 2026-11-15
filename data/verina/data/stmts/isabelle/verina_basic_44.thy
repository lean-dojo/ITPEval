(*
  Statement-only formalization of VERINA corpus artifact verina_basic_44
  (verina__isabelle__verina_basic_44), catalog title "isOddAtIndexOdd": an
  executable integer-array program checks that every entry at an odd index is
  odd, together with its unconditional precondition, Boolean postcondition,
  and final correctness proposition. This file contains no proof.
*)

theory verina_basic_44
  imports Main
begin

definition isOdd :: "int \<Rightarrow> bool" where
  "isOdd n \<longleftrightarrow> n mod 2 = 1"

definition isOddAtIndexOdd_precond :: "int list \<Rightarrow> bool" where
  "isOddAtIndexOdd_precond a \<longleftrightarrow> True"

definition isOddAtIndexOdd_indexedArray ::
    "int list \<Rightarrow> (nat \<times> int) list" where
  "isOddAtIndexOdd_indexedArray a = zip [0..<length a] a"

definition isOddAtIndexOdd :: "int list \<Rightarrow> bool" where
  "isOddAtIndexOdd a =
    (let indexedArray = isOddAtIndexOdd_indexedArray a
     in list_all
          (\<lambda>(i, x). \<not> isOdd (int i) \<or> isOdd x)
          indexedArray)"

definition isOddAtIndexOdd_postcond ::
    "int list \<Rightarrow> bool \<Rightarrow> bool" where
  "isOddAtIndexOdd_postcond a result \<longleftrightarrow>
    (result \<longleftrightarrow>
      (\<forall>i<length a. isOdd (int i) \<longrightarrow> isOdd (a ! i)))"

theorem isOddAtIndexOdd_spec_satisfied:
  assumes "isOddAtIndexOdd_precond a"
  shows "isOddAtIndexOdd_postcond a (isOddAtIndexOdd a)"
  sorry

end
