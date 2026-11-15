(*
  Statement-only formalization of VERINA corpus artifact verina_basic_15,
  catalog title "containsConsecutiveNumbers": an executable integer-array
  program returns true exactly when some adjacent pair consists of an integer
  followed by that integer plus one, together with its trivial precondition
  and Boolean correctness contract. This file contains no proof.
*)

theory verina_basic_15
  imports Main
begin

fun containsConsecutiveNumbers_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "containsConsecutiveNumbers_getBang [] i = 0"
| "containsConsecutiveNumbers_getBang (x # xs) 0 = x"
| "containsConsecutiveNumbers_getBang (x # xs) (Suc i) =
    containsConsecutiveNumbers_getBang xs i"

definition containsConsecutiveNumbers_precond :: "int list \<Rightarrow> bool" where
  "containsConsecutiveNumbers_precond a \<longleftrightarrow> True"

definition containsConsecutiveNumbers :: "int list \<Rightarrow> bool" where
  "containsConsecutiveNumbers a =
    (if length a \<le> 1 then False
     else
       list_ex
         (\<lambda>(i, x).
           i < length a - 1 \<and>
           x + 1 = containsConsecutiveNumbers_getBang a (i + 1))
         (zip [0..<length a] a))"

definition containsConsecutiveNumbers_postcond ::
    "int list \<Rightarrow> bool \<Rightarrow> bool" where
  "containsConsecutiveNumbers_postcond a result \<longleftrightarrow>
    ((\<exists>i.
       i < length a - 1 \<and>
       containsConsecutiveNumbers_getBang a i + 1 =
         containsConsecutiveNumbers_getBang a (i + 1))
      \<longleftrightarrow> result)"

theorem containsConsecutiveNumbers_spec_satisfied:
  assumes "containsConsecutiveNumbers_precond a"
  shows "containsConsecutiveNumbers_postcond a (containsConsecutiveNumbers a)"
  sorry

end
