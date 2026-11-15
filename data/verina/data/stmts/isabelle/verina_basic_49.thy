(*
  Statement-only formalization of VERINA corpus artifact verina_basic_49
  (verina__isabelle__verina_basic_49), catalog title "findFirstOdd": an
  executable integer-array program indexes the input, finds the first odd
  entry, and returns its natural-number index when present, together with its
  nonempty-array precondition, postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_49
  imports Main
begin

definition isOdd :: "int \<Rightarrow> bool" where
  "isOdd x \<longleftrightarrow> x mod 2 \<noteq> 0"

definition findFirstOdd_precond :: "int list \<Rightarrow> bool" where
  "findFirstOdd_precond a \<longleftrightarrow> length a > 0"

definition findFirstOdd_indexed ::
    "int list \<Rightarrow> (int \<times> nat) list" where
  "findFirstOdd_indexed a = zip a [0..<length a]"

fun findFirstOdd_find ::
    "(int \<times> nat) list \<Rightarrow> (int \<times> nat) option" where
  "findFirstOdd_find [] = None"
| "findFirstOdd_find (p # ps) =
    (if isOdd (fst p) then Some p else findFirstOdd_find ps)"

definition findFirstOdd :: "int list \<Rightarrow> nat option" where
  "findFirstOdd a =
    map_option snd (findFirstOdd_find (findFirstOdd_indexed a))"

definition findFirstOdd_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "findFirstOdd_getBang a i =
    (if i < length a then a ! i else 0)"

definition findFirstOdd_postcond ::
    "int list \<Rightarrow> nat option \<Rightarrow> bool" where
  "findFirstOdd_postcond a result \<longleftrightarrow>
    (case result of
       Some idx \<Rightarrow>
         idx < length a \<and>
         isOdd (findFirstOdd_getBang a idx) \<and>
         (\<forall>j<idx. \<not> isOdd (findFirstOdd_getBang a j))
     | None \<Rightarrow>
         (\<forall>i<length a. \<not> isOdd (findFirstOdd_getBang a i)))"

theorem findFirstOdd_spec_satisfied:
  assumes "findFirstOdd_precond a"
  shows "findFirstOdd_postcond a (findFirstOdd a)"
  sorry

end
