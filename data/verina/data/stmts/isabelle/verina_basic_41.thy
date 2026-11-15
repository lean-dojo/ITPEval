(*
  Statement-only formalization of VERINA corpus artifact verina_basic_41
  (verina__isabelle__verina_basic_41), catalog title
  "hasOnlyOneDistinctElement": an executable integer-array scan compares every
  entry with the first, together with its nonempty precondition,
  pairwise-equality postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_41
  imports Main
begin

fun hasOnlyOneDistinctElement_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "hasOnlyOneDistinctElement_getBang [] i = 0"
| "hasOnlyOneDistinctElement_getBang (x # xs) 0 = x"
| "hasOnlyOneDistinctElement_getBang (x # xs) (Suc i) =
    hasOnlyOneDistinctElement_getBang xs i"

definition hasOnlyOneDistinctElement_toList ::
    "int list \<Rightarrow> int list" where
  "hasOnlyOneDistinctElement_toList a = a"

definition hasOnlyOneDistinctElement_precond ::
    "int list \<Rightarrow> bool" where
  "hasOnlyOneDistinctElement_precond a \<longleftrightarrow> length a > 0"

fun hasOnlyOneDistinctElement_loop ::
    "int \<Rightarrow> int list \<Rightarrow> bool" where
  "hasOnlyOneDistinctElement_loop firstElement [] = True"
| "hasOnlyOneDistinctElement_loop firstElement (x # xs) =
    (if x = firstElement
     then hasOnlyOneDistinctElement_loop firstElement xs
     else False)"

definition hasOnlyOneDistinctElement :: "int list \<Rightarrow> bool" where
  "hasOnlyOneDistinctElement a =
    (if length a = 0 then True
     else
       let firstElement = hasOnlyOneDistinctElement_getBang a 0
       in hasOnlyOneDistinctElement_loop firstElement (drop 1 a))"

fun hasOnlyOneDistinctElement_pairwise_eq ::
    "int list \<Rightarrow> bool" where
  "hasOnlyOneDistinctElement_pairwise_eq [] = True"
| "hasOnlyOneDistinctElement_pairwise_eq (x # xs) =
    (list_all (\<lambda>y. x = y) xs \<and>
     hasOnlyOneDistinctElement_pairwise_eq xs)"

definition hasOnlyOneDistinctElement_postcond ::
    "int list \<Rightarrow> bool \<Rightarrow> bool" where
  "hasOnlyOneDistinctElement_postcond a result \<longleftrightarrow>
    (let l = hasOnlyOneDistinctElement_toList a
     in (result \<longrightarrow>
           hasOnlyOneDistinctElement_pairwise_eq l) \<and>
        (\<not> result \<longrightarrow>
           list_ex
             (\<lambda>x.
               x \<noteq> hasOnlyOneDistinctElement_getBang l 0)
             l))"

theorem hasOnlyOneDistinctElement_spec_satisfied:
  assumes "hasOnlyOneDistinctElement_precond a"
  shows
    "hasOnlyOneDistinctElement_postcond
      a (hasOnlyOneDistinctElement a)"
  sorry

end
