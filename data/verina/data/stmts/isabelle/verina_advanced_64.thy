(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_64,
  catalog title "removeElement": an executable recursive natural-list program
  removes every occurrence of a target while preserving the order of all
  remaining entries, together with its precondition and exact indexed
  correctness contract. This file contains no proof.
*)

theory verina_advanced_64
  imports Main
begin

definition removeElement_precond :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "removeElement_precond lst target \<longleftrightarrow> True"

fun removeElement_helper :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "removeElement_helper [] target = []"
| "removeElement_helper (x # xs) target =
    (let rest = removeElement_helper xs target
     in if x = target then rest else x # rest)"

definition removeElement :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "removeElement lst target = removeElement_helper lst target"

definition removeElement_zipIdx ::
    "nat list \<Rightarrow> (nat \<times> nat) list" where
  "removeElement_zipIdx xs = zip xs [0..<length xs]"

fun removeElement_getOpt :: "nat list \<Rightarrow> nat \<Rightarrow> nat option" where
  "removeElement_getOpt [] i = None"
| "removeElement_getOpt (x # xs) 0 = Some x"
| "removeElement_getOpt (x # xs) (Suc i) = removeElement_getOpt xs i"

definition removeElement_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "removeElement_postcond lst target result \<longleftrightarrow>
    (let expected = filter (\<lambda>x. x \<noteq> target) lst
     in
       list_all
         (\<lambda>(x, i).
           case removeElement_getOpt expected i of
             Some y \<Rightarrow> x = y
           | None \<Rightarrow> False)
         (removeElement_zipIdx result) \<and>
       length result = length expected)"

theorem removeElement_spec_satisfied:
  assumes "removeElement_precond lst target"
  shows
    "removeElement_postcond lst target (removeElement lst target)"
  sorry

end
