(*
  Statement-only formalization of VERINA corpus artifact verina_basic_40
  (verina__isabelle__verina_basic_40), catalog title "secondSmallest": an
  executable integer-array scan returns the second-smallest distinct value,
  together with its precondition, postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_40
  imports Main
begin

definition intList_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "intList_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition secondSmallest_precond :: "int list \<Rightarrow> bool" where
  "secondSmallest_precond s \<longleftrightarrow>
    length s > 1 \<and>
    (\<exists>i<length s. \<exists>j<length s.
      intList_getBang s i \<noteq> intList_getBang s j)"

fun secondSmallestAux_fuel ::
    "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat
      \<Rightarrow> nat option \<Rightarrow> int" where
  "secondSmallestAux_fuel 0 s i minIdx secondIdx =
    (case secondIdx of
       None \<Rightarrow> 0
     | Some si \<Rightarrow> intList_getBang s si)"
| "secondSmallestAux_fuel (Suc fuel) s i minIdx secondIdx =
    (let x = intList_getBang s i;
         m = intList_getBang s minIdx
     in case secondIdx of
          None \<Rightarrow>
            (if x < m
             then secondSmallestAux_fuel fuel s (i + 1) i (Some minIdx)
             else if x > m
                  then secondSmallestAux_fuel fuel s (i + 1) minIdx (Some i)
                  else secondSmallestAux_fuel fuel s (i + 1) minIdx None)
        | Some si \<Rightarrow>
            (let smin = intList_getBang s si
             in if x < m
                then secondSmallestAux_fuel fuel s (i + 1) i (Some minIdx)
                else if x < smin \<and> x > m
                     then
                       secondSmallestAux_fuel fuel s (i + 1) minIdx (Some i)
                     else
                       secondSmallestAux_fuel
                         fuel s (i + 1) minIdx (Some si)))"

definition secondSmallestAux ::
    "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> int"
    where
  "secondSmallestAux s i minIdx secondIdx =
    secondSmallestAux_fuel (length s - i) s i minIdx secondIdx"

definition secondSmallest :: "int list \<Rightarrow> int" where
  "secondSmallest s = secondSmallestAux s 1 0 None"

definition secondSmallest_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "secondSmallest_postcond s result \<longleftrightarrow>
    (\<exists>i<length s. intList_getBang s i = result) \<and>
    (\<exists>j<length s.
      intList_getBang s j < result \<and>
      (\<forall>k<length s.
        intList_getBang s k \<noteq> intList_getBang s j
        \<longrightarrow> intList_getBang s k \<ge> result))"

theorem secondSmallest_spec_satisfied:
  assumes "secondSmallest_precond s"
  shows "secondSmallest_postcond s (secondSmallest s)"
  sorry

end
