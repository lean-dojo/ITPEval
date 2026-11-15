(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_60,
  catalog title "partitionEvensOdds": an executable recursive list program
  partitions natural numbers into order-preserving even and odd sublists,
  together with its precondition and correctness contract. This file contains
  no proof.
*)

theory verina_advanced_60
  imports Main
begin

definition partitionEvensOdds_precond :: "nat list \<Rightarrow> bool" where
  "partitionEvensOdds_precond nums \<longleftrightarrow> True"

fun partitionEvensOdds_helper ::
    "nat list \<Rightarrow> nat list \<times> nat list" where
  "partitionEvensOdds_helper [] = ([], [])"
| "partitionEvensOdds_helper (x # xs) =
    (case partitionEvensOdds_helper xs of
       (evens, odds) \<Rightarrow>
         if x mod 2 = 0
         then (x # evens, odds)
         else (evens, x # odds))"

definition partitionEvensOdds ::
    "nat list \<Rightarrow> nat list \<times> nat list" where
  "partitionEvensOdds nums = partitionEvensOdds_helper nums"

definition partitionEvensOdds_postcond ::
    "nat list \<Rightarrow> (nat list \<times> nat list) \<Rightarrow> bool" where
  "partitionEvensOdds_postcond nums result \<longleftrightarrow>
    (let evens = fst result;
         odds = snd result
     in evens @ odds =
          filter (\<lambda>n. n mod 2 = 0) nums @
          filter (\<lambda>n. n mod 2 = 1) nums \<and>
        list_all (\<lambda>n. n mod 2 = 0) evens \<and>
        list_all (\<lambda>n. n mod 2 = 1) odds)"

theorem partitionEvensOdds_spec_satisfied:
  assumes "partitionEvensOdds_precond nums"
  shows
    "partitionEvensOdds_postcond nums (partitionEvensOdds nums)"
  sorry

end
