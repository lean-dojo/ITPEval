(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_9,
  catalog title "countSumDivisibleBy": an executable natural-number program
  counts the values below a bound whose decimal digit sum is divisible by a
  positive divisor, together with its precondition and correctness contract.
  This file contains no proof.
*)

theory verina_advanced_9
  imports Main
begin

fun sumOfDigits_go :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sumOfDigits_go 0 n acc = acc"
| "sumOfDigits_go (Suc fuel) n acc =
    (if n = 0
     then acc
     else sumOfDigits_go fuel (n div 10) (acc + n mod 10))"

definition sumOfDigits :: "nat \<Rightarrow> nat" where
  "sumOfDigits x = sumOfDigits_go (Suc x) x 0"

definition countSumDivisibleBy_precond :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "countSumDivisibleBy_precond n d \<longleftrightarrow> d > 0"

definition isSumDivisibleBy :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "isSumDivisibleBy x d \<longleftrightarrow> sumOfDigits x mod d = 0"

fun countSumDivisibleBy_go ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "countSumDivisibleBy_go 0 acc d = acc"
| "countSumDivisibleBy_go (Suc i) acc d =
    (let acc' = (if isSumDivisibleBy i d then acc + 1 else acc)
     in countSumDivisibleBy_go i acc' d)"

definition countSumDivisibleBy :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "countSumDivisibleBy n d = countSumDivisibleBy_go n 0 d"

definition countSumDivisibleBy_postcond ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "countSumDivisibleBy_postcond n d result \<longleftrightarrow>
    length
        (filter
          (\<lambda>x. x < n \<and> sumOfDigits x mod d = 0)
          [0..<n]) -
      result =
      0 \<and>
    result \<le>
      length
        (filter
          (\<lambda>x. x < n \<and> sumOfDigits x mod d = 0)
          [0..<n])"

theorem countSumDivisibleBy_spec_satisfied:
  assumes "countSumDivisibleBy_precond n d"
  shows
    "countSumDivisibleBy_postcond n d
      (countSumDivisibleBy n d)"
  sorry

end
