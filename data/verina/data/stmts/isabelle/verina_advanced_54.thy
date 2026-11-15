(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_54,
  catalog title "missingNumber": triangular-sum subtraction computes the
  missing natural number from a distinct list whose entries are bounded by
  its length, with the full range-membership postcondition. This file contains
  no proof.
*)

theory verina_advanced_54
  imports Main
begin

definition missingNumber_precond :: "nat list \<Rightarrow> bool" where
  "missingNumber_precond nums \<longleftrightarrow>
    list_all (\<lambda>x. x \<le> length nums) nums \<and>
    distinct nums"

definition missingNumber :: "nat list \<Rightarrow> nat" where
  "missingNumber nums =
    (let n = length nums;
         expectedSum = (n * (n + 1)) div 2;
         actualSum = foldl (+) 0 nums
     in expectedSum - actualSum)"

definition missingNumber_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "missingNumber_postcond nums result \<longleftrightarrow>
    (let n = length nums
     in result \<in> set [0..<n + 1] \<and>
        result \<notin> set nums \<and>
        (\<forall>x.
          x \<in> set [0..<n + 1] \<longrightarrow>
          x \<noteq> result \<longrightarrow>
          x \<in> set nums))"

theorem missingNumber_spec_satisfied:
  assumes "missingNumber_precond nums"
  shows "missingNumber_postcond nums (missingNumber nums)"
  sorry

end
