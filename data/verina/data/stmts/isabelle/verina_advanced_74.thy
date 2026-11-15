(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_74,
  catalog title "solution": an executable nested-fold program sums, over all
  contiguous subarrays of a natural-number list, the square of each subarray's
  number of distinct values, together with its bounded-input correctness
  contract. This file contains no proof.
*)

theory verina_advanced_74
  imports Main
begin

definition solution_precond :: "nat list \<Rightarrow> bool" where
  "solution_precond nums \<longleftrightarrow>
    1 \<le> length nums \<and>
    length nums \<le> 100 \<and>
    list_all (\<lambda>x. 1 \<le> x \<and> x \<le> 100) nums"

definition solution_subarray ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "solution_subarray nums i j = take (j - i + 1) (drop i nums)"

definition solution_distinctCount :: "nat list \<Rightarrow> nat" where
  "solution_distinctCount xs =
    length
      (foldl
        (\<lambda>seen x. if x \<in> set seen then seen else x # seen)
        [] xs)"

definition solution_innerSum :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "solution_innerSum nums i =
    foldl
      (\<lambda>acc d.
        let subarr = solution_subarray nums i (i + d);
            cnt = solution_distinctCount subarr
        in acc + cnt * cnt)
      0 [0..<(length nums - i)]"

definition solution :: "nat list \<Rightarrow> nat" where
  "solution nums =
    foldl
      (\<lambda>acc i. acc + solution_innerSum nums i)
      0 [0..<length nums]"

definition solution_getSubarray_local ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "solution_getSubarray_local nums i j =
    take (j - i + 1) (drop i nums)"

definition solution_distinctCount_local :: "nat list \<Rightarrow> nat" where
  "solution_distinctCount_local xs =
    length
      (foldl
        (\<lambda>seen x. if x \<in> set seen then seen else x # seen)
        [] xs)"

definition solution_square_local :: "nat \<Rightarrow> nat" where
  "solution_square_local n = n * n"

definition solution_expectedSum :: "nat list \<Rightarrow> nat" where
  "solution_expectedSum nums =
    (let n = length nums
     in foldl
       (\<lambda>outerSum i.
         let innerSum =
           foldl
             (\<lambda>currentInnerSum d.
               let j = i + d;
                   subarr = solution_getSubarray_local nums i j;
                   count = solution_distinctCount_local subarr
               in currentInnerSum + solution_square_local count)
             0 [0..<(n - i)]
         in outerSum + innerSum)
       0 [0..<n])"

definition solution_postcond :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "solution_postcond nums result \<longleftrightarrow>
    (solution_precond nums \<longrightarrow>
      result \<ge> 0 \<and> result = solution_expectedSum nums)"

theorem solution_spec_satisfied:
  "solution_postcond nums (solution nums)"
  sorry

end
