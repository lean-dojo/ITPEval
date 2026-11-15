(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_52,
  catalog title "minOperations": an executable reverse-list scan counts the
  minimum removals from the end needed to collect every natural number from
  1 through k under the source presence precondition, with k = 0 returning
  zero. This file contains no proof.
*)

theory verina_advanced_52
  imports Main
begin

definition minOperations_target_nums :: "nat \<Rightarrow> nat list" where
  "minOperations_target_nums k = map Suc [0..<k]"

definition minOperations_precond :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "minOperations_precond nums k \<longleftrightarrow>
    list_all (\<lambda>n. n \<in> set nums) (minOperations_target_nums k)"

fun minOperations_loop ::
    "nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
     nat \<Rightarrow> nat" where
  "minOperations_loop [] collected collected_count ops k = ops"
| "minOperations_loop (head # tail) collected collected_count ops k =
    (let ops' = ops + 1
     in if 0 < head \<and> head \<le> k \<and> head \<notin> set collected
        then
          (let collected' = head # collected;
               collected_count' = collected_count + 1
           in if collected_count' = k
              then ops'
              else
                minOperations_loop
                  tail collected' collected_count' ops' k)
        else minOperations_loop tail collected collected_count ops' k)"

definition minOperations :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "minOperations nums k =
    (if k = 0
     then 0
     else minOperations_loop (rev nums) [] 0 0 k)"

definition minOperations_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "minOperations_postcond nums k result \<longleftrightarrow>
    (let processed = take result (rev nums);
         target_nums = minOperations_target_nums k;
         collected_all =
           list_all (\<lambda>n. n \<in> set processed) target_nums;
         is_minimal =
           (if 0 < result
            then
              (let processed_minus_one =
                 take (result - 1) (rev nums)
               in \<not>
                 list_all
                   (\<lambda>n. n \<in> set processed_minus_one)
                   target_nums)
            else k = 0)
     in collected_all \<and> is_minimal)"

theorem minOperations_spec_satisfied:
  assumes "minOperations_precond nums k"
  shows "minOperations_postcond nums k (minOperations nums k)"
  sorry

end
