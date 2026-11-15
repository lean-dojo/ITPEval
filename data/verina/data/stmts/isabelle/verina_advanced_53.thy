(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_53,
  catalog title "minimumRightShifts": an executable bounded search computes
  the minimum number of cyclic right shifts that sorts a distinct integer
  list, or returns -1 when no rotation is sorted. This file contains no proof.
*)

theory verina_advanced_53
  imports Main
begin

definition minimumRightShifts_precond :: "int list \<Rightarrow> bool" where
  "minimumRightShifts_precond nums \<longleftrightarrow> distinct nums"

fun minimumRightShifts_isSorted :: "int list \<Rightarrow> bool" where
  "minimumRightShifts_isSorted [] = True"
| "minimumRightShifts_isSorted [x] = True"
| "minimumRightShifts_isSorted (x # y # xs) =
    (if x \<le> y
     then minimumRightShifts_isSorted (y # xs)
     else False)"

definition minimumRightShifts_rightShiftOnce ::
    "int list \<Rightarrow> int list" where
  "minimumRightShifts_rightShiftOnce xs =
    (case rev xs of
       [] \<Rightarrow> []
     | z # zs \<Rightarrow> z # rev zs)"

fun minimumRightShifts_checkShifts ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int" where
  "minimumRightShifts_checkShifts 0 n shifts current = -1"
| "minimumRightShifts_checkShifts (Suc fuel) n shifts current =
    (if shifts \<ge> n
     then -1
     else if minimumRightShifts_isSorted current
     then int shifts
     else minimumRightShifts_checkShifts
       fuel n (shifts + 1) (minimumRightShifts_rightShiftOnce current))"

definition minimumRightShifts :: "int list \<Rightarrow> int" where
  "minimumRightShifts nums =
    (let n = length nums
     in if n \<le> 1
        then 0
        else if minimumRightShifts_isSorted nums
        then 0
        else minimumRightShifts_checkShifts
          n n 1 (minimumRightShifts_rightShiftOnce nums))"

fun minimumRightShifts_rightShift ::
    "nat \<Rightarrow> int list \<Rightarrow> int list" where
  "minimumRightShifts_rightShift 0 xs = xs"
| "minimumRightShifts_rightShift (Suc k) xs =
    minimumRightShifts_rightShift
      k (minimumRightShifts_rightShiftOnce xs)"

definition minimumRightShifts_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "minimumRightShifts_postcond nums result \<longleftrightarrow>
    (let n = length nums
     in if n \<le> 1
        then result = 0
        else
          (result \<ge> 0 \<and>
           result < int n \<and>
           minimumRightShifts_isSorted
             (minimumRightShifts_rightShift (nat result) nums) \<and>
           (\<forall>j < nat result.
             \<not> minimumRightShifts_isSorted
               (minimumRightShifts_rightShift j nums)))
          \<or>
          (result = -1 \<and>
           (\<forall>k < n.
             \<not> minimumRightShifts_isSorted
               (minimumRightShifts_rightShift k nums))))"

theorem minimumRightShifts_spec_satisfied:
  assumes "minimumRightShifts_precond nums"
  shows
    "minimumRightShifts_postcond nums (minimumRightShifts nums)"
  sorry

end
