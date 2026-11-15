(*
  Statement-only formalization of VERINA corpus artifact verina_basic_108,
  catalog title "below_zero": an executable left fold builds all integer
  partial sums from zero and a recursive scan reports whether any sum is
  negative, together with the complete correctness contract. This file
  contains no proof.
*)

theory verina_basic_108
  imports Main
begin

definition below_zero_precond :: "int list \<Rightarrow> bool" where
  "below_zero_precond operations \<longleftrightarrow> True"

definition below_zero_getLastD :: "int list \<Rightarrow> int" where
  "below_zero_getLastD xs =
    (case rev xs of
       [] \<Rightarrow> 0
     | x # rest \<Rightarrow> x)"

definition buildS :: "int list \<Rightarrow> int list" where
  "buildS operations =
    foldl
      (\<lambda>acc op. acc @ [below_zero_getLastD acc + op])
      [0] operations"

fun below_zero_check_negative :: "int list \<Rightarrow> bool" where
  "below_zero_check_negative [] = False"
| "below_zero_check_negative (x # xs) =
    (if x < 0 then True else below_zero_check_negative xs)"

definition below_zero :: "int list \<Rightarrow> (int list \<times> bool)" where
  "below_zero operations =
    (let s = buildS operations;
         result = below_zero_check_negative s
     in (s, result))"

definition below_zero_getOpt ::
    "int list \<Rightarrow> nat \<Rightarrow> int option" where
  "below_zero_getOpt xs i =
    (if i < length xs then Some (xs ! i) else None)"

definition below_zero_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "below_zero_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition below_zero_postcond ::
    "int list \<Rightarrow> (int list \<times> bool) \<Rightarrow> bool" where
  "below_zero_postcond operations output \<longleftrightarrow>
    (let s = fst output;
         result = snd output
     in length s = length operations + 1 \<and>
        below_zero_getOpt s 0 = Some 0 \<and>
        list_all
          (\<lambda>i.
            below_zero_getOpt s (i + 1) =
              Some
                (below_zero_getBang s i +
                 below_zero_getBang operations i))
          [0..<(length s - 1)] \<and>
        (result = True \<longrightarrow>
          list_ex
            (\<lambda>i. below_zero_getBang s (i + 1) < 0)
            [0..<length operations]) \<and>
        (result = False \<longrightarrow>
          list_all (\<lambda>x. x \<ge> 0) s))"

theorem below_zero_spec_satisfied:
  assumes "below_zero_precond operations"
  shows "below_zero_postcond operations (below_zero operations)"
  sorry

end
