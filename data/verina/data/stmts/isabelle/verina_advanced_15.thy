(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_15,
  catalog title "increasingTriplet": an executable two-threshold list scan
  decides whether three integer entries at increasing indices have strictly
  increasing values, together with its correctness contract. This file
  contains no proof.
*)

theory verina_advanced_15
  imports Main
begin

definition increasingTriplet_precond :: "int list \<Rightarrow> bool" where
  "increasingTriplet_precond nums \<longleftrightarrow> True"

fun increasingTriplet_loop ::
    "int list \<Rightarrow> int option \<Rightarrow> int option \<Rightarrow> bool" where
  "increasingTriplet_loop [] first second = False"
| "increasingTriplet_loop (x # rest) None second =
    increasingTriplet_loop rest (Some x) None"
| "increasingTriplet_loop (x # rest) (Some first) second =
    (if x \<le> first
     then increasingTriplet_loop rest (Some x) second
     else
       (case second of
          None \<Rightarrow> increasingTriplet_loop rest (Some first) (Some x)
        | Some second' \<Rightarrow>
            (if x \<le> second'
             then increasingTriplet_loop rest (Some first) (Some x)
             else True)))"

definition increasingTriplet :: "int list \<Rightarrow> bool" where
  "increasingTriplet nums =
    (if length nums < 3
     then False
     else increasingTriplet_loop nums None None)"

definition increasingTriplet_zipIdx ::
    "int list \<Rightarrow> (int \<times> nat) list" where
  "increasingTriplet_zipIdx nums = zip nums [0..<length nums]"

definition increasingTriplet_postcond ::
    "int list \<Rightarrow> bool \<Rightarrow> bool" where
  "increasingTriplet_postcond nums result \<longleftrightarrow>
    (let nums' = increasingTriplet_zipIdx nums
     in
       (result \<longrightarrow>
         list_ex
           (\<lambda>(x, i).
             list_ex
               (\<lambda>(y, j).
                 list_ex
                   (\<lambda>(z, k).
                     i < j \<and> j < k \<and> x < y \<and> y < z)
                   nums')
               nums')
           nums') \<and>
       (\<not> result \<longrightarrow>
         list_all
           (\<lambda>(x, i).
             list_all
               (\<lambda>(y, j).
                 list_all
                   (\<lambda>(z, k).
                     i \<ge> j \<or> j \<ge> k \<or> x \<ge> y \<or> y \<ge> z)
                   nums')
               nums')
           nums'))"

theorem increasingTriplet_spec_satisfied:
  assumes "increasingTriplet_precond nums"
  shows "increasingTriplet_postcond nums (increasingTriplet nums)"
  sorry

end
