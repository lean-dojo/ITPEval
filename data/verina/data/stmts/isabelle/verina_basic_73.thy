(*
  Statement-only formalization of VERINA corpus artifact verina_basic_73
  (verina__isabelle__verina_basic_73), catalog title "Match": an executable
  Unicode-scalar string matcher checks equal-length input against a pattern
  whose question-mark characters are wildcards, together with its length
  precondition, pointwise postcondition, and final correctness proposition.
  This file contains no proof.
*)

theory verina_basic_73
  imports Main
begin

datatype lean_trit = Trit0 | Trit1 | Trit2

datatype lean_bits3 = LeanBits3 bool bool bool

datatype lean_bits4 = LeanBits4 bool bool bool bool

datatype lean_bits5 = LeanBits5 bool bool bool bool bool

datatype lean_byte = LeanByte bool bool bool bool bool bool bool bool

datatype lean_char =
    BMP_Low lean_trit lean_trit lean_trit lean_bits3 lean_byte
  | BMP_High lean_bits5 lean_byte
  | Supplementary lean_bits4 lean_byte lean_byte

type_synonym lean_string = "lean_char list"

definition lean_nul :: lean_char where
  "lean_nul =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False False False False False False False)"

definition lean_question_mark :: lean_char where
  "lean_question_mark =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False True True True True True True)"

definition Match_toList :: "lean_string \<Rightarrow> lean_char list" where
  "Match_toList s = s"

definition Match_precond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "Match_precond s p \<longleftrightarrow>
    length (Match_toList s) = length (Match_toList p)"

fun Match_getBang ::
    "lean_char list \<Rightarrow> nat \<Rightarrow> lean_char" where
  "Match_getBang [] i = lean_nul"
| "Match_getBang (c # cs) 0 = c"
| "Match_getBang (c # cs) (Suc i) = Match_getBang cs i"

fun Match_loop ::
    "lean_char list \<Rightarrow> lean_char list \<Rightarrow> nat \<Rightarrow> bool"
    where
  "Match_loop [] p i = True"
| "Match_loop (c # cs) p i =
    (let pc = Match_getBang p i
     in if c \<noteq> pc \<and> pc \<noteq> lean_question_mark
        then False
        else Match_loop cs p (Suc i))"

definition Match :: "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "Match s p =
    Match_loop (Match_toList s) (Match_toList p) 0"

definition Match_postcond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> bool \<Rightarrow> bool"
    where
  "Match_postcond s p result \<longleftrightarrow>
    (result = True \<longleftrightarrow>
      (\<forall>n. n < length (Match_toList s) \<longrightarrow>
        (Match_getBang (Match_toList s) n =
           Match_getBang (Match_toList p) n \<or>
         Match_getBang (Match_toList p) n = lean_question_mark)))"

theorem Match_spec_satisfied:
  fixes s p :: lean_string
  assumes "Match_precond s p"
  shows "Match_postcond s p (Match s p)"
  sorry

end
