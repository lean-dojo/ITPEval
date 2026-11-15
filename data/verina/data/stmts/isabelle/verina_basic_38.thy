(*
  Statement-only formalization of VERINA corpus artifact verina_basic_38
  (verina__isabelle__verina_basic_38), catalog title "allCharactersSame": an
  executable Unicode-scalar string test returns true for the empty string and
  otherwise exactly when every remaining character equals the first, together
  with its unconditional precondition, pairwise-equality postcondition, and
  final correctness proposition. This file contains no proof.
*)

theory verina_basic_38
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

definition allCharactersSame_precond :: "lean_string \<Rightarrow> bool" where
  "allCharactersSame_precond s \<longleftrightarrow> True"

definition allCharactersSame_toList ::
    "lean_string \<Rightarrow> lean_char list" where
  "allCharactersSame_toList s = s"

definition allCharactersSame :: "lean_string \<Rightarrow> bool" where
  "allCharactersSame s =
    (case allCharactersSame_toList s of
       [] \<Rightarrow> True
     | c # cs \<Rightarrow> list_all (\<lambda>x. x = c) cs)"

fun allCharactersSame_pairwise_eq :: "lean_char list \<Rightarrow> bool" where
  "allCharactersSame_pairwise_eq [] = True"
| "allCharactersSame_pairwise_eq (c # cs) =
    (list_all (\<lambda>x. c = x) cs \<and>
     allCharactersSame_pairwise_eq cs)"

fun allCharactersSame_getBang ::
    "lean_char list \<Rightarrow> nat \<Rightarrow> lean_char" where
  "allCharactersSame_getBang [] i = lean_nul"
| "allCharactersSame_getBang (c # cs) 0 = c"
| "allCharactersSame_getBang (c # cs) (Suc i) =
    allCharactersSame_getBang cs i"

definition allCharactersSame_postcond ::
    "lean_string \<Rightarrow> bool \<Rightarrow> bool" where
  "allCharactersSame_postcond s result \<longleftrightarrow>
    (let cs = allCharactersSame_toList s
     in (result \<longrightarrow> allCharactersSame_pairwise_eq cs) \<and>
        (\<not> result \<longrightarrow>
          cs \<noteq> [] \<and>
          list_ex
            (\<lambda>x. x \<noteq> allCharactersSame_getBang cs 0)
            cs))"

theorem allCharactersSame_spec_satisfied:
  assumes "allCharactersSame_precond s"
  shows "allCharactersSame_postcond s (allCharactersSame s)"
  sorry

end
