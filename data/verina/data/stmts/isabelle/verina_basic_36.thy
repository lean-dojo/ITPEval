(*
  Statement-only formalization of VERINA corpus artifact verina_basic_36
  (verina__isabelle__verina_basic_36), catalog title "replaceWithColon": an
  executable Unicode-scalar string program replaces every ASCII space, comma,
  or dot with a colon and leaves all other characters unchanged, together with
  its unconditional precondition, length-preserving pointwise postcondition,
  and final correctness proposition. This file contains no proof.
*)

theory verina_basic_36
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

definition lean_space :: lean_char where
  "lean_space =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False True False False False False False)"

definition lean_comma :: lean_char where
  "lean_comma =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False True False True True False False)"

definition lean_dot :: lean_char where
  "lean_dot =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False True False True True True False)"

definition lean_colon :: lean_char where
  "lean_colon =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False True True True False True False)"

definition isSpaceCommaDot :: "lean_char \<Rightarrow> bool" where
  "isSpaceCommaDot c \<longleftrightarrow>
    c = lean_space \<or> c = lean_comma \<or> c = lean_dot"

definition replaceWithColon_precond :: "lean_string \<Rightarrow> bool" where
  "replaceWithColon_precond s \<longleftrightarrow> True"

definition replaceWithColon_toList ::
    "lean_string \<Rightarrow> lean_char list" where
  "replaceWithColon_toList s = s"

definition replaceWithColon_mk ::
    "lean_char list \<Rightarrow> lean_string" where
  "replaceWithColon_mk chars = chars"

definition replaceWithColon :: "lean_string \<Rightarrow> lean_string" where
  "replaceWithColon s =
    (let cs = replaceWithColon_toList s;
         cs' =
           map
             (\<lambda>c. if isSpaceCommaDot c then lean_colon else c)
             cs
     in replaceWithColon_mk cs')"

fun replaceWithColon_getBang ::
    "lean_char list \<Rightarrow> nat \<Rightarrow> lean_char" where
  "replaceWithColon_getBang [] i = lean_nul"
| "replaceWithColon_getBang (c # cs) 0 = c"
| "replaceWithColon_getBang (c # cs) (Suc i) =
    replaceWithColon_getBang cs i"

definition replaceWithColon_postcond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "replaceWithColon_postcond s result \<longleftrightarrow>
    (let cs = replaceWithColon_toList s;
         cs' = replaceWithColon_toList result
     in length result = length s \<and>
        (\<forall>i. i < length s \<longrightarrow>
          ((isSpaceCommaDot (replaceWithColon_getBang cs i)
              \<longrightarrow>
            replaceWithColon_getBang cs' i = lean_colon) \<and>
           (\<not> isSpaceCommaDot (replaceWithColon_getBang cs i)
              \<longrightarrow>
            replaceWithColon_getBang cs' i =
              replaceWithColon_getBang cs i))))"

theorem replaceWithColon_spec_satisfied:
  assumes "replaceWithColon_precond s"
  shows "replaceWithColon_postcond s (replaceWithColon s)"
  sorry

end
