(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_67,
  catalog title "runLengthEncode": an executable Unicode-scalar string program
  groups consecutive equal characters into positive run lengths, together with
  its precondition, decoder, postcondition, and correctness contract. This file
  contains no proof.
*)

theory verina_advanced_67
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

definition runLengthEncode_precond :: "lean_string \<Rightarrow> bool" where
  "runLengthEncode_precond s \<longleftrightarrow> True"

fun runLengthEncode_encodeAux ::
    "(lean_char \<times> nat) list \<Rightarrow>
     lean_char list \<Rightarrow>
     (lean_char \<times> nat) list" where
  "runLengthEncode_encodeAux acc [] = rev acc"
| "runLengthEncode_encodeAux [] (h # t) =
    runLengthEncode_encodeAux [(h, 1)] t"
| "runLengthEncode_encodeAux ((ch, count) # accTail) (h # t) =
    (if ch = h
     then runLengthEncode_encodeAux ((ch, count + 1) # accTail) t
     else
       runLengthEncode_encodeAux
         ((h, 1) # (ch, count) # accTail) t)"

definition runLengthEncode ::
    "lean_string \<Rightarrow> (lean_char \<times> nat) list" where
  "runLengthEncode s = runLengthEncode_encodeAux [] s"

fun decodeRLE :: "(lean_char \<times> nat) list \<Rightarrow> lean_string" where
  "decodeRLE [] = []"
| "decodeRLE ((ch, cnt) # tail) =
    replicate cnt ch @ decodeRLE tail"

definition runLengthEncode_postcond ::
    "lean_string \<Rightarrow> (lean_char \<times> nat) list \<Rightarrow> bool" where
  "runLengthEncode_postcond s result \<longleftrightarrow>
    (\<forall>pair \<in> set result. snd pair > 0) \<and>
    (\<forall>i. i < length result - 1 \<longrightarrow>
      fst (result ! i) \<noteq> fst (result ! (i + 1))) \<and>
    decodeRLE result = s"

theorem runLengthEncode_spec_satisfied:
  assumes "runLengthEncode_precond s"
  shows "runLengthEncode_postcond s (runLengthEncode s)"
  sorry

end
