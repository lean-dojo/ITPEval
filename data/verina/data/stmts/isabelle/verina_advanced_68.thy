(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_68,
  catalog title "runLengthEncoder": an executable Unicode-scalar string
  program replaces each maximal run by its character and decimal count, under
  the no-digit precondition, together with its parser-based output contract and
  final correctness proposition. This file contains no proof.
*)

theory verina_advanced_68
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

definition lean_bit_value :: "bool \<Rightarrow> nat" where
  "lean_bit_value b = (if b then 1 else 0)"

fun lean_trit_value :: "lean_trit \<Rightarrow> nat" where
  "lean_trit_value Trit0 = 0"
| "lean_trit_value Trit1 = 1"
| "lean_trit_value Trit2 = 2"

fun lean_bits3_value :: "lean_bits3 \<Rightarrow> nat" where
  "lean_bits3_value (LeanBits3 b2 b1 b0) =
    (lean_bit_value b2 * 2 + lean_bit_value b1) * 2 +
    lean_bit_value b0"

fun lean_bits4_value :: "lean_bits4 \<Rightarrow> nat" where
  "lean_bits4_value (LeanBits4 b3 b2 b1 b0) =
    ((lean_bit_value b3 * 2 + lean_bit_value b2) * 2 +
      lean_bit_value b1) * 2 + lean_bit_value b0"

fun lean_bits5_value :: "lean_bits5 \<Rightarrow> nat" where
  "lean_bits5_value (LeanBits5 b4 b3 b2 b1 b0) =
    (((lean_bit_value b4 * 2 + lean_bit_value b3) * 2 +
       lean_bit_value b2) * 2 + lean_bit_value b1) * 2 +
    lean_bit_value b0"

fun lean_byte_value :: "lean_byte \<Rightarrow> nat" where
  "lean_byte_value (LeanByte b7 b6 b5 b4 b3 b2 b1 b0) =
    (((((((lean_bit_value b7 * 2 + lean_bit_value b6) * 2 +
          lean_bit_value b5) * 2 + lean_bit_value b4) * 2 +
        lean_bit_value b3) * 2 + lean_bit_value b2) * 2 +
      lean_bit_value b1) * 2 + lean_bit_value b0)"

fun lean_char_to_nat :: "lean_char \<Rightarrow> nat" where
  "lean_char_to_nat (BMP_Low t2 t1 t0 bits byte) =
    ((((lean_trit_value t2 * 3 + lean_trit_value t1) * 3 +
        lean_trit_value t0) * 8 + lean_bits3_value bits) * 256 +
      lean_byte_value byte)"
| "lean_char_to_nat (BMP_High bits byte) =
    57344 + lean_bits5_value bits * 256 + lean_byte_value byte"
| "lean_char_to_nat (Supplementary bits high low) =
    65536 + lean_bits4_value bits * 65536 +
    lean_byte_value high * 256 + lean_byte_value low"

definition lean_trit_of_nat :: "nat \<Rightarrow> lean_trit" where
  "lean_trit_of_nat n =
    (if n mod 3 = 0 then Trit0
     else if n mod 3 = 1 then Trit1
     else Trit2)"

definition lean_bits3_of_nat :: "nat \<Rightarrow> lean_bits3" where
  "lean_bits3_of_nat n =
    LeanBits3
      ((n div 4) mod 2 = 1)
      ((n div 2) mod 2 = 1)
      (n mod 2 = 1)"

definition lean_byte_of_nat :: "nat \<Rightarrow> lean_byte" where
  "lean_byte_of_nat n =
    LeanByte
      ((n div 128) mod 2 = 1)
      ((n div 64) mod 2 = 1)
      ((n div 32) mod 2 = 1)
      ((n div 16) mod 2 = 1)
      ((n div 8) mod 2 = 1)
      ((n div 4) mod 2 = 1)
      ((n div 2) mod 2 = 1)
      (n mod 2 = 1)"

definition lean_low_char_of_nat :: "nat \<Rightarrow> lean_char" where
  "lean_low_char_of_nat n =
    (let q = n div 2048
     in BMP_Low
          (lean_trit_of_nat (q div 9))
          (lean_trit_of_nat ((q div 3) mod 3))
          (lean_trit_of_nat (q mod 3))
          (lean_bits3_of_nat ((n div 256) mod 8))
          (lean_byte_of_nat (n mod 256)))"

definition runLengthEncoder_isDigit :: "lean_char \<Rightarrow> bool" where
  "runLengthEncoder_isDigit c \<longleftrightarrow>
    48 \<le> lean_char_to_nat c \<and> lean_char_to_nat c \<le> 57"

definition runLengthEncoder_precond :: "lean_string \<Rightarrow> bool" where
  "runLengthEncoder_precond input \<longleftrightarrow>
    list_all (\<lambda>c. \<not> runLengthEncoder_isDigit c) input"

fun runLengthEncoder_digits_go ::
    "nat \<Rightarrow> nat \<Rightarrow> lean_string" where
  "runLengthEncoder_digits_go 0 n = []"
| "runLengthEncoder_digits_go (Suc fuel) n =
    (if n < 10
     then [lean_low_char_of_nat (n + 48)]
     else
       runLengthEncoder_digits_go fuel (n div 10) @
       [lean_low_char_of_nat (n mod 10 + 48)])"

definition runLengthEncoder_numToString :: "nat \<Rightarrow> lean_string" where
  "runLengthEncoder_numToString n =
    runLengthEncoder_digits_go (Suc n) n"

fun runLengthEncoder_encode ::
    "lean_char list \<Rightarrow> lean_char option \<Rightarrow> nat \<Rightarrow>
     lean_string" where
  "runLengthEncoder_encode [] None count = []"
| "runLengthEncoder_encode [] (Some c) count =
    c # runLengthEncoder_numToString count"
| "runLengthEncoder_encode (c # rest) None count =
    runLengthEncoder_encode rest (Some c) 1"
| "runLengthEncoder_encode (c # rest) (Some current) count =
    (if c = current
     then runLengthEncoder_encode rest (Some current) (count + 1)
     else
       current # runLengthEncoder_numToString count @
       runLengthEncoder_encode rest (Some c) 1)"

fun runLengthEncoder_headOption :: "'a list \<Rightarrow> 'a option" where
  "runLengthEncoder_headOption [] = None"
| "runLengthEncoder_headOption (x # xs) = Some x"

definition runLengthEncoder :: "lean_string \<Rightarrow> lean_string" where
  "runLengthEncoder input =
    (if input = []
     then []
     else
       runLengthEncoder_encode
         (tl input) (runLengthEncoder_headOption input) 1)"

fun runLengthEncoder_parseState ::
    "lean_char list \<Rightarrow>
     lean_char option \<Rightarrow>
     nat option \<Rightarrow>
     (lean_char \<times> nat) list \<Rightarrow>
     (lean_char \<times> nat) list" where
  "runLengthEncoder_parseState [] None currentCount acc = acc"
| "runLengthEncoder_parseState [] (Some c) None acc = acc"
| "runLengthEncoder_parseState [] (Some c) (Some n) acc = (c, n) # acc"
| "runLengthEncoder_parseState (c # cs) None currentCount acc =
    (if runLengthEncoder_isDigit c
     then []
     else runLengthEncoder_parseState cs (Some c) None acc)"
| "runLengthEncoder_parseState (c # cs) (Some current) currentCount acc =
    (if runLengthEncoder_isDigit c
     then
       (let digit = lean_char_to_nat c - 48;
            newCount =
              (case currentCount of
                 None \<Rightarrow> digit
               | Some n \<Rightarrow> n * 10 + digit)
        in runLengthEncoder_parseState
             cs (Some current) (Some newCount) acc)
     else
       (let newAcc =
          (case currentCount of
             None \<Rightarrow> acc
           | Some n \<Rightarrow> (current, n) # acc)
        in runLengthEncoder_parseState cs (Some c) None newAcc))"

definition runLengthEncoder_parseEncodedString ::
    "lean_string \<Rightarrow> (lean_char \<times> nat) list" where
  "runLengthEncoder_parseEncodedString s =
    rev (runLengthEncoder_parseState s None None [])"

fun runLengthEncoder_checkPairs ::
    "lean_char list \<Rightarrow> bool \<Rightarrow> bool" where
  "runLengthEncoder_checkPairs [] nowDigit = True"
| "runLengthEncoder_checkPairs (c # cs) nowDigit =
    (if nowDigit \<and> runLengthEncoder_isDigit c
     then runLengthEncoder_checkPairs cs True
     else
       (case cs of
          [] \<Rightarrow> False
        | d # ds \<Rightarrow>
            (if runLengthEncoder_isDigit d
             then runLengthEncoder_checkPairs ds True
             else False)))"

definition runLengthEncoder_postcond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "runLengthEncoder_postcond input result \<longleftrightarrow>
    (let formatValid = runLengthEncoder_checkPairs result False;
         pairs = runLengthEncoder_parseEncodedString result;
         expanded = concat (map (\<lambda>(c, n). replicate n c) pairs);
         contentValid = (expanded = input);
         nonEmptyValid = ((input = []) = (result = []))
     in formatValid \<and> contentValid \<and> nonEmptyValid)"

theorem runLengthEncoder_spec_satisfied:
  assumes "runLengthEncoder_precond input"
  shows "runLengthEncoder_postcond input (runLengthEncoder input)"
  sorry

end
