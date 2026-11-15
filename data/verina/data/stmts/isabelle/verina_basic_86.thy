(*
  Statement-only formalization of VERINA corpus artifact verina_basic_86
  (verina__isabelle__verina_basic_86), catalog title "rotate": an executable
  integer-array program rotates its input to the left by a nonnegative integer
  offset using modular indexing, together with its precondition, length-and-
  elements postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_86
  imports Main
begin

definition rotate_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "rotate_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition rotate_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "rotate_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition rotate_intEmod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "rotate_intEmod x y =
    (if y = 0 then x else x mod \<bar>y\<bar>)"

definition rotate_precond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "rotate_precond a offset \<longleftrightarrow> offset \<ge> 0"

definition rotateAux_step ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow>
      nat \<Rightarrow> int list" where
  "rotateAux_step a offset len b i =
    (let idx_int = rotate_intEmod (int i + offset) (int len);
         idx_int_adjusted =
           (if idx_int < 0 then idx_int + int len else idx_int);
         idx_nat = nat idx_int_adjusted;
         new_b = rotate_setBang b i (rotate_getBang a idx_nat)
     in new_b)"

definition rotateAux ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      int list \<Rightarrow> int list" where
  "rotateAux a offset i len b =
    foldl (rotateAux_step a offset len) b [i..<len]"

definition rotate :: "int list \<Rightarrow> int \<Rightarrow> int list" where
  "rotate a offset =
    (let len = length a;
         default_val = (if len > 0 then rotate_getBang a 0 else 0);
         b0 = replicate len default_val
     in rotateAux a offset 0 len b0)"

definition rotate_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool" where
  "rotate_postcond a offset result \<longleftrightarrow>
    length result = length a \<and>
    (\<forall>i. i < length a \<longrightarrow>
      rotate_getBang result i =
        rotate_getBang a
          (nat (rotate_intEmod
            (int i + offset) (int (length a)))))"

theorem rotate_spec_satisfied:
  fixes a :: "int list" and offset :: int
  assumes "rotate_precond a offset"
  shows "rotate_postcond a offset (rotate a offset)"
  sorry

end
