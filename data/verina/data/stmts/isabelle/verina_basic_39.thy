(*
  Statement-only formalization of VERINA corpus artifact verina_basic_39
  (verina__isabelle__verina_basic_39), catalog title "rotateRight": an
  executable integer-list program rotates by a natural-number offset using
  integer modular indexing, together with its unconditional precondition,
  length-and-index postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_39
  imports Main
begin

definition rotateRight_headD :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "rotateRight_headD xs d =
    (case xs of [] \<Rightarrow> d | x # _ \<Rightarrow> x)"

definition rotateRight_getD ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "rotateRight_getD xs i d =
    (if i < length xs then xs ! i else d)"

fun rotateRight_getOpt :: "int list \<Rightarrow> nat \<Rightarrow> int option" where
  "rotateRight_getOpt [] i = None"
| "rotateRight_getOpt (x # xs) 0 = Some x"
| "rotateRight_getOpt (x # xs) (Suc i) = rotateRight_getOpt xs i"

definition rotateRight_precond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "rotateRight_precond l n \<longleftrightarrow> True"

definition rotateRight :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "rotateRight l n =
    (let len = length l
     in if len = 0 then l
        else
          map
            (\<lambda>i.
              let idx_int =
                (int i - int n + int len) mod int len;
                  idx_nat = nat idx_int
              in rotateRight_getD
                   l idx_nat (rotateRight_headD l 0))
            [0..<len])"

definition rotateRight_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> bool" where
  "rotateRight_postcond l n result \<longleftrightarrow>
    length result = length l \<and>
    (\<forall>i < length l.
      let len = length l;
          rotated_index =
            nat ((int i - int n + int len) mod int len)
      in rotateRight_getOpt result i =
         rotateRight_getOpt l rotated_index)"

theorem rotateRight_spec_satisfied:
  assumes "rotateRight_precond l n"
  shows "rotateRight_postcond l n (rotateRight l n)"
  sorry

end
