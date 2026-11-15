(*
  Statement-only formalization of VERINA corpus artifact verina_basic_56,
  catalog title "copy": the executable program copies a bounded segment from
  a source integer array into a destination array by descending indexed
  updates and states its precondition/postcondition correctness contract.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val copy_getBang_def = new_definition (
  "copy_getBang_def",
  ``copy_getBang (xs : int list) (index : num) =
      if index < LENGTH xs then EL index xs else (0 : int)``
);

val copy_precond_def = new_definition (
  "copy_precond_def",
  ``copy_precond
      (src : int list) (sStart : num)
      (dest : int list) (dStart : num) (len : num) <=>
      sStart + len <= LENGTH src /\
      dStart + len <= LENGTH dest``
);

val updateSegment_def = Define `
  (updateSegment
      (r : int list) (src : int list)
      (sStart : num) (dStart : num) 0 =
     r) /\
  (updateSegment r src sStart dStart (SUC n) =
     let rNew =
       LUPDATE
         (copy_getBang src (sStart + n))
         (dStart + n)
         r
     in
       updateSegment rNew src sStart dStart n)
`;

val copy_def = new_definition (
  "copy_def",
  ``copy
      (src : int list) (sStart : num)
      (dest : int list) (dStart : num) (len : num) =
      if len = 0 then
        dest
      else
        updateSegment dest src sStart dStart len``
);

val copy_postcond_def = new_definition (
  "copy_postcond_def",
  ``copy_postcond
      (src : int list) (sStart : num)
      (dest : int list) (dStart : num) (len : num)
      (result : int list) <=>
      LENGTH result = LENGTH dest /\
      (!i : num.
         i < dStart ==>
         copy_getBang result i = copy_getBang dest i) /\
      (!i : num.
         dStart + len <= i ==>
         i < LENGTH result ==>
         copy_getBang result i = copy_getBang dest i) /\
      (!i : num.
         i < len ==>
         copy_getBang result (dStart + i) =
         copy_getBang src (sStart + i))``
);

val copy_spec_satisfied =
  ``!(src : int list) (sStart : num)
      (dest : int list) (dStart : num) (len : num).
      copy_precond src sStart dest dStart len ==>
      copy_postcond
        src sStart dest dStart len
        (copy src sStart dest dStart len)``;
