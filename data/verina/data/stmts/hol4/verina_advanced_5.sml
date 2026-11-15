(*
  Statement-only formalization of VERINA artifact verina_advanced_5,
  cataloged as "addTwoNumbers": the executable program adds two nonempty
  reverse-decimal digit lists using digitwise carry propagation. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val listToNat_def = Define `
  (listToNat ([] : num list) = 0) /\
  (listToNat (d::ds) = d + 10 * listToNat ds)
`;

val getLastNat_def = new_definition (
  "getLastNat_def",
  ``getLastNat (xs : num list) =
      case REVERSE xs of
        [] => 0
      | d::_ => d``
);

val addTwoNumbers_precond_def = new_definition (
  "addTwoNumbers_precond_def",
  ``addTwoNumbers_precond (l1 : num list) (l2 : num list) <=>
      0 < LENGTH l1 /\
      0 < LENGTH l2 /\
      EVERY (\d. d < 10) l1 /\
      EVERY (\d. d < 10) l2 /\
      (getLastNat l1 <> 0 \/ l1 = [0]) /\
      (getLastNat l2 <> 0 \/ l2 = [0])``
);

val addTwoNumbersAux_def = Define `
  (addTwoNumbersAux
      ([] : num list) ([] : num list) (carry : num) =
     if carry = 0 then [] else [carry]) /\
  (addTwoNumbersAux (h1::t1) ([] : num list) carry =
     let sum = h1 + carry
     in
       (sum MOD 10)::addTwoNumbersAux t1 [] (sum DIV 10)) /\
  (addTwoNumbersAux ([] : num list) (h2::t2) carry =
     let sum = h2 + carry
     in
       (sum MOD 10)::addTwoNumbersAux [] t2 (sum DIV 10)) /\
  (addTwoNumbersAux (h1::t1) (h2::t2) carry =
     let sum = h1 + h2 + carry
     in
       (sum MOD 10)::addTwoNumbersAux t1 t2 (sum DIV 10))
`;

val addTwoNumbers_def = new_definition (
  "addTwoNumbers_def",
  ``addTwoNumbers (l1 : num list) (l2 : num list) =
      addTwoNumbersAux l1 l2 0``
);

val addTwoNumbers_postcond_def = new_definition (
  "addTwoNumbers_postcond_def",
  ``addTwoNumbers_postcond
      (l1 : num list) (l2 : num list) (result : num list) <=>
      listToNat result = listToNat l1 + listToNat l2 /\
      EVERY (\d. d < 10) result /\
      (getLastNat result <> 0 \/
       (l1 = [0] /\ l2 = [0] /\ result = [0]))``
);

val addTwoNumbers_spec_satisfied =
  ``!(l1 : num list) (l2 : num list).
      addTwoNumbers_precond l1 l2 ==>
      addTwoNumbers_postcond l1 l2 (addTwoNumbers l1 l2)``;
