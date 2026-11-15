(*
  Statement-only formalization of VERINA corpus artifact verina_basic_73,
  catalog title "Match": the executable Unicode-string program checks equal-
  length strings position by position, allowing question marks in the pattern
  to match any character, and states its Boolean correctness contract. This
  file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val Match_isUnicodeScalar_def = new_definition (
  "Match_isUnicodeScalar_def",
  ``Match_isUnicodeScalar (c : num) <=>
      c < 1114112 /\ ~(55296 <= c /\ c <= 57343)``
);

val Match_isUnicodeString_def = new_definition (
  "Match_isUnicodeString_def",
  ``Match_isUnicodeString (s : num list) <=>
      EVERY Match_isUnicodeScalar s``
);

val Match_getBang_def = new_definition (
  "Match_getBang_def",
  ``Match_getBang (xs : num list) (index : num) =
      if index < LENGTH xs then EL index xs else 0``
);

val Match_precond_def = new_definition (
  "Match_precond_def",
  ``Match_precond (s : num list) (p : num list) <=>
      LENGTH s = LENGTH p``
);

val Match_loopFuel_def = Define `
  (Match_loopFuel
      0
      (s : num list)
      (p : num list)
      (i : num) =
     T) /\
  (Match_loopFuel
      (SUC fuel)
      s
      p
      i =
     if i < LENGTH s then
       if Match_getBang s i <> Match_getBang p i /\
          Match_getBang p i <> 63 then
         F
       else
         Match_loopFuel fuel s p (i + 1)
     else
       T)
`;

val Match_loop_def = new_definition (
  "Match_loop_def",
  ``Match_loop
      (s : num list) (p : num list) (i : num) =
      Match_loopFuel (SUC (LENGTH s - i)) s p i``
);

val Match_def = new_definition (
  "Match_def",
  ``Match (s : num list) (p : num list) =
      Match_loop s p 0``
);

val Match_postcond_def = new_definition (
  "Match_postcond_def",
  ``Match_postcond
      (s : num list) (p : num list) (result : bool) <=>
      (result = T <=>
       !n : num.
         n < LENGTH s ==>
         (Match_getBang s n = Match_getBang p n \/
          Match_getBang p n = 63))``
);

val Match_spec_satisfied =
  ``!(s : num list) (p : num list).
      Match_isUnicodeString s ==>
      Match_isUnicodeString p ==>
      Match_precond s p ==>
      Match_postcond s p (Match s p)``;
