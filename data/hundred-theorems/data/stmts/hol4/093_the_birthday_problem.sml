(*
  Statement-only formalization of Hundred Theorems artifact
  hundred-theorems__hol4__093, cataloged as "The Birthday Problem": more than
  half of all birthday assignments for 23 people have a collision, whereas
  fewer than half do for 22 people. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val the_birthday_problem =
  ``2 *
      CARD
        {birthdays |
           LENGTH birthdays = 23 /\
           EVERY (\day. day < 365) birthdays /\
           ~ALL_DISTINCT birthdays} >
      CARD
        {birthdays |
           LENGTH birthdays = 23 /\
           EVERY (\day. day < 365) birthdays} /\
    2 *
      CARD
        {birthdays |
           LENGTH birthdays = 22 /\
           EVERY (\day. day < 365) birthdays /\
           ~ALL_DISTINCT birthdays} <
      CARD
        {birthdays |
           LENGTH birthdays = 22 /\
           EVERY (\day. day < 365) birthdays}``;
