(*
  Statement-only formalization of miniF2F test problem mathd_numbertheory_345:
  the sum of the integers from 2000 through 2006 has remainder zero modulo 7.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_numbertheory_345 =
  ``(2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) MOD 7 = 0``;
