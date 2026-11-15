(*
  Statement-only formalization of miniF2F test problem amc12b_2021_p9: a real logarithmic
  expression involving 20, 40, 80, and 160 evaluates to 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val _ = new_theory "hello";

val amc12b_2021_p9 =
  ``(ln (&80) / ln (&2)) / (ln (&2) / ln (&40)) -
    (ln (&160) / ln (&2)) / (ln (&2) / ln (&20)) = 2``;

val _ = export_theory();
