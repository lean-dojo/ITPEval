(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1933521, "Kleene's recursion theorem": every binary partial-recursive
  function on source-style program codes and natural-number inputs has a code
  whose unary evaluation is obtained by feeding that same code to the
  function. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val _ = Datatype `
  q1933521_code =
      Q1933521Zero
    | Q1933521Succ
    | Q1933521Left
    | Q1933521Right
    | Q1933521Pair q1933521_code q1933521_code
    | Q1933521Comp q1933521_code q1933521_code
    | Q1933521Prec q1933521_code q1933521_code
    | Q1933521Rfind q1933521_code
`;

val q1933521_pair_def = new_definition (
  "q1933521_pair_def",
  ``q1933521_pair a b =
      if a < b then b * b + a else a * a + a + b``
);

val q1933521_encode_def = Define`
  (q1933521_encode Q1933521Zero = 0) /\
  (q1933521_encode Q1933521Succ = 1) /\
  (q1933521_encode Q1933521Left = 2) /\
  (q1933521_encode Q1933521Right = 3) /\
  (q1933521_encode (Q1933521Pair c d) =
     4 * q1933521_pair (q1933521_encode c) (q1933521_encode d) + 4) /\
  (q1933521_encode (Q1933521Comp c d) =
     4 * q1933521_pair (q1933521_encode c) (q1933521_encode d) + 6) /\
  (q1933521_encode (Q1933521Prec c d) =
     4 * q1933521_pair (q1933521_encode c) (q1933521_encode d) + 5) /\
  (q1933521_encode (Q1933521Rfind c) =
     4 * q1933521_encode c + 7)
`;

val (q1933521_eval_rules, q1933521_eval_ind, q1933521_eval_cases) =
  Hol_reln`
    (!n. q1933521_eval Q1933521Zero n 0) /\
    (!n. q1933521_eval Q1933521Succ n (SUC n)) /\
    (!a b. q1933521_eval Q1933521Left (q1933521_pair a b) a) /\
    (!a b. q1933521_eval Q1933521Right (q1933521_pair a b) b) /\
    (!c d n a b.
       q1933521_eval c n a /\ q1933521_eval d n b ==>
       q1933521_eval
         (Q1933521Pair c d) n (q1933521_pair a b)) /\
    (!c d n a b.
       q1933521_eval d n a /\ q1933521_eval c a b ==>
       q1933521_eval (Q1933521Comp c d) n b) /\
    (!c d a b.
       q1933521_eval c a b ==>
       q1933521_eval
         (Q1933521Prec c d) (q1933521_pair a 0) b) /\
    (!c d a n r b.
       q1933521_eval
         (Q1933521Prec c d) (q1933521_pair a n) r /\
       q1933521_eval d
         (q1933521_pair a (q1933521_pair n r)) b ==>
       q1933521_eval
         (Q1933521Prec c d) (q1933521_pair a (SUC n)) b) /\
    (!c a m.
       q1933521_eval c (q1933521_pair a m) 0 ==>
       q1933521_eval
         (Q1933521Rfind c) (q1933521_pair a m) m) /\
    (!c a m z r.
       q1933521_eval c (q1933521_pair a m) z /\ z <> 0 /\
       q1933521_eval
         (Q1933521Rfind c) (q1933521_pair a (SUC m)) r ==>
       q1933521_eval
         (Q1933521Rfind c) (q1933521_pair a m) r)
  `;

val q1933521_partrec2_def = new_definition (
  "q1933521_partrec2_def",
  ``q1933521_partrec2 f <=>
      ?program. !c n y.
        (f c n = SOME y <=>
         q1933521_eval program
           (q1933521_pair (q1933521_encode c) n) y)``
);

val q1933521_kleene_recursion_theorem =
  ``!f : q1933521_code -> num -> num option.
      q1933521_partrec2 f
      ==>
      ?c. !n y.
        (q1933521_eval c n y <=> f c n = SOME y)``;
