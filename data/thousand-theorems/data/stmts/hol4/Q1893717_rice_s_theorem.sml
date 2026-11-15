(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1893717, "Rice's theorem": a computably decidable semantic property of
  unary partial-recursive functions that contains one such function contains
  every unary partial-recursive function. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val _ = Datatype `
  q1893717_code =
      Q1893717Zero
    | Q1893717Succ
    | Q1893717Left
    | Q1893717Right
    | Q1893717Pair q1893717_code q1893717_code
    | Q1893717Comp q1893717_code q1893717_code
    | Q1893717Prec q1893717_code q1893717_code
    | Q1893717Rfind q1893717_code
`;

val q1893717_pair_def = new_definition (
  "q1893717_pair_def",
  ``q1893717_pair a b =
      if a < b then b * b + a else a * a + a + b``
);

val q1893717_encode_def = Define`
  (q1893717_encode Q1893717Zero = 0) /\
  (q1893717_encode Q1893717Succ = 1) /\
  (q1893717_encode Q1893717Left = 2) /\
  (q1893717_encode Q1893717Right = 3) /\
  (q1893717_encode (Q1893717Pair c d) =
     4 * q1893717_pair (q1893717_encode c) (q1893717_encode d) + 4) /\
  (q1893717_encode (Q1893717Comp c d) =
     4 * q1893717_pair (q1893717_encode c) (q1893717_encode d) + 6) /\
  (q1893717_encode (Q1893717Prec c d) =
     4 * q1893717_pair (q1893717_encode c) (q1893717_encode d) + 5) /\
  (q1893717_encode (Q1893717Rfind c) =
     4 * q1893717_encode c + 7)
`;

val (q1893717_eval_rules, q1893717_eval_ind, q1893717_eval_cases) =
  Hol_reln`
    (!n. q1893717_eval Q1893717Zero n 0) /\
    (!n. q1893717_eval Q1893717Succ n (SUC n)) /\
    (!a b. q1893717_eval Q1893717Left (q1893717_pair a b) a) /\
    (!a b. q1893717_eval Q1893717Right (q1893717_pair a b) b) /\
    (!c d n a b.
       q1893717_eval c n a /\ q1893717_eval d n b ==>
       q1893717_eval (Q1893717Pair c d) n (q1893717_pair a b)) /\
    (!c d n a b.
       q1893717_eval d n a /\ q1893717_eval c a b ==>
       q1893717_eval (Q1893717Comp c d) n b) /\
    (!c d a b.
       q1893717_eval c a b ==>
       q1893717_eval (Q1893717Prec c d) (q1893717_pair a 0) b) /\
    (!c d a n r b.
       q1893717_eval (Q1893717Prec c d) (q1893717_pair a n) r /\
       q1893717_eval d
         (q1893717_pair a (q1893717_pair n r)) b ==>
       q1893717_eval
         (Q1893717Prec c d) (q1893717_pair a (SUC n)) b) /\
    (!c a m.
       q1893717_eval c (q1893717_pair a m) 0 ==>
       q1893717_eval (Q1893717Rfind c) (q1893717_pair a m) m) /\
    (!c a m z r.
       q1893717_eval c (q1893717_pair a m) z /\ z <> 0 /\
       q1893717_eval
         (Q1893717Rfind c) (q1893717_pair a (SUC m)) r ==>
       q1893717_eval (Q1893717Rfind c) (q1893717_pair a m) r)
  `;

val q1893717_partrec_def = new_definition (
  "q1893717_partrec_def",
  ``q1893717_partrec f <=>
      ?program. !x y.
        (f x y <=> q1893717_eval program x y)``
);

val q1893717_computable_pred_def = new_definition (
  "q1893717_computable_pred_def",
  ``q1893717_computable_pred predicate <=>
      ?program. !c y.
        (q1893717_eval program (q1893717_encode c) y <=>
         if predicate c then y = 1 else y = 0)``
);

val q1893717_rice_theorem =
  ``!(C : (num -> num -> bool) -> bool)
      (f g : num -> num -> bool).
      q1893717_computable_pred (\c. C (q1893717_eval c)) /\
      q1893717_partrec f /\
      q1893717_partrec g /\
      C f
      ==>
      C g``;
