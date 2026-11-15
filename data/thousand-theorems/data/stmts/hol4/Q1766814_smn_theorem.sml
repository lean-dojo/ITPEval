(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1766814, "Smn theorem": a total computable specialization operation on
  program codes fixes the first component of a paired input while preserving
  the represented partial computation. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

Datatype:
  q1766814_code =
    Q1766814Zero
  | Q1766814Succ
  | Q1766814Left
  | Q1766814Right
  | Q1766814Pair q1766814_code q1766814_code
  | Q1766814Comp q1766814_code q1766814_code
  | Q1766814Prec q1766814_code q1766814_code
  | Q1766814Rfind q1766814_code
End

val q1766814_pair_def = new_definition (
  "q1766814_pair_def",
  ``q1766814_pair a b =
      if a < b then b * b + a else a * a + a + b``
);

val q1766814_encode_def = Define`
  (q1766814_encode Q1766814Zero = 0) /\
  (q1766814_encode Q1766814Succ = 1) /\
  (q1766814_encode Q1766814Left = 2) /\
  (q1766814_encode Q1766814Right = 3) /\
  (q1766814_encode (Q1766814Pair c d) =
     4 * q1766814_pair (q1766814_encode c) (q1766814_encode d) + 4) /\
  (q1766814_encode (Q1766814Comp c d) =
     4 * q1766814_pair (q1766814_encode c) (q1766814_encode d) + 6) /\
  (q1766814_encode (Q1766814Prec c d) =
     4 * q1766814_pair (q1766814_encode c) (q1766814_encode d) + 5) /\
  (q1766814_encode (Q1766814Rfind c) =
     4 * q1766814_encode c + 7)
`;

val (q1766814_eval_rules, q1766814_eval_ind, q1766814_eval_cases) =
  Hol_reln`
    (!n. q1766814_eval Q1766814Zero n 0) /\
    (!n. q1766814_eval Q1766814Succ n (SUC n)) /\
    (!a b. q1766814_eval Q1766814Left (q1766814_pair a b) a) /\
    (!a b. q1766814_eval Q1766814Right (q1766814_pair a b) b) /\
    (!c d n a b.
       q1766814_eval c n a /\ q1766814_eval d n b ==>
       q1766814_eval (Q1766814Pair c d) n (q1766814_pair a b)) /\
    (!c d n a b.
       q1766814_eval d n a /\ q1766814_eval c a b ==>
       q1766814_eval (Q1766814Comp c d) n b) /\
    (!c d a b.
       q1766814_eval c a b ==>
       q1766814_eval (Q1766814Prec c d) (q1766814_pair a 0) b) /\
    (!c d a n r b.
       q1766814_eval (Q1766814Prec c d) (q1766814_pair a n) r /\
       q1766814_eval d
         (q1766814_pair a (q1766814_pair n r)) b ==>
       q1766814_eval
         (Q1766814Prec c d) (q1766814_pair a (SUC n)) b) /\
    (!c a m.
       q1766814_eval c (q1766814_pair a m) 0 ==>
       q1766814_eval (Q1766814Rfind c) (q1766814_pair a m) m) /\
    (!c a m z r.
       q1766814_eval c (q1766814_pair a m) z /\ z <> 0 /\
       q1766814_eval
         (Q1766814Rfind c) (q1766814_pair a (SUC m)) r ==>
       q1766814_eval (Q1766814Rfind c) (q1766814_pair a m) r)
  `;

val q1766814_computable2_def = new_definition (
  "q1766814_computable2_def",
  ``q1766814_computable2 f <=>
      ?p. !c n.
        q1766814_eval p
          (q1766814_pair (q1766814_encode c) n)
          (q1766814_encode (f c n))``
);

val q1766814_smn_theorem =
  ``?f : q1766814_code -> num -> q1766814_code.
      q1766814_computable2 f /\
      !c n x y.
        (q1766814_eval (f c n) x y <=>
         q1766814_eval c (q1766814_pair n x) y)``;
