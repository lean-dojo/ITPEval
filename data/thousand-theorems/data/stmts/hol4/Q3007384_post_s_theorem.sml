(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3007384, "Post's theorem": on an arbitrary Primcodable carrier, a predicate
  is computable exactly when both it and its complement are recursively
  enumerable. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val _ = Datatype `
  q3007384_code =
      Q3007384Zero
    | Q3007384Succ
    | Q3007384Left
    | Q3007384Right
    | Q3007384Pair q3007384_code q3007384_code
    | Q3007384Comp q3007384_code q3007384_code
    | Q3007384Prec q3007384_code q3007384_code
    | Q3007384Rfind q3007384_code
`;

val q3007384_pair_def = new_definition (
  "q3007384_pair_def",
  ``q3007384_pair a b =
      if a < b then b * b + a else a * a + a + b``
);

val (q3007384_eval_rules, q3007384_eval_ind, q3007384_eval_cases) =
  Hol_reln`
    (!n. q3007384_eval Q3007384Zero n 0) /\
    (!n. q3007384_eval Q3007384Succ n (SUC n)) /\
    (!a b. q3007384_eval Q3007384Left (q3007384_pair a b) a) /\
    (!a b. q3007384_eval Q3007384Right (q3007384_pair a b) b) /\
    (!c d n a b.
       q3007384_eval c n a /\ q3007384_eval d n b ==>
       q3007384_eval (Q3007384Pair c d) n (q3007384_pair a b)) /\
    (!c d n a b.
       q3007384_eval d n a /\ q3007384_eval c a b ==>
       q3007384_eval (Q3007384Comp c d) n b) /\
    (!c d a b.
       q3007384_eval c a b ==>
       q3007384_eval (Q3007384Prec c d) (q3007384_pair a 0) b) /\
    (!c d a n r b.
       q3007384_eval (Q3007384Prec c d) (q3007384_pair a n) r /\
       q3007384_eval d
         (q3007384_pair a (q3007384_pair n r)) b ==>
       q3007384_eval
         (Q3007384Prec c d) (q3007384_pair a (SUC n)) b) /\
    (!c a m.
       q3007384_eval c (q3007384_pair a m) 0 ==>
       q3007384_eval (Q3007384Rfind c) (q3007384_pair a m) m) /\
    (!c a m z r.
       q3007384_eval c (q3007384_pair a m) z /\ z <> 0 /\
       q3007384_eval
         (Q3007384Rfind c) (q3007384_pair a (SUC m)) r ==>
       q3007384_eval (Q3007384Rfind c) (q3007384_pair a m) r)
  `;

val q3007384_primitive_code_def = Define`
  (q3007384_primitive_code Q3007384Zero = T) /\
  (q3007384_primitive_code Q3007384Succ = T) /\
  (q3007384_primitive_code Q3007384Left = T) /\
  (q3007384_primitive_code Q3007384Right = T) /\
  (q3007384_primitive_code (Q3007384Pair c d) =
     (q3007384_primitive_code c /\ q3007384_primitive_code d)) /\
  (q3007384_primitive_code (Q3007384Comp c d) =
     (q3007384_primitive_code c /\ q3007384_primitive_code d)) /\
  (q3007384_primitive_code (Q3007384Prec c d) =
     (q3007384_primitive_code c /\ q3007384_primitive_code d)) /\
  (q3007384_primitive_code (Q3007384Rfind c) = F)
`;

val q3007384_primrec_def = new_definition (
  "q3007384_primrec_def",
  ``q3007384_primrec f <=>
      ?program.
        q3007384_primitive_code program /\
        !n y. (q3007384_eval program n y <=> y = f n)``
);

val q3007384_primcodable_def = new_definition (
  "q3007384_primcodable_def",
  ``q3007384_primcodable encode decode <=>
      (!a. decode (encode a) = SOME a) /\
      q3007384_primrec
        (\n. case decode n of
               NONE => 0
             | SOME a => SUC (encode a))``
);

val q3007384_computable_pred_def = new_definition (
  "q3007384_computable_pred_def",
  ``q3007384_computable_pred encode predicate <=>
      ?program. !a y.
        (q3007384_eval program (encode a) y <=>
         if predicate a then y = 1 else y = 0)``
);

val q3007384_re_pred_def = new_definition (
  "q3007384_re_pred_def",
  ``q3007384_re_pred encode predicate <=>
      ?program. !a.
        (predicate a <=> ?y. q3007384_eval program (encode a) y)``
);

val q3007384_post_s_theorem =
  ``!(encode : 'a -> num) (decode : num -> 'a option)
      (predicate : 'a -> bool).
      q3007384_primcodable encode decode ==>
      (q3007384_computable_pred encode predicate <=>
       q3007384_re_pred encode predicate /\
       q3007384_re_pred encode (\a. ~predicate a))``;
