(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1766814,
  "Smn theorem": a computable specialization operation on partial-recursive
  program codes fixes the first component of a paired input while preserving
  partial evaluation. This file contains no proof.
*)

let q1766814_code_INDUCT,q1766814_code_RECURSION = define_type
  "q1766814_code =
       Q1766814_Zero
     | Q1766814_Succ
     | Q1766814_Left
     | Q1766814_Right
     | Q1766814_Pair q1766814_code q1766814_code
     | Q1766814_Comp q1766814_code q1766814_code
     | Q1766814_Prec q1766814_code q1766814_code
     | Q1766814_Rfind q1766814_code";;

let q1766814_pair = new_definition
  `q1766814_pair a b =
     if a < b then b * b + a else a * a + a + b`;;

let q1766814_encode = new_recursive_definition q1766814_code_RECURSION
  `(q1766814_encode Q1766814_Zero = 0) /\
   (q1766814_encode Q1766814_Succ = 1) /\
   (q1766814_encode Q1766814_Left = 2) /\
   (q1766814_encode Q1766814_Right = 3) /\
   (q1766814_encode (Q1766814_Pair c d) =
      4 + 4 * q1766814_pair (q1766814_encode c) (q1766814_encode d)) /\
   (q1766814_encode (Q1766814_Comp c d) =
      6 + 4 * q1766814_pair (q1766814_encode c) (q1766814_encode d)) /\
   (q1766814_encode (Q1766814_Prec c d) =
      5 + 4 * q1766814_pair (q1766814_encode c) (q1766814_encode d)) /\
   (q1766814_encode (Q1766814_Rfind c) =
      7 + 4 * q1766814_encode c)`;;

let q1766814_eval_RULES,q1766814_eval_INDUCT,q1766814_eval_CASES =
  new_inductive_definition
   `(!n:num. q1766814_eval Q1766814_Zero n 0) /\
    (!n:num. q1766814_eval Q1766814_Succ n (SUC n)) /\
    (!a b:num. q1766814_eval Q1766814_Left
                 (q1766814_pair a b) a) /\
    (!a b:num. q1766814_eval Q1766814_Right
                 (q1766814_pair a b) b) /\
    (!c d n x y.
       q1766814_eval c n x /\ q1766814_eval d n y
       ==> q1766814_eval (Q1766814_Pair c d) n
             (q1766814_pair x y)) /\
    (!c d n x y.
       q1766814_eval d n x /\ q1766814_eval c x y
       ==> q1766814_eval (Q1766814_Comp c d) n y) /\
    (!c d a y.
       q1766814_eval c a y
       ==> q1766814_eval (Q1766814_Prec c d)
             (q1766814_pair a 0) y) /\
    (!c d a k i y.
       q1766814_eval (Q1766814_Prec c d)
         (q1766814_pair a k) i /\
       q1766814_eval d (q1766814_pair a (q1766814_pair k i)) y
       ==> q1766814_eval (Q1766814_Prec c d)
             (q1766814_pair a (SUC k)) y) /\
    (!c a m.
       q1766814_eval c (q1766814_pair a m) 0
       ==> q1766814_eval (Q1766814_Rfind c)
             (q1766814_pair a m) m) /\
    (!c a m z y.
       q1766814_eval c (q1766814_pair a m) (SUC z) /\
       q1766814_eval (Q1766814_Rfind c)
         (q1766814_pair a (SUC m)) y
       ==> q1766814_eval (Q1766814_Rfind c)
             (q1766814_pair a m) y)`;;

let q1766814_computable2 = new_definition
  `q1766814_computable2
      (f:q1766814_code->num->q1766814_code) <=>
     ?program:q1766814_code.
       !c n y.
         q1766814_eval program
           (q1766814_pair (q1766814_encode c) n) y <=>
         y = q1766814_encode (f c n)`;;

let Q1766814_SMN_THEOREM =
  `?f:q1766814_code->num->q1766814_code.
     q1766814_computable2 f /\
     (!c n x y.
        q1766814_eval (f c n) x y <=>
        q1766814_eval c (q1766814_pair n x) y)`;;
