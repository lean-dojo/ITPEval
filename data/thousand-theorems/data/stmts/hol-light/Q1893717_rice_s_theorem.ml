(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1893717,
  "Rice's theorem": a computably decidable extensional property of program
  semantics that holds for one partial-recursive function holds for every
  partial-recursive function. This file contains no proof.
*)

let q1893717_code_INDUCT,q1893717_code_RECURSION = define_type
  "q1893717_code =
       Q1893717_Zero
     | Q1893717_Succ
     | Q1893717_Left
     | Q1893717_Right
     | Q1893717_Pair q1893717_code q1893717_code
     | Q1893717_Comp q1893717_code q1893717_code
     | Q1893717_Prec q1893717_code q1893717_code
     | Q1893717_Rfind q1893717_code";;

let q1893717_pair = new_definition
  `q1893717_pair a b =
     ((a + b) * (a + b + 1)) DIV 2 + b`;;

let q1893717_encode = new_recursive_definition q1893717_code_RECURSION
  `(q1893717_encode Q1893717_Zero = 0) /\
   (q1893717_encode Q1893717_Succ = 1) /\
   (q1893717_encode Q1893717_Left = 2) /\
   (q1893717_encode Q1893717_Right = 3) /\
   (q1893717_encode (Q1893717_Pair c d) =
      4 + 4 * q1893717_pair
        (q1893717_encode c) (q1893717_encode d)) /\
   (q1893717_encode (Q1893717_Comp c d) =
      6 + 4 * q1893717_pair
        (q1893717_encode c) (q1893717_encode d)) /\
   (q1893717_encode (Q1893717_Prec c d) =
      5 + 4 * q1893717_pair
        (q1893717_encode c) (q1893717_encode d)) /\
   (q1893717_encode (Q1893717_Rfind c) =
      7 + 4 * q1893717_encode c)`;;

let q1893717_eval_RULES,q1893717_eval_INDUCT,q1893717_eval_CASES =
  new_inductive_definition
   `(!n:num. q1893717_eval Q1893717_Zero n 0) /\
    (!n:num. q1893717_eval Q1893717_Succ n (SUC n)) /\
    (!a b:num.
       q1893717_eval Q1893717_Left (q1893717_pair a b) a) /\
    (!a b:num.
       q1893717_eval Q1893717_Right (q1893717_pair a b) b) /\
    (!c d n x y.
       q1893717_eval c n x /\ q1893717_eval d n y
       ==> q1893717_eval (Q1893717_Pair c d) n
             (q1893717_pair x y)) /\
    (!c d n x y.
       q1893717_eval d n x /\ q1893717_eval c x y
       ==> q1893717_eval (Q1893717_Comp c d) n y) /\
    (!c d a y.
       q1893717_eval c a y
       ==> q1893717_eval (Q1893717_Prec c d)
             (q1893717_pair a 0) y) /\
    (!c d a k i y.
       q1893717_eval (Q1893717_Prec c d)
         (q1893717_pair a k) i /\
       q1893717_eval d (q1893717_pair a (q1893717_pair k i)) y
       ==> q1893717_eval (Q1893717_Prec c d)
             (q1893717_pair a (SUC k)) y) /\
    (!c a m.
       q1893717_eval c (q1893717_pair a m) 0
       ==> q1893717_eval (Q1893717_Rfind c)
             (q1893717_pair a m) m) /\
    (!c a m z y.
       q1893717_eval c (q1893717_pair a m) (SUC z) /\
       q1893717_eval (Q1893717_Rfind c)
         (q1893717_pair a (SUC m)) y
       ==> q1893717_eval (Q1893717_Rfind c)
             (q1893717_pair a m) y)`;;

let q1893717_partrec = new_definition
  `q1893717_partrec (f:num->num->bool) <=>
     ?program:q1893717_code.
       !x y. f x y <=> q1893717_eval program x y`;;

let q1893717_computable_predicate = new_definition
  `q1893717_computable_predicate (p:q1893717_code->bool) <=>
     ?program:q1893717_code.
       !c y.
         q1893717_eval program (q1893717_encode c) y <=>
         (if p c then y = 1 else y = 0)`;;

let Q1893717_RICES_THEOREM =
  `!C:(num->num->bool)->bool.
   !f g:num->num->bool.
     q1893717_computable_predicate
       (\c. C (q1893717_eval c)) /\
     q1893717_partrec f /\
     q1893717_partrec g /\
     C f
     ==> C g`;;
