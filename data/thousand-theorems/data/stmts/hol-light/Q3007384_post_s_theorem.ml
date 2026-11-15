(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3007384
  (thousand-theorems__hol-light__Q3007384), "Post's theorem": on an arbitrary
  primcodable domain, a decidable predicate is computable exactly when it and
  its complement are recursively enumerable. This file contains no proof.
*)

let Q3007384_POSTS_THEOREM =
  let q3007384_code_INDUCT,q3007384_code_RECURSION = define_type
    "q3007384_code =
       Q3007384_Zero
     | Q3007384_Succ
     | Q3007384_Left
     | Q3007384_Right
     | Q3007384_Pair q3007384_code q3007384_code
     | Q3007384_Comp q3007384_code q3007384_code
     | Q3007384_Prec q3007384_code q3007384_code
     | Q3007384_Rfind q3007384_code" in

  let _ = new_definition
    `q3007384_pair a b =
       ((a + b) * (a + b + 1)) DIV 2 + b` in

  let _,_,_ = new_inductive_definition
   `(!n:num. q3007384_eval Q3007384_Zero n 0) /\
    (!n:num. q3007384_eval Q3007384_Succ n (SUC n)) /\
    (!a b:num.
       q3007384_eval Q3007384_Left (q3007384_pair a b) a) /\
    (!a b:num.
       q3007384_eval Q3007384_Right (q3007384_pair a b) b) /\
    (!c d n x y.
       q3007384_eval c n x /\ q3007384_eval d n y
       ==> q3007384_eval (Q3007384_Pair c d) n
             (q3007384_pair x y)) /\
    (!c d n x y.
       q3007384_eval d n x /\ q3007384_eval c x y
       ==> q3007384_eval (Q3007384_Comp c d) n y) /\
    (!c d a y.
       q3007384_eval c a y
       ==> q3007384_eval (Q3007384_Prec c d)
             (q3007384_pair a 0) y) /\
    (!c d a k i y.
       q3007384_eval (Q3007384_Prec c d)
         (q3007384_pair a k) i /\
       q3007384_eval d
         (q3007384_pair a (q3007384_pair k i)) y
       ==> q3007384_eval (Q3007384_Prec c d)
             (q3007384_pair a (SUC k)) y) /\
    (!c a m.
       q3007384_eval c (q3007384_pair a m) 0
       ==> q3007384_eval (Q3007384_Rfind c)
             (q3007384_pair a m) m) /\
    (!c a m z y.
       q3007384_eval c (q3007384_pair a m) (SUC z) /\
       q3007384_eval (Q3007384_Rfind c)
         (q3007384_pair a (SUC m)) y
       ==> q3007384_eval (Q3007384_Rfind c)
             (q3007384_pair a m) y)` in

  let _ = new_recursive_definition q3007384_code_RECURSION
  `(q3007384_primitive Q3007384_Zero <=> T) /\
   (q3007384_primitive Q3007384_Succ <=> T) /\
   (q3007384_primitive Q3007384_Left <=> T) /\
   (q3007384_primitive Q3007384_Right <=> T) /\
   (q3007384_primitive (Q3007384_Pair c d) <=>
      q3007384_primitive c /\ q3007384_primitive d) /\
   (q3007384_primitive (Q3007384_Comp c d) <=>
      q3007384_primitive c /\ q3007384_primitive d) /\
   (q3007384_primitive (Q3007384_Prec c d) <=>
      q3007384_primitive c /\ q3007384_primitive d) /\
   (q3007384_primitive (Q3007384_Rfind c) <=> F)` in

  let _ = new_definition
    `q3007384_primcodable
      (encode:A->num) (decode:num->A option) <=>
     (!a:A. decode (encode a) = SOME a) /\
     (?encode_program:q3007384_code.
        q3007384_primitive encode_program /\
        !a:A. !y:num.
          q3007384_eval encode_program (encode a) y <=>
          y = encode a) /\
     (?decode_program:q3007384_code.
        q3007384_primitive decode_program /\
        !n y:num.
          q3007384_eval decode_program n y <=>
          (decode n = NONE /\ y = 0) \/
          (?a:A. decode n = SOME a /\ y = SUC (encode a)))` in

  let _ = new_definition
    `q3007384_computable_predicate
      (encode:A->num) (p:A->bool) <=>
     ?program:q3007384_code.
       !a:A. !y:num.
         q3007384_eval program (encode a) y <=>
         (if p a then y = 1 else y = 0)` in

  let _ = new_definition
    `q3007384_re_predicate (encode:A->num) (p:A->bool) <=>
     ?program:q3007384_code.
       !a:A. !y:num.
         q3007384_eval program (encode a) y <=>
         p a /\ y = 0` in

  `!encode:A->num.
   !decode:num->A option.
   !p:A->bool.
     q3007384_primcodable encode decode
     ==> (q3007384_computable_predicate encode p <=>
          q3007384_re_predicate encode p /\
          q3007384_re_predicate encode (\a:A. ~(p a)))`;;
