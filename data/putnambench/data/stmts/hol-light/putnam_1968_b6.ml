(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b6:
  nonexistence of a countable family cofinal under inclusion among compact
  sets of rational numbers. This file contains no proof.
*)

let statement =
  `let compact_real =
     \(S:real->bool).
       !f:num->real.
         (!n. f n IN S)
         ==> ?l r.
               l IN S /\
               (!m n:num. m < n ==> r m < r n) /\
               (!e. &0 < e
                    ==> ?N. !n. N <= n ==> abs (f (r n) - l) < e) in
   let compact_rational =
     \(S:real->bool).
       compact_real S /\
       (!x. x IN S
            ==> ?p q:int.
                  ~(q = (&0:int)) /\
                  x = real_of_int p / real_of_int q) in
   ~(?K:num->real->bool.
       (!n. compact_rational (K n)) /\
       (!S:real->bool.
          compact_rational S ==> ?n. S SUBSET K n))`;;
