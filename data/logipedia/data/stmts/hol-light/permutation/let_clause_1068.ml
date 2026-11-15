(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.let_clause_1068, catalog title
  "permutation.let_clause_1068": under the source's explicit boundedness,
  image, closure, injectivity, and equal-preimage hypotheses, a bounded
  natural-number permutation retains the first preimage's specified image.
  This file contains no proof.
*)

let statement =
  `let injn =
     \(f:num->num) n.
       !i j:num.
         i <= n
         ==> j <= n
         ==> f i = f j
         ==> i = j
   in
   let permut =
     \(f:num->num) n.
       (!i:num. i <= n ==> f i <= n) /\ injn f n
   in
   !f:num->num.
   !n:num.
     permut f n
     ==> !i:num.
         !j:num.
           i <= n
           ==> j <= n
           ==> !a:num.
               (a <= n /\ f a = i)
               ==> a <= n
                   ==> f a = i
                       ==> !b:num.
                           (b <= n /\ f b = j)
                           ==> b <= n
                               ==> f b = j
                                   ==> (!i0:num.
                                          i0 <= n
                                          ==> f i0 <= n)
                                       ==> injn f n
                                           ==> a = b
                                               ==> f a = i`;;
