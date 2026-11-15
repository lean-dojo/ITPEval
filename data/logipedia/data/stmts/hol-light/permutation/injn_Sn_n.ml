(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.injn_Sn_n, catalog title "permutation.injn_Sn_n": injectivity
  of a natural-number function on indices at most a successor entails
  injectivity on indices at most the preceding natural. This file contains no
  proof.
*)

let statement =
  `let injn =
     \(f:num->num) n.
       !i j:num.
         i <= n
         ==> j <= n
         ==> f i = f j
         ==> i = j in
   !f:num->num. !n:num. injn f (SUC n) ==> injn f n`;;
