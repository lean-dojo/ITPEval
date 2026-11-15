(*
  Statement-only formalization of Logipedia corpus artifact
  permutation.permut_S_to_permut_transpose, catalog title
  "permutation.permut_S_to_permut_transpose": a permutation of the natural
  initial segment through SUC m remains a permutation through m after its
  values are transposed with the value at SUC m. This file contains no proof.
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
   let transpose =
     \(i:num) j n.
       if n = i then j else if n = j then i else n
   in
   !f:num->num.
   !m:num.
     permut f (SUC m)
     ==>
     permut
       (\n. transpose (f (SUC m)) (SUC m) (f n))
       m`;;
