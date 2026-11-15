(*
  Statement-only formalization of PutnamBench artifact putnam_1965_a4:
  a finite bipartite dance relation with no boy dancing with every girl but
  every girl dancing with some boy has a crossed non-dancing pair of couples.
  This file contains no proof.
*)

let statement =
  `!dances:G->B->bool.
     FINITE (UNIV:G->bool) /\
     FINITE (UNIV:B->bool) /\
     (~(?b:B. !g:G. dances g b) /\
      (!g:G. ?b:B. dances g b))
     ==> ?g h:G. ?b c:B.
           dances g b /\
           dances h c /\
           ~dances h b /\
           ~dances g c`;;
