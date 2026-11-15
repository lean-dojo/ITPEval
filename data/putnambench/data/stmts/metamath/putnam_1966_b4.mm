$(
  Statement-only formalization of PutnamBench artifact putnam_1966_b4:
  every finite set of mn + 1 positive integers contains either a divisibility
  antichain of size m + 1 or a divisibility chain of size n + 1. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the set of nonnegative integers, so it preserves the source domains
  of m and n. Requiring the finite set S to be a subset of NN is equivalent to
  requiring every natural-number member of S to be positive. Membership of T
  in the power set of S preserves the internally existential subset witness.

  In the first alternative, every ordered pair of distinct members is
  nondivisible in the indicated direction, hence no member divides another.
  In the second, every smaller member divides every larger member. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d S T i j m n $.

  putnambench-putnam-1966-b4 $a |- A. m e. NN0
    A. n e. NN0
      A. S e. Fin
        (
          (
            S C_ NN
            /\
            ( # ` S ) = ( ( m x. n ) + 1 )
          )
          ->
          E. T e. ~P S
            (
              (
                ( # ` T ) = ( m + 1 )
                /\
                A. j e. T A. i e. T
                  (
                    i =/= j
                    ->
                    -. j || i
                  )
              )
              \/
              (
                ( # ` T ) = ( n + 1 )
                /\
                A. j e. T A. i e. T
                  (
                    j < i
                    ->
                    j || i
                  )
              )
            )
        )
  $.
$}
