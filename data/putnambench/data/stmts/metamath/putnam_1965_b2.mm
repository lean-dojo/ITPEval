$(
  Statement-only formalization of PutnamBench artifact putnam_1965_b2:
  in a finite round-robin tournament, the sum of the squares of the players'
  win counts equals the sum of the squares of their loss counts. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P is an arbitrary finite player set of cardinality n. The subset W of
  P X. P is the true-pair relation of the source Boolean-valued function won:
  <. i , j >. e. W means that i defeated j. Thus relation membership and its
  negation give a bidirectional encoding of the two Boolean values.

  The functions w and l retain the source integer codomain and are explicitly
  equated to the win-cardinality and n - 1 - w definitions. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d P W i j n r w l $.

  putnambench-putnam-1965-b2 $a |- A. n e. NN0
    A. P e. Fin
      A. W e. ~P ( P X. P )
        A. w e. ( ZZ ^m P )
          A. l e. ( ZZ ^m P )
            (
              (
                (
                  (
                    ( # ` P ) = n
                    /\
                    1 < n
                  )
                  /\
                  A. i e. P -. <. i , i >. e. W
                )
                /\
                A. i e. P A. j e. P
                  (
                    i =/= j
                    ->
                    (
                      <. i , j >. e. W
                      <->
                      -. <. j , i >. e. W
                    )
                  )
              )
              /\
              (
                w =
                  (
                    r e. P |->
                      ( # ` { j e. P | <. r , j >. e. W } )
                  )
                /\
                l =
                  (
                    r e. P |->
                      ( ( n - 1 ) - ( w ` r ) )
                  )
              )
            )
            ->
            (
              sum_ r e. P ( ( w ` r ) ^ 2 )
            )
            =
            (
              sum_ r e. P ( ( l ` r ) ^ 2 )
            )
  $.
$}
