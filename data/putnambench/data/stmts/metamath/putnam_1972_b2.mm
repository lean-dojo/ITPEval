$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_b2: the maximum time for a twice-differentiable real
  trajectory with nonincreasing second derivative and prescribed positive
  displacement s and final velocity v is 2s/v. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of total real-valued functions. The first two
  entries of ( RR Dn F ) are the first and second real derivatives of F.
  Inclusion of [0,t] in their domains expresses the two differentiability
  requirements, and the nested universal quantifiers express that the second
  derivative is antitone there.

  The witness function remains existentially quantified separately at the
  attained value 2s/v and at every excluded larger time. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d F a b s t v $.

  putnambench-putnam-1972-b2 $a |-
    A. s e. RR A. v e. RR
      (
        (
          0 < s
          /\
          0 < v
        )
        ->
        (
          E. F e. ( RR ^m RR )
            (
              (
                (
                  ( 0 [,] ( ( 2 x. s ) / v ) )
                    C_ dom ( ( RR Dn F ) ` 1 )
                  /\
                  ( 0 [,] ( ( 2 x. s ) / v ) )
                    C_ dom ( ( RR Dn F ) ` 2 )
                )
                /\
                A. a e. ( 0 [,] ( ( 2 x. s ) / v ) )
                  A. b e. ( 0 [,] ( ( 2 x. s ) / v ) )
                    (
                      a <_ b
                      ->
                      ( ( ( RR Dn F ) ` 2 ) ` b )
                        <_ ( ( ( RR Dn F ) ` 2 ) ` a )
                    )
              )
              /\
              (
                (
                  ( ( ( RR Dn F ) ` 1 ) ` 0 ) = 0
                  /\
                  ( ( ( RR Dn F ) ` 1 )
                      ` ( ( 2 x. s ) / v ) ) = v
                )
                /\
                (
                  ( F ` ( ( 2 x. s ) / v ) )
                  -
                  ( F ` 0 )
                )
                =
                s
              )
            )
          /\
          A. t e. RR
            (
              ( ( 2 x. s ) / v ) < t
              ->
              -. E. F e. ( RR ^m RR )
                (
                  (
                    (
                      ( 0 [,] t )
                        C_ dom ( ( RR Dn F ) ` 1 )
                      /\
                      ( 0 [,] t )
                        C_ dom ( ( RR Dn F ) ` 2 )
                    )
                    /\
                    A. a e. ( 0 [,] t )
                      A. b e. ( 0 [,] t )
                        (
                          a <_ b
                          ->
                          ( ( ( RR Dn F ) ` 2 ) ` b )
                            <_ ( ( ( RR Dn F ) ` 2 ) ` a )
                        )
                  )
                  /\
                  (
                    (
                      ( ( ( RR Dn F ) ` 1 ) ` 0 ) = 0
                      /\
                      ( ( ( RR Dn F ) ` 1 ) ` t ) = v
                    )
                    /\
                    ( ( F ` t ) - ( F ` 0 ) ) = s
                  )
                )
            )
        )
      )
  $.
$}
