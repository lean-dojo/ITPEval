$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_a5: a controlled linear system of two real differential
  equations reaches the origin at a prescribed positive time exactly when
  its two initial values are equal. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The witnesses X and Y range over all total real-valued functions, and U
  ranges over set.mm's class of continuous real-valued functions. Membership
  of every real p in dom ( RR _D X ) and dom ( RR _D Y ) states global
  differentiability; the corresponding derivative values state the two
  differential equations pointwise. The witnesses remain internal to the
  equivalence, as in all three source formulations.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b t p X Y U $.

  putnambench-putnam-1969-a5 $a |-
    A. a e. RR A. b e. RR A. t e. RR
      (
        0 < t
        ->
        (
          a = b
          <->
          E. X e. ( RR ^m RR )
          E. Y e. ( RR ^m RR )
          E. U e. ( RR -cn-> RR )
            (
              (
                A. p e. RR
                  (
                    p e. dom ( RR _D X )
                    /\
                    ( ( RR _D X ) ` p )
                    =
                    (
                      ( ( -u 2 ) x. ( Y ` p ) )
                      +
                      ( U ` p )
                    )
                  )
                /\
                A. p e. RR
                  (
                    p e. dom ( RR _D Y )
                    /\
                    ( ( RR _D Y ) ` p )
                    =
                    (
                      ( ( -u 2 ) x. ( X ` p ) )
                      +
                      ( U ` p )
                    )
                  )
              )
              /\
              (
                (
                  ( X ` 0 ) = a
                  /\
                  ( Y ` 0 ) = b
                )
                /\
                (
                  ( X ` t ) = 0
                  /\
                  ( Y ` t ) = 0
                )
              )
            )
        )
      )
  $.
$}
