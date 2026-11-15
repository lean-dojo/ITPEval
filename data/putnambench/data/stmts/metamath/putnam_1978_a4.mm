$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_a4: consequences and a finite example for binary operations
  satisfying (a * b) * (c * d) = a * d. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  An arbitrary source carrier is represented by the set s, and f is a total
  binary operation represented as a function from s X. s to s. Application
  to an ordered pair represents the source multiplication.

  The first conjunct quantifies over every carrier and operation satisfying
  the bypass identity and states both requested consequences of a * b = c.
  The second conjunct keeps the finite carrier and its operation internally
  existential and states the bypass identity together with conditions
  (A), (B), and (C).

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c d f s $.

  putnambench-putnam-1978-a4 $a |- (
    (
      A. s
        A. f e. ( s ^m ( s X. s ) )
          (
            A. a e. s A. b e. s A. c e. s A. d e. s
              ( f ` <. ( f ` <. a , b >. ) , ( f ` <. c , d >. ) >. )
              =
              ( f ` <. a , d >. )
            ->
            A. a e. s A. b e. s A. c e. s
              (
                ( f ` <. a , b >. ) = c
                ->
                (
                  ( f ` <. c , c >. ) = c
                  /\
                  A. d e. s
                    ( f ` <. a , d >. ) = ( f ` <. c , d >. )
                )
              )
          )
    )
    /\
    E. s e. Fin
      E. f e. ( s ^m ( s X. s ) )
        (
          A. a e. s A. b e. s A. c e. s A. d e. s
            ( f ` <. ( f ` <. a , b >. ) , ( f ` <. c , d >. ) >. )
            =
            ( f ` <. a , d >. )
          /\
          (
            A. a e. s
              ( f ` <. a , a >. ) = a
            /\
            (
              E. a e. s E. b e. s
                (
                  ( f ` <. a , b >. ) = a
                  /\
                  a =/= b
                )
              /\
              E. a e. s E. b e. s
                ( f ` <. a , b >. ) =/= a
            )
          )
        )
  ) $.
$}
