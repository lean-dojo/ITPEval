$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_b3: an even-team round-robin tournament admits a choice of
  one winning team from each day with no team chosen twice. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, 0 ..^ (2n - 1) and 0 ..^ 2n are respectively the finite
  day and team carriers corresponding to the source Fin types. M is a total
  day-indexed family of team maps. The fixed-point-free involution conditions
  say that every team plays exactly one opponent each day, and the following
  existential condition says every distinct pair meets during the tournament.

  W is a day-indexed family of functions from teams to the two-element ordinal
  2o = {0,1}, a definitional encoding of the source Bool-valued win function.
  Inequality of the two values is equivalent to Boolean complementation. The
  witness C remains internally existential and is required to be a one-to-one
  function from all days to teams, with every chosen team assigned win value
  one. The source solution proposition is True, represented by T. in the final
  biconditional. The sole declaration is an unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

${
  $d C M W d n t u $.

  putnambench-putnam-2012-b3 $a |- (
    (
      A. n e. NN
        A. M e.
          (
            (
              ( 0 ..^ ( 2 x. n ) )
              ^m
              ( 0 ..^ ( 2 x. n ) )
            )
            ^m
            ( 0 ..^ ( ( 2 x. n ) - 1 ) )
          )
          A. W e.
            (
              (
                2o
                ^m
                ( 0 ..^ ( 2 x. n ) )
              )
              ^m
              ( 0 ..^ ( ( 2 x. n ) - 1 ) )
            )
            (
              (
                (
                  A. d e. ( 0 ..^ ( ( 2 x. n ) - 1 ) )
                    A. t e. ( 0 ..^ ( 2 x. n ) )
                      (
                        (
                          ( ( M ` d ) ` t )
                          =/=
                          t
                        )
                        /\
                        (
                          ( ( M ` d ) ` ( ( M ` d ) ` t ) )
                          =
                          t
                        )
                      )
                  /\
                  A. t e. ( 0 ..^ ( 2 x. n ) )
                    A. u e. ( 0 ..^ ( 2 x. n ) )
                      (
                        t =/= u
                        ->
                        E. d e. ( 0 ..^ ( ( 2 x. n ) - 1 ) )
                          ( ( M ` d ) ` t ) = u
                      )
                )
                /\
                A. d e. ( 0 ..^ ( ( 2 x. n ) - 1 ) )
                  A. t e. ( 0 ..^ ( 2 x. n ) )
                    (
                      ( ( W ` d ) ` t )
                      =/=
                      ( ( W ` d ) ` ( ( M ` d ) ` t ) )
                    )
              )
              ->
              E. C
                (
                  C
                  :
                  ( 0 ..^ ( ( 2 x. n ) - 1 ) )
                  -1-1->
                  ( 0 ..^ ( 2 x. n ) )
                  /\
                  A. d e. ( 0 ..^ ( ( 2 x. n ) - 1 ) )
                    ( ( W ` d ) ` ( C ` d ) ) = 1
                )
            )
    )
    <-> T.
  ) $.
$}
