$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_a4: a consistent orientation of the distinct triples of a
  finite set admits an injective real-valued ordering whose increasing
  triples have that orientation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  An arbitrary A e. Fin is the source finite carrier. The powerset of
  ( A X. A ) X. A contains every ternary relation on A when SetMM's ordered
  triple <. a , b , c >. is used. The explicit inequalities retain the
  pairwise-distinct scopes of the nontrivial distinct-element formulation.

  The witness g remains existential and SetMM's -1-1-> notation requires it
  to be an injective total function from A into RR. The final declaration is
  the single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d A S a b c d g $.

  putnambench-putnam-1996-a4 $a |- A. A e. Fin
    A. S e. ~P ( ( A X. A ) X. A )
      (
        (
          A. a e. A A. b e. A A. c e. A
            (
              <. a , b , c >. e. S
              ->
              (
                a =/= b
                /\
                (
                  b =/= c
                  /\
                  a =/= c
                )
              )
            )
          /\
          (
            A. a e. A A. b e. A A. c e. A
              (
                (
                  a =/= b
                  /\
                  (
                    b =/= c
                    /\
                    a =/= c
                  )
                )
                ->
                (
                  <. a , b , c >. e. S
                  <->
                  <. b , c , a >. e. S
                )
              )
            /\
            (
              A. a e. A A. b e. A A. c e. A
                (
                  (
                    a =/= b
                    /\
                    (
                      b =/= c
                      /\
                      a =/= c
                    )
                  )
                  ->
                  (
                    <. a , b , c >. e. S
                    <->
                    -. <. c , b , a >. e. S
                  )
                )
              /\
              A. a e. A A. b e. A A. c e. A A. d e. A
                (
                  (
                    a =/= b
                    /\
                    (
                      a =/= c
                      /\
                      (
                        a =/= d
                        /\
                        (
                          b =/= c
                          /\
                          (
                            b =/= d
                            /\
                            c =/= d
                          )
                        )
                      )
                    )
                  )
                  ->
                  (
                    (
                      <. a , b , c >. e. S
                      /\
                      <. c , d , a >. e. S
                    )
                    <->
                    (
                      <. b , c , d >. e. S
                      /\
                      <. d , a , b >. e. S
                    )
                  )
                )
            )
          )
        )
        ->
        E. g
          (
            g : A -1-1-> RR
            /\
            A. a e. A A. b e. A A. c e. A
              (
                (
                  ( g ` a ) < ( g ` b )
                  /\
                  ( g ` b ) < ( g ` c )
                )
                ->
                <. a , b , c >. e. S
              )
          )
      )
  $.
$}
