$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_a3: classification of two positivity implications for globally
  twice-differentiable real solutions of a second-order differential equation,
  with the first implication false and the second true. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of all total real functions. Membership of each real
  x in the domains of the first two entries of ( RR Dn f ) or ( RR Dn g )
  expresses the two pointwise derivative-existence assumptions. The two
  biconditionals retain the source solution pair ( False , True ) literally
  as SetMM's logical constants F. and T. The final declaration is the single
  unproved $a corpus statement; this database contains no $p declaration.
$)

${
  $d f x $.
  $d g x $.

  putnambench-putnam-1987-a3 $a |- (
    (
      (
        A. f e. ( RR ^m RR )
          (
            (
              A. x e. RR
                (
                  x e. dom ( ( RR Dn f ) ` 1 )
                  /\
                  x e. dom ( ( RR Dn f ) ` 2 )
                  /\
                  (
                    (
                      (
                        ( ( ( RR Dn f ) ` 2 ) ` x )
                        -
                        (
                          2
                          x.
                          ( ( ( RR Dn f ) ` 1 ) ` x )
                        )
                      )
                      +
                      ( f ` x )
                    )
                    =
                    ( 2 x. ( exp ` x ) )
                  )
                  /\
                  0 < ( f ` x )
                )
            )
            ->
            A. x e. RR
              0 < ( ( ( RR Dn f ) ` 1 ) ` x )
          )
      )
      <-> F.
    )
    /\
    (
      (
        A. g e. ( RR ^m RR )
          (
            (
              A. x e. RR
                (
                  x e. dom ( ( RR Dn g ) ` 1 )
                  /\
                  x e. dom ( ( RR Dn g ) ` 2 )
                  /\
                  (
                    (
                      (
                        ( ( ( RR Dn g ) ` 2 ) ` x )
                        -
                        (
                          2
                          x.
                          ( ( ( RR Dn g ) ` 1 ) ` x )
                        )
                      )
                      +
                      ( g ` x )
                    )
                    =
                    ( 2 x. ( exp ` x ) )
                  )
                  /\
                  0 < ( ( ( RR Dn g ) ` 1 ) ` x )
                )
            )
            ->
            A. x e. RR
              0 < ( g ` x )
          )
      )
      <-> T.
    )
  ) $.
$}
