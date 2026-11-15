$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_b3: nonvanishing and continuity of a real function g at zero,
  together with differentiability there of f*g and f/g, imply
  differentiability of f at zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The functions f and g range over all total real-valued functions.
  Continuity of g at zero is expanded in the standard epsilon-delta form.
  Membership of zero in dom ( RR _D F ) is set.mm's native assertion that
  the real function F is differentiable at zero. The product and quotient
  functions are displayed explicitly.

  The source solution proposition is True, represented by set.mm's T., so
  the final biconditional preserves the source statement literally. The
  final declaration is a single unproved $a statement; this database
  contains no $p proof declaration.
$)

${
  $d d e f g x $.

  putnambench-putnam-2011-b3 $a |- (
    (
      A. f e. ( RR ^m RR )
      A. g e. ( RR ^m RR )
        (
          (
            ( g ` 0 ) =/= 0
            /\
            (
              A. e e. RR
                (
                  0 < e
                  ->
                  E. d e. RR
                    (
                      0 < d
                      /\
                      A. x e. RR
                        (
                          ( abs ` x ) < d
                          ->
                          (
                            abs
                            `
                            (
                              ( g ` x )
                              -
                              ( g ` 0 )
                            )
                          )
                          < e
                        )
                    )
                )
              /\
              (
                0 e. dom
                  (
                    RR _D
                      (
                        x e. RR |->
                          (
                            ( f ` x )
                            x.
                            ( g ` x )
                          )
                      )
                  )
                /\
                0 e. dom
                  (
                    RR _D
                      (
                        x e. RR |->
                          (
                            ( f ` x )
                            /
                            ( g ` x )
                          )
                      )
                  )
              )
            )
          )
          ->
          0 e. dom ( RR _D f )
        )
    )
    <-> T.
  ) $.
$}
