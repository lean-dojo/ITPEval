$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_b5: bounded real functions with values at least one admit a
  representation equating the suprema of an exponential family and an
  affine family at every real parameter. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  G and H range over arbitrary real-valued functions on RR. Their common
  antecedent preserves the pointwise lower bounds and the internally
  existential joint upper bounds from the sources.

  For bases at least one, set.mm's complex-power operation ^c is real-valued
  and agrees with the source real power exp(x log(G(s))). Each set in a sup
  expression is the unrestricted real image of the corresponding family.
  Set.mm's sup(A, RR, <) is the real-order supremum, matching sSup/Sup in the
  Lean and Isabelle ground truth.

  U and V remain internally existential arbitrary functions RR -> RR. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d B C G H U V s t x y $.

  putnambench-putnam-2012-b5 $a |-
    A. G e. ( RR ^m RR )
      A. H e. ( RR ^m RR )
        (
          (
            A. x e. RR
              (
                1 <_ ( G ` x )
                /\
                1 <_ ( H ` x )
              )
            /\
            E. B e. RR
              E. C e. RR
                A. x e. RR
                  (
                    ( G ` x ) <_ B
                    /\
                    ( H ` x ) <_ C
                  )
          )
          ->
          E. U e. ( RR ^m RR )
            E. V e. ( RR ^m RR )
              A. x e. RR
                sup
                  (
                    {
                      y e. RR |
                        E. s e. RR
                          y =
                          (
                            ( ( G ` s ) ^c x )
                            x.
                            ( H ` s )
                          )
                    } ,
                    RR ,
                    <
                  )
                =
                sup
                  (
                    {
                      y e. RR |
                        E. t e. RR
                          y =
                          (
                            ( x x. ( U ` t ) )
                            +
                            ( V ` t )
                          )
                    } ,
                    RR ,
                    <
                  )
        )
  $.
$}
