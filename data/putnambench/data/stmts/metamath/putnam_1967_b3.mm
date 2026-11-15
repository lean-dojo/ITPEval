$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1967_b3: for continuous real-valued functions of period one, the
  oscillatory unit-interval integral converges to the product of their
  unit-interval means. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F and G range over arbitrary total real-valued functions on the reals.
  Membership in RR -cn-> RR expresses continuity, and the two translation
  equations express period one. The limit is taken at positive infinity over
  the integers, as in the Isabelle and Lean sources; restricting the same
  eventual limit to natural indices gives the Rocq formulation.

  The Lebesgue integrals use the open interval (0,1), matching the Lean and
  Rocq sources. Adding or removing the endpoints does not change these
  integrals and therefore also matches the Isabelle interval integral. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d F G n x $.

  putnambench-putnam-1967-b3 $a |-
    A. F e. ( RR ^m RR )
    A. G e. ( RR ^m RR )
      (
        (
          (
            F e. ( RR -cn-> RR )
            /\
            G e. ( RR -cn-> RR )
          )
          /\
          (
            A. x e. RR
              ( F ` ( x + 1 ) ) = ( F ` x )
            /\
            A. x e. RR
              ( G ` ( x + 1 ) ) = ( G ` x )
          )
        )
        ->
        (
          n e. ZZ |->
            S. ( 0 (,) 1 )
              (
                ( F ` x )
                x.
                ( G ` ( n x. x ) )
              )
              _d x
        )
        ~~>
        (
          (
            S. ( 0 (,) 1 )
              ( F ` x )
              _d x
          )
          x.
          (
            S. ( 0 (,) 1 )
              ( G ` x )
              _d x
          )
        )
      )
  $.
$}
