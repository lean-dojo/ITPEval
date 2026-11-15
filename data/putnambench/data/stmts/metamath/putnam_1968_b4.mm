$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1968_b4: invariance of a convergent symmetric improper integral
  under the substitution x maps to x minus one over x. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over arbitrary total real-valued functions on the reals, and
  membership in RR -cn-> RR is continuity. The real limit relation ~~>r
  gives the limit at positive infinity of the RR-indexed symmetric
  integrals.

  The transformed integral is taken over
  (-y,-1/y) union (1/y,y). This is the punctured symmetric domain used
  explicitly by Lean and required by the singularity at zero. The
  unpunctured Isabelle and Rocq formulas do not preserve this
  improper-integral domain.
  Open versus closed finite endpoints does not change a Lebesgue integral.
  The same internally quantified real r is the limit of both integral
  families. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d F r x y $.

  putnambench-putnam-1968-b4 $a |- A. F e. ( RR ^m RR )
    (
      (
        F e. ( RR -cn-> RR )
        /\
        E. r e. RR
          (
            y e. RR |->
              S. ( ( -u y ) (,) y )
                ( F ` x )
                _d x
          )
          ~~>r
          r
      )
      ->
      E. r e. RR
        (
          (
            y e. RR |->
              S.
                (
                  ( ( -u y ) (,) ( -u ( 1 / y ) ) )
                  u.
                  ( ( 1 / y ) (,) y )
                )
                ( F ` ( x - ( 1 / x ) ) )
                _d x
          )
          ~~>r
          r
          /\
          (
            y e. RR |->
              S. ( ( -u y ) (,) y )
                ( F ` x )
                _d x
          )
          ~~>r
          r
        )
    )
  $.
$}
