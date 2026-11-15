$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_a1: the positive real height 4/9 below the maximum of
  2x - 3x^3 for which the two specified first-quadrant areas are equal.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The resolved height 4/9 is substituted directly. The S. binders are
  set.mm's real Lebesgue integrals over the open intervals used by Lean.
  They also equal Isabelle's interval integrals, since changing finitely
  many endpoints does not affect a Lebesgue integral.

  Each conditional has the form if ( u <_ 0 , 0 , u ), hence represents
  max(u,0). The final declaration preserves the source positivity, strict
  upper bound, and equality of the two areas. All declarations below are
  unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

putnambench-putnam-1993-a1 $a |- (
  0 < ( 4 / 9 )
  /\
  (
    ( 4 / 9 )
    <
    (
      ( 4 x. ( sqrt ` 2 ) )
      /
      9
    )
    /\
    (
      S. ( 0 (,) ( ( sqrt ` 2 ) / 3 ) )
        if (
          (
            ( 4 / 9 )
            -
            (
              ( 2 x. x )
              -
              ( 3 x. ( x ^ 3 ) )
            )
          )
          <_
          0
          ,
          0
          ,
          (
            ( 4 / 9 )
            -
            (
              ( 2 x. x )
              -
              ( 3 x. ( x ^ 3 ) )
            )
          )
        )
        _d x
      =
      S. ( 0 (,) ( ( sqrt ` 6 ) / 3 ) )
        if (
          (
            (
              ( 2 x. x )
              -
              ( 3 x. ( x ^ 3 ) )
            )
            -
            ( 4 / 9 )
          )
          <_
          0
          ,
          0
          ,
          (
            (
              ( 2 x. x )
              -
              ( 3 x. ( x ^ 3 ) )
            )
            -
            ( 4 / 9 )
          )
        )
        _d x
    )
  )
) $.
