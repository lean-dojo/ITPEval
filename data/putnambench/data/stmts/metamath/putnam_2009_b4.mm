$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_b4: the real vector space of balanced bivariate polynomials of
  total degree at most 2009 has dimension 2020050. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The ordinal 2o is the two-element variable-index set, so
  ( 2o mPoly RRfld ) is SetMM's vector space of arbitrary finite-support
  bivariate polynomials over the real field. The function mDeg is total
  degree, and eval evaluates a polynomial at a real coordinate assignment.

  The displayed subset is exactly the source subspace V: for every positive
  real radius r, the polynomial evaluated on
  (r cos(t), r sin(t)) has normalized integral zero around the circle. The
  closed integration interval differs from the source interval integral only
  at its endpoints. Restricting the polynomial vector space to this subset
  gives V, and dim is SetMM's vector-space dimension.

  The declaration below is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i p r t $.

  putnambench-putnam-2009-b4 $a |- (
    dim
    `
    (
      ( 2o mPoly RRfld )
      |`s
      {
        p e. ( Base ` ( 2o mPoly RRfld ) ) |
          (
            (
              ( ( 2o mDeg RRfld ) ` p )
              <_
              ; ; ; 2 0 0 9
            )
            /\
            A. r e. RR
              (
                0 < r
                ->
                (
                  S. ( 0 [,] ( 2 x. _pi ) )
                    (
                      (
                        ( ( 2o eval RRfld ) ` p )
                        `
                        (
                          i e. 2o |->
                            if (
                              i = (/) ,
                              ( r x. ( cos ` t ) ) ,
                              ( r x. ( sin ` t ) )
                            )
                        )
                      )
                    )
                    _d t
                  /
                  ( ( 2 x. _pi ) x. r )
                )
                =
                0
              )
          )
      }
    )
    =
    ; ; ; ; ; ; 2 0 2 0 0 5 0
  ) $.
$}
