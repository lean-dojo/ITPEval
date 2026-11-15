$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_b3: parametrization of the unit circle over every field of
  characteristic not two by a distinguished point and a rational parameter.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over set.mm's class Field of arbitrary commutative field
  structures. Base ` F is its carrier; +g, .r, -g, 0g, 1r, and invr are
  respectively its addition, multiplication, subtraction, zero, one, and
  multiplicative inverse.

  The source equality of subsets of F x F is written as the bidirectionally
  equivalent pointwise membership statement for every x and y in Base ` F.
  Multiplication by invr is exactly field division, and
  ( 0g ` F ) ( -g ` F ) ( 1r ` F ) is the field element -1. Thus the
  existential parameter restriction and both coordinates are unchanged.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F r x y $.

  putnambench-putnam-1987-b3 $a |-
    A. F
      (
        (
          F e. Field
          /\
          (
            ( ( 1r ` F ) ( +g ` F ) ( 1r ` F ) )
            =/=
            ( 0g ` F )
          )
        )
        ->
        A. x e. ( Base ` F )
          A. y e. ( Base ` F )
            (
              (
                (
                  ( x ( .r ` F ) x )
                  ( +g ` F )
                  ( y ( .r ` F ) y )
                )
                =
                ( 1r ` F )
              )
              <->
              (
                (
                  x = ( 1r ` F )
                  /\
                  y = ( 0g ` F )
                )
                \/
                E. r e. ( Base ` F )
                  (
                    (
                      ( r ( .r ` F ) r )
                      =/=
                      (
                        ( 0g ` F )
                        ( -g ` F )
                        ( 1r ` F )
                      )
                    )
                    /\
                    (
                      x
                      =
                      (
                        (
                          ( r ( .r ` F ) r )
                          ( -g ` F )
                          ( 1r ` F )
                        )
                        ( .r ` F )
                        (
                          ( invr ` F )
                          `
                          (
                            ( r ( .r ` F ) r )
                            ( +g ` F )
                            ( 1r ` F )
                          )
                        )
                      )
                      /\
                      y
                      =
                      (
                        (
                          (
                            ( 1r ` F )
                            ( +g ` F )
                            ( 1r ` F )
                          )
                          ( .r ` F )
                          r
                        )
                        ( .r ` F )
                        (
                          ( invr ` F )
                          `
                          (
                            ( r ( .r ` F ) r )
                            ( +g ` F )
                            ( 1r ` F )
                          )
                        )
                      )
                    )
                  )
              )
            )
      )
  $.
$}
