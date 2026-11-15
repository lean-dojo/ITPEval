$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1989_a2: evaluation of an iterated real integral over a positive
  rectangle whose integrand is the exponential of the maximum of two
  quadratic terms. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The nested S. binders are set.mm's real Lebesgue integrals. The closed
  intervals agree directly with the Isabelle rectangle and Rocq bounds;
  replacing them by the Lean source's open intervals changes only boundary
  sets of Lebesgue measure zero.

  The conditional if ( u <_ v , v , u ) is max(u,v). The right side is the
  explicit solution defined by the Rocq source and recorded in the Lean and
  Isabelle solution annotations. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d a b x y $.

  putnambench-putnam-1989-a2 $a |-
    A. a e. RR A. b e. RR
      (
        (
          0 < a
          /\
          0 < b
        )
        ->
        S. ( 0 [,] a )
          (
            S. ( 0 [,] b )
              (
                exp
                `
                if (
                  (
                    ( b ^ 2 )
                    x.
                    ( x ^ 2 )
                  )
                  <_
                  (
                    ( a ^ 2 )
                    x.
                    ( y ^ 2 )
                  ) ,
                  (
                    ( a ^ 2 )
                    x.
                    ( y ^ 2 )
                  ) ,
                  (
                    ( b ^ 2 )
                    x.
                    ( x ^ 2 )
                  )
                )
              )
              _d y
          )
          _d x
        =
        (
          (
            exp
            `
            (
              ( a ^ 2 )
              x.
              ( b ^ 2 )
            )
          )
          -
          1
        )
        /
        ( a x. b )
      )
  $.
$}
