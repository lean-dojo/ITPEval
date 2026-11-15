$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_a4: evaluation of the positive-infinity limit of a rational
  function integrated over expanding disks in the real coordinate plane.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P21A4Index is the coordinate set {0,1}, so RR ^m P21A4Index is the real
  coordinate plane. P21A4Disk R is the closed disk x^2 + y^2 <= R^2.
  P21A4Integrand R is the source rational integrand on that disk and zero
  elsewhere. P21A4Integral R expands the same scalar function in coordinates
  and uses two applications of set.mm's real Lebesgue integral binder S.;
  this is the source disk integral written as an iterated integral.

  The relation ~~>r is set.mm's finite real limit at positive infinity. The
  right side is the value recorded in the Lean and Isabelle solution
  annotations. The final declaration is an unproved $a corpus statement;
  this database contains no $p proof statement.
$)

$c P21A4Index P21A4Disk P21A4Integrand P21A4Integral $.

p21a4-index-syntax $a class P21A4Index $.
p21a4-disk-syntax $a class ( P21A4Disk R ) $.
p21a4-integrand-syntax $a class ( P21A4Integrand R ) $.
p21a4-integral-syntax $a class ( P21A4Integral R ) $.

p21a4-index-definition $a |- P21A4Index = ( 0 ... 1 ) $.

${
  $d p R $.

  p21a4-disk-definition $a |- (
    P21A4Disk R
  ) = {
    p e. ( RR ^m P21A4Index ) |
      (
        (
          ( ( p ` 0 ) ^ 2 )
          +
          ( ( p ` 1 ) ^ 2 )
        )
        <_
        ( R ^ 2 )
      )
  } $.
$}

${
  $d p R $.

  p21a4-integrand-definition $a |- (
    P21A4Integrand R
  ) = (
    p e. ( RR ^m P21A4Index ) |->
      if (
        p e. ( P21A4Disk R ) ,
        (
          (
            (
              1
              +
              ( 2 x. ( ( p ` 0 ) ^ 2 ) )
            )
            /
            (
              (
                (
                  1
                  +
                  ( ( p ` 0 ) ^ 4 )
                )
                +
                (
                  6
                  x.
                  (
                    ( ( p ` 0 ) ^ 2 )
                    x.
                    ( ( p ` 1 ) ^ 2 )
                  )
                )
              )
              +
              ( ( p ` 1 ) ^ 4 )
            )
          )
          -
          (
            (
              1
              +
              ( ( p ` 1 ) ^ 2 )
            )
            /
            (
              (
                2
                +
                ( ( p ` 0 ) ^ 4 )
              )
              +
              ( ( p ` 1 ) ^ 4 )
            )
          )
        )
        ,
        0
      )
  ) $.
$}

${
  $d R x y $.

  p21a4-integral-definition $a |- (
    P21A4Integral R
  ) = (
    S. RR
      (
        S. RR
          if (
            (
              (
                ( x ^ 2 )
                +
                ( y ^ 2 )
              )
              <_
              ( R ^ 2 )
            ) ,
            (
              (
                (
                  1
                  +
                  ( 2 x. ( x ^ 2 ) )
                )
                /
                (
                  (
                    (
                      1
                      +
                      ( x ^ 4 )
                    )
                    +
                    (
                      6
                      x.
                      (
                        ( x ^ 2 )
                        x.
                        ( y ^ 2 )
                      )
                    )
                  )
                  +
                  ( y ^ 4 )
                )
              )
              -
              (
                (
                  1
                  +
                  ( y ^ 2 )
                )
                /
                (
                  (
                    2
                    +
                    ( x ^ 4 )
                  )
                  +
                  ( y ^ 4 )
                )
              )
            ) ,
            0
          )
          _d y
      )
      _d x
  ) $.
$}

putnambench-putnam-2021-a4 $a |- (
  R e. RR |->
    ( P21A4Integral R )
)
~~>r
(
  (
    ( sqrt ` 2 )
    /
    2
  )
  x.
  (
    _pi
    x.
    ( log ` 2 )
  )
)
$.
