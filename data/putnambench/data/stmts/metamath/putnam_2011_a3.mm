$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_a3: the choice c = -1 and L = 2 / pi gives a positive
  real limit for the specified ratio of two trigonometric power integrals.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Set.mm's S. binder is the real Lebesgue integral. The open interval
  ( 0 , pi / 2 ) exactly matches the primary Lean and Isabelle sources.
  On this interval x is positive, so x ^c r is real-valued and agrees with
  their real-power operation for every real exponent r.

  The maps-to expression retains the source's arbitrary real parameter r,
  and ~~>r is set.mm's finite real limit at positive infinity. The factor
  r ^c ( -1 ) is the source factor r^c for the explicit solution c = -1;
  its values away from the eventually positive part of the real line do not
  affect the limit. The target 2 / _pi is the explicit positive value given
  by the Rocq source and by the solution annotations in the Lean and
  Isabelle sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d r x $.

  putnambench-putnam-2011-a3 $a |- (
    0 < ( 2 / _pi )
    /\
    (
      (
        r e. RR |->
          (
            (
              ( r ^c ( -u 1 ) )
              x.
              S. ( 0 (,) ( _pi / 2 ) )
                (
                  ( x ^c r )
                  x.
                  ( sin ` x )
                )
                _d x
            )
            /
            S. ( 0 (,) ( _pi / 2 ) )
              (
                ( x ^c r )
                x.
                ( cos ` x )
              )
              _d x
          )
      )
      ~~>r
      ( 2 / _pi )
    )
  ) $.
$}
