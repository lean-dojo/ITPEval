$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_b6 (putnambench__metamath__putnam_2022_b6):
  continuous positive-real-valued functions on the positive reals satisfy
  the given functional equation exactly when they have the form
  f(x) = 1 / (1 + c*x) for a nonnegative real c. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The interval ( 0 (,) +oo ) is set.mm's full set of positive reals.
  Membership in its continuous-function space quantifies over exactly the
  continuous maps from the positive reals to the positive reals, so no
  values outside the source domain are introduced.

  The two-variable functional equation retains its universal positive-real
  scope. The coefficient c remains internally existentially quantified over
  the reals with c >= 0, and the displayed identity is required at every
  positive real input. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d F c x y $.

  putnambench-putnam-2022-b6 $a |-
    A. F e.
      (
        ( 0 (,) +oo )
        -cn->
        ( 0 (,) +oo )
      )
      (
        A. x e. ( 0 (,) +oo )
          A. y e. ( 0 (,) +oo )
            (
              (
                F
                `
                (
                  x
                  x.
                  ( F ` y )
                )
              )
              +
              (
                F
                `
                (
                  y
                  x.
                  ( F ` x )
                )
              )
            )
            =
            (
              1
              +
              ( F ` ( x + y ) )
            )
        <->
        E. c e. RR
          (
            0 <_ c
            /\
            A. x e. ( 0 (,) +oo )
              ( F ` x )
              =
              (
                1
                /
                (
                  1
                  +
                  ( c x. x )
                )
              )
          )
      )
  $.
$}
