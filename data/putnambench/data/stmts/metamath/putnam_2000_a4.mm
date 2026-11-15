$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_a4: convergence to a finite real limit of the improper
  integral from zero to B of sin(x) sin(x^2) as B tends to positive
  infinity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The binder S. ( 0 [,] t ) F _d x is set.mm's real Lebesgue integral.
  Changing endpoint inclusion does not affect this integral, so it agrees
  with the interval formulations in the ground-truth sources.

  The maps-to expression retains an arbitrary real upper endpoint, and the
  relation ~~>r is set.mm's finite real limit at positive infinity. Thus the
  existentially quantified L is the internal convergence witness. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d L t x $.

  putnambench-putnam-2000-a4 $a |-
    E. L e. RR
      (
        (
          t e. RR |->
            S. ( 0 [,] t )
              (
                ( sin ` x )
                x.
                ( sin ` ( x ^ 2 ) )
              )
              _d x
        )
        ~~>r
        L
      )
  $.
$}
