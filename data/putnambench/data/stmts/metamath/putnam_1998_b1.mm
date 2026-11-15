$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_b1: the minimum over positive real x of the stated rational
  expression in x and its reciprocal is 6. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The first conjunct states that 6 is a lower bound for the objective at
  every positive real x. The second conjunct keeps the attaining positive
  real x existentially quantified inside the statement and requires the
  objective to equal 6 there. Together these clauses are the explicit
  IsLeast characterization of the minimum in the ground-truth sources.

  The rational expression is inlined exactly, with all powers and reciprocal
  terms over the real numbers. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

putnambench-putnam-1998-b1 $a |- (
    A. x e. RR
      (
        0 < x
        ->
        6
        <_
        (
          (
            (
              ( ( x + ( 1 / x ) ) ^ 6 )
              -
              (
                ( x ^ 6 )
                +
                ( 1 / ( x ^ 6 ) )
              )
            )
            -
            2
          )
          /
          (
            ( ( x + ( 1 / x ) ) ^ 3 )
            +
            (
              ( x ^ 3 )
              +
              ( 1 / ( x ^ 3 ) )
            )
          )
        )
      )
    /\
    E. x e. RR
      (
        0 < x
        /\
        (
          (
            (
              ( ( x + ( 1 / x ) ) ^ 6 )
              -
              (
                ( x ^ 6 )
                +
                ( 1 / ( x ^ 6 ) )
              )
            )
            -
            2
          )
          /
          (
            ( ( x + ( 1 / x ) ) ^ 3 )
            +
            (
              ( x ^ 3 )
              +
              ( 1 / ( x ^ 3 ) )
            )
          )
        )
        =
        6
      )
  ) $.
