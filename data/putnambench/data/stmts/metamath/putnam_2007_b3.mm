$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_b3: the value at index 2007 of the real sequence defined by
  x(0) = 1 and x(n+1) = 3x(n) + floor(x(n) sqrt(5)) has the stated closed
  form. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers, and x ranges over all total
  real-valued sequences on NN0. SetMM's sqrt is the principal square root,
  and |_ is the real floor function, so the initial value and recurrence are
  the published problem's defining conditions.

  Write phi = (1 + sqrt(5)) / 2. The annotated solution's negative integer
  power phi^(-4017) is inlined as 1 / phi^4017. Since phi is positive, these
  are equal, so the conclusion is the same closed form as the Rocq definition
  and the Lean solution annotation.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d n x $.

  putnambench-putnam-2007-b3 $a |-
    A. x e. ( RR ^m NN0 )
      (
        (
          ( x ` 0 ) = 1
          /\
          A. n e. NN0
            ( x ` ( n + 1 ) )
            =
            (
              ( 3 x. ( x ` n ) )
              +
              (
                |_
                `
                (
                  ( x ` n )
                  x.
                  ( sqrt ` 5 )
                )
              )
            )
        )
        ->
        ( x ` ; ; ; 2 0 0 7 )
        =
        (
          (
            ( 2 ^ ; ; ; 2 0 0 6 )
            /
            ( sqrt ` 5 )
          )
          x.
          (
            (
              (
                ( 1 + ( sqrt ` 5 ) )
                /
                2
              )
              ^
              ; ; ; 4 0 1 7
            )
            +
            (
              1
              /
              (
                (
                  ( 1 + ( sqrt ` 5 ) )
                  /
                  2
                )
                ^
                ; ; ; 4 0 1 7
              )
            )
          )
        )
      )
  $.
$}
