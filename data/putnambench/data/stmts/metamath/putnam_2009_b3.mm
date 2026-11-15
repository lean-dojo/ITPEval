$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_b3: classification of the positive integers for which the
  second difference of the number of average-closed subsets of 1 through n
  equals one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P09B3Mediocre n S says exactly that S is a subset of the integer interval
  1 ... n and contains the average of any two of its elements whenever that
  average is an integer. P09B3A maps every integer n to the finite cardinality
  of the full class of such subsets.

  The right-hand set retains the internally existential positive integer
  exponent from the annotated solution in the ground truth. All declarations
  are unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c P09B3Mediocre P09B3A $.

p09b3-mediocre-syntax $a wff ( P09B3Mediocre n S ) $.
p09b3-a-syntax $a class P09B3A $.

${
  $d S a b n $.

  p09b3-mediocre-definition $a |- (
    ( P09B3Mediocre n S )
    <->
    (
      S C_ ( 1 ... n )
      /\
      A. a e. S A. b e. S
        (
          2 || ( a + b )
          ->
          ( ( a + b ) / 2 ) e. S
        )
    )
  ) $.
$}

${
  $d S n $.

  p09b3-a-definition $a |- P09B3A =
    (
      n e. ZZ |->
        (
          # `
          {
            S e. ~P ( 1 ... n )
            |
            ( P09B3Mediocre n S )
          }
        )
    )
  $.
$}

${
  $d k n $.

  putnambench-putnam-2009-b3 $a |- (
    {
      n e. ZZ
      |
      (
        0 < n
        /\
        (
          (
            ( P09B3A ` ( n + 2 ) )
            -
            ( 2 x. ( P09B3A ` ( n + 1 ) ) )
          )
          +
          ( P09B3A ` n )
        )
        =
        1
      )
    }
    =
    {
      n e. ZZ
      |
      E. k e. NN
        n = ( ( 2 ^ k ) - 1 )
    }
  ) $.
$}
