$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1976_b5: the alternating binomial sum of the shifted powers
  (x - k)^n is the constant real polynomial n factorial. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the set of nonnegative integers, RR is the set of real numbers, and
  ( 0 ... n ) is the inclusive integer interval from zero through n. The
  summand uses set.mm's binomial coefficients, real multiplication and
  subtraction, natural powers, and factorial.

  This pointwise real identity is bidirectionally equivalent to the Lean
  integer-polynomial equality: polynomial evaluation gives this statement,
  while equality at every real x determines an integer polynomial because
  RR is infinite. The resulting integer polynomial identity transports to
  every MathComp realType, matching the Rocq statement, and pointwise
  equality is equivalent by extensionality to the Isabelle function
  equality. The final declaration is one unproved $a statement; this
  database contains no $p proof statement.
$)

${
  $d k n x $.

  putnambench-putnam-1976-b5 $a |-
    A. n e. NN0
      A. x e. RR
        (
          sum_ k e. ( 0 ... n )
            (
              (
                ( ( -u 1 ) ^ k )
                x.
                ( n _C k )
              )
              x.
              ( ( x - k ) ^ n )
            )
          =
          ( ! ` n )
        )
  $.
$}
