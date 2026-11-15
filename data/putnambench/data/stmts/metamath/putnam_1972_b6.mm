$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_b6: a polynomial with constant term one and strictly increasing
  positive-integer exponents has no complex zero of modulus less than
  (sqrt(5) - 1) / 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The positive natural k is the number of exponents, and 0 ..^ k is the
  k-element zero-based carrier corresponding to Fin k. The function n maps
  that carrier to the positive integers and is strictly increasing. Restriction
  to this carrier, and extension outside it, give the same data as the
  natural-indexed Isabelle and Rocq formulations.

  The source-defined function zpoly is inlined as the finite complex sum
  1 + sum_i z^(n_i). Since every n_i is positive, the natural exponent here
  agrees with the positive integer exponent in the Lean formulation. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d i j k n z $.

  putnambench-putnam-1972-b6 $a |-
    A. k e. NN
      A. n e. ( NN ^m ( 0 ..^ k ) )
        (
          A. i e. ( 0 ..^ k )
            A. j e. ( 0 ..^ k )
              ( i < j -> ( n ` i ) < ( n ` j ) )
          ->
          A. z e. CC
            (
              ( abs ` z ) < ( ( ( sqrt ` 5 ) - 1 ) / 2 )
              ->
              (
                1
                +
                sum_ i e. ( 0 ..^ k )
                  ( z ^ ( n ` i ) )
              )
              =/=
              0
            )
        )
  $.
$}
