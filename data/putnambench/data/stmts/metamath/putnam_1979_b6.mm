$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_b6: the absolute real part of the principal square root of the
  sum of squares of a finite complex sequence is bounded by the sum of the
  absolute real parts of its terms. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, the class CC ^m ( 1 ... n ) is the set of all n-term
  complex families. This is equivalent to the source representations by
  Fin n, finite sequences, and functions restricted to the inclusive
  interval from 1 through n.

  Set.mm's sqrt is the principal complex square root, Re is the real-part
  function, abs is complex modulus and hence real absolute value on real
  inputs, and sum_ is the finite sum binder. Thus the assertion preserves
  both sides of the source inequality, including the empty-family case.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i n z $.

  putnambench-putnam-1979-b6 $a |- A. n e. NN0
    A. z e. ( CC ^m ( 1 ... n ) )
      (
        (
          abs
          `
          (
            Re
            `
            (
              sqrt
              `
              (
                sum_ i e. ( 1 ... n )
                  ( ( z ` i ) ^ 2 )
              )
            )
          )
        )
        <_
        (
          sum_ i e. ( 1 ... n )
            ( abs ` ( Re ` ( z ` i ) ) )
        )
      )
  $.
$}
