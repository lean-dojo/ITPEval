$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1989_a3: every complex root of
  11 z^10 + 10 i z^9 + 10 i z - 11 has modulus one.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  CC is SetMM's class of all complex numbers, _i is the imaginary unit,
  natural powers are the usual complex powers, and abs is complex modulus.
  Thus the assertion directly preserves the source polynomial equation and
  conclusion for an arbitrary complex z. The final declaration is a single
  unproved $a statement; this database contains no $p proof statement.
$)

putnambench-putnam-1989-a3 $a |- A. z e. CC
  (
    (
      (
        (
          (
            ( ; 1 1 )
            x.
            ( z ^ ( ; 1 0 ) )
          )
          +
          ( ( ( ; 1 0 ) x. _i ) x. ( z ^ 9 ) )
        )
        +
        ( ( ( ; 1 0 ) x. _i ) x. z )
      )
      -
      ( ; 1 1 )
    )
    =
    0
    ->
    ( abs ` z ) = 1
  )
$.
