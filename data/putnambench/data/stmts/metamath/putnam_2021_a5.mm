$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_a5: divisibility by 2021 of power sums over the positive
  integers at most 2021 that are coprime to 2021, characterized by
  nondivisibility of the exponent by 42 and 46. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers, 1 ... 2021 is the inclusive
  finite interval, gcd is integer greatest common divisor, sum_ is finite
  summation, and || is integer divisibility. Thus the restricted sum inlines
  the source definitions of A and S without changing their domains or
  quantifier scope. The right side is the intended solution set displayed in
  the primary Lean source and the Isabelle source.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d j n $.

  putnambench-putnam-2021-a5 $a |-
    A. j e. NN0
      (
        (
          ( ; ; ; 2 0 2 1 )
          ||
          sum_ n e.
            {
              n e. ( 1 ... ( ; ; ; 2 0 2 1 ) ) |
              ( n gcd ( ; ; ; 2 0 2 1 ) ) = 1
            }
            ( n ^ j )
        )
        <->
        (
          -. ( ( ; 4 2 ) || j )
          /\
          -. ( ( ; 4 6 ) || j )
        )
      )
  $.
$}
