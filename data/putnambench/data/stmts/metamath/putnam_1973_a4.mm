$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1973_a4: the real function x |-> 2^x - 1 - x^2 has exactly
  three zeros on the real line. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source function is inlined into its zero set. On the positive real
  base 2, set.mm's complex-power operation ^c equals the source real power
  exp(x log 2). Thus the cardinality assertion below is definitionally
  equivalent to saying that the source function has exactly three real
  zeros.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  putnambench-putnam-1973-a4 $a |- (
    #
    `
    {
      x e. RR |
        (
          (
            ( 2 ^c x )
            -
            1
          )
          -
          ( x ^ 2 )
        )
        =
        0
    }
  )
  =
  3 $.
$}
