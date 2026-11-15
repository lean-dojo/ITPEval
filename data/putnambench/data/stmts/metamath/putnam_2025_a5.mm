$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_a5 (putnambench__metamath__putnam_2025_a5): the sign
  sequences maximizing the number of permutations with prescribed adjacent
  ascent and descent directions are exactly the two alternating sequences.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, 0 ..^ n is the canonical n-element carrier corresponding
  to Fin n, and { -u 1 , 1 } ^m ( 0 ..^ n ) is the full space of sign
  functions, exactly representing the integer units in the Lean source.
  A bijection p of 0 ..^ ( n + 1 ) represents a permutation of Fin (n+1).

  For each sign function, the restricted class counted by # contains exactly
  those permutations for which every signed adjacent difference is positive.
  The universal comparison with every sign function therefore states that s
  maximizes this count. The biconditional identifies the maximizers as the
  two alternating sign functions, with the two possible initial signs.

  The source parameter n counts signs rather than permutation entries, so
  n e. NN is equivalent to its hypothesis 1 <= n and to the informal
  requirement that the permutation have at least two entries. The declaration
  below is the single unproved $a corpus statement; this database contains no
  $p proof declaration.
$)

${
  $d i n p s t $.

  putnambench-putnam-2025-a5 $a |-
    A. n e. NN
      A. s e. ( { -u 1 , 1 } ^m ( 0 ..^ n ) )
        (
          A. t e. ( { -u 1 , 1 } ^m ( 0 ..^ n ) )
            (
              #
              `
              {
                p |
                (
                  p
                  :
                  ( 0 ..^ ( n + 1 ) )
                  -1-1-onto->
                  ( 0 ..^ ( n + 1 ) )
                  /\
                  A. i e. ( 0 ..^ n )
                    0
                    <
                    (
                      ( t ` i )
                      x.
                      (
                        ( p ` ( i + 1 ) )
                        -
                        ( p ` i )
                      )
                    )
                )
              }
            )
            <_
            (
              #
              `
              {
                p |
                (
                  p
                  :
                  ( 0 ..^ ( n + 1 ) )
                  -1-1-onto->
                  ( 0 ..^ ( n + 1 ) )
                  /\
                  A. i e. ( 0 ..^ n )
                    0
                    <
                    (
                      ( s ` i )
                      x.
                      (
                        ( p ` ( i + 1 ) )
                        -
                        ( p ` i )
                      )
                    )
                )
              }
            )
          <->
          (
            A. i e. ( 0 ..^ n )
              ( s ` i ) = ( ( -u 1 ) ^ ( i + 1 ) )
            \/
            A. i e. ( 0 ..^ n )
              ( s ` i ) = ( ( -u 1 ) ^ i )
          )
        )
  $.
$}
