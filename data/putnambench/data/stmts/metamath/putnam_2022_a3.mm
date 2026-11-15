$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_a3: for every prime p greater than 5, the number of infinite
  nonzero residue sequences satisfying the specified second-order recurrence
  modulo p is congruent to 0 or 2 modulo 5. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The interval 1 ... ( p - 1 ) is a complete set of representatives for the
  nonzero residues modulo p, and its function space over NN0 contains all
  infinite sequences from the source, with the harmless index shift from
  a_1, a_2, ... to indices 0, 1, ... . Equality of the displayed remainders
  is exactly the source congruence at every index.

  The auxiliary count f is eliminated by substituting its defining finite
  cardinality into the conclusion. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d a n p $.

  putnambench-putnam-2022-a3 $a |- A. p e. Prime
    (
      5 < p
      ->
      (
        (
          (
            #
            `
            {
              a e. ( ( 1 ... ( p - 1 ) ) ^m NN0 ) |
              A. n e. NN0
                (
                  (
                    ( ( a ` n ) x. ( a ` ( n + 2 ) ) )
                    mod p
                  )
                  =
                  (
                    ( 1 + ( a ` ( n + 1 ) ) )
                    mod p
                  )
                )
            }
          )
          mod 5
        )
        =
        0
        \/
        (
          (
            #
            `
            {
              a e. ( ( 1 ... ( p - 1 ) ) ^m NN0 ) |
              A. n e. NN0
                (
                  (
                    ( ( a ` n ) x. ( a ` ( n + 2 ) ) )
                    mod p
                  )
                  =
                  (
                    ( 1 + ( a ` ( n + 1 ) ) )
                    mod p
                  )
                )
            }
          )
          mod 5
        )
        =
        2
      )
    )
  $.
$}
