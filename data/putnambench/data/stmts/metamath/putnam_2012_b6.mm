$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_b6: parity of the cube permutation on residue classes modulo
  an odd prime congruent to two modulo three. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For p in NN, 0 ..^ p is the full set of residue representatives modulo p.
  Base ` ( SymGrp ` ( 0 ..^ p ) ) is exactly the set of permutations of that
  carrier. The pointwise hypothesis identifies P with the source permutation
  x |-> x^3 modulo p, preserving the Fin p multiplication used by the Lean
  statement.

  Prime and Odd are SetMM's classes of natural primes and odd integers.
  Equality of remainders expresses the two source congruences. SetMM's pmSgn
  is 1 exactly on even permutations, so the final biconditional is the source
  parity characterization. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d P i p $.

  putnambench-putnam-2012-b6 $a |- A. p e. NN
    A. P e. ( Base ` ( SymGrp ` ( 0 ..^ p ) ) )
      (
        (
          (
            (
              p e. Prime
              /\
              p e. Odd
            )
            /\
            ( p mod 3 ) = 2
          )
          /\
          A. i e. ( 0 ..^ p )
            ( P ` i ) = ( ( i ^ 3 ) mod p )
        )
        ->
        (
          (
            ( pmSgn ` ( 0 ..^ p ) )
            `
            P
          )
          =
          1
          <->
          ( p mod 4 ) = 3
        )
      )
  $.
$}
