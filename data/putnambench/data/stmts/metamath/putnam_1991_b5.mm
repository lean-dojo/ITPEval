$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_b5: the number of residue classes modulo an odd prime that
  are both a square and one more than a square. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime is SetMM's class of natural primes, and ( 0 ..^ p ) is the standard
  set of representatives {0,...,p-1}. The two restricted classes therefore
  represent exactly the square residues and the residues that are one more
  than a square. This is the representative-set presentation used directly
  by Isabelle and Rocq, and reduction to standard representatives gives a
  bijection with Lean's ZMod p presentation.

  For odd p, floor(p/4) + 1 equals ceiling(p/4), so the right side is the
  explicit Rocq solution and the solution described in the Lean and Isabelle
  source comments. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d p x y z $.

  putnambench-putnam-1991-b5 $a |- A. p e. Prime
    (
      ( p mod 2 ) = 1
      ->
      (
        #
        `
        (
          {
            z e. ( 0 ..^ p ) |
            E. x e. ( 0 ..^ p )
              z = ( ( x ^ 2 ) mod p )
          }
          i^i
          {
            z e. ( 0 ..^ p ) |
            E. y e. ( 0 ..^ p )
              z = ( ( ( y ^ 2 ) + 1 ) mod p )
          }
        )
      )
      =
      ( ( |_ ` ( p / 4 ) ) + 1 )
    )
  $.
$}
