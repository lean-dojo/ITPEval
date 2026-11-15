$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_b5: classification of the positive integers n for which every
  integer relatively prime to n has a permutation square acting as
  multiplication modulo n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers. For positive n, the
  inclusive interval 1 ... n is the problem's n-element carrier, and the
  base of its symmetric group is exactly the set of its permutations.
  Equality of the displayed residues is congruence modulo n.

  The integer multiplier m remains universally quantified, and the
  permutation p remains existentially quantified inside that scope. The
  right side is the documented classification n = 1 or n congruent to 2
  modulo 4. The final declaration is a single unproved $a corpus statement;
  this database contains no $p proof declaration.
$)

${
  $d k m n p $.

  putnambench-putnam-2023-b5 $a |- A. n e. NN0
    (
      (
        0 < n
        /\
        A. m e. ZZ
          (
            ( m gcd n ) = 1
            ->
            E. p e. ( Base ` ( SymGrp ` ( 1 ... n ) ) )
              A. k e. ( 1 ... n )
                (
                  ( ( p ` ( p ` k ) ) mod n )
                  =
                  ( ( m x. k ) mod n )
                )
          )
      )
      <->
      (
        n = 1
        \/
        ( n mod 4 ) = 2
      )
    )
  $.
$}
