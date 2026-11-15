$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_b1: every positive rational number is a quotient of two finite
  products of factorials of prime numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For k in NN0, 0 ..^ k is the k-element natural index set, and a member of
  Prime ^m ( 0 ..^ k ) is exactly a k-term family of natural primes. Thus the
  two existential families below represent the source finite lists, including
  repetition and the empty list. SetMM's ! is factorial and prod_ is finite
  product, with value 1 on an empty index set.

  The witnesses k, m, a, and b remain internally existential for each positive
  rational q. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d a b i j k m q $.

  putnambench-putnam-2009-b1 $a |-
    A. q e. QQ
      (
        0 < q
        ->
        E. k e. NN0
          E. m e. NN0
            E. a e. ( Prime ^m ( 0 ..^ k ) )
              E. b e. ( Prime ^m ( 0 ..^ m ) )
                q
                =
                (
                  (
                    prod_ i e. ( 0 ..^ k )
                      ( ! ` ( a ` i ) )
                  )
                  /
                  (
                    prod_ j e. ( 0 ..^ m )
                      ( ! ` ( b ` j ) )
                  )
                )
      )
  $.
$}
