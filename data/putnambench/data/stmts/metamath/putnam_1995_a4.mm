$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_a4: a cyclic integer necklace of positive length and total
  label sum n minus one has a cut after which every nonempty prefix sum is
  at most its zero-based final index. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal interval 0 ..^ n is the n-element carrier representing Fin n.
  Thus a e. ( ZZ ^m ( 0 ..^ n ) ) is an arbitrary integer labeling of the
  necklace. For k in that carrier, 0 ... k indexes the first k+1 labels
  after the cut, and reduction modulo n implements cyclic wraparound.

  The existential cut remains internal to the conclusion. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d a c i k n $.

  putnambench-putnam-1995-a4 $a |- A. n e. NN
    A. a e. ( ZZ ^m ( 0 ..^ n ) )
      (
        (
          sum_ i e. ( 0 ..^ n ) ( a ` i )
        )
        =
        ( n - 1 )
        ->
        E. c e. ( 0 ..^ n )
          A. k e. ( 0 ..^ n )
            (
              sum_ i e. ( 0 ... k )
                (
                  a
                  `
                  ( ( c + i ) mod n )
                )
            )
            <_
            k
      )
  $.
$}
