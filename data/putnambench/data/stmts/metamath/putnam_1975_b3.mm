$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_b3: the sharp supremum 1/k! of the kth elementary symmetric
  sum divided by the kth power of the first, over all finite tuples of
  positive real numbers having length at least k. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  A tuple of length n is represented by a real-valued function on the
  finite index set ( 1 ... n ), so equal entries remain distinct indexed
  occurrences. Its kth elementary symmetric sum is written directly as
  the sum over all k-element subsets s of the index set of the product of
  the entries indexed by s.

  Quantification over k in NN incorporates the source condition k > 0.
  The first conjunct is the upper-bound property for every admissible
  tuple. The second says that every real M below 1/k! is exceeded by an
  admissible tuple, preserving the internally existential witness and the
  source statement that the bound is the supremum. The final declaration
  is the single unproved $a corpus statement; this database contains no
  $p proof statement.
$)

${
  $d A M i k n s $.

  putnambench-putnam-1975-b3 $a |-
    A. k e. NN
      (
        A. n e. NN0
        A. A e. ( RR ^m ( 1 ... n ) )
          (
            (
              k <_ n
              /\
              A. i e. ( 1 ... n ) 0 < ( A ` i )
            )
            ->
            (
              (
                sum_ s e.
                  { s e. ~P ( 1 ... n ) | ( # ` s ) = k }
                  prod_ i e. s ( A ` i )
              )
              /
              (
                (
                  sum_ s e.
                    { s e. ~P ( 1 ... n ) | ( # ` s ) = 1 }
                    prod_ i e. s ( A ` i )
                )
                ^ k
              )
            )
            <_
            ( 1 / ( ! ` k ) )
          )
        /\
        A. M e. RR
          (
            M < ( 1 / ( ! ` k ) )
            ->
            E. n e. NN0
            E. A e. ( RR ^m ( 1 ... n ) )
              (
                (
                  k <_ n
                  /\
                  A. i e. ( 1 ... n ) 0 < ( A ` i )
                )
                /\
                M
                <
                (
                  (
                    sum_ s e.
                      { s e. ~P ( 1 ... n ) | ( # ` s ) = k }
                      prod_ i e. s ( A ` i )
                  )
                  /
                  (
                    (
                      sum_ s e.
                        { s e. ~P ( 1 ... n ) | ( # ` s ) = 1 }
                        prod_ i e. s ( A ` i )
                    )
                    ^ k
                  )
                )
              )
          )
      )
  $.
$}
