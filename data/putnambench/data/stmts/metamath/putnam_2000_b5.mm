$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_b5: finite sets of positive integers evolving by exclusive
  membership with their unit shift recur arbitrarily late as the union of
  the initial set and its index translate. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function space ( ( ~P ZZ ) ^m NN0 ) quantifies arbitrary sequences of
  sets of integers. Finiteness and positivity are imposed pointwise. The
  recurrence expands exclusive-or into its two disjoint cases, preserving
  exactly the source membership condition.

  For N in NN0, the restricted class
  { M e. ZZ | ( M - N ) e. ( S ` 0 ) } is exactly the translate
  { N + a | a e. ( S ` 0 ) }. The quantifier
  A. n e. NN0 E. N e. NN0 ( n <_ N /\ ... ) states that such indices are
  arbitrarily large. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d M N S a n s $.

  putnambench-putnam-2000-b5 $a |-
    A. S e. ( ( ~P ZZ ) ^m NN0 )
      (
        (
          (
            A. n e. NN0
              ( S ` n ) e. Fin
            /\
            A. n e. NN0 A. s e. ( S ` n )
              0 < s
          )
          /\
          A. n e. NN0 A. a e. ZZ
            (
              a e. ( S ` ( n + 1 ) )
              <->
              (
                (
                  ( a - 1 ) e. ( S ` n )
                  /\
                  -. a e. ( S ` n )
                )
                \/
                (
                  a e. ( S ` n )
                  /\
                  -. ( a - 1 ) e. ( S ` n )
                )
              )
            )
        )
        ->
        A. n e. NN0 E. N e. NN0
          (
            n <_ N
            /\
            ( S ` N )
            =
            (
              ( S ` 0 )
              u.
              { M e. ZZ | ( M - N ) e. ( S ` 0 ) }
            )
          )
      )
  $.
$}
