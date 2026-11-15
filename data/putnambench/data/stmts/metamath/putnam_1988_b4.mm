$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_b4: a convergent series of positive real terms remains a
  convergent series of positive terms after replacing a_n by
  a_n^(n/(n+1)). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over every total real-valued sequence indexed by the nonnegative
  integers. Positivity is required at exactly the positive indices, and each
  existential real limit together with set.mm's real-sequence convergence
  relation expresses convergence of the partial sums from 1 through n.

  Since every base occurring in either series is positive, set.mm's complex
  power A(n) ^c (n/(n+1)) agrees with the source real power. Inlining the
  source predicates appos, apconv, and apposconv is a definitional
  equivalence. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d A B C k n $.

  putnambench-putnam-1988-b4 $a |- A. A e. ( RR ^m NN0 )
    (
      (
        A. n e. NN 0 < ( A ` n )
        /\
        E. B e. RR
          (
            n e. NN0 |->
              sum_ k e. ( 1 ... n )
                ( A ` k )
          )
          ~~>
          B
      )
      ->
      (
        A. n e. NN
          0 < ( ( A ` n ) ^c ( n / ( n + 1 ) ) )
        /\
        E. C e. RR
          (
            n e. NN0 |->
              sum_ k e. ( 1 ... n )
                ( ( A ` k ) ^c ( k / ( k + 1 ) ) )
          )
          ~~>
          C
      )
    )
  $.
$}
