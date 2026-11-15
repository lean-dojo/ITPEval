$(
  Statement-only formalization of PutnamBench artifact putnam_1966_b3:
  convergence of the series with terms n squared times a positive sequence
  term divided by the square of its prefix sum, assuming convergence of the
  reciprocal series. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over all real-valued sequences indexed by the nonnegative
  integers. For m in NN0, the interval 1 ... m is inclusive and is empty
  when m is zero, exactly matching the source partial sums. Each existential
  real limit together with set.mm's real-sequence convergence relation
  expresses convergence of the corresponding series.

  The positivity assumption includes index zero exactly as in all three
  ground-truth formalizations, although both series begin at index one. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d A B C i m n $.

  putnambench-putnam-1966-b3 $a |- A. A e. ( RR ^m NN0 )
    (
      (
        A. n e. NN0 0 < ( A ` n )
        /\
        E. B e. RR
          (
            m e. NN0 |->
              sum_ n e. ( 1 ... m )
                ( 1 / ( A ` n ) )
          )
          ~~>
          B
      )
      ->
      E. C e. RR
        (
          m e. NN0 |->
            sum_ n e. ( 1 ... m )
              (
                (
                  ( A ` n )
                  x.
                  ( n ^ 2 )
                )
                /
                (
                  (
                    sum_ i e. ( 1 ... n )
                      ( A ` i )
                  )
                  ^ 2
                )
              )
        )
        ~~>
        C
    )
  $.
$}
