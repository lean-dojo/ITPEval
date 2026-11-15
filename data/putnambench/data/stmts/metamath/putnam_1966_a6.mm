$(
  Statement-only formalization of PutnamBench artifact putnam_1966_a6:
  the first entries of finite square-root recurrences with diagonal value n
  converge to three as the recurrence length tends to infinity. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The function a ranges over all NN0-indexed families of NN0-indexed real
  sequences. Quantification over NN exactly represents the source bounds
  n >= 1 and m >= 1, while the recurrence retains the guard m < n. The
  piecewise square-root term is the total real square root used by the
  sources: set.mm's principal square root on nonnegative reals and zero on
  negative reals. The conclusion uses set.mm's real-sequence convergence
  relation.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a m n $.

  putnambench-putnam-1966-a6 $a |-
    A. a e. ( ( RR ^m NN0 ) ^m NN0 )
      (
        A. n e. NN
          (
            ( ( a ` n ) ` n ) = n
            /\
            A. m e. NN
              (
                m < n
                ->
                ( ( a ` n ) ` m )
                =
                (
                  m
                  x.
                  if
                    (
                      0 <_ ( 1 + ( ( a ` n ) ` ( m + 1 ) ) ) ,
                      ( sqrt ` ( 1 + ( ( a ` n ) ` ( m + 1 ) ) ) ) ,
                      0
                    )
                )
              )
          )
        ->
        (
          n e. NN0 |->
            ( ( a ` n ) ` 1 )
        )
        ~~>
        3
      )
  $.
$}
