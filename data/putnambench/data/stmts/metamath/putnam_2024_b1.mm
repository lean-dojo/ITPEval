$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_b1: the positive grid sizes n and offsets k admitting a
  nonattacking selection whose integer entries are exactly 1 through n
  are precisely (2 l + 1, l + 1). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, the interval 1 ... n is the n-element carrier corresponding
  to Fin n, with its elements numbered by the source's successor coordinates.
  A self-map of this finite carrier is injective exactly when it is bijective,
  so f : ( 1 ... n ) -1-1-onto-> ( 1 ... n ) faithfully renders the
  nonattacking choice of one column in every row.

  The restricted class abstraction is the range of the selected integer grid
  entries i + f(i) - k. Its equality to 1 ... n is exactly the source range
  equality with the integer interval from 1 through n. Quantifying n and k
  over NN0 and retaining both positivity conditions preserves the zero cases
  of the source set equality. The right side inlines the annotated solution
  set { (2 l + 1, l + 1) | l is a natural number }.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f i k l n z $.

  putnambench-putnam-2024-b1 $a |- A. n e. NN0
    A. k e. NN0
      (
        (
          (
            0 < n
            /\
            0 < k
          )
          /\
          E. f
            (
              f : ( 1 ... n ) -1-1-onto-> ( 1 ... n )
              /\
              {
                z e. ZZ |
                E. i e. ( 1 ... n )
                  z = ( ( i + ( f ` i ) ) - k )
              }
              =
              ( 1 ... n )
            )
        )
        <->
        E. l e. NN0
          (
            n = ( ( 2 x. l ) + 1 )
            /\
            k = ( l + 1 )
          )
      )
  $.
$}
