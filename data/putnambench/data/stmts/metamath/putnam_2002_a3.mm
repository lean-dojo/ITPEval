$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2002_a3: the parity of the number of nonempty subsets of
  {1, ..., n} whose average is an integer. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The class ( 1 ... n ) is the inclusive integer interval from the sources,
  and s ranges over its full powerset. The condition s =/= (/) preserves
  nonemptiness. The internally quantified integer k witnesses that the real
  average (1 / #s) times the finite sum of the elements of s is integral.

  The variable t represents T_n and is equated to the cardinality of exactly
  those subsets. For integers t and n, 2 || ( t - n ) is the source
  conclusion that T_n - n is even. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d j k n s t $.

  putnambench-putnam-2002-a3 $a |-
    A. n e. ZZ A. t e. ZZ
      (
        (
          2 <_ n
          /\
          t
          =
          (
            #
            `
            {
              s e. ~P ( 1 ... n )
              |
              (
                s =/= (/)
                /\
                E. k e. ZZ
                  k
                  =
                  (
                    ( 1 / ( # ` s ) )
                    x.
                    ( sum_ j e. s j )
                  )
              )
            }
          )
        )
        ->
        2 || ( t - n )
      )
  $.
$}
