$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2020_b1: the binary-digit-sum signed sum of cubes from 1 through
  2020 has remainder 1990 modulo 2020. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers. The universally quantified
  function d is characterized by the binary digit-sum recurrence: d(n) is n
  below two, and otherwise is n mod 2 plus d(floor(n/2)).

  The finite sum is over the inclusive interval from 1 through 2020, and each
  term is (-1) raised to d(k), times k cubed. The source hypotheses uniquely
  define S as this sum, so substituting the sum for S is bidirectionally
  equivalent to the source's quantified presentation. The final declaration
  is the single unproved $a corpus statement; this database contains no $p
  proof declaration.
$)

${
  $d d k n $.

  putnambench-putnam-2020-b1 $a |-
    A. d e. ( NN0 ^m NN0 )
      (
        A. n e. NN0
          ( d ` n )
          =
          if (
            n < 2 ,
            n ,
            (
              ( n mod 2 )
              +
              ( d ` ( |_ ` ( n / 2 ) ) )
            )
          )
        ->
        (
          (
            sum_ k e. ( 1 ... ; ; ; 2 0 2 0 )
              (
                ( ( -u 1 ) ^ ( d ` k ) )
                x.
                ( k ^ 3 )
              )
          )
          mod
          ; ; ; 2 0 2 0
        )
        =
        ; ; ; 1 9 9 0
      )
  $.
$}
