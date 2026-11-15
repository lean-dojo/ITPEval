$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2020_a1: the number of positive integers divisible by 2020, having
  at most 2020 decimal digits, and consisting of consecutive ones followed
  by consecutive zeros is 508536. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers, and || is integer
  divisibility. The internally existential nonnegative integers k and l,
  with l <= k, express a nonempty block of k-l+1 ones followed by l zeros.
  Its displayed sum is positive, so the enclosing NN0 set contains exactly
  the source's positive integers.

  For these positive integers, n < 10^2020 is equivalent to having at most
  2020 decimal digits, hence to the source condition
  Nat.log 10 n + 1 <= 2020. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d i k l n $.

  putnambench-putnam-2020-a1 $a |-
    (
      #
      `
      {
        n e. NN0 |
        (
          ; ; ; 2 0 2 0 || n
          /\
          (
            n < ( ( ; 1 0 ) ^ ; ; ; 2 0 2 0 )
            /\
            E. k e. NN0 E. l e. NN0
              (
                l <_ k
                /\
                n
                =
                sum_ i e. ( 0 ... ( k - l ) )
                  ( ( ; 1 0 ) ^ ( i + l ) )
              )
          )
        )
      }
    )
    =
    ; ; ; ; ; 5 0 8 5 3 6
  $.
$}
