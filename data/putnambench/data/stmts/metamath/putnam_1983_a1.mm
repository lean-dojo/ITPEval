$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1983_a1: the number of positive integers dividing at least one of
  10^40 and 20^30 is 2301. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers, so the restricted class is
  exactly the positive divisors appearing in the Lean and Isabelle sources.
  The Rocq natural-number formulation gives the same class because zero
  divides neither positive power. The decimal numeral on the right is the
  source solution value 2301.

  The final declaration is the single unproved $a corpus statement; this
  root artifact file declares no $p proof statement.
$)

putnambench-putnam-1983-a1 $a |-
  (
    #
    `
    {
      n e. NN
      |
      (
        n || ( ; 1 0 ^ ; 4 0 )
        \/
        n || ( ; 2 0 ^ ; 3 0 )
      )
    }
  )
  =
  ; ; ; 2 3 0 1
$.
