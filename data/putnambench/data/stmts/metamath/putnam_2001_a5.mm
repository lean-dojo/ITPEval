$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2001_a5: uniqueness of the positive integer-natural pair satisfying
  a^(n+1) - (a+1)^n = 2001. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Set.mm's ZZ and NN0 are the classes of integers and nonnegative integers.
  A source pair (a,n) is represented by an element t of ZZ X. NN0; its
  projections recover a and n. The restricted unique existential therefore
  states uniqueness of the entire pair, while the two strict inequalities
  preserve both source positivity conditions.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

putnambench-putnam-2001-a5 $a |- E! t e. ( ZZ X. NN0 )
  (
    0 < ( 1st ` t )
    /\
    (
      0 < ( 2nd ` t )
      /\
      (
        ( ( 1st ` t ) ^ ( ( 2nd ` t ) + 1 ) )
        -
        ( ( ( 1st ` t ) + 1 ) ^ ( 2nd ` t ) )
      )
      =
      ; ; ; 2 0 0 1
    )
  )
$.
