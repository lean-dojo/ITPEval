$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_a3: a positive-indexed integer sequence with the specified
  2006-term initial segment and recurrence has 2005 consecutive terms
  divisible by 2006. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers, so x ranges over arbitrary
  positive-indexed integer sequences. This is bidirectionally equivalent to
  the Lean integer-indexed representation: restriction forgets only indices
  unused by the recurrence and conclusion, and every such restricted sequence
  extends to all integers with x(0) = 0 and arbitrary negative-index values.
  It also directly matches the positive-indexed sequence in the published
  problem and the relevant portion of the Isabelle natural-indexed sequence.

  The ordinal interval 0 ..^ 2005 contains exactly the offsets 0 through
  2004. Thus the internally existential positive index i starts a block of
  exactly 2005 consecutive terms, each satisfying integer divisibility by
  2006. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d i j k x $.

  putnambench-putnam-2006-a3 $a |-
    A. x e. ( ZZ ^m NN )
      (
        (
          A. k e. ( 1 ... ; ; ; 2 0 0 6 )
            ( x ` k ) = k
          /\
          A. k e. NN
            (
              ; ; ; 2 0 0 6 <_ k
              ->
              ( x ` ( k + 1 ) )
              =
              (
                ( x ` k )
                +
                ( x ` ( k - ; ; ; 2 0 0 5 ) )
              )
            )
        )
        ->
        E. i e. NN
          A. j e. ( 0 ..^ ; ; ; 2 0 0 5 )
            ; ; ; 2 0 0 6 || ( x ` ( i + j ) )
      )
  $.
$}
