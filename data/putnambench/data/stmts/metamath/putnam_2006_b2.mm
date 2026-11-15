$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_b2: every finite set of n real numbers, for positive n, has a
  nonempty subset whose sum is within 1 / (n + 1) of an integer. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers. The conditions X C_ RR and
  ( # ` X ) = n represent an arbitrary n-element set of real numbers; the
  finite cardinality equality also ensures that X is finite. The witness S
  ranges over the full powerset of X and is required to be nonempty.

  The finite sum over S is added to the internally existential integer m,
  and its absolute value is bounded by 1 / (n + 1), exactly as in the source
  statements. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d m n s S X $.

  putnambench-putnam-2006-b2 $a |- A. n e. NN A. X
    (
      (
        X C_ RR
        /\
        ( # ` X ) = n
      )
      ->
      E. S e. ~P X
        (
          S =/= (/)
          /\
          E. m e. ZZ
            (
              abs
              `
              (
                m
                +
                ( sum_ s e. S s )
              )
            )
            <_
            ( 1 / ( n + 1 ) )
        )
    )
  $.
$}
