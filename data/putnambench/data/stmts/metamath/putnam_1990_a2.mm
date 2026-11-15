$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1990_a2: existence of a real sequence of differences of cube roots
  of nonnegative integers that converges to the square root of two. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is set.mm's class of all real-valued sequences indexed by the
  nonnegative integers. For every sequence index, the witnesses n and m
  remain internally existentially quantified over NN0. On these nonnegative
  bases, set.mm's complex-power operation ^c with exponent 1 / 3 is the
  source real cube-root operation, including its value zero at base zero.

  The source-defined numform predicate is inlined without changing its
  quantifier scope. The Rocq source defines the solution proposition as True,
  and the Lean and Isabelle annotations give the same intended solution, so
  their biconditional with this existence claim is logically equivalent to
  the existence claim asserted below. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d i m n s $.

  putnambench-putnam-1990-a2 $a |-
    E. s e. ( RR ^m NN0 )
      (
        A. i e. NN0
          E. n e. NN0 E. m e. NN0
            ( s ` i )
            =
            (
              ( n ^c ( 1 / 3 ) )
              -
              ( m ^c ( 1 / 3 ) )
            )
        /\
        s ~~> ( sqrt ` 2 )
      )
  $.
$}
