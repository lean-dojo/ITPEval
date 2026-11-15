$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2001_b6: infinitely many strict midpoint inequalities in every
  positive increasing real sequence that grows sublinearly. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers, so a ranges over exactly the
  positive-indexed real sequences in the published problem. The Lean source
  extends a to all integers, but its hypotheses and conclusion observe only
  positive indices; the Isabelle and Rocq sources use natural indices with
  the same positive-indexed content.

  The sequence n |-> a(n)/n is the index-shifted form of the source sequence
  n |-> a(n+1)/(n+1), and therefore has the same limit. Non-membership of the
  displayed subset of NN in Fin states that infinitely many positive n
  satisfy every inequality for i from 1 through n-1. The source solution is
  True, so its biconditional with the displayed proposition is logically
  equivalent to the proposition itself.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a i n $.

  putnambench-putnam-2001-b6 $a |-
    A. a e. ( RR ^m NN )
      (
        (
          A. n e. NN
            (
              0 < ( a ` n )
              /\
              ( a ` n ) < ( a ` ( n + 1 ) )
            )
          /\
          (
            n e. NN |->
              ( ( a ` n ) / n )
          )
          ~~>
          0
        )
        ->
        {
          n e. NN
          |
          A. i e. ( 1 ... ( n - 1 ) )
            (
              ( ( a ` ( n - i ) ) + ( a ` ( n + i ) ) )
              <
              ( 2 x. ( a ` n ) )
            )
        }
        e/
        Fin
      )
  $.
$}
