$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_b2: classification of the positive integer tuples whose sum is
  5n - 4 and whose reciprocal sum is one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers. The function k ranges over all
  integer-valued sequences on NN0, while 0 ..^ n selects exactly its first n
  entries. Thus values outside the tuple remain unconstrained, as in the Lean
  and Isabelle sources. Positivity of the selected entries makes the displayed
  reciprocal sum a sum of positive real numbers.

  The right side lists the one-entry solution, all six permutations of
  (2, 3, 6), and the four-entry constant solution. This is the explicit Rocq
  solution and the solution set documented by the Lean and Isabelle sources.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i k n $.

  putnambench-putnam-2005-b2 $a |- A. n e. NN
    A. k e. ( ZZ ^m NN0 )
      (
        (
          (
            A. i e. ( 0 ..^ n )
              0 < ( k ` i )
            /\
            sum_ i e. ( 0 ..^ n ) ( k ` i )
              =
            ( ( 5 x. n ) - 4 )
          )
          /\
          sum_ i e. ( 0 ..^ n ) ( 1 / ( k ` i ) )
            =
          1
        )
        <->
        (
          (
            n = 1
            /\
            ( k ` 0 ) = 1
          )
          \/
          (
            n = 3
            /\
            (
              (
                ( k ` 0 ) = 2
                /\
                ( k ` 1 ) = 3
                /\
                ( k ` 2 ) = 6
              )
              \/
              (
                ( k ` 0 ) = 2
                /\
                ( k ` 1 ) = 6
                /\
                ( k ` 2 ) = 3
              )
              \/
              (
                ( k ` 0 ) = 3
                /\
                ( k ` 1 ) = 2
                /\
                ( k ` 2 ) = 6
              )
              \/
              (
                ( k ` 0 ) = 3
                /\
                ( k ` 1 ) = 6
                /\
                ( k ` 2 ) = 2
              )
              \/
              (
                ( k ` 0 ) = 6
                /\
                ( k ` 1 ) = 2
                /\
                ( k ` 2 ) = 3
              )
              \/
              (
                ( k ` 0 ) = 6
                /\
                ( k ` 1 ) = 3
                /\
                ( k ` 2 ) = 2
              )
            )
          )
          \/
          (
            n = 4
            /\
            ( k ` 0 ) = 4
            /\
            ( k ` 1 ) = 4
            /\
            ( k ` 2 ) = 4
            /\
            ( k ` 3 ) = 4
          )
        )
      )
  $.
$}
