$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1967_b4: after successively toggling exactly the lockers whose
  numbers are divisible by each operation index, the open lockers are
  exactly those with perfect-square numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The locker state is an arbitrary total integer-valued function of a
  nonnegative operation index and a nonnegative locker number. On the
  constrained indices, 0 and 1 encode the two Boolean states, and
  1 - state is exactly Boolean negation. Values outside stages 0 through n
  and locker numbers 1 through n are irrelevant, so total extension is
  equivalent to the source finite-index function representations.

  Quantification over NN incorporates the source assumption n >= 1. For a
  positive integer i, existence of an integer j with j ^ 2 = i is equivalent
  to existence of a natural-number square root. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d L i j k n $.

  putnambench-putnam-1967-b4 $a |-
    A. n e. NN
    A. L e. ( ( ZZ ^m NN0 ) ^m NN0 )
      (
        (
          A. i e. ( 1 ... n )
            ( ( L ` 0 ) ` i ) = 0
          /\
          A. k e. ( 1 ... n )
          A. i e. ( 1 ... n )
            ( ( L ` k ) ` i )
            =
            if (
              k || i ,
              ( 1 - ( ( L ` ( k - 1 ) ) ` i ) ) ,
              ( ( L ` ( k - 1 ) ) ` i )
            )
        )
        ->
        A. i e. ( 1 ... n )
          (
            ( ( L ` n ) ` i ) = 1
            <->
            E. j e. ZZ ( j ^ 2 ) = i
          )
      )
  $.
$}
