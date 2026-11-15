$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1982_a6: the assertion that the stated decay and convergence
  conditions force every bijective rearrangement to retain sum one is false.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers. Thus b ranges over all
  bijections of the positive integers and x over all positive-indexed real
  sequences. The pairwise inequality is exactly strict decrease of |x(n)|.
  The three uses of ~~> are the source limits of the displacement product,
  the original partial sums, and the rearranged partial sums.

  Negating the universal implication is logically equivalent to the source
  biconditional between that implication and False. Values at index zero in
  the source function types are unobserved, so restricting the function
  carriers to NN is bidirectionally equivalent. The final declaration is the
  single unproved $a corpus statement; this database contains no $p statement.
$)

${
  $d b i j k n x $.

  putnambench-putnam-1982-a6 $a |- -.
    (
      A. b e. ( NN ^m NN )
      A. x e. ( RR ^m NN )
        (
          (
            (
              b : NN -1-1-onto-> NN
              /\
              A. i e. NN
              A. j e. NN
                (
                  i < j
                  ->
                  ( abs ` ( x ` j ) ) < ( abs ` ( x ` i ) )
                )
            )
            /\
            (
              (
                n e. NN |->
                  (
                    ( abs ` ( ( b ` n ) - n ) )
                    x.
                    ( abs ` ( x ` n ) )
                  )
              )
              ~~>
              0
              /\
              (
                n e. NN |->
                  sum_ k e. ( 1 ... n ) ( x ` k )
              )
              ~~>
              1
            )
          )
          ->
          (
            n e. NN |->
              sum_ k e. ( 1 ... n ) ( x ` ( b ` k ) )
          )
          ~~>
          1
        )
    )
  $.
$}
