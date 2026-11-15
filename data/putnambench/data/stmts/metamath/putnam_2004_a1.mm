$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_a1: a free-throw prefix success rate that moves from below
  80 percent to above 80 percent must equal 80 percent at an intermediate
  attempt count. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The class { 0 , 1 } ^m NN0 consists of all infinite binary attempt
  sequences, bijectively representing both the Lean Fin 2-valued sequences
  and the Isabelle Boolean-valued sequences. F assigns a real-valued rate
  sequence to every such attempt sequence. Its antecedent is exactly the
  source definition at every positive index: the numerator is the finite
  prefix sum over indices 0 through n - 1, and 4 / 5 is the real number 0.8.

  Binding a, b, and c over NN incorporates the source condition 1 <= a;
  under a < c < b all three indices are positive. The source solution
  proposition is annotated True, so its biconditional with the universally
  quantified crossing property is equivalent to the assertion below. The
  final declaration is a single unproved $a statement, with no $p proof.
$)

${
  $d A F a b c i n $.

  putnambench-putnam-2004-a1 $a |-
    A. F e.
      ( ( RR ^m NN0 ) ^m ( { 0 , 1 } ^m NN0 ) )
      (
        A. A e. ( { 0 , 1 } ^m NN0 )
          A. n e. NN
            (
              ( ( F ` A ) ` n )
              =
              (
                (
                  sum_ i e. ( 0 ..^ n )
                    ( A ` i )
                )
                /
                n
              )
            )
        ->
        A. A e. ( { 0 , 1 } ^m NN0 )
          A. a e. NN
            A. b e. NN
              (
                (
                  a < b
                  /\
                  (
                    ( ( F ` A ) ` a ) < ( 4 / 5 )
                    /\
                    ( 4 / 5 ) < ( ( F ` A ) ` b )
                  )
                )
                ->
                E. c e. NN
                  (
                    a < c
                    /\
                    (
                      c < b
                      /\
                      ( ( F ` A ) ` c ) = ( 4 / 5 )
                    )
                  )
              )
      )
  $.
$}
