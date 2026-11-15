$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_b6: zero asymptotic density for a nonempty set of positive
  integers when the increasing enumeration of its positive difference set
  has unbounded successive gaps. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over arbitrary nonempty subsets of the positive integers NN,
  preserving the source's potentially infinite set. N is its counting
  function on real thresholds: # gives the cardinality of exactly those
  members of A not exceeding x. These bounded subsets of NN are finite.

  The source-defined set B is inlined as the positive integers d expressible
  as a - c with a,c in A. Because d is positive, ordinary integer subtraction
  is equivalent here to the source natural subtraction. The range and strict
  increase clauses say that b enumerates this set in increasing order.

  The first clause of the conclusion is exactly unboundedness of the
  successive gaps. The epsilon-threshold consequent expands convergence of
  N(x)/x to zero as the real variable x tends to positive infinity. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d A N a b c d e i m r x $.

  putnambench-putnam-2004-b6 $a |-
    A. A e. ~P NN
      A. N e. ( NN0 ^m RR )
        A. b e. ( NN0 ^m NN0 )
          (
            (
              (
                A =/= (/)
                /\
                A. x e. RR
                  (
                    ( N ` x )
                    =
                    (
                      #
                      `
                      { a e. A | a <_ x }
                    )
                  )
              )
              /\
              (
                ran b
                =
                {
                  d e. NN |
                  E. a e. A
                    E. c e. A
                      d = ( a - c )
                }
                /\
                A. i e. NN0
                  ( b ` i ) < ( b ` ( i + 1 ) )
              )
            )
            ->
            (
              A. r e. NN0
                E. i e. NN0
                  r <_ ( ( b ` ( i + 1 ) ) - ( b ` i ) )
              ->
              A. e e. RR
                (
                  0 < e
                  ->
                  E. m e. RR
                    A. x e. RR
                      (
                        m <_ x
                        ->
                        (
                          abs
                          `
                          (
                            (
                              ( N ` x )
                              /
                              x
                            )
                            -
                            0
                          )
                        )
                        < e
                      )
                )
            )
          )
  $.
$}
