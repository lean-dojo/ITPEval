$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_a3: termination and choice-independence of the process replacing
  a nondividing pair of positive integers by its gcd and lcm.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, the set ( 0 ..^ n ) is the n-element index set corresponding
  to Fin n. The initial sequence a is an arbitrary positive-integer-valued
  function on that set. A trajectory P is an NN0-indexed family of
  nonnegative-integer-valued functions on the same index set.

  The antecedent inlines the source predicates init and trans. At every time
  when some j < k has P(t,j) not dividing P(t,k), the next state is obtained
  by replacing precisely those entries by their gcd and lcm. The conclusion
  says that one finite sequence f is the terminal state of every such
  trajectory, so the stopping state is independent of all legal choices.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d P a f i j k n t $.

  putnambench-putnam-2008-a3 $a |-
    A. n e. NN
      A. a e. ( NN ^m ( 0 ..^ n ) )
        E. f e. ( NN0 ^m ( 0 ..^ n ) )
          A. P e. ( ( NN0 ^m ( 0 ..^ n ) ) ^m NN0 )
            (
              (
                ( P ` 0 ) = a
                /\
                A. t e. NN0
                  (
                    (
                      E. j e. ( 0 ..^ n ) E. k e. ( 0 ..^ n )
                        (
                          j < k
                          /\
                          -. ( ( ( P ` t ) ` j ) || ( ( P ` t ) ` k ) )
                        )
                    )
                    ->
                    E. j e. ( 0 ..^ n ) E. k e. ( 0 ..^ n )
                      (
                        j < k
                        /\
                        (
                          -. ( ( ( P ` t ) ` j ) || ( ( P ` t ) ` k ) )
                          /\
                          (
                            ( ( P ` ( t + 1 ) ) ` j )
                            =
                            ( ( ( P ` t ) ` j ) gcd ( ( P ` t ) ` k ) )
                            /\
                            (
                              ( ( P ` ( t + 1 ) ) ` k )
                              =
                              ( ( ( P ` t ) ` j ) lcm ( ( P ` t ) ` k ) )
                              /\
                              A. i e. ( 0 ..^ n )
                                (
                                  (
                                    i =/= j
                                    /\
                                    i =/= k
                                  )
                                  ->
                                  ( ( P ` ( t + 1 ) ) ` i )
                                  =
                                  ( ( P ` t ) ` i )
                                )
                            )
                          )
                        )
                      )
                  )
              )
              ->
              E. t e. NN0
                (
                  -.
                    E. j e. ( 0 ..^ n ) E. k e. ( 0 ..^ n )
                      (
                        j < k
                        /\
                        -. ( ( ( P ` t ) ` j ) || ( ( P ` t ) ` k ) )
                      )
                  /\
                  ( P ` t ) = f
                )
            )
  $.
$}
