$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_7
  (verina__metamath__verina_basic_7), catalog title
  sumOfSquaresOfFirstNOddNumbers: the exact descending natural-number
  accumulator recursion sums the squares of the first n odd numbers and
  satisfies its closed-form correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number execution traces.

  VERINAB7NatSub is Lean's truncated natural subtraction.
  VERINAB7LoopGraph is the exact execution graph of the source local loop for
  every natural current counter and accumulator. Its two traces begin with
  those arguments. At each of exactly A transitions the positive counter is
  decremented by one and the accumulator is increased by the square of
  2*k-1, using truncated subtraction exactly as in the Lean program. The
  final counter is zero and C is the final accumulator. VERINAB7Loop selects
  this unique result, and VERINAB7SumOfSquares invokes it with accumulator
  zero. Thus the executable result is fixed independently of the
  postcondition and no extra output is admitted.

  VERINAB7ClosedForm is the source natural-number expression
  n*(2*n-1)*(2*n+1)/3. Since its numerator is nonnegative, floor of SetMM
  rational division by three is exactly Lean's Nat.div. VERINAB7Pre is the
  source True precondition together with the Nat input type. VERINAB7Post
  preserves both source conjuncts using truncated natural subtraction.
  The proof-valued precondition arguments are computationally and
  propositionally unused and are represented by the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB7NatSub VERINAB7LoopGraph VERINAB7Loop
  VERINAB7Pre VERINAB7SumOfSquares VERINAB7ClosedForm VERINAB7Post
$.

verinab7-nat-sub-syntax
  $a class ( VERINAB7NatSub A B ) $.
verinab7-loop-graph-syntax
  $a wff ( VERINAB7LoopGraph A B C ) $.
verinab7-loop-syntax
  $a class ( VERINAB7Loop A B ) $.
verinab7-precondition-syntax
  $a wff ( VERINAB7Pre A ) $.
verinab7-program-syntax
  $a class ( VERINAB7SumOfSquares A ) $.
verinab7-closed-form-syntax
  $a class ( VERINAB7ClosedForm A ) $.
verinab7-postcondition-syntax
  $a wff ( VERINAB7Post A B ) $.

verinab7-nat-sub-definition $a |- (
  VERINAB7NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d i k s A B C $.

  verinab7-loop-graph-definition $a |- (
    VERINAB7LoopGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. NN0
      )
      /\
      C e. NN0
    )
    /\
    E. k e. Word NN0 E. s e. Word NN0
      (
        (
          (
            ( # ` k ) = ( A + 1 )
            /\
            ( # ` s ) = ( A + 1 )
          )
          /\
          (
            ( k ` 0 ) = A
            /\
            ( s ` 0 ) = B
          )
        )
        /\
        (
          A. i e. ( 0 ..^ A )
            (
              0 < ( k ` i )
              /\
              (
                (
                  k ` ( i + 1 )
                ) = (
                  VERINAB7NatSub
                    ( k ` i )
                    1
                )
                /\
                (
                  s ` ( i + 1 )
                ) = (
                  ( s ` i )
                  +
                  (
                    (
                      VERINAB7NatSub
                        ( 2 x. ( k ` i ) )
                        1
                    )
                    x.
                    (
                      VERINAB7NatSub
                        ( 2 x. ( k ` i ) )
                        1
                    )
                  )
                )
              )
            )
          /\
          (
            ( k ` A ) = 0
            /\
            C = ( s ` A )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab7-loop-definition $a |- (
    VERINAB7Loop A B
  ) = (
    iota_ y e. NN0
      ( VERINAB7LoopGraph A B y )
  ) $.
$}

verinab7-precondition-definition $a |- (
  VERINAB7Pre A
) <-> (
  A e. NN0
) $.

verinab7-program-definition $a |- (
  VERINAB7SumOfSquares A
) = (
  VERINAB7Loop A 0
) $.

verinab7-closed-form-definition $a |- (
  VERINAB7ClosedForm A
) = (
  |_ ` (
    (
      (
        A
        x.
        ( VERINAB7NatSub ( 2 x. A ) 1 )
      )
      x.
      ( ( 2 x. A ) + 1 )
    )
    /
    3
  )
) $.

verinab7-postcondition-definition $a |- (
  VERINAB7Post A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    (
      VERINAB7NatSub
        B
        ( VERINAB7ClosedForm A )
    ) = 0
    /\
    (
      VERINAB7NatSub
        ( VERINAB7ClosedForm A )
        B
    ) = 0
  )
) $.

verina-basic-7-sum-of-squares-of-first-n-odd-numbers $a |- A. n e. NN0
  (
    ( VERINAB7Pre n )
    ->
    (
      VERINAB7Post
        n
        ( VERINAB7SumOfSquares n )
    )
  )
$.
